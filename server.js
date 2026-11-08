import http from 'node:http';
import { readFile } from 'node:fs/promises';
import { mkdirSync } from 'node:fs';
import { resolve, extname } from 'node:path';
import { randomInt, randomBytes, scrypt as scryptCb, timingSafeEqual, createHash } from 'node:crypto';
import { promisify } from 'node:util';
import { DatabaseSync } from 'node:sqlite';
import nodemailer from 'nodemailer';

const scrypt = promisify(scryptCb);
const root = process.cwd();
const dataDir = process.env.DATA_DIR || root;
mkdirSync(dataDir, { recursive: true });
const db = new DatabaseSync(resolve(dataDir, 'fauna.db'));
db.exec(`PRAGMA journal_mode = WAL;
CREATE TABLE IF NOT EXISTS users (id INTEGER PRIMARY KEY, email TEXT UNIQUE NOT NULL, password_hash TEXT NOT NULL, verified INTEGER NOT NULL DEFAULT 0, created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP);
CREATE TABLE IF NOT EXISTS verification_codes (email TEXT PRIMARY KEY, code_hash TEXT NOT NULL, expires_at INTEGER NOT NULL, attempts INTEGER NOT NULL DEFAULT 0);
CREATE TABLE IF NOT EXISTS support_messages (id INTEGER PRIMARY KEY, user_id INTEGER NOT NULL, sender TEXT NOT NULL CHECK(sender IN ('user','admin')), message TEXT NOT NULL, created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP, read_by_admin INTEGER NOT NULL DEFAULT 0);`);
const sessions = new Map();
const adminSessions = new Map();
const adminFailures = new Map();
const pendingPasswords = new Map();
const taxaCache = new Map();
const chatRateLimits = new Map();
let taxaQueue = Promise.resolve(), taxaLastRequest = 0;
const smtpReady = !!(process.env.SMTP_HOST && process.env.SMTP_USER && process.env.SMTP_PASS && process.env.SMTP_FROM);
const resendReady = !!(process.env.RESEND_API_KEY && process.env.EMAIL_FROM);
const brevoReady = !!(process.env.BREVO_API_KEY && process.env.BREVO_FROM_EMAIL && process.env.BREVO_FROM_NAME);
const emailReady = brevoReady || resendReady || smtpReady;
const mailer = smtpReady ? nodemailer.createTransport({ host: process.env.SMTP_HOST, port: Number(process.env.SMTP_PORT || 587), secure: process.env.SMTP_SECURE === 'true', connectionTimeout: 10000, greetingTimeout: 10000, socketTimeout: 20000, auth: { user: process.env.SMTP_USER, pass: process.env.SMTP_PASS } }) : null;
const mime = { '.html':'text/html; charset=utf-8', '.css':'text/css; charset=utf-8', '.js':'text/javascript; charset=utf-8', '.svg':'image/svg+xml' };

function send(res, status, data, cookie='') { res.writeHead(status, { 'content-type':'application/json; charset=utf-8', 'set-cookie': cookie, 'cache-control':'no-store', 'x-content-type-options':'nosniff', 'x-frame-options':'DENY', 'referrer-policy':'no-referrer' }); res.end(JSON.stringify(data)); }
async function body(req) { let s=''; for await (const c of req) { s+=c; if (s.length>12000) throw Error('too large'); } return JSON.parse(s || '{}'); }
function emailOk(x) { return typeof x==='string' && x.length<=254 && /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(x); }
function sessionUser(req) { const raw=(req.headers.cookie||'').split(';').map(x=>x.trim()).find(x=>x.startsWith('fauna_session='))?.split('=')[1]; const email=raw && sessions.get(raw); return email ? db.prepare('SELECT id,email,verified FROM users WHERE email=?').get(email) : null; }
function adminToken(req) { return (req.headers.cookie||'').split(';').map(x=>x.trim()).find(x=>x.startsWith('fauna_admin='))?.slice('fauna_admin='.length); }
function isAdmin(req) { const token=adminToken(req), expires=token&&adminSessions.get(token); if(!expires)return false; if(expires<Date.now()){adminSessions.delete(token);return false} adminSessions.set(token,Date.now()+60*60*1000); return true; }
function fixedEqual(a,b) { return timingSafeEqual(createHash('sha256').update(String(a)).digest(),createHash('sha256').update(String(b)).digest()); }
async function fetchTaxa(url,options) { const waitFor=taxaQueue;let release;taxaQueue=new Promise(resolve=>release=resolve);await waitFor;const delay=Math.max(0,1000-(Date.now()-taxaLastRequest));if(delay)await new Promise(resolve=>setTimeout(resolve,delay));taxaLastRequest=Date.now();try{return await fetch(url,options)}finally{release()} }
async function sendEmail(to,subject,textBody,htmlBody) {
  if(brevoReady) {
    const response=await fetch('https://api.brevo.com/v3/smtp/email',{method:'POST',headers:{'api-key':process.env.BREVO_API_KEY,'Content-Type':'application/json','Accept':'application/json'},body:JSON.stringify({sender:{name:process.env.BREVO_FROM_NAME,email:process.env.BREVO_FROM_EMAIL},to:[{email:to}],subject,textContent:textBody,htmlContent:htmlBody}),signal:AbortSignal.timeout(15000)});
    if(!response.ok) throw Error(`Brevo API HTTP ${response.status}: ${(await response.text()).slice(0,1000)}`);
  } else if(resendReady) {
    const response=await fetch('https://api.resend.com/emails',{method:'POST',headers:{'Authorization':`Bearer ${process.env.RESEND_API_KEY}`,'Content-Type':'application/json'},body:JSON.stringify({from:process.env.EMAIL_FROM,to,subject,text:textBody,html:htmlBody}),signal:AbortSignal.timeout(15000)});
    if(!response.ok) throw Error(`Resend API HTTP ${response.status}: ${(await response.text()).slice(0,1000)}`);
  } else if(smtpReady) await mailer.sendMail({from:process.env.SMTP_FROM,to,subject,text:textBody,html:htmlBody});
  else throw Error('Email provider is not configured');
}
async function route(req,res) {
  const url=new URL(req.url,'http://localhost');
  if (url.pathname.startsWith('/api/')) {
    try {
      const input=['POST'].includes(req.method) ? await body(req) : {};
      if(url.pathname==='/api/admin/login' && req.method==='POST') {
        const ip=String(req.headers['x-forwarded-for']||req.socket.remoteAddress||'unknown').split(',').at(-1).trim();
        const attempt=adminFailures.get(ip), now=Date.now();
        if(attempt && attempt.until>now && attempt.count>=5) return send(res,429,{error:'Слишком много попыток. Попробуйте снова через 15 минут.'});
        const configuredEmail=String(process.env.ADMIN_EMAIL||'').trim().toLowerCase(), configuredPassword=String(process.env.ADMIN_PASSWORD||'');
        if(!configuredEmail||configuredPassword.length<16) return send(res,503,{error:'Настройте ADMIN_EMAIL и ADMIN_PASSWORD в Railway → Variables.'});
        const email=String(input.email||'').trim().toLowerCase(), password=String(input.password||'');
        const valid=fixedEqual(email,configuredEmail)&&fixedEqual(password,configuredPassword);
        if(!valid) { const current=attempt&&attempt.until>now?attempt:{count:0,until:now+15*60*1000}; current.count++;adminFailures.set(ip,current);return send(res,401,{error:'Почта администратора или пароль неверны.'}); }
        adminFailures.delete(ip);
        const token=randomBytes(32).toString('hex');adminSessions.set(token,now+60*60*1000);
        return send(res,200,{ok:true},`fauna_admin=${token}; HttpOnly; SameSite=Strict; Path=/api/admin; Max-Age=3600${process.env.NODE_ENV==='production'?'; Secure':''}`);
      }
      if(url.pathname==='/api/admin/me' && req.method==='GET') return isAdmin(req)?send(res,200,{ok:true}):send(res,401,{error:'Требуется вход администратора.'});
      if(url.pathname==='/api/admin/logout' && req.method==='POST') { const token=adminToken(req);if(token)adminSessions.delete(token);return send(res,200,{ok:true},'fauna_admin=; HttpOnly; SameSite=Strict; Path=/api/admin; Max-Age=0'+(process.env.NODE_ENV==='production'?'; Secure':'')); }
      if(url.pathname==='/api/admin/users' && req.method==='GET') {
        if(!isAdmin(req)) return send(res,401,{error:'Требуется вход администратора.'});
        const rows=db.prepare('SELECT id,email,verified,created_at FROM users ORDER BY id DESC').all();
        const summary=db.prepare('SELECT COUNT(*) AS total, SUM(CASE WHEN verified=1 THEN 1 ELSE 0 END) AS verified FROM users').get();
        return send(res,200,{users:rows,summary:{total:summary.total,verified:summary.verified||0}});
      }
      if(url.pathname==='/api/admin/support' && req.method==='GET') {
        if(!isAdmin(req)) return send(res,401,{error:'Требуется вход администратора.'});
        const threads=db.prepare(`SELECT u.id AS user_id,u.email,MAX(m.created_at) AS last_message,COUNT(m.id) AS message_count,SUM(CASE WHEN m.sender='user' AND m.read_by_admin=0 THEN 1 ELSE 0 END) AS unread FROM users u JOIN support_messages m ON m.user_id=u.id GROUP BY u.id ORDER BY MAX(m.id) DESC`).all();
        return send(res,200,{threads});
      }
      const adminThread=url.pathname.match(/^\/api\/admin\/support\/(\d+)$/);
      if(adminThread && req.method==='GET') {
        if(!isAdmin(req)) return send(res,401,{error:'Требуется вход администратора.'});
        const userId=Number(adminThread[1]), account=db.prepare('SELECT id,email FROM users WHERE id=?').get(userId);
        if(!account)return send(res,404,{error:'Пользователь не найден.'});
        db.prepare("UPDATE support_messages SET read_by_admin=1 WHERE user_id=? AND sender='user'").run(userId);
        const messages=db.prepare('SELECT id,sender,message,created_at FROM support_messages WHERE user_id=? ORDER BY id').all(userId);
        return send(res,200,{account,messages});
      }
      const adminReply=url.pathname.match(/^\/api\/admin\/support\/(\d+)\/reply$/);
      if(adminReply && req.method==='POST') {
        if(!isAdmin(req))return send(res,401,{error:'Требуется вход администратора.'});
        const userId=Number(adminReply[1]), message=String(input.message||'').trim();
        if(!db.prepare('SELECT id FROM users WHERE id=?').get(userId))return send(res,404,{error:'Пользователь не найден.'});
        if(!message||message.length>3000)return send(res,400,{error:'Ответ должен содержать от 1 до 3000 символов.'});
        db.prepare("INSERT INTO support_messages(user_id,sender,message,read_by_admin) VALUES(?,'admin',?,1)").run(userId,message);
        return send(res,200,{ok:true});
      }
      if(url.pathname==='/api/support/messages' && req.method==='GET') {
        const account=sessionUser(req);if(!account?.verified)return send(res,401,{error:'Войдите, чтобы написать в поддержку.'});
        return send(res,200,{messages:db.prepare('SELECT id,sender,message,created_at FROM support_messages WHERE user_id=? ORDER BY id DESC LIMIT 100').all(account.id).reverse()});
      }
      if(url.pathname==='/api/support/messages' && req.method==='POST') {
        const account=sessionUser(req);if(!account?.verified)return send(res,401,{error:'Войдите, чтобы написать в поддержку.'});
        const message=String(input.message||'').trim();if(!message||message.length>3000)return send(res,400,{error:'Сообщение должно содержать от 1 до 3000 символов.'});
        const recent=db.prepare("SELECT COUNT(*) AS total FROM support_messages WHERE user_id=? AND sender='user' AND created_at>=datetime('now','-1 minute')").get(account.id);
        if(recent.total>=5)return send(res,429,{error:'Слишком много сообщений подряд. Подожди минуту и попробуй снова.'});
        const result=db.prepare("INSERT INTO support_messages(user_id,sender,message) VALUES(?,'user',?)").run(account.id,message);
        return send(res,201,{message:db.prepare('SELECT id,sender,message,created_at FROM support_messages WHERE id=?').get(result.lastInsertRowid)});
      }
      if(url.pathname==='/api/chat' && req.method==='POST') {
        const key=String(process.env.GEMINI_API_KEY||''), question=String(input.message||'').trim();
        if(!key)return send(res,503,{error:'AI-помощник пока не подключён: владельцу сайта нужно добавить GEMINI_API_KEY в Railway Variables.'});
        if(!question||question.length>1200)return send(res,400,{error:'Напишите вопрос длиной до 1200 символов.'});
        const ip=String(req.headers['x-forwarded-for']||req.socket.remoteAddress||'unknown').split(',').at(-1).trim(), now=Date.now(), prev=chatRateLimits.get(ip);
        if(prev&&prev.until>now&&prev.count>=12)return send(res,429,{error:'Слишком много вопросов подряд. Попробуйте через минуту.'});
        const state=prev&&prev.until>now?prev:{count:0,until:now+60_000};state.count++;chatRateLimits.set(ip,state);
        const history=Array.isArray(input.history)?input.history.slice(-8).map(m=>({role:m?.role==='model'?'model':'user',parts:[{text:String(m?.text||'').slice(0,1200)}]})).filter(m=>m.parts[0].text):[];
        const model=String(process.env.GEMINI_MODEL||'gemini-3.8-flash');
        try {
          const response=await fetch(`https://generativelanguage.googleapis.com/v1beta/models/${encodeURIComponent(model)}:generateContent`,{method:'POST',headers:{'content-type':'application/json','x-goog-api-key':key},body:JSON.stringify({systemInstruction:{parts:[{text:'Ты дружелюбный русскоязычный помощник сайта Fauna Violet. Отвечай понятно и доброжелательно, преимущественно о животных, природе и использовании сайта. Не выдумывай факты: если не уверен, прямо скажи об этом и предложи проверить надёжный источник. Не проси пароли, коды подтверждения или платёжные данные. Ответ до 180 слов.'}]},contents:[...history,{role:'user',parts:[{text:question}]}],generationConfig:{temperature:0.55,maxOutputTokens:700}}),signal:AbortSignal.timeout(25000)});
          const data=await response.json();if(!response.ok){console.error(`Gemini API failed: HTTP ${response.status}`);return send(res,response.status===429?429:502,{error:response.status===429?'У AI временно закончился лимит запросов. Попробуйте позже.':'AI сейчас не смог ответить. Попробуйте ещё раз.'});}
          const answer=data.candidates?.[0]?.content?.parts?.map(p=>p.text||'').join('').trim();if(!answer)return send(res,502,{error:'AI прислал пустой ответ. Попробуйте ещё раз.'});
          return send(res,200,{answer});
        } catch(err) { console.error(`Gemini request failed: ${err.name||'Error'}`);return send(res,502,{error:'Не удалось связаться с AI. Попробуйте ещё раз.'}); }
      }
      if(url.pathname==='/api/animals/search' && req.method==='GET') {
        const q=String(url.searchParams.get('q')||'').trim().slice(0,100);
        if(q.length<2)return send(res,200,{animals:[]});
        const cacheKey=q.toLocaleLowerCase('ru');let results=taxaCache.get(cacheKey);
        if(!results||results.until<Date.now()) {
          const apiUrl=new URL('https://api.inaturalist.org/v1/taxa/autocomplete');apiUrl.searchParams.set('q',q);apiUrl.searchParams.set('per_page','20');apiUrl.searchParams.set('locale','ru');apiUrl.searchParams.set('taxon_id','2');
          try { const response=await fetchTaxa(apiUrl,{headers:{'Accept':'application/json','User-Agent':'FaunaViolet/1.0'},signal:AbortSignal.timeout(12000)});if(!response.ok)throw Error(`iNaturalist HTTP ${response.status}`);const data=await response.json();results=(data.results||[]).filter(t=>t.is_active&&['species','subspecies'].includes(t.rank)).map(t=>{const icons={Mammalia:'🐾',Aves:'🐦',Amphibia:'🐸',Reptilia:'🦎',Actinopterygii:'🐟',Insecta:'🦋',Arachnida:'🕷️',Mollusca:'🐙',Annelida:'🪱',Chromista:'🪸'};return {id:`inat-${t.id}`,taxonId:t.id,name:t.preferred_common_name||t.name,latin:t.name,group:'Онлайн-каталог',emoji:icons[t.iconic_taxon_name]||'🐾',color:'#65537f',image:null,observationsCount:t.observations_count,rank:t.rank,sourceUrl:`https://www.inaturalist.org/taxa/${t.id}`,detail:`Вид из международного каталога iNaturalist. На платформе зарегистрировано наблюдений: ${Number(t.observations_count||0).toLocaleString('ru-RU')}.`};});taxaCache.set(cacheKey,{until:Date.now()+10*60*1000,results});if(taxaCache.size>150)taxaCache.delete(taxaCache.keys().next().value); }
          catch(err) { console.error(`iNaturalist search failed: ${err.name||'Error'}`);return send(res,502,{error:'Не удалось выполнить поиск по каталогу видов. Попробуйте позже.'}); }
        }
        return send(res,200,{animals:results,source:'iNaturalist'});
      }
      if(url.pathname==='/api/animals/detail' && req.method==='GET') {
        const id=Number(url.searchParams.get('id'));if(!Number.isSafeInteger(id)||id<1)return send(res,400,{error:'Некорректный ID вида.'});
        try { const response=await fetchTaxa(`https://api.inaturalist.org/v1/taxa/${id}?locale=ru`,{headers:{'Accept':'application/json','User-Agent':'FaunaViolet/1.0'},signal:AbortSignal.timeout(15000)});if(!response.ok)throw Error(`iNaturalist HTTP ${response.status}`);const data=await response.json(),taxon=data.results?.[0];if(!taxon)return send(res,404,{error:'Описание этого вида не найдено.'});const detail=String(taxon.wikipedia_summary||'').replace(/<[^>]*>/g,' ').replace(/&nbsp;/g,' ').replace(/&amp;/g,'&').replace(/&#39;/g,"'").replace(/&quot;/g,'"').replace(/\s+/g,' ').trim();return send(res,200,{detail:detail||`${taxon.preferred_common_name||taxon.name} — таксон из каталога iNaturalist. Подробная статья может отсутствовать на русском языке.`,habitat:'Уточняйте по научным источникам для конкретного подвида и региона.',diet:'Рацион зависит от конкретного вида.',lifespan:'Продолжительность жизни зависит от конкретного вида.',sourceUrl:`https://www.inaturalist.org/taxa/${id}`,sourceName:'iNaturalist'}); }
        catch(err) { console.error(`iNaturalist detail failed: ${err.name||'Error'}`);return send(res,502,{error:'Не удалось загрузить описание вида. Попробуйте позже.'}); }
      }
      if(url.pathname==='/api/forgot' && req.method==='POST') {
        const email=String(input.email||'').trim().toLowerCase();
        if(!emailOk(email)) return send(res,400,{error:'Введите корректный адрес почты.'});
        const user=db.prepare('SELECT id FROM users WHERE email=? AND verified=1').get(email);
        if(!user) return send(res,200,{message:'Если адрес зарегистрирован, на него придёт код для сброса пароля.'});
        const code=String(randomInt(0,1000000)).padStart(6,'0');
        const codeHash=await scrypt(code,process.env.CODE_PEPPER||'fauna-violet-local',32);
        db.prepare('INSERT INTO verification_codes(email,code_hash,expires_at,attempts) VALUES(?,?,?,0) ON CONFLICT(email) DO UPDATE SET code_hash=excluded.code_hash,expires_at=excluded.expires_at,attempts=0').run(email,codeHash,Date.now()+10*60*1000);
        const textBody=`Код для сброса пароля Fauna Violet: ${code}\\nОн действует 10 минут.`;
        const htmlBody=`<div style="font:16px Arial;color:#302341"><h2>Сброс пароля Fauna Violet</h2><p style="font-size:32px;letter-spacing:8px"><b>${code}</b></p><p>Код действует 10 минут. Если вы не запрашивали сброс, просто проигнорируйте это письмо.</p></div>`;
        try { await sendEmail(email,'Код для сброса пароля Fauna Violet',textBody,htmlBody); }
        catch(err) { console.error(`Password reset email failed: ${err.code||'UNKNOWN'}: ${err.message}`); db.prepare('DELETE FROM verification_codes WHERE email=?').run(email); return send(res,502,{error:'Не удалось отправить письмо. Проверьте почтовый ящик и попробуйте позже.'}); }
        return send(res,200,{message:'Если адрес зарегистрирован, на него придёт код для сброса пароля.'});
      }
      if(url.pathname==='/api/reset' && req.method==='POST') {
        const email=String(input.email||'').trim().toLowerCase(), code=String(input.code||'').trim(), password=String(input.password||'');
        if(!emailOk(email)) return send(res,400,{error:'Введите корректный адрес почты.'});
        if(password.length<8 || password.length>128) return send(res,400,{error:'Новый пароль должен содержать от 8 до 128 символов.'});
        const row=db.prepare('SELECT * FROM verification_codes WHERE email=?').get(email);
        if(!row || row.expires_at<Date.now()) { db.prepare('DELETE FROM verification_codes WHERE email=?').run(email); return send(res,400,{error:'Код истёк. Запросите новый.'}); }
        if(row.attempts>=5) { db.prepare('DELETE FROM verification_codes WHERE email=?').run(email); return send(res,429,{error:'Слишком много попыток. Запросите новый код.'}); }
        const given=await scrypt(code,process.env.CODE_PEPPER||'fauna-violet-local',32);
        if(!/^\d{6}$/.test(code) || !timingSafeEqual(given,Buffer.from(row.code_hash))) { db.prepare('UPDATE verification_codes SET attempts=attempts+1 WHERE email=?').run(email); return send(res,400,{error:'Код неверный. Проверьте письмо и попробуйте ещё раз.'}); }
        const salt=randomBytes(16).toString('hex'), hash=(await scrypt(password,salt,64)).toString('hex');
        const result=db.prepare('UPDATE users SET password_hash=? WHERE email=? AND verified=1').run(`${salt}:${hash}`,email);
        db.prepare('DELETE FROM verification_codes WHERE email=?').run(email);
        if(!result.changes) return send(res,400,{error:'Не удалось сбросить пароль. Проверьте адрес и попробуйте снова.'});
        return send(res,200,{message:'Пароль успешно изменён. Теперь войдите с новым паролем.'});
      }
      if (url.pathname==='/api/register' && req.method==='POST') {
        if (process.env.NODE_ENV === 'production' && !emailReady) return send(res,503,{error:'Регистрация временно недоступна: владелец сайта ещё не настроил отправку почты.'});
        const email=String(input.email||'').trim().toLowerCase(), password=String(input.password||'');
        if(!emailOk(email)) return send(res,400,{error:'Введите корректный адрес почты.'});
        if(password.length<8 || password.length>128) return send(res,400,{error:'Пароль должен содержать от 8 до 128 символов.'});
        if(db.prepare('SELECT id FROM users WHERE email=?').get(email)) return send(res,409,{error:'Этот адрес уже зарегистрирован. Попробуйте войти.'});
        const code=String(randomInt(0,1000000)).padStart(6,'0');
        const codeHash=await scrypt(code, process.env.CODE_PEPPER||'fauna-violet-local',32);
        db.prepare('INSERT INTO verification_codes(email,code_hash,expires_at,attempts) VALUES(?,?,?,0) ON CONFLICT(email) DO UPDATE SET code_hash=excluded.code_hash,expires_at=excluded.expires_at,attempts=0').run(email,codeHash,Date.now()+10*60*1000);
        const salt=randomBytes(16).toString('hex'); pendingPasswords.set(email,{salt,hash:(await scrypt(password,salt,64)).toString('hex'),until:Date.now()+10*60*1000});
        if(emailReady) {
          const subject='Ваш код для Fauna Violet';
          const textBody=`Код подтверждения: ${code}\nОн действует 10 минут.`;
          const htmlBody=`<div style="font:16px Arial;color:#302341"><h2>Ваш код подтверждения</h2><p style="font-size:32px;letter-spacing:8px"><b>${code}</b></p><p>Код действует 10 минут.</p></div>`;
          try {
            if(brevoReady) {
              const response=await fetch('https://api.brevo.com/v3/smtp/email',{method:'POST',headers:{'api-key':process.env.BREVO_API_KEY,'Content-Type':'application/json','Accept':'application/json'},body:JSON.stringify({sender:{name:process.env.BREVO_FROM_NAME,email:process.env.BREVO_FROM_EMAIL},to:[{email}],subject,textContent:textBody,htmlContent:htmlBody}),signal:AbortSignal.timeout(15000)});
              if(!response.ok) { const detail=(await response.text()).slice(0,1000); throw Error(`Brevo API HTTP ${response.status}: ${detail}`); }
            } else if(resendReady) {
              const response=await fetch('https://api.resend.com/emails',{method:'POST',headers:{'Authorization':`Bearer ${process.env.RESEND_API_KEY}`,'Content-Type':'application/json'},body:JSON.stringify({from:process.env.EMAIL_FROM,to:[email],subject,text:textBody,html:htmlBody}),signal:AbortSignal.timeout(15000)});
              if(!response.ok) { const detail=(await response.text()).slice(0,1000); throw Error(`Resend API HTTP ${response.status}: ${detail}`); }
            } else {
              await mailer.sendMail({from:process.env.SMTP_FROM,to:email,subject,text:textBody,html:htmlBody});
            }
          } catch (err) {
            console.error(`${brevoReady?'Brevo API':resendReady?'Resend API':'SMTP'} send failed: ${err.code || 'UNKNOWN'}${err.responseCode ? ` (${err.responseCode})` : ''}: ${err.message}`);
            db.prepare('DELETE FROM verification_codes WHERE email=?').run(email); pendingPasswords.delete(email);
            return send(res,502,{error:'Не удалось отправить письмо. Проверьте настройки почтового сервиса и попробуйте снова.'});
          }
        }
        const exposeDevCode=process.env.NODE_ENV!=='production' && !emailReady;
        return send(res,200,{message:`Код отправлен на ${email}.`,...(exposeDevCode?{devCode:code}:{})});
      }
      if(url.pathname==='/api/verify' && req.method==='POST') {
        const email=String(input.email||'').trim().toLowerCase(), code=String(input.code||'').trim();
        const row=db.prepare('SELECT * FROM verification_codes WHERE email=?').get(email), pending=pendingPasswords.get(email);
        if(!row || !pending || pending.until<Date.now() || row.expires_at<Date.now()) { db.prepare('DELETE FROM verification_codes WHERE email=?').run(email); pendingPasswords.delete(email); return send(res,400,{error:'Код истёк. Запросите новый.'}); }
        if(row.attempts>=5) { db.prepare('DELETE FROM verification_codes WHERE email=?').run(email); pendingPasswords.delete(email); return send(res,429,{error:'Слишком много попыток. Начните регистрацию заново.'}); }
        const given=await scrypt(code,process.env.CODE_PEPPER||'fauna-violet-local',32);
        if(!/^\d{6}$/.test(code) || !timingSafeEqual(given,Buffer.from(row.code_hash))) { db.prepare('UPDATE verification_codes SET attempts=attempts+1 WHERE email=?').run(email); return send(res,400,{error:'Код неверный. Проверьте письмо и попробуйте ещё раз.'}); }
        db.prepare('INSERT INTO users(email,password_hash,verified) VALUES(?,?,1)').run(email,`${pending.salt}:${pending.hash}`);
        db.prepare('DELETE FROM verification_codes WHERE email=?').run(email); pendingPasswords.delete(email);
        const token=randomBytes(32).toString('hex'); sessions.set(token,email);
        return send(res,200,{user:{email} },`fauna_session=${token}; HttpOnly; SameSite=Lax; Path=/; Max-Age=604800${process.env.NODE_ENV==='production'?'; Secure':''}`);
      }
      if(url.pathname==='/api/login' && req.method==='POST') {
        const email=String(input.email||'').trim().toLowerCase(), password=String(input.password||'');
        const user=db.prepare('SELECT * FROM users WHERE email=? AND verified=1').get(email);
        if(!user) return send(res,401,{error:'Неверная почта или пароль.'});
        const [salt,hash]=user.password_hash.split(':'), actual=await scrypt(password,salt,64);
        if(!timingSafeEqual(actual,Buffer.from(hash,'hex'))) return send(res,401,{error:'Неверная почта или пароль.'});
        const token=randomBytes(32).toString('hex'); sessions.set(token,email);
        return send(res,200,{user:{email}},`fauna_session=${token}; HttpOnly; SameSite=Lax; Path=/; Max-Age=604800${process.env.NODE_ENV==='production'?'; Secure':''}`);
      }
      if(url.pathname==='/api/me' && req.method==='GET') { const u=sessionUser(req); return send(res,200,{user:u?.verified?{email:u.email}:null}); }
      if(url.pathname==='/api/logout' && req.method==='POST') { const token=(req.headers.cookie||'').match(/(?:^|;\s*)fauna_session=([^;]+)/)?.[1]; if(token) sessions.delete(token); return send(res,200,{ok:true},'fauna_session=; HttpOnly; SameSite=Lax; Path=/; Max-Age=0'); }
      if(url.pathname==='/api/animals' && req.method==='GET') return send(res,200,{animals:animals});
      return send(res,404,{error:'Не найдено.'});
    } catch(e) { console.error(e); return send(res,500,{error:'Что-то пошло не так. Попробуйте ещё раз.'}); }
  }
  if(url.pathname==='/admin' || url.pathname==='/admin/') {
    try { const data=await readFile(resolve(root,'public','admin.html'));res.writeHead(200,{'content-type':'text/html; charset=utf-8','cache-control':'no-store','x-content-type-options':'nosniff','x-frame-options':'DENY','referrer-policy':'no-referrer','x-robots-tag':'noindex, nofollow','content-security-policy':"default-src 'self'; style-src 'self' https://fonts.googleapis.com; font-src 'self' https://fonts.gstatic.com; script-src 'self'; connect-src 'self'; img-src 'self' data:; base-uri 'none'; form-action 'self'; frame-ancestors 'none'"});return res.end(data); }
    catch { res.writeHead(404);return res.end('Not found'); }
  }
  const path=url.pathname==='/'?'/index.html':url.pathname;
  if(path.includes('..')) { res.writeHead(400); return res.end(); }
  try { const data=await readFile(resolve(root,'public',path.slice(1))); res.writeHead(200,{'content-type':mime[extname(path)]||'application/octet-stream','x-content-type-options':'nosniff','x-frame-options':'DENY','referrer-policy':'no-referrer'}); res.end(data); } catch { res.writeHead(404);res.end('Not found'); }
}
const animals=[
{id:'fox',name:'Рыжая лисица',latin:'Vulpes vulpes',group:'Лес',emoji:'🦊',color:'#d87845',image:'https://images.unsplash.com/photo-1588167056547-c183313da47c?auto=format&fit=crop&w=1200&q=85',fact:'Слышит движения мыши под снегом и точно рассчитывает прыжок.',habitat:'Леса, тундра, степи и даже окраины городов по всему Северному полушарию.',diet:'Грызуны, птицы, насекомые, ягоды и сезонные плоды.',lifespan:'Обычно 3–6 лет в природе',detail:'Рыжая лисица — один из самых приспособляемых хищников планеты. Её большие уши улавливают слабые звуки под снегом: заметив мышь, лисица делает высокий прыжок и ныряет мордой в сугроб. Длинный пушистый хвост помогает сохранять равновесие на повороте и служит тёплым укрытием во время сна. Лисицы живут в разнообразных местах — от северных лесов до пустынь — и меняют рацион в зависимости от сезона.'},
{id:'owl',name:'Полярная сова',latin:'Bubo scandiacus',group:'Арктика',emoji:'🦉',color:'#8797aa',image:'https://images.unsplash.com/photo-1670336815587-cc650a664a53?auto=format&fit=crop&w=1200&q=85',fact:'Охотится даже при дневном свете полярного лета.',habitat:'Открытая арктическая тундра Евразии и Северной Америки.',diet:'Лемминги составляют основу рациона; также зайцы и птицы.',lifespan:'Около 10 лет в природе',detail:'Полярная сова отличается от многих сов тем, что часто охотится при свете дня. Белое оперение помогает ей сливаться со снежной тундрой, а густые перья защищают от холода. Успех размножения тесно связан с численностью леммингов: когда грызунов много, самка может вырастить особенно крупный выводок. Сова молча летит низко над землёй и замечает добычу на большом расстоянии.'},
{id:'otter',name:'Речная выдра',latin:'Lutra lutra',group:'Океан',emoji:'🦦',color:'#47766b',fact:'Чувствительные усы помогают находить добычу в мутной воде.',habitat:'Чистые реки и озёра Европы и Азии, берега с густой растительностью.',diet:'Рыба, лягушки, ракообразные и водные насекомые.',lifespan:'До 10 лет в природе',detail:'Речная выдра прекрасно приспособлена к жизни у воды: её плотный мех удерживает тепло, а пальцы соединены плавательными перепонками. Во время охоты выдра использует чувствительные усы, чтобы уловить движение рыбы даже в мутной воде. Нору с несколькими входами она устраивает у берега, а чистые водоёмы и укромные прибрежные участки необходимы ей для выращивания детёнышей.'},
{id:'panda',name:'Большая панда',latin:'Ailuropoda melanoleuca',group:'Горы',emoji:'🐼',color:'#b1aaa0',fact:'Особая кость запястья помогает ловко хватать стебли бамбука.',habitat:'Горные бамбуковые леса центрального Китая.',diet:'Почти исключительно бамбук; ест много часов в день.',lifespan:'15–20 лет в природе',detail:'Несмотря на принадлежность к отряду хищных, большая панда питается почти исключительно бамбуком. Так как эта пища даёт сравнительно мало энергии, животное проводит за едой большую часть дня. Увеличенная кость запястья работает как подобие большого пальца и помогает удерживать стебли. Панды предпочитают прохладные горные леса, где есть разные виды бамбука и достаточно тихих мест для отдыха.'},
{id:'snow-leopard',name:'Снежный барс',latin:'Panthera uncia',group:'Горы',emoji:'🐆',color:'#91a5b2',image:'https://images.unsplash.com/photo-1526289636136-bce3fd37f962?auto=format&fit=crop&w=1200&q=85',fact:'Длинный хвост помогает удерживать равновесие на скалах и согревает в холод.',habitat:'Высокогорья Центральной и Южной Азии.',diet:'Горные козлы, бараны, сурки и другие животные.',lifespan:'Около 15 лет в природе',detail:'Снежный барс живёт в труднодоступных горах, где его дымчато-серая пятнистая шерсть почти сливается со скалами. Широкие лапы работают как природные снегоступы, а длинный хвост помогает балансировать во время прыжка через ущелье. Барс охотится из засады и способен преодолевать большие расстояния в поисках добычи. Сохранение горных местообитаний важно для будущего этого редкого хищника.'},
{id:'wolf',name:'Серый волк',latin:'Canis lupus',group:'Лес',emoji:'🐺',color:'#737d84',image:'https://images.unsplash.com/photo-1588167056547-c183313da47c?auto=format&fit=crop&w=1200&q=85',fact:'Вой помогает членам стаи находить друг друга на большом расстоянии.',habitat:'Леса, тундра, степи и горы Северного полушария.',diet:'Крупные копытные и более мелкие животные.',lifespan:'6–8 лет в природе',detail:'Волки живут семейными группами, где взрослые совместно заботятся о молодняке и защищают территорию. Каждый член стаи хорошо знает знакомые маршруты, а вой помогает поддерживать связь, когда животные разошлись. Волки способны долго идти за добычей и выбирают цель, исходя из ситуации. Их присутствие влияет на поведение других животных и помогает сохранять сложное равновесие экосистем.'},
{id:'elephant',name:'Африканский слон',latin:'Loxodonta africana',group:'Саванна',emoji:'🐘',color:'#9a8e7b',image:'https://images.unsplash.com/photo-1725953116569-3b2a8907bcfa?auto=format&fit=crop&w=1200&q=85',fact:'Слоны общаются низкими звуками, часть которых человек почти не слышит.',habitat:'Саванны, редколесья и леса Африки.',diet:'Травы, листья, кора, корни и плоды.',lifespan:'До 60–70 лет',detail:'Африканский слон — крупнейшее наземное животное. Хобот служит ему одновременно для дыхания, питья, общения и захвата пищи. Слоны живут семейными группами и запоминают маршруты к водопоям. Они общаются в том числе низкочастотными сигналами, которые могут распространяться далеко по земле. Разрушение путей миграции и сокращение природных территорий мешают этим гигантам находить воду и корм.'},
{id:'tiger',name:'Амурский тигр',latin:'Panthera tigris altaica',group:'Лес',emoji:'🐅',color:'#b66a38',fact:'Полосатый рисунок уникален у каждого тигра — как отпечатки пальцев.',habitat:'Хвойные и смешанные леса российского Дальнего Востока.',diet:'Олени, кабаны и другие крупные копытные.',lifespan:'10–15 лет в природе',detail:'Амурский тигр приспособлен к снежным зимам: его густой мех и широкие лапы позволяют передвигаться по холодному лесу. Полосы помогают скрываться среди теней и стволов, причём рисунок каждой особи неповторим. Тигр ведёт одиночный образ жизни и нуждается в большой территории с достаточным количеством добычи. Для его сохранения необходимы целые лесные пространства и защита животных, которыми он питается.'},
{id:'red-panda',name:'Красная панда',latin:'Ailurus fulgens',group:'Горы',emoji:'🦝',color:'#a25d39',image:'https://images.unsplash.com/photo-1714067557102-1ae9d7d9d8a4?auto=format&fit=crop&w=1000&q=85',fact:'Пушистый хвост служит одеялом, когда панда спит в прохладном лесу.',habitat:'Горные леса Гималаев и юго-западного Китая.',diet:'Бамбук, ягоды, плоды, яйца и насекомые.',lifespan:'Около 8–10 лет в природе',detail:'Красная панда — самостоятельный вид, не близкий родственник большой панды. Она ловко лазает по деревьям, а длинный пушистый хвост помогает держать равновесие и укрывать тело во время сна. Основу её пищи составляет бамбук, но в сезон она дополняет рацион плодами и насекомыми. Вырубка горных лесов разделяет её местообитание на небольшие участки, поэтому непрерывные лесные коридоры особенно важны.'},
{id:'polar-bear',name:'Белый медведь',latin:'Ursus maritimus',group:'Арктика',emoji:'🐻‍❄️',color:'#b9c2c9',fact:'Под густой шерстью у него чёрная кожа, которая поглощает тепло солнца.',habitat:'Морской лёд и арктические побережья.',diet:'В основном тюлени; иногда птицы, яйца и падаль.',lifespan:'Около 25 лет в природе',detail:'Белый медведь большую часть жизни проводит рядом с морским льдом. По запаху он может обнаружить тюленя у дыхательной лунки и долго ждать подходящего момента для охоты. Светлая шерсть состоит из полупрозрачных волосков, а кожа под ней тёмная. Состояние морского льда напрямую влияет на возможность медведя добыть пищу и вырастить потомство.'},
{id:'orca',name:'Косатка',latin:'Orcinus orca',group:'Океан',emoji:'🐋',color:'#465467',fact:'У каждой семьи косаток есть свои звуковые сигналы и привычки.',habitat:'Океаны от полярных вод до тропических морей.',diet:'Рыба, кальмары или морские млекопитающие — зависит от группы.',lifespan:'Самки могут жить более 50 лет',detail:'Косатки — высокоразвитые зубатые киты, которые живут семейными группами. Разные популяции могут специализироваться на разной добыче и использовать собственные приёмы охоты. Детёныши долго остаются рядом с матерью и учатся у старших членов семьи. Их свисты и щелчки помогают общаться и ориентироваться под водой, где звуковые волны распространяются далеко.'},
{id:'blue-whale',name:'Синий кит',latin:'Balaenoptera musculus',group:'Океан',emoji:'🐳',color:'#466a8b',fact:'Это крупнейшее животное, когда-либо жившее на Земле.',habitat:'Открытые воды мирового океана.',diet:'Крошечные криль и другие мелкие ракообразные.',lifespan:'Около 80–90 лет',detail:'Синий кит может быть длиннее нескольких городских автобусов, но питается крошечным крилем. Он набирает воду с рачками в огромный рот и процеживает её через пластины китового уса. Во время сезонных перемещений киты проходят тысячи километров между местами кормления и размножения. Их низкие песни могут распространяться на большие расстояния под водой.'},
{id:'monarch',name:'Бабочка монарх',latin:'Danaus plexippus',group:'Лес',emoji:'🦋',color:'#c4793e',fact:'Некоторые монархи совершают многотысячекилометровые сезонные перелёты.',habitat:'Луга, сады и лесные опушки Северной Америки.',diet:'Нектар цветов; гусеницы питаются листьями ваточника.',lifespan:'От нескольких недель до месяцев',detail:'Бабочка монарх известна дальними миграциями: несколько поколений участвуют в сезонном перемещении между севером и югом Северной Америки. Яркая окраска предупреждает хищников о неприятном вкусе, который гусеницы получают благодаря растениям ваточника. Для успешного путешествия монархам нужны места для отдыха и цветы с нектаром на пути.'},
{id:'capybara',name:'Капибара',latin:'Hydrochoerus hydrochaeris',group:'Океан',emoji:'🦫',color:'#927963',fact:'Капибара отлично плавает и может прятаться под водой от опасности.',habitat:'Берега рек и болот Южной Америки.',diet:'Травы, водные растения и мягкая зелень.',lifespan:'Около 8–10 лет',detail:'Капибара — крупнейший современный грызун, но большую часть времени проводит рядом с водой. Перепонки между пальцами помогают плавать, а глаза и ноздри расположены высоко, поэтому она может наблюдать за берегом, оставаясь почти полностью погружённой. Капибары живут группами и часто отдыхают в тени в самое жаркое время дня.'},
{id:'fennec',name:'Фенек',latin:'Vulpes zerda',group:'Саванна',emoji:'🦊',color:'#c7a06e',fact:'Большие уши помогают отводить тепло и улавливать звуки под песком.',habitat:'Песчаные пустыни Северной Африки.',diet:'Насекомые, грызуны, ящерицы, яйца и плоды.',lifespan:'Около 10 лет',detail:'Фенек — самая маленькая лисица. Его крупные уши не только улавливают шорохи добычи, но и помогают отдавать лишнее тепло. Днём зверёк отдыхает в норе, а ночью выходит на охоту, когда пустыня остывает. Пушистые подошвы защищают лапы от горячего песка, а норы могут иметь несколько ходов и комнат.'},
{id:'octopus',name:'Осьминог',latin:'Octopus vulgaris',group:'Океан',emoji:'🐙',color:'#9a5c68',fact:'Осьминог меняет цвет и узор кожи, чтобы сливаться с окружением.',habitat:'Прибрежные моря и коралловые рифы.',diet:'Крабы, моллюски, рыба и другие небольшие морские животные.',lifespan:'Обычно 1–2 года',detail:'Осьминог способен менять цвет и текстуру кожи, маскируясь среди камней и кораллов. Большая часть его нервных клеток находится в щупальцах, которые могут исследовать предметы почти самостоятельно. Осьминоги решают задачи, открывают контейнеры и используют укрытия. Мягкое тело позволяет им пролезать в очень узкие щели.'},
{id:'axolotl',name:'Аксолотль',latin:'Ambystoma mexicanum',group:'Океан',emoji:'🦎',color:'#cc7f99',fact:'В отличие от большинства амфибий, он обычно всю жизнь остаётся водным.',habitat:'Пресноводные каналы и озёра в районе Мехико.',diet:'Черви, личинки насекомых, мелкие ракообразные и рыба.',lifespan:'Около 10–15 лет в неволе',detail:'Аксолотль — амфибия, которая сохраняет юношеские черты и жабры во взрослом возрасте. Он известен способностью восстанавливать повреждённые ткани и даже некоторые части конечностей. В природе аксолотль встречается в небольшом числе водоёмов центральной Мексики. Загрязнение и изменение водных каналов поставили его под угрозу, поэтому чистая пресная вода для вида жизненно важна.'},
{id:'penguin',name:'Императорский пингвин',latin:'Aptenodytes forsteri',group:'Арктика',emoji:'🐧',color:'#7c8996',fact:'Самец согревает яйцо на лапах в самый холодный сезон Антарктиды.',habitat:'Морские льды и побережье Антарктиды.',diet:'Рыба, кальмары и криль.',lifespan:'Около 15–20 лет',detail:'Императорский пингвин размножается в антарктическую зиму. После откладывания яйца самка отправляется кормиться, а самец несколько недель удерживает яйцо на лапах под тёплой складкой кожи. Пингвины собираются в плотные группы, меняясь местами от края к центру, чтобы пережить сильный ветер. В воде их крылья работают как ласты, позволяя быстро преследовать рыбу.'},
{id:'jaguar',name:'Ягуар',latin:'Panthera onca',group:'Лес',emoji:'🐆',color:'#a57845',fact:'Узор из розеток помогает ягуару скрываться в пятнистой тени тропического леса.',habitat:'Тропические леса, болота и саванны Центральной и Южной Америки.',diet:'Капибары, кайманы, олени, рыба и черепахи.',lifespan:'12–15 лет в природе',detail:'Ягуар — мощный хищник, который хорошо плавает и часто охотится у воды. Его пятнистая шкура маскирует среди листвы, а сильные челюсти позволяют справляться с разнообразной добычей. Ягуар обычно охотится в одиночку и занимает обширную территорию. Сохранение лесных коридоров помогает отдельным популяциям оставаться связанными между собой.'},
{id:'sloth',name:'Трёхпалый ленивец',latin:'Bradypus variegatus',group:'Лес',emoji:'🦥',color:'#73836c',fact:'Медленный обмен веществ помогает экономить энергию на листьях.',habitat:'Влажные тропические леса Центральной и Южной Америки.',diet:'Листья, молодые побеги и иногда плоды.',lifespan:'Около 20–30 лет',detail:'Ленивец большую часть жизни проводит на деревьях, крепко цепляясь длинными когтями за ветви. Листья перевариваются медленно и дают мало энергии, поэтому зверёк двигается экономно и отдыхает часами. Иногда ленивец спускается на землю, чтобы сменить дерево или выполнить свои естественные потребности. Влажный лес с непрерывным древесным покровом — его главный дом.'},
{id:'giraffe',name:'Жираф',latin:'Giraffa camelopardalis',group:'Саванна',emoji:'🦒',color:'#bd8a49',fact:'Длинный язык помогает срывать листья с колючих ветвей акации.',habitat:'Саванны и редколесья Африки.',diet:'Листья и побеги деревьев, особенно акаций.',lifespan:'Около 20–25 лет',detail:'Жираф — самое высокое наземное животное. Его длинная шея помогает дотягиваться до листьев, недоступных многим травоядным. Несмотря на длину шеи, у жирафа столько же шейных позвонков, сколько у человека, но они намного крупнее. Пятна создают индивидуальный узор и помогают регулировать теплообмен, а длинный тёмный язык защищён от колючек.'},
{id:'lynx',name:'Евразийская рысь',latin:'Lynx lynx',group:'Лес',emoji:'🐈',color:'#77746f',fact:'Кисточки на ушах помогают улавливать направление звука в лесу.',habitat:'Леса и горы Европы и Азии.',diet:'Зайцы, косули, птицы и мелкие млекопитающие.',lifespan:'Около 10–15 лет',detail:'Рысь — скрытный лесной хищник с коротким хвостом и широкими лапами. Зимой лапы работают как снегоступы, а острый слух помогает заметить добычу среди густых деревьев. Рысь охотится из засады, бесшумно приближаясь к цели. Ей нужны большие участки леса с укрытиями и достаточным количеством животных-жертв.'},
{id:'hummingbird',name:'Колибри',latin:'Trochilidae',group:'Лес',emoji:'🐦',color:'#4d8b77',fact:'Колибри может зависать у цветка, быстро взмахивая крыльями.',habitat:'Леса, горы и сады Америки.',diet:'Нектар цветов и мелкие насекомые.',lifespan:'В среднем 3–5 лет',detail:'Колибри — крошечные птицы с очень быстрыми крыльями. Они умеют зависать в воздухе и летать назад, пока собирают нектар длинным языком. Высокая активность требует большого количества энергии, поэтому колибри регулярно посещают множество цветов. Пыльца переносится вместе с птицей, делая её важным участником опыления растений.'},
{id:'turtle',name:'Зелёная морская черепаха',latin:'Chelonia mydas',group:'Океан',emoji:'🐢',color:'#4f8171',fact:'Самки возвращаются откладывать яйца на пляжи, где сами появились на свет.',habitat:'Тропические и субтропические океаны; гнездовые пляжи.',diet:'Молодые едят разнообразную пищу, взрослые часто питаются морскими травами.',lifespan:'Может жить более 60 лет',detail:'Зелёная морская черепаха мигрирует между местами кормления и пляжами, где откладывает яйца. Взрослые особи часто пасутся на подводных лугах морской травы, помогая поддерживать здоровье прибрежных экосистем. Черепашата вылупляются ночью и самостоятельно направляются к морю. Световое загрязнение пляжей может сбить их с пути, поэтому тёмные участки побережья особенно важны.'}
];
const server=http.createServer(route); server.listen(Number(process.env.PORT||3000),'0.0.0.0',()=>console.log(`Fauna Violet: http://localhost:${process.env.PORT||3000} (${brevoReady?'Brevo API enabled':resendReady?'Resend API enabled':smtpReady?'SMTP email enabled':process.env.NODE_ENV==='production'?'email not configured':'development email mode'})`));
