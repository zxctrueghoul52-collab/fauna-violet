import http from 'node:http';
import { readFile } from 'node:fs/promises';
import { mkdirSync } from 'node:fs';
import { resolve, extname } from 'node:path';
import { randomInt, randomBytes, scrypt as scryptCb, timingSafeEqual } from 'node:crypto';
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
CREATE TABLE IF NOT EXISTS verification_codes (email TEXT PRIMARY KEY, code_hash TEXT NOT NULL, expires_at INTEGER NOT NULL, attempts INTEGER NOT NULL DEFAULT 0);`);
const sessions = new Map();
const pendingPasswords = new Map();
const smtpReady = !!(process.env.SMTP_HOST && process.env.SMTP_USER && process.env.SMTP_PASS && process.env.SMTP_FROM);
const resendReady = !!(process.env.RESEND_API_KEY && process.env.EMAIL_FROM);
const brevoReady = !!(process.env.BREVO_API_KEY && process.env.BREVO_FROM_EMAIL && process.env.BREVO_FROM_NAME);
const emailReady = brevoReady || resendReady || smtpReady;
const mailer = smtpReady ? nodemailer.createTransport({ host: process.env.SMTP_HOST, port: Number(process.env.SMTP_PORT || 587), secure: process.env.SMTP_SECURE === 'true', connectionTimeout: 10000, greetingTimeout: 10000, socketTimeout: 20000, auth: { user: process.env.SMTP_USER, pass: process.env.SMTP_PASS } }) : null;
const mime = { '.html':'text/html; charset=utf-8', '.css':'text/css; charset=utf-8', '.js':'text/javascript; charset=utf-8', '.svg':'image/svg+xml' };

function send(res, status, data, cookie='') { res.writeHead(status, { 'content-type':'application/json; charset=utf-8', 'set-cookie': cookie, 'cache-control':'no-store' }); res.end(JSON.stringify(data)); }
async function body(req) { let s=''; for await (const c of req) { s+=c; if (s.length>12000) throw Error('too large'); } return JSON.parse(s || '{}'); }
function emailOk(x) { return typeof x==='string' && x.length<=254 && /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(x); }
function sessionUser(req) { const raw=(req.headers.cookie||'').split(';').map(x=>x.trim()).find(x=>x.startsWith('fauna_session='))?.split('=')[1]; const email=raw && sessions.get(raw); return email ? db.prepare('SELECT id,email,verified FROM users WHERE email=?').get(email) : null; }
async function route(req,res) {
  const url=new URL(req.url,'http://localhost');
  if (url.pathname.startsWith('/api/')) {
    try {
      const input=['POST'].includes(req.method) ? await body(req) : {};
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
      if(url.pathname==='/api/animals' && req.method==='GET') { const u=sessionUser(req); if(!u?.verified) return send(res,401,{error:'Войдите, чтобы открыть полный путеводитель.'}); return send(res,200,{animals:animals}); }
      return send(res,404,{error:'Не найдено.'});
    } catch(e) { console.error(e); return send(res,500,{error:'Что-то пошло не так. Попробуйте ещё раз.'}); }
  }
  const path=url.pathname==='/'?'/index.html':url.pathname;
  if(path.includes('..')) { res.writeHead(400); return res.end(); }
  try { const data=await readFile(resolve(root,'public',path.slice(1))); res.writeHead(200,{'content-type':mime[extname(path)]||'application/octet-stream'}); res.end(data); } catch { res.writeHead(404);res.end('Not found'); }
}
const animals=[
{id:'fox',name:'Рыжая лисица',latin:'Vulpes vulpes',group:'Лесные жители',emoji:'🦊',color:'#ffc18c',fact:'Лисицы слышат писк мыши под толстым слоем снега и могут определить его положение по звуку.',habitat:'От тундры до пустынь и городских окраин. Лисицы освоили самые разные ландшафты.',diet:'Грызуны, птицы, насекомые, ягоды и другие небольшие животные.',lifespan:'3–7 лет в природе',detail:'Лисица меняет способ охоты в зависимости от сезона: зимой находит добычу под снегом по слуху, а летом дополнительно ест ягоды и насекомых. Хвост помогает ей балансировать в прыжке и согреваться во время отдыха.'},
{id:'owl',name:'Полярная сова',latin:'Bubo scandiacus',group:'Птицы севера',emoji:'🦉',color:'#c9c4ff',fact:'Белоснежное оперение полярной совы помогает ей оставаться почти незаметной среди снежной тундры.',habitat:'Арктические тундры Евразии и Северной Америки.',diet:'В основном лемминги; также зайцы, птицы и другая мелкая добыча.',lifespan:'Около 10 лет в природе',detail:'Полярная сова охотится и днём, когда долгий полярный день освещает тундру. Численность её потомства зависит от количества леммингов: в богатые добычей годы сова откладывает больше яиц.'},
{id:'otter',name:'Речная выдра',latin:'Lutra lutra',group:'Обитатели рек',emoji:'🦦',color:'#9ee5d1',fact:'Усы выдры улавливают движение воды и помогают находить рыбу даже в мутной реке.',habitat:'Чистые реки и озёра Европы и Азии с берегами, где можно устроить укрытие.',diet:'Рыба, ракообразные, лягушки и другие небольшие водные животные.',lifespan:'До 10 лет в природе',detail:'Выдра проводит много времени в воде, но отдыхает и выращивает детёнышей в норе на берегу. Чистые водоёмы и густая прибрежная растительность особенно важны для её жизни.'},
{id:'panda',name:'Большая панда',latin:'Ailuropoda melanoleuca',group:'Жители гор',emoji:'🐼',color:'#d8c8ff',fact:'У панды есть увеличенная кость запястья — она работает как дополнительный «палец» для хватания бамбука.',habitat:'Горные бамбуковые леса центрального Китая.',diet:'Почти исключительно бамбук — до многих килограммов ежедневно.',lifespan:'15–20 лет в природе',detail:'Большая панда относится к хищным, но приспособилась питаться бамбуком. Чтобы получить достаточно энергии, она ест большую часть дня и выбирает разные части растения по сезону.'}
];
const server=http.createServer(route); server.listen(Number(process.env.PORT||3000),'0.0.0.0',()=>console.log(`Fauna Violet: http://localhost:${process.env.PORT||3000} (${brevoReady?'Brevo API enabled':resendReady?'Resend API enabled':smtpReady?'SMTP email enabled':process.env.NODE_ENV==='production'?'email not configured':'development email mode'})`));
