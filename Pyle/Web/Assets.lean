import Pyle.Http.Message

/-!
# The script and the stylesheet

Served from `/assets/pyle.js` and `/assets/pyle.css`, out of strings in this
file, so that the binary is the whole deployment and the Content Security
Policy can stay `script-src 'self'; style-src 'self'` with nothing inline.
There is no framework and no third-party code: the script is a few hundred
lines that turn base64url into `ArrayBuffer`s and back, call
`navigator.credentials`, and post JSON to the endpoints of `Pyle.SignIn` and
`Pyle.Account`.

What the script relies on, and the Lean side provides:

* `body[data-page]` is `signin`, `account`, `add`, `add-app`,
  `add-password`, `add-recovery`, `invite` or `message`; the sign-in page adds
  `data-mode` (`signin` or `stepup`), `data-return`, a return address
  `SignIn.safeReturn` has already accepted, and `data-acr`, the level the
  sign-in must reach, which the script passes on to the endpoints; the
  authenticator-app page adds `data-pending`, the sealed new secret; the
  invitation page adds `data-token`.
* The element ids each page's script looks up are the ones the page writes
  (`Pyle.Web.Pages`), and the JSON members it reads and sends are the ones
  the endpoints document.
* After a sign-in the script goes to the `redirect` the server answered with,
  never to an address of its own: the server is where `return` is checked.
-/

namespace Pyle
namespace Web

open Http

/-- `/assets/pyle.js`. -/
def script : String := r##"// pyle: the sign-in, account and invitation pages.
// No framework and no third-party code; served under script-src 'self'.
'use strict';

// base64url without padding <-> ArrayBuffer, as every binary value travels.
function b64uToBuf(s) {
  let t = s.replace(/-/g, '+').replace(/_/g, '/');
  while (t.length % 4 !== 0) t += '=';
  const bin = atob(t);
  const bytes = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
  return bytes.buffer;
}

function bufToB64u(buf) {
  const bytes = new Uint8Array(buf);
  let bin = '';
  for (let i = 0; i < bytes.length; i++) bin += String.fromCharCode(bytes[i]);
  return btoa(bin).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}

function say(message) {
  const el = document.getElementById('status');
  if (el) el.textContent = message;
}

function on(id, event, handler) {
  const el = document.getElementById(id);
  if (el) el.addEventListener(event, handler);
}

// A field's value: trimmed, except a password, which is taken as typed.
function value(id) {
  const el = document.getElementById(id);
  return el ? el.value.trim() : '';
}

function rawValue(id) {
  const el = document.getElementById(id);
  return el ? el.value : '';
}

async function post(url, body) {
  const res = await fetch(url, {
    method: 'POST',
    credentials: 'same-origin',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body || {}),
  });
  let data = {};
  if (res.status !== 204) {
    try { data = await res.json(); } catch (e) { data = {}; }
  }
  return { ok: res.ok, status: res.status, data: data };
}

function describe(res) {
  const d = res.data || {};
  if (d.error === 'second_factor_required') {
    return 'This authenticator needs a second factor: fill in a code or your password, ' +
      'then try again.';
  }
  return d.error_description || d.error || ('The request failed (' + res.status + ').');
}

function failed(e) {
  if (e && e.name === 'NotAllowedError') say('The authenticator was dismissed or timed out.');
  else say(e && e.message ? e.message : String(e));
}

function descriptors(list) {
  return (list || []).map(function (c) {
    const d = { type: c.type, id: b64uToBuf(c.id) };
    if (c.transports) d.transports = c.transports;
    return d;
  });
}

// The server's options, with the binary fields as ArrayBuffers.
function requestOptions(o) {
  return {
    challenge: b64uToBuf(o.challenge),
    rpId: o.rpId,
    timeout: o.timeout,
    userVerification: o.userVerification,
    allowCredentials: descriptors(o.allowCredentials),
  };
}

function creationOptions(o) {
  return {
    challenge: b64uToBuf(o.challenge),
    rp: o.rp,
    user: { id: b64uToBuf(o.user.id), name: o.user.name, displayName: o.user.displayName },
    pubKeyCredParams: o.pubKeyCredParams,
    timeout: o.timeout,
    attestation: o.attestation,
    authenticatorSelection: o.authenticatorSelection,
    excludeCredentials: descriptors(o.excludeCredentials),
  };
}

// What the browser hands back, with the binary fields as base64url.
function assertionJson(cred) {
  const r = cred.response;
  return {
    id: bufToB64u(cred.rawId),
    clientDataJSON: bufToB64u(r.clientDataJSON),
    authenticatorData: bufToB64u(r.authenticatorData),
    signature: bufToB64u(r.signature),
    userHandle: r.userHandle ? bufToB64u(r.userHandle) : null,
  };
}

function registrationJson(cred) {
  const r = cred.response;
  return {
    id: bufToB64u(cred.rawId),
    clientDataJSON: bufToB64u(r.clientDataJSON),
    attestationObject: bufToB64u(r.attestationObject),
    transports: typeof r.getTransports === 'function' ? r.getTransports() : [],
  };
}

async function getAssertion(beginUrl, beginBody) {
  const begin = await post(beginUrl, beginBody);
  if (!begin.ok) throw new Error(describe(begin));
  say('Waiting for your authenticator…');
  const cred = await navigator.credentials.get({ publicKey: requestOptions(begin.data) });
  if (!cred) throw new Error('No authenticator was used.');
  return assertionJson(cred);
}

async function createCredential(options) {
  say('Waiting for your authenticator…');
  const cred = await navigator.credentials.create({ publicKey: creationOptions(options) });
  if (!cred) throw new Error('No authenticator was registered.');
  return registrationJson(cred);
}

// Post a sign-in and, if it succeeded, go where the server says.
async function finish(url, body) {
  const res = await post(url, body);
  if (!res.ok) throw new Error(describe(res));
  window.location.assign(res.data.redirect);
}

function secondFactors() {
  return { totp: value('totp'), recovery: value('recovery'), password: rawValue('password') };
}

// The sign-in page, which also serves step-up.
function setupSignIn(body) {
  const ret = body.dataset.return || '/account';
  const acr = body.dataset.acr || 'mfa';
  const stepUp = body.dataset.mode === 'stepup';
  const beginUrl = stepUp ? '/signin/stepup/begin' : '/signin/webauthn/begin';
  const finishUrl = stepUp ? '/signin/stepup/finish' : '/signin/webauthn/finish';
  on('passkey', 'click', async function () {
    try {
      const credential = await getAssertion(beginUrl, {});
      await finish(finishUrl, { credential: credential, return: ret, acr: acr });
    } catch (e) { failed(e); }
  });
  on('security-key', 'click', async function () {
    const name = value('name');
    if (!stepUp && !name) { say('Enter your user name first.'); return; }
    try {
      const credential = await getAssertion(beginUrl,
        stepUp ? { userVerification: 'discouraged' } : { name: name });
      await finish(finishUrl,
        Object.assign({ credential: credential, return: ret, acr: acr }, secondFactors()));
    } catch (e) { failed(e); }
  });
  on('other', 'submit', async function (ev) {
    ev.preventDefault();
    try {
      await finish('/signin/codes',
        Object.assign({ name: value('name'), return: ret, acr: acr }, secondFactors()));
    } catch (e) { failed(e); }
  });
}

// The account pages.  A change that needs a recent sign-in answers 403
// step_up_required; then confirm with an authenticator and try once more.
function here() {
  return window.location.pathname;
}

async function stepUpHere() {
  const credential = await getAssertion('/signin/stepup/begin', {});
  const res = await post('/signin/stepup/finish', { credential: credential, return: here() });
  if (!res.ok) throw new Error(describe(res));
}

async function act(url, body) {
  let res = await post(url, body);
  if (res.status === 403 && res.data.error === 'step_up_required') {
    say('Confirm it is you first.');
    try {
      await stepUpHere();
    } catch (e) {
      // No authenticator at hand that verifies the user: the sign-in page
      // offers the other ways, and comes back here.  The authenticator-app
      // page then has a new key; remember to say so, and the name typed.
      if (document.body.dataset.page === 'add-app') {
        try { window.sessionStorage.setItem('pyle-rescan', value('app-name')); } catch (s) { }
      }
      window.location.assign('/signin?return=' + encodeURIComponent(here()) + '&max_age=0');
      throw new Error('Confirm it is you on the sign-in page.');
    }
    res = await post(url, body);
  }
  if (!res.ok) throw new Error(describe(res));
  return res.data;
}

async function accountAction(button) {
  const action = button.dataset.action;
  try {
    if (action === 'rename') {
      const name = window.prompt('A new name for this passkey or security key');
      if (!name) return;
      await act('/account/authenticators/rename', { id: button.dataset.id, name: name });
    } else if (action === 'remove') {
      if (!window.confirm('Remove this passkey or security key?')) return;
      await act('/account/authenticators/remove', { id: button.dataset.id });
    } else if (action === 'totp-rename') {
      const name = window.prompt('A new name for this authenticator app');
      if (!name) return;
      await act('/account/totp/rename', { id: Number(button.dataset.id), name: name });
    } else if (action === 'totp-remove') {
      if (!window.confirm('Remove this authenticator app? Its codes stop working.')) return;
      await act('/account/totp/remove', { id: Number(button.dataset.id) });
    } else if (action === 'password-remove') {
      if (!window.confirm('Remove the password?')) return;
      await act('/account/password/remove', {});
    } else if (action === 'end-session') {
      await act('/account/sessions/end', { handle: button.dataset.handle });
      if (button.dataset.current === 'true') { window.location.assign('/signin'); return; }
    } else {
      return;
    }
    window.location.assign('/account');
  } catch (e) { failed(e); }
}

function setupAccount() {
  document.querySelectorAll('button[data-action]').forEach(function (b) {
    b.addEventListener('click', function () { accountAction(b); });
  });
  on('sign-out', 'click', async function () {
    await post('/logout', {});
    window.location.assign('/signin');
  });
}

// The choice of what to add: a passkey or a security key is registered
// right here, with the options for its kind.
function setupAdd() {
  document.querySelectorAll('button[data-kind]').forEach(function (b) {
    b.addEventListener('click', async function () {
      const kind = b.dataset.kind;
      try {
        const options = await act('/account/authenticators/register/begin', { kind: kind });
        const credential = await createCredential(options);
        await act('/account/authenticators/register/finish',
          { credential: credential, kind: kind });
        window.location.assign('/account?added=' + encodeURIComponent(kind));
      } catch (e) { failed(e); }
    });
  });
}

// Adding an authenticator app: the page carries the new secret, sealed, and
// the first code from the app stores it under the name given.
function setupAddApp(body) {
  let rescan = null;
  try {
    rescan = window.sessionStorage.getItem('pyle-rescan');
    window.sessionStorage.removeItem('pyle-rescan');
  } catch (e) { rescan = null; }
  const notice = document.getElementById('rescan');
  const name = document.getElementById('app-name');
  if (rescan !== null && notice && name) {
    notice.hidden = false;
    if (rescan) name.value = rescan;
  }
  on('totp-confirm', 'click', async function () {
    try {
      await act('/account/totp/confirm', { pending: body.dataset.pending,
        code: value('totp-code'), name: value('app-name') });
      window.location.assign('/account?added=app');
    } catch (e) { failed(e); }
  });
}

function setupAddPassword() {
  on('password-set', 'click', async function () {
    try {
      await act('/account/password', { password: rawValue('new-password') });
      window.location.assign('/account?added=password');
    } catch (e) { failed(e); }
  });
}

// New recovery codes, shown once.  Replacing codes asks first.
function setupAddRecovery() {
  on('recovery-generate', 'click', async function () {
    const button = document.getElementById('recovery-generate');
    if (button.dataset.replace === 'true' &&
        !window.confirm('New codes replace the old ones. Continue?')) return;
    try {
      const data = await act('/account/recovery-codes', {});
      const list = document.getElementById('recovery-list');
      list.textContent = '';
      data.codes.forEach(function (c) {
        const li = document.createElement('li');
        li.textContent = c;
        list.appendChild(li);
      });
      list.hidden = false;
      button.hidden = true;
      document.getElementById('recovery-done').hidden = false;
      say('Write these codes down now: they are not shown again.');
    } catch (e) { failed(e); }
  });
}

// The invitation page: register the first passkey, say that it worked, and
// leave signing in with it to the sign-in page, as a step of its own.
function setupInvite(body) {
  const base = '/invite/' + encodeURIComponent(body.dataset.token);
  on('create', 'click', async function () {
    try {
      const begin = await post(base + '/begin', {});
      if (!begin.ok) throw new Error(describe(begin));
      const credential = await createCredential(begin.data);
      const res = await post(base + '/finish',
        { credential: credential, name: value('passkey-name') });
      if (!res.ok) throw new Error(describe(res));
      document.getElementById('invite-form').hidden = true;
      document.getElementById('invite-done').hidden = false;
      say('Your passkey is registered.');
      document.getElementById('continue-signin').focus();
    } catch (e) { failed(e); }
  });
  on('continue-signin', 'click', function () {
    window.location.assign('/signin?return=%2Faccount');
  });
}

document.addEventListener('DOMContentLoaded', function () {
  const body = document.body;
  if (body.dataset.page !== 'message' && !window.PublicKeyCredential) {
    say('This browser does not support passkeys.');
  }
  if (body.dataset.page === 'signin') setupSignIn(body);
  else if (body.dataset.page === 'account') setupAccount();
  else if (body.dataset.page === 'add') setupAdd();
  else if (body.dataset.page === 'add-app') setupAddApp(body);
  else if (body.dataset.page === 'add-password') setupAddPassword();
  else if (body.dataset.page === 'add-recovery') setupAddRecovery();
  else if (body.dataset.page === 'invite') setupInvite(body);
});"##

/-- `/assets/pyle.css`. -/
def stylesheet : String := r##"/* pyle: plain, readable, accessible. */
:root {
  color-scheme: light dark;
  --fg: #1d1f21;
  --bg: #fdfdfc;
  --muted: #5c6166;
  --accent: #2456a6;
  --notice: #fff4d6;
  --line: #d6d8db;
}
@media (prefers-color-scheme: dark) {
  :root {
    --fg: #e6e6e3;
    --bg: #17191b;
    --muted: #a3a7ab;
    --accent: #8fb3ff;
    --notice: #3a3220;
    --line: #3a3d41;
  }
}
* { box-sizing: border-box; }
[hidden] { display: none !important; }
body {
  margin: 0;
  font: 1rem/1.5 system-ui, -apple-system, "Segoe UI", sans-serif;
  color: var(--fg);
  background: var(--bg);
}
main { max-width: 40rem; margin: 0 auto; padding: 2rem 1rem 4rem; }
a { color: var(--accent); }
h1 { font-size: 1.6rem; margin: 0 0 1.5rem; }
h2 { font-size: 1.15rem; margin: 2rem 0 0.75rem; border-top: 1px solid var(--line); padding-top: 1.25rem; }
label { display: block; margin: 0.75rem 0 0.25rem; font-weight: 600; }
input {
  width: 100%;
  padding: 0.55rem 0.6rem;
  font: inherit;
  color: inherit;
  background: transparent;
  border: 1px solid var(--line);
  border-radius: 0.35rem;
}
button {
  margin: 0.75rem 0.5rem 0 0;
  padding: 0.55rem 1rem;
  font: inherit;
  color: var(--bg);
  background: var(--accent);
  border: 0;
  border-radius: 0.35rem;
  cursor: pointer;
}
button.secondary, li button {
  color: var(--accent);
  background: transparent;
  border: 1px solid var(--accent);
  padding: 0.25rem 0.6rem;
  margin-top: 0.25rem;
}
/* A link that does what a button does. */
a.button {
  display: inline-block;
  padding: 0.55rem 1rem;
  color: var(--bg);
  background: var(--accent);
  border: 1px solid var(--accent);
  border-radius: 0.35rem;
  text-decoration: none;
  font-weight: 600;
}
a.button.secondary { color: var(--accent); background: transparent; font-weight: 400; }
button.small, a.button.small {
  margin: 0;
  padding: 0.25rem 0.6rem;
  font-size: 0.9rem;
  font-weight: 400;
  color: var(--accent);
  background: transparent;
  border: 1px solid var(--accent);
}
:focus-visible { outline: 3px solid var(--accent); outline-offset: 2px; }
ul.items { list-style: none; padding: 0; margin: 0; }
ul.items li {
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  align-items: center;
  gap: 0.5rem;
  padding: 0.6rem 0;
  border-bottom: 1px solid var(--line);
}
.meta, .hint { color: var(--muted); font-size: 0.9rem; }
.notice { background: var(--notice); padding: 0.75rem 1rem; border-radius: 0.35rem; }
code, ol.codes { font-family: ui-monospace, "SFMono-Regular", Menlo, monospace; word-break: break-all; }
#status { min-height: 1.5rem; font-weight: 600; }
.visually-hidden {
  position: absolute;
  width: 1px;
  height: 1px;
  overflow: hidden;
  clip: rect(0 0 0 0);
  white-space: nowrap;
}
/* The account pages: wider, for the table of sign-in methods. */
body[data-page="account"] main, body[data-page^="add"] main { max-width: 46rem; }
a.back { display: inline-block; margin-bottom: 0.75rem; }
.page-head {
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  align-items: baseline;
  gap: 0.5rem;
  margin-bottom: 1.5rem;
}
.page-head h1 { margin: 0; }
.page-head .signed-in { margin: 0; }
a.nudge-link { font-weight: 600; }
.lead { color: var(--muted); margin: 0 0 1.5rem; }
.signed-in { color: var(--muted); }
.protection {
  display: flex;
  flex-wrap: wrap;
  gap: 0.75rem;
  align-items: center;
  justify-content: space-between;
  padding: 0.9rem 1rem;
  border: 1px solid var(--line);
  border-radius: 0.35rem;
}
.protection.notice { border-color: transparent; }
.protection-text { flex: 1 1 22rem; }
.protection p { margin: 0 0 0.35rem; }
.protection p:last-child { margin-bottom: 0; }
.protection-title { font-weight: 600; }
.section-head {
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  align-items: center;
  gap: 0.75rem;
  margin-top: 2rem;
  border-top: 1px solid var(--line);
  padding-top: 1.25rem;
}
.section-head h2 { margin: 0; border: 0; padding: 0; }
/* On a narrow screen the table scrolls sideways in its box, not the page. */
.table-scroll { overflow-x: auto; margin-top: 1rem; }
table.methods { width: 100%; min-width: 34rem; border-collapse: collapse; font-size: 0.95rem; }
table.methods th, table.methods td { text-align: left; vertical-align: top; padding: 0.6rem 0.5rem; }
table.methods th:first-child, table.methods td:first-child { padding-left: 0; }
table.methods thead th { padding-top: 0.4rem; padding-bottom: 0.4rem; }
table.methods tbody tr { border-bottom: 1px solid var(--line); }
table.methods th[scope="colgroup"] { padding: 1.25rem 0 0.35rem; font-size: 1rem; }
table.methods th[scope="colgroup"] .meta { font-weight: 400; font-size: 0.85rem; }
table.methods td .meta { font-size: 0.85rem; }
table.methods td.actions { text-align: right; white-space: nowrap; padding-right: 0; }
/* The choices of what to add, each a card. */
.choices { display: flex; flex-direction: column; gap: 0.75rem; }
.choice {
  display: flex;
  flex-wrap: wrap;
  gap: 0.5rem 1rem;
  align-items: center;
  justify-content: space-between;
  width: 100%;
  margin: 0;
  padding: 1rem 1.1rem;
  font: inherit;
  text-align: left;
  text-decoration: none;
  color: var(--fg);
  background: transparent;
  border: 1px solid var(--line);
  border-radius: 0.5rem;
  cursor: pointer;
}
.choice.recommended { border: 2px solid var(--accent); }
.choice-text { flex: 1 1 22rem; }
.choice-title { display: block; font-weight: 600; font-size: 1.05rem; }
.choice-desc { display: block; color: var(--muted); font-size: 0.95rem; }
.choice-go { font-weight: 600; color: var(--accent); }
.badge {
  margin-left: 0.35rem;
  padding: 0.1rem 0.55rem;
  font-size: 0.8rem;
  font-weight: 600;
  vertical-align: middle;
  color: var(--bg);
  background: var(--accent);
  border-radius: 1rem;
}
.enrol { display: flex; flex-wrap: wrap; gap: 1.5rem; align-items: flex-start; }
.enrol-key { flex: 1 1 16rem; }
.enrol-key p { margin: 0 0 0.5rem; }
.key-label { font-weight: 600; }
input.code { width: 10rem; letter-spacing: 0.15em; }
.buttons { display: flex; flex-wrap: wrap; gap: 0.5rem; align-items: center; margin-top: 1rem; }
.buttons button { margin: 0; }
/* White in either scheme: a phone camera reads dark modules on light. */
img.qr { display: block; width: 100%; max-width: 14rem; height: auto; background: #fff; padding: 0.5rem; border-radius: 0.35rem; }"##

/-- A reply with an asset. -/
def asset (body contentType : String) : Reply :=
  { status := .ok, body := body.toUTF8, contentType, headers := [("Cache-Control", "no-cache")] }

end Web
end Pyle