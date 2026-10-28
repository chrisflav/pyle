import Pyle.Http.Message

/-!
# The administration pages' script

Served from `/admin/assets/admin.js`, to administrators only (anyone else
gets the `404` every path under `/admin` gives them), and loaded after
`/assets/pyle.js`, whose functions — `post`, `say`, `describe`, `failed`,
`getAssertion`, `on`, `value` — it uses.  Like that script it never writes
HTML: what the server answers is put on the page as text.

What it relies on, and the Lean side provides (`Pyle.Admin.Pages`):

* `body[data-page]` is `admin-users`, `admin-user`, `admin-invitations`,
  `admin-clients`, `admin-client`, `admin-audit` or `admin-keys`; the account
  page adds `data-user`, the account's name, and `data-self`, whether it is
  the administrator's own; the client page adds `data-client`.
* Every change is posted with `adminAct`, which meets `403 step_up_required`
  by confirming with a passkey at `phr` and trying once more, and failing
  that sends the browser to sign in at `phr` and come back.
* A client's secret and an invitation's link are shown from the answer that
  made them, and are gone when the page is left.
-/

namespace Pyle
namespace Admin

/-- `/admin/assets/admin.js`. -/
def script : String := r##"// pyle: the administration pages.  Served to administrators only, after
// /assets/pyle.js, whose functions it uses.  Text only, never HTML.
'use strict';

// A change needs a passkey sign-in within the last five minutes.  Confirm
// with a passkey here, at phr, and try once more; without one at hand, the
// sign-in page does it and comes back.
async function adminStepUp() {
  const credential = await getAssertion('/signin/stepup/begin', {});
  const res = await post('/signin/stepup/finish',
    { credential: credential, return: window.location.pathname, acr: 'phr' });
  if (!res.ok) throw new Error(describe(res));
}

async function adminAct(url, body) {
  let res = await post(url, body);
  if (res.status === 403 && res.data.error === 'step_up_required') {
    say('Confirm it is you with a passkey first.');
    try {
      await adminStepUp();
    } catch (e) {
      window.location.assign('/signin?return=' + encodeURIComponent(window.location.pathname) +
        '&max_age=0&acr=phr');
      throw new Error('Confirm it is you on the sign-in page.');
    }
    res = await post(url, body);
  }
  if (!res.ok) throw new Error(describe(res));
  return res.data;
}

// Groups and scopes are separated by commas or white space, neither of which
// either can contain.
function wordsOf(text) {
  return text.split(/[\s,]+/).filter(function (w) { return w.length > 0; });
}

// Addresses may contain commas, never white space.
function linesOf(text) {
  return text.split(/\s+/).filter(function (w) { return w.length > 0; });
}

function checked(id) {
  const el = document.getElementById(id);
  return el ? el.checked : false;
}

function again() {
  window.location.assign(window.location.pathname);
}

function show(id, text) {
  const el = document.getElementById(id);
  if (el) el.textContent = text;
}

function reveal(id) {
  const el = document.getElementById(id);
  if (el) el.hidden = false;
}

// One account.  A change to the administrator's own access ends their
// session, and then the sign-in page is where to go.
function setupAdminUser(body) {
  const name = body.dataset.user;
  const self = body.dataset.self === 'true';
  const after = function (endsOwn) {
    if (self && endsOwn) window.location.assign('/signin');
    else again();
  };
  on('save-contact', 'click', async function () {
    try {
      await adminAct('/admin/users/contact',
        { name: name, email: value('user-email'), displayName: value('user-display-name') });
      after(false);
    } catch (e) { failed(e); }
  });
  on('save-groups', 'click', async function () {
    try {
      await adminAct('/admin/users/groups', { name: name, groups: wordsOf(value('user-groups')) });
      after(false);
    } catch (e) { failed(e); }
  });
  on('disable', 'click', async function () {
    if (!window.confirm('Disable this account? Its sessions and tokens end now.')) return;
    try {
      await adminAct('/admin/users/disable', { name: name });
      after(true);
    } catch (e) { failed(e); }
  });
  on('enable', 'click', async function () {
    try {
      await adminAct('/admin/users/enable', { name: name });
      after(false);
    } catch (e) { failed(e); }
  });
  on('revoke', 'click', async function () {
    if (!window.confirm('End every session and token of this account?')) return;
    try {
      await adminAct('/admin/users/revoke', { name: name });
      after(true);
    } catch (e) { failed(e); }
  });
  document.querySelectorAll('button[data-action="end-session"]').forEach(function (b) {
    b.addEventListener('click', async function () {
      try {
        await adminAct('/admin/users/sessions/end', { name: name, handle: b.dataset.handle });
        after(b.dataset.current === 'true');
      } catch (e) { failed(e); }
    });
  });
  on('remove', 'click', async function () {
    const typed = value('remove-confirm');
    if (typed !== name) { say('Type the account name to confirm.'); return; }
    try {
      await adminAct('/admin/users/remove', { name: name, confirm: typed });
      window.location.assign(self ? '/signin' : '/admin');
    } catch (e) { failed(e); }
  });
}

// Invitations: the link is shown once, from the answer that made it.
function setupAdminInvitations() {
  on('invite-create', 'click', async function () {
    try {
      const data = await adminAct('/admin/invitations/create', {
        name: value('invite-name'), email: value('invite-email'),
        displayName: value('invite-display-name'), groups: wordsOf(value('invite-groups')),
        ttl: value('invite-ttl'),
      });
      show('invite-url', data.url);
      reveal('invite-created');
      say('The invitation is made. Copy the link now: it is not shown again.');
    } catch (e) { failed(e); }
  });
  document.querySelectorAll('button[data-action="revoke-invitation"]').forEach(function (b) {
    b.addEventListener('click', async function () {
      if (!window.confirm('Withdraw this invitation? Its link stops working.')) return;
      try {
        await adminAct('/admin/invitations/revoke', { handle: b.dataset.handle });
        again();
      } catch (e) { failed(e); }
    });
  });
}

// Clients: a confidential client's secret is shown once.
function setupAdminClients() {
  on('client-add', 'click', async function () {
    try {
      const data = await adminAct('/admin/clients/add', {
        id: value('client-id'), name: value('client-name'),
        redirectUris: linesOf(value('client-redirects')),
        postLogoutUris: linesOf(value('client-post-logout')),
        scopes: wordsOf(value('client-scopes')), public: checked('client-public'),
        rs256: checked('client-rs256'), minAcr: value('client-min-acr'),
      });
      show('client-created-id', data.id);
      if (data.secret) {
        show('client-secret', data.secret);
        reveal('client-secret-shown');
      }
      reveal('client-created');
      say(data.secret ? 'The client is registered. Copy its secret now: it is not shown again.'
        : 'The public client is registered.');
    } catch (e) { failed(e); }
  });
}

function setupAdminClient(body) {
  const id = body.dataset.client;
  on('client-save', 'click', async function () {
    try {
      await adminAct('/admin/clients/update', {
        id: id, name: value('edit-name'), redirectUris: linesOf(value('edit-redirects')),
        postLogoutUris: linesOf(value('edit-post-logout')), scopes: wordsOf(value('edit-scopes')),
        minAcr: value('edit-min-acr'),
      });
      again();
    } catch (e) { failed(e); }
  });
  on('client-remove', 'click', async function () {
    const typed = value('client-remove-confirm');
    if (typed !== id) { say('Type the client id to confirm.'); return; }
    try {
      await adminAct('/admin/clients/remove', { id: id, confirm: typed });
      window.location.assign('/admin/clients');
    } catch (e) { failed(e); }
  });
}

function setupAdminKeys() {
  document.querySelectorAll('button[data-action="rotate-key"]').forEach(function (b) {
    b.addEventListener('click', async function () {
      try {
        await adminAct('/admin/keys/rotate', { use: b.dataset.use });
        again();
      } catch (e) { failed(e); }
    });
  });
  on('rotate-all', 'click', async function () {
    try {
      await adminAct('/admin/keys/rotate', {});
      again();
    } catch (e) { failed(e); }
  });
}

document.addEventListener('DOMContentLoaded', function () {
  const body = document.body;
  if (body.dataset.page === 'admin-user') setupAdminUser(body);
  else if (body.dataset.page === 'admin-invitations') setupAdminInvitations();
  else if (body.dataset.page === 'admin-clients') setupAdminClients();
  else if (body.dataset.page === 'admin-client') setupAdminClient(body);
  else if (body.dataset.page === 'admin-keys') setupAdminKeys();
});"##

end Admin
end Pyle
