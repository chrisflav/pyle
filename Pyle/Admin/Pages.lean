import Pyle.Admin.Endpoints
import Pyle.Admin.Assets
import Pyle.Web.Pages

/-!
# The administration pages

What an administrator sees under `/admin`, driven by `/admin/assets/admin.js`
(`Pyle.Admin.Assets`) and the endpoints of `Pyle.Admin.Endpoints`:

* `GET /admin` — the accounts: name, display name, email address, groups,
  whether disabled, how many authenticators, the level the account can sign
  in at, when it was created and when one of its sessions was last used.
* `GET /admin/users/<name>` — one account: its email address and display
  name, its groups, disabling and enabling it, ending its sessions (each, or
  all of them with its tokens), its ways in, and removing it.
* `GET /admin/invitations` — make an invitation, whose link is shown once,
  and the pending ones, which can be withdrawn.
* `GET /admin/clients` and `GET /admin/clients/<id>` — the OpenID Connect
  clients, registering one (its secret shown once), changing one, removing
  one.
* `GET /admin/audit?page=<n>` — the audit log, newest first, fifty entries a
  page, and whether its hash chain verifies.
* `GET /admin/keys` — the signing keys and their states, and rotating them.

Every page answers `404` to anyone but an administrator, and sends an
administrator whose session is below `phr` to sign in at `phr` and come back
(`withAdministratorPage`, the `rule` of `Pyle.Admin.Endpoints`).  No page
changes anything.  Every value that reaches a page goes through `escape`,
and no page shows a client secret, an invitation token or anything else
that opens something.
-/

namespace Pyle
namespace Admin

open Http Store SignIn Web

/-- Where the administration script is served. -/
def scriptPath : String := "/admin/assets/admin.js"

/-- The parts of the administration pages, as tabs: a key, the address and
the label. -/
def sections : List (String × String × String) :=
  [("users", "/admin", "Accounts"), ("invitations", "/admin/invitations", "Invitations"),
   ("clients", "/admin/clients", "Clients"), ("audit", "/admin/audit", "Audit log"),
   ("keys", "/admin/keys", "Signing keys")]

/-- The tabs, with `current` marked as the page. -/
def tabs (current : String) : String :=
  "<nav class=\"tabs\" aria-label=\"Administration\">\n" ++
  String.join (sections.map fun (k, href, label) =>
    if k == current then s!"<a href=\"{href}\" aria-current=\"page\">{label}</a>\n"
    else s!"<a href=\"{href}\">{label}</a>\n") ++
  "</nav>\n"

/-- An administration page: the tabs, then `content` (already HTML), with
both scripts. -/
def adminPage (pageName title current : String) (attrs : List (String × String))
    (content : String) (status : Std.Http.Status := .ok) : Reply :=
  htmlReply (page pageName title attrs (tabs current ++ content)
    (back := some ("/account", "Your account")) (scripts := [scriptPath])) status

/-- Run `act` for an administrator's page: `404` for anyone else, and a
session below `phr` is sent to sign in at `phr` and come back to this path. -/
def withAdministratorPage (ctx : Ctx) (r : Req) (act : Session → User → IO Reply) :
    IO Reply := do
  match ← decision ctx r (mutating := false) with
  | (.allow, some (s, u)) => act s u
  | (.hidden, _) | (_, none) => return hidden
  | _ => return Reply.redirect (signInUrl r.path ++ s!"&acr={Acr.phr.shortName}")

/-! ## Pieces -/

/-- A table of `rows` under `headers`, scrolling sideways in its box, or a row
saying `empty`.  Cells are already HTML. -/
def table (label : String) (headers : List String) (rows : List String) (empty : String) :
    String :=
  let head := String.join (headers.map fun h => s!"<th scope=\"col\">{escape h}</th>")
  let body := if rows.isEmpty then
      s!"<tr><td colspan=\"{headers.length}\" class=\"meta\">{escape empty}</td></tr>"
    else "\n".intercalate rows
  s!"<div class=\"table-scroll\" role=\"region\" aria-label=\"{escape label}\" tabindex=\"0\">\n\
    <table class=\"list\">\n<thead>\n<tr>{head}</tr>\n</thead>\n<tbody>\n{body}\n</tbody>\n\
    </table>\n</div>\n"

/-- A table row of cells that are already HTML. -/
def row (cells : List String) : String :=
  "<tr>" ++ String.join (cells.map fun c => s!"<td>{c}</td>") ++ "</tr>"

/-- An optional value, escaped, or a dash. -/
def optText (o : Option String) : String :=
  (o.map escape).getD "<span class=\"meta\">–</span>"

/-- A list, escaped, or a dash. -/
def listText (xs : List String) (sep : String := ", ") : String :=
  if xs.isEmpty then "<span class=\"meta\">–</span>" else escape (sep.intercalate xs)

/-- The level an account can sign in at, in a word. -/
def levelText : Option Acr → String
  | some a => a.shortName
  | none => "none"

/-- A labelled text field. -/
def field (id label value : String) (hint : String := "") (attrs : String := "") : String :=
  s!"<label for=\"{id}\">{escape label}</label>\n\
    <input id=\"{id}\" value=\"{escape value}\" autocomplete=\"off\" spellcheck=\"false\"{attrs}>\n" ++
  (if hint.isEmpty then "" else s!"<p class=\"hint\">{escape hint}</p>\n")

/-- A labelled text area, one value per line. -/
def area (id label : String) (values : List String) (hint : String := "") : String :=
  s!"<label for=\"{id}\">{escape label}</label>\n\
    <textarea id=\"{id}\" rows=\"3\" autocomplete=\"off\" spellcheck=\"false\">\
    {escape ("\n".intercalate values)}</textarea>\n" ++
  (if hint.isEmpty then "" else s!"<p class=\"hint\">{escape hint}</p>\n")

/-- A choice of level, with `current` chosen. -/
def levelSelect (id label : String) (current : Acr) : String :=
  s!"<label for=\"{id}\">{escape label}</label>\n<select id=\"{id}\">" ++
  String.join (Acr.all.map fun a =>
    s!"<option value=\"{a.shortName}\"{if a == current then " selected" else ""}>\
      {a.shortName}</option>") ++
  "</select>\n"

/-- A labelled check box. -/
def checkBox (id label : String) : String :=
  s!"<label class=\"check\" for=\"{id}\"><input type=\"checkbox\" id=\"{id}\"> \
    {escape label}</label>\n"

/-! ## Accounts -/

/-- `GET /admin`: every account. -/
def usersPage : Handler := fun ctx r => withAdministratorPage ctx r fun _ _ => do
  let users ← ctx.store.listUsers
  let rows ← users.toList.mapM fun u => do
    let n ← ctx.store.authenticatorCount u.id
    let level ← Policy.accountLevel ctx u.id
    let sessions ← ctx.store.listSessions u.id
    let last := sessions.foldl (fun m s => max m s.lastSeen) 0
    return row [s!"<a href=\"/admin/users/{escape u.name}\">{escape u.name}</a>",
      optText u.displayName, optText u.email, listText u.groups,
      if u.disabled then "<strong>disabled</strong>" else "enabled", toString n,
      levelText level, formatDate u.created,
      if sessions.isEmpty then "<span class=\"meta\">no session</span>" else formatTime last]
  return adminPage "admin-users" "Accounts" "users" [] <|
    s!"<p class=\"lead\">{users.size} account{if users.size == 1 then "" else "s"}. New \
      accounts are made by <a href=\"/admin/invitations\">invitation</a>.</p>\n" ++
    table "Accounts" ["Name", "Display name", "Email", "Groups", "State", "Authenticators",
      "Level", "Created", "Last active"] rows "No accounts yet."

/-- One of an account's sessions, with a button that ends it. -/
def sessionLine (current : Session) (s : Session) : String :=
  let this := s.handle == current.handle
  let ua := if s.userAgent.isEmpty then "an unknown browser" else s.userAgent
  s!"<li><span>{escape ua} <span class=\"meta\">· {if this then "this browser · " else ""}\
    from {escape s.clientAddress} · signed in {formatTime s.created} at \
    {s.level.shortName} · last used {formatTime s.lastSeen}</span></span>\
    <button type=\"button\" class=\"small\" data-action=\"end-session\" \
    data-handle=\"{escape s.handle}\" data-current=\"{this}\">End</button></li>"

/-- `GET /admin/users/<name>`: one account, and what can be done to it. -/
def userPage : Handler := fun ctx r => withAdministratorPage ctx r fun current admin => do
  let name := (r.param "name").getD ""
  let some u ← ctx.store.findUserByName name
    | return adminPage "admin-missing" "No such account" "users" []
        s!"<p>There is no account named <strong>{escape name}</strong>.</p>" .notFound
  let creds ← ctx.store.listCredentials u.id
  let apps ← ctx.store.listTotpApps u.id
  let n ← ctx.store.authenticatorCount u.id
  let level ← Policy.accountLevel ctx u.id
  let sessions ← Session.list ctx u.id
  let self := admin.id == u.id
  let state := if u.disabled then
      "<p id=\"state\" class=\"notice\">This account is <strong>disabled</strong>: it cannot \
        sign in, and services refuse its tokens.</p>\n\
        <div class=\"buttons\">\n<button type=\"button\" id=\"enable\">Enable it</button>\n"
    else
      "<p id=\"state\">This account is enabled.</p>\n\
        <div class=\"buttons\">\n<button type=\"button\" id=\"disable\" class=\"danger\">Disable \
        it</button>\n"
  let ways := creds.toList.map (fun c => s!"<li><span>{escape c.name} <span class=\"meta\">· \
      {escape (keyKind c)} · added {formatDate c.created}</span></span></li>") ++
    apps.toList.map (fun a => s!"<li><span>{escape a.name} <span class=\"meta\">· \
      authenticator app · added {formatDate a.created}</span></span></li>")
  let sessionList := if sessions.isEmpty then "<p class=\"meta\">No sessions.</p>\n" else
    s!"<ul class=\"items\">\n{"\n".intercalate (sessions.toList.map (sessionLine current))}\n</ul>\n"
  return adminPage "admin-user" u.name "users" [("user", u.name), ("self", toString self)] <|
    s!"<p class=\"lead\">Created {formatDate u.created} · {n} authenticator\
      {if n == 1 then "" else "s"} · can sign in at {levelText level}\
      {if self then " · your own account" else ""}</p>\n" ++
    "<h2>Name and email address</h2>\n" ++
    field "user-display-name" "Display name" (u.displayName.getD "")
      (attrs := s!" maxlength=\"{maxDisplayNameLength}\"") ++
    field "user-email" "Email address" (u.email.getD "")
      "Leave a field empty to clear it. Services such as Zulip know accounts by their email \
        address: giving an address to another account hands that account whatever the first \
        had there." (attrs := s!" maxlength=\"{maxEmailLength}\"") ++
    "<div class=\"buttons\">\n<button type=\"button\" id=\"save-contact\">Save</button>\n\
      </div>\n" ++
    "<h2>Groups</h2>\n" ++
    field "user-groups" "Groups, separated by commas" (", ".intercalate u.groups)
      s!"Members of {ctx.config.adminGroup} are administrators." ++
    "<div class=\"buttons\">\n<button type=\"button\" id=\"save-groups\">Save the groups\
      </button>\n</div>\n" ++
    "<h2>Access</h2>\n" ++ state ++
    "<button type=\"button\" id=\"revoke\" class=\"secondary\">End all sessions and tokens\
      </button>\n</div>\n\
      <p class=\"hint\">Ending access ends the sessions, the refresh tokens and the codes not \
      yet used. Access tokens already issued live until they expire.</p>\n" ++
    s!"<h2>Sessions</h2>\n{sessionList}" ++
    "<h2>Ways in</h2>\n" ++
    (if ways.isEmpty then "<p class=\"meta\">None: this account cannot sign in.</p>\n"
      else s!"<ul class=\"items\">\n{"\n".intercalate ways}\n</ul>\n") ++
    "<h2>Remove the account</h2>\n" ++
    s!"<p>Removing the account deletes it and everything that is its, for good. The audit \
      log keeps its name and email address. Type <strong>{escape u.name}</strong> to \
      confirm.</p>\n" ++
    field "remove-confirm" "Account name" "" ++
    "<div class=\"buttons\">\n<button type=\"button\" id=\"remove\" class=\"danger\">Remove \
      the account</button>\n</div>"

/-! ## Invitations -/

/-- `GET /admin/invitations`: make one, and the pending ones. -/
def invitationsPage : Handler := fun ctx r => withAdministratorPage ctx r fun _ _ => do
  let now ← ctx.clock
  let pending ← ctx.store.listInvitations now
  let rows := pending.toList.map fun (h, i) =>
    row [escape i.userName, optText i.displayName, optText i.email, listText i.groups,
      escape i.createdBy, formatTime i.created, formatTime i.expires,
      rowButton "revoke-invitation" "Withdraw" [("handle", invitationHandle h)]]
  return adminPage "admin-invitations" "Invitations" "invitations" [] <|
    "<p class=\"lead\">An invitation is a link that creates an account with its first \
      passkey. Hand it to the person it is for: it is shown once, here, and pyle keeps only \
      a hash of it.</p>\n" ++
    "<h2>Invite someone</h2>\n" ++
    field "invite-name" "Account name" ""
      "Lower-case letters, digits, '-', '_' and '.', at most 64." (attrs := " maxlength=\"64\"") ++
    field "invite-display-name" "Display name (optional)" "" ++
    field "invite-email" "Email address (optional)" "" ++
    field "invite-groups" "Groups, separated by commas (optional)" ""
      s!"Members of {ctx.config.adminGroup} are administrators." ++
    field "invite-ttl" "Valid for" "7d" "A number followed by d, h, m or s." ++
    "<div class=\"buttons\">\n<button type=\"button\" id=\"invite-create\">Make the \
      invitation</button>\n</div>\n" ++
    "<div id=\"invite-created\" class=\"notice\" hidden>\n<p>The link, shown only now:</p>\n\
      <p><code id=\"invite-url\"></code></p>\n<p class=\"hint\">Load the page again to see it \
      among the pending invitations.</p>\n</div>\n" ++
    "<h2>Pending</h2>\n" ++
    table "Pending invitations" ["Account", "Display name", "Email", "Groups", "Made by",
      "Made", "Expires", ""] rows "No pending invitations."

/-! ## Clients -/

/-- A client's kind: confidential, with a secret, or public. -/
def clientKind (c : Client) : String := if c.secretHash.isSome then "confidential" else "public"

/-- `GET /admin/clients`: every client, and registering one. -/
def clientsPage : Handler := fun ctx r => withAdministratorPage ctx r fun _ _ => do
  let clients ← ctx.store.listClients
  let rows ← clients.toList.mapM fun c => do
    let st := (← ctx.store.clientSettings c.id).getD {}
    return row [s!"<a href=\"/admin/clients/{escape c.id}\">{escape c.id}</a>", escape c.name,
      clientKind c, escape st.idTokenAlg, st.minAcr.shortName, listText c.scopes " ",
      listText c.redirectUris "\n", listText st.postLogoutRedirectUris "\n"]
  return adminPage "admin-clients" "Clients" "clients" [] <|
    table "Clients" ["Id", "Name", "Kind", "ID tokens", "Min level", "Scopes", "Redirect URIs",
      "Post-logout URIs"] rows "No clients yet." ++
    "<h2>Register a client</h2>\n" ++
    field "client-id" "Client id" "" "Letters, digits, '-', '_' and '.', at most 64."
      (attrs := " maxlength=\"64\"") ++
    field "client-name" "Name (optional; the id otherwise)" "" ++
    area "client-redirects" "Redirect URIs, one per line" []
      "Compared byte for byte. http only for the loopback." ++
    area "client-post-logout" "Post-logout URIs, one per line (optional)" [] ++
    field "client-scopes" "Scopes, separated by spaces" (" ".intercalate Oidc.defaultScopes)
      "openid is required. Add email for services that need addresses, offline_access to keep \
        refresh tokens past sign-out, kleis for kleis attestations." ++
    levelSelect "client-min-acr" "The lowest level a session must reach" .mfa ++
    checkBox "client-public" "Public client (no secret, PKCE only)" ++
    checkBox "client-rs256" "Sign its ID tokens with RS256 rather than ES256" ++
    "<div class=\"buttons\">\n<button type=\"button\" id=\"client-add\">Register</button>\n\
      </div>\n" ++
    "<div id=\"client-created\" class=\"notice\" hidden>\n<p>Registered \
      <code id=\"client-created-id\"></code>.</p>\n\
      <div id=\"client-secret-shown\" hidden>\n<p>Its secret, shown only now:</p>\n\
      <p><code id=\"client-secret\"></code></p>\n</div>\n</div>"

/-- `GET /admin/clients/<id>`: change a client, or remove it. -/
def clientPage : Handler := fun ctx r => withAdministratorPage ctx r fun _ _ => do
  let id := (r.param "id").getD ""
  let some c ← ctx.store.findClient id
    | return adminPage "admin-missing" "No such client" "clients" []
        s!"<p>There is no client <strong>{escape id}</strong>.</p>" .notFound
  let st := (← ctx.store.clientSettings c.id).getD {}
  return adminPage "admin-client" c.id "clients" [("client", c.id)] <|
    s!"<p class=\"lead\">{escape c.name} · {clientKind c} · ID tokens signed with \
      {escape st.idTokenAlg} · registered {formatDate c.created}</p>\n" ++
    "<h2>Settings</h2>\n" ++
    field "edit-name" "Name" c.name ++
    area "edit-redirects" "Redirect URIs, one per line" c.redirectUris ++
    area "edit-post-logout" "Post-logout URIs, one per line" st.postLogoutRedirectUris ++
    field "edit-scopes" "Scopes, separated by spaces" (" ".intercalate c.scopes)
      "Taking a scope away does not reach the refresh tokens granted before: they keep it \
        until they expire or are revoked." ++
    levelSelect "edit-min-acr" "The lowest level a session must reach" st.minAcr ++
    "<div class=\"buttons\">\n<button type=\"button\" id=\"client-save\">Save</button>\n\
      </div>\n" ++
    "<h2>Remove the client</h2>\n" ++
    s!"<p>Removing the client ends its codes and tokens, for good. Type \
      <strong>{escape c.id}</strong> to confirm.</p>\n" ++
    field "client-remove-confirm" "Client id" "" ++
    "<div class=\"buttons\">\n<button type=\"button\" id=\"client-remove\" class=\"danger\">\
      Remove the client</button>\n</div>"

/-! ## The audit log -/

/-- How many entries a page of the audit log shows. -/
def auditPageSize : Nat := 50

/-- `GET /admin/audit?page=<n>`: the newest entries first, a page at a time,
and whether the whole chain verifies. -/
def auditPage : Handler := fun ctx r => withAdministratorPage ctx r fun _ _ => do
  let n := ((r.queryParams.toOption.bind (lookupOnce · "page")).bind String.toNat?).getD 1
  let n := max n 1
  let total ← Audit.count ctx.store
  let pages := max 1 ((total + auditPageSize - 1) / auditPageSize)
  let entries ← Audit.recent ctx.store auditPageSize ((n - 1) * auditPageSize)
  let chain := match ← Audit.verify ctx.store with
    | .ok k => s!"<p id=\"audit-chain\">The log's {k} entries form an unbroken chain.</p>\n"
    | .error e => s!"<p id=\"audit-chain\" class=\"notice\"><strong>The audit log is broken: \
        {escape e}</strong></p>\n"
  let rows := entries.toList.map fun e =>
    row [toString e.seq, formatTime e.time, escape e.event, optText e.userName,
      optText e.factor, escape e.clientAddress, escape e.outcome, escape e.detail]
  let link (k : Nat) (label : String) : String :=
    s!"<a href=\"/admin/audit?page={k}\">{label}</a>"
  let nav := "<p class=\"pager\">" ++
    (if n > 1 then link (n - 1) "← Newer" ++ " " else "") ++
    s!"<span>Page {n} of {pages}</span>" ++
    (if n < pages then " " ++ link (n + 1) "Older →" else "") ++ "</p>\n"
  return adminPage "admin-audit" "Audit log" "audit" [] <|
    chain ++
    "<p class=\"hint\">An entry made from these pages names the administrator as its account, \
      and what was changed at the start of its detail.</p>\n" ++
    nav ++
    table "Audit log" ["#", "Time", "Event", "Account", "Factor", "From", "Outcome", "Detail"]
      rows "No entries." ++ nav

/-! ## Signing keys -/

/-- `GET /admin/keys`: every signing key and its state. -/
def keysPage : Handler := fun ctx r => withAdministratorPage ctx r fun _ _ => do
  let keys ← ctx.store.allKeys
  let rows := keys.toList.map fun k =>
    let use := ((Keys.Use.ofAlgorithm? k.algorithm).map (·.name)).getD k.algorithm
    row [escape use, k.state.toString, s!"<code>{escape k.kid}</code>", formatTime k.created]
  let buttons := Keys.Use.all.map fun u =>
    rowButton "rotate-key" s!"Rotate {u.name}" [("use", u.name)]
  return adminPage "admin-keys" "Signing keys" "keys" [] <|
    table "Signing keys" ["Use", "State", "Key id", "Created"] rows "No keys yet." ++
    "<h2>Rotate</h2>\n" ++
    "<p>Rotating promotes the waiting next key to current, the current one to previous \
      (still published, so what it signed verifies) and retires the previous one, then \
      announces a fresh next key. Rotate once, let clients and services fetch the new key, \
      then rotate again.</p>\n" ++
    "<div class=\"buttons\">\n" ++ " ".intercalate buttons ++
    "\n<button type=\"button\" id=\"rotate-all\" class=\"secondary\">Rotate all three\
      </button>\n</div>\n" ++
    "<p class=\"notice\" id=\"cli-only\">Replacing the root key (<code>pyle root-key \
      rotate</code>) and ending every account's sessions at once (<code>pyle sessions revoke \
      --all</code>) are done on the command line only.</p>"

/-- `GET /admin/assets/admin.js`, for administrators only. -/
def scriptAsset : Handler := fun ctx r => do
  match ← administrator ctx r with
  | some _ => return asset Admin.script "text/javascript; charset=utf-8"
  | none => return hidden

end Admin
end Pyle
