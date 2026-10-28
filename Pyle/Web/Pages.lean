import Pyle.SignIn.Invite
import Pyle.Account.Endpoints
import Pyle.Web.Html
import Pyle.Web.Assets
import Pyle.Admin

/-!
# The pages

The pages, rendered here and driven by `/assets/pyle.js`:

* `GET /signin?return=…&max_age=…&acr=…` — the sign-in page of the seam
  with the protocol endpoints.  `acr` is the level the sign-in must reach, as
  a short name or an identifier (`Acr.ofIdentifier?`); without it, any.  A request
  whose session already satisfies `max_age` and `acr` is sent straight back to
  `return` (`303`); one with a session that does not is shown the page in
  step-up mode, which re-authenticates that session; one without a session is
  shown the sign-in page.  The page offers only what can reach the level: at
  `phr` and `phrh` a passkey alone, since nothing else is phishing-resistant;
  at `mfa` a passkey, a security key with a code or a password, or two codes.
  It passes the level on to the endpoints, which refuse what falls short.  A
  step-up for an account that has nothing that could reach the level says so,
  and points to the account page.  A `return` that is not a path on this origin is refused with `400`
  rather than replaced, so a link that tried to misuse it fails visibly.
* `GET /account` — the account: how well it is protected, in a word and a
  sentence (`protectionSummary`, from `Policy.capabilities`), with what to
  add — a passkey below `phr`, a second authenticator below two (§1),
  recovery codes when none are left; every way it signs in, as one table
  grouped by kind (passkeys and security keys, authenticator apps, the
  password if the deployment allows them, recovery codes), each row with its
  rename and remove buttons; and the sessions.  `?added=` names a method just
  added, which the page then says.
* `GET /account/add` — the choice of what to add.  A passkey or a security
  key is registered from this page; the others have a page each:
  `GET /account/add/app` (an authenticator app: name, QR code, confirming
  code), `GET /account/add/password` and `GET /account/add/recovery-codes`.

Every account page sends a browser without a session to sign in first, and
comes back.
* `GET /invite/<token>` — register the first passkey of an invited account.

Every value that reaches a page goes through `escape`.
-/

namespace Pyle
namespace Web

open Http Store SignIn

/-- The address of the sign-in page that comes back to `ret`. -/
def signInUrl (ret : String) : String :=
  "/signin?return=" ++ Factor.Totp.percentEncode ret

/-! ## Sign-in -/

/-- The sign-in form for the other ways in: a name, then two of a password, a
TOTP code and a recovery code, or one of them with a security key.  In
step-up mode the name is the session's and cannot be changed. -/
def otherWays (passwords : Bool) (name : Option String) : String :=
  let nameField := match name with
    | some n => s!"<input id=\"name\" name=\"name\" value=\"{escape n}\" readonly \
        autocomplete=\"username\">"
    | none => "<input id=\"name\" name=\"name\" autocomplete=\"username\" autocapitalize=\"none\" \
        spellcheck=\"false\">"
  let password := if passwords then
      "<label for=\"password\">Password</label>\n\
       <input id=\"password\" name=\"password\" type=\"password\" \
         autocomplete=\"current-password\">\n"
    else ""
  "<section>\n<h2>Other ways</h2>\n<form id=\"other\" novalidate>\n" ++
  "<label for=\"name\">User name</label>\n" ++ nameField ++ "\n" ++ password ++
  "<label for=\"totp\">Code from your authenticator app</label>\n" ++
  "<input id=\"totp\" name=\"totp\" inputmode=\"numeric\" autocomplete=\"one-time-code\">\n" ++
  "<label for=\"recovery\">Recovery code</label>\n" ++
  "<input id=\"recovery\" name=\"recovery\" autocomplete=\"off\" spellcheck=\"false\">\n" ++
  "<p class=\"hint\">Fill in two of these, or one of them and use a security key.</p>\n" ++
  "<button type=\"button\" id=\"security-key\" class=\"secondary\">Use a security key</button>\n" ++
  "<button type=\"submit\" id=\"codes\" class=\"secondary\">Sign in with these</button>\n" ++
  "</form>\n</section>"

/-- The sign-in page, for signing in (`stepUpName = none`) or for confirming
the session of the named user, at level `want` or better.  `reachable` is
false for a step-up of an account that has nothing that could reach `want`. -/
def signInPage (passwords : Bool) (want : Acr) (ret : String) (stepUpName : Option String)
    (reachable : Bool := true) : String :=
  let (title, mode, intro, button) := match stepUpName with
    | some n => ("Confirm it is you", "stepup",
        s!"You are signed in as <strong>{escape n}</strong>. To continue, confirm it is you.",
        "Confirm with a passkey")
    | none => ("Sign in", "signin",
        "Sign in with the passkey on this device, or with a security key that asks for your \
          PIN or fingerprint.",
        "Sign in with a passkey")
  let wantPhr := Acr.phr ≤ want
  let levelNote :=
    if want == .phrh then
      "\n<p class=\"hint\">This needs a passkey or security key that verifies you and keeps \
        its key on the device: a synced passkey will not do.</p>"
    else if wantPhr then
      "\n<p class=\"hint\">This needs a passkey or a security key that verifies you.</p>"
    else ""
  let unreachable := if reachable then "" else
    "\n<p class=\"notice\">Your account has nothing that can sign in this strongly yet. \
      <a href=\"/account\">Add a passkey on your account page</a>, then try again.</p>"
  page "signin" title [("mode", mode), ("return", ret), ("acr", want.shortName)] <|
    s!"<section>\n<p>{intro}</p>{levelNote}{unreachable}\n" ++
    s!"<button type=\"button\" id=\"passkey\">{button}</button>\n</section>\n" ++
    (if wantPhr then "" else otherWays passwords stepUpName)

/-- `GET /signin`. -/
def signIn : Handler := fun ctx r => do
  let some ps := r.queryParams.toOption
    | return messagePage "Sign in" "The address is malformed." .badRequest
  let some ret := safeReturn ((lookupOnce ps "return").getD defaultReturn)
    | return messagePage "Sign in" "That return address is not a page of this site."
        .badRequest
  let maxAge ← match lookupOnce ps "max_age" with
    | none => pure none
    | some s => match s.toNat? with
      | some n => pure (some n)
      | none => return messagePage "Sign in" "max_age must be a number of seconds." .badRequest
  let want ← match lookupOnce ps "acr" with
    | none => pure Acr.mfa
    | some a => match Acr.ofIdentifier? a with
      | some l => pure l
      | none => return messagePage "Sign in" "acr is not a level pyle knows." .badRequest
  match ← Session.current ctx r with
  | some s =>
    if Policy.satisfies s (← ctx.clock) maxAge want then return Reply.redirect ret
    let name := (← ctx.store.findUser s.user).map (·.name)
    let reachable := (← Policy.accountLevel ctx s.user).any (·.satisfies want)
    return htmlReply (signInPage ctx.config.allowPasswords want ret (some (name.getD ""))
      reachable)
  | none => return htmlReply (signInPage ctx.config.allowPasswords want ret none)

/-! ## The account -/

/-- How well an account with these factors is protected, in plain words, and
whether to urge a passkey: below `phr`, it does. -/
def safety (c : Acr.Capabilities) : String × Bool :=
  match c.level with
  | some .phrh =>
    ("This account can sign in with a security key that verifies you and keeps its key on \
      the device: the strongest protection there is.", false)
  | some .phr => ("This account can sign in with a passkey, which cannot be phished.", false)
  | some .mfa =>
    ("This account signs in with two factors, but has no passkey, which would also stop \
      phishing. Add a passkey for stronger protection.", true)
  | none =>
    ("This account has no passkey and only one kind of factor left: it cannot sign in \
      again. Add a passkey.", true)

/-- The one word the protection summary leads with, for the strongest level
an account could sign in at. -/
def protectionWord : Option Acr → String
  | some .phrh => "strongest"
  | some .phr => "strong"
  | some .mfa => "fair"
  | none => "at risk"

/-- The paragraph of the account page that says how well the account is
protected. -/
def safetyParagraph (c : Acr.Capabilities) : String :=
  s!"<p id=\"safety\">{escape (safety c).1}</p>\n"

/-- The "Account protection" summary at the top of the account page: the
level in a word, what it means (`safety`), and what to add — a passkey
below `phr`, a second authenticator below two, recovery codes when none are
left — with a link to add it. -/
def protectionSummary (c : Acr.Capabilities) (count recovery : Nat) : String :=
  let (_, nudgePasskey) := safety c
  let nags :=
    (if count < 2 then
      [s!"You have {count} authenticator{if count == 1 then "" else "s"}. Add a second \
        passkey or security key, so that losing one does not lock you out."]
    else []) ++
    (if recovery == 0 then
      ["You have no unused recovery codes. Make some and keep them somewhere safe."]
    else [])
  let nudge := nudgePasskey || !nags.isEmpty
  let nagText := String.join (nags.map fun n => s!"<p>{escape n}</p>\n")
  s!"<div id=\"protection\" class=\"protection{if nudge then " notice" else ""}\">\n\
    <div class=\"protection-text\">\n\
    <p class=\"protection-title\">Account protection: {protectionWord c.level}</p>\n" ++
  safetyParagraph c ++ nagText ++ "</div>\n" ++
  (if nudge then "<a class=\"nudge-link\" href=\"/account/add\">Add one</a>\n" else "") ++
  "</div>\n"

/-- What an authenticator is and how its key is held, in plain words: a
passkey synced between devices, from the backup-eligible flag; a passkey that
stays on this device, for one that is not and that the browser reached as
`internal`; a security key that keeps its key, otherwise.  Then whether it
verifies the user, which decides whether it is enough on its own. -/
def keyKind (c : Credential) : String :=
  (if c.backupEligible then "Passkey · synced between your devices"
    else if c.transports.contains "internal" then "Passkey · stays on this device"
    else "Security key · stays on the key") ++
  (if c.userVerified then " · asks for your PIN, fingerprint or face"
    else " · a touch only, so one step of two")

/-- When something was last used, or that it has not been. -/
def lastUsedText (t : Option Nat) : String :=
  match t with
  | some t => formatTime t
  | none => "not used yet"

/-- A row of the sign-in methods table: the name, the details with a date
under them, when it was last used, and the actions, all already HTML. -/
def methodRow (name details date used actions : String) : String :=
  s!"<tr>\n<td><strong>{name}</strong></td>\n\
    <td>{details}<br><span class=\"meta\">{date}</span></td>\n\
    <td>{used}</td>\n<td class=\"actions\">{actions}</td>\n</tr>"

/-- A group of the table: a `tbody` with a header row, then its rows, or a
row saying there are none. -/
def methodGroup (title note : String) (rows : List String) (empty : String) : String :=
  let noteHtml := if note.isEmpty then "" else s!" <span class=\"meta\">· {escape note}</span>"
  let body := if rows.isEmpty then
      s!"<tr>\n<td colspan=\"4\" class=\"meta\">{escape empty}</td>\n</tr>"
    else String.intercalate "\n" rows
  s!"<tbody>\n<tr><th colspan=\"4\" scope=\"colgroup\">{escape title}{noteHtml}</th></tr>\n\
    {body}\n</tbody>\n"

/-- A small button for an action on one row. -/
def rowButton (action label : String) (data : List (String × String)) : String :=
  let attrs := data.foldl (init := "") fun acc (k, v) => acc ++ s!" data-{k}=\"{escape v}\""
  s!"<button type=\"button\" class=\"small\" data-action=\"{action}\"{attrs}>{label}</button>"

/-- A small link styled as a button. -/
def rowLink (href label : String) : String :=
  s!"<a class=\"button small secondary\" href=\"{escape href}\">{label}</a>"

/-- One passkey or security key. -/
def credentialRow (c : Credential) : String :=
  let id := b64 c.id
  methodRow (escape c.name) (escape (keyKind c)) s!"added {formatDate c.created}"
    (lastUsedText c.lastUsed)
    (rowButton "rename" "Rename" [("id", id)] ++ " " ++ rowButton "remove" "Remove" [("id", id)])

/-- One authenticator app. -/
def appRow (a : TotpApp) : String :=
  let id := toString a.id
  methodRow (escape a.name) "Authenticator app" s!"added {formatDate a.created}"
    (lastUsedText a.lastUsed)
    (rowButton "totp-rename" "Rename" [("id", id)] ++ " " ++
      rowButton "totp-remove" "Remove" [("id", id)])

/-- The password row: whether one is set and since when.  pyle does not
record when a password was last used. -/
def passwordRow (setAt : Option Nat) : String :=
  match setAt with
  | some t =>
    methodRow "Password" "Only together with another method" s!"set {formatDate t}"
      "not recorded"
      (rowLink "/account/add/password" "Change" ++ " " ++
        rowButton "password-remove" "Remove" [])
  | none =>
    methodRow "Password" "Not set" "only together with another method" "never"
      (rowLink "/account/add/password" "Set")

/-- The recovery-codes row: how many of the last set are left. -/
def recoveryRow (unspent total : Nat) : String :=
  let details := if total == 0 then "None made yet" else s!"{unspent} of {total} left"
  let used := if total == 0 then "none used" else s!"{total - unspent} used"
  methodRow "Recovery codes" details "each works once" used
    (rowLink "/account/add/recovery-codes" (if total == 0 then "Make codes" else "Make new codes"))

/-- What `/account?added=…` says: the method that was just added. -/
def addedMessage : String → Option String
  | "passkey" => some "Your passkey was added."
  | "security-key" => some "Your security key was added."
  | "app" => some "Your authenticator app was added."
  | "password" => some "Your password was set."
  | _ => none

/-- One session in the list.  The request's own has no button: "Sign out"
below ends it. -/
def sessionItem (current : Session) (s : Session) : String :=
  let this := s.handle == current.handle
  let ua := if s.userAgent.isEmpty then "an unknown browser" else s.userAgent
  let button := if this then "" else
    s!"<button type=\"button\" class=\"small\" data-action=\"end-session\" \
      data-handle=\"{escape s.handle}\" data-current=\"false\">Sign out there</button>"
  s!"<li><span>{escape ua} <span class=\"meta\">· {if this then "this browser · " else ""}from \
    {escape s.clientAddress} · signed in {formatTime s.created} · last used \
    {formatTime s.lastSeen}</span></span>{button}</li>"

/-- The account page's content: the protection summary, every way to sign
in as one table grouped by kind, and the sessions. -/
def accountContent (ctx : Ctx) (s : Session) (u : User) (added : Option String) :
    IO String := do
  let creds ← ctx.store.listCredentials u.id
  let apps ← ctx.store.listTotpApps u.id
  let count ← ctx.store.authenticatorCount u.id
  let recovery ← ctx.store.unspentRecoveryCodes u.id
  let recoveryTotal ← ctx.store.recoveryCodeCount u.id
  let passwordAt ← ctx.store.passwordSetAt u.id
  let sessions ← Session.list ctx u.id
  let caps ← Policy.capabilities ctx u.id
  let addedNote := match added.bind addedMessage with
    | some m => s!"<p id=\"added\" class=\"notice\">{escape m}</p>\n"
    | none => ""
  let passwordGroup := if !ctx.config.allowPasswords then "" else
    methodGroup "Password" "" [passwordRow passwordAt] ""
  let sessionList := String.intercalate "\n" (sessions.toList.map (sessionItem s))
  return addedNote ++
    protectionSummary caps count recovery ++
    "<div class=\"section-head\">\n<h2 id=\"methods-title\">How you sign in</h2>\n\
     <a class=\"button\" id=\"add-method\" href=\"/account/add\">Add a sign-in method</a>\n\
     </div>\n\
     <div class=\"table-scroll\" role=\"region\" aria-labelledby=\"methods-title\" \
     tabindex=\"0\">\n\
     <table class=\"methods\">\n<thead>\n<tr>\n<th scope=\"col\">Name</th>\n\
     <th scope=\"col\">Details</th>\n<th scope=\"col\">Last used</th>\n\
     <th scope=\"col\"><span class=\"visually-hidden\">Actions</span></th>\n</tr>\n</thead>\n" ++
    methodGroup "Passkeys and security keys" "the strongest way in"
      (creds.toList.map credentialRow) "None yet." ++
    methodGroup "Authenticator apps" "6-digit codes, a second step" (apps.toList.map appRow)
      "None yet." ++
    passwordGroup ++
    methodGroup "Recovery codes" "for when you lose a device"
      [recoveryRow recovery recoveryTotal] "" ++
    "</table>\n</div>\n\
     <p class=\"hint\">Changing these asks you to confirm it's you again if you last signed in \
     more than 5 minutes ago.</p>\n" ++
    "<h2>Where you're signed in</h2>\n" ++
    s!"<ul class=\"items\">\n{sessionList}\n</ul>\n" ++
    "<button type=\"button\" id=\"sign-out\" class=\"secondary\">Sign out</button>"

/-- Run `act` with the request's session and its user, or send the browser
to sign in and come back to `path`. -/
def withAccount (ctx : Ctx) (r : Req) (path : String) (act : Session → User → IO Reply) :
    IO Reply := do
  let some s ← Session.current ctx r | return Reply.redirect (signInUrl path)
  let some u ← ctx.store.findUser s.user | return Reply.redirect (signInUrl path)
  act s u

/-- The account's display name and email address, as services are told
them, read-only: an administrator sets both (`pyle user set`), never the
user. -/
def contactDetails (u : User) : String :=
  let name := (u.displayName.map escape).getD s!"{escape u.name} <span class=\"meta\">(no \
    display name set)</span>"
  let email := (u.email.map escape).getD "<span class=\"meta\">none</span>"
  s!"<p class=\"account-details\" id=\"account-details\">Name: <span id=\"display-name\">\
    {name}</span> · Email: <span id=\"email\">{email}</span> \
    <span class=\"meta\">· set by your administrator</span></p>"

/-- `GET /account?added=…`. -/
def account : Handler := fun ctx r => withAccount ctx r "/account" fun s u => do
  let added := r.queryParams.toOption.bind (lookupOnce · "added")
  let groups := if u.groups.isEmpty then "" else
    s!" <span class=\"meta\">· groups: {escape (", ".intercalate u.groups)}</span>"
  -- Only administrators are told the administration pages exist.
  let adminLink := if !Admin.isAdministrator ctx.config.adminGroup u then "" else
    "\n<p class=\"admin-link\"><a id=\"admin-link\" href=\"/admin\">Administration</a></p>"
  return htmlReply (page "account" "Your account" [] (← accountContent ctx s u added)
    (aside := s!"<div class=\"who\">\n<p class=\"signed-in\">Signed in as \
      <strong>{escape u.name}</strong>{groups}</p>\n{contactDetails u}{adminLink}\n</div>"))

/-! ## Adding a way to sign in -/

/-- One choice on the add page, styled as a card: a button (`id` and
`data-kind` for the script) or a link. -/
def choice (title badge description go : String) (target : Sum (String × String) String) :
    String :=
  let badgeHtml := if badge.isEmpty then "" else s!" <span class=\"badge\">{escape badge}</span>"
  let inner := s!"<span class=\"choice-text\">\
    <span class=\"choice-title\">{escape title}{badgeHtml}</span>\
    <span class=\"choice-desc\">{escape description}</span></span>\
    <span class=\"choice-go\">{escape go} →</span>"
  let cls := if badge.isEmpty then "choice" else "choice recommended"
  match target with
  | .inl (id, kind) =>
    s!"<button type=\"button\" class=\"{cls}\" id=\"{id}\" data-kind=\"{kind}\">{inner}</button>"
  | .inr href => s!"<a class=\"{cls}\" href=\"{escape href}\">{inner}</a>"

/-- The back link of the pages under `/account/add/`. -/
def backToChoices : Option (String × String) := some ("/account/add", "Choose another method")

/-- `GET /account/add`: what can be added, each with what it is good for
under pyle's rules.  A passkey and a security key are registered from here
by the script; the rest have pages of their own. -/
def add : Handler := fun ctx r => withAccount ctx r "/account/add" fun _ u => do
  let hasPassword := (← ctx.store.findPassword u.id).isSome
  let apps := (← ctx.store.listTotpApps u.id).size
  let app := if apps ≥ maxTotpApps then
      s!"<p class=\"hint\" id=\"apps-full\">You have {maxTotpApps} authenticator apps, the \
        most an account can have. Remove one to add another.</p>\n"
    else
      choice "Authenticator app" ""
        "An app that shows a 6-digit code, such as Aegis, 2FAS or Google Authenticator. Used \
          as a second step, together with another kind of method: two apps are still one step."
        "Add" (.inr "/account/add/app") ++ "\n"
  let password := if !ctx.config.allowPasswords then "" else
    choice "Password" ""
      "At least 12 characters. Never enough on its own: always used together with another \
        method, and services that ask for a passkey won't take it." (if hasPassword then "Change"
        else "Set") (.inr "/account/add/password") ++ "\n"
  return htmlReply <| page "add" "Add a sign-in method" [] (back := some ("/account",
      "Back to your account")) <|
    s!"<p class=\"lead\">Pick what you want to add. You can have as many passkeys and \
      security keys as you like, and up to {maxTotpApps} authenticator apps.</p>\n\
      <div class=\"choices\">\n" ++
    choice "Passkey" "Recommended"
      "Sign in with your fingerprint, face or screen lock, on this device or your phone. \
        Enough on its own, and it can't be phished." "Add" (.inl ("add-passkey", "passkey")) ++
    "\n" ++
    choice "Security key" ""
      "A USB or NFC key such as a YubiKey. With a PIN it is enough on its own and can't be \
        phished; with just a touch it is one step, used together with another method." "Add"
      (.inl ("add-security-key", "security-key")) ++ "\n" ++
    app ++ password ++
    choice "Recovery codes" ""
      "Ten one-time codes to write down. Each works once, together with another method, for \
        when you lose a device. Making new ones replaces the old ones." "Make"
      (.inr "/account/add/recovery-codes") ++
    "\n</div>"

/-- The base32 key in groups of four, as people read it out and type it. -/
def groupedKey (key : String) : String :=
  String.ofList <| (key.toList.zipIdx.flatMap fun (c, i) =>
    if i > 0 && i % 4 == 0 then [' ', c] else [c])

/-- The step-up sign-in that comes back to `path`: a sign-in within the
step-up window. -/
def stepUpUrl (path : String) : String :=
  s!"{signInUrl path}&max_age={SignIn.stepUpSeconds}"

/-- `GET /account/add/app`: add an authenticator app in three steps — name
it, scan the QR code or type the key, confirm with a code.  The page makes
the secret itself, as `POST /account/totp/begin` does and under the same
step-up rule: a session that has not signed in within the step-up window is
sent to confirm it is the user first.  The secret travels to the browser
sealed (`data-pending`), and only `POST /account/totp/confirm` with a code
from it stores anything.  An account with `maxTotpApps` apps is told so,
and offered nothing to scan. -/
def addApp : Handler := fun ctx r => withAccount ctx r "/account/add/app" fun s u => do
  unless Session.authenticatedWithin s (← ctx.clock) SignIn.stepUpSeconds do
    return Reply.redirect (stepUpUrl "/account/add/app")
  let n := (← ctx.store.listTotpApps u.id).size
  if n ≥ maxTotpApps then
    return htmlReply <| page "add-app" "Add an authenticator app" [] (back := backToChoices) <|
      s!"<p class=\"notice\" id=\"apps-full\">You have {n} authenticator apps, the most an \
        account can have. Remove one on <a href=\"/account\">your account page</a> to add \
        another.</p>"
  let a ← Account.newApp ctx u (Account.defaultAppName n)
  let lead := if n == 0 then
      "Each app gets its own key, so you can add more later and remove one without touching \
        the others."
    else
      s!"You already have {n} authenticator app{if n == 1 then "" else "s"}. Each one gets its \
        own key, so you can remove one without touching the others."
  let qr := if a.qr.isEmpty then "" else
    s!"<img id=\"totp-qr\" class=\"qr\" alt=\"QR code for your authenticator app\" \
      src=\"{escape a.qr}\">\n"
  return htmlReply <| page "add-app" "Add an authenticator app" [("pending", a.pending)]
      (back := backToChoices) <|
    s!"<p class=\"lead\">{escape lead}</p>\n" ++
    "<p id=\"rescan\" class=\"notice\" hidden>You confirmed it is you on the sign-in page, \
     so this page has a new key. If you scanned the one before, remove it from your app and \
     scan this one instead.</p>\n" ++
    "<h2>1. Name it</h2>\n\
     <label for=\"app-name\">A name you'll recognise in the list</label>\n" ++
    s!"<input id=\"app-name\" value=\"{escape a.name}\" maxlength=\"{SignIn.maxCredentialName}\" \
      autocomplete=\"off\" required>\n" ++
    "<h2>2. Add it to your app</h2>\n\
     <p>Scan this with your authenticator app, or enter the key by hand.</p>\n\
     <div class=\"enrol\">\n" ++ qr ++
    "<div class=\"enrol-key\">\n" ++
    s!"<p><a id=\"totp-uri\" href=\"{escape a.uri}\">On your phone? Open in your \
      authenticator app</a></p>\n" ++
    "<p class=\"key-label\">The key</p>\n" ++
    s!"<p><code id=\"totp-secret\">{escape (groupedKey a.secret)}</code></p>\n" ++
    "<p class=\"hint\">Time-based, 6 digits, every 30 seconds: the defaults every app uses.</p>\n\
     </div>\n</div>\n\
     <h2>3. Confirm it works</h2>\n\
     <label for=\"totp-code\">The 6-digit code your app shows now</label>\n\
     <input id=\"totp-code\" class=\"code\" inputmode=\"numeric\" autocomplete=\"one-time-code\" \
     placeholder=\"123456\">\n\
     <div class=\"buttons\">\n\
     <button type=\"button\" id=\"totp-confirm\">Add this app</button>\n\
     <a class=\"button secondary\" href=\"/account\">Cancel</a>\n</div>\n" ++
    s!"<p class=\"hint\">Nothing is saved until the code checks out. Finish within \
      {Account.enrolmentSeconds / 60} minutes, or load this page again for a new key.</p>"

/-- `GET /account/add/password`: set or change the password, where the
deployment allows passwords. -/
def addPassword : Handler := fun ctx r => withAccount ctx r "/account/add/password" fun _ u => do
  if !ctx.config.allowPasswords then
    return messagePage "Password" "This deployment does not use passwords." .notFound
  let has := (← ctx.store.findPassword u.id).isSome
  return htmlReply <| page "add-password" (if has then "Change your password" else "Set a password")
      [] (back := backToChoices) <|
    s!"<p class=\"lead\">At least {Account.minPasswordLength} characters. A password is never \
      enough on its own: pyle always asks for another method with it.</p>\n" ++
    s!"<label for=\"new-password\">New password (at least {Account.minPasswordLength} \
      characters)</label>\n" ++
    "<input id=\"new-password\" type=\"password\" autocomplete=\"new-password\">\n\
     <div class=\"buttons\">\n\
     <button type=\"button\" id=\"password-set\">Set the password</button>\n\
     <a class=\"button secondary\" href=\"/account\">Cancel</a>\n</div>"

/-- `GET /account/add/recovery-codes`: make a new set of recovery codes and
show them, once.  Making them is the script's `POST /account/recovery-codes`,
after asking, if the account has codes, whether to replace them. -/
def addRecovery : Handler := fun ctx r =>
    withAccount ctx r "/account/add/recovery-codes" fun _ u => do
  let unspent ← ctx.store.unspentRecoveryCodes u.id
  let total ← ctx.store.recoveryCodeCount u.id
  let replace := if total == 0 then "" else
    s!"<p class=\"notice\">You have {unspent} unused code{if unspent == 1 then "" else "s"}. \
      New codes replace them: the old ones stop working.</p>\n"
  return htmlReply <| page "add-recovery" "Recovery codes" [] (back := backToChoices) <|
    s!"<p class=\"lead\">{Factor.RecoveryCode.count} one-time codes to write down. Each works \
      once, together with another method, for when you lose a device.</p>\n" ++ replace ++
    s!"<button type=\"button\" id=\"recovery-generate\" data-replace=\"{total != 0}\">\
      Make new codes</button>\n" ++
    "<ol id=\"recovery-list\" class=\"codes\" hidden></ol>\n\
     <p id=\"recovery-done\" hidden>Write these codes down now: they are not shown again. \
     <a href=\"/account\">Back to your account</a></p>"

/-! ## Invitations -/

/-- `GET /invite/<token>`. -/
def invite : Handler := fun ctx r => do
  let some (_, inv) ← invitationOf ctx r
    | return messagePage "Invitation" "This invitation does not exist or has expired."
        .notFound
  let token := (r.param "token").getD ""
  return htmlReply <| page "invite" "Welcome" [("token", token)] <|
    s!"<div id=\"invite-form\">\n\
      <p>You are invited to an account named <strong>{escape inv.userName}</strong>. \
      Create a passkey for it on this device or on a security key.</p>\n" ++
    "<label for=\"passkey-name\">A name for the passkey</label>\n\
     <input id=\"passkey-name\" autocomplete=\"off\" placeholder=\"my laptop\">\n\
     <button type=\"button\" id=\"create\">Create a passkey</button>\n\
     </div>\n" ++
    -- Shown once the passkey is stored.  Signing in is a second ceremony, so it
    -- waits for the person to ask for it rather than following unannounced.
    s!"<div id=\"invite-done\" hidden>\n\
      <p class=\"notice\">Your account <strong>{escape inv.userName}</strong> is set up, \
      and your passkey is registered.</p>\n\
      <p>Sign in with it to continue to your account.</p>\n\
      <button type=\"button\" id=\"continue-signin\">Continue to sign in</button>\n\
      </div>"

/-! ## The rest -/

/-- `GET /`: the account. -/
def root : Handler := fun _ _ => return Reply.redirect "/account"

/-- `GET /assets/pyle.js`. -/
def scriptAsset : Handler := fun _ _ => return asset script "text/javascript; charset=utf-8"

/-- `GET /assets/pyle.css`. -/
def stylesheetAsset : Handler := fun _ _ => return asset stylesheet "text/css; charset=utf-8"

end Web
end Pyle