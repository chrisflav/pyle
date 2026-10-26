import Pyle.SignIn.Invite
import Pyle.Web.Html
import Pyle.Web.Assets

/-!
# The pages

Three pages, rendered here and driven by `/assets/pyle.js`:

* `GET /signin?return=…&max_age=…&acr=…` — the sign-in page of the seam
  with the protocol endpoints.  `acr` is the level the sign-in must reach, as
  a short name or an identifier (`Acr.ofName?`); without it, any.  A request
  whose session already satisfies `max_age` and `acr` is sent straight back to
  `return` (`303`); one with a session that does not is shown the page in
  step-up mode, which re-authenticates that session; one without a session is
  shown the sign-in page.  The page offers only what can reach the level: at
  `phr` and `phrh` a passkey alone, since nothing else is phishing-resistant;
  at `mfa` a passkey, a security key with a code or a password, or two codes;
  at `sfa` also a password or a security key alone.  It passes the level on to
  the endpoints, which refuse what falls short.  A step-up for an account that
  has nothing that could reach the level says so, and points to the account
  page.  A `return` that is not a path on this origin is refused with `400`
  rather than replaced, so a link that tried to misuse it fails visibly.
* `GET /account` — the account: how well it is protected (`safety`), its
  authenticators, the authenticator app, recovery codes, the password if the
  deployment allows them, and the sessions.  It nags until two authenticators
  are registered (§1), and until it has a passkey.  Without a session it sends
  the browser to sign in first.
* `GET /invite/<token>` — create an invited account with its first way in: a
  passkey, a security key, or a password where passwords are allowed.

Every value that reaches a page goes through `escape`.
-/

namespace Pyle
namespace Web

open Http Store SignIn

/-- The address of the sign-in page that comes back to `ret`. -/
def signInUrl (ret : String) : String :=
  "/signin?return=" ++ Factor.Totp.percentEncode ret

/-! ## Sign-in -/

/-- What the form for the other ways in says can be done with it, for a
sign-in that must reach `want` (`sfa` or `mfa`; above that the form is not
shown). -/
def otherWaysHint (passwords : Bool) (want : Acr) : String :=
  if want == .sfa then
    (if passwords then "Sign in with your password, or with a security key. " else
      "Sign in with a security key. ") ++
    "Fill in a code as well for a stronger sign-in, or two of these without a security key."
  else "This needs two factors: a security key with one of these, or two of these."

/-- The sign-in form for the other ways in: a name, then a password alone, two
of a password, a TOTP code and a recovery code, or a security key alone or
with one of them; `want` says which of these the hint offers.  In step-up
mode the name is the session's and cannot be changed. -/
def otherWays (passwords : Bool) (name : Option String) (want : Acr := .mfa) : String :=
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
  s!"<p class=\"hint\">{otherWaysHint passwords want}</p>\n" ++
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
    (if wantPhr then "" else otherWays passwords stepUpName want)

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
    | none => pure Acr.sfa
    | some a => match Acr.ofName? a with
      | some l => pure l
      | none => return messagePage "Sign in" "acr is not a level pyle knows." .badRequest
  match ← Session.current ctx r with
  | some s =>
    if Policy.satisfies s (← ctx.clock) maxAge want then return Reply.redirect ret
    let name := (← ctx.store.findUser s.user).map (·.name)
    let reachable := ((← Policy.accountLevel ctx s.user).getD .sfa).satisfies want
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
  | some .sfa =>
    if c.webauthn then
      ("This account can only sign in with a security key that does not ask for a PIN or \
        fingerprint. Add a passkey for stronger protection.", true)
    else ("This account can only sign in with a password. Add a passkey for stronger \
      protection.", true)
  | none => ("This account has no way to sign in on its own. Add a passkey.", true)

/-- The paragraph of the account page that says how well the account is
protected. -/
def safetyParagraph (c : Acr.Capabilities) : String :=
  let (text, nudge) := safety c
  s!"<p id=\"safety\"{if nudge then " class=\"notice\"" else ""}>{escape text}</p>\n"

/-- How an authenticator's key is held: synced or bound to one device. -/
def keyKind (c : Credential) : String :=
  if c.backupEligible then "synced passkey" else "device-bound"

/-- One authenticator in the list. -/
def credentialItem (c : Credential) : String :=
  let id := escape (b64 c.id)
  let verifies := if c.userVerified then "verifies you" else "touch only"
  let used := match c.lastUsed with
    | some t => s!"last used {formatTime t}"
    | none => "not used yet"
  s!"<li><strong>{escape c.name}</strong> <span class=\"meta\">{keyKind c}, {verifies}, added \
    {formatTime c.created}, {used}</span><br>\
    <button type=\"button\" data-action=\"rename\" data-id=\"{id}\">Rename</button> \
    <button type=\"button\" data-action=\"remove\" data-id=\"{id}\">Remove</button></li>"

/-- One session in the list. -/
def sessionItem (current : Session) (s : Session) : String :=
  let this := s.handle == current.handle
  let ua := if s.userAgent.isEmpty then "an unknown browser" else s.userAgent
  s!"<li>{escape ua} <span class=\"meta\">from {escape s.clientAddress}, signed in \
    {formatTime s.created}, last used {formatTime s.lastSeen}\
    {if this then ", this session" else ""}</span><br>\
    <button type=\"button\" data-action=\"end-session\" data-handle=\"{escape s.handle}\" \
    data-current=\"{this}\">End</button></li>"

/-- The account page's content. -/
def accountContent (ctx : Ctx) (s : Session) (u : User) : IO String := do
  let creds ← ctx.store.listCredentials u.id
  let totp ← ctx.store.findTotp u.id
  let count ← ctx.store.authenticatorCount u.id
  let recovery ← ctx.store.unspentRecoveryCodes u.id
  let hasPassword := (← ctx.store.findPassword u.id).isSome
  let sessions ← Session.list ctx u.id
  let caps ← Policy.capabilities ctx u.id
  let nag := if count < 2 then
      s!"<p class=\"notice\">You have {count} authenticator{if count == 1 then "" else "s"}. \
        Add a second, so that losing one does not lock you out.</p>\n"
    else ""
  let recoveryNag := if recovery == 0 then
      "<p class=\"notice\">You have no unused recovery codes. Generate some and keep them \
        somewhere safe.</p>\n"
    else ""
  let groups := if u.groups.isEmpty then "" else
    s!" <span class=\"meta\">groups: {escape (", ".intercalate u.groups)}</span>"
  let credList := String.intercalate "\n" (creds.toList.map credentialItem)
  let totpSection := if totp.isSome then
      "<p>An authenticator app is set up.</p>\n\
       <button type=\"button\" data-action=\"totp-remove\">Remove the authenticator app</button>"
    else
      "<p>No authenticator app is set up.</p>\n\
       <button type=\"button\" id=\"totp-begin\">Set up an authenticator app</button>\n\
       <div id=\"totp-setup\" hidden>\n\
       <p>Scan this with your authenticator app, or enter the key by hand.</p>\n\
       <img id=\"totp-qr\" class=\"qr\" alt=\"QR code for your authenticator app\" hidden>\n\
       <p><a id=\"totp-uri\" href=\"/account\">On your phone? \
       Open in your authenticator app</a></p>\n\
       <p>The key: <code id=\"totp-secret\"></code></p>\n\
       <label for=\"totp-code\">The code your app shows</label>\n\
       <input id=\"totp-code\" inputmode=\"numeric\" autocomplete=\"one-time-code\">\n\
       <button type=\"button\" id=\"totp-confirm\">Confirm</button>\n</div>"
  let passwordSection := if !ctx.config.allowPasswords then "" else
    "<h2>Password</h2>\n" ++
    (if hasPassword then "<p>A password is set. On its own it is the weakest way in, and \
        most services ask for more.</p>\n"
      else "<p>No password is set. On its own a password is the weakest way in, and most \
        services ask for more.</p>\n") ++
    "<label for=\"new-password\">New password (at least 12 characters)</label>\n\
     <input id=\"new-password\" type=\"password\" autocomplete=\"new-password\">\n\
     <button type=\"button\" id=\"password-set\">Set the password</button>\n" ++
    (if hasPassword then
      "<button type=\"button\" data-action=\"password-remove\">Remove the password</button>\n"
      else "")
  let sessionList := String.intercalate "\n" (sessions.toList.map (sessionItem s))
  return safetyParagraph caps ++ nag ++ recoveryNag ++
    s!"<p>Signed in as <strong>{escape u.name}</strong>.{groups}</p>\n" ++
    "<section>\n<h2>Passkeys and security keys</h2>\n" ++
    s!"<ul class=\"items\">\n{credList}\n</ul>\n" ++
    "<label for=\"new-name\">A name for a new one</label>\n\
     <input id=\"new-name\" autocomplete=\"off\">\n\
     <button type=\"button\" id=\"add-authenticator\">Add a passkey or security key</button>\n\
     </section>\n<section>\n<h2>Authenticator app</h2>\n" ++ totpSection ++
    "\n</section>\n<section>\n<h2>Recovery codes</h2>\n" ++
    s!"<p>{recovery} of {Factor.RecoveryCode.count} unused.</p>\n" ++
    "<button type=\"button\" id=\"recovery-generate\">Generate new recovery codes</button>\n\
     <ol id=\"recovery-list\" hidden></ol>\n</section>\n<section>\n" ++ passwordSection ++
    "</section>\n<section>\n<h2>Sessions</h2>\n" ++
    s!"<ul class=\"items\">\n{sessionList}\n</ul>\n" ++
    "<button type=\"button\" id=\"sign-out\">Sign out</button>\n</section>"

/-- `GET /account`. -/
def account : Handler := fun ctx r => do
  let some s ← Session.current ctx r | return Reply.redirect (signInUrl "/account")
  let some u ← ctx.store.findUser s.user | return Reply.redirect (signInUrl "/account")
  let caps ← Policy.capabilities ctx u.id
  return htmlReply (page "account" "Your account"
    [("passkey", if caps.verifying then "true" else "false")] (← accountContent ctx s u))

/-! ## Invitations -/

/-- `GET /invite/<token>`. -/
def invite : Handler := fun ctx r => do
  let some (_, inv) ← invitationOf ctx r
    | return messagePage "Invitation" "This invitation does not exist or has expired."
        .notFound
  let token := (r.param "token").getD ""
  let password := if !ctx.config.allowPasswords then "" else
    "<label for=\"invite-password\">Or a password (at least 12 characters)</label>\n\
     <input id=\"invite-password\" type=\"password\" autocomplete=\"new-password\">\n\
     <button type=\"button\" id=\"create-password\" class=\"secondary\">Use a password</button>\n\
     <p class=\"hint\">A password alone is the weakest way in; many services will ask for \
       more. Add a passkey once you are signed in.</p>\n"
  return htmlReply <| page "invite" "Welcome" [("token", token)] <|
    s!"<div id=\"invite-form\">\n\
      <p>You are invited to an account named <strong>{escape inv.userName}</strong>. \
      Choose how you will sign in to it.</p>\n" ++
    "<label for=\"passkey-name\">A name for the passkey or security key</label>\n\
     <input id=\"passkey-name\" autocomplete=\"off\" placeholder=\"my laptop\">\n\
     <button type=\"button\" id=\"create\">Create a passkey</button>\n\
     <p class=\"hint\">On this device, or on a security key that asks for your PIN or \
       fingerprint: the strongest choice.</p>\n\
     <button type=\"button\" id=\"create-key\" class=\"secondary\">Use a security key \
       without a PIN</button>\n\
     <p class=\"hint\">A key you only touch signs in alone at the lowest level; many \
       services will ask for more.</p>\n" ++ password ++
    "</div>\n" ++
    -- Shown once the first factor is stored.  Signing in is a step of its own,
    -- so it waits for the person to ask for it rather than following unannounced.
    s!"<div id=\"invite-done\" hidden>\n\
      <p class=\"notice\">Your account <strong>{escape inv.userName}</strong> is set up.</p>\n\
      <p id=\"invite-level\"></p>\n\
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