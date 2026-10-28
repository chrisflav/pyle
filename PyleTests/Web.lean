import PyleTests.Account

/-!
# The pages

The pages, their assets and the invitation flow, through
`Server.route`.  No browser runs here, so the script is checked against the
server by reading it: every endpoint it posts to is a `POST` route, every page
it navigates to is a `GET` route, every element id it looks up is on a page,
and every account action it handles is a button on the account page.  The
pages are checked for what the Content Security Policy forbids: inline
script, inline style and event-handler attributes.
-/

namespace PyleTests

open Pyle Pyle.Http Pyle.WebAuthn Pyle.Encoding
open Lean (Json toJson)

/-- The quoted strings that follow `marker` in `s`, up to the next `'`. -/
def quotedAfter (s marker : String) : List String :=
  ((s.splitOn marker).drop 1).map fun piece => (piece.splitOn "'").headD ""

/-- Whether some route answers `method` at `path` (ignoring the query). -/
def routed (method : Std.Http.Method) (path : String) : Bool :=
  let path := (path.splitOn "?").headD path
  match pathSegments path with
  | some segs => Server.routes.any fun rt =>
    rt.method == method && (matchPattern rt.pattern segs).isSome
  | none => false

/-- Escaping. -/
def escapeTests : IO Unit := do
  group "web: escaping and dates"
  checkEq "the five characters" (Web.escape "<a href=\"x\">&'") "&lt;a href=&quot;x&quot;&gt;&amp;&#39;"
  checkEq "the epoch" (Web.formatTime 0) "1 Jan 1970, 00:00 UTC"
  checkEq "a leap day" (Web.formatTime 951782400) "29 Feb 2000, 00:00 UTC"
  checkEq "the test clock" (Web.formatTime 1700000000) "14 Nov 2023, 22:13 UTC"
  checkEq "a date, as the prototype writes it" (Web.formatDate 1793000000) "26 Oct 2026"
  checkEq "December" (Web.formatDate 1703980800) "31 Dec 2023"
  for (s, n) in [("7d", some 604800), ("12h", some 43200), ("30m", some 1800), ("90s", some 90),
      ("d", none), ("7", none), ("0d", none), ("-1d", none), ("7w", none)] do
    checkEq s!"lifetime {s}" (SignIn.parseDuration s) n

/-- The configuration keys of this round. -/
def signInConfigTests : IO Unit := do
  group "web: configuration"
  let base := "{\"issuer\":\"https://a.example\",\"rpId\":\"a.example\",\
    \"origins\":[\"https://a.example\"]"
  let parse (extra : String) := (Json.parse (base ++ extra ++ "}")).toOption.map
    (Config.ofJson · "/etc/pyle")
  let ok (extra : String) : Bool := match parse extra with
    | some (.ok _) => true
    | _ => false
  match parse "" with
  | some (.ok c) =>
    check "passwords are off by default" (!c.allowPasswords)
    check "no attestation roots or allow-list by default"
      (c.attestationRoots.isEmpty && c.aaguidAllowList.isEmpty)
  | _ => check "the minimal configuration parses" false
  match parse ",\"allowPasswords\":true,\"attestationRoots\":[\"roots.pem\"],\
      \"aaguidAllowList\":[\"F00DF00D-F00D-F00D-F00D-F00DF00DF00D\"]" with
  | some (.ok c) =>
    check "allowPasswords" c.allowPasswords
    checkEq "roots are relative to the configuration" c.attestationRoots
      [("/etc/pyle" : System.FilePath) / "roots.pem"]
    checkEq "AAGUIDs are normalised" c.aaguidAllowList ["f00df00df00df00df00df00df00df00d"]
  | _ => check "the sign-in keys parse" false
  check "an allow-list needs roots"
    (!ok ",\"aaguidAllowList\":[\"f00df00df00df00df00df00df00df00d\"]")
  check "an AAGUID must be 32 hex digits"
    (!ok ",\"attestationRoots\":[\"r.pem\"],\"aaguidAllowList\":[\"f00d\"]")
  check "allowPasswords must be a boolean" (!ok ",\"allowPasswords\":\"yes\"")
  let hosts := ",\"forwardAuthHosts\":{\"app.a.example\":\"allow if user($u);\"}"
  check "forward-auth hosts need the proxy's secret" (!ok hosts)
  check "and parse with it" (ok (hosts ++ ",\"forwardAuthSecret\":\"0123456789abcdef\""))
  check "which is at least 16 characters"
    (!ok (hosts ++ ",\"forwardAuthSecret\":\"0123456789abcde\""))

/-- Assets and the policy every page lives under. -/
def assetTests : IO Unit := withSignInCtx (fun c => { c with allowPasswords := true })
    fun ctx clock => do
  group "web: assets and the content security policy"
  let js ← getPage ctx "/assets/pyle.js"
  checkEq "the script is served" (js.status.toCode, js.contentType)
    (200, "text/javascript; charset=utf-8")
  checkEq "it is the embedded one" js.bodyText Web.script
  let css ← getPage ctx "/assets/pyle.css"
  checkEq "the stylesheet is served" (css.status.toCode, css.contentType)
    (200, "text/css; charset=utf-8")
  check "under the strict policy" (hasHeader js "Content-Security-Policy" contentSecurityPolicy)
  let root ← getPage ctx "/"
  checkEq "/ goes to the account" (root.status.toCode, root.header "Location")
    (303, some "/account")
  let u ← ctx.store.addUser "lee" [] 1
  let (id, lk) ← sessionFor ctx u
  discard <| signInVia ctx lk
  discard <| giveTotp ctx u
  ctx.store.setPassword u.id "$argon2id$v=19$m=65536,t=3,p=4$AAAAAAAAAAAAAAAAAAAAAA$AAAA" 1
  let inviteUrl ← SignIn.createInvitation ctx.store ctx.config.issuer "newbie" [] 3600 1700000000
  let invitePath := (inviteUrl.drop ctx.config.issuer.length).toString
  clock.modify (· + 1)
  let mut pages := []
  for (name, path, cookie) in [("sign-in", "/signin", none), ("step-up", "/signin?max_age=0", some id),
      ("account", "/account", some id), ("add", "/account/add", some id),
      ("authenticator-app", "/account/add/app", some id),
      ("password", "/account/add/password", some id),
      ("recovery-codes", "/account/add/recovery-codes", some id),
      ("invitation", invitePath, none),
      ("a missing invitation", "/invite/AAAA", none)] do
    let r ← getPage ctx path cookie
    check s!"the {name} page is HTML" (r.contentType == "text/html; charset=utf-8")
    check s!"under the strict policy"
      (hasHeader r "Content-Security-Policy" contentSecurityPolicy &&
        hasHeader r "X-Frame-Options" "DENY")
    let html := r.bodyText
    check s!"the {name} page loads the script and the stylesheet from this origin"
      (containsStr html "<script src=\"/assets/pyle.js\" defer></script>" &&
        containsStr html "<link rel=\"stylesheet\" href=\"/assets/pyle.css\">")
    check s!"the {name} page has no inline script, style or handler"
      (!containsStr html "<script>" && !containsStr html " style=" &&
        !containsStr html "<style" && !containsStr html " onclick=" &&
        !containsStr html " onsubmit=" && !containsStr html " onload=" &&
        !containsStr html "javascript:")
    pages := html :: pages
  -- The authenticator-app page: the QR code, then the link with a label of its
  -- own, then the key to type in, all written by the server.
  let setup := (← getPage ctx "/account/add/app" (some id)).bodyText
  let posOf (s : String) : Nat := ((setup.splitOn s).headD setup).length
  check "the app page has the QR code with alternative text"
    (containsStr setup "<img id=\"totp-qr\" class=\"qr\" \
      alt=\"QR code for your authenticator app\" src=\"data:image/svg+xml;base64,")
  check "and says it can be scanned or typed"
    (containsStr setup "Scan this with your authenticator app, or enter the key by hand")
  check "the link to the app is labelled in the page"
    (containsStr setup ">On your phone? Open in your authenticator app</a>")
  check "the QR code, the link and the key, in that order"
    (posOf "id=\"totp-qr\"" < posOf "id=\"totp-uri\"" &&
      posOf "id=\"totp-uri\"" < posOf "id=\"totp-secret\"" &&
      posOf "id=\"totp-secret\"" < setup.length)
  check "the script sends the sealed secret back with the code and the name"
    (containsStr Web.script "pending: body.dataset.pending" &&
      containsStr Web.script "name: value('app-name')")
  check "the stylesheet gives the QR code a white ground"
    (containsStr Web.stylesheet "img.qr {" && containsStr Web.stylesheet "background: #fff")
  check "and lets the table scroll in its box"
    (containsStr Web.stylesheet ".table-scroll { overflow-x: auto;")
  -- With passwords off, the account page and the choices offer none.
  let v ← ctx.store.addUser "vic" [] 1
  let (vid, _) ← sessionFor ctx v
  let off := { ctx with config := { ctx.config with allowPasswords := false } }
  check "with passwords off, no password row or choice"
    (!containsStr (← getPage off "/account" (some vid)).bodyText "/account/add/password" &&
      !containsStr (← getPage off "/account/add" (some vid)).bodyText "/account/add/password")
  let all := String.join pages
  -- The script against the pages.
  let script := Web.script
  check "the script never writes HTML" (!containsStr script "innerHTML" &&
    !containsStr script "outerHTML" && !containsStr script "document.write" &&
    !containsStr script "eval(")
  let ids := (quotedAfter script " on('" ++ quotedAfter script "getElementById('" ++
    quotedAfter script "value('" ++ quotedAfter script "rawValue('").eraseDups
  check "the script looks up elements" (ids.length ≥ 20)
  for i in ids do
    check s!"element #{i} is on a page" (containsStr all s!"id=\"{i}\"")
  for a in (quotedAfter script "action === '").eraseDups do
    check s!"account action {a} is a button" (containsStr all s!"data-action=\"{a}\"")
  for d in ["mode", "return", "token", "id", "handle", "current", "pending", "kind", "replace"] do
    check s!"data-{d} is written by a page" (containsStr all s!"data-{d}=\"")
  let posts := (quotedAfter script "post('" ++ quotedAfter script "act('" ++
    quotedAfter script "getAssertion('").eraseDups
  check "the script posts to endpoints" (posts.length ≥ 14)
  for p in posts do
    check s!"POST {p} is a route" (routed .post p)
  -- Named in the script by variables or ternaries, which `quotedAfter` cannot see.
  for p in ["/invite/x/begin", "/invite/x/finish", "/signin/webauthn/begin",
      "/signin/webauthn/finish", "/signin/stepup/begin", "/signin/stepup/finish",
      "/signin/codes"] do
    check s!"POST {p} is a route" (routed .post p)
    check s!"and the script names {p}"
      (p.startsWith "/invite/" || containsStr script s!"'{p}'")
  check "the script uses both invitation endpoints"
    (containsStr script "base + '/begin'" && containsStr script "base + '/finish'")
  for p in (quotedAfter script "location.assign('").eraseDups do
    check s!"GET {p} is a route" (routed .get p)
  for k in ["challenge", "rpId", "timeout", "userVerification", "allowCredentials", "rp",
      "user", "pubKeyCredParams", "attestation", "authenticatorSelection",
      "excludeCredentials", "redirect", "codes"] do
    check s!"the script reads {k}" (containsStr script s!"o.{k}" ||
      containsStr script s!"data.{k}")
  for (p, d) in [("add", "kind"), ("add-app", "pending"), ("add-recovery", "replace")] do
    check s!"the script handles the {p} page and reads its data-{d}"
      (containsStr script s!"body.dataset.page === '{p}'" &&
        containsStr script s!"dataset.{d}")

/-- A `return` with HTML in it is escaped into the page. -/
def pageEscapeTests : IO Unit := withCtx fun ctx _ => do
  group "web: escaping into pages"
  let r ← getPage ctx "/signin?return=%2Fx%3Fq%3D%22%3E%3Cscript%3E"
  checkEq "a return with quotes and brackets is accepted" r.status.toCode 200
  check "and escaped" (containsStr r.bodyText "data-return=\"/x?q=&quot;&gt;&lt;script&gt;\"" &&
    !containsStr r.bodyText "\"><script>")
  let bad ← getPage ctx "/signin?return=%2Fx&return=%2Fy"
  checkEq "two returns are none, which defaults" bad.status.toCode 200
  check "to the account" (containsStr bad.bodyText "data-return=\"/account\"")
  let age ← getPage ctx "/signin?max_age=soon"
  checkEq "a max_age that is not a number is refused" age.status.toCode 400

/-- Invitations, from `pyle invite` to the first sign-in. -/
def invitationTests : IO Unit := withCtx fun ctx clock => do
  group "web: invitations"
  let now ← clock.get
  let url ← SignIn.createInvitation ctx.store ctx.config.issuer "newbie" ["staff"] 3600 now
  check "the link is under the issuer" (url.startsWith "https://auth.example.org/invite/")
  let path := (url.drop ctx.config.issuer.length).toString
  let token := (path.drop "/invite/".length).toString
  check "the token is 256 bits of base64url" ((Base64Url.decode token).map (·.size) == some 32)
  let stored ← ctx.store.run fun c =>
    Store.query c "SELECT token_hash FROM invitations" #[] (Store.colBlob · 0)
  check "only its hash is stored"
    (stored.toList == [(Store.SecretHash.of ((Base64Url.decode token).getD .empty)).bytes])
  check "an invalid name is refused"
    (← throws (SignIn.createInvitation ctx.store ctx.config.issuer "Not Valid" [] 60 now))
  discard <| ctx.store.addUser "taken" [] 1
  check "a taken name is refused"
    (← throws (SignIn.createInvitation ctx.store ctx.config.issuer "taken" [] 60 now))
  let page ← getPage ctx path
  checkEq "the invitation page answers 200" page.status.toCode 200
  check "greeting the account by name" (containsStr page.bodyText "<strong>newbie</strong>")
  check "and carrying the token for the script"
    (containsStr page.bodyText s!"data-token=\"{token}\"")
  check "with the confirmation hidden until the passkey is stored"
    (containsStr page.bodyText "<div id=\"invite-done\" hidden>")
  check "which leads on to sign-in"
    (containsStr page.bodyText "id=\"continue-signin\"")
  let inviteScript :=
    ((Web.script.splitOn "function setupInvite").getD 1 "").splitOn "document.addEventListener"
  check "the script shows the confirmation instead of signing in at once"
    (containsStr Web.script "getElementById('invite-done').hidden = false" &&
      !containsStr (inviteScript.headD "") "getAssertion(" &&
      !containsStr (inviteScript.headD "") "finish(")
  let signin ← getPage ctx "/signin?return=%2Faccount"
  checkEq "the sign-in it leads to answers 200" signin.status.toCode 200
  check "and returns to the account" (containsStr signin.bodyText "data-return=\"/account\"")
  checkEq "a malformed token is 404" (← getPage ctx "/invite/xyz").status.toCode 404
  checkEq "an unknown token is 404"
    (← getPage ctx s!"/invite/{b64u (← Crypto.randomBytes 32)}").status.toCode 404
  let b ← postJson ctx (path ++ "/begin") emptyObj
  checkEq "begin answers 200" b.status.toCode 200
  let opts := replyJson b
  let sel := (opts.getObjVal? "authenticatorSelection").toOption.getD .null
  checkEq "a discoverable credential is required" (jstr sel "residentKey") "required"
  checkEq "and user verification" (jstr sel "userVerification") "required"
  checkEq "for the invited name" (jstr ((opts.getObjVal? "user").toOption.getD .null) "name")
    "newbie"
  -- A security key that does not verify the user is refused, and the
  -- invitation survives.
  let weak ← SoftKey.new (uv := false)
  let r1 ← postJson ctx (path ++ "/finish")
    (Json.mkObj [("credential", ← weak.create opts)])
  checkEq "a credential without user verification is refused" r1.status.toCode 400
  check "the invitation is still good"
    ((← ctx.store.findInvitation (.of ((Base64Url.decode token).getD .empty)) now).isSome)
  -- A passkey.
  let k ← SoftKey.new (backupEligible := true)
  let b2 ← postJson ctx (path ++ "/begin") emptyObj
  let spare ← postJson ctx (path ++ "/begin") emptyObj
  let cred ← k.create (replyJson b2)
  let r2 ← postJson ctx (path ++ "/finish")
    (Json.mkObj [("credential", cred), ("name", "phone")])
  checkEq "a passkey registers" (r2.status.toCode, jstr (replyJson r2) "name") (201, "newbie")
  check "and no session yet" (sessionCookieOf r2).isNone
  let some u ← ctx.store.findUserByName "newbie" | check "the account exists" false
  checkEq "with the invitation's groups" u.groups ["staff"]
  checkEq "and its passkey" ((← ctx.store.listCredentials u.id).toList.map (·.name)) ["phone"]
  checkEq "the invitation is used up" (← getPage ctx path).status.toCode 404
  checkEq "begin too" (← postJson ctx (path ++ "/begin") emptyObj).status.toCode 404
  let k2 ← SoftKey.new
  let r3 ← postJson ctx (path ++ "/finish")
    (Json.mkObj [("credential", ← k2.create (replyJson spare))])
  checkEq "a second registration with it is refused" r3.status.toCode 404
  checkEq "and no second account is made" (← ctx.store.listUsers).size 2
  -- The page then signs in with the passkey: the handle must be the account's.
  let signIn ← signInVia ctx k
  checkEq "the new passkey signs in" signIn.status.toCode 200
  checkEq "as newbie" ((← Session.current ctx (withCookie ((sessionCookieOf signIn).getD "")))
    |>.map (·.user)) (some u.id)
  checkEq "amr: a synced passkey" ((replyJson signIn).getObjValAs? (List String) "amr").toOption
    (some ["swk", "user"])
  let summary ← auditSummary ctx
  check "audited" (summary.contains ("invitation-used", "success") &&
    summary.contains ("register", "success"))
  -- An expired invitation.
  let url2 ← SignIn.createInvitation ctx.store ctx.config.issuer "late" [] 60 (← clock.get)
  clock.modify (· + 61)
  let path2 := (url2.drop ctx.config.issuer.length).toString
  checkEq "an expired invitation is 404" (← getPage ctx path2).status.toCode 404
  checkEq "and cannot begin" (← postJson ctx (path2 ++ "/begin") emptyObj).status.toCode 404

/-- An invitation with an email address and a display name: `pyle invite
--email --display-name` refuses a bad or taken address, and the account the
link creates has both, which its account page shows and does not offer to
change. -/
def inviteWithEmailTests : IO Unit := withCtx fun ctx clock => do
  group "web: invitations with an email address"
  let now ← clock.get
  let invite (name : String) (email displayName : Option String) :=
    SignIn.createInvitation ctx.store ctx.config.issuer name [] 3600 now (email := email)
      (displayName := displayName)
  discard <| ctx.store.addUser "taken" [] 1 (email := some "Taken@example.org")
  check "a bad address is refused" (← throws (invite "pat" (some "pat at example.org") none))
  check "so is one another account has, in any case"
    (← throws (invite "pat" (some "taken@EXAMPLE.org") none))
  check "and a bad display name" (← throws (invite "pat" none (some "\x1b[31m")))
  check "none of which leaves an invitation" ((← ctx.store.run fun c =>
    Store.query c "SELECT 1 FROM invitations" #[] (Store.colInt · 0)).isEmpty)
  let url ← invite "pat" (some " Pat@Example.org ") (some "Pat <O'Hara>")
  let path := (url.drop ctx.config.issuer.length).toString
  let k ← SoftKey.new
  let b ← postJson ctx (path ++ "/begin") emptyObj
  let r ← postJson ctx (path ++ "/finish") (Json.mkObj [("credential", ← k.create (replyJson b))])
  checkEq "the passkey registers" r.status.toCode 201
  let some u ← ctx.store.findUserByName "pat" | check "the account exists" false
  checkEq "with the invitation's address, trimmed, and display name"
    (u.email, u.displayName) (some "Pat@Example.org", some "Pat <O'Hara>")
  let some cookie := sessionCookieOf (← signInVia ctx k) | check "pat signs in" false
  let page := (← getPage ctx "/account" cookie).bodyText
  check "the account page shows the address"
    (containsStr page "<span id=\"email\">Pat@Example.org</span>")
  check "and the display name, escaped"
    (containsStr page "<span id=\"display-name\">Pat &lt;O&#39;Hara&gt;</span>")
  check "as set by the administrator" (containsStr page "set by your administrator")
  check "with nothing to change them" (!containsStr page "<input id=\"email\"" &&
    !containsStr page "name=\"email\"")
  let some taken ← ctx.store.findUserByName "taken" | check "the other account" false
  let (cookie2, _) ← sessionFor ctx taken
  let page2 := (← getPage ctx "/account" cookie2).bodyText
  check "an account without a display name shows its name and says so"
    (containsStr page2 "<span id=\"display-name\">taken <span class=\"meta\">(no display name set)")

/-- What the account page says about how well an account is protected. -/
def safetyTests : IO Unit := do
  group "web: account safety"
  let says (c : Acr.Capabilities) (text : String) (nudge : Bool) : IO Unit := do
    let (t, n) := Web.safety c
    check s!"says {text.take 40}…" (containsStr t text && n == nudge) s!"{t} {n}"
  says { verifyingDeviceBound := true, verifying := true, webauthn := true } "strongest" false
  says { verifying := true, webauthn := true } "a passkey, which cannot be phished" false
  says { webauthn := true, totp := true } "two factors, but has no passkey" true
  says { password := true, recovery := true } "two factors" true
  says { password := true } "cannot sign in again" true
  says { webauthn := true } "cannot sign in again" true
  says {} "cannot sign in again" true
  for (c, level) in [(({ totp := true, recovery := true } : Acr.Capabilities), some Acr.mfa),
      ({ totp := true }, none), ({ recovery := true }, none), ({ password := true }, none),
      ({ webauthn := true }, none), ({ verifying := true, webauthn := true }, some .phr)] do
    check s!"the level of {repr c}" (c.level == level)

/-- The web tests. -/
def webTests : IO Unit := do
  escapeTests
  signInConfigTests
  assetTests
  pageEscapeTests
  invitationTests
  inviteWithEmailTests
  safetyTests

end PyleTests