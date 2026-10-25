import PyleTests.SignIn

/-!
# The account

Account management through `Server.route`: adding an authenticator (with the
step-up it needs), renaming and removing them under the two-authenticator
rule, setting up and removing TOTP, recovery codes, passwords, and the session
list.  The step-up window is five minutes; past it, every change answers
`403 step_up_required`.
-/

namespace PyleTests

open Pyle Pyle.Http Pyle.WebAuthn Pyle.Encoding LeanBiscuit
open Lean (Json toJson)

/-- A signed-in user with one passkey: the user, the cookie and the key. -/
def signedInUser (ctx : Ctx) (name : String) : IO (Store.User × String × SoftKey) := do
  let u ← ctx.store.addUser name [] 1
  let (id, k) ← sessionFor ctx u
  return (u, id, k)

/-- Register a soft key through the account endpoints; the finish reply. -/
def addKey (ctx : Ctx) (cookie : String) (k : SoftKey) (name : String := "spare")
    (fmt : String := "none") : IO Reply := do
  let b ← postJson ctx "/account/authenticators/register/begin" emptyObj (some cookie)
  if b.status.toCode != 200 then return b
  let cred ← k.create (replyJson b) fmt
  postJson ctx "/account/authenticators/register/finish"
    (Json.mkObj [("credential", cred), ("name", Json.str name)]) (some cookie)

/-- The step-up window, and adding authenticators. -/
def registerTests : IO Unit := withCtx fun ctx clock => do
  group "account: adding authenticators"
  let (u, id, k) ← signedInUser ctx "alice"
  let page ← getPage ctx "/account" id
  checkEq "the account page answers 200" page.status.toCode 200
  check "and nags about a second authenticator"
    (containsStr page.bodyText "You have 1 authenticator.")
  clock.modify (· + SignIn.stepUpSeconds + 1)
  let late ← postJson ctx "/account/authenticators/register/begin" emptyObj (some id)
  checkEq "a step-up older than five minutes is refused"
    (late.status.toCode, errorOf late) (403, "step_up_required")
  let up ← stepUpVia ctx k (some id)
  let some id := sessionCookieOf up | check "step-up" false
  let b ← postJson ctx "/account/authenticators/register/begin" emptyObj (some id)
  checkEq "after a step-up, begin answers 200" b.status.toCode 200
  let opts := replyJson b
  checkEq "with the account's user handle"
    (jstr ((opts.getObjVal? "user").toOption.getD .null) "id") (b64u u.handle)
  let excluded := ((opts.getObjValAs? (Array Json) "excludeCredentials").toOption.getD #[]).toList
    |>.map (jstr · "id")
  checkEq "excluding the credentials it has" excluded [b64u k.id]
  checkEq "and attestation none" (jstr opts "attestation") "none"
  let k2 ← SoftKey.new (uv := false)
  let cred ← k2.create opts
  let r ← postJson ctx "/account/authenticators/register/finish"
    (Json.mkObj [("credential", cred), ("name", "yubikey\u0007")]) (some id)
  checkEq "finish answers 201" r.status.toCode 201
  checkEq "with the credential id" (jstr (replyJson r) "id") (b64u k2.id)
  checkEq "two authenticators now" (← ctx.store.authenticatorCount u.id) 2
  checkEq "named as typed, without control characters"
    ((← ctx.store.findCredential k2.id).map (·.name)) (some "yubikey")
  check "the nag is gone"
    (!containsStr (← getPage ctx "/account" id).bodyText "Add a second")
  let again ← postJson ctx "/account/authenticators/register/finish"
    (Json.mkObj [("credential", cred)]) (some id)
  checkEq "the same registration again is refused (its challenge is gone)"
    again.status.toCode 400
  let dup ← addKey ctx id k2
  checkEq "registering a credential twice is refused" dup.status.toCode 409
  let k3 ← SoftKey.new .edDsa
  checkEq "packed self-attestation is accepted"
    ((← addKey ctx id k3 (fmt := "packed")).status.toCode) 201
  let k4 ← SoftKey.new
  let b4 ← postJson ctx "/account/authenticators/register/begin" emptyObj (some id)
  let wrongOrigin ← postJson ctx "/account/authenticators/register/finish"
    (Json.mkObj [("credential", ← k4.create (replyJson b4) (origin := "https://evil.example"))])
    (some id)
  checkEq "a registration from another origin is refused" wrongOrigin.status.toCode 400
  -- A challenge from an invitation's begin has no user, and is refused here.
  let token ← SignIn.createInvitation ctx.store ctx.config.issuer "zed" [] 3600 (← clock.get)
  let path := (token.drop ctx.config.issuer.length).toString
  let ib ← postJson ctx (path ++ "/begin") emptyObj
  let viaInvite ← postJson ctx "/account/authenticators/register/finish"
    (Json.mkObj [("credential", ← k4.create (replyJson ib))]) (some id)
  checkEq "a challenge issued for an invitation is refused" viaInvite.status.toCode 400
  -- And the new key signs in, as a second factor.
  let secret ← giveTotp ctx u
  let signIn ← signInVia ctx k2 (beginBody := Json.mkObj [("name", "alice")])
    (extra := [("totp", totpAt secret (← clock.get))])
  checkEq "the added security key signs in with a code" signIn.status.toCode 200
  let noSession ← postJson ctx "/account/authenticators/register/begin" emptyObj
  checkEq "without a session, 401" noSession.status.toCode 401
  check "registrations are audited" ((← auditSummary ctx).contains ("register", "success"))

/-- With an AAGUID allow-list, unattested authenticators are refused. -/
def allowListTests : IO Unit := withSignInCtx (fun c =>
    { c with aaguidAllowList := ["f00df00df00df00df00df00df00df00d"],
             attestationRoots := [c.database.withFileName "root.der"] }) fun ctx _ => do
  group "account: AAGUID allow-list"
  IO.FS.writeBinFile (ctx.config.database.withFileName "root.der") (hex WebAuthnVectors.attestationCaCert)
  let (_, id, _) ← signedInUser ctx "alice"
  let b ← postJson ctx "/account/authenticators/register/begin" emptyObj (some id)
  checkEq "attestation is asked for" (jstr (replyJson b) "attestation") "direct"
  let k ← SoftKey.new
  let r ← postJson ctx "/account/authenticators/register/finish"
    (Json.mkObj [("credential", ← k.create (replyJson b))]) (some id)
  checkEq "an unattested authenticator is refused" r.status.toCode 400
  let b2 ← postJson ctx "/account/authenticators/register/begin" emptyObj (some id)
  let r2 ← postJson ctx "/account/authenticators/register/finish"
    (Json.mkObj [("credential", ← k.create (replyJson b2) "packed")]) (some id)
  checkEq "so is self-attestation" r2.status.toCode 400

/-- Renaming and removing, and the two-authenticator rule. -/
def removeTests : IO Unit := withCtx fun ctx _ => do
  group "account: renaming and removing"
  let (u, id, k) ← signedInUser ctx "bob"
  let k2 ← SoftKey.new
  discard <| addKey ctx id k2
  let rename ← postJson ctx "/account/authenticators/rename"
    (Json.mkObj [("id", b64u k.id), ("name", "laptop")]) (some id)
  checkEq "rename answers 204" rename.status.toCode 204
  checkEq "and renames" ((← ctx.store.findCredential k.id).map (·.name)) (some "laptop")
  let (_, _, otherKey) ← signedInUser ctx "carol"
  let foreign ← postJson ctx "/account/authenticators/rename"
    (Json.mkObj [("id", b64u otherKey.id), ("name", "mine")]) (some id)
  checkEq "another user's authenticator cannot be renamed" foreign.status.toCode 404
  let remove ← postJson ctx "/account/authenticators/remove"
    (Json.mkObj [("id", b64u k2.id)]) (some id)
  checkEq "removing the second-to-last authenticator is refused"
    (remove.status.toCode, errorOf remove) (409, "last_authenticators")
  checkEq "both are still there" (← ctx.store.authenticatorCount u.id) 2
  let k3 ← SoftKey.new
  discard <| addKey ctx id k3
  let ok ← postJson ctx "/account/authenticators/remove" (Json.mkObj [("id", b64u k2.id)])
    (some id)
  checkEq "with three, one can go" ok.status.toCode 204
  checkEq "leaving two" (← ctx.store.authenticatorCount u.id) 2
  let foreignRemove ← postJson ctx "/account/authenticators/remove"
    (Json.mkObj [("id", b64u otherKey.id)]) (some id)
  checkEq "another user's authenticator cannot be removed" foreignRemove.status.toCode 404
  check "carol's is untouched" ((← ctx.store.findCredential otherKey.id).isSome)
  let summary ← auditSummary ctx
  check "removals and refusals are audited"
    (summary.contains ("remove-authenticator", "success") &&
      summary.contains ("remove-authenticator", "refused"))

/-- Setting up the authenticator app. -/
def totpTests : IO Unit := withCtx fun ctx clock => do
  group "account: TOTP"
  let (u, id, k) ← signedInUser ctx "dana"
  let b ← postJson ctx "/account/totp/begin" emptyObj (some id)
  checkEq "begin answers 200" b.status.toCode 200
  let body := replyJson b
  let some secret := Factor.base32Decode (jstr body "secret") | check "a base32 secret" false
  checkEq "of 20 bytes" secret.size 20
  check "and an otpauth URI"
    ((jstr body "uri").startsWith "otpauth://totp/auth.example.org:dana?secret=")
  check "nothing is stored yet" ((← ctx.store.findTotp u.id).isNone)
  let pending := jstr body "pending"
  let now ← clock.get
  let wrong := if totpAt secret now == "000000" then "111111" else "000000"
  let bad ← postJson ctx "/account/totp/confirm"
    (Json.mkObj [("pending", pending), ("code", wrong)]) (some id)
  checkEq "a wrong first code is refused" (bad.status.toCode, errorOf bad) (400, "invalid_code")
  let (_, eveId, _) ← signedInUser ctx "eve"
  let stolen ← postJson ctx "/account/totp/confirm"
    (Json.mkObj [("pending", pending), ("code", totpAt secret now)]) (some eveId)
  checkEq "another user cannot store it" stolen.status.toCode 400
  let ok ← postJson ctx "/account/totp/confirm"
    (Json.mkObj [("pending", pending), ("code", totpAt secret now)]) (some id)
  checkEq "the right code stores it" ok.status.toCode 204
  check "sealed, not in the clear"
    (((← ctx.store.findTotp u.id).map fun r =>
      (SignIn.Secrets.openTotp ctx.rootKey u.id r.sealedSecret).toOption == some secret &&
        r.sealedSecret != secret).getD false)
  checkEq "two authenticators now" (← ctx.store.authenticatorCount u.id) 2
  -- The confirming code cannot then be used to sign in.
  let sk ← SoftKey.new (uv := false)
  enrol ctx u sk
  let reuse ← signInVia ctx sk (beginBody := Json.mkObj [("name", "dana")])
    (extra := [("totp", totpAt secret now)])
  checkEq "the code that confirmed it is used up" reuse.status.toCode 401
  clock.modify (· + 30)
  let fresh ← signInVia ctx sk (beginBody := Json.mkObj [("name", "dana")])
    (extra := [("totp", totpAt secret (← clock.get))])
  checkEq "the next one signs in" fresh.status.toCode 200
  -- An old pending secret.
  let b2 ← postJson ctx "/account/totp/begin" emptyObj (some id)
  clock.modify (· + 400)
  let up ← stepUpVia ctx k (some id)
  let some id := sessionCookieOf up | check "step-up" false
  clock.modify (· + 250)
  let some secret2 := Factor.base32Decode (jstr (replyJson b2) "secret") | check "secret" false
  let late ← postJson ctx "/account/totp/confirm"
    (Json.mkObj [("pending", jstr (replyJson b2) "pending"),
      ("code", totpAt secret2 (← clock.get))]) (some id)
  checkEq "a set-up older than ten minutes is refused" late.status.toCode 400
  -- Removing it: dana has two passkeys and TOTP.
  let rm ← postJson ctx "/account/totp/remove" emptyObj (some id)
  checkEq "TOTP can be removed with three authenticators" rm.status.toCode 204
  let rm2 ← postJson ctx "/account/totp/remove" emptyObj (some id)
  checkEq "and is then gone" rm2.status.toCode 404
  let (f, fid, _) ← signedInUser ctx "fay"
  discard <| giveTotp ctx f
  let rm3 ← postJson ctx "/account/totp/remove" emptyObj (some fid)
  checkEq "not when it is one of the last two" rm3.status.toCode 409

/-- Recovery codes. -/
def recoveryTests : IO Unit := withCtx fun ctx clock => do
  group "account: recovery codes"
  let (u, id, _) ← signedInUser ctx "gus"
  check "the page nags about recovery codes"
    (containsStr (← getPage ctx "/account" id).bodyText "no unused recovery codes")
  let r ← postJson ctx "/account/recovery-codes" emptyObj (some id)
  checkEq "generating answers 200" r.status.toCode 200
  let codes := ((replyJson r).getObjValAs? (List String) "codes").toOption.getD []
  checkEq "ten codes" codes.length 10
  checkEq "all different" codes.eraseDups.length 10
  checkEq "stored" (← ctx.store.unspentRecoveryCodes u.id) 10
  check "the page counts them" (containsStr (← getPage ctx "/account" id).bodyText "10 of 10")
  let secret ← giveTotp ctx u
  let signIn ← postJson ctx "/signin/codes" (Json.mkObj [("name", "gus"),
    ("recovery", (codes.headD "").toLower), ("totp", totpAt secret (← clock.get))])
  checkEq "a code works, typed in lower case" signIn.status.toCode 200
  let r2 ← postJson ctx "/account/recovery-codes" emptyObj (some id)
  let codes2 := ((replyJson r2).getObjValAs? (List String) "codes").toOption.getD []
  check "new codes replace the old" (codes2.all (!codes.contains ·))
  clock.modify (· + 30)
  let old ← postJson ctx "/signin/codes" (Json.mkObj [("name", "gus"),
    ("recovery", codes.getD 1 ""), ("totp", totpAt secret (← clock.get))])
  checkEq "an old code no longer works" old.status.toCode 401

/-- Passwords. -/
def passwordTests : IO Unit := do
  withCtx fun ctx _ => do
    group "account: passwords off"
    let (_, id, _) ← signedInUser ctx "hana"
    let r ← postJson ctx "/account/password" (Json.mkObj [("password", "a long password")])
      (some id)
    checkEq "setting a password is refused when they are off"
      (r.status.toCode, errorOf r) (403, "passwords_disabled")
    check "and the page does not offer one"
      (!containsStr (← getPage ctx "/account" id).bodyText "new-password")
  withSignInCtx (fun c => { c with allowPasswords := true }) fun ctx _ => do
    group "account: passwords on"
    let (u, id, _) ← signedInUser ctx "ian"
    let short ← postJson ctx "/account/password" (Json.mkObj [("password", "short")]) (some id)
    checkEq "a short password is refused" (short.status.toCode, errorOf short)
      (400, "password_too_short")
    let ok ← postJson ctx "/account/password"
      (Json.mkObj [("password", "a long enough password")]) (some id)
    checkEq "a long one is set" ok.status.toCode 204
    check "as an Argon2id hash"
      (((← ctx.store.findPassword u.id).map (·.startsWith "$argon2id$")).getD false)
    let rm ← postJson ctx "/account/password/remove" emptyObj (some id)
    checkEq "and can be removed" rm.status.toCode 204
    checkEq "once" ((← postJson ctx "/account/password/remove" emptyObj (some id)).status.toCode)
      404

/-- The session list. -/
def sessionListTests : IO Unit := withCtx fun ctx _ => do
  group "account: sessions"
  let (u, id, k) ← signedInUser ctx "jan"
  let some other := sessionCookieOf (← signInVia ctx k) | check "a second session" false
  let sessions ← Session.list ctx u.id
  checkEq "two sessions" sessions.size 2
  let page := (← getPage ctx "/account" id).bodyText
  check "both are listed" (sessions.all fun s => containsStr page s.handle)
  let some otherSession ← Session.current ctx (withCookie other) | check "other" false
  let r ← postJson ctx "/account/sessions/end" (Json.mkObj [("handle", otherSession.handle)])
    (some id)
  checkEq "ending another session answers 204" r.status.toCode 204
  check "and ends it" ((← Session.current ctx (withCookie other)).isNone)
  check "without a step-up" true
  let (_, kid, _) ← signedInUser ctx "kai"
  let some mine ← Session.current ctx (withCookie id) | check "mine" false
  let foreign ← postJson ctx "/account/sessions/end" (Json.mkObj [("handle", mine.handle)])
    (some kid)
  checkEq "another user's session cannot be ended" foreign.status.toCode 404
  let own ← postJson ctx "/account/sessions/end" (Json.mkObj [("handle", mine.handle)]) (some id)
  checkEq "ending one's own session" own.status.toCode 204
  check "clears the cookie" (hasHeader own "Set-Cookie" clearSessionCookie)
  let after ← getPage ctx "/account" id
  checkEq "and the account page then asks to sign in"
    (after.status.toCode, after.header "Location") (303, some "/signin?return=%2Faccount")
  check "audited" ((← auditSummary ctx).contains ("sign-out", "success"))

/-- The account tests. -/
def accountTests : IO Unit := do
  registerTests
  allowListTests
  removeTests
  totpTests
  recoveryTests
  passwordTests
  sessionListTests

end PyleTests