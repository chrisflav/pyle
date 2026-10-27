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

/-- Register a soft key of a kind from the add page; the finish reply. -/
def addKind (ctx : Ctx) (cookie : String) (k : SoftKey) (kind : String) : IO Reply := do
  let b ← postJson ctx "/account/authenticators/register/begin"
    (Json.mkObj [("kind", Json.str kind)]) (some cookie)
  if b.status.toCode != 200 then return b
  let cred ← k.create (replyJson b)
  postJson ctx "/account/authenticators/register/finish"
    (Json.mkObj [("credential", cred), ("kind", Json.str kind)]) (some cookie)

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

/-- A reply's integer member. -/
def jint (j : Json) (k : String) : Int := (j.getObjValAs? Int k).toOption.getD (-1)

/-- Confirm an app set up with `begin`'s reply `b`, with a code from it at
`t`; the reply and the secret. -/
def confirmApp (ctx : Ctx) (cookie : String) (b : Reply) (t : Nat)
    (extra : List (String × Json) := []) : IO (Reply × ByteArray) := do
  let body := replyJson b
  let secret := (Factor.base32Decode (jstr body "secret")).getD .empty
  let r ← postJson ctx "/account/totp/confirm"
    (Json.mkObj ([("pending", Json.str (jstr body "pending")),
      ("code", Json.str (totpAt secret t))] ++ extra)) (some cookie)
  return (r, secret)

/-- Setting up authenticator apps, renaming and removing them. -/
def totpTests : IO Unit := withCtx fun ctx clock => do
  group "account: authenticator apps"
  let (u, id, k) ← signedInUser ctx "dana"
  let b ← postJson ctx "/account/totp/begin" (Json.mkObj [("name", "phone")]) (some id)
  checkEq "begin answers 200" b.status.toCode 200
  let body := replyJson b
  let some secret := Factor.base32Decode (jstr body "secret") | check "a base32 secret" false
  checkEq "of 20 bytes" secret.size 20
  check "and an otpauth URI"
    ((jstr body "uri").startsWith "otpauth://totp/auth.example.org:dana?secret=")
  check "and its QR code, as a data URL of SVG"
    (jstr body "qr" == Account.totpQr (jstr body "uri") &&
      (jstr body "qr").startsWith "data:image/svg+xml;base64,")
  checkEq "and the name it will have" (jstr body "name") "phone"
  checkEq "and the reply, carrying the secret, is not cached" (b.header "cache-control")
    (some "no-store")
  check "nothing is stored yet" ((← ctx.store.listTotpApps u.id).isEmpty)
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
  let (ok, _) ← confirmApp ctx id b now
  checkEq "the right code stores it" ok.status.toCode 201
  let apps ← ctx.store.listTotpApps u.id
  checkEq "as one app, named as begin was told" (apps.toList.map (·.name)) ["phone"]
  let some a := apps[0]? | check "the app" false
  checkEq "the reply gives its id and name" (jint (replyJson ok) "id", jstr (replyJson ok) "name")
    (a.id, "phone")
  check "sealed for its row, not in the clear"
    ((SignIn.Secrets.openTotpApp ctx.rootKey u.id a.id a.sealedSecret).toOption == some secret &&
      a.sealedSecret != secret)
  check "and not openable as another of the user's apps"
    ((SignIn.Secrets.openTotpApp ctx.rootKey u.id (a.id + 1) a.sealedSecret).toOption.isNone)
  checkEq "the confirming code is its last step, but not a use"
    (a.lastStep.isSome, a.lastUsed) (true, none)
  checkEq "two authenticators now" (← ctx.store.authenticatorCount u.id) 2
  let audit ← Audit.entries ctx.store
  check "the audit log names the app"
    (audit.any fun e => e.event == "register" && e.factor == some s!"totp:{a.id}" &&
      containsStr e.detail "'phone'")
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
  -- A second app, named at confirm.
  let some id := sessionCookieOf (← stepUpVia ctx k (some id)) | check "step-up" false
  let b2 ← postJson ctx "/account/totp/begin" emptyObj (some id)
  checkEq "a second app gets a numbered default name" (jstr (replyJson b2) "name")
    "Authenticator app 2"
  let (ok2, secret2) ← confirmApp ctx id b2 (← clock.get) [("name", "tablet")]
  checkEq "and is stored beside the first" ok2.status.toCode 201
  checkEq "under the name confirm gave" ((← ctx.store.listTotpApps u.id).toList.map (·.name))
    ["phone", "tablet"]
  check "with its own secret" (secret2 != secret)
  checkEq "every app counts" (← ctx.store.authenticatorCount u.id) 4
  let a2 := jint (replyJson ok2) "id"
  -- Renaming, by id.
  let rn ← postJson ctx "/account/totp/rename"
    (Json.mkObj [("id", toJson a.id), ("name", "old phone")]) (some id)
  checkEq "renaming answers 204" rn.status.toCode 204
  checkEq "and renames that app" ((← ctx.store.findTotpApp u.id a.id).map (·.name))
    (some "old phone")
  let rnStr ← postJson ctx "/account/totp/rename"
    (Json.mkObj [("id", Json.str (toString a2)), ("name", "my tablet")]) (some id)
  checkEq "an id may come as a string" rnStr.status.toCode 204
  let empty ← postJson ctx "/account/totp/rename"
    (Json.mkObj [("id", toJson a.id), ("name", " ")]) (some id)
  checkEq "an empty name is refused" empty.status.toCode 400
  let (fay, _, fk) ← signedInUser ctx "fay"
  let (fayApp, _) ← giveTotpApp ctx fay
  let foreign ← postJson ctx "/account/totp/rename"
    (Json.mkObj [("id", toJson fayApp.id), ("name", "mine")]) (some id)
  checkEq "another user's app cannot be renamed" foreign.status.toCode 404
  -- An old pending secret.
  let b3 ← postJson ctx "/account/totp/begin" emptyObj (some id)
  clock.modify (· + 400)
  let some id := sessionCookieOf (← stepUpVia ctx k (some id)) | check "step-up" false
  clock.modify (· + 250)
  let (late, _) ← confirmApp ctx id b3 (← clock.get)
  checkEq "a set-up older than ten minutes is refused" late.status.toCode 400
  -- Removing, by id: dana has two keys and two apps.
  let noId ← postJson ctx "/account/totp/remove" emptyObj (some id)
  checkEq "removing needs an id" noId.status.toCode 400
  let foreignRm ← postJson ctx "/account/totp/remove" (Json.mkObj [("id", toJson fayApp.id)])
    (some id)
  checkEq "another user's app cannot be removed" foreignRm.status.toCode 404
  check "fay's is untouched" ((← ctx.store.findTotpApp fay.id fayApp.id).isSome)
  let rm ← postJson ctx "/account/totp/remove" (Json.mkObj [("id", toJson a.id)]) (some id)
  checkEq "an app can be removed with four authenticators" rm.status.toCode 204
  checkEq "that one, and not the other" ((← ctx.store.listTotpApps u.id).toList.map (·.name))
    ["my tablet"]
  let rm2 ← postJson ctx "/account/totp/remove" (Json.mkObj [("id", toJson a.id)]) (some id)
  checkEq "and is then gone" rm2.status.toCode 404
  let again ← signInVia ctx fk (client := "192.0.2.77")
  let some fid := sessionCookieOf again | check "fay signs in again" false again.bodyText
  let rm3 ← postJson ctx "/account/totp/remove" (Json.mkObj [("id", toJson fayApp.id)])
    (some fid)
  checkEq "not when it is one of the last two" rm3.status.toCode 409
  check "removals are audited by app"
    ((← Audit.entries ctx.store).any fun e => e.event == "remove-authenticator" &&
      e.factor == some s!"totp:{a.id}" && containsStr e.detail "'old phone'")

/-- Several apps at sign-in: a code counts for the app it came from, is good
once for it, the lock is the account's, and two apps are one factor. -/
def severalAppsTests : IO Unit := withCtx fun ctx clock => do
  group "account: several authenticator apps at sign-in"
  let ctx := { ctx with limiter := ← RateLimiter.new (policy := { freeFailures := 100 }) }
  let olga ← ctx.store.addUser "olga" [] 1
  let (appA, sa) ← giveTotpApp ctx olga "phone"
  let (appB, sb) ← giveTotpApp ctx olga "tablet"
  let (appC, _) ← giveTotpApp ctx olga "old phone"
  let sk ← SoftKey.new (uv := false)
  enrol ctx olga sk
  let withCode (code : String) (client : String := "192.0.2.1") : IO Reply :=
    signInVia ctx sk (beginBody := Json.mkObj [("name", "olga")]) (extra := [("totp", code)])
      (client := client)
  let now ← clock.get
  let rb ← withCode (totpAt sb now)
  checkEq "a code from the second app signs in" rb.status.toCode 200
  checkEq "as otp" (((replyJson rb).getObjValAs? (List String) "amr").toOption.map
    (·.contains "otp")) (some true)
  let steps ← lastSteps ctx olga.id
  checkEq "using up a step of that app only" steps [none, some (Factor.Totp.stepOf now), none]
  let rb2 ← withCode (totpAt sb now)
  checkEq "the same code again is refused" rb2.status.toCode 401
  let ra ← withCode (totpAt sa now)
  checkEq "the first app's code for the same step still signs in" ra.status.toCode 200
  let ra2 ← withCode (totpAt sa now)
  checkEq "once" ra2.status.toCode 401
  checkEq "the last use is recorded per app"
    ((← ctx.store.listTotpApps olga.id).toList.map (·.lastUsed)) [some now, some now, none]
  let some s ← Session.current ctx (withCookie ((sessionCookieOf ra).getD ""))
    | check "a session" false
  check "the session names the app it used" (s.factors.contains s!"totp:{appA.id}")
  -- Two codes from two apps are one factor.
  clock.modify (· + 30)
  let t ← clock.get
  let .ok fa ← Policy.checkTotp ctx olga.id (totpAt sa t) | check "app A's code" false
  let .ok fb ← Policy.checkTotp ctx olga.id (totpAt sb t) | check "app B's code" false
  check "both codes check out, each for its own app"
    (fa.label == s!"totp:{appA.id}" && fb.label == s!"totp:{appB.id}")
  check "but two codes from two apps are no authentication"
    (Policy.Authentication.ofFactors [fa, fb]).isNone
  check "not mfa in either order" (Policy.Authentication.ofFactors [fb, fa]).isNone
  -- The lock is the account's: one wrong code is one failure, however many
  -- apps it was checked against.
  let codes := [totpAt sa t, totpAt sb t, totpAt sa (t + 30), totpAt sb (t + 30),
    totpAt sa (t - 30), totpAt sb (t - 30)]
  let wrong := (["000000", "111111", "222222", "333333", "444444", "555555", "666666"].find?
    (!codes.contains ·)).getD "777777"
  let r1 ← withCode wrong
  checkEq "a wrong code is refused" r1.status.toCode 401
  checkEq "and counts once, not once per app" (← ctx.store.totpLock olga.id).failures 1
  for i in [0:4] do
    discard <| withCode wrong (client := s!"203.0.113.{i}")
  check "five wrong codes lock TOTP for the account"
    ((← ctx.store.totpLock olga.id).lockedUntil ≥ t + 900)
  clock.modify (· + 30)
  let t2 ← clock.get
  let la ← withCode (totpAt sa t2)
  let lb ← withCode (totpAt sb t2)
  checkEq "then a right code from any app is refused" (la.status.toCode, lb.status.toCode)
    (401, 401)
  check "and uses up no step"
    ((← lastSteps ctx olga.id).all (·.all (· < Factor.Totp.stepOf t2)))
  -- Counting: olga has a key and three apps.
  checkEq "a key and three apps are four authenticators" (← ctx.store.authenticatorCount olga.id) 4
  check "two apps may go" ((← ctx.store.removeTotpApp olga.id appC.id) &&
    (← ctx.store.removeTotpApp olga.id appB.id))
  check "the last two may not" (!(← ctx.store.removeTotpApp olga.id appA.id) &&
    !(← ctx.store.removeCredential olga.id sk.id))
  check "capabilities see the app" (← Policy.capabilities ctx olga.id).totp

/-- Migration 6 turns an account's one TOTP secret into its first app. -/
def totpMigrationTests : IO Unit := IO.FS.withTempDir fun dir => do
  group "account: migration 6"
  let s ← Store.Store.openFile (dir / "old.db")
  let rootKey ← Crypto.randomBytes 32
  let secret ← Factor.Totp.generateSecret
  let other ← Factor.Totp.generateSecret
  let created := 1700000000
  let step := Factor.Totp.stepOf created
  let usedStep := step + 100
  s.run fun c => do
    discard <| Store.currentVersion c
    for m in Store.migrations.take 5 do
      for st in m.statements do discard <| Store.exec c st
      discard <| Store.exec c
        "INSERT INTO schema_version (version, description, applied) VALUES (?, ?, ?)"
        #[m.version, m.description, (1 : Nat)]
    for (n, h) in [("ann", 1), ("ben", 2), ("cy", 3)] do
      discard <| Store.exec c "INSERT INTO users (handle, name, created) VALUES (?, ?, 1)"
        #[.blob (ByteArray.mk #[UInt8.ofNat h]), .text n]
  let sealed ← Crypto.«seal» (SignIn.Secrets.totpKey rootKey)
    (SignIn.Secrets.userAd ⟨1⟩) secret
  let sealedBen ← Crypto.«seal» (SignIn.Secrets.totpKey rootKey)
    (SignIn.Secrets.userAd ⟨2⟩) other
  s.run fun c => do
    discard <| Store.exec c
      "INSERT INTO totp (user_id, secret, last_step, failures, locked_until, created) \
        VALUES (1, ?, ?, 3, 0, ?)" #[sealed, usedStep, created]
    discard <| Store.exec c
      "INSERT INTO totp (user_id, secret, last_step, failures, locked_until, created) \
        VALUES (2, ?, ?, 0, ?, ?)" #[sealedBen, step, (created + 5000 : Nat), created]
  checkEq "the database is at version 5" (← s.version) 5
  s.migrate 2
  checkEq "and is brought to 6" (← s.version) 6
  let ann ← s.listTotpApps ⟨1⟩
  checkEq "the old secret is the account's one app" (ann.toList.map (·.name))
    ["Authenticator app"]
  let some a := ann[0]? | check "ann's app" false
  checkEq "with the user's id as its own" a.id 1
  checkEq "the same sealed secret, created time and last step"
    (a.sealedSecret == sealed, a.created, a.lastStep) (true, created, some usedStep)
  checkEq "a step long after it was stored was a use" a.lastUsed (some (usedStep * 30))
  checkEq "the failures carry over to the account" (← s.totpLock ⟨1⟩).failures 3
  check "it still opens"
    ((SignIn.Secrets.openTotpApp rootKey ⟨1⟩ a.id a.sealedSecret).toOption == some secret)
  let ben ← s.listTotpApps ⟨2⟩
  checkEq "a step the confirming code used is no use"
    (ben.toList.map fun b => (b.id, b.lastUsed)) [(2, none)]
  checkEq "and the lock carries over" (← s.totpLock ⟨2⟩).lockedUntil (created + 5000)
  check "an account without a secret has no app" ((← s.listTotpApps ⟨3⟩).isEmpty)
  checkEq "the old table is gone"
    (← s.run fun c => Store.query c
      "SELECT COUNT(*) FROM sqlite_master WHERE name = 'totp'" #[] (Store.colNat · 0)) #[0]
  -- The old associated data opens only the row migration 6 made.
  let moved ← s.addTotpApp ⟨1⟩ "copy" none 9 fun _ => pure sealed
  check "the old sealed secret moved into another of the user's apps does not open"
    ((SignIn.Secrets.openTotpApp rootKey ⟨1⟩ moved.id sealed).toOption.isNone)
  check "nor as another user's"
    ((SignIn.Secrets.openTotpApp rootKey ⟨3⟩ 3 sealed).toOption.isNone)
  check "new ids come after the migrated ones" (moved.id > 2)
  discard <| s.run fun c => Store.exec c "DELETE FROM totp_apps WHERE id = ?" #[.int moved.id]
  -- And it signs in.
  let clock ← IO.mkRef (usedStep * 30 + 60)
  let ctx : Ctx := { config := testConfig dir, store := s, limiter := ← RateLimiter.new,
                     rootKey, clock := clock.get }
  match ← Policy.checkTotp ctx ⟨1⟩ (totpAt secret (← clock.get)) with
  | .ok f => checkEq "a code from the migrated app checks out" f.label "totp:1"
  | .error _ => check "a code from the migrated app checks out" false
  checkEq "and clears the failures" (← s.totpLock ⟨1⟩).failures 0

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
      (!containsStr (← getPage ctx "/account" id).bodyText "/account/add/password")
  withSignInCtx (fun c => { c with allowPasswords := true }) fun ctx _ => do
    group "account: passwords on"
    let (u, id, _) ← signedInUser ctx "ian"
    let pwPage ← getPage ctx "/account/add/password" id
    checkEq "the password page answers 200" pwPage.status.toCode 200
    check "with the field" (containsStr pwPage.bodyText "id=\"new-password\"")
    let before := (← getPage ctx "/account" id).bodyText
    check "the account page lists the password as not set"
      (containsStr before ">Password</th>" && containsStr before "Not set")
    let short ← postJson ctx "/account/password" (Json.mkObj [("password", "short")]) (some id)
    checkEq "a short password is refused" (short.status.toCode, errorOf short)
      (400, "password_too_short")
    let ok ← postJson ctx "/account/password"
      (Json.mkObj [("password", "a long enough password")]) (some id)
    checkEq "a long one is set" ok.status.toCode 204
    check "as an Argon2id hash"
      (((← ctx.store.findPassword u.id).map (·.startsWith "$argon2id$")).getD false)
    let after := (← getPage ctx "/account" id).bodyText
    check "then as only together with another method, to change or remove"
      (containsStr after "Only together with another method" &&
        containsStr after "data-action=\"password-remove\"" && containsStr after ">Change</a>")
    check "and the password page offers to change it"
      (containsStr (← getPage ctx "/account/add/password" id).bodyText "Change your password")
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
  let some mine ← Session.current ctx (withCookie id) | check "mine" false
  check "both are listed, the other with a button to sign out there"
    ((page.splitOn "<li>").length == 3 &&
      sessions.all fun s => s.handle == mine.handle || containsStr page s!"data-handle=\"{s.handle}\"")
  check "and this one marked" (containsStr page "this browser")
  let some otherSession ← Session.current ctx (withCookie other) | check "other" false
  let r ← postJson ctx "/account/sessions/end" (Json.mkObj [("handle", otherSession.handle)])
    (some id)
  checkEq "ending another session answers 204" r.status.toCode 204
  check "and ends it" ((← Session.current ctx (withCookie other)).isNone)
  check "without a step-up" true
  let (_, kid, _) ← signedInUser ctx "kai"
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

/-- The value of the first `attr="…"` in some HTML. -/
def attrValue (html attr : String) : String :=
  (((html.splitOn s!"{attr}=\"").getD 1 "").splitOn "\"").headD ""

/-- The text of the first element with id `id`, up to the next tag. -/
def elementText (html id : String) : String :=
  (((((html.splitOn s!"id=\"{id}\"").getD 1 "").splitOn ">").getD 1 "").splitOn "<").headD ""

/-- The account page and the pages for adding a way to sign in. -/
def addPageTests : IO Unit := withCtx fun ctx clock => do
  group "account: the pages"
  let (u, id, _) ← signedInUser ctx "pia"
  for path in ["/account", "/account/add", "/account/add/app", "/account/add/recovery-codes"] do
    let r ← getPage ctx path (some id)
    checkEq s!"{path} answers 200 with a session" r.status.toCode 200
    let anon ← getPage ctx path
    checkEq s!"and without one sends to sign in and back"
      (anon.status.toCode, anon.header "Location") (303, some (Web.signInUrl path))
  let pw ← getPage ctx "/account/add/password" (some id)
  checkEq "the password page is 404 when passwords are off" pw.status.toCode 404
  -- The choices.
  let add := (← getPage ctx "/account/add" id).bodyText
  check "the add page offers a passkey, recommended, registered from the page"
    (containsStr add "class=\"choice recommended\" id=\"add-passkey\" data-kind=\"passkey\"" &&
      containsStr add "Recommended")
  check "a security key, likewise"
    (containsStr add "id=\"add-security-key\" data-kind=\"security-key\"")
  check "an authenticator app and recovery codes, on pages of their own"
    (containsStr add "href=\"/account/add/app\"" &&
      containsStr add "href=\"/account/add/recovery-codes\"")
  check "and no password when they are off" (!containsStr add "/account/add/password")
  check "and leads back" (containsStr add "<a class=\"back\" href=\"/account\">")
  -- What each kind asks the authenticator for.
  let selection (kind : String) : IO (String × String) := do
    let r ← postJson ctx "/account/authenticators/register/begin"
      (Json.mkObj [("kind", Json.str kind)]) (some id)
    let sel := ((replyJson r).getObjVal? "authenticatorSelection").toOption.getD .null
    return (jstr sel "residentKey", jstr sel "userVerification")
  checkEq "a passkey: discoverable and verifying" (← selection "passkey") ("required", "required")
  checkEq "a security key: neither required" (← selection "security-key")
    ("discouraged", "preferred")
  let weak ← SoftKey.new (uv := false)
  let refused ← addKind ctx id weak "passkey"
  checkEq "a passkey that did not verify the user is refused" refused.status.toCode 400
  let synced ← SoftKey.new (backupEligible := true)
  checkEq "a passkey registers" (← addKind ctx id synced "passkey").status.toCode 201
  checkEq "the touch-only key registers as a security key"
    (← addKind ctx id weak "security-key").status.toCode 201
  let names := (← ctx.store.listCredentials u.id).toList.map (·.name)
  check "named by kind"
    (names.length == 3 && ["test key", "Passkey 2", "Security key 3"].all names.contains)
  -- The account page.
  discard <| giveTotp ctx u "phone"
  let page := (← getPage ctx "/account" id).bodyText
  check "it sums up the protection" (containsStr page "Account protection: ")
  check "one table" ((page.splitOn "<table").length == 2 &&
    containsStr page "<div class=\"table-scroll\"")
  check "grouped by kind, a tbody each with a colgroup header"
    ((page.splitOn "<tbody>").length == 4 &&
      ["Passkeys and security keys", "Authenticator apps", "Recovery codes"].all fun g =>
        containsStr page s!"<th colspan=\"4\" scope=\"colgroup\">{g}")
  check "no password group when passwords are off" (!containsStr page ">Password</th>")
  check "the passkeys say how they keep their key"
    (containsStr page "Synced passkey" && containsStr page "Stays on the key" &&
      !containsStr page "device-bound")
  check "the app is listed by name" (containsStr page "<strong>phone</strong>")
  check "one button adds" (containsStr page "id=\"add-method\" href=\"/account/add\">\
    Add a sign-in method</a>")
  check "the five-minute note stays" (containsStr page "more than 5 minutes ago")
  check "and no set-up form is left on it"
    (["totp-begin", "totp-setup", "new-name", "recovery-generate", "new-password"].all
      (!containsStr page ·))
  check "the sessions come after the table"
    (((page.splitOn "Where you're signed in").headD "").length >
      ((page.splitOn "<table").headD "").length)
  -- Added messages.
  checkEq "an added app is announced"
    (elementText (← getPage ctx "/account?added=app" id).bodyText "added")
    "Your authenticator app was added."
  check "an unknown one is not, nor echoed"
    (!containsStr (← getPage ctx "/account?added=%3Cb%3E" id).bodyText "id=\"added\"")
  -- The app page.
  let appPage := (← getPage ctx "/account/add/app" id).bodyText
  let pending := attrValue appPage "data-pending"
  check "the app page carries a sealed pending secret" (!pending.isEmpty)
  check "its QR code, as a data URL"
    (containsStr appPage "<img id=\"totp-qr\" class=\"qr\" \
      alt=\"QR code for your authenticator app\" src=\"data:image/svg+xml;base64,")
  check "the link to open it in an app, labelled in the page"
    ((attrValue ((appPage.splitOn "id=\"totp-uri\"").getD 1 "") "href").startsWith
      "otpauth://totp/auth.example.org:pia?secret=" &&
      containsStr appPage ">On your phone? Open in your authenticator app</a>")
  check "the name, the QR code, the link, the key and the code, in that order"
    (let pos (s : String) : Nat := ((appPage.splitOn s).headD appPage).length
     pos "id=\"app-name\"" < pos "id=\"totp-qr\"" && pos "id=\"totp-qr\"" < pos "id=\"totp-uri\"" &&
       pos "id=\"totp-uri\"" < pos "id=\"totp-secret\"" &&
       pos "id=\"totp-secret\"" < pos "id=\"totp-code\"" &&
       pos "id=\"totp-code\"" < appPage.length)
  check "a second app is named so by default"
    (attrValue ((appPage.splitOn "id=\"app-name\"").getD 1 "") "value" == "Authenticator app 2" &&
      containsStr appPage "You already have 1 authenticator app.")
  let key := elementText appPage "totp-secret"
  check "the key is in groups of four" ((key.splitOn " ").all (·.length ≤ 4))
  let some secret := Factor.base32Decode (String.ofList (key.toList.filter (· != ' ')))
    | check "the key decodes" false
  let r ← postJson ctx "/account/totp/confirm" (Json.mkObj [("pending", Json.str pending),
    ("code", Json.str (totpAt secret (← clock.get))), ("name", "work phone")]) (some id)
  checkEq "and its code adds the app" r.status.toCode 201
  checkEq "beside the first" ((← ctx.store.listTotpApps u.id).toList.map (·.name))
    ["phone", "work phone"]
  clock.modify (· + SignIn.stepUpSeconds + 1)
  let late ← getPage ctx "/account/add/app" id
  checkEq "after five minutes the app page asks to confirm it is you first"
    (late.status.toCode, late.header "Location")
    (303, some "/signin?return=%2Faccount%2Fadd%2Fapp&max_age=300")
  checkEq "the other add pages do not" (← getPage ctx "/account/add" id).status.toCode 200
  -- The recovery-codes page asks before replacing.
  let rec0 := (← getPage ctx "/account/add/recovery-codes" id).bodyText
  check "with no codes, nothing to replace" (containsStr rec0 "data-replace=\"false\"")
  discard <| ctx.store.setRecoveryCodes u.id ["a".toUTF8]
  let rec1 := (← getPage ctx "/account/add/recovery-codes" id).bodyText
  check "with codes, it asks first" (containsStr rec1 "data-replace=\"true\"" &&
    containsStr rec1 "New codes replace them")

/-- The account tests. -/
def accountTests : IO Unit := do
  registerTests
  allowListTests
  removeTests
  totpTests
  severalAppsTests
  totpMigrationTests
  recoveryTests
  passwordTests
  sessionListTests
  addPageTests

end PyleTests