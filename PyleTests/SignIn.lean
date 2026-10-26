import PyleTests.Http
import PyleTests.WebAuthn

/-!
# Signing in

The sign-in endpoints driven through `Server.route`, with no socket and no
browser.  `SoftKey` stands in for both: it makes the client data a browser
would and the authenticator data and signature an authenticator would, with
`lean-biscuit`'s signers (in tests only, DESIGN §6.2).

The negative cases are the point: a TOTP code alone and a recovery code alone
get no session, and a password alone and a security key without user
verification alone get one only at `sfa`, and none when more is asked for;
each level is reached by the factors that justify it and by no others; a
replayed challenge, a wrong origin, a counter that went
backwards and an open-redirect `return` are refused; five wrong TOTP codes
lock TOTP; and the rate limiter answers `429`.

**The test-only way to a session.**  `sessionFor ctx user` registers a fresh
software passkey for `user` and signs in with it through the real endpoints,
returning the cookie.  Other suites that need a signed-in user use it: there
is no shortcut that writes a session row, because there is none in pyle.
-/

namespace PyleTests

open Pyle Pyle.Http Pyle.WebAuthn Pyle.Encoding LeanBiscuit
open Lean (Json toJson)

/-! ## A browser and an authenticator -/

/-- The origin the test pages run on. -/
def testOrigin : String := "https://auth.example.org"

/-- A software authenticator holding one credential. -/
structure SoftKey where
  /-- The signature algorithm. -/
  alg : CoseAlgorithm
  /-- The private key. -/
  secret : ByteArray
  /-- The credential id. -/
  id : ByteArray
  /-- The user handle it was registered with. -/
  handle : IO.Ref ByteArray
  /-- The signature counter. -/
  counter : IO.Ref Nat
  /-- Whether it verifies the user (a PIN or a fingerprint). -/
  uv : Bool
  /-- Whether its key may be synced. -/
  backupEligible : Bool

/-- A new software authenticator with a random key and credential id. -/
def SoftKey.new (alg : CoseAlgorithm := .es256) (uv : Bool := true)
    (backupEligible : Bool := false) : IO SoftKey := do
  let mut secret ← Crypto.randomBytes 32
  -- A P-256 scalar must be below the group order; retry the rare one that is not.
  while alg == .es256 && (P256.publicKeyOfSecret secret).isNone do
    secret ← Crypto.randomBytes 32
  return { alg, secret, id := ← Crypto.randomBytes 16, handle := ← IO.mkRef .empty,
           counter := ← IO.mkRef 0, uv, backupEligible }

/-- The public key, as the store keeps it. -/
def SoftKey.publicKey (k : SoftKey) : ByteArray :=
  match k.alg with
  | .es256 => (P256.publicKeyOfSecret k.secret).getD .empty
  | .edDsa => (Ed25519.publicKeyOfSecret k.secret).getD .empty

/-- The public key, as a COSE key. -/
def SoftKey.cose (k : SoftKey) : Cbor :=
  match k.alg with
  | .es256 => let (x, y) := p256Coordinates k.secret; coseEs256 x y
  | .edDsa => coseEdDsa k.publicKey

/-- Sign with the key. -/
def SoftKey.sign (k : SoftKey) (m : ByteArray) : ByteArray :=
  match k.alg with
  | .es256 => (P256.sign k.secret m).getD .empty
  | .edDsa => (Ed25519.sign k.secret m).getD .empty

/-- The flags byte: present always, verified if `uv`, backup-eligible and
backed up if the key may be synced, and the attested-credential flag. -/
def SoftKey.flags (k : SoftKey) (uv attested : Bool) : UInt8 :=
  0x01 ||| (if uv then 0x04 else 0) ||| (if k.backupEligible then 0x18 else 0) |||
    (if attested then 0x40 else 0)

/-- base64url. -/
def b64u (b : ByteArray) : String := Base64Url.encode b

/-- Client data as a browser serialises it. -/
def browserClientData (type challenge : String) (origin : String := testOrigin) : ByteArray :=
  (s!"\{\"type\":\"{type}\",\"challenge\":\"{challenge}\",\"origin\":\"{origin}\"," ++
    "\"crossOrigin\":false}").toUTF8

/-- A string member of a JSON object, or empty. -/
def jstr (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

/-- What `navigator.credentials.get` hands back for these options, as the
page posts it.  The challenge can be overridden, to replay an old one. -/
def SoftKey.assert (k : SoftKey) (opts : Json) (origin : String := testOrigin)
    (uv : Bool := k.uv) (withHandle : Bool := true) (challenge : Option String := none)
    (rpId : String := "auth.example.org") : IO Json := do
  let n ← k.counter.modifyGet fun n => (n + 1, n + 1)
  let ad := Sha256.hash rpId.toUTF8 ++ ByteArray.mk #[k.flags uv false] ++ Bytes.ofNatBE 4 n
  let cd := browserClientData "webauthn.get" (challenge.getD (jstr opts "challenge")) origin
  let h ← k.handle.get
  return Json.mkObj [("id", b64u k.id), ("clientDataJSON", b64u cd),
    ("authenticatorData", b64u ad), ("signature", b64u (k.sign (ad ++ Sha256.hash cd))),
    ("userHandle", if withHandle then Json.str (b64u h) else Json.null)]

/-- What `navigator.credentials.create` hands back for these options:
attestation `none`, or `packed` self-attestation. -/
def SoftKey.create (k : SoftKey) (opts : Json) (fmt : String := "none") (uv : Bool := k.uv)
    (origin : String := testOrigin) : IO Json := do
  let user := (opts.getObjVal? "user").toOption.getD .null
  k.handle.set ((Base64Url.decode (jstr user "id")).getD .empty)
  let ad := Sha256.hash "auth.example.org".toUTF8 ++ ByteArray.mk #[k.flags uv true] ++
    Bytes.ofNatBE 4 0 ++ ByteArray.mk (Array.replicate 16 0) ++ Bytes.ofNatBE 2 k.id.size ++
    k.id ++ Cbor.encode k.cose
  let cd := browserClientData "webauthn.create" (jstr opts "challenge") origin
  let alg : Cbor := match k.alg with
    | .es256 => .negative 6
    | .edDsa => .negative 7
  let attStmt : Cbor := if fmt == "packed" then
      .map [(.text "alg", alg), (.text "sig", .bytes (k.sign (ad ++ Sha256.hash cd)))]
    else .map []
  let ao := Cbor.encode (.map [(.text "fmt", .text fmt), (.text "attStmt", attStmt),
    (.text "authData", .bytes ad)])
  return Json.mkObj [("id", b64u k.id), ("clientDataJSON", b64u cd),
    ("attestationObject", b64u ao), ("transports", toJson ["internal"])]

/-- Register a soft key for a user straight into the store: test set-up, not
a ceremony. -/
def enrol (ctx : Ctx) (user : Store.User) (k : SoftKey) (name : String := "test key") :
    IO Unit := do
  k.handle.set user.handle
  ctx.store.addCredential
    { id := k.id, user := user.id, algorithm := k.alg.toInt, publicKey := k.publicKey,
      signCount := 0, backupEligible := k.backupEligible, backupState := k.backupEligible,
      aaguid := ByteArray.mk (Array.replicate 16 0), transports := [], name,
      created := ← ctx.clock, lastUsed := none, userVerified := k.uv }

/-! ## Requests -/

/-- A context over a fresh database, with the configuration adjusted. -/
def withSignInCtx (modify : Config → Config) (f : Ctx → IO.Ref Nat → IO α) : IO α :=
  IO.FS.withTempDir fun dir => do
    let clock ← IO.mkRef 1700000000
    let config := modify (testConfig dir)
    let store ← Store.Store.openAt config.database 1700000000
    let ctx : Ctx :=
      { config, store, limiter := ← RateLimiter.new, rootKey := ← Crypto.randomBytes 32,
        clock := clock.get }
    f ctx clock

/-- The `Cookie` header for a session, if any. -/
def cookieHeader : Option String → List (String × String)
  | some id => [("Cookie", s!"{sessionCookieName}={id}")]
  | none => []

/-- Post JSON from the test origin, with a session cookie if given. -/
def postJson (ctx : Ctx) (path : String) (body : Json) (cookie : Option String := none)
    (client : String := "198.51.100.7") (origin : String := testOrigin) : IO Reply :=
  Server.route ctx (Req.mk' .post path
    ([("Origin", origin), ("Content-Type", "application/json")] ++ cookieHeader cookie)
    body.compress.toUTF8 client)

/-- `GET` a page, with a session cookie if given. -/
def getPage (ctx : Ctx) (path : String) (cookie : Option String := none) : IO Reply :=
  Server.route ctx (Req.mk' .get path (cookieHeader cookie))

/-- A reply's body as JSON. -/
def replyJson (r : Reply) : Json := (Json.parse r.bodyText).toOption.getD .null

/-- A reply's `error`. -/
def errorOf (r : Reply) : String := jstr (replyJson r) "error"

/-- The session cookie a reply sets, if any. -/
def sessionCookieOf (r : Reply) : Option String :=
  r.headers.findSome? fun (k, v) =>
    if k.toLower == "set-cookie" && v.startsWith (sessionCookieName ++ "=") then
      let val := ((v.drop (sessionCookieName.length + 1)).toString.splitOn ";").headD ""
      if val.isEmpty then none else some val
    else none

/-- A request carrying a session cookie. -/
def withCookie (id : String) (method : Std.Http.Method := .get) (path : String := "/")
    (headers : List (String × String) := []) : Req :=
  Req.mk' method path ((("Cookie", s!"{sessionCookieName}={id}")) :: headers)

/-- The empty JSON object. -/
def emptyObj : Json := Json.mkObj []

/-- Sign in through the endpoints: begin (with `beginBody`), assert with the
key, finish with `extra` members.  The finish reply. -/
def signInVia (ctx : Ctx) (k : SoftKey) (cookie : Option String := none)
    (beginBody : Json := emptyObj) (extra : List (String × Json) := [])
    (client : String := "198.51.100.7") (uv : Bool := k.uv) : IO Reply := do
  let b ← postJson ctx "/signin/webauthn/begin" beginBody cookie client
  let cred ← k.assert (replyJson b) (uv := uv)
  postJson ctx "/signin/webauthn/finish" (Json.mkObj ([("credential", cred)] ++ extra)) cookie
    client

/-- Step up through the endpoints. -/
def stepUpVia (ctx : Ctx) (k : SoftKey) (cookie : Option String)
    (extra : List (String × Json) := []) (beginBody : Json := emptyObj) : IO Reply := do
  let b ← postJson ctx "/signin/stepup/begin" beginBody cookie
  let cred ← k.assert (replyJson b)
  postJson ctx "/signin/stepup/finish" (Json.mkObj ([("credential", cred)] ++ extra)) cookie

/-- **The test-only path to a session**: register a fresh software passkey for
`user` and sign in with it through the real endpoints.  The cookie, and the
key for later step-ups. -/
def sessionFor (ctx : Ctx) (user : Store.User) : IO (String × SoftKey) := do
  let k ← SoftKey.new
  enrol ctx user k
  -- A limiter of its own, so that set-up is not held up by the failures a
  -- test provokes on purpose.
  let r ← signInVia { ctx with limiter := ← RateLimiter.new } k
  let some id := sessionCookieOf r
    | throw (.userError s!"sessionFor: the sign-in failed: {r.bodyText}")
  return (id, k)

/-- An `Authentication` for a soft key alone, through `Policy.checkAssertion`
and a challenge issued the way the endpoints issue one. -/
def authFor (ctx : Ctx) (k : SoftKey) : IO Policy.Authentication := do
  let ch ← match ← SignIn.newChallenge ctx (Req.mk' .post "/") .authenticate none with
    | .ok ch => pure ch
    | .error _ => throw (.userError "authFor: no challenge")
  let cred ← k.assert (SignIn.requestOptions ctx ch [] "required")
  let resp ← IO.ofExcept (SignIn.parseAssertion cred)
  match ← Policy.checkAssertion ctx .authenticate resp with
  | .error e => throw (.userError s!"authFor: {e.reason}")
  | .ok ca =>
    match Policy.Authentication.ofFactors [ca.factor] with
    | some sa => return sa
    | none => throw (.userError "authFor: no authentication")

/-- Give a user a TOTP secret straight in the store; the secret. -/
def giveTotp (ctx : Ctx) (u : Store.User) : IO ByteArray := do
  let secret ← Factor.Totp.generateSecret
  ctx.store.setTotp u.id (← SignIn.Secrets.sealTotp ctx.rootKey u.id secret) (← ctx.clock)
  return secret

/-- The TOTP code for a secret at a time. -/
def totpAt (secret : ByteArray) (t : Nat) : String :=
  Factor.Totp.code secret (Factor.Totp.stepOf t)

/-- The audit entries' events and outcomes. -/
def auditSummary (ctx : Ctx) : IO (List (String × String)) :=
  return (← Audit.entries ctx.store).toList.map fun e => (e.event, e.outcome)

/-! ## The tests -/

/-- Return addresses. -/
def returnTests : IO Unit := do
  group "signin: return addresses"
  for good in ["/", "/account", "/authorize?client_id=x&state=y", "/a/b%2Fc"] do
    checkEq s!"accepted: {good}" (SignIn.safeReturn good) (some good)
  for bad in ["", "//evil.example", "/\\evil.example", "https://evil.example/",
      "evil.example", "/a b", "/a\nb", "javascript:alert(1)", "/\\/evil", "\\\\evil",
      "/a\\b", "/" ++ String.ofList (List.replicate 2048 'a')] do
    checkEq s!"refused: {bad.quote}" (SignIn.safeReturn bad) none
  for c in ['"', '<', '~', '%', '?', '#'] do
    let t := "/a" ++ c.toString
    check s!"printable {c} is allowed after the slash" (SignIn.safeReturn t == some t)
  for c in [' ', '\t', '\\', '\x7f', 'é'] do
    let t := "/a" ++ c.toString
    check s!"but not {c.toNat}" (SignIn.safeReturn t).isNone

/-- Passkeys: the discoverable flow. -/
def passkeyTests : IO Unit := withCtx fun ctx clock => do
  group "signin: passkeys"
  let alice ← ctx.store.addUser "alice" [] 1
  let k ← SoftKey.new
  enrol ctx alice k
  let b ← postJson ctx "/signin/webauthn/begin" emptyObj
  let opts := replyJson b
  checkEq "begin answers 200" b.status.toCode 200
  checkEq "with user verification required" (jstr opts "userVerification") "required"
  checkEq "for our relying party" (jstr opts "rpId") "auth.example.org"
  checkEq "and no credential list: the authenticator offers its passkeys"
    ((opts.getObjValAs? (Array Json) "allowCredentials").toOption.map (·.size)) (some 0)
  let cred ← k.assert opts
  let r ← postJson ctx "/signin/webauthn/finish" (Json.mkObj [("credential", cred)])
  checkEq "finish answers 200" r.status.toCode 200
  let body := replyJson r
  checkEq "and goes to the account by default" (jstr body "redirect") "/account"
  checkEq "amr: a device-bound key with user verification"
    ((body.getObjValAs? (List String) "amr").toOption) (some ["hwk", "user"])
  checkEq "acr: phishing-resistant, from a device-bound key" (jstr body "acr") "phrh"
  let some id := sessionCookieOf r | check "a session cookie is set" false
  let s ← Session.current ctx (withCookie id)
  checkEq "the cookie is alice's session" (s.map (·.user)) (some alice.id)
  checkEq "recording the key" (s.map (·.factors)) (some ["webauthn:" ++ b64u k.id])
  let stored ← ctx.store.findCredential k.id
  checkEq "the counter is recorded" (stored.map (·.signCount)) (some 1)
  checkEq "and when it was used" (stored.bind (·.lastUsed)) (some (← clock.get))
  -- Replays.
  let again ← postJson ctx "/signin/webauthn/finish" (Json.mkObj [("credential", cred)])
  checkEq "the same assertion again is refused" again.status.toCode 401
  check "and sets no cookie" (sessionCookieOf again).isNone
  let fresh ← k.assert opts
  let replay ← postJson ctx "/signin/webauthn/finish" (Json.mkObj [("credential", fresh)])
  checkEq "a fresh signature over a used challenge is refused" replay.status.toCode 401
  -- The challenge is used up by a failed attempt too.
  let b2 ← postJson ctx "/signin/webauthn/begin" emptyObj
  let wrongOrigin ← k.assert (replyJson b2) (origin := "https://evil.example")
  let r2 ← postJson ctx "/signin/webauthn/finish" (Json.mkObj [("credential", wrongOrigin)])
  checkEq "an assertion from another origin is refused" r2.status.toCode 401
  let right ← k.assert (replyJson b2)
  let r3 ← postJson ctx "/signin/webauthn/finish" (Json.mkObj [("credential", right)])
  checkEq "and its challenge is gone" r3.status.toCode 401
  -- An expired challenge.
  let b3 ← postJson ctx "/signin/webauthn/begin" emptyObj
  clock.modify (· + SignIn.challengeSeconds + 1)
  let late ← postJson ctx "/signin/webauthn/finish"
    (Json.mkObj [("credential", ← k.assert (replyJson b3))])
  checkEq "an expired challenge is refused" late.status.toCode 401
  -- No user handle in the discoverable flow.
  let ctx := { ctx with limiter := ← RateLimiter.new }
  let b4 ← postJson ctx "/signin/webauthn/begin" emptyObj
  let noHandle ← postJson ctx "/signin/webauthn/finish"
    (Json.mkObj [("credential", ← k.assert (replyJson b4) (withHandle := false))])
  checkEq "the discoverable flow needs the user handle" noHandle.status.toCode 401
  -- An unknown credential.
  let stranger ← SoftKey.new
  let b5 ← postJson ctx "/signin/webauthn/begin" emptyObj
  let unknown ← postJson ctx "/signin/webauthn/finish"
    (Json.mkObj [("credential", ← stranger.assert (replyJson b5))])
  checkEq "an unknown credential is refused" unknown.status.toCode 401
  -- Another relying party.
  let b6 ← postJson ctx "/signin/webauthn/begin" emptyObj
  let otherRp ← postJson ctx "/signin/webauthn/finish"
    (Json.mkObj [("credential", ← k.assert (replyJson b6) (rpId := "evil.example"))])
  checkEq "an assertion for another relying party is refused" otherRp.status.toCode 401
  -- A counter that went backwards.
  let ctx := { ctx with limiter := ← RateLimiter.new }
  k.counter.set 0
  let cloned ← signInVia ctx k
  checkEq "a counter that did not increase is refused" cloned.status.toCode 401
  let log ← Audit.entries ctx.store
  check "and audited as possibly cloned"
    (log.any fun e => e.event == "sign-in" && containsStr e.detail "cloned")
  k.counter.set 100
  -- Bad bodies.
  let notJson ← Server.route ctx (Req.mk' .post "/signin/webauthn/finish"
    [("Origin", testOrigin), ("Content-Type", "text/plain")] "x".toUTF8)
  checkEq "a body that is not JSON is refused" notJson.status.toCode 400
  let noCred ← postJson ctx "/signin/webauthn/finish" emptyObj
  checkEq "a body without a credential is refused" noCred.status.toCode 400
  let cross ← postJson ctx "/signin/webauthn/begin" emptyObj (origin := "https://evil.example")
  checkEq "a cross-origin begin is refused" cross.status.toCode 403
  -- A disabled account.
  discard <| ctx.store.setUserDisabled alice.id true
  let disabled ← signInVia ctx k
  checkEq "a disabled account cannot sign in" disabled.status.toCode 401
  discard <| ctx.store.setUserDisabled alice.id false
  let ok ← signInVia ctx k
  checkEq "re-enabled, it can" ok.status.toCode 200
  let summary ← auditSummary ctx
  check "every attempt is audited"
    (summary.count ("sign-in", "failure") ≥ 9 && summary.count ("sign-in", "success") == 2)
  check "and the chain verifies" ((← Audit.verify ctx.store) matches .ok _)

/-- Synced passkeys and EdDSA. -/
def syncedTests : IO Unit := withCtx fun ctx _ => do
  group "signin: a synced EdDSA passkey"
  let bob ← ctx.store.addUser "bob" [] 1
  let k ← SoftKey.new .edDsa (backupEligible := true)
  enrol ctx bob k
  let r ← signInVia ctx k
  checkEq "signs in" r.status.toCode 200
  checkEq "amr: a synced key" ((replyJson r).getObjValAs? (List String) "amr").toOption
    (some ["swk", "user"])
  checkEq "still phishing-resistant" (jstr (replyJson r) "acr") "phr"

/-- Security keys that do not verify the user, and second factors. -/
def secondFactorTests : IO Unit := withCtx fun ctx clock => do
  group "signin: security keys and second factors"
  let carol ← ctx.store.addUser "carol" [] 1
  let k ← SoftKey.new (uv := false)
  enrol ctx carol k
  -- Named begin: the account's credentials, user verification discouraged.
  let b ← postJson ctx "/signin/webauthn/begin" (Json.mkObj [("name", "Carol ")])
  let opts := replyJson b
  checkEq "a named begin discourages user verification" (jstr opts "userVerification")
    "discouraged"
  let allowIds := ((opts.getObjValAs? (Array Json) "allowCredentials").toOption.getD #[]).toList
    |>.map (jstr · "id")
  checkEq "and lists the account's credentials first" (allowIds.take 1) [b64u k.id]
  let notEnough ← postJson ctx "/signin/webauthn/finish"
    (Json.mkObj [("credential", ← k.assert opts (withHandle := false)), ("acr", "mfa")])
  checkEq "a security key without user verification alone is not mfa"
    (notEnough.status.toCode, errorOf notEnough) (401, "second_factor_required")
  check "and gets no cookie" (sessionCookieOf notEnough).isNone
  check "and no session row" ((← ctx.store.listSessions carol.id).isEmpty)
  let b1 ← postJson ctx "/signin/webauthn/begin" (Json.mkObj [("name", "carol")])
  let alone ← postJson ctx "/signin/webauthn/finish"
    (Json.mkObj [("credential", ← k.assert (replyJson b1) (withHandle := false))])
  checkEq "asked for nothing more, it signs in alone" alone.status.toCode 200
  checkEq "at sfa" (jstr (replyJson alone) "acr") "https://refeds.org/profile/sfa"
  checkEq "amr: the key, no user" ((replyJson alone).getObjValAs? (List String) "amr").toOption
    (some ["hwk"])
  check "with a session" (sessionCookieOf alone).isSome
  let b1' ← postJson ctx "/signin/webauthn/begin" (Json.mkObj [("name", "carol")])
  let notPhr ← postJson ctx "/signin/webauthn/finish"
    (Json.mkObj [("credential", ← k.assert (replyJson b1') (withHandle := false)),
      ("totp", "123456"), ("acr", "phr")])
  checkEq "phr is refused before a second factor is checked"
    (notPhr.status.toCode, errorOf notPhr) (401, "stronger_authentication_required")
  let unknownAcr ← postJson ctx "/signin/webauthn/finish"
    (Json.mkObj [("credential", ← k.assert (replyJson b1') (withHandle := false)),
      ("acr", "gold")])
  checkEq "an unknown level is a bad request" unknownAcr.status.toCode 400
  -- With a TOTP code.
  let secret ← giveTotp ctx carol
  let b2 ← postJson ctx "/signin/webauthn/begin" (Json.mkObj [("name", "carol")])
  let now ← clock.get
  let withCode ← postJson ctx "/signin/webauthn/finish"
    (Json.mkObj [("credential", ← k.assert (replyJson b2) (withHandle := false)),
      ("totp", totpAt secret now)])
  checkEq "with a TOTP code it signs in" withCode.status.toCode 200
  checkEq "amr: the key, otp and mfa"
    ((replyJson withCode).getObjValAs? (List String) "amr").toOption
    (some ["hwk", "otp", "mfa"])
  checkEq "acr: mfa, not phishing-resistant" (jstr (replyJson withCode) "acr")
    "https://refeds.org/profile/mfa"
  -- The same code again, in the next sign-in.
  let b3 ← postJson ctx "/signin/webauthn/begin" (Json.mkObj [("name", "carol")])
  let reused ← postJson ctx "/signin/webauthn/finish"
    (Json.mkObj [("credential", ← k.assert (replyJson b3) (withHandle := false)),
      ("totp", totpAt secret now)])
  checkEq "a TOTP code is good once" reused.status.toCode 401
  -- A known and an unknown name get answers of the same shape.
  let d1 ← postJson ctx "/signin/webauthn/begin" (Json.mkObj [("name", "nobody")])
  let d2 ← postJson ctx "/signin/webauthn/begin" (Json.mkObj [("name", "nobody")])
  let known ← postJson ctx "/signin/webauthn/begin" (Json.mkObj [("name", "carol")])
  let descs (r : Reply) : List Json :=
    ((replyJson r).getObjValAs? (Array Json) "allowCredentials").toOption.getD #[] |>.toList
  let keys (d : Json) : List String := match d with
    | .obj kvs => kvs.toArray.toList.map (·.1)
    | _ => []
  let lengths (r : Reply) : List Nat :=
    (descs r).map fun d => ((Base64Url.decode (jstr d "id")).map (·.size)).getD 0
  checkEq "an unknown name gets as many descriptors as a known one"
    ((descs d1).length, (descs known).length) (SignIn.namedAllowCount, SignIn.namedAllowCount)
  checkEq "with the same keys and no transports"
    (((descs d1) ++ (descs known)).map keys).eraseDups [["id", "type"]]
  check "and ids of lengths drawn from the same set"
    ((lengths d1 ++ lengths known).all (SignIn.Secrets.paddingIdLengths.contains ·))
  checkEq "the same answer each time" ((descs d1).map (jstr · "id"))
    ((descs d2).map (jstr · "id"))
  checkEq "answering 200 like a known name" d1.status.toCode 200
  let many := (List.range 40).map fun i =>
    (SignIn.Secrets.paddingCredentialId ctx.rootKey s!"name{i}" (i % 8)).size
  check "padding ids come in more than one length" (many.eraseDups.length > 1)

/-- Codes without a security key. -/
def codeTests : IO Unit :=
    withSignInCtx (fun c => { c with allowPasswords := true }) fun ctx clock => do
  group "signin: passwords and codes"
  let dave ← ctx.store.addUser "dave" [] 1
  let secret ← giveTotp ctx dave
  ctx.store.setPassword dave.id (← Factor.Password.hash "correct horse battery") 1
  let codes ← Factor.RecoveryCode.generate
  ctx.store.setRecoveryCodes dave.id
    (codes.map (Factor.RecoveryCode.digest (SignIn.Secrets.recoveryKey ctx.rootKey)))
  let signIn (fields : List (String × Json)) (client : String := "198.51.100.7") :=
    postJson ctx "/signin/codes" (Json.mkObj ([("name", Json.str "dave")] ++ fields))
      (client := client)
  let pw := Json.str "correct horse battery"
  let notEnough ← signIn [("password", pw), ("acr", "mfa")]
  checkEq "a password alone is not mfa"
    (notEnough.status.toCode, errorOf notEnough) (401, "second_factor_required")
  check "and gets no cookie" (sessionCookieOf notEnough).isNone
  let notPhr ← signIn [("password", pw), ("totp", "123456"), ("acr", "phr")]
  checkEq "codes are never phr"
    (notPhr.status.toCode, errorOf notPhr) (401, "stronger_authentication_required")
  let now ← clock.get
  let totpAlone ← signIn [("totp", totpAt secret now)]
  checkEq "a TOTP code alone gets no session" totpAlone.status.toCode 400
  let recAlone ← signIn [("recovery", codes.headD "")]
  checkEq "a recovery code alone gets no session" recAlone.status.toCode 400
  check "nothing was used up by those"
    ((← ctx.store.unspentRecoveryCodes dave.id) == 10 &&
      ((← ctx.store.findTotp dave.id).bind (·.lastStep)).isNone)
  check "and no session exists" ((← ctx.store.listSessions dave.id).isEmpty)
  let alone ← signIn [("password", pw)]
  checkEq "a password alone signs in" alone.status.toCode 200
  checkEq "at sfa" (jstr (replyJson alone) "acr") "https://refeds.org/profile/sfa"
  checkEq "amr: pwd" ((replyJson alone).getObjValAs? (List String) "amr").toOption (some ["pwd"])
  let log ← Audit.entries ctx.store
  check "the level reached is audited"
    (log.any fun e => e.event == "sign-in" && e.detail == "acr https://refeds.org/profile/sfa")
  let wrongAlone ← signIn [("password", "incorrect horse")]
  checkEq "a wrong password alone is refused" wrongAlone.status.toCode 401
  let wrongPw ← signIn [("password", "incorrect horse"), ("totp", totpAt secret now)]
  checkEq "a wrong password with a right code is refused" wrongPw.status.toCode 401
  check "without using up the code" ((← ctx.store.findTotp dave.id).bind (·.lastStep)).isNone
  let ok ← signIn [("password", pw), ("totp", totpAt secret now)]
  checkEq "a password and a TOTP code sign in" ok.status.toCode 200
  checkEq "amr: pwd, otp, mfa" ((replyJson ok).getObjValAs? (List String) "amr").toOption
    (some ["pwd", "otp", "mfa"])
  let unknown ← postJson ctx "/signin/codes"
    (Json.mkObj [("name", "nobody"), ("password", pw), ("totp", "123456")])
    (client := "198.51.100.8")
  checkEq "an unknown name answers like a wrong factor" (unknown.status.toCode, errorOf unknown)
    (wrongPw.status.toCode, errorOf wrongPw)
  clock.modify (· + 60)
  let now ← clock.get
  let withRec ← signIn [("totp", totpAt secret now), ("recovery", codes.headD "")]
    (client := "198.51.100.9")
  checkEq "a TOTP code and a recovery code sign in" withRec.status.toCode 200
  checkEq "amr: otp, rec, mfa" ((replyJson withRec).getObjValAs? (List String) "amr").toOption
    (some ["otp", "rec", "mfa"])
  checkEq "the recovery code is spent" (← ctx.store.unspentRecoveryCodes dave.id) 9
  clock.modify (· + 60)
  let spent ← signIn [("password", pw), ("recovery", codes.headD "")] (client := "198.51.100.10")
  checkEq "a spent recovery code is refused" spent.status.toCode 401
  -- Five wrong TOTP codes lock TOTP.
  let ctx := { ctx with limiter := ← RateLimiter.new (policy := { freeFailures := 100 }) }
  let wrong := if totpAt secret (← clock.get) == "000000" then "111111" else "000000"
  for i in [0:5] do
    discard <| postJson ctx "/signin/codes"
      (Json.mkObj [("name", "dave"), ("password", pw), ("totp", wrong)])
      (client := s!"203.0.113.{i}")
  check "five wrong codes lock TOTP"
    (((← ctx.store.findTotp dave.id).map (·.lockedUntil)).getD 0 > (← clock.get))
  check "audited" ((← auditSummary ctx).contains ("totp-locked", "refused"))
  clock.modify (· + 30)
  let locked ← postJson ctx "/signin/codes"
    (Json.mkObj [("name", "dave"), ("password", pw), ("totp", totpAt secret (← clock.get))])
  checkEq "then even the right code is refused" locked.status.toCode 401
  clock.modify (· + 900)
  let unlocked ← postJson ctx "/signin/codes"
    (Json.mkObj [("name", "dave"), ("password", pw), ("totp", totpAt secret (← clock.get))])
  checkEq "until the lock lapses" unlocked.status.toCode 200

/-- Passwords are off by default. -/
def passwordsOffTests : IO Unit := withCtx fun ctx clock => do
  group "signin: passwords off"
  let erin ← ctx.store.addUser "erin" [] 1
  let secret ← giveTotp ctx erin
  ctx.store.setPassword erin.id (← Factor.Password.hash "correct horse battery") 1
  let r ← postJson ctx "/signin/codes" (Json.mkObj [("name", "erin"),
    ("password", "correct horse battery"), ("totp", totpAt secret (← clock.get))])
  checkEq "a stored password counts for nothing when passwords are off" r.status.toCode 401
  let alone ← postJson ctx "/signin/codes" (Json.mkObj [("name", "erin"),
    ("password", "correct horse battery")])
  checkEq "nor alone" alone.status.toCode 401
  check "and makes no session" ((← ctx.store.listSessions erin.id).isEmpty)

/-- The rate limiter. -/
def signInRateLimitTests : IO Unit := withCtx fun ctx _ => do
  group "signin: rate limits"
  let frank ← ctx.store.addUser "frank" [] 1
  let k ← SoftKey.new
  enrol ctx frank k
  let stranger ← SoftKey.new
  let mut statuses := #[]
  for _ in [0:6] do
    let r ← signInVia ctx stranger (client := "192.0.2.1")
    statuses := statuses.push r.status.toCode
  checkEq "failures, then 429" statuses #[401, 401, 401, 401, 429, 429]
  let limited ← signInVia ctx k (client := "192.0.2.1")
  checkEq "even for a good passkey from that address" limited.status.toCode 429
  check "with Retry-After" ((limited.header "Retry-After").isSome)
  let other ← signInVia ctx k (client := "192.0.2.2")
  checkEq "another address is not affected" other.status.toCode 200
  check "the refusals are audited" ((← auditSummary ctx).contains ("sign-in", "refused"))
  let codes ← (List.range 6).mapM fun i => do
    let r ← postJson ctx "/signin/codes"
      (Json.mkObj [("name", "frank"), ("totp", "123456"), ("recovery", "AAAAA-AAAAA")])
      (client := s!"192.0.2.{10 + i}")
    return r.status.toCode
  checkEq "an account is limited across addresses" codes [401, 401, 401, 401, 429, 429]

/-- Step-up, `max_age` and `acr=phr`. -/
def stepUpTests : IO Unit := withCtx fun ctx clock => do
  group "signin: step-up"
  let gina ← ctx.store.addUser "gina" [] 1
  let k ← SoftKey.new
  enrol ctx gina k
  let sk ← SoftKey.new (uv := false)
  enrol ctx gina sk
  let secret ← giveTotp ctx gina
  let some id := sessionCookieOf (← signInVia ctx k) | check "signed in" false
  let r ← getPage ctx "/signin?return=%2Fdone&max_age=60" id
  checkEq "a fresh enough session goes straight back" (r.status.toCode, r.header "Location")
    (303, some "/done")
  clock.modify (· + 600)
  let page ← getPage ctx "/signin?return=%2Fdone&max_age=60" id
  checkEq "an older one is asked to step up" page.status.toCode 200
  check "in step-up mode" (containsStr page.bodyText "data-mode=\"stepup\"")
  let noSession ← postJson ctx "/signin/stepup/begin" emptyObj
  checkEq "step-up needs a session" noSession.status.toCode 401
  let before ← Session.current ctx (withCookie id)
  let up ← stepUpVia ctx k (some id) [("return", "/done")]
  checkEq "step-up answers 200" up.status.toCode 200
  checkEq "and goes back" (jstr (replyJson up) "redirect") "/done"
  let some id2 := sessionCookieOf up | check "a new cookie" false
  check "the identifier is rotated" (id2 != id && (← Session.current ctx (withCookie id)).isNone)
  let after ← Session.current ctx (withCookie id2)
  let now ← clock.get
  checkEq "the session is the same one, re-authenticated"
    (after.map fun s => (s.created, s.authTime)) (before.map fun s => (s.created, now))
  let back ← getPage ctx "/signin?return=%2Fdone&max_age=60" id2
  checkEq "then max_age is satisfied" back.status.toCode 303
  -- A security key with a code is not phishing-resistant.
  let b ← postJson ctx "/signin/stepup/begin" (Json.mkObj [("userVerification", "discouraged")])
    (some id2)
  let viaKey ← postJson ctx "/signin/stepup/finish"
    (Json.mkObj [("credential", ← sk.assert (replyJson b) (withHandle := false)),
      ("totp", totpAt secret (← clock.get))]) (some id2)
  checkEq "a step-up with a security key and a code" viaKey.status.toCode 200
  let some id3 := sessionCookieOf viaKey | check "a new cookie" false
  let phr ← getPage ctx "/signin?return=%2Fdone&acr=phr" id3
  checkEq "acr=phr is not satisfied by it" phr.status.toCode 200
  check "and only the passkey is offered" (!containsStr phr.bodyText "id=\"other\"")
  let up2 ← stepUpVia ctx k (some id3)
  let some id4 := sessionCookieOf up2 | check "a new cookie" false
  checkEq "a passkey step-up makes it phishing-resistant"
    ((← getPage ctx "/signin?return=%2Fdone&acr=phr" id4).status.toCode) 303
  -- Another user's credential cannot step up this session.
  let hal ← ctx.store.addUser "hal" [] 1
  let hk ← SoftKey.new
  enrol ctx hal hk
  let foreign ← stepUpVia ctx hk (some id4)
  checkEq "another user's passkey cannot step up a session" foreign.status.toCode 401
  check "and the session is untouched" ((← Session.current ctx (withCookie id4)).isSome)
  -- A sign-in by another user replaces the session rather than stepping it up.
  let replaced ← signInVia ctx hk (some id4)
  let some hid := sessionCookieOf replaced | check "hal signs in" false
  checkEq "signing in as someone else gives their session"
    ((← Session.current ctx (withCookie hid)).map (·.user)) (some hal.id)
  check "and ends the one the browser had" ((← Session.current ctx (withCookie id4)).isNone)
  check "step-ups are audited" ((← auditSummary ctx).contains ("step-up", "success"))

/-- Open redirects. -/
def redirectTests : IO Unit := withCtx fun ctx _ => do
  group "signin: open redirects"
  for bad in ["%2F%2Fevil.example", "https%3A%2F%2Fevil.example", "%2F%5Cevil.example",
      "javascript%3Aalert(1)"] do
    let r ← getPage ctx s!"/signin?return={bad}"
    checkEq s!"the sign-in page refuses return={bad}" r.status.toCode 400
  let ivy ← ctx.store.addUser "ivy" [] 1
  let k ← SoftKey.new
  enrol ctx ivy k
  let r ← signInVia ctx k (extra := [("return", "//evil.example/x")])
  checkEq "finish refuses an open-redirect return" r.status.toCode 400
  check "before checking anything, so no session" (sessionCookieOf r).isNone
  let ok ← signInVia ctx k (extra := [("return", "/authorize?client_id=c&state=s")])
  checkEq "a path on this origin is where it goes"
    (jstr (replyJson ok) "redirect") "/authorize?client_id=c&state=s"
  let some id := sessionCookieOf ok | check "signed in" false
  let page ← getPage ctx "/signin?return=%2F%2Fevil.example" id
  checkEq "a signed-in user is not redirected off-site either" page.status.toCode 400

/-- Sessions made through the policy. -/
def establishTests : IO Unit := withCtx fun ctx _ => do
  group "signin: establish"
  let jo ← ctx.store.addUser "jo" [] 1
  let k ← SoftKey.new
  enrol ctx jo k
  let sa ← authFor ctx k
  checkEq "a passkey assertion is an authentication" sa.amr ["hwk", "user"]
  check "at phrh" (sa.level == .phrh)
  let (s, _) ← Policy.establish ctx (Req.mk' .post "/") sa
  checkEq "establish starts jo's session" s.user jo.id
  check "which records the level" (s.level == .phrh)
  for (amr, level) in [(["hwk", "user"], Acr.phrh), (["swk", "user"], .phr),
      (["swk", "user", "otp", "mfa"], .phr), (["hwk", "otp", "mfa"], .mfa),
      (["pwd", "otp", "mfa"], .mfa), (["pwd"], .sfa), (["hwk"], .sfa), (["swk"], .sfa)] do
    check s!"the level of {amr}" (Acr.ofAmr amr == level)
  let synced ← SoftKey.new (backupEligible := true)
  enrol ctx jo synced
  check "a synced passkey is phr" ((← authFor ctx synced).level == .phr)
  let touch ← SoftKey.new (uv := false)
  enrol ctx jo touch
  check "a security key touched alone is sfa" ((← authFor ctx touch).level == .sfa)
  let kim ← ctx.store.addUser "kim" [] 1
  let (ks, _) ← Policy.establish ctx (Req.mk' .post "/") (← authFor ctx (← do
    let kk ← SoftKey.new
    enrol ctx kim kk
    pure kk))
  checkEq "a step-up with another user's authentication is refused"
    ((← Policy.stepUp ctx ks sa).isNone) true

/-- Second factors that come with an assertion count against the account. -/
def assertionAccountLimitTests : IO Unit :=
    withSignInCtx (fun c => { c with allowPasswords := true }) fun ctx _ => do
  group "signin: second factors with an assertion are limited per account"
  let mo ← ctx.store.addUser "mo" [] 1
  let k ← SoftKey.new (uv := false)
  enrol ctx mo k
  ctx.store.setPassword mo.id (← Factor.Password.hash "correct horse battery") 1
  let mut statuses := #[]
  for i in [0:12] do
    let client := s!"203.0.113.{100 + i}"
    let b ← postJson ctx "/signin/webauthn/begin" (Json.mkObj [("name", "mo")]) (client := client)
    let r ← postJson ctx "/signin/webauthn/finish"
      (Json.mkObj [("credential", ← k.assert (replyJson b) (withHandle := false)),
        ("password", "wrong password")]) (client := client)
    statuses := statuses.push r.status.toCode
  check "twelve wrong passwords from twelve addresses meet 429s"
    (statuses.contains 429 && statuses.back? == some 429) s!"{statuses}"
  check "after at most four tries" ((statuses.toList.take 4).all (· == 401))
  check "and the refusals are audited" ((← auditSummary ctx).contains ("sign-in", "refused"))

/-- Guessing a recovery code does not lock someone's TOTP. -/
def totpLockTests : IO Unit := withCtx fun ctx clock => do
  group "signin: TOTP is tried only after the other factor"
  let nia ← ctx.store.addUser "nia" [] 1
  let secret ← giveTotp ctx nia
  let ctx := { ctx with limiter := ← RateLimiter.new (policy := { freeFailures := 100 }) }
  let wrong := if totpAt secret (← clock.get) == "000000" then "111111" else "000000"
  for i in [0:8] do
    discard <| postJson ctx "/signin/codes" (Json.mkObj [("name", "nia"),
      ("recovery", "AAAAA-AAAAA"), ("totp", wrong)]) (client := s!"198.18.0.{i}")
  let rec_ ← ctx.store.findTotp nia.id
  checkEq "wrong recovery codes do not count as TOTP failures"
    (rec_.map fun t => (t.failures, t.lockedUntil)) (some (0, 0))
  let codes ← Factor.RecoveryCode.generate
  ctx.store.setRecoveryCodes nia.id
    (codes.map (Factor.RecoveryCode.digest (SignIn.Secrets.recoveryKey ctx.rootKey)))
  let bad ← postJson ctx "/signin/codes" (Json.mkObj [("name", "nia"),
    ("recovery", codes.headD ""), ("totp", wrong)])
  checkEq "a right recovery code with a wrong TOTP code is refused" bad.status.toCode 401
  checkEq "without spending the recovery code" (← ctx.store.unspentRecoveryCodes nia.id) 10
  checkEq "and that TOTP failure counts" ((← ctx.store.findTotp nia.id).map (·.failures)) (some 1)
  let ok ← postJson ctx "/signin/codes" (Json.mkObj [("name", "nia"),
    ("recovery", codes.headD ""), ("totp", totpAt secret (← clock.get))])
  checkEq "both right sign in" ok.status.toCode 200
  checkEq "spending the code" (← ctx.store.unspentRecoveryCodes nia.id) 9

/-- What is audited, and when the limiter is told of success. -/
def concludeTests : IO Unit := withCtx fun ctx _ => do
  group "signin: audit after the session exists"
  let oz ← ctx.store.addUser "oz" [] 1
  let (ozId, ozKey) ← sessionFor ctx oz
  let pat ← ctx.store.addUser "pat" [] 1
  let (patId, _) ← sessionFor ctx pat
  -- Oz begins a step-up, and the finish arrives with pat's cookie.
  let b ← postJson ctx "/signin/stepup/begin" emptyObj (some ozId)
  let before ← Audit.entries ctx.store
  let r ← postJson ctx "/signin/stepup/finish"
    (Json.mkObj [("credential", ← ozKey.assert (replyJson b))]) (some patId)
  checkEq "a step-up with another user's session is refused" r.status.toCode 401
  let after := (← Audit.entries ctx.store).toList.drop before.size
  checkEq "and audited as a failure, not a success"
    (after.map fun e => (e.event, e.outcome, e.detail))
    [("step-up", "failure", "no session to step up")]
  check "pat's session is untouched" ((← Session.current ctx (withCookie patId)).isSome)
  -- Signing in as oz from a browser with pat's session ends pat's.
  let r2 ← signInVia ctx ozKey (some patId)
  checkEq "signing in replaces the session the browser had" r2.status.toCode 200
  let log ← Audit.entries ctx.store
  check "and the ended session is audited"
    (log.any fun e => e.event == "sign-out" && e.userName == some "pat" &&
      e.detail == "replaced by a new sign-in")

/-- Begin endpoints are limited by pending challenges. -/
def beginLimitTests : IO Unit := withCtx fun ctx _ => do
  group "signin: pending challenges are capped"
  let mut codes := #[]
  for _ in [0:SignIn.maxPendingPerClient + 1] do
    codes := codes.push (← postJson ctx "/signin/webauthn/begin" emptyObj
      (client := "192.0.2.77")).status.toCode
  checkEq "an address may have twenty challenges pending"
    (codes.toList.take SignIn.maxPendingPerClient |>.all (· == 200), codes.back?)
    (true, some 429)
  let named ← postJson ctx "/signin/webauthn/begin" (Json.mkObj [("name", "x")])
    (client := "192.0.2.77")
  checkEq "named begins count too" named.status.toCode 429
  let url ← SignIn.createInvitation ctx.store ctx.config.issuer "quinn" [] 3600 (← ctx.clock)
  let inv ← postJson ctx ((url.drop ctx.config.issuer.length).toString ++ "/begin") emptyObj
    (client := "192.0.2.77")
  checkEq "and invitation begins" inv.status.toCode 429
  let v6a ← (List.range SignIn.maxPendingPerClient).mapM fun i =>
    postJson ctx "/signin/webauthn/begin" emptyObj (client := s!"2001:db8::{i + 1}")
  check "an IPv6 /64 counts as one address" (v6a.all (·.status.toCode == 200))
  checkEq "so another host in it is refused"
    (← postJson ctx "/signin/webauthn/begin" emptyObj (client := "2001:db8::ffff")).status.toCode
    429
  let other ← postJson ctx "/signin/webauthn/begin" emptyObj (client := "192.0.2.78")
  checkEq "another address is not affected" other.status.toCode 200
  match ← SignIn.newChallenge ctx (Req.mk' .post "/" (clientAddress := "192.0.2.79"))
      .authenticate none (total := 10) with
  | .error rep => checkEq "a full table answers 503" rep.status.toCode 503
  | .ok _ => check "a full table answers 503" false

/-- The sign-in tests. -/
def signInTests : IO Unit := do
  returnTests
  passkeyTests
  syncedTests
  secondFactorTests
  codeTests
  passwordsOffTests
  signInRateLimitTests
  stepUpTests
  redirectTests
  establishTests
  assertionAccountLimitTests
  totpLockTests
  concludeTests
  beginLimitTests

end PyleTests