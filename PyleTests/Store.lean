import PyleTests.Harness

/-!
# The store

Every table's accessors against a temporary database, with the weight on the
consume-once operations: a challenge, code, refresh token, device code,
invitation or recovery code is accepted once and never again, including when
several requests race for it.

`withCtx` is shared with the HTTP, session and audit tests: a handler context
over a fresh database, with a clock the test moves by hand.
-/

namespace PyleTests

open Pyle Pyle.Store

/-- A configuration for tests. -/
def testConfig (dir : System.FilePath) : Config :=
  { issuer := "https://auth.example.org", rpId := "auth.example.org",
    origins := ["https://auth.example.org"], database := dir / "pyle.db",
    rootKeyFile := dir / "root.key", port := 0 }

/-- Run `f` with a context over a fresh database in a temporary directory, and
a clock starting at `start` that `f` can set through the reference. -/
def withCtx (f : Http.Ctx → IO.Ref Nat → IO α) (start : Nat := 1700000000) : IO α :=
  IO.FS.withTempDir fun dir => do
    let clock ← IO.mkRef start
    let config := testConfig dir
    let store ← Store.openAt config.database start
    let ctx : Http.Ctx :=
      { config, store, limiter := ← Http.RateLimiter.new, rootKey := ← Crypto.randomBytes 32,
        clock := clock.get }
    f ctx clock

/-- Whether an action throws. -/
def throws (act : IO α) : IO Bool := do
  try discard act; return false
  catch _ => return true

/-- Run `n` copies of an action at once and count how many returned `true`. -/
def raceCount (n : Nat) (act : IO Bool) : IO Nat := do
  let tasks ← (List.range n).mapM fun _ => IO.asTask act
  let mut wins := 0
  for t in tasks do
    match ← IO.wait t with
    | .ok true => wins := wins + 1
    | _ => pure ()
  return wins

/-- Schema, migrations and opening. -/
def schemaTests : IO Unit := do
  group "store: schema"
  IO.FS.withTempDir fun dir => do
    let path := dir / "pyle.db"
    let s ← Store.openAt path 1
    checkEq "a new database is at the current version" (← s.version) schemaVersion
    let s ← Store.openAt path 2
    checkEq "migrating again changes nothing" (← s.version) schemaVersion
    let applied ← s.run fun c => query c "SELECT COUNT(*) FROM schema_version" #[] (colNat · 0)
    checkEq "each migration is recorded once" applied #[migrations.length]
    discard <| s.run fun c => exec c
      "INSERT INTO schema_version (version, description, applied) VALUES (?, ?, ?)"
      #[.int (schemaVersion + 1), "from the future", (3 : Nat)]
    check "a database from a newer pyle is refused" (← throws (Store.openAt path 3))
  -- Two processes starting on one new file: the version is read inside the
  -- migration's transaction, so the second sees the first's work.
  IO.FS.withTempDir fun dir => do
    let path := dir / "pyle.db"
    let opens ← (List.range 4).mapM fun _ => IO.asTask (Store.openAt path 1)
    let mut ok := true
    for t in opens do
      if let .error e ← IO.wait t then
        ok := false
        say s!"  open failed: {e}"
    check "concurrent first opens all succeed" ok
    let s ← Store.openAt path 1
    checkEq "and the migration is applied once"
      (← s.run fun c => query c "SELECT COUNT(*) FROM schema_version" #[] (colNat · 0))
      #[migrations.length]

/-- A client for the OIDC tests. -/
def sampleClient (id : String) : Client :=
  { id, name := "Example", secretHash := some (.of "secret".toUTF8),
    redirectUris := ["https://app.example.org/cb"], scopes := ["openid"], created := 1 }

/-- Accounts. -/
def userTests : IO Unit := withCtx fun ctx _ => do
  group "store: users"
  let s := ctx.store
  let alice ← s.addUser "alice" ["admin", "dev"] 10
  checkEq "the handle is 32 bytes" alice.handle.size 32
  check "a duplicate name is refused" (← throws (s.addUser "alice" [] 11))
  check "an upper-case name is refused" (← throws (s.addUser "Alice" [] 11))
  check "an empty name is refused" (← throws (s.addUser "" [] 11))
  check "a name with a quote is refused" (← throws (s.addUser "a'b" [] 11))
  let bob ← s.addUser "bob" [] 12
  check "handles differ" (alice.handle != bob.handle)
  checkEq "found by name" ((← s.findUserByName "alice").map (·.id)) (some alice.id)
  checkEq "found by handle" ((← s.findUserByHandle bob.handle).map (·.name)) (some "bob")
  checkEq "groups round-trip" ((← s.findUser alice.id).map (·.groups)) (some ["admin", "dev"])
  checkEq "an unknown name is none" ((← s.findUserByName "carol").isNone) true
  -- leansqlite binds text as a C string; a NUL would truncate the value.
  check "a name with NUL is refused, not truncated to alice"
    (← throws (s.findUserByName "alice\x00whatever"))
  check "and cannot be stored" (← throws (s.putClient (sampleClient "app\x00x")))
  checkEq "listed by name" ((← s.listUsers).map (·.name)) #["alice", "bob"]
  check "disabled" (← s.setUserDisabled bob.id true)
  checkEq "and reads back disabled" ((← s.findUser bob.id).map (·.disabled)) (some true)

/-- A credential for `user` with id `id`. -/
def sampleCredential (user : UserId) (id : ByteArray) : Credential :=
  { id, user, algorithm := -7, publicKey := ⟨Array.replicate 33 2⟩, signCount := 5,
    backupEligible := false, backupState := false, aaguid := ⟨Array.replicate 16 0⟩,
    transports := ["usb"], name := "key", created := 100, lastUsed := none }

/-- WebAuthn credentials and the two-authenticator rule. -/
def credentialTests : IO Unit := withCtx fun ctx _ => do
  group "store: credentials"
  let s := ctx.store
  let alice ← s.addUser "alice" [] 1
  let bob ← s.addUser "bob" [] 1
  let id1 := "cred-1".toUTF8
  let id2 := "cred-2".toUTF8
  let id3 := "cred-3".toUTF8
  s.addCredential (sampleCredential alice.id id1)
  s.addCredential (sampleCredential alice.id id2)
  check "a credential id registered to anyone is refused"
    (← throws (s.addCredential (sampleCredential bob.id id1)))
  let c ← s.findCredential id1
  checkEq "the key round-trips" (c.map (·.publicKey.size)) (some 33)
  checkEq "the algorithm round-trips" (c.map (·.algorithm)) (some (-7))
  checkEq "transports round-trip" (c.map (·.transports)) (some ["usb"])
  checkEq "listed for the user" ((← s.listCredentials alice.id).size) 2
  check "a use against the stored counter applies" (← s.recordCredentialUse id1 5 6 false false 200)
  check "a second use against the same counter does not"
    (!(← s.recordCredentialUse id1 5 7 false false 201))
  checkEq "the counter moved once" ((← s.findCredential id1).map (·.signCount)) (some 6)
  checkEq "last used is recorded" ((← s.findCredential id1).bind (·.lastUsed)) (some 200)
  check "removing the second-to-last authenticator is refused"
    (!(← s.removeCredential alice.id id1))
  s.addCredential (sampleCredential alice.id id3)
  check "another user cannot remove it" (!(← s.removeCredential bob.id id1))
  check "with three, one may go" (← s.removeCredential alice.id id1)
  checkEq "two remain" (← s.authenticatorCount alice.id) 2
  s.setTotp alice.id "sealed".toUTF8 5
  checkEq "a TOTP secret counts" (← s.authenticatorCount alice.id) 3

/-- TOTP replay and lockout, and recovery codes. -/
def storedFactorTests : IO Unit := withCtx fun ctx _ => do
  group "store: totp and recovery codes"
  let s := ctx.store
  let u ← s.addUser "alice" [] 1
  s.setTotp u.id "sealed".toUTF8 1
  check "a first step is accepted" (← s.acceptTotpStep u.id 100 3000)
  check "the same step is refused" (!(← s.acceptTotpStep u.id 100 3000))
  check "an earlier step is refused" (!(← s.acceptTotpStep u.id 99 3000))
  check "a later step is accepted" (← s.acceptTotpStep u.id 101 3030)
  checkEq "two racing for one step: one wins" (← raceCount 8 (s.acceptTotpStep u.id 200 6000)) 1
  for _ in [0:4] do
    checkEq "a failure below the limit locks nothing" (← s.recordTotpFailure u.id 7000) none
  checkEq "the fifth failure locks for fifteen minutes" (← s.recordTotpFailure u.id 7000)
    (some 7900)
  check "a good code is refused while locked" (!(← s.acceptTotpStep u.id 300 7100))
  check "and accepted after" (← s.acceptTotpStep u.id 300 7900)
  checkEq "the secret reads back" ((← s.findTotp u.id).map (·.sealedSecret)) (some "sealed".toUTF8)
  s.addCredential (sampleCredential u.id "c1".toUTF8)
  check "TOTP as one of two authenticators cannot be removed" (!(← s.removeTotp u.id))
  s.addCredential (sampleCredential u.id "c2".toUTF8)
  check "as one of three it can" (← s.removeTotp u.id)
  check "and then it is gone" ((← s.findTotp u.id).isNone)
  let codes := ["a", "b", "c"].map (·.toUTF8)
  s.setRecoveryCodes u.id codes
  checkEq "three unspent" (← s.unspentRecoveryCodes u.id) 3
  check "a code is spent once" (← s.spendRecoveryCode u.id "b".toUTF8 10)
  check "and not twice" (!(← s.spendRecoveryCode u.id "b".toUTF8 11))
  check "an unknown code is not spent" (!(← s.spendRecoveryCode u.id "z".toUTF8 11))
  checkEq "two unspent" (← s.unspentRecoveryCodes u.id) 2
  checkEq "racing for one code: one wins"
    (← raceCount 8 (s.spendRecoveryCode u.id "c".toUTF8 12)) 1

/-- Challenges: consumed by the first attempt, whatever its outcome. -/
def challengeTests : IO Unit := withCtx fun ctx _ => do
  group "store: challenges"
  let s := ctx.store
  let ch ← Crypto.randomBytes 32
  s.addChallenge { value := ch, purpose := .authenticate, user := none, expires := 100 }
  check "consumed for its purpose" ((← s.consumeChallenge ch .authenticate 50).isSome)
  check "not twice" ((← s.consumeChallenge ch .authenticate 51).isNone)
  let ch2 ← Crypto.randomBytes 32
  s.addChallenge { value := ch2, purpose := .register, user := none, expires := 100 }
  check "the wrong purpose is refused" ((← s.consumeChallenge ch2 .authenticate 50).isNone)
  check "and has used it up" ((← s.consumeChallenge ch2 .register 50).isNone)
  let ch3 ← Crypto.randomBytes 32
  s.addChallenge { value := ch3, purpose := .stepUp, user := none, expires := 100 }
  check "an expired challenge is refused" ((← s.consumeChallenge ch3 .stepUp 100).isNone)
  let ch4 ← Crypto.randomBytes 32
  s.addChallenge { value := ch4, purpose := .authenticate, user := none, expires := 100 }
  checkEq "sixteen racing for one challenge: one wins"
    (← raceCount 16 do return (← s.consumeChallenge ch4 .authenticate 10).isSome) 1
  s.addChallenge { value := ← Crypto.randomBytes 32, purpose := .register, user := none,
                   expires := 5 }
  checkEq "expired ones are purged" (← s.purgeChallenges 10) 1

/-- Clients, codes, refresh tokens. -/
def oidcTests : IO Unit := withCtx fun ctx _ => do
  group "store: clients, codes and refresh tokens"
  let s := ctx.store
  let u ← s.addUser "alice" [] 1
  -- Bound parameters, not spliced text: a quote in a value is just a quote.
  let odd := "x'); DROP TABLE users; --"
  s.putClient (sampleClient odd)
  checkEq "an id with SQL in it round-trips" ((← s.findClient odd).map (·.id)) (some odd)
  checkEq "and the users table is still there" ((← s.listUsers).size) 1
  s.putClient (sampleClient "app")
  checkEq "redirect URIs round-trip" ((← s.findClient "app").map (·.redirectUris))
    (some ["https://app.example.org/cb"])
  check "the secret is stored hashed"
    (((← s.findClient "app").bind (·.secretHash)).map (·.bytes) ==
      some (SecretHash.of "secret".toUTF8).bytes)
  let code ← Crypto.randomBytes 32
  let a : AuthCode :=
    { clientId := "app", redirectUri := "https://app.example.org/cb", codeChallenge := "abc",
      user := u.id, scope := "openid", nonce := some "n", amr := ["hwk", "user"],
      authTime := 90, expires := 160 }
  s.addCode (.of code) a
  let stored ← s.run fun c => query c "SELECT code_hash FROM codes" #[] (colBlob · 0)
  check "the database holds the hash, not the code" (stored == #[(SecretHash.of code).bytes])
  let got ← s.consumeCode (.of code) 120
  checkEq "a code is redeemed with its bindings"
    (got.map fun g => (g.clientId, g.redirectUri, g.codeChallenge, g.nonce, g.amr))
    (some ("app", "https://app.example.org/cb", "abc", some "n", ["hwk", "user"]))
  check "and only once" ((← s.consumeCode (.of code) 121).isNone)
  let code2 ← Crypto.randomBytes 32
  s.addCode (.of code2) a
  check "an expired code is refused" ((← s.consumeCode (.of code2) 160).isNone)
  let code3 ← Crypto.randomBytes 32
  s.addCode (.of code3) a
  checkEq "racing for one code: one wins"
    (← raceCount 8 do return (← s.consumeCode (.of code3) 100).isSome) 1
  -- Refresh-token rotation and reuse detection.
  let family ← Crypto.randomBytes 16
  let g : RefreshGrant :=
    { family, clientId := "app", user := u.id, scope := "openid", amr := ["hwk"],
      authTime := 90, expires := 10000 }
  let t1 ← Crypto.randomBytes 32
  let t2 ← Crypto.randomBytes 32
  let t3 ← Crypto.randomBytes 32
  s.startRefreshFamily (.of t1) g 100
  check "a family is begun once" (← throws (s.startRefreshFamily (.of t2) g 100))
  let isInvalid (o : RefreshOutcome) : Bool := o matches .invalid
  check "another client's presentation is invalid"
    (isInvalid (← s.rotateRefreshToken (.of t1) (.of t2) "other" 150 20000))
  match ← s.rotateRefreshToken (.of t1) (.of t2) "app" 200 20000 with
  | .rotated g' =>
    checkEq "a current token rotates with its grant" (g'.clientId, g'.expires) ("app", 20000)
  | _ => check "a current token rotates" false
  match ← s.rotateRefreshToken (.of t2) (.of t3) "app" 250 20000 with
  | .rotated _ => check "the successor was stored with it, and rotates in turn" true
  | _ => check "the successor was stored with it, and rotates in turn" false
  check "another client replaying a used token revokes nothing"
    (isInvalid (← s.rotateRefreshToken (.of t1) (.of (← Crypto.randomBytes 32)) "other" 260
      20000))
  match ← s.rotateRefreshToken (.of t1) (.of (← Crypto.randomBytes 32)) "app" 300 20000 with
  | .reused => check "presenting a used token is reuse" true
  | _ => check "presenting a used token is reuse" false
  check "and the family, including its newest token, is revoked"
    (isInvalid (← s.rotateRefreshToken (.of t3) (.of (← Crypto.randomBytes 32)) "app" 301
      20000))
  check "a revoked family cannot be begun again"
    (← throws (s.startRefreshFamily (.of (← Crypto.randomBytes 32)) g 302))
  let stray ← Crypto.randomBytes 32
  check "nor can anything be inserted into it, by any path" (← throws (s.run fun c => exec c
    "INSERT INTO refresh_tokens (token_hash, family, client_id, user_id, scope, amr, \
      auth_time, created, expires) VALUES (?, ?, 'app', ?, 'openid', '[]', 0, 0, 99999)"
    #[.blob stray, .blob family, .int u.id.val]))
  check "an unknown token is invalid"
    (isInvalid (← s.rotateRefreshToken (.of (← Crypto.randomBytes 32))
      (.of (← Crypto.randomBytes 32)) "app" 302 20000))
  let family2 ← Crypto.randomBytes 16
  let t4 ← Crypto.randomBytes 32
  s.startRefreshFamily (.of t4) { g with family := family2 } 400
  checkEq "racing with one refresh token: one rotation"
    (← raceCount 8 do
      match ← s.rotateRefreshToken (.of t4) (.of (← Crypto.randomBytes 32)) "app" 500 20000 with
      | .rotated _ => return true
      | _ => return false) 1
  checkEq "and the losers' reuse leaves no live token in the family"
    (← s.run fun c => query c
      "SELECT COUNT(*) FROM refresh_tokens WHERE family = ? AND used_at IS NULL"
      #[.blob family2] (colNat · 0)) #[0]
  check "removing a client" (← s.removeClient "app")
  check "removes its tokens too" ((← s.run fun c =>
    query c "SELECT 1 FROM refresh_tokens WHERE client_id = ?" #[.text "app"] (colInt · 0)).isEmpty)

/-- Device codes, invitations, signing keys. -/
def deviceTests : IO Unit := withCtx fun ctx _ => do
  group "store: device codes, invitations and keys"
  let s := ctx.store
  let u ← s.addUser "alice" [] 1
  s.putClient (sampleClient "cli")
  let dc ← Crypto.randomBytes 32
  s.addDeviceCode (.of dc)
    { userCode := "WDJB-MJHT", clientId := "cli", scope := "openid", interval := 5,
      expires := 1000 }
  match ← s.pollDeviceCodeFor (.of dc) "cli" 100 with
  | some .pending => check "a fresh code is pending" true
  | _ => check "a fresh code is pending" false
  match ← s.pollDeviceCodeFor (.of dc) "cli" 102 with
  | some .slowDown => check "polling too fast is slow_down" true
  | _ => check "polling too fast is slow_down" false
  match ← s.pollDeviceCodeFor (.of dc) "cli" 108 with
  | some .slowDown => check "slow_down grows the interval by five seconds" true
  | _ => check "slow_down grows the interval by five seconds" false
  match ← s.pollDeviceCodeFor (.of dc) "other" 109 with
  | none => check "another client's poll is refused" true
  | _ => check "another client's poll is refused" false
  checkEq "the user code finds it" ((← s.findPendingDeviceCode "WDJB-MJHT" 110).map (·.clientId))
    (some "cli")
  check "approved" (← s.decideDeviceCode "WDJB-MJHT" (.approved u.id ["hwk"] 110) 110)
  check "not twice" (!(← s.decideDeviceCode "WDJB-MJHT" .denied 111))
  match ← s.pollDeviceCodeFor (.of dc) "other" 115 with
  | none => check "another client cannot collect the approval" true
  | _ => check "another client cannot collect the approval" false
  match ← s.pollDeviceCodeFor (.of dc) "cli" 120 with
  | some (.approved cl _ user amr _) =>
    check "the poll collects the approval" (cl == "cli" && user == u.id && amr == ["hwk"])
  | _ => check "the poll collects the approval" false
  match ← s.pollDeviceCodeFor (.of dc) "cli" 130 with
  | some .expired => check "and only once" true
  | _ => check "and only once" false
  let dc2 ← Crypto.randomBytes 32
  s.addDeviceCode (.of dc2)
    { userCode := "AAAA-BBBB", clientId := "cli", scope := "openid", interval := 5,
      expires := 1000 }
  check "denied" (← s.decideDeviceCode "AAAA-BBBB" .denied 100)
  match ← s.pollDeviceCodeFor (.of dc2) "cli" 120 with
  | some .denied => check "the poll sees the denial" true
  | _ => check "the poll sees the denial" false
  let dc3 ← Crypto.randomBytes 32
  s.addDeviceCode (.of dc3)
    { userCode := "CCCC-DDDD", clientId := "cli", scope := "openid", interval := 5,
      expires := 200 }
  match ← s.pollDeviceCodeFor (.of dc3) "cli" 200 with
  | some .expired => check "an expired code is expired" true
  | _ => check "an expired code is expired" false
  match ← s.pollDeviceCodeFor (.of dc3) "other" 200 with
  | none => check "even an expired code is refused to another client" true
  | _ => check "even an expired code is refused to another client" false
  let inv ← Crypto.randomBytes 32
  s.addInvitation (.of inv)
    { userName := "bob", groups := ["dev"], createdBy := "alice", created := 1, expires := 100 }
  checkEq "an invitation is redeemed" ((← s.consumeInvitation (.of inv) 50).map (·.userName))
    (some "bob")
  check "once" ((← s.consumeInvitation (.of inv) 51).isNone)
  let k (kid : String) (state : KeyState) : StoredKey :=
    { kid, algorithm := "ES256", state, sealedKey := "sealed".toUTF8,
      publicKey := "pub".toUTF8, created := 1 }
  s.addKey (k "k1" .current)
  s.addKey (k "k2" .next)
  check "a next key is promoted" (← s.promoteKey "k2")
  check "a key that is not next is not" (!(← s.promoteKey "k1"))
  let states := (← s.listKeys).toList.map fun k => (k.kid, k.state.toString)
  checkEq "current and previous after rotation" (states.toArray.qsort (·.1 < ·.1))
    #[("k1", "previous"), ("k2", "current")]

/-- The configuration file. -/
def configTests : IO Unit := do
  group "config"
  let parse (s : String) : Except String Config := do
    Config.ofJson (← Lean.Json.parse s) "/etc/pyle"
  let minimal := "{\"issuer\": \"https://auth.example.org\", \"rpId\": \"auth.example.org\", " ++
    "\"origins\": [\"https://auth.example.org\"]}"
  match parse minimal with
  | .ok c =>
    checkEq "defaults: port" c.port 8420
    checkEq "defaults: idle timeout is eight hours" c.sessionIdleSeconds 28800
    checkEq "defaults: absolute timeout is thirty days" c.sessionAbsoluteSeconds 2592000
    checkEq "relative paths are relative to the file" c.database.toString "/etc/pyle/pyle.db"
    checkEq "no proxy is trusted by default" c.trustedProxies []
  | .error e => check "a minimal configuration parses" false e
  let bad (name : String) (json : String) :=
    check name (parse json matches .error _)
  bad "an unknown key is refused" ("{\"issuer\": \"https://a.org\", \"rpId\": \"a.org\", " ++
    "\"origins\": [\"https://a.org\"], \"sessionIdleSecond\": 5}")
  bad "a plain-http issuer is refused" ("{\"issuer\": \"http://a.org\", \"rpId\": \"a.org\", " ++
    "\"origins\": [\"https://a.org\"]}")
  bad "an origin with a path is refused" ("{\"issuer\": \"https://a.org\", \"rpId\": " ++
    "\"a.org\", \"origins\": [\"https://a.org/x\"]}")
  bad "no origins is refused" ("{\"issuer\": \"https://a.org\", \"rpId\": \"a.org\", " ++
    "\"origins\": []}")
  bad "an idle timeout past the absolute one is refused" ("{\"issuer\": \"https://a.org\", " ++
    "\"rpId\": \"a.org\", \"origins\": [\"https://a.org\"], \"sessionIdleSeconds\": 10, " ++
    "\"sessionAbsoluteSeconds\": 5}")
  bad "a missing issuer is refused" "{\"rpId\": \"a.org\", \"origins\": [\"https://a.org\"]}"
  bad "a host that only starts with localhost is refused" ("{\"issuer\": " ++
    "\"http://localhost.evil.example\", \"rpId\": \"a.org\", \"origins\": [\"https://a.org\"]}")
  bad "an origin that only starts with localhost is refused" ("{\"issuer\": \"https://a.org\", " ++
    "\"rpId\": \"a.org\", \"origins\": [\"http://localhostile.example\"]}")
  check "http on localhost with a port is accepted" ((parse ("{\"issuer\": " ++
    "\"http://localhost:8080\", \"rpId\": \"localhost\", " ++
    "\"origins\": [\"http://localhost:8080\"]}")) matches .ok _)

/-- The store. -/
def storeTests : IO Unit := do
  configTests
  schemaTests
  userTests
  credentialTests
  storedFactorTests
  challengeTests
  oidcTests
  deviceTests

end PyleTests