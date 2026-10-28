import PyleTests.Assurance

/-!
# Replacing the root key, ending access, administering accounts

`RootKey.rotate` against a database with everything sealed in it — signing
keys of every use and state, authenticator apps (one still sealed with the
associated data of before migration 6), recovery codes — and a server
context that has to notice: afterwards the keys sign under the same `kid`s
and verify, the apps' codes are accepted, the forward-authentication cookie
made before is refused, the recovery codes are gone, and a write sealed with
the retired key is refused.  Then each point a rotation can be interrupted
at, a key file that belongs to another database, and a database brought
forward from version 8.

`Admin.revokeSessions`, `Admin.disableUser` and `Admin.removeUser`: what each
ends, for one account or for everyone, including refresh-token families not
tied to a session, and that a disabled account gets in nowhere.
-/

namespace PyleTests

open Pyle Pyle.Http Pyle.Oidc
open Lean (Json)

/-- A context as `pyle serve` makes one (`Server.openCtx`), over a fresh key
and database in `dir`, with a clock the test moves. -/
def serverCtx (dir : System.FilePath) (clock : IO.Ref Nat) : IO Ctx := do
  let config := testConfig dir
  RootKey.create config.rootKeyFile
  Server.openCtx config clock.get

/-- The `kid` in a reply's ID token. -/
def idTokenKid (r : Reply) : String :=
  ((jwsHeader ((jsonStr r "id_token").getD "")).bind
    (·.getObjValAs? String "kid" |>.toOption)).getD ""

/-- Refresh as the confidential client `client`. -/
def refreshAs (ctx : Ctx) (rt client secret : String) : IO Reply :=
  postForm ctx "/token" [("grant_type", "refresh_token"), ("refresh_token", rt)]
    (basic client secret)

/-- Whether an IO error's message contains `s`. -/
def failsWith (act : IO α) (s : String) : IO Bool := do
  try discard act; return false
  catch e => return containsStr (toString e) s

/-- The stored mode of a file, as an octal number's digits. -/
def fileMode (p : System.FilePath) : IO Nat := do
  let out ← IO.Process.output { cmd := "stat", args := #["-c", "%a", p.toString] }
  return out.stdout.trimAscii.toString.toNat!

/-! ## Rotation -/

/-- Rotation re-seals everything, and the server keeps working. -/
def rotationTests : IO Unit := IO.FS.withTempDir fun dir => do
  group "root key: rotation"
  let clock ← IO.mkRef 1700000000
  let ctx0 ← serverCtx dir clock
  let ctx := withForwardAuth ctx0
  let config := ctx.config
  let key0 ← RootKey.load config.rootKeyFile
  checkEq "openCtx records the key's fingerprint" (← ctx.store.recordedRootKey)
    (some (Store.rootKeyId key0))
  check "which is not the key, nor a key derived for a purpose"
    (Store.rootKeyId key0 != key0 && Store.rootKeyId key0 != Keys.sealingKey key0 &&
      Store.rootKeyId key0 != SignIn.Secrets.totpKey key0)
  let alice ← ctx.store.addUser "alice" ["admin"] 1
  let (secret, _) ← addClients ctx
  let (cookie, _) ← sessionFor ctx alice
  -- Signing keys: next, current and previous of ES256; the other uses current.
  let now ← clock.get
  for use in Keys.Use.all do Keys.ensure ctx.store ctx.rootKey use now
  for i in [1:4] do discard <| Keys.rotate ctx.store ctx.rootKey .idTokenEs256 (now + i)
  let before := (← ctx.store.allKeys).toList.map fun k =>
    (k.kid, k.state.toString, k.publicKey.toList)
  check "a retired key is among them" (before.any (·.2.1 == "retired"))
  -- Apps: one new, one sealed with the associated data of before migration 6.
  let (_, appSecret) ← giveTotpApp ctx alice "phone"
  let legacySecret ← Factor.Totp.generateSecret
  let legacySealed ← Crypto.«seal» (SignIn.Secrets.totpKey key0) (SignIn.Secrets.userAd alice.id)
    legacySecret
  ctx.store.run fun c => discard <| Store.exec c
    "INSERT INTO totp_apps (user_id, name, secret, created, legacy_ad) VALUES (?, 'old', ?, 1, 1)"
    #[alice.id, legacySealed]
  -- Recovery codes.
  let codes ← Factor.RecoveryCode.generate
  ctx.store.setRecoveryCodes alice.id (Store.rootKeyId key0)
    (codes.map (Factor.RecoveryCode.digest (SignIn.Secrets.recoveryKey key0)))
  -- An ID token, a refresh token, a forward-auth cookie.
  let t ← exchange ctx (← obtainCode ctx cookie) secret
  let kid := idTokenKid t
  let some rt := jsonStr t "refresh_token" | check "a refresh token" false
  let some fwd ← forwardSignIn ctx cookie "app.example.org" "/"
    | check "a forward-auth cookie" false
  checkEq "the cookie passes before" (← askProxy ctx "app.example.org" "/" (cookies := [fwd])
    ).status.toCode 200
  -- Rotate, as the command does: its own connection to the database.
  let cli ← Store.Store.openAt config.database (← clock.get)
  let rot ← RootKey.rotate cli config.rootKeyFile (← clock.get)
  let key1 ← RootKey.load config.rootKeyFile
  check "the key file holds a new key" (key1 != key0 && key1.size == 32)
  checkEq "still mode 0600" (← fileMode config.rootKeyFile) 600
  check "and nothing is left at .new" !(← (RootKey.newPath config.rootKeyFile).pathExists)
  checkEq "the database records the new key" (← ctx.store.recordedRootKey)
    (some (Store.rootKeyId key1))
  checkEq "the rotation reports it" (rot.oldId, rot.newId)
    (Store.rootKeyId key0, Store.rootKeyId key1)
  checkEq "every signing key and app was re-sealed, and the codes deleted"
    (rot.resealed.keys, rot.resealed.totpApps, rot.resealed.recoveryCodes,
      rot.resealed.recoveryAccounts) (before.length, 2, 10, 1)
  let after ← ctx.store.allKeys
  checkEq "the same keys, kids, states and public keys"
    (after.toList.map fun k => (k.kid, k.state.toString, k.publicKey.toList)) before
  check "every one opens under the new key" (after.all (RootKey.opensKey key1))
  check "and none under the old" (after.all (!RootKey.opensKey key0 ·))
  let apps ← ctx.store.listTotpApps alice.id
  check "every app opens under the new key, none under the old"
    (apps.all (RootKey.opensApp key1) && apps.all (!RootKey.opensApp key0 ·))
  check "with its own row's associated data: the legacy flag is cleared"
    (apps.all (!·.legacyAd))
  checkEq "the recovery codes are gone" (← ctx.store.recoveryCodeCount alice.id) 0
  check "the rotation is audited"
    ((← Audit.entries ctx.store).any fun e => e.event == "root-key-rotated" &&
      containsStr e.detail (RootKey.showId rot.newId))
  check "and the chain verifies" ((← Audit.verify ctx.store) matches .ok _)
  -- The running server notices.
  let page ← get ctx "/account" cookie
  checkEq "the server answers with its session, without a restart" page.status.toCode 200
  let some cache := ctx.rootKeyCache | check "the server context has a cache" false
  checkEq "and now holds the new key" (← cache.get) (Store.rootKeyId key1, key1)
  let live ← Server.withCurrentRootKey ctx
  check "requests get the new key" (live.rootKey == key1)
  let r ← refreshAs ctx rt "app" secret
  checkEq "the refresh token still rotates" r.status.toCode 200
  checkEq "and the ID token is signed by the same kid" (idTokenKid r) kid
  check "verifying against the JWKS" ((← verifyEs256 ctx ((jsonStr r "id_token").getD ""))
    matches .ok _)
  let access := (jsonStr r "access_token").getD ""
  checkEq "the biscuit signed after it is good at /userinfo"
    (← get ctx "/userinfo" (headers := [("Authorization", s!"Bearer {access}")])).status.toCode 200
  checkEq "and so is the one from before"
    (← get ctx "/userinfo" (headers := [("Authorization",
      s!"Bearer {(jsonStr t "access_token").getD ""}")])).status.toCode 200
  clock.modify (· + 30)
  let ok (r : Except Policy.TotpRefusal Policy.Factor) : Bool := r matches .ok _
  check "a code from the app is accepted"
    (ok (← Policy.checkTotp live alice.id (totpAt appSecret (← clock.get))))
  clock.modify (· + 30)
  check "and one from the migrated app"
    (ok (← Policy.checkTotp live alice.id (totpAt legacySecret (← clock.get))))
  check "no app was unreadable"
    !((← Audit.entries ctx.store).any (·.event == "totp-secret-unreadable"))
  let r ← askProxy ctx "app.example.org" "/" (cookies := [fwd])
  checkEq "the forward-auth cookie made before no longer passes" r.status.toCode 302
  let some fwd' ← forwardSignIn ctx cookie "app.example.org" "/"
    | check "a new forward-auth cookie" false
  checkEq "a new one does" (← askProxy ctx "app.example.org" "/" (cookies := [fwd'])
    ).status.toCode 200
  check "the old recovery codes no longer sign in"
    ((← Policy.checkRecovery live alice.id (codes.headD "")).isNone)
  -- Writes sealed under the retired key are refused.
  let stale := { ctx0 with rootKey := key0, rootKeyCache := none }
  let late ← Factor.Totp.generateSecret
  check "an app sealed under the old key is refused"
    (← failsWith (ctx.store.addTotpApp alice.id "late" none 9 (Store.rootKeyId key0)
      (SignIn.Secrets.sealTotpApp key0 alice.id · late)) "root key was replaced")
  checkEq "and not stored" (← ctx.store.listTotpApps alice.id).size 2
  check "so are recovery codes under it"
    (← failsWith (ctx.store.setRecoveryCodes alice.id (Store.rootKeyId key0) []) "replaced")
  let fresh ← Crypto.SigningKey.generate .edDsa
  let row ← Keys.toStored key0 fresh .next now
  check "and a signing key" (← failsWith (ctx.store.addKey row (Store.rootKeyId key0)) "replaced")
  check "the key lifecycle with the old key fails too"
    (← throws (Keys.rotate stale.store stale.rootKey .idTokenRs256 (now + 9)))
  check "while the new key's writes go through"
    ((← ctx.store.addTotpApp alice.id "new" none 9 (Store.rootKeyId key1)
      (SignIn.Secrets.sealTotpApp key1 alice.id · late)).isSome)
  -- A request already under way with the old key, enrolling an app.
  let (_, key) ← sessionFor live alice
  let some cookie2 := sessionCookieOf (← stepUpVia live key (some cookie))
    | check "a step-up" false
  let b ← postJson stale "/account/totp/begin" (Json.mkObj [("name", "racing")]) (some cookie2)
  checkEq "an enrolment begins under the old key" b.status.toCode 200
  let (c, _) ← confirmApp stale cookie2 b (← clock.get)
  checkEq "and its confirmation fails rather than store a secret under it" c.status.toCode 500
  check "nothing is stored" ((← ctx.store.listTotpApps alice.id).all (·.name != "racing"))
  let (c, _) ← confirmApp ctx cookie2 b (← clock.get)
  checkEq "under the new key, the pending secret no longer opens" c.status.toCode 400
  -- Rotating again works from the new key.
  let rot2 ← RootKey.rotate cli config.rootKeyFile (← clock.get)
  check "a second rotation starts from the first's key" (rot2.oldId == Store.rootKeyId key1)
  checkEq "and the server follows again" (← get ctx "/account" cookie2).status.toCode 200

/-- Where a rotation can stop, and what the next start makes of it. -/
def crashTests : IO Unit := do
  group "root key: interrupted rotations"
  -- Only the new key written: the transaction never committed.
  IO.FS.withTempDir fun dir => do
    let clock ← IO.mkRef 1700000000
    let ctx ← serverCtx dir clock
    let config := ctx.config
    let key0 ← RootKey.load config.rootKeyFile
    Keys.ensure ctx.store ctx.rootKey .biscuitRoot 1
    let next := RootKey.newPath config.rootKeyFile
    check "interrupted after writing the new key"
      (← throws (RootKey.rotate ctx.store config.rootKeyFile 2 (interrupt := some .afterNew)))
    check "the new key is left at .new, mode 0600"
      ((← next.pathExists) && (← fileMode next) == 600)
    checkEq "the database still records the old key" (← ctx.store.recordedRootKey)
      (some (Store.rootKeyId key0))
    check "and its keys open under it" ((← ctx.store.allKeys).all (RootKey.opensKey key0))
    check "nothing was audited" !((← Audit.entries ctx.store).any (·.event == "root-key-rotated"))
    let ctx' ← Server.openCtx config clock.get
    check "a restart uses the old key, ignoring .new" (ctx'.rootKey == key0)
    let rot ← RootKey.rotate ctx.store config.rootKeyFile 3
    check "the next rotation replaces the stale .new and succeeds"
      ((← RootKey.load config.rootKeyFile) != key0 && !(← next.pathExists) &&
        rot.oldId == Store.rootKeyId key0)
  -- Committed, not installed.
  IO.FS.withTempDir fun dir => do
    let clock ← IO.mkRef 1700000000
    let ctx ← serverCtx dir clock
    let config := ctx.config
    let key0 ← RootKey.load config.rootKeyFile
    Keys.ensure ctx.store ctx.rootKey .biscuitRoot 1
    let next := RootKey.newPath config.rootKeyFile
    check "interrupted after the commit"
      (← throws (RootKey.rotate ctx.store config.rootKeyFile 2 (interrupt := some .afterCommit)))
    let some key1 ← RootKey.tryLoad next | check "the new key is at .new" false
    checkEq "the database records the new key" (← ctx.store.recordedRootKey)
      (some (Store.rootKeyId key1))
    check "while the key file is still the old one" ((← RootKey.load config.rootKeyFile) == key0)
    let ctx' ← Server.openCtx config clock.get
    check "a restart finishes the rotation" (ctx'.rootKey == key1 &&
      (← RootKey.load config.rootKeyFile) == key1 && !(← next.pathExists))
    check "and the keys open under what it uses" ((← ctx.store.allKeys).all (RootKey.opensKey key1))
  -- Committed, not installed, under a running server.
  IO.FS.withTempDir fun dir => do
    let clock ← IO.mkRef 1700000000
    let ctx ← serverCtx dir clock
    let config := ctx.config
    let alice ← ctx.store.addUser "alice" [] 1
    let (cookie, _) ← sessionFor ctx alice
    discard <| RootKey.rotate (← Store.Store.openAt config.database 2) config.rootKeyFile 2
      (interrupt := some .afterCommit) |>.toBaseIO
    checkEq "the running server finishes it at its next request"
      (← get ctx "/account" cookie).status.toCode 200
    let key1 ← RootKey.load config.rootKeyFile
    checkEq "installing the new key" (← ctx.store.recordedRootKey) (some (Store.rootKeyId key1))
    check "from .new" !(← (RootKey.newPath config.rootKeyFile).pathExists)
    check "and using it" ((← Server.withCurrentRootKey ctx).rootKey == key1)
  -- A key file that is not the database's.
  IO.FS.withTempDir fun dir => do
    let clock ← IO.mkRef 1700000000
    let ctx ← serverCtx dir clock
    let config := ctx.config
    let alice ← ctx.store.addUser "alice" [] 1
    let (cookie, _) ← sessionFor ctx alice
    let key0 ← RootKey.load config.rootKeyFile
    IO.FS.removeFile config.rootKeyFile
    RootKey.create config.rootKeyFile
    check "another key file is refused at start-up"
      (← failsWith (Server.openCtx config clock.get) "is not the one this database is sealed under")
    check "and by the commands" (← failsWith (RootKey.resolve ctx.store config.rootKeyFile 3)
      "refusing to start")
    let other ← Crypto.randomBytes 32
    Sys.writeNewPrivate (RootKey.newPath config.rootKeyFile).toString other
    check "so is a .new that does not match either"
      (← throws (RootKey.resolve ctx.store config.rootKeyFile 3))
    check "and it is left alone" ((← RootKey.tryLoad (RootKey.newPath config.rootKeyFile)) == some other)
    -- The running server answers 503 until the right key is back.
    let some cache := ctx.rootKeyCache | check "a cache" false
    cache.set (ByteArray.mk #[0], key0)
    checkEq "a running server that cannot find its key answers 503"
      (← get ctx "/account" cookie).status.toCode 503
    IO.FS.removeFile config.rootKeyFile
    IO.FS.writeBinFile config.rootKeyFile key0
    checkEq "and recovers once it is back" (← get ctx "/account" cookie).status.toCode 200
    check "without a rotation to finish, the stray .new is ignored"
      ((← RootKey.resolve ctx.store config.rootKeyFile 4) == key0)
  -- No key file at all.
  IO.FS.withTempDir fun dir => do
    let config := testConfig dir
    check "without a key file nothing starts"
      (← failsWith (Server.openCtx config (pure 1)) "cannot read the root key")
    check "and no database is created" !(← config.database.pathExists)

/-- A database from before migration 9 records the key it is first opened
with, if the key opens what it has sealed. -/
def rootKeyMigrationTests : IO Unit := IO.FS.withTempDir fun dir => do
  group "root key: migration 9"
  let config := testConfig dir
  let key ← Crypto.randomBytes 32
  let s ← Store.Store.openFile config.database
  let row ← Keys.toStored key (← Crypto.SigningKey.generate .edDsa) .current 1
  s.run fun c => do
    discard <| Store.currentVersion c
    for m in Store.migrations.take 8 do
      for st in m.statements do discard <| Store.exec c st
      discard <| Store.exec c
        "INSERT INTO schema_version (version, description, applied) VALUES (?, ?, ?)"
        #[m.version, m.description, (1 : Nat)]
    discard <| Store.exec c
      "INSERT INTO keys (kid, algorithm, state, sealed, public_key, created) \
        VALUES (?, ?, 'current', ?, ?, 1)" #[row.kid, row.algorithm, row.sealedKey, row.publicKey]
    discard <| Store.exec c
      "INSERT INTO challenges (challenge, purpose, expires) VALUES (X'01', 'register', 99)"
  checkEq "the database is at version 8" (← s.version) 8
  s.migrate 2
  checkEq "and is brought forward" (← s.version) Store.schemaVersion
  checkEq "with no key recorded" (← s.recordedRootKey) none
  checkEq "an old challenge has no user handle"
    ((← s.consumeChallenge (ByteArray.mk #[1]) .register 5).map (·.userHandle)) (some none)
  IO.FS.writeBinFile config.rootKeyFile (← Crypto.randomBytes 32)
  check "a key that opens nothing sealed there is refused"
    (← failsWith (RootKey.resolve s config.rootKeyFile 3) "opens nothing sealed")
  checkEq "and not recorded" (← s.recordedRootKey) none
  IO.FS.writeBinFile config.rootKeyFile key
  check "its own key is accepted" ((← RootKey.resolve s config.rootKeyFile 3) == key)
  checkEq "and recorded" (← s.recordedRootKey) (some (Store.rootKeyId key))
  let s2 ← Store.Store.openAt (dir / "empty.db") 1
  IO.FS.writeBinFile (dir / "other.key") (← Crypto.randomBytes 32)
  check "an empty database takes any key" ((← RootKey.resolve s2 (dir / "other.key") 1).size == 32)

/-- An invitation finished after a rotation creates the account with the
handle its passkey was given. -/
def invitationHandleTests : IO Unit := withCtx fun ctx clock => do
  group "root key: invitations across a rotation"
  let url ← SignIn.createInvitation ctx.store ctx.config.issuer "ivy" [] 3600 (← clock.get)
  let path := (url.drop ctx.config.issuer.length).toString
  let b ← postJson ctx (path ++ "/begin") emptyObj
  let k ← SoftKey.new
  let cred ← k.create (replyJson b)
  let rotated := { ctx with rootKey := ← Crypto.randomBytes 32 }
  let r ← postJson rotated (path ++ "/finish") (Json.mkObj [("credential", cred)])
  checkEq "the invitation is finished under another root key" r.status.toCode 201
  let some ivy ← ctx.store.findUserByName "ivy" | check "ivy exists" false
  checkEq "with the user handle the passkey holds" ivy.handle.toList (← k.handle.get).toList
  checkEq "and the passkey signs in" (← signInVia rotated k).status.toCode 200

/-! ## Ending access -/

/-- Revoking one account's sessions, and everyone's. -/
def revokeTests : IO Unit := withCtx fun ctx clock => do
  group "admin: sessions revoke"
  let ctx := withForwardAuth ctx
  let alice ← ctx.store.addUser "alice" ["admin"] 1
  let bob ← ctx.store.addUser "bob" ["admin"] 1
  let (secret, _) ← addClients ctx
  let some offSecret ← registerClient ctx.store "offline" "Offline" [appRedirect]
      ["openid", "offline_access"] false {} 1
    | check "an offline client" false
  let a1 ← signedIn ctx alice
  let a2 ← signedIn ctx alice
  let b1 ← signedIn ctx bob
  let bound := (jsonStr (← exchange ctx (← obtainCode ctx a1) secret) "refresh_token").getD ""
  let offline := (jsonStr (← exchange ctx (← obtainCode ctx a1 "offline"
    (scope := "openid offline_access")) offSecret (client := "offline")) "refresh_token").getD ""
  let bobs := (jsonStr (← exchange ctx (← obtainCode ctx b1 "offline"
    (scope := "openid offline_access")) offSecret (client := "offline")) "refresh_token").getD ""
  let pendingCode ← obtainCode ctx a2
  -- A device approved and not yet polled.
  let d ← deviceCodes ctx
  let dc := (jsonStr d "device_code").getD ""
  discard <| postForm ctx "/device" [("user_code", (jsonStr d "user_code").getD ""),
    ("decision", "approve")] sameOrigin (cookie := some a1)
  -- A device that has its tokens: a family tied to no session.
  let d2 ← deviceCodes ctx
  discard <| postForm ctx "/device" [("user_code", (jsonStr d2 "user_code").getD ""),
    ("decision", "approve")] sameOrigin (cookie := some a1)
  clock.modify (· + ctx.config.devicePollSeconds)
  let dt ← pollDevice ctx ((jsonStr d2 "device_code").getD "")
  let deviceRefresh := (jsonStr dt "refresh_token").getD ""
  check "a device has a refresh token" !deviceRefresh.isEmpty
  -- A forward-auth code not yet redeemed.
  let begun ← askProxy ctx "app.example.org" "/"
  let g ← get ctx (location begun |>.drop issuer.length |>.toString) a1
  check "a forward-auth code is pending" ((location g).startsWith "https://app.example.org/")
  let r ← Admin.revokeSessions ctx.store (some alice) (← clock.get)
  checkEq "alice's two sessions end" r.sessions 2
  checkEq "her three families are revoked: session-bound, offline, device" r.families 3
  checkEq "her pending code, device approval and forward-auth code are withdrawn" r.codes 3
  for c in [a1, a2] do
    check "her session is gone" (← Session.current ctx (withCookie c)).isNone
  checkEq "the session's refresh token is refused"
    (jsonStr (← refreshAs ctx bound "app" secret) "error") (some "invalid_grant")
  checkEq "so is the offline_access one"
    (jsonStr (← refreshAs ctx offline "offline" offSecret) "error") (some "invalid_grant")
  checkEq "and the device's"
    (jsonStr (← postForm ctx "/token" [("grant_type", "refresh_token"),
      ("refresh_token", deviceRefresh), ("client_id", "cli")]) "error") (some "invalid_grant")
  checkEq "the unexchanged code is refused"
    (jsonStr (← exchange ctx pendingCode secret) "error") (some "invalid_grant")
  clock.modify (· + ctx.config.devicePollSeconds)
  checkEq "the approved device is denied" (jsonStr (← pollDevice ctx dc) "error")
    (some "access_denied")
  let back ← askProxy ctx "app.example.org" ((location g).drop "https://app.example.org".length
    |>.toString) (cookies := [(cookieSet begun ForwardAuth.stateCookieName).getD ""])
  check "the forward-auth code sets no cookie" (forwardCookie back).isNone
  check "bob's session lives on" (← Session.current ctx (withCookie b1)).isSome
  let rb ← refreshAs ctx bobs "offline" offSecret
  checkEq "and his offline token" rb.status.toCode 200
  let bobs := (jsonStr rb "refresh_token").getD ""
  check "the revocation is audited with alice's name"
    ((← Audit.entries ctx.store).any fun e => e.event == "sessions-revoked" &&
      e.userName == some "alice" && containsStr e.detail "3 refresh-token families")
  let all ← Admin.revokeSessions ctx.store none (← clock.get)
  checkEq "revoking everyone's ends bob's session and family" (all.sessions, all.families) (1, 1)
  check "his session is gone" (← Session.current ctx (withCookie b1)).isNone
  checkEq "and his offline token" (jsonStr (← refreshAs ctx bobs "offline" offSecret) "error")
    (some "invalid_grant")
  checkEq "no sessions are left" (← ctx.store.listAllSessions).size 0
  check "audited for every account"
    ((← Audit.entries ctx.store).any fun e => e.event == "sessions-revoked" &&
      e.userName.isNone && containsStr e.detail "every account")
  let again ← signedIn ctx alice
  check "signing in again works" (← Session.current ctx (withCookie again)).isSome
  checkEq "and sessions list shows it" (← ctx.store.listAllSessions).size 1

/-- A disabled account gets in nowhere, and an enabled one again. -/
def disableTests : IO Unit :=
    withSignInCtx (fun c => { c with allowPasswords := true }) fun ctx0 clock => do
  group "admin: disabled accounts"
  let ctx := withForwardAuth ctx0
  let alice ← ctx.store.addUser "alice" ["admin"] 1
  discard <| addClients ctx
  let some offSecret ← registerClient ctx.store "offline" "Offline" [appRedirect]
      ["openid", "offline_access"] false {} 1
    | check "an offline client" false
  let (cookie, k) ← sessionFor ctx alice
  let totp ← giveTotp ctx alice
  ctx.store.setPassword alice.id (← Factor.Password.hash "correct horse battery") 1
  let codes ← Factor.RecoveryCode.generate
  ctx.store.setRecoveryCodes alice.id .empty
    (codes.map (Factor.RecoveryCode.digest (SignIn.Secrets.recoveryKey ctx.rootKey)))
  let t ← exchange ctx (← obtainCode ctx cookie "offline" (scope := "openid offline_access"))
    offSecret (client := "offline")
  let offline := (jsonStr t "refresh_token").getD ""
  let access := (jsonStr t "access_token").getD ""
  let some fwd ← forwardSignIn ctx cookie "app.example.org" "/" | check "a cookie" false
  let d ← deviceCodes ctx
  discard <| postForm ctx "/device" [("user_code", (jsonStr d "user_code").getD ""),
    ("decision", "approve")] sameOrigin (cookie := some cookie)
  let some r ← Admin.disableUser ctx.store alice (← clock.get) | check "alice is disabled" false
  check "disabling ends her session and her family" (r.sessions == 1 && r.families == 1)
  check "and is audited"
    ((← Audit.entries ctx.store).any fun e => e.event == "user-changed" &&
      e.userName == some "alice" && e.detail.startsWith "disabled")
  clock.modify (· + 60)
  let now ← clock.get
  let passkey ← signInVia ctx k
  check "no passkey sign-in" (passkey.status.toCode == 401 && (sessionCookieOf passkey).isNone)
  let named ← signInVia ctx k (beginBody := Json.mkObj [("name", "alice")])
    (extra := [("totp", totpAt totp now)])
  checkEq "no sign-in by name with a key and a code" named.status.toCode 401
  -- Each with a limiter of its own: the refusal is for the account, not the rate.
  let codesIn (fields : List (String × Json)) : IO Reply := do
    postJson { ctx with limiter := ← RateLimiter.new } "/signin/codes"
      (Json.mkObj ([("name", Json.str "alice")] ++ fields))
  checkEq "no sign-in with a password and a code"
    (← codesIn [("password", "correct horse battery"), ("totp", totpAt totp (now + 30))]
      ).status.toCode 401
  checkEq "nor with a password and a recovery code"
    (← codesIn [("password", "correct horse battery"), ("recovery", codes.headD "")]
      ).status.toCode 401
  checkEq "nor with a code and a recovery code"
    (← codesIn [("totp", totpAt totp (now + 60)), ("recovery", codes.headD "")]).status.toCode 401
  checkEq "her recovery codes were not spent by trying" (← ctx.store.unspentRecoveryCodes alice.id)
    10
  check "her old session is not honoured" (← Session.current ctx (withCookie cookie)).isNone
  checkEq "nor its step-up" (← stepUpVia ctx k (some cookie)).status.toCode 401
  checkEq "no refresh" (jsonStr (← refreshAs ctx offline "offline" offSecret) "error")
    (some "invalid_grant")
  clock.modify (· + ctx.config.devicePollSeconds)
  checkEq "the device she approved gets nothing"
    (jsonStr (← pollDevice ctx ((jsonStr d "device_code").getD "")) "error") (some "access_denied")
  let userinfo ← get ctx "/userinfo" (headers := [("Authorization", s!"Bearer {access}")])
  checkEq "her access token is refused at /userinfo" userinfo.status.toCode 401
  checkEq "forward auth does not pass her"
    (← askProxy ctx "app.example.org" "/" (cookies := [fwd])).status.toCode 302
  -- Even a refresh token that survived (as a backup restored over the
  -- revocation might bring back) is refused for a disabled account.
  let restored ← exchange ctx (← obtainCode ctx (← signedInEnabled ctx alice) "offline"
    (scope := "openid offline_access")) offSecret (client := "offline")
  ctx.store.run fun c => discard <| Store.exec c "UPDATE users SET disabled = 1 WHERE id = ?"
    #[alice.id]
  checkEq "a refresh token of a disabled account is refused"
    (jsonStr (← refreshAs ctx ((jsonStr restored "refresh_token").getD "") "offline" offSecret)
      "error") (some "invalid_grant")
  check "an invitation cannot recreate the name"
    (← throws (SignIn.createInvitation ctx.store ctx.config.issuer "alice" [] 60 now))
  check "enabling works" (← Admin.enableUser ctx.store alice now)
  checkEq "and the passkey signs in again" (← signInVia ctx k).status.toCode 200
  check "audited" ((← Audit.entries ctx.store).any fun e => e.event == "user-changed" &&
    e.detail == "enabled")
where
  /-- Enable an account behind the store's back, sign in, and leave it so. -/
  signedInEnabled (ctx : Ctx) (u : Store.User) : IO String := do
    ctx.store.run fun c => discard <| Store.exec c "UPDATE users SET disabled = 0 WHERE id = ?"
      #[u.id]
    signedIn ctx u

/-- Removing an account removes everything that was its. -/
def userRemoveTests : IO Unit := withCtx fun ctx clock => do
  group "admin: user remove"
  let alice ← ctx.store.addUser "alice" ["admin"] 1 (email := some "alice@example.org")
  let bob ← ctx.store.addUser "bob" [] 1
  let (secret, _) ← addClients ctx
  let (cookie, k) ← sessionFor ctx alice
  let bobCookie ← signedIn ctx bob
  discard <| giveTotp ctx alice
  ctx.store.setRecoveryCodes alice.id .empty [ByteArray.mk #[1]]
  ctx.store.setPassword alice.id "phc" 1
  let rt := (jsonStr (← exchange ctx (← obtainCode ctx cookie) secret) "refresh_token").getD ""
  discard <| obtainCode ctx cookie
  let some r ← Admin.removeUser ctx.store alice (← clock.get) | check "alice is removed" false
  checkEq "ending her session and family first" (r.sessions, r.families) (1, 1)
  checkEq "she is gone" ((← ctx.store.findUserByName "alice").map (·.name)) none
  let count (table : String) : IO Nat := do
    let n ← ctx.store.run fun c => Store.queryOne c
      s!"SELECT COUNT(*) FROM {table} WHERE user_id = ?" #[alice.id] (Store.colNat · 0)
    return n.getD 0
  for table in ["webauthn_credentials", "totp_apps", "recovery_codes", "passwords", "sessions",
      "refresh_tokens", "codes", "challenges", "totp_lock", "device_codes"] do
    checkEq s!"nothing of hers is left in {table}" (← count table) 0
  checkEq "her refresh token is refused" (jsonStr (← refreshAs ctx rt "app" secret) "error")
    (some "invalid_grant")
  checkEq "her passkey signs nobody in" (← signInVia ctx k).status.toCode 401
  check "bob is untouched" (← Session.current ctx (withCookie bobCookie)).isSome
  check "the removal is audited with her name and address"
    ((← Audit.entries ctx.store).any fun e => e.event == "user-removed" &&
      e.userName == some "alice" && containsStr e.detail "email: alice@example.org")
  check "and the chain verifies" ((← Audit.verify ctx.store) matches .ok _)
  let again ← ctx.store.addUser "alice" [] 2 (email := some "alice@example.org")
  checkEq "the name and address can be given again, to an account with nothing"
    ((← ctx.store.listCredentials again.id).size, (← ctx.store.listTotpApps again.id).size)
    (0, 0)
  checkEq "removing someone who is not there" (← Admin.removeUser ctx.store alice 3).isSome false

/-- Every test of this module. -/
def hardeningTests : IO Unit := do
  rotationTests
  crashTests
  rootKeyMigrationTests
  invitationHandleTests
  revokeTests
  disableTests
  userRemoveTests

end PyleTests
