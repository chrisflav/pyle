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

/-- Email addresses and display names: what is accepted, how it is stored,
and that two accounts cannot share an address in any case. -/
def contactTests : IO Unit := withCtx fun ctx _ => do
  group "store: email addresses and display names"
  let s := ctx.store
  let okEmail (e : String) := (normalizeEmail e).toOption
  checkEq "an address is trimmed and kept as given" (okEmail "  Ann.Lee@Example.ORG\n")
    (some "Ann.Lee@Example.ORG")
  checkEq "a plus and a subdomain are fine" (okEmail "a+zulip@mail.example.org")
    (some "a+zulip@mail.example.org")
  for (why, e) in [("empty", "   "), ("without an @", "ann.example.org"),
      ("with two @", "a@b@example.org"), ("empty before the @", "@example.org"),
      ("on a domain without a dot", "ann@localhost"),
      ("on a domain ending in a dot", "ann@example."),
      ("on a domain starting with a dot", "a@.org"), ("spaced", "ann lee@example.org"),
      ("tabbed", "ann\t@example.org"), ("with a control character", "ann\x01@example.org"),
      ("with a NUL", "ann\x00@example.org"),
      ("too long", String.ofList (List.replicate 243 'a') ++ "@example.org")] do
    check s!"an address {why} is refused" (okEmail e).isNone
  -- pyle folds ASCII case only, services fold Unicode case: two addresses
  -- distinct to pyle must not be one to them.
  for e in ["eve@exÄmple.org", "eve@exämple.org", "évé@example.org", "ann b@example.org",
      "ann@example.org​", "ｅve@example.org"] do
    check s!"a non-ASCII address ({e}) is refused as such"
      (match normalizeEmail e with
       | .error why => (why.splitOn "email addresses must be ASCII").length > 1
       | .ok _ => false)
  checkEq "every printable ASCII character but the space may appear"
    (okEmail "!#$%&'*+-/=?^_`{|}~.\"()<>[]:;,\\0Az@example.org").isSome true
  checkEq "254 characters is the most" ((okEmail (String.ofList (List.replicate 242 'a') ++
    "@example.org")).map (·.length)) (some 254)
  let okName (n : String) := (normalizeDisplayName n).toOption
  checkEq "a display name is trimmed" (okName "  Ann Lee ") (some "Ann Lee")
  checkEq "and may be any printable text" (okName "Zoë O'Brien-Łukasz 李")
    (some "Zoë O'Brien-Łukasz 李")
  check "an empty display name is refused" (okName " ").isNone
  check "one with a newline inside is refused" (okName "Ann\nLee").isNone
  check "one with a C1 control is refused" (okName "Ann\u0085Lee").isNone
  for (what, c) in [("a zero-width space", '​'), ("a zero-width joiner", '‍'),
      ("a left-to-right mark", '‎'), ("a right-to-left mark", '‏'),
      ("a right-to-left override", '‮'), ("a left-to-right embedding", '‪'),
      ("a right-to-left isolate", '⁧'), ("a pop directional isolate", '⁩'),
      ("a byte-order mark", '﻿'), ("a soft hyphen", '­'),
      ("a word joiner", '⁠'), ("an Arabic letter mark", '؜'),
      ("a line separator", ' '), ("a paragraph separator", ' '),
      ("a no-break space", ' '), ("an ogham space", ' '),
      ("an en quad", ' '), ("a hair space", ' '),
      ("a narrow no-break space", ' '), ("a medium mathematical space", ' '),
      ("an ideographic space", '　'), ("a language tag", Char.ofNat 0xe0001),
      ("a tag letter", Char.ofNat 0xe0041)] do
    check s!"one with {what} inside is refused" (okName s!"Ann{c}Lee").isNone
  check "even at either end, where trimming does not reach"
    ((okName " Ann").isNone && (okName "Ann　").isNone)
  checkEq "but not one with accents, other scripts or emoji" (okName "Ånn Lée 李 🙂 ﷺ")
    (some "Ånn Lée 李 🙂 ﷺ")
  checkEq "128 characters is the most"
    ((okName (String.ofList (List.replicate 128 'x'))).map (·.length)) (some 128)
  check "129 is too many" (okName (String.ofList (List.replicate 129 'x'))).isNone
  -- Accounts.
  let ann ← s.addUser "ann" [] 10 (email := some " Ann@Example.org ")
    (displayName := some "Ann Lee")
  checkEq "an account is created with an address and a display name"
    ((← s.findUser ann.id).map fun u => (u.email, u.displayName))
    (some (some "Ann@Example.org", some "Ann Lee"))
  let bob ← s.addUser "bob" [] 11
  checkEq "or without" ((← s.findUser bob.id).map fun u => (u.email, u.displayName))
    (some (none, none))
  check "a bad address refuses the account" (← throws (s.addUser "cy" [] 12 (email := some "cy")))
  check "and creates nothing" (← s.findUserByName "cy").isNone
  check "a bad display name too" (← throws (s.addUser "cy" [] 12 (displayName := some "")))
  let taken {α : Type} (act : IO α) : IO Bool := do
    try discard act; return false
    catch e => return ((toString e).splitOn "already used by the account 'ann'").length > 1
  check "another account cannot have the same address in another case, and is told whose"
    (← taken (s.addUser "cy" [] 12 (email := some "ann@EXAMPLE.org")))
  check "nor be given it later" (← taken (s.setUserEmail bob.id (some "ANN@example.org")))
  check "the database refuses it too, whatever path tries" (← throws (s.run fun c => exec c
    "UPDATE users SET email = 'ann@example.ORG' WHERE id = ?" #[bob.id]))
  check "an account may be given its own address again, in another case"
    (← s.setUserEmail ann.id (some "ann@example.org"))
  checkEq "and keeps it as given" ((← s.findUser ann.id).bind (·.email)) (some "ann@example.org")
  check "bob gets one of his own" (← s.setUserEmail bob.id (some "bob@example.org"))
  check "a bad one is refused" (← throws (s.setUserEmail bob.id (some "bob@")))
  checkEq "and leaves his as it was" ((← s.findUser bob.id).bind (·.email))
    (some "bob@example.org")
  check "an address is cleared" (← s.setUserEmail ann.id none)
  checkEq "and is then none" ((← s.findUser ann.id).bind (·.email)) none
  check "which frees it for another account" (← s.setUserEmail bob.id (some "ANN@example.org"))
  check "accounts without an address do not collide"
    ((← s.addUser "dee" [] 13).email.isNone && (← s.addUser "eve" [] 14).email.isNone)
  check "a display name is set" (← s.setUserDisplayName bob.id (some " Bob Ray "))
  checkEq "trimmed" ((← s.findUser bob.id).bind (·.displayName)) (some "Bob Ray")
  check "and refused when bad" (← throws (s.setUserDisplayName bob.id (some "a\x07b")))
  check "and cleared" (← s.setUserDisplayName bob.id none)
  checkEq "to none" ((← s.findUser bob.id).bind (·.displayName)) none
  check "setting them on an unknown account says so"
    (!(← s.setUserEmail ⟨999⟩ (some "x@example.org")) && !(← s.setUserDisplayName ⟨999⟩ none))
  checkEq "lookups are unaffected" ((← s.findUserByName "bob").map (·.id)) (some bob.id)
  checkEq "and the list carries them" ((← s.listUsers).toList.map (·.email))
    [none, some "ANN@example.org", none, none]
  -- Both fields in one transaction.
  match ← s.setUserContact ann.id (email := some (some "ann@example.net"))
      (displayName := some (some "Ann Lee")) with
  | some (before, after) =>
    checkEq "both are changed together, and the account before and after is given"
      ((before.email, before.displayName), (after.email, after.displayName))
      ((none, some "Ann Lee"), (some "ann@example.net", some "Ann Lee"))
    checkEq "the audit details name the old and the new address, and only what changed"
      (Audit.contactChanges before after) ["email: none -> ann@example.net"]
  | none => check "both are changed together" false
  check "a bad display name beside a good address" (← throws (s.setUserContact ann.id
    (email := some (some "ann@example.com")) (displayName := some (some "Ann‮Lee"))))
  checkEq "changes neither" ((← s.findUser ann.id).map fun u => (u.email, u.displayName))
    (some (some "ann@example.net", some "Ann Lee"))
  -- bob has ANN@example.org now.
  check "a taken address beside a good display name is refused" (← throws (s.setUserContact
    ann.id (email := some (some "ann@EXAMPLE.org")) (displayName := some none)))
  checkEq "and changes neither either" ((← s.findUser ann.id).map fun u => (u.email, u.displayName))
    (some (some "ann@example.net", some "Ann Lee"))
  checkEq "an unknown account is none" ((← s.setUserContact ⟨999⟩ (some none) none).isNone) true
  let some ann' ← s.findUser ann.id | check "ann" false
  checkEq "an address changed and a display name removed are two details"
    (Audit.contactChanges ann' { ann' with email := some "a@x.org", displayName := none })
    ["email: ann@example.net -> a@x.org", "display name: \"Ann Lee\" -> none"]
  checkEq "an address removed" (Audit.contactChanges ann' { ann' with email := none })
    ["email: ann@example.net -> none"]
  checkEq "a new account's details" (Audit.contactDetail (some "a@x.org") (some "A B"))
    "email: a@x.org; display name: \"A B\""
  checkEq "and none without" (Audit.contactDetail none none) ""

/-- Migration 8 brings a version-7 database forward: its accounts keep
everything and have no address or display name, and its invitations neither. -/
def contactMigrationTests : IO Unit := IO.FS.withTempDir fun dir => do
  group "store: migration 8"
  let s ← Store.openFile (dir / "old.db")
  let token := SecretHash.of (ByteArray.mk #[9])
  s.run fun c => do
    discard <| currentVersion c
    for m in migrations.take 7 do
      for st in m.statements do discard <| exec c st
      discard <| exec c
        "INSERT INTO schema_version (version, description, applied) VALUES (?, ?, ?)"
        #[m.version, m.description, (1 : Nat)]
    discard <| exec c
      "INSERT INTO users (handle, name, groups, created) VALUES (?, 'old', '[\"staff\"]', 5)"
      #[.blob (ByteArray.mk #[1, 2, 3])]
    discard <| exec c
      "INSERT INTO invitations (token_hash, user_name, groups, created_by, created, expires) \
        VALUES (?, 'later', '[]', 'cli', 1, 100)" #[token]
  checkEq "the database is at version 7" (← s.version) 7
  s.migrate 2
  checkEq "and is brought forward" (← s.version) schemaVersion
  let some old ← s.findUserByName "old" | check "the old account is still there" false
  checkEq "the account keeps its handle, groups and creation time"
    (old.handle.toList, old.groups, old.created) ([1, 2, 3], ["staff"], 5)
  checkEq "and has no address or display name" (old.email, old.displayName) (none, none)
  checkEq "the old invitation reads, without them"
    ((← s.findInvitation token 50).map fun i => (i.userName, i.email, i.displayName))
    (some ("later", none, none))
  check "the account can be given an address" (← s.setUserEmail old.id (some "old@example.org"))
  check "which the new index holds to"
    (← throws (s.addUser "new" [] 6 (email := some "OLD@example.org")))

/-- A credential for `user` with id `id`. -/
def sampleCredential (user : UserId) (id : ByteArray) (userVerified : Bool := true) :
    Credential :=
  { id, user, algorithm := -7, publicKey := ⟨Array.replicate 33 2⟩, signCount := 5,
    backupEligible := false, backupState := false, aaguid := ⟨Array.replicate 16 0⟩,
    transports := ["usb"], name := "key", created := 100, lastUsed := none, userVerified }

/-- Add an authenticator app whose sealed secret is `sealed`, which must fit
under the cap. -/
def addApp (s : Store) (user : UserId) (name : String) (step : Option Nat := none)
    (sealFor : Int → IO ByteArray := fun _ => pure "sealed".toUTF8) : IO TotpApp := do
  let some a ← s.addTotpApp user name step 5 sealFor
    | throw (.userError "addApp: the app was refused")
  return a

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
  checkEq "removing the second-to-last authenticator is refused"
    (← s.removeCredential alice.id id1) .wouldLockOut
  s.addCredential (sampleCredential alice.id id3)
  checkEq "another user cannot remove it" (← s.removeCredential bob.id id1) .notFound
  checkEq "with three, one may go" (← s.removeCredential alice.id id1) .removed
  checkEq "two remain" (← s.authenticatorCount alice.id) 2
  discard <| addApp s alice.id "phone"
  checkEq "an authenticator app counts" (← s.authenticatorCount alice.id) 3
  discard <| addApp s alice.id "tablet"
  checkEq "but all the apps together count once" (← s.authenticatorCount alice.id) 3

/-- A removal must leave a way in: factors that reach a level, and two
authenticators with the apps counted once. -/
def wayInTests : IO Unit := withCtx fun ctx _ => do
  group "store: a removal leaves a way in"
  let s := ctx.store
  -- A passkey and two apps: without the passkey, nothing could sign in.
  let u ← s.addUser "una" [] 1
  s.addCredential (sampleCredential u.id "pk".toUTF8)
  let a ← addApp s u.id "phone"
  let b ← addApp s u.id "tablet"
  checkEq "a passkey and two apps are two authenticators" (← s.authenticatorCount u.id) 2
  checkEq "the passkey cannot go, leaving two apps" (← s.removeCredential u.id "pk".toUTF8)
    .wouldLockOut
  check "and is still there" ((← s.findCredential "pk".toUTF8).isSome)
  checkEq "nor the apps, which are one authenticator" (← s.removeTotpApp u.id a.id) .removed
  checkEq "the last app cannot go then" (← s.removeTotpApp u.id b.id) .wouldLockOut
  -- Two touch-only keys alone cannot sign in.
  let v ← s.addUser "vera" [] 1
  s.addCredential (sampleCredential v.id "uv".toUTF8)
  s.addCredential (sampleCredential v.id "t1".toUTF8 (userVerified := false))
  s.addCredential (sampleCredential v.id "t2".toUTF8 (userVerified := false))
  checkEq "the key that verifies cannot go, leaving two touch-only keys"
    (← s.removeCredential v.id "uv".toUTF8) .wouldLockOut
  checkEq "a touch-only one can" (← s.removeCredential v.id "t1".toUTF8) .removed
  checkEq "and the level is what it was" ((← s.capabilities v.id false).level) (some .phrh)
  -- A touch-only key and an app reach mfa.
  let w ← s.addUser "wim" [] 1
  s.addCredential (sampleCredential w.id "w1".toUTF8 (userVerified := false))
  s.addCredential (sampleCredential w.id "w2".toUTF8)
  discard <| addApp s w.id "phone"
  checkEq "the key that verifies may go when a key and an app are left"
    (← s.removeCredential w.id "w2".toUTF8) .removed
  -- The password counts only where passwords are allowed, and only for the level.
  let x ← s.addUser "xia" [] 1
  s.addCredential (sampleCredential x.id "x1".toUTF8 (userVerified := false))
  s.setPassword x.id "phc" 1
  checkEq "the password of a touch-only key's account cannot go"
    (← s.removePassword x.id) .wouldLockOut
  check "and is kept" ((← s.findPassword x.id).isSome)
  checkEq "with passwords off it is no factor, and can" (← s.removePassword x.id false) .removed
  s.setPassword x.id "phc" 1
  discard <| addApp s x.id "phone"
  checkEq "with an app beside the key, the password can go" (← s.removePassword x.id) .removed
  checkEq "and once" (← s.removePassword x.id) .notFound
  -- Recovery codes are the last resort: no removal may leave them as the
  -- only second factor, since each sign-in spends one.
  let codes := ["c1", "c2", "c3"].map (·.toUTF8)
  let r ← s.addUser "rosa" [] 1
  s.addCredential (sampleCredential r.id "r0".toUTF8)
  s.addCredential (sampleCredential r.id "r1".toUTF8 (userVerified := false))
  s.addCredential (sampleCredential r.id "r2".toUTF8 (userVerified := false))
  s.setRecoveryCodes r.id codes
  checkEq "the key that verifies cannot go, leaving touch-only keys and recovery codes"
    (← s.removeCredential r.id "r0".toUTF8) .wouldLockOut
  check "and is kept" ((← s.findCredential "r0".toUTF8).isSome)
  let q ← s.addUser "quin" [] 1
  s.addCredential (sampleCredential q.id "q1".toUTF8 (userVerified := false))
  s.addCredential (sampleCredential q.id "q2".toUTF8 (userVerified := false))
  s.setPassword q.id "phc" 1
  s.setRecoveryCodes q.id codes
  checkEq "the password cannot go, leaving touch-only keys and recovery codes"
    (← s.removePassword q.id) .wouldLockOut
  check "though the account's level still counts the codes"
    ((← s.capabilities q.id true).recovery)
  -- At most five apps.
  let y ← s.addUser "yan" [] 1
  for i in [0:maxTotpApps] do discard <| addApp s y.id s!"app {i}"
  check "a sixth app is refused"
    ((← s.addTotpApp y.id "one more" none 9 fun _ => pure .empty).isNone)
  checkEq "and not stored" (← s.listTotpApps y.id).size maxTotpApps

/-- TOTP replay and lockout, and recovery codes. -/
def storedFactorTests : IO Unit := withCtx fun ctx _ => do
  group "store: totp and recovery codes"
  let s := ctx.store
  let u ← s.addUser "alice" [] 1
  let a ← addApp s u.id "phone" (sealFor := fun id => pure s!"sealed {id}".toUTF8)
  checkEq "the sealer is given the new row's id"
    ((← s.findTotpApp u.id a.id).map (·.sealedSecret)) (some s!"sealed {a.id}".toUTF8)
  check "a first step is accepted" (← s.acceptTotpStep u.id a.id 100 3000)
  check "the same step is refused" (!(← s.acceptTotpStep u.id a.id 100 3000))
  check "an earlier step is refused" (!(← s.acceptTotpStep u.id a.id 99 3000))
  check "a later step is accepted" (← s.acceptTotpStep u.id a.id 101 3030)
  checkEq "and its time recorded as the last use"
    ((← s.findTotpApp u.id a.id).bind (·.lastUsed)) (some 3030)
  checkEq "two racing for one step: one wins"
    (← raceCount 8 (s.acceptTotpStep u.id a.id 200 6000)) 1
  -- A second app keeps its own last step.
  let b ← addApp s u.id "tablet" (some 150) (fun _ => pure "other".toUTF8)
  check "the second app's step is its own: one before the first app's last is accepted"
    (← s.acceptTotpStep u.id b.id 199 6000)
  check "and the same step for it is then refused" (!(← s.acceptTotpStep u.id b.id 199 6000))
  checkEq "the first app's last step is untouched"
    ((← s.findTotpApp u.id a.id).bind (·.lastStep)) (some 200)
  let bob ← s.addUser "bob" [] 1
  check "another user's app takes no step" (!(← s.acceptTotpStep bob.id a.id 500 6000))
  check "nor is found for them" ((← s.findTotpApp bob.id a.id).isNone)
  -- The lock is the account's.
  for _ in [0:4] do
    checkEq "a failure below the limit locks nothing" (← s.recordTotpFailure u.id 7000) none
  checkEq "the fifth failure locks for fifteen minutes" (← s.recordTotpFailure u.id 7000)
    (some 7900)
  check "a good code is refused while locked, for either app"
    (!(← s.acceptTotpStep u.id a.id 300 7100) && !(← s.acceptTotpStep u.id b.id 300 7100))
  check "and accepted after" (← s.acceptTotpStep u.id a.id 300 7900)
  checkEq "which clears the failures" (← s.totpLock u.id).failures 0
  discard <| s.recordTotpFailure u.id 8000
  discard <| s.acceptTotpStep u.id b.id 301 8000
  checkEq "an accepted code for either app clears them" (← s.totpLock u.id).failures 0
  checkEq "bob has no lock" (← s.totpLock bob.id).lockedUntil 0
  check "renaming" ((← s.renameTotpApp u.id a.id "old phone") &&
    ((← s.findTotpApp u.id a.id).map (·.name)) == some "old phone")
  check "not someone else's" (!(← s.renameTotpApp bob.id a.id "mine"))
  checkEq "two apps are one authenticator" (← s.authenticatorCount u.id) 1
  s.addCredential (sampleCredential u.id "c1".toUTF8)
  s.addCredential (sampleCredential bob.id "b1".toUTF8)
  s.addCredential (sampleCredential bob.id "b2".toUTF8)
  checkEq "an app cannot be removed by someone else" (← s.removeTotpApp bob.id a.id) .notFound
  checkEq "with a key and another app beside it, it can" (← s.removeTotpApp u.id a.id) .removed
  check "and then it is gone" ((← s.findTotpApp u.id a.id).isNone)
  checkEq "leaving the other" ((← s.listTotpApps u.id).toList.map (·.name)) ["tablet"]
  checkEq "the other cannot go now" (← s.removeTotpApp u.id b.id) .wouldLockOut
  let c ← addApp s u.id "new"
  check "ids are not reused" (c.id > b.id)
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
  let inv ← Crypto.randomBytes 32
  s.addInvitation (.of inv)
    { userName := "cy", groups := [], createdBy := "cli", created := 1, expires := 100,
      email := some "Cy@example.org", displayName := some "Cy Young" }
  checkEq "an invitation carries an address and a display name"
    ((← s.consumeInvitation (.of inv) 50).map fun i => (i.email, i.displayName))
    (some (some "Cy@example.org", some "Cy Young"))
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

/-- Redeeming an invitation gives the account the invitation's address and
display name, unless another account has taken the address since. -/
def invitationContactTests : IO Unit := withCtx fun ctx _ => do
  group "store: invitations with an address"
  let s := ctx.store
  let invite (name : String) (email : Option String) : IO SecretHash := do
    let t := SecretHash.of (← Crypto.randomBytes 32)
    s.addInvitation t { userName := name, groups := ["staff"], createdBy := "cli", created := 1,
                        expires := 100, email, displayName := email.map fun _ => "Fay Wray" }
    return t
  let redeem (t : SecretHash) : IO (Except String User) := do
    let handle ← Crypto.randomBytes 32
    let id ← Crypto.randomBytes 16
    s.redeemInvitation t handle (sampleCredential · id) 50
  match ← redeem (← invite "fay" (some "Fay@example.org")) with
  | .ok u =>
    checkEq "the account gets the invitation's address and display name"
      ((← s.findUser u.id).map fun u => (u.email, u.displayName, u.groups))
      (some (some "Fay@example.org", some "Fay Wray", ["staff"]))
  | .error e => check "an invitation with an address is redeemed" false e
  match ← redeem (← invite "gus" none) with
  | .ok u => checkEq "one without gives none" (u.email, u.displayName) (none, none)
  | .error e => check "an invitation without an address is redeemed" false e
  let late ← invite "hal" (some "hal@example.org")
  discard <| s.addUser "ian" [] 2 (email := some "HAL@example.org")
  checkEq "an address taken since the invitation stops its redemption"
    (← redeem late).toOption.isNone true
  check "which creates nothing" (← s.findUserByName "hal").isNone
  check "and leaves the invitation" (← s.findInvitation late 50).isSome

/-- The store. -/
def storeTests : IO Unit := do
  configTests
  schemaTests
  userTests
  contactTests
  contactMigrationTests
  invitationContactTests
  credentialTests
  wayInTests
  storedFactorTests
  challengeTests
  oidcTests
  deviceTests

end PyleTests