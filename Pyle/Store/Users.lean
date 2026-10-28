import Pyle.Store.Schema
import Pyle.Crypto.Ffi
import Pyle.Session.Acr

/-!
# Users and their authenticators

The accounts, and what each one signs in with: WebAuthn credentials,
authenticator apps (TOTP) and recovery codes (DESIGN.md §1, §3).

The store keeps what the ceremonies need and checks nothing about it: whether
an assertion is good is `Pyle.WebAuthn`'s question, and this module only
remembers the answer.  The one exception is the consume-once operations — a
recovery code is spent, and an app's TOTP step is used, by a single conditional
`UPDATE`, so two requests racing with the same code cannot both succeed.
-/

namespace Pyle
namespace Store

/-- A row id in `users`. -/
structure UserId where
  /-- The integer key. -/
  val : Int
  deriving DecidableEq, Repr, Inhabited, Hashable

instance : ToString UserId := ⟨fun u => toString u.val⟩
instance : Coe UserId Value := ⟨fun u => .int u.val⟩

/-- An account. -/
structure User where
  /-- The row id. -/
  id : UserId
  /-- The WebAuthn user handle: 32 random bytes, fixed for the account's life. -/
  handle : ByteArray
  /-- The name people and services know the account by. -/
  name : String
  /-- Groups, for services that authorize by them (`Remote-Groups`, §5.3). -/
  groups : List String
  /-- When it was created. -/
  created : Nat
  /-- A disabled account cannot sign in, and its sessions are not honoured. -/
  disabled : Bool
  /-- Its email address (migration 8), set by an administrator and never by
  the user: what the `email` claim says. -/
  email : Option String := none
  /-- What the `name` claim says in place of `name`, if set (migration 8). -/
  displayName : Option String := none

/-- The columns of `users`, in the order `readUser` reads them. -/
def userColumns : String :=
  "id, handle, name, groups, created, disabled, email, display_name"

/-- Read a `users` row selected with `userColumns`. -/
def readUser (stmt : SQLite.Stmt) : IO User := do
  return {
    id := ⟨← colInt stmt 0⟩
    handle := ← colBlob stmt 1
    name := ← colText stmt 2
    groups := ← colList stmt 3
    created := ← colNat stmt 4
    disabled := (← colInt stmt 5) != 0
    email := ← colOpt colText stmt 6
    displayName := ← colOpt colText stmt 7 }

/-- Whether a user name is acceptable: 1 to 64 characters from lower-case
letters, digits, `-`, `_` and `.`, starting with a letter or digit.  Names
appear in tokens, headers and datalog, and a narrow alphabet keeps every one of
those encodings trivial. -/
def validUserName (name : String) : Bool :=
  let cs := name.toList
  !cs.isEmpty && cs.length ≤ 64 &&
    cs.all (fun c => c.isLower || c.isDigit || c == '-' || c == '_' || c == '.') &&
    (cs.head?.any fun c => c.isLower || c.isDigit)

/-! ## Email addresses and display names

Both are set by an administrator, never by the user (migration 8), and both
are optional.  An address is checked only for its shape — nothing is sent to
it — and is stored as given, trimmed.  It must be printable ASCII: uniqueness
ignores case as the database's `lower` does, which folds ASCII letters only
(the unique index is over it), while services that key accounts by address
(Zulip) fold Unicode case, so a non-ASCII address could be two accounts to
pyle and one to the service.

A display name may be any text people read, but not text that hides or
reorders what is around it: control and format characters, line and paragraph
separators and non-ASCII spaces are refused (`hiddenInDisplayName`). -/

/-- Whether a character is a control character (C0, DEL or C1). -/
def isControl (c : Char) : Bool :=
  c.val < 0x20 || (0x7f ≤ c.val && c.val < 0xa0)

/-- Ranges of code points that a display name may not contain beside the
control characters: the format characters (general category Cf — soft
hyphen, zero-width characters, bidirectional controls, invisible operators,
the byte-order mark, interlinear annotations, tags…), the line and paragraph
separators, and every space but the ASCII one.  Hard-coded from Unicode 15.1,
since Lean has no table of categories. -/
def hiddenRanges : List (Nat × Nat) :=
  [(0x00a0, 0x00a0), (0x00ad, 0x00ad), (0x0600, 0x0605), (0x061c, 0x061c),
   (0x06dd, 0x06dd), (0x070f, 0x070f), (0x0890, 0x0891), (0x08e2, 0x08e2),
   (0x1680, 0x1680), (0x180e, 0x180e), (0x2000, 0x200f), (0x2028, 0x202f),
   (0x205f, 0x2064), (0x2066, 0x206f), (0x3000, 0x3000), (0xfeff, 0xfeff),
   (0xfff9, 0xfffb), (0x110bd, 0x110bd), (0x110cd, 0x110cd), (0x13430, 0x1343f),
   (0x1bca0, 0x1bca3), (0x1d173, 0x1d17a), (0xe0001, 0xe0001), (0xe0020, 0xe007f)]

/-- Whether a character may not appear in a display name: a control
character, or one of `hiddenRanges`. -/
def hiddenInDisplayName (c : Char) : Bool :=
  isControl c || hiddenRanges.any fun r => decide (r.1 ≤ c.toNat ∧ c.toNat ≤ r.2)

/-- Whether a character is printable ASCII other than the space: `!` to `~`. -/
def isPrintableAscii (c : Char) : Bool :=
  0x21 ≤ c.val && c.val ≤ 0x7e

/-- The longest email address accepted (RFC 5321's path limit, less the
angle brackets). -/
def maxEmailLength : Nat := 254

/-- The longest display name accepted. -/
def maxDisplayNameLength : Nat := 128

/-- An email address as it is stored, or why it is not one: trimmed, at most
`maxEmailLength` characters, printable ASCII only (`!` to `~`, so no spaces
either), exactly one `@` with a non-empty local part before it and a domain
containing a dot after it, not starting or ending with one. -/
def normalizeEmail (given : String) : Except String String :=
  let e := given.trimAscii.toString
  let fail (why : String) : Except String String :=
    .error s!"'{e}' is not an acceptable email address: {why}"
  if e.isEmpty then .error "an email address cannot be empty"
  else if e.any isControl then .error "an email address cannot contain control characters"
  else if !e.all isPrintableAscii then
    fail "email addresses must be ASCII, printable and without spaces"
  else if e.length > maxEmailLength then fail s!"longer than {maxEmailLength} characters"
  else match e.splitOn "@" with
    | [localPart, domain] =>
      if localPart.isEmpty then fail "nothing before the '@'"
      else if !domain.contains '.' || domain.startsWith "." || domain.endsWith "." then
        fail "the domain after the '@' needs a dot, inside it"
      else .ok e
    | _ => fail "it needs exactly one '@'"

/-- A display name as it is stored, or why it is not one: trimmed, 1 to
`maxDisplayNameLength` characters, none of them `hiddenInDisplayName`. -/
def normalizeDisplayName (given : String) : Except String String :=
  let n := given.trimAscii.toString
  if n.isEmpty then .error "a display name cannot be empty"
  else if n.length > maxDisplayNameLength then
    .error s!"a display name is at most {maxDisplayNameLength} characters"
  else if n.any hiddenInDisplayName then
    .error "a display name cannot contain control or invisible formatting characters, \
      line separators, or spaces other than the ASCII space"
  else .ok n

/-- `normalizeEmail` and `normalizeDisplayName` of optional values, throwing
the reason for a bad one. -/
def normalizeContact (email displayName : Option String) :
    IO (Option String × Option String) := do
  let norm (f : String → Except String String) : Option String → IO (Option String)
    | none => pure none
    | some v => match f v with
      | .ok v => pure (some v)
      | .error why => throw (.userError why)
  return (← norm normalizeEmail email, ← norm normalizeDisplayName displayName)

/-- The account other than `except` that has this email address, ignoring
the case of ASCII letters, if there is one: its name. -/
def emailOwner (c : SQLite) (email : String) (except : Option UserId := none) :
    IO (Option String) :=
  queryOne c "SELECT name FROM users WHERE email IS NOT NULL AND lower(email) = lower(?) \
    AND id IS NOT ?" #[email, Value.opt except] (colText · 0)

/-- The error for an address another account has. -/
def emailTaken (email owner : String) : IO.Error :=
  .userError s!"the email address '{email}' is already used by the account '{owner}' \
    (addresses are compared ignoring case)"

/-- Create an account with a fresh random handle, and optionally an email
address and a display name (`normalizeEmail`, `normalizeDisplayName`).  Fails
if the name is invalid or taken, or the address invalid or another account's. -/
def Store.addUser (s : Store) (name : String) (groups : List String) (now : Nat)
    (email displayName : Option String := none) : IO User := do
  unless validUserName name do
    throw (.userError s!"'{name}' is not a valid user name (lower-case letters, digits, \
      '-', '_' and '.', at most 64)")
  let (email, displayName) ← normalizeContact email displayName
  let handle ← Crypto.randomBytes 32
  s.atomically fun c => do
    if (← queryOne c "SELECT 1 FROM users WHERE name = ?" #[name] (colInt · 0)).isSome then
      throw (.userError s!"there is already a user named '{name}'")
    if let some e := email then
      if let some owner ← emailOwner c e then throw (emailTaken e owner)
    let some u ← queryOne c
        s!"INSERT INTO users (handle, name, groups, created, email, display_name) \
          VALUES (?, ?, ?, ?, ?, ?) RETURNING {userColumns}"
        #[handle, name, encodeList groups, now, Value.opt email, Value.opt displayName] readUser
      | throw (.userError "store: the new user was not returned")
    return u

/-- Change an account's email address and display name together: for each,
`none` leaves it, `some none` clears it and `some (some v)` sets it.  Both new
values are checked (`normalizeEmail`, `normalizeDisplayName`, the address not
another account's) before either is written, and both are written in one
transaction, so a bad one changes nothing.  The account before and after, or
`none` if there is no such account. -/
def Store.setUserContact (s : Store) (id : UserId)
    (email displayName : Option (Option String) := none) : IO (Option (User × User)) := do
  let (newEmail, newName) ← normalizeContact (email.getD none) (displayName.getD none)
  s.atomically fun c => do
    let some before ← queryOne c s!"SELECT {userColumns} FROM users WHERE id = ?" #[id]
        readUser
      | return none
    if email.isSome then
      if let some e := newEmail then
        if let some owner ← emailOwner c e (some id) then throw (emailTaken e owner)
      discard <| exec c "UPDATE users SET email = ? WHERE id = ?" #[Value.opt newEmail, id]
    if displayName.isSome then
      discard <| exec c "UPDATE users SET display_name = ? WHERE id = ?"
        #[Value.opt newName, id]
    let some after ← queryOne c s!"SELECT {userColumns} FROM users WHERE id = ?" #[id]
        readUser
      | throw (.userError "store: the account was not read back")
    return some (before, after)

/-- Set or clear an account's email address (`setUserContact`).  Fails if the
address is invalid or another account's.  Whether the account existed. -/
def Store.setUserEmail (s : Store) (id : UserId) (email : Option String) : IO Bool :=
  return (← s.setUserContact id (email := some email)).isSome

/-- Set or clear an account's display name (`setUserContact`).  Fails if the
name is invalid.  Whether the account existed. -/
def Store.setUserDisplayName (s : Store) (id : UserId) (displayName : Option String) :
    IO Bool :=
  return (← s.setUserContact id (displayName := some displayName)).isSome

/-- Look an account up by name. -/
def Store.findUserByName (s : Store) (name : String) : IO (Option User) := s.run fun c =>
  queryOne c s!"SELECT {userColumns} FROM users WHERE name = ?" #[name] readUser

/-- Look an account up by row id. -/
def Store.findUser (s : Store) (id : UserId) : IO (Option User) := s.run fun c =>
  queryOne c s!"SELECT {userColumns} FROM users WHERE id = ?" #[id] readUser

/-- Look an account up by its WebAuthn user handle. -/
def Store.findUserByHandle (s : Store) (handle : ByteArray) : IO (Option User) :=
  s.run fun c =>
    queryOne c s!"SELECT {userColumns} FROM users WHERE handle = ?" #[handle] readUser

/-- Every account, by name. -/
def Store.listUsers (s : Store) : IO (Array User) := s.run fun c =>
  query c s!"SELECT {userColumns} FROM users ORDER BY name" #[] readUser

/-- Disable or re-enable an account.  Disabling also ends its sessions.
Whether the account existed. -/
def Store.setUserDisabled (s : Store) (id : UserId) (disabled : Bool) : IO Bool :=
  s.atomically fun c => do
    let n ← exec c "UPDATE users SET disabled = ? WHERE id = ?"
      #[(if disabled then (1 : Nat) else 0 : Nat), id]
    if disabled then
      discard <| exec c "DELETE FROM sessions WHERE user_id = ?" #[id]
    return n > 0

/-- Replace an account's groups.  Whether the account existed. -/
def Store.setUserGroups (s : Store) (id : UserId) (groups : List String) : IO Bool :=
  s.run fun c => return (← exec c "UPDATE users SET groups = ? WHERE id = ?"
    #[encodeList groups, id]) > 0

/-! ## WebAuthn credentials -/

/-- A registered WebAuthn credential, as stored.  The public key is kept as
the COSE algorithm number and the key bytes `Pyle.WebAuthn.PublicKey` uses, so
the store does not depend on the WebAuthn modules. -/
structure Credential where
  /-- The credential id the authenticator chose. -/
  id : ByteArray
  /-- Whose it is. -/
  user : UserId
  /-- The COSE algorithm: `-7` for ES256, `-8` for EdDSA. -/
  algorithm : Int
  /-- The public key: 33-byte compressed SEC1 for ES256, 32 bytes for EdDSA. -/
  publicKey : ByteArray
  /-- The last signature counter seen. -/
  signCount : Nat
  /-- The backup-eligible flag at registration, which must never change (§2.1). -/
  backupEligible : Bool
  /-- The backup-state flag last seen. -/
  backupState : Bool
  /-- The authenticator model's AAGUID, 16 bytes (zero when not attested). -/
  aaguid : ByteArray
  /-- The transports the browser reported, as hints for the next ceremony. -/
  transports : List String
  /-- A name the user gave it. -/
  name : String
  /-- When it was registered. -/
  created : Nat
  /-- When it was last used to sign in. -/
  lastUsed : Option Nat
  /-- Whether it has verified the user (a PIN or a fingerprint), at
  registration or in any assertion since: what makes it a passkey rather than
  a security key that is only touched.  Of the credentials registered before
  migration 5, only the one an invitation created is assumed to. -/
  userVerified : Bool := false

/-- The columns of `webauthn_credentials`, in the order `readCredential` reads
them. -/
def credentialColumns : String :=
  "id, user_id, algorithm, public_key, sign_count, backup_eligible, backup_state, aaguid, \
    transports, name, created, last_used, user_verified"

/-- Read a credential row selected with `credentialColumns`. -/
def readCredential (stmt : SQLite.Stmt) : IO Credential := do
  return {
    id := ← colBlob stmt 0
    user := ⟨← colInt stmt 1⟩
    algorithm := ← colInt stmt 2
    publicKey := ← colBlob stmt 3
    signCount := ← colNat stmt 4
    backupEligible := (← colInt stmt 5) != 0
    backupState := (← colInt stmt 6) != 0
    aaguid := ← colBlob stmt 7
    transports := ← colList stmt 8
    name := ← colText stmt 9
    created := ← colNat stmt 10
    lastUsed := ← colOpt colNat stmt 11
    userVerified := (← colInt stmt 12) != 0 }

/-- A flag as an integer column. -/
private def flag (b : Bool) : Value := .int (if b then 1 else 0)

/-- Record a newly registered credential.  The id is the primary key, so a
credential id already registered to anyone is refused (§2.2) by the database
itself rather than by a check that could race. -/
def Store.addCredential (s : Store) (cred : Credential) : IO Unit := s.run fun c => do
  discard <| exec c
    "INSERT INTO webauthn_credentials (id, user_id, algorithm, public_key, sign_count, \
      backup_eligible, backup_state, aaguid, transports, name, created, user_verified) \
      VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)"
    #[cred.id, cred.user, cred.algorithm, cred.publicKey, cred.signCount,
      flag cred.backupEligible, flag cred.backupState, cred.aaguid,
      encodeList cred.transports, cred.name, cred.created, flag cred.userVerified]

/-- Look a credential up by id. -/
def Store.findCredential (s : Store) (id : ByteArray) : IO (Option Credential) :=
  s.run fun c => queryOne c
    s!"SELECT {credentialColumns} FROM webauthn_credentials WHERE id = ?" #[id] readCredential

/-- A user's credentials, oldest first. -/
def Store.listCredentials (s : Store) (user : UserId) : IO (Array Credential) :=
  s.run fun c => query c
    s!"SELECT {credentialColumns} FROM webauthn_credentials WHERE user_id = ? \
      ORDER BY created, id" #[user] readCredential

/-- Record a successful assertion: the new counter, backup state and time,
and that the credential verified the user, if it did this time.
The update only applies if the stored counter is still the one the assertion
was checked against, so two assertions racing with the same counter cannot
both be recorded.  Whether it applied. -/
def Store.recordCredentialUse (s : Store) (id : ByteArray) (expectedCount newCount : Nat)
    (backupState userVerified : Bool) (now : Nat) : IO Bool := s.run fun c => do
  let n ← exec c
    "UPDATE webauthn_credentials SET sign_count = ?, backup_state = ?, last_used = ?, \
      user_verified = MAX(user_verified, ?) WHERE id = ? AND sign_count = ?"
    #[newCount, flag backupState, now, flag userVerified, id, expectedCount]
  return n > 0

/-- Rename a credential.  Whether it belonged to that user. -/
def Store.renameCredential (s : Store) (user : UserId) (id : ByteArray) (name : String) :
    IO Bool := s.run fun c => do
  return (← exec c "UPDATE webauthn_credentials SET name = ? WHERE id = ? AND user_id = ?"
    #[name, id, user]) > 0

/-! ## A way in

An account must always be able to sign in again (§1), so a removal is checked
against what it leaves, inside the transaction that makes it: the factors
left must reach a level (`Acr.Capabilities.level`, at least `mfa`) without
counting recovery codes, and there must still be two authenticators —
WebAuthn credentials, and the account's authenticator apps counted once,
since they are one kind of factor and often on one phone.  A removal that fails either is rolled back.

Recovery codes are left out of the level here because they are the last
resort (§3): each sign-in spends one, so an account that signs in only thanks
to them is ten sign-ins from being locked out. -/

/-- The kinds of factor an account has, read on one connection: its
credentials, whether any verifies the user and whether that one is
device-bound, any authenticator app, a password if `passwords` (the
deployment allows them), and unspent recovery codes.  `Policy.capabilities`
is this. -/
def capabilitiesIn (c : SQLite) (user : UserId) (passwords : Bool) : IO Acr.Capabilities := do
  let creds ← query c
    "SELECT user_verified, backup_eligible FROM webauthn_credentials WHERE user_id = ?" #[user]
    fun st => return ((← colInt st 0) != 0, (← colInt st 1) != 0)
  let count (sql : String) : IO Nat := return (← queryOne c sql #[user] (colNat · 0)).getD 0
  let apps ← count "SELECT COUNT(*) FROM totp_apps WHERE user_id = ?"
  let password ← if passwords then count "SELECT COUNT(*) FROM passwords WHERE user_id = ?"
    else pure 0
  let recovery ← count
    "SELECT COUNT(*) FROM recovery_codes WHERE user_id = ? AND spent_at IS NULL"
  return { verifyingDeviceBound := creds.any fun (uv, be) => uv && !be,
           verifying := creds.any (·.1), webauthn := !creds.isEmpty, totp := apps > 0,
           password := password > 0, recovery := recovery > 0 }

/-- How many authenticators a user has for the two-authenticator rule of §1:
WebAuthn credentials, plus one if they have any authenticator apps. -/
def countAuthenticators (c : SQLite) (user : UserId) : IO Nat := do
  let creds ← queryOne c "SELECT COUNT(*) FROM webauthn_credentials WHERE user_id = ?"
    #[user] (colNat · 0)
  let apps ← queryOne c "SELECT COUNT(*) FROM totp_apps WHERE user_id = ?" #[user]
    (colNat · 0)
  return creds.getD 0 + min (apps.getD 0) 1

/-- How many authenticators a user has (see `countAuthenticators`). -/
def Store.authenticatorCount (s : Store) (user : UserId) : IO Nat :=
  s.run (countAuthenticators · user)

/-- What an account has, as `capabilitiesIn` reads it. -/
def Store.capabilities (s : Store) (user : UserId) (passwords : Bool) :
    IO Acr.Capabilities :=
  s.run (capabilitiesIn · user passwords)

/-- Whether what an account has left is still a way in: its factors reach a
level, and, if `requireTwo`, it has two authenticators. -/
def keepsWayIn (caps : Acr.Capabilities) (authenticators : Nat) (requireTwo : Bool) : Bool :=
  caps.level.isSome && (!requireTwo || authenticators ≥ 2)

/-- What a removal came to. -/
inductive Removal where
  /-- It was removed. -/
  | removed
  /-- There was nothing of that user's to remove. -/
  | notFound
  /-- Removing it would have left no way in, and it was kept. -/
  | wouldLockOut
  deriving DecidableEq, Repr

instance : ToString Removal := ⟨fun r => reprStr r⟩

/-- Run `delete` (which removes one factor of `user` and returns how many
rows it removed) under a savepoint, and keep the removal only if what is left
`keepsWayIn`, with recovery codes not counted; otherwise roll it back.  The caller runs this inside
`Store.atomically`, so two concurrent removals cannot both pass the check. -/
def removeKeepingWayIn (c : SQLite) (user : UserId) (passwords requireTwo : Bool)
    (delete : IO Nat) : IO Removal := do
  discard <| exec c "SAVEPOINT removal"
  let n ← delete
  let outcome ← if n == 0 then pure Removal.notFound else do
    let caps := { (← capabilitiesIn c user passwords) with recovery := false }
    if keepsWayIn caps (← countAuthenticators c user) requireTwo then pure Removal.removed
    else pure Removal.wouldLockOut
  if outcome == .wouldLockOut then discard <| exec c "ROLLBACK TO removal"
  discard <| exec c "RELEASE removal"
  return outcome

/-- Remove a credential, unless that would leave no way in (§1).  `passwords`
is whether the deployment allows them, so whether a password counts. -/
def Store.removeCredential (s : Store) (user : UserId) (id : ByteArray)
    (passwords : Bool := false) : IO Removal := s.atomically fun c =>
  removeKeepingWayIn c user passwords true <|
    exec c "DELETE FROM webauthn_credentials WHERE id = ? AND user_id = ?" #[id, user]

/-! ## TOTP

An account may have several authenticator apps, each with its own secret
(migration 6).  Each app keeps the step of the last code it accepted, so the
replay rule of §3 holds per app; the failure count and the lock of §7 are the
account's, shared by all its apps. -/

/-- One of a user's authenticator apps: its sealed secret and its replay
state. -/
structure TotpApp where
  /-- The row id, never reused. -/
  id : Int
  /-- Whose it is. -/
  user : UserId
  /-- A name the user gave it. -/
  name : String
  /-- The secret, sealed under the root key for this row (§6.3,
  `Secrets.sealTotpApp`).  The store never sees it in the clear. -/
  sealedSecret : ByteArray
  /-- The time step of the last code this app accepted (§3). -/
  lastStep : Option Nat
  /-- When it was added. -/
  created : Nat
  /-- When a code from it last signed in, if one has and that is known. -/
  lastUsed : Option Nat
  /-- Whether its secret is still sealed with the associated data of the one
  secret an account had before migration 6 (the user id alone); only that
  migration sets it. -/
  legacyAd : Bool := false

/-- The columns of `totp_apps`, in the order `readTotpApp` reads them. -/
def totpAppColumns : String :=
  "id, user_id, name, secret, last_step, created, last_used, legacy_ad"

/-- Read a `totp_apps` row selected with `totpAppColumns`. -/
def readTotpApp (st : SQLite.Stmt) : IO TotpApp := do
  return { id := ← colInt st 0, user := ⟨← colInt st 1⟩, name := ← colText st 2,
           sealedSecret := ← colBlob st 3, lastStep := ← colOpt colNat st 4,
           created := ← colNat st 5, lastUsed := ← colOpt colNat st 6,
           legacyAd := (← colInt st 7) != 0 }

/-- An account's TOTP lock (§7): consecutive failed codes, whichever app they
were meant for, and until when TOTP is locked. -/
structure TotpLock where
  /-- Consecutive failed codes. -/
  failures : Nat := 0
  /-- Until when TOTP is locked for this account. -/
  lockedUntil : Nat := 0
  deriving Repr, BEq, Inhabited

/-- The most authenticator apps an account may have.  Every app is a secret a
code is checked against, so this bounds the work one sign-in does. -/
def maxTotpApps : Nat := 5

/-- Add an authenticator app, unless the user has `maxTotpApps` already;
`none` then.  The secret is sealed by `sealFor`, which is given the new row's
id, so that the sealed secret can be bound to its row; the count, the row and
its secret are written in one transaction.  `lastStep` is the step of the
code that confirmed it, which is then used up. -/
def Store.addTotpApp (s : Store) (user : UserId) (name : String) (lastStep : Option Nat)
    (now : Nat) (sealFor : Int → IO ByteArray) : IO (Option TotpApp) := s.atomically fun c => do
  let n ← queryOne c "SELECT COUNT(*) FROM totp_apps WHERE user_id = ?" #[user] (colNat · 0)
  if n.getD 0 ≥ maxTotpApps then return none
  let some id ← queryOne c
      "INSERT INTO totp_apps (user_id, name, secret, last_step, created) \
        VALUES (?, ?, X'', ?, ?) RETURNING id"
      #[user, name, Value.opt lastStep, now] (colInt · 0)
    | throw (.userError "store: the new authenticator app was not returned")
  let sealedSecret ← sealFor id
  discard <| exec c "UPDATE totp_apps SET secret = ? WHERE id = ?" #[sealedSecret, id]
  return some { id, user, name, sealedSecret, lastStep, created := now, lastUsed := none }

/-- A user's authenticator apps, oldest first. -/
def Store.listTotpApps (s : Store) (user : UserId) : IO (Array TotpApp) := s.run fun c =>
  query c s!"SELECT {totpAppColumns} FROM totp_apps WHERE user_id = ? ORDER BY id" #[user]
    readTotpApp

/-- One of a user's authenticator apps, by id. -/
def Store.findTotpApp (s : Store) (user : UserId) (id : Int) : IO (Option TotpApp) :=
  s.run fun c => queryOne c
    s!"SELECT {totpAppColumns} FROM totp_apps WHERE id = ? AND user_id = ?" #[id, user]
    readTotpApp

/-- Rename one of a user's authenticator apps.  Whether it was theirs. -/
def Store.renameTotpApp (s : Store) (user : UserId) (id : Int) (name : String) : IO Bool :=
  s.run fun c => return (← exec c "UPDATE totp_apps SET name = ? WHERE id = ? AND user_id = ?"
    #[name, id, user]) > 0

/-- Remove one of a user's authenticator apps, under the same rule as
`removeCredential`: not if it would leave no way in. -/
def Store.removeTotpApp (s : Store) (user : UserId) (id : Int) (passwords : Bool := false) :
    IO Removal := s.atomically fun c =>
  removeKeepingWayIn c user passwords true <|
    exec c "DELETE FROM totp_apps WHERE id = ? AND user_id = ?" #[id, user]

/-- Replace the secret of an app still sealed with the old associated data by
one sealed for its row, and clear its `legacyAd` flag.  Whether it applied. -/
def Store.resealTotpApp (s : Store) (user : UserId) (id : Int) (sealedSecret : ByteArray) :
    IO Bool := s.run fun c => return (← exec c
      "UPDATE totp_apps SET secret = ?, legacy_ad = 0 \
        WHERE id = ? AND user_id = ? AND legacy_ad = 1" #[sealedSecret, id, user]) > 0

/-- An account's TOTP lock; an account that has never failed has none
recorded, which is no failures and no lock. -/
def Store.totpLock (s : Store) (user : UserId) : IO TotpLock := s.run fun c => do
  let l ← queryOne c "SELECT failures, locked_until FROM totp_lock WHERE user_id = ?" #[user]
    fun st => return ({ failures := ← colNat st 0, lockedUntil := ← colNat st 1 } : TotpLock)
  return l.getD {}

/-- Record a code accepted by app `app` for time step `step`.  Applies only if
the app is the user's, `step` is strictly later than the last step that app
accepted, and the account's TOTP is not locked, in one conditional `UPDATE`;
that is the replay rule of §3, per app, enforced where two concurrent requests
cannot both pass it.  An accepted code clears the account's failures.  Whether
it applied. -/
def Store.acceptTotpStep (s : Store) (user : UserId) (app : Int) (step now : Nat) : IO Bool :=
  s.atomically fun c => do
    let n ← exec c
      "UPDATE totp_apps SET last_step = ?, last_used = ? \
        WHERE id = ? AND user_id = ? AND (last_step IS NULL OR last_step < ?) \
        AND NOT EXISTS (SELECT 1 FROM totp_lock WHERE user_id = ? AND locked_until > ?)"
      #[step, now, app, user, step, user, now]
    if n > 0 then
      discard <| exec c "UPDATE totp_lock SET failures = 0 WHERE user_id = ?" #[user]
    return n > 0

/-- Record a failed code for an account, once for the attempt however many
apps it was checked against.  After `maxFailures` consecutive failures TOTP is
locked for `lockSeconds` and the count starts again (§7: five, fifteen
minutes).  Returns the time it is locked until, if it now is. -/
def Store.recordTotpFailure (s : Store) (user : UserId) (now : Nat)
    (maxFailures : Nat := 5) (lockSeconds : Nat := 900) : IO (Option Nat) :=
  s.atomically fun c => do
    let some failures ← queryOne c
        "INSERT INTO totp_lock (user_id, failures) VALUES (?, 1) \
          ON CONFLICT (user_id) DO UPDATE SET failures = failures + 1 RETURNING failures"
        #[user] (colNat · 0)
      | return none
    if failures ≥ maxFailures then
      discard <| exec c "UPDATE totp_lock SET failures = 0, locked_until = ? WHERE user_id = ?"
        #[now + lockSeconds, user]
      return some (now + lockSeconds)
    return none

/-! ## Recovery codes -/

/-- Replace a user's recovery codes with new digests (HMAC-SHA256 under a
server key, computed by `Pyle.Factor`). -/
def Store.setRecoveryCodes (s : Store) (user : UserId) (digests : List ByteArray) :
    IO Unit := s.atomically fun c => do
  discard <| exec c "DELETE FROM recovery_codes WHERE user_id = ?" #[user]
  for d in digests do
    discard <| exec c "INSERT INTO recovery_codes (user_id, digest) VALUES (?, ?)" #[user, d]

/-- Spend a recovery code: mark the unspent code with this digest spent, in one
conditional `UPDATE`.  Whether there was one to spend; a code is good once. -/
def Store.spendRecoveryCode (s : Store) (user : UserId) (digest : ByteArray) (now : Nat) :
    IO Bool := s.run fun c => do
  return (← exec c
    "UPDATE recovery_codes SET spent_at = ? \
      WHERE user_id = ? AND digest = ? AND spent_at IS NULL"
    #[now, user, digest]) > 0

/-- How many of a user's recovery codes are unspent. -/
def Store.unspentRecoveryCodes (s : Store) (user : UserId) : IO Nat := s.run fun c => do
  return (← queryOne c
    "SELECT COUNT(*) FROM recovery_codes WHERE user_id = ? AND spent_at IS NULL"
    #[user] (colNat · 0)).getD 0

/-- How many recovery codes a user has, spent or not: the ten of the last
set made, or none. -/
def Store.recoveryCodeCount (s : Store) (user : UserId) : IO Nat := s.run fun c => do
  return (← queryOne c "SELECT COUNT(*) FROM recovery_codes WHERE user_id = ?" #[user]
    (colNat · 0)).getD 0

end Store
end Pyle