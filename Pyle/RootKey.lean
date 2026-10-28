import Pyle.Keys.Lifecycle
import Pyle.SignIn.Secrets
import Pyle.Audit
import Pyle.Sys

/-!
# The root key: reading it, and replacing it

The root key is 32 random bytes in a file of its own (`rootKeyFile`), mode
0600.  Nothing uses it directly: each purpose derives a key of its own with
HKDF (`SignIn.Secrets`, `Keys.sealingKey`, `ForwardAuth.macKey`).  What the
database holds under those keys:

| what | how | on rotation |
| --- | --- | --- |
| signing keys (`keys.sealed`, retired ones too) | sealed, `pyle signing-key v1` | re-sealed, same `kid` and key pair |
| authenticator-app secrets (`totp_apps.secret`) | sealed, `pyle totp v1` | re-sealed for their row, `legacy_ad` cleared |
| recovery codes (`recovery_codes.digest`) | HMAC, `pyle recovery-code v1` | deleted: they cannot be recomputed |

and what is keyed by it without being stored: forward-authentication
cookies (`pyle forward-auth v1`), which stop verifying, so protected hosts send
their users round the grant once more; secrets being enrolled, handed to the
browser (`pyle totp v1`), which have to be begun again; the user handles of
invitations begun before migration 9 (`pyle invitation-handle v1`); and the
padding credential ids of a named sign-in (`pyle decoy-credential v1`).

**Which key.**  The database records the fingerprint of the key it is sealed
under (`Store.rootKeyId`, migration 9).  `resolve` is how every process that
needs the key gets it: it reads `rootKeyFile` and accepts it only if it
matches; a database with nothing recorded yet — one migrated from before 9,
or a new one — records the key it is opened with, after checking that the key
opens what is sealed there.

**Rotation** (`rotate`, `pyle root-key rotate`), with `new` the path with
`.new` appended:

1. `resolve` the current key, which finishes an interrupted rotation first.
2. Draw a new key.  In one `BEGIN IMMEDIATE` transaction (synchronous `FULL`,
   so that its commit is on disk when it returns): check that the recorded
   fingerprint is the current key's; remove a stale `new` left by a rotation
   that never committed; write the new key to `new` with `O_EXCL`, mode 0600,
   and `fsync` it and its directory; re-seal every signing key and every app
   secret, opening each result under the new key before it is written; delete
   the recovery codes; record the new fingerprint and the audit entry.
3. Rename `new` over the key file, `fsync` the directory, and overwrite the
   old key's bytes through a descriptor opened before the rename.

**Crash safety.**  At every moment, one of the two files holds the key the
database records, and `resolve` finds it:

* before the commit, the database still records the old key, which is still
  the key file: `new`, if it was written, is ignored, and the next rotation
  removes it;
* after the commit and before the rename, the database records the new key,
  which is in `new` — durable, since its directory was synced before the
  commit — and not the key file: `resolve` renames `new` over the key file,
  as step 3 would have;
* after the rename, the key file is the new key.

A key file that matches neither, with no `new` that does, is refused with an
error saying so: such a pair is a backup of one with the key of another, and
running on would seal new secrets under a key nothing else can open.

**A running server** keeps the key in memory.  `Server.route` compares the
fingerprint it holds against the database's before each request, and calls
`resolve` again when they differ.  A request already under way when the
rotation commits may still hold the old key; every write that seals checks
the fingerprint in its own transaction (`Store.requireRootKeyIn`), so such a
write fails rather than store something sealed under the retired key.
-/

namespace Pyle
namespace RootKey

open Store

/-- The length of a root key, in bytes. -/
def bytes : Nat := 32

/-- Where `rotate` writes the new key before it installs it: the key file's
path with `.new` appended. -/
def newPath (path : System.FilePath) : System.FilePath := ⟨path.toString ++ ".new"⟩

/-- The directory holding a file, for `fsync`. -/
def dirOf (path : System.FilePath) : System.FilePath :=
  match path.parent with
  | some d => if d.toString.isEmpty then "." else d
  | none => "."

/-- A fingerprint as it is shown: its first eight bytes in hex. -/
def showId (keyId : ByteArray) : String := LeanBiscuit.Bytes.toHex (keyId.extract 0 8)

/-- Write a new random root key to `path`, readable only by its owner.  The
file is created by one `open` with `O_CREAT | O_EXCL | O_NOFOLLOW` and mode
0600 and written through that descriptor (`Sys.writeNewPrivate`), so it is
never readable by anyone else, is not reached through a planted symbolic link,
and an existing file is never replaced: losing the root key loses every secret
sealed under it. -/
def create (path : System.FilePath) : IO Unit := do
  if let some dir := path.parent then
    if !dir.toString.isEmpty then IO.FS.createDirAll dir
  try Sys.writeNewPrivate path.toString (← Crypto.randomBytes bytes.toUSize)
  catch e => throw (.userError s!"cannot create the root key {path} (it must not exist): {e}")

/-- Read a root key file, checking its length. -/
def load (path : System.FilePath) : IO ByteArray := do
  let key ← try IO.FS.readBinFile path
    catch e => throw (.userError s!"cannot read the root key {path}: {e}")
  unless key.size == bytes do
    throw (.userError s!"{path} is not a root key ({key.size} bytes, expected {bytes})")
  return key

/-- A root key file, if there is a readable one of the right length. -/
def tryLoad (path : System.FilePath) : IO (Option ByteArray) := do
  try return some (← load path) catch _ => return none

/-- Whether a signing key opens under a root key. -/
def opensKey (rootKey : ByteArray) (k : StoredKey) : Bool :=
  match Keys.open rootKey k with
  | .ok _ => true
  | .error _ => false

/-- Whether an authenticator app's secret opens under a root key. -/
def opensApp (rootKey : ByteArray) (a : TotpApp) : Bool :=
  match SignIn.Secrets.openTotpApp rootKey a.user a.id a.sealedSecret a.legacyAd with
  | .ok _ => true
  | .error _ => false

/-- Refuse a key under which nothing the database has sealed opens, when it
has sealed anything: it is another database's key. -/
def checkOpens (store : Store) (rootKey : ByteArray) (path : System.FilePath) : IO Unit := do
  let (keys, apps) ← store.sealedRows
  if keys.isEmpty && apps.isEmpty then return
  unless keys.any (opensKey rootKey) || apps.any (opensApp rootKey) do
    throw (.userError s!"the root key {path} opens nothing sealed in this database: it is \
      another database's key; restore the key file that belongs to this one")

/-- The error for a key file that is not the database's. -/
def mismatch (path : System.FilePath) (recorded : ByteArray) : IO.Error :=
  .userError s!"the root key {path} is not the one this database is sealed under \
    (fingerprint {showId recorded}), and neither is {newPath path}; refusing to start.  \
    Restore the key file that belongs to this database (from the backup made with it), \
    or the database that belongs to this key"

/-- The root key the database is sealed under, from the key file — or from
`newPath`, finishing a rotation that committed but did not install its key.
Records the key's fingerprint in a database that has none.  Throws, saying
why, when neither file is the database's key. -/
def resolve (store : Store) (path : System.FilePath) (now : Nat) : IO ByteArray := do
  let next := newPath path
  match ← store.recordedRootKey with
  | none =>
    let key ← load path
    checkOpens store key path
    let fp ← store.recordRootKey (rootKeyId key) now
    unless fp == rootKeyId key do throw (mismatch path fp)
    return key
  | some fp =>
    let current ← tryLoad path
    if let some k := current then
      if rootKeyId k == fp then return k
    let some pending ← tryLoad next | throw (mismatch path fp)
    unless rootKeyId pending == fp do throw (mismatch path fp)
    -- A rotation committed and stopped before installing its key: finish it.
    discard <| Sys.installFile next.toString path.toString (current.getD .empty)
    let installed ← load path
    unless rootKeyId installed == fp do throw (mismatch path fp)
    IO.eprintln s!"pyle: finished an interrupted root-key rotation: {next} is now {path}"
    return installed

/-- What `rotate` did. -/
structure Rotation where
  /-- The fingerprint of the key replaced. -/
  oldId : ByteArray
  /-- The fingerprint of the new key. -/
  newId : ByteArray
  /-- What was re-sealed and what deleted. -/
  resealed : Resealed

/-- Re-seal a signing key under `new`, checking that the result opens. -/
def resealKey (old new : ByteArray) (k : StoredKey) : IO ByteArray := do
  let sk ← match Keys.open old k with
    | .ok sk => pure sk
    | .error e => throw (.userError s!"the signing key {k.kid} does not open under the \
        current root key ({e}); nothing was changed")
  let sealedKey ← Crypto.«seal» (Keys.sealingKey new) k.kid.toUTF8 sk.serialize
  match Keys.open new { k with sealedKey } with
  | .ok again =>
    unless again.serialize == sk.serialize do
      throw (.userError s!"the signing key {k.kid} did not re-seal; nothing was changed")
    return sealedKey
  | .error e =>
    throw (.userError s!"the signing key {k.kid} did not re-seal ({e}); nothing was changed")

/-- Re-seal an authenticator app's secret under `new` for its row, checking
that the result opens. -/
def resealApp (old new : ByteArray) (a : TotpApp) : IO ByteArray := do
  let secret ← match SignIn.Secrets.openTotpApp old a.user a.id a.sealedSecret a.legacyAd with
    | .ok s => pure s
    | .error e => throw (.userError s!"authenticator app {a.id} of account {a.user} does not \
        open under the current root key ({e}); remove it and run the rotation again")
  let sealedSecret ← SignIn.Secrets.sealTotpApp new a.user a.id secret
  match SignIn.Secrets.openTotpApp new a.user a.id sealedSecret with
  | .ok again =>
    unless again == secret do
      throw (.userError s!"authenticator app {a.id} did not re-seal; nothing was changed")
    return sealedSecret
  | .error e =>
    throw (.userError s!"authenticator app {a.id} did not re-seal ({e}); nothing was changed")

/-- The audit entry of a rotation. -/
def auditRecord (oldId newId : ByteArray) (r : Resealed) : Audit.Record :=
  { event := .rootKeyRotated, outcome := .success, clientAddress := "cli",
    detail := s!"root key {showId oldId} replaced by {showId newId}: {r.keys} signing keys \
      and {r.totpApps} authenticator apps re-sealed, {r.recoveryCodes} recovery codes of \
      {r.recoveryAccounts} accounts deleted" }

/-- Where a test stops `rotate`, as a crash could. -/
inductive Interruption where
  /-- After the new key is written to `newPath`, before the transaction
  commits, which then rolls back. -/
  | afterNew
  /-- After the commit, before the new key is installed. -/
  | afterCommit
  deriving BEq, Repr

/-- Remove `path` if it holds exactly `key`. -/
def removeIfHolds (path : System.FilePath) (key : ByteArray) : IO Unit := do
  if (← tryLoad path) == some key then
    try IO.FS.removeFile path catch _ => pure ()

/-- Replace the root key of the database `store` and of the key file `path`
(see the module documentation for the steps and why each crash leaves a
working pair).  `interrupt` is for tests, to stop where a crash could. -/
def rotate (store : Store) (path : System.FilePath) (now : Nat)
    (interrupt : Option Interruption := none) : IO Rotation := do
  let old ← resolve store path now
  let new ← Crypto.randomBytes bytes.toUSize
  let oldId := rootKeyId old
  let newId := rootKeyId new
  let next := newPath path
  let unfinished : IO.Error := .userError s!"the new root key was committed but {path} does \
    not hold it yet; run `pyle root-key check` to install it from {next}"
  store.run fun c => c.exec "PRAGMA synchronous = FULL"
  try
    let resealed ← try
        store.resealRootKey oldId newId now
          (prepare := do
            if ← next.pathExists then IO.FS.removeFile next
            Sys.writeNewPrivate next.toString new
            Sys.fsyncDir (dirOf next).toString
            if interrupt == some .afterNew then
              throw (.userError "interrupted after writing the new key"))
          (resealKey old new) (resealApp old new)
          (fun c r => discard <| Audit.appendIn c now (auditRecord oldId newId r))
      catch e =>
        -- Committed after all (an error past the commit): the new key is the
        -- database's now, and `resolve` installs it.
        if (← store.recordedRootKey) == some newId then throw unfinished
        -- Rolled back: the new key sealed nothing and is of no use.  A test's
        -- interruption leaves it, as a crash would.
        if interrupt != some .afterNew then removeIfHolds next new
        throw e
    if interrupt == some .afterCommit then
      throw (.userError "interrupted after the commit")
    discard <| Sys.installFile next.toString path.toString old
    unless (← tryLoad path).map rootKeyId == some newId do throw unfinished
    return { oldId, newId, resealed }
  finally
    store.run fun c => c.exec "PRAGMA synchronous = NORMAL"

end RootKey
end Pyle
