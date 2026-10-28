import Pyle.Store.Schema
import Pyle.Crypto.Hkdf

/-!
# Which root key the database is sealed under

Migration 9's `root_key` table records the fingerprint of the root key that
everything sealed in the database is sealed under (`rootKeyId`, an HKDF
output of the key with its own `info`, so it says nothing about the key or
about any key derived from it for a purpose).  The store never sees the key
itself.

Every write that stores something sealed under the root key, or keyed by it —
a signing key, an authenticator app's secret, recovery-code digests — takes
the fingerprint of the key it used and checks it against the recorded one in
its own transaction (`requireRootKeyIn`).  `pyle root-key rotate` changes the
recorded fingerprint in the transaction that re-seals everything, which holds
SQLite's write lock throughout; so a write sealed under the old key either
commits before the rotation, and is re-sealed by it, or fails after it,
instead of storing something nothing can open any more.
-/

namespace Pyle
namespace Store

/-- The fingerprint of a root key: 32 bytes of HKDF-SHA256 under its own
`info`, which is not one of the keys derived for a purpose. -/
def rootKeyId (rootKey : ByteArray) : ByteArray :=
  (Crypto.hkdfSha256 rootKey .empty "pyle root-key fingerprint v1".toUTF8 32).getD .empty

/-- The fingerprint recorded in the database, if one is. -/
def recordedRootKeyIn (c : SQLite) : IO (Option ByteArray) :=
  queryOne c "SELECT fingerprint FROM root_key WHERE id = 1" #[] (colBlob · 0)

/-- What a write sealed under a replaced root key fails with. -/
def rootKeyReplaced : IO.Error :=
  .userError "the root key was replaced while this request was in progress; try again"

/-- Refuse, inside a transaction, a write made with a root key other than the
recorded one.  A database with no fingerprint recorded yet accepts any; every
process that holds the key records it before it uses it. -/
def requireRootKeyIn (c : SQLite) (keyId : ByteArray) : IO Unit := do
  if let some fp ← recordedRootKeyIn c then
    unless fp == keyId do throw rootKeyReplaced

/-- The recorded fingerprint, if one is. -/
def Store.recordedRootKey (s : Store) : IO (Option ByteArray) := s.run recordedRootKeyIn

/-- Record a fingerprint if none is recorded yet; the one recorded afterwards,
which is another process's if it recorded one first. -/
def Store.recordRootKey (s : Store) (keyId : ByteArray) (now : Nat) : IO ByteArray :=
  s.atomically fun c => do
    discard <| exec c
      "INSERT OR IGNORE INTO root_key (id, fingerprint, recorded) VALUES (1, ?, ?)" #[keyId, now]
    let some fp ← recordedRootKeyIn c | throw (.userError "store: no root key recorded")
    return fp

/-- Replace the recorded fingerprint, inside the transaction that re-seals
everything under the new key. -/
def replaceRootKeyIn (c : SQLite) (keyId : ByteArray) (now : Nat) : IO Unit := do
  discard <| exec c
    "INSERT INTO root_key (id, fingerprint, recorded) VALUES (1, ?, ?) \
      ON CONFLICT (id) DO UPDATE SET fingerprint = excluded.fingerprint, \
        recorded = excluded.recorded" #[keyId, now]

end Store
end Pyle
