import Pyle.Store.Protocols
import Pyle.Crypto.Aead
import Pyle.Crypto.Hkdf
import Pyle.Oidc.Jwk

/-!
# Signing keys and their rotation

pyle signs with three keys, each rotated on its own (DESIGN.md §6.3): an ES256
key for ID tokens, an RS256 key for the clients that accept nothing else, and
an Ed25519 key that is the root of every biscuit it issues.  A key moves
through the states of `Store.KeyState`:

```
next ──rotate──▶ current ──rotate──▶ previous ──rotate──▶ retired
```

A key is published from the moment it is `next`, so that services and clients
can fetch it before anything is signed with it, and stays published while it
is `previous`, so that what it signed still verifies.  `rotate` therefore does
two things: it promotes the waiting next key, if there is one, and announces a
fresh one.  The first `rotate` after a key has been in use only announces; a
key never signs before it has been published.

**At rest.**  A key is stored sealed with ChaCha20-Poly1305 under a key derived
from the root key with HKDF-SHA256 and the info `"pyle signing-key v1"`, with
its `kid` as associated data, so a sealed key moved to another row no longer
opens.  The `kid` is the key's RFC 7638 thumbprint, a function of its public
half, and opening a key checks that the public key it yields is the one the row
records.  A new key is stored only while the root key it was sealed under is
still the database's (`Store.requireRootKeyIn`); replacing the root key
re-seals every key, retired ones too, keeping its `kid` and its key pair
(`RootKey.rotate`).

**First use.**  An algorithm with no current key gets one the first time it is
needed (`current`), recorded only if no other process recorded one first.
-/

namespace Pyle
namespace Keys

open Pyle.Crypto
open Pyle.Store

/-- What a key is for.  Each use has its own algorithm, and so its own
rotation. -/
inductive Use where
  /-- ID tokens, by default. -/
  | idTokenEs256
  /-- ID tokens for clients registered with `RS256`. -/
  | idTokenRs256
  /-- The root key of the biscuits pyle issues, and of its kleis attestations. -/
  | biscuitRoot
  deriving BEq, Repr, Inhabited

namespace Use

/-- Every use. -/
def all : List Use := [.idTokenEs256, .idTokenRs256, .biscuitRoot]

/-- The algorithm a use signs with. -/
def algorithm : Use → SigningAlgorithm
  | .idTokenEs256 => .es256
  | .idTokenRs256 => .rs256
  | .biscuitRoot => .edDsa

/-- The name `pyle keys` uses for it. -/
def name : Use → String
  | .idTokenEs256 => "es256"
  | .idTokenRs256 => "rs256"
  | .biscuitRoot => "biscuit"

/-- The use with the given `pyle keys` name. -/
def ofName? (s : String) : Option Use := all.find? (·.name == s)

/-- The use of a stored key, by its algorithm column. -/
def ofAlgorithm? (alg : String) : Option Use := all.find? (·.algorithm.joseName == alg)

end Use

/-- The HKDF info the sealing key is derived with. -/
def sealingInfo : String := "pyle signing-key v1"

/-- The key that seals signing keys at rest, derived from the root key. -/
def sealingKey (rootKey : ByteArray) : ByteArray :=
  (hkdfSha256 rootKey .empty sealingInfo.toUTF8 32).getD .empty

/-- A key's `kid`: its RFC 7638 thumbprint. -/
def kidOf (k : SigningKey) : Except String String := Oidc.Jwk.keyId k

/-- A key as a row in the given state, its private half sealed. -/
def toStored (rootKey : ByteArray) (k : SigningKey) (state : KeyState) (now : Nat) :
    IO StoredKey := do
  let kid ← IO.ofExcept (kidOf k)
  let sealedKey ← «seal» (sealingKey rootKey) kid.toUTF8 k.serialize
  return { kid, algorithm := k.algorithm.joseName, state, sealedKey, publicKey := k.publicKey,
           created := now }

/-- Open a stored key: unseal it under its `kid`, and check that it is a key of
the algorithm the row names with the public key the row records. -/
def «open» (rootKey : ByteArray) (sk : StoredKey) : Except String SigningKey := do
  let bytes ← Crypto.open (sealingKey rootKey) sk.kid.toUTF8 sk.sealedKey
  let k ← SigningKey.deserialize bytes
  if k.algorithm.joseName != sk.algorithm then throw "a stored key is not of its algorithm"
  if k.publicKey != sk.publicKey then throw "a stored key does not match its public key"
  return k

/-- The keys of a use that are published: next, current and previous. -/
def published (store : Store) (use : Use) : IO (Array StoredKey) :=
  store.keysOf use.algorithm.joseName

/-- Make sure a use has a current key, generating one if it has none. -/
def ensure (store : Store) (rootKey : ByteArray) (use : Use) (now : Nat) : IO Unit := do
  let keys ← published store use
  unless keys.any (·.state == .current) do
    let k ← SigningKey.generate use.algorithm
    discard <| store.addFirstKey (← toStored rootKey k .current now) (rootKeyId rootKey)

/-- The current key of a use and its `kid`, generating the first one if there
is none yet. -/
def current (store : Store) (rootKey : ByteArray) (use : Use) (now : Nat) :
    IO (String × SigningKey) := do
  ensure store rootKey use now
  let some sk := (← published store use).find? (·.state == .current)
    | throw (.userError s!"no current {use.name} key")
  return (sk.kid, ← IO.ofExcept (Keys.open rootKey sk))

/-- What a rotation did. -/
structure Rotation where
  /-- The key that became current, if a next key was waiting. -/
  promoted : Option String
  /-- The fresh next key now announced. -/
  announced : String

/-- Rotate a use: promote its next key, if one is waiting, to current (the
current one becomes previous, the previous one retired), then announce a fresh
next key.  A use with no current key at all gets one first. -/
def rotate (store : Store) (rootKey : ByteArray) (use : Use) (now : Nat) : IO Rotation := do
  ensure store rootKey use now
  let waiting := (← published store use).find? (·.state == .next)
  let promoted ← match waiting with
    | some n =>
      if ← store.promoteKeyOf use.algorithm.joseName n.kid then pure (some n.kid) else pure none
    | none => pure none
  let k ← SigningKey.generate use.algorithm
  let sk ← toStored rootKey k .next now
  store.addKey sk (rootKeyId rootKey)
  return { promoted, announced := sk.kid }

end Keys
end Pyle