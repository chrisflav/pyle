import LeanBiscuit.Crypto.P256
import Pyle.Crypto.Ffi

/-!
# Signing keys

pyle signs what it issues — ID tokens now, biscuits later — with keys that
never leave the FFI boundary in usable form: a `SigningKey` carries its private
half as an opaque DER PKCS#8 blob, and only `ffi/PyleFfi.c` ever interprets it
(DESIGN.md §6.2).  The structure derives neither `Repr` nor `ToString`, so a
key cannot end up in a log line by accident, and its constructor is private, so
the only keys that exist are ones OpenSSL has accepted for their algorithm.

Three algorithms are supported: ES256 and EdDSA because `lean-biscuit` can
verify both in Lean, and RS256 because it is the one algorithm every OpenID
Connect client is required to accept.

At rest a key is `serialize`d and then sealed with `Pyle.Crypto.seal` under the
root key (DESIGN.md §6.3); `serialize` itself does not encrypt.
-/

namespace Pyle
namespace Crypto

/-- The signature algorithms pyle signs with. -/
inductive SigningAlgorithm where
  /-- ECDSA over P-256 with SHA-256. -/
  | es256
  /-- Ed25519 (RFC 8032). -/
  | edDsa
  /-- RSASSA-PKCS1-v1_5 with SHA-256, over a key of at least 2048 bits. -/
  | rs256
  deriving DecidableEq, Repr, Inhabited

namespace SigningAlgorithm

/-- The number the FFI shim and the serialised form use for the algorithm. -/
def code : SigningAlgorithm → UInt8
  | .es256 => 0
  | .edDsa => 1
  | .rs256 => 2

/-- The algorithm with the given code, if there is one. -/
def ofCode? : UInt8 → Option SigningAlgorithm
  | 0 => some .es256
  | 1 => some .edDsa
  | 2 => some .rs256
  | _ => none

/-- The algorithm's name in JOSE (RFC 7518 §3.1, RFC 8037 §3.1). -/
def joseName : SigningAlgorithm → String
  | .es256 => "ES256"
  | .edDsa => "EdDSA"
  | .rs256 => "RS256"

/-- The algorithm with the given JOSE name, if pyle supports it.  `none` and
the HMAC algorithms are deliberately absent. -/
def ofJoseName? : String → Option SigningAlgorithm
  | "ES256" => some .es256
  | "EdDSA" => some .edDsa
  | "RS256" => some .rs256
  | _ => none

/-- Decoding a code gives back the algorithm it encodes. -/
theorem ofCode?_code (a : SigningAlgorithm) : ofCode? a.code = some a := by
  cases a <;> rfl

/-- Reading a JOSE name gives back the algorithm it names. -/
theorem ofJoseName?_joseName (a : SigningAlgorithm) : ofJoseName? a.joseName = some a := by
  cases a <;> rfl

end SigningAlgorithm

/-- A private signing key together with its algorithm and public key.  The
private half is a DER PKCS#8 `PrivateKeyInfo` that only the FFI reads. -/
structure SigningKey where
  private mk ::
  /-- The algorithm the key signs with. -/
  algorithm : SigningAlgorithm
  /-- The private key as DER PKCS#8.  This is the secret: the field is private,
  so outside this module it is reachable only through `serialize`, whose output
  is sealed for storage. -/
  private pkcs8 : ByteArray
  /-- The public key: for ES256 the 33-byte compressed SEC1 point, as
  `LeanBiscuit.P256.verify` takes it; for EdDSA the 32-byte key; for RS256 the
  DER `SubjectPublicKeyInfo`. -/
  publicKey : ByteArray

namespace SigningKey

/-- Accept a DER PKCS#8 private key for an algorithm, once OpenSSL has parsed
it, checked that it belongs to that algorithm (for ES256, that its scalar `d`
satisfies `0 < d < n`) and computed its public key. -/
def ofPkcs8 (algorithm : SigningAlgorithm) (pkcs8 : ByteArray) : Except String SigningKey := do
  let publicKey ← Ffi.keyPublic algorithm.code pkcs8
  pure ⟨algorithm, pkcs8, publicKey⟩

/-- The PKCS#8 header of an Ed25519 private key (RFC 8410 §7), to which the
32-byte seed is appended. -/
private def ed25519Pkcs8Prefix : ByteArray :=
  ⟨#[0x30, 0x2e, 0x02, 0x01, 0x00, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x04, 0x22,
    0x04, 0x20]⟩

/-- The PKCS#8 header of a P-256 private key without the optional public key
(RFC 5208 around RFC 5915), to which the 32-byte big-endian scalar is appended. -/
private def p256Pkcs8Prefix : ByteArray :=
  ⟨#[0x30, 0x41, 0x02, 0x01, 0x00, 0x30, 0x13, 0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d,
    0x02, 0x01, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07, 0x04, 0x27,
    0x30, 0x25, 0x02, 0x01, 0x01, 0x04, 0x20]⟩

/-- An EdDSA key from its 32-byte RFC 8032 seed.  For importing published test
keys; keys pyle uses come from `generate`. -/
def ofEd25519Seed (seed : ByteArray) : Except String SigningKey :=
  if seed.size != 32 then .error "an Ed25519 seed is 32 bytes"
  else ofPkcs8 .edDsa (ed25519Pkcs8Prefix ++ seed)

/-- An ES256 key from its 32-byte big-endian scalar `d`, which must satisfy
`0 < d < n` for the group order `n`.  For importing published test keys; keys
pyle uses come from `generate`.  (`ofPkcs8`, and so `deserialize`, have the FFI
check the same range.) -/
def ofP256Scalar (scalar : ByteArray) : Except String SigningKey :=
  if scalar.size != 32 then .error "a P-256 scalar is 32 bytes"
  else
    let d := LeanBiscuit.Bytes.toNatBE scalar
    if d == 0 || d ≥ LeanBiscuit.P256.n then .error "a P-256 scalar is between 0 and n"
    else ofPkcs8 .es256 (p256Pkcs8Prefix ++ scalar)

/-- A fresh key for the algorithm, generated by OpenSSL from its DRBG.  RSA
keys are 2048 bits. -/
def generate (algorithm : SigningAlgorithm) : IO SigningKey := do
  let pkcs8 ← Ffi.keyGenerate algorithm.code
  IO.ofExcept (ofPkcs8 algorithm pkcs8)

/-- Sign a message.  ES256 signatures are DER `SEQUENCE { r, s }`, which is what
`LeanBiscuit.P256.verify` and WebAuthn use; `Pyle.Oidc.Jwt` converts them to the
fixed-width `r ‖ s` of JWS.  EdDSA signatures are 64 bytes; RS256 signatures are
as long as the modulus. -/
def sign (k : SigningKey) (message : ByteArray) : IO ByteArray :=
  Ffi.keySign k.algorithm.code k.pkcs8 message

/-- The key for storage: one byte of algorithm code followed by the PKCS#8
private key.  This is secret, and is sealed under the root key before it is
written anywhere. -/
def serialize (k : SigningKey) : ByteArray :=
  ⟨#[k.algorithm.code]⟩ ++ k.pkcs8

/-- Read a key written by `serialize`, checking it as `ofPkcs8` does. -/
def deserialize (bytes : ByteArray) : Except String SigningKey :=
  if h : 0 < bytes.size then
    match SigningAlgorithm.ofCode? bytes[0] with
    | some algorithm => ofPkcs8 algorithm (bytes.extract 1 bytes.size)
    | none => .error "unknown signing algorithm"
  else .error "empty serialised key"

end SigningKey

end Crypto
end Pyle