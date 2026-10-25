/-!
# The constant-time boundary

The declarations backed by `ffi/PyleFfi.c`.  Anything that generates, signs
with, encrypts under, derives from or compares a secret goes through here; see
DESIGN.md §6.2 for why this is not written in Lean.

Most of these are raw: they take algorithm codes and DER blobs, and the typed
interfaces in `Pyle.Crypto.Keys`, `Pyle.Crypto.Aead` and `Pyle.Crypto.X509` sit
on top.  Only `randomBytes` and `ctEqual` are meant to be called directly.

Declarations that are deterministic and only read their arguments are pure
functions returning `Except`; the ones that draw randomness or can fail for
reasons outside their arguments live in `IO`.
-/

namespace Pyle
namespace Crypto

/-- `n` bytes from the operating system's random generator. -/
@[extern "pyle_random_bytes"]
opaque randomBytes (n : USize) : IO ByteArray

/-- Equality of two byte strings, in time that depends only on their lengths. -/
@[extern "pyle_ct_equal"]
opaque ctEqual (a b : @& ByteArray) : Bool

namespace Ffi

/-- A fresh private key for the algorithm with the given code, as a DER PKCS#8
`PrivateKeyInfo`. -/
@[extern "pyle_key_generate"]
opaque keyGenerate (algorithm : UInt8) : IO ByteArray

/-- The public key of a DER PKCS#8 private key: the compressed SEC1 point for
ES256, the 32 raw bytes for EdDSA, and the DER `SubjectPublicKeyInfo` for RS256.
Fails if the key is malformed or does not belong to the algorithm. -/
@[extern "pyle_key_public"]
opaque keyPublic (algorithm : UInt8) (pkcs8 : @& ByteArray) : Except String ByteArray

/-- Sign a message with a DER PKCS#8 private key: DER `SEQUENCE { r, s }` for
ES256, RFC 8032 for EdDSA, RSASSA-PKCS1-v1_5 with SHA-256 for RS256. -/
@[extern "pyle_key_sign"]
opaque keySign (algorithm : UInt8) (pkcs8 message : @& ByteArray) : IO ByteArray

/-- Whether a signature verifies as RSASSA-PKCS1-v1_5 with SHA-256 under an RSA
public key given as a DER `SubjectPublicKeyInfo` of at least 2048 bits. -/
@[extern "pyle_rs256_verify"]
opaque rs256Verify (spki message signature : @& ByteArray) : Bool

/-- The big-endian modulus and public exponent of an RSA `SubjectPublicKeyInfo`. -/
@[extern "pyle_rsa_public_numbers"]
opaque rsaPublicNumbers (spki : @& ByteArray) : Except String (ByteArray × ByteArray)

/-- ChaCha20-Poly1305 (RFC 8439) under a 32-byte key and a caller-chosen 12-byte
nonce, returning `nonce ‖ ciphertext ‖ tag`. -/
@[extern "pyle_aead_seal"]
opaque aeadSeal (key nonce ad plaintext : @& ByteArray) : Except String ByteArray

/-- The inverse of `aeadSeal`, failing unless the tag authenticates the
ciphertext and the associated data. -/
@[extern "pyle_aead_open"]
opaque aeadOpen (key ad sealed : @& ByteArray) : Except String ByteArray

/-- Argon2id (RFC 9106, version `0x13`) with the given passes, memory in KiB,
lanes and output length.  Fails if the linked OpenSSL does not provide it. -/
@[extern "pyle_argon2id"]
opaque argon2id (password salt secret ad : @& ByteArray)
    (iterations memoryKiB lanes outputLength : UInt32) : IO ByteArray

/-- X.509 path validation of a DER chain, leaf first, against DER trust
anchors, at the current time unless `atTime` is set, in which case at the Unix
time `time`. -/
@[extern "pyle_x509_verify"]
opaque x509Verify (chain roots : @& Array ByteArray) (atTime : UInt8) (time : UInt64) :
    IO (Except String Unit)

end Ffi

end Crypto
end Pyle