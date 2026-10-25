import Pyle.Crypto.Ffi

/-!
# Authenticated encryption at rest

Secret columns — TOTP secrets, signing keys — are stored sealed with
ChaCha20-Poly1305 under the root key, with the row's identity as associated
data so that a sealed value copied into another row no longer opens
(DESIGN.md §6.3).  The cipher runs in OpenSSL because it handles the root key.

The nonce is 12 random bytes drawn afresh for every `seal` and stored in front
of the ciphertext.  With random nonces the usual bound applies: well under
2³² seals per key keeps the probability of a repeated nonce negligible, far
beyond anything an identity provider writes.
-/

namespace Pyle
namespace Crypto

/-- ChaCha20-Poly1305 under a caller-chosen nonce, returning
`nonce ‖ ciphertext ‖ tag`.  Reusing a nonce under the same key destroys
confidentiality and authenticity both; outside test vectors, use `seal`. -/
def sealWithNonce (key nonce ad plaintext : ByteArray) : Except String ByteArray :=
  Ffi.aeadSeal key nonce ad plaintext

/-- Encrypt and authenticate `plaintext`, binding `ad` to it, under a 32-byte
key and a fresh random nonce.  The result is `nonce ‖ ciphertext ‖ tag`, 28
bytes longer than the plaintext. -/
def «seal» (key ad plaintext : ByteArray) : IO ByteArray := do
  let nonce ← randomBytes 12
  IO.ofExcept (sealWithNonce key nonce ad plaintext)

/-- The plaintext of a value made by `seal`, if it was sealed under `key` with
the same `ad` and has not been modified. -/
def «open» (key ad sealed : ByteArray) : Except String ByteArray :=
  Ffi.aeadOpen key ad sealed

end Crypto
end Pyle