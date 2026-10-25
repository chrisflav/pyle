module

public import Crypto

/-!
# HMAC-SHA1

TOTP (RFC 6238) is defined over HMAC-SHA1, and every authenticator app
implements only that, so pyle needs it although SHA-1 is broken as a hash.  It
is not broken as the PRF inside HMAC, which is all TOTP asks of it.

`lean-crypto-hash` provides SHA-1 but HMAC only over SHA-2, so the few lines of
RFC 2104 are written here.  The key is the TOTP secret, but the timing of this
code reveals only lengths: every operation is a fixed sequence of hash blocks
determined by the key and message sizes.

This file is a `module` because `lean-crypto-hash` is built for the module
system; the rest of pyle imports it as an ordinary file.
-/

public section

namespace Pyle
namespace Crypto

/-- SHA-1 (FIPS 180-4), for HMAC-SHA1 only. -/
def sha1 (message : ByteArray) : ByteArray :=
  (Crypto.Hash.digest .sha1 message).toByteArray

/-- Every byte of `b` exclusive-or'd with `pad`. -/
private def xorEach (b : ByteArray) (pad : UInt8) : ByteArray :=
  ⟨b.data.map (· ^^^ pad)⟩

/-- HMAC-SHA1 (RFC 2104): `H((K ⊕ opad) ‖ H((K ⊕ ipad) ‖ m))` with SHA-1's
64-byte block, where a key longer than a block is first hashed and a shorter
one is padded with zeros. -/
def hmacSha1 (key message : ByteArray) : ByteArray :=
  let k := if key.size > 64 then sha1 key else key
  let k := k ++ ⟨Array.replicate (64 - k.size) 0⟩
  sha1 (xorEach k 0x5c ++ sha1 (xorEach k 0x36 ++ message))

end Crypto
end Pyle

end