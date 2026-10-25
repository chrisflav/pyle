import LeanBiscuit.Crypto.Hash

/-!
# HKDF-SHA256

HKDF (RFC 5869) derives independent keys from the root key, one per purpose,
so that the key sealing TOTP secrets is not the key that MACs recovery codes.
It is written in Lean over `lean-crypto-hash`'s HMAC-SHA256: deriving is a
fixed sequence of HMAC computations whose timing depends only on the lengths
involved.
-/

namespace Pyle
namespace Crypto

/-- The most output HKDF-SHA256 can produce: 255 blocks of 32 bytes. -/
def hkdfSha256MaxLength : Nat := 255 * 32

/-- HKDF-Extract: a pseudorandom key from input keying material and a salt.  An
empty salt stands for 32 zero bytes, as RFC 5869 §2.2 says. -/
def hkdfSha256Extract (salt ikm : ByteArray) : ByteArray :=
  let salt := if salt.isEmpty then ⟨Array.replicate 32 0⟩ else salt
  LeanBiscuit.Hmac.sha256 salt ikm

/-- HKDF-Expand: `T(1) ‖ T(2) ‖ …` truncated to `length` bytes, where
`T(i) = HMAC(prk, T(i-1) ‖ info ‖ i)` and `T(0)` is empty.  At most
`hkdfSha256MaxLength` bytes are produced: the block counter is a single byte. -/
def hkdfSha256Expand (prk info : ByteArray) (length : Nat) : ByteArray :=
  let length := min length hkdfSha256MaxLength
  let blocks := (length + 31) / 32
  let rec go (i : Nat) (fuel : Nat) (prev acc : ByteArray) : ByteArray :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      let t := LeanBiscuit.Hmac.sha256 prk (prev ++ info ++ ⟨#[UInt8.ofNat i]⟩)
      go (i + 1) fuel t (acc ++ t)
  (go 1 blocks .empty .empty).extract 0 length

/-- HKDF with SHA-256 (RFC 5869): extract a pseudorandom key from `ikm` and
`salt`, then expand it with `info` to `length` bytes, capped at
`hkdfSha256MaxLength`. -/
def hkdfSha256 (ikm salt info : ByteArray) (length : Nat) : ByteArray :=
  hkdfSha256Expand (hkdfSha256Extract salt ikm) info length

end Crypto
end Pyle