/-!
# Base32

The encoding of RFC 4648 §6, which `otpauth://` URIs use for TOTP secrets and
pyle uses for recovery codes: its alphabet has no characters that are easily
confused with each other in either case, and it survives being read aloud or
typed from paper.

The encoder pads to a multiple of eight characters, as RFC 4648 says; the
decoder accepts input with or without that padding and in either case, since
that is what people and authenticator apps produce.  It rejects everything
else, including non-zero bits after the last whole byte, so every byte string
has exactly one unpadded upper-case encoding that decodes to it.
-/

namespace Pyle
namespace Factor

/-- The RFC 4648 base32 alphabet. -/
def base32Alphabet : String := "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"

/-- The base32 character for a 5-bit value. -/
def base32Char (n : Nat) : Char := base32Alphabet.toList.getD n 'A'

/-- The 5-bit value of a base32 character, accepting lower case. -/
def base32Value (c : Char) : Option Nat :=
  if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat)
  else if '2' ≤ c && c ≤ '7' then some (c.toNat - '2'.toNat + 26)
  else none

/-- Base32 encoding (RFC 4648 §6), padded with `=` to a multiple of eight
characters. -/
def base32Encode (b : ByteArray) : String :=
  -- `acc` holds the `bits` low bits not yet written out.
  let step := fun ((out, acc, bits) : String × Nat × Nat) (byte : UInt8) =>
    let acc := acc * 256 + byte.toNat
    let bits := bits + 8
    let rec emit (out : String) (acc bits : Nat) (fuel : Nat) : String × Nat × Nat :=
      match fuel with
      | 0 => (out, acc, bits)
      | fuel + 1 =>
        if bits ≥ 5 then
          emit (out.push (base32Char (acc / 2 ^ (bits - 5)))) (acc % 2 ^ (bits - 5)) (bits - 5) fuel
        else (out, acc, bits)
    emit out acc bits 2
  let (out, acc, bits) := b.foldl step ("", 0, 0)
  let out := if bits > 0 then out.push (base32Char (acc * 2 ^ (5 - bits))) else out
  out.pushn '=' ((8 - out.length % 8) % 8)

/-- Base32 decoding (RFC 4648 §6).  Padding is optional but may only appear at
the end; upper and lower case are both accepted; anything else, a length no
encoding has, or non-zero trailing bits make it fail. -/
def base32Decode (s : String) : Option ByteArray := do
  let chars := s.toList
  let body := chars.reverse.dropWhile (· == '=') |>.reverse
  let padding := chars.length - body.length
  if padding > 0 && chars.length % 8 != 0 then none
  if body.length % 8 ∉ [0, 2, 4, 5, 7] then none
  let (out, acc, bits) ← body.foldlM (init := (ByteArray.empty, 0, 0))
    fun ((out, acc, bits) : ByteArray × Nat × Nat) c => do
      let v ← base32Value c
      let acc := acc * 32 + v
      let bits := bits + 5
      if bits ≥ 8 then
        pure (out.push (UInt8.ofNat (acc / 2 ^ (bits - 8))), acc % 2 ^ (bits - 8), bits - 8)
      else pure (out, acc, bits)
  if bits ≥ 5 || acc != 0 then none
  pure out

end Factor
end Pyle