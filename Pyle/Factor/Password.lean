import LeanBiscuit.Util.Base64
import Pyle.Crypto.Ffi

/-!
# Passwords

Optional, and off unless an operator enables them (DESIGN.md §3).  When they
are on, a password is stored as an Argon2id hash in the PHC string format,

```
$argon2id$v=19$m=65536,t=3,p=4$<salt>$<hash>
```

with the parameters of RFC 9106 §4's second recommended option — three passes
over 64 MiB in four lanes, a 128-bit salt and a 256-bit tag — for machines that
cannot spare the 2 GiB of the first.  Salt and hash are base64 without padding,
as the PHC format prescribes.

`verify` recomputes the hash with the parameters stored in the string, so a
later change of `recommended` does not lock anyone out, and compares the result
with the constant-time primitive.  It refuses parameters outside `Params.sane`
(at most 256 MiB, eight passes and eight lanes), so a tampered database row
cannot make one verification allocate gigabytes.

A password is hashed as the UTF-8 bytes it arrives as, without the RFC 8265
normalisation, so the same password typed with differently composed accents
would not match.  That is acceptable here because passwords are an optional
factor next to passkeys, and a user who cannot sign in with one still has
their authenticators and recovery codes.

Checking a new password against a breached-password list is the caller's
business, at the time it is set.

Argon2id itself is OpenSSL's (3.2 and later).  If the linked library lacks it,
both `hash` and `verify` raise an IO error rather than pretending a password is
wrong.
-/

namespace Pyle
namespace Factor
namespace Password

/-- Argon2id cost parameters. -/
structure Params where
  /-- Passes over memory, `t`. -/
  iterations : Nat
  /-- Memory in KiB, `m`. -/
  memoryKiB : Nat
  /-- Lanes, `p`. -/
  lanes : Nat
  deriving DecidableEq, Repr

/-- RFC 9106 §4, second recommended option: `t = 3`, `m = 2¹⁶` KiB, `p = 4`. -/
def recommended : Params := ⟨3, 65536, 4⟩

/-- Salt length in bytes: 128 bits, as RFC 9106 §4 recommends. -/
def saltLength : Nat := 16

/-- Tag length in bytes: 256 bits, as RFC 9106 §4 recommends. -/
def tagLength : Nat := 32

/-- Whether stored parameters are within the bounds `verify` is willing to
compute with: at most 8 passes, 2¹⁸ KiB (256 MiB) and 8 lanes, and at least
the 8 KiB per lane Argon2 needs.  `recommended` is well inside them. -/
def Params.sane (p : Params) : Bool :=
  1 ≤ p.iterations && p.iterations ≤ 8 && 1 ≤ p.lanes && p.lanes ≤ 8 &&
    8 * p.lanes ≤ p.memoryKiB && p.memoryKiB ≤ 2 ^ 18

/-- The recommended parameters are among the sane ones. -/
theorem recommended_sane : recommended.sane = true := by decide

/-- Standard base64 without padding, as the PHC string format uses it. -/
def b64Encode (b : ByteArray) : String :=
  String.ofList <| (LeanBiscuit.Base64.encode b).toList.filterMap fun
    | '=' => none
    | '-' => some '+'
    | '_' => some '/'
    | c => some c

/-- The inverse of `b64Encode`.  Padding and the URL-safe characters are
rejected, so that each byte string has exactly one accepted encoding. -/
def b64Decode (s : String) : Option ByteArray := do
  let chars ← s.toList.mapM fun
    | '=' | '-' | '_' => none
    | '+' => some '-'
    | '/' => some '_'
    | c => some c
  LeanBiscuit.Base64.decode? (String.ofList chars)

/-- Argon2id of a password under a salt with the given parameters, giving
`length` bytes. -/
def argon2id (password salt : ByteArray) (p : Params) (length : Nat) : IO ByteArray :=
  Crypto.Ffi.argon2id password salt .empty .empty (UInt32.ofNat p.iterations)
    (UInt32.ofNat p.memoryKiB) (UInt32.ofNat p.lanes) (UInt32.ofNat length)

/-- The PHC string for an Argon2id hash. -/
def format (p : Params) (salt hash : ByteArray) : String :=
  s!"$argon2id$v=19$m={p.memoryKiB},t={p.iterations},p={p.lanes}" ++
    s!"${b64Encode salt}${b64Encode hash}"

/-- A decimal number without sign or leading zeros. -/
def parseNat? (s : String) : Option Nat :=
  if s.isEmpty || (s.length > 1 && s.front == '0') || s.length > 10 then none
  else s.toNat?

/-- Read a PHC string written by `format`: only Argon2id version 19, the
parameters in the order `m,t,p`, salts of 8 to 64 bytes and hashes of 16 to 64
bytes are accepted. -/
def parse? (phc : String) : Option (Params × ByteArray × ByteArray) := do
  let ["", "argon2id", "v=19", params, salt, hash] := phc.splitOn "$" | none
  let [m, t, p] := params.splitOn "," | none
  let m ← parseNat? (← m.dropPrefix? "m=").toString
  let t ← parseNat? (← t.dropPrefix? "t=").toString
  let p ← parseNat? (← p.dropPrefix? "p=").toString
  let salt ← b64Decode salt
  let hash ← b64Decode hash
  if salt.size < 8 || salt.size > 64 || hash.size < 16 || hash.size > 64 then none
  pure (⟨t, m, p⟩, salt, hash)

/-- Hash a new password with the recommended parameters and a fresh salt,
giving the PHC string to store. -/
def hash (password : String) : IO String := do
  let salt ← Crypto.randomBytes saltLength.toUSize
  let tag ← argon2id password.toUTF8 salt recommended tagLength
  pure (format recommended salt tag)

/-- Whether a password matches a stored PHC string.  A string that does not
parse, or whose parameters are not `sane`, matches nothing. -/
def verify (phc password : String) : IO Bool := do
  let some (params, salt, expected) := parse? phc | pure false
  if !params.sane then return false
  let tag ← argon2id password.toUTF8 salt params expected.size
  pure (Crypto.ctEqual tag expected)

end Password
end Factor
end Pyle