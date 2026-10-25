import LeanBiscuit.Crypto.Hash
import Pyle.Crypto.Ffi
import Pyle.Factor.Base32

/-!
# Recovery codes

Ten single-use codes, shown once, for the day every authenticator is lost
(DESIGN.md §3).  Each is ten base32 characters, 50 bits drawn from the
operating system's generator, shown as two groups of five.

The database keeps only `digest`, an HMAC-SHA256 of the normalised code under a
server key, so a leaked database is not a list of working codes, and checking a
code is a lookup of its digest rather than a comparison against each stored
value.  Marking a code spent is the store's business: it must be a single
atomic delete of that digest.

Normalisation forgives what people do when typing a code from paper or
pasting it from a document: lower case, spaces and hyphens anywhere (including
the Unicode ones word processors substitute), and the digits 0, 1 and 8 for the
letters O, I and B they resemble.  RFC 4648's base32 alphabet has none of
those digits, so reading them as letters can never turn one valid code into
another.
-/

namespace Pyle
namespace Factor
namespace RecoveryCode

/-- How many codes a user is given. -/
def count : Nat := 10

/-- How many base32 characters a code has, separators not counted. -/
def length : Nat := 10

/-- One code from `length` random bytes.  Each byte picks a character by its
low five bits; 256 is a multiple of 32, so every character is uniform. -/
def ofRandom (bytes : ByteArray) : String :=
  let chars := bytes.toList.take length |>.map fun b => base32Char (b.toNat % 32)
  String.ofList (chars.take 5) ++ "-" ++ String.ofList (chars.drop 5)

/-- Whether a character is a separator someone might type or paste inside a
code: ASCII whitespace and hyphen-minus, the Unicode spaces (no-break, figure,
narrow no-break, the U+2000 block, ideographic), the zero-width space and
byte-order mark, and the Unicode hyphens, dashes and minus sign. -/
def isSeparator (c : Char) : Bool :=
  c.isWhitespace || c == '-' ||
    [0x00A0, 0x00AD, 0x1680, 0x200B, 0x200C, 0x200D, 0x2060, 0x202F, 0x205F, 0x2212, 0x3000,
      0xFEFF].contains c.toNat ||
    (0x2000 ≤ c.toNat && c.toNat ≤ 0x200A) || (0x2010 ≤ c.toNat && c.toNat ≤ 0x2015)

/-- A character as typed, read as the base32 character it is meant to be:
upper case, with `0`, `1` and `8` read as `O`, `I` and `B`. -/
def canonicalChar (c : Char) : Char :=
  match c.toUpper with
  | '0' => 'O'
  | '1' => 'I'
  | '8' => 'B'
  | c => c

/-- The canonical form of a code as typed: separators removed, letters in
upper case, and the digits that look like base32 letters read as them. -/
def normalize (code : String) : String :=
  String.ofList (code.toList.filter (!isSeparator ·) |>.map canonicalChar)

/-- Whether a string, once normalised, has the shape of a recovery code. -/
def wellFormed (code : String) : Bool :=
  let n := normalize code
  n.length == length && n.toList.all fun c => (base32Value c).isSome

/-- Ten fresh codes, pairwise distinct.  A collision among ten 50-bit codes is
already less likely than one in 2⁴³; drawing again when it happens makes
"distinct" a property rather than a probability. -/
def generate : IO (List String) := do
  let rec go (fuel : Nat) : IO (List String) := do
    let mut codes := []
    for _ in [0:count] do
      codes := ofRandom (← Crypto.randomBytes length.toUSize) :: codes
    if codes.eraseDups.length == count then return codes
    match fuel with
    | 0 => throw (IO.userError "recovery codes: the random generator repeats itself")
    | fuel + 1 => go fuel
  go 8

/-- The value stored for a code: HMAC-SHA256 under the server key of the
normalised code's UTF-8 bytes.  Codes that differ only in case or separators
have the same digest. -/
def digest (serverKey : ByteArray) (code : String) : ByteArray :=
  LeanBiscuit.Hmac.sha256 serverKey (normalize code).toUTF8

end RecoveryCode
end Factor
end Pyle