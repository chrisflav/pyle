/-!
# A strict JSON reader for client data

`clientDataJSON` is the browser's, but it reaches the server before any
signature over it has been checked, so whoever posts to the sign-in endpoint
chooses it.  A general JSON library is the wrong tool for that: `Lean.Json`
evaluates every number it reads, so `1e1000000000` becomes a bignum with a
billion digits before anyone has looked at whether the message is signed.

This reader does only what client data needs.  The input is an object whose
members are read as strings, booleans, or *something else*; a number is
checked for RFC 8259 syntax and never evaluated, and nested objects and arrays
are checked for syntax and skipped.  It refuses repeated keys in any object
(two readers of a message with a repeated key need not agree on what it
says), input longer than `maxSize` bytes, and nesting deeper than `maxDepth`.
Every step consumes input, and a fuel argument bounded by the input length
makes that the termination argument.
-/

namespace Pyle
namespace Encoding
namespace Json

/-- The longest input read, 4 KiB.  Real client data is a few hundred bytes. -/
def maxSize : Nat := 4096

/-- The deepest nesting followed inside the top-level object. -/
def maxDepth : Nat := 8

/-- A member's value, as far as it is read. -/
inductive Value where
  /-- A string. -/
  | str (s : String)
  /-- `true` or `false`. -/
  | bool (b : Bool)
  /-- Anything else: a number, `null`, an object or an array, all checked for
  syntax and nothing more. -/
  | other
  deriving Repr, DecidableEq

/-- Whether a character is JSON whitespace. -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Skip whitespace. -/
def skipWs : List Char → List Char
  | c :: cs => if isWs c then skipWs cs else c :: cs
  | [] => []

/-- The value of a hex digit. -/
def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Four hex digits, as after `\u`. -/
def hex4 : List Char → Except String (Nat × List Char)
  | a :: b :: c :: d :: rest =>
    match hexValue a, hexValue b, hexValue c, hexValue d with
    | some a, some b, some c, some d => .ok (((a * 16 + b) * 16 + c) * 16 + d, rest)
    | _, _, _, _ => .error "bad \\u escape"
  | _ => .error "bad \\u escape"

/-- Read the four hex digits after `\u`, and a second escape if the first is a
high surrogate, returning the character they stand for. -/
def readUnicodeEscape (cs : List Char) : Except String (Char × List Char) := do
  let (hi, rest) ← hex4 cs
  if 0xDC00 ≤ hi ∧ hi ≤ 0xDFFF then throw "lone low surrogate"
  if hi < 0xD800 ∨ 0xDBFF < hi then return (Char.ofNat hi, rest)
  let '\\' :: 'u' :: rest := rest | throw "high surrogate without a low one"
  let (lo, rest) ← hex4 rest
  if lo < 0xDC00 ∨ 0xDFFF < lo then throw "high surrogate without a low one"
  return (Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)), rest)

/-- Read a string after its opening quote, up to and including the closing
one.  Control characters must be escaped, and a surrogate must be escaped as a
high one followed by a low one.  A string is never longer than the input, so a
`fuel` of `maxSize + 1` is enough. -/
def readString (fuel : Nat) (acc : String) (cs : List Char) : Except String (String × List Char) :=
  match fuel with
  | 0 => .error "string too long"
  | fuel + 1 =>
    match cs with
    | [] => .error "unterminated string"
    | '"' :: rest => .ok (acc, rest)
    | '\\' :: e :: rest =>
      let simple : Option Char := match e with
        | '"' => some '"'
        | '\\' => some '\\'
        | '/' => some '/'
        | 'b' => some '\x08'
        | 'f' => some '\x0c'
        | 'n' => some '\n'
        | 'r' => some '\r'
        | 't' => some '\t'
        | _ => none
      match simple with
      | some c => readString fuel (acc.push c) rest
      | none =>
        if e != 'u' then .error "bad escape"
        else
          match readUnicodeEscape rest with
          | .ok (c, rest) => readString fuel (acc.push c) rest
          | .error e => .error e
    | c :: rest =>
      if c.toNat < 0x20 then .error "control character in string"
      else readString fuel (acc.push c) rest

/-- Skip one or more decimal digits. -/
def digits1 : List Char → Except String (List Char)
  | c :: cs => if c.isDigit then .ok (cs.dropWhile Char.isDigit) else .error "expected a digit"
  | [] => .error "expected a digit"

/-- Check the syntax of a number and skip it, without evaluating it:
`-? (0 | [1-9][0-9]*) (. [0-9]+)? ([eE] [+-]? [0-9]+)?`. -/
def skipNumber (cs : List Char) : Except String (List Char) := do
  let cs := match cs with
    | '-' :: rest => rest
    | _ => cs
  let cs ← match cs with
    | '0' :: rest => pure rest
    | _ => digits1 cs
  let cs ← match cs with
    | '.' :: rest => digits1 rest
    | _ => pure cs
  match cs with
  | 'e' :: rest | 'E' :: rest =>
    let rest := match rest with
      | '+' :: r | '-' :: r => r
      | _ => rest
    digits1 rest
  | _ => pure cs

/-- Expect a literal word such as `true`. -/
def literal (word : List Char) (cs : List Char) : Except String (List Char) :=
  if word.isPrefixOf cs then .ok (cs.drop word.length) else .error "bad literal"

mutual

/-- Read one value, at most `depth` levels deep.  `fuel` bounds the recursion
by the input length. -/
def readValue (fuel depth : Nat) (cs : List Char) : Except String (Value × List Char) :=
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
    match skipWs cs with
    | '"' :: rest => (readString (maxSize + 1) "" rest).map fun (s, rest) => (.str s, rest)
    | 't' :: _ => (literal "true".toList (skipWs cs)).map fun rest => (.bool true, rest)
    | 'f' :: _ => (literal "false".toList (skipWs cs)).map fun rest => (.bool false, rest)
    | 'n' :: _ => (literal "null".toList (skipWs cs)).map fun rest => (.other, rest)
    | '{' :: rest =>
      match depth with
      | 0 => .error "nested too deeply"
      | depth + 1 => (readMembers fuel depth [] true rest).map fun (_, rest) => (.other, rest)
    | '[' :: rest =>
      match depth with
      | 0 => .error "nested too deeply"
      | depth + 1 => (readItems fuel depth true rest).map fun rest => (.other, rest)
    | rest => (skipNumber rest).map fun rest => (.other, rest)

/-- Read the members of an object after its `{`, up to and including its `}`,
refusing a key seen before.  `first` says whether no member has been read. -/
def readMembers (fuel depth : Nat) (acc : List (String × Value)) (first : Bool)
    (cs : List Char) : Except String (List (String × Value) × List Char) :=
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
    match skipWs cs with
    | '}' :: rest => if first then .ok ([], rest) else .error "trailing comma"
    | '"' :: rest => do
      let (key, rest) ← readString (maxSize + 1) "" rest
      if acc.any (·.1 == key) then throw s!"repeated key {key.quote}"
      let rest ← match skipWs rest with
        | ':' :: rest => pure rest
        | _ => throw "expected ':'"
      let (value, rest) ← readValue fuel depth rest
      let acc := acc ++ [(key, value)]
      match skipWs rest with
      | ',' :: rest => readMembers fuel depth acc false rest
      | '}' :: rest => pure (acc, rest)
      | _ => throw "expected ',' or '}'"
    | _ => .error "expected a key"

/-- Read the items of an array after its `[`, up to and including its `]`. -/
def readItems (fuel depth : Nat) (first : Bool) (cs : List Char) :
    Except String (List Char) :=
  match fuel with
  | 0 => .error "out of fuel"
  | fuel + 1 =>
    match skipWs cs with
    | ']' :: rest => if first then .ok rest else .error "trailing comma"
    | _ => do
      let (_, rest) ← readValue fuel depth cs
      match skipWs rest with
      | ',' :: rest => readItems fuel depth false rest
      | ']' :: rest => pure rest
      | _ => throw "expected ',' or ']'"

end

/-- Read a JSON text that is a single object, returning its members in order.
The input must be UTF-8, at most `maxSize` bytes, with nothing but whitespace
after the object. -/
def readObject (bytes : ByteArray) : Except String (List (String × Value)) := do
  if bytes.size > maxSize then throw "longer than 4 KiB"
  let some text := String.fromUTF8? bytes | throw "not UTF-8"
  let cs := text.toList
  let fuel := 2 * cs.length + 2
  let rest ← match skipWs cs with
    | '{' :: rest => pure rest
    | _ => throw "not an object"
  let (members, rest) ← readMembers fuel maxDepth [] true rest
  if !(skipWs rest).isEmpty then throw "trailing characters"
  pure members

end Json
end Encoding
end Pyle