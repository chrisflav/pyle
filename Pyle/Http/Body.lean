import Pyle.Http.Message

/-!
# Request bodies and query strings

Two body formats are accepted, and only when the request says which it is:
`application/json` for the API, and `application/x-www-form-urlencoded` for
plain HTML forms and for the OAuth endpoints, which RFC 6749 specifies as
form-encoded.  A body whose `Content-Type` does not match is refused rather
than sniffed.

Percent-decoding is total: a malformed escape or a decoding that is not UTF-8
makes the whole parse fail, because a parameter that means something slightly
different to two readers is how request smuggling starts.
-/

namespace Pyle
namespace Http

open Lean (Json)

/-- The value of a hexadecimal digit. -/
private def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Percent-decode a component, reading `+` as a space when `plusIsSpace` (the
form encoding).  `none` for a malformed escape, a result that is not UTF-8, or
one containing NUL, which nothing legitimate sends and which C-string layers
below (SQLite's text binding) would silently truncate at. -/
def percentDecode (s : String) (plusIsSpace : Bool := true) : Option String :=
  let rec go : List Char → ByteArray → Option ByteArray
    | [], acc => some acc
    | '%' :: a :: b :: rest, acc => do
      let hi ← hexVal a
      let lo ← hexVal b
      go rest (acc.push (UInt8.ofNat (hi * 16 + lo)))
    | '%' :: _, _ => none
    | '+' :: rest, acc => go rest (acc.push (if plusIsSpace then 0x20 else 0x2b))
    | c :: rest, acc => go rest (acc ++ c.toString.toUTF8)
  (go s.toList .empty).bind String.fromUTF8? |>.filter (!·.contains '\x00')

/-- Parse `a=1&b=2`.  An empty string is no pairs; a pair without `=` has an
empty value; empty pairs (`a=1&&b=2`) are skipped.  `none` if any part fails
to decode. -/
def parseUrlEncoded (s : String) : Option (List (String × String)) :=
  if s.isEmpty then some [] else
  ((s.splitOn "&").filter (!·.isEmpty)).mapM fun part =>
    match part.splitOn "=" with
    | [k] => return (← percentDecode k, "")
    | k :: rest => return (← percentDecode k, ← percentDecode ("=".intercalate rest))
    | [] => none

/-- The value of a parameter in a decoded list, if it appears exactly once.
A parameter given twice is treated as absent, as OAuth requires (RFC 6749
§3.1: "parameters MUST NOT be included more than once"). -/
def lookupOnce (ps : List (String × String)) (name : String) : Option String :=
  match ps.filter (·.1 == name) with
  | [(_, v)] => some v
  | _ => none

/-- The media type of a `Content-Type`, lower-cased, without parameters. -/
def mediaType (contentType : String) : String :=
  ((contentType.splitOn ";").headD "").trimAscii.toString.toLower

/-- The request's query parameters. -/
def Req.queryParams (r : Req) : Except String (List (String × String)) :=
  match parseUrlEncoded r.query with
  | some ps => .ok ps
  | none => .error "the query string is not well-formed"

/-- The body as text. -/
def Req.bodyText (r : Req) : Except String String :=
  match String.fromUTF8? r.body with
  | some s => .ok s
  | none => .error "the body is not UTF-8"

/-- The body as a form, if the request says it is one. -/
def Req.form (r : Req) : Except String (List (String × String)) := do
  unless mediaType ((r.header "content-type").getD "") ==
      "application/x-www-form-urlencoded" do
    throw "the body must be application/x-www-form-urlencoded"
  match parseUrlEncoded (← r.bodyText) with
  | some ps => return ps
  | none => throw "the form is not well-formed"

/-- Whether a JSON value contains a NUL character in any string or key. -/
partial def jsonHasNul : Json → Bool
  | .str s => s.contains '\x00'
  | .arr xs => xs.any jsonHasNul
  | .obj kvs => kvs.toArray.any fun (k, v) => k.contains '\x00' || jsonHasNul v
  | _ => false

/-- The body as JSON, if the request says it is.  A body with NUL in any
string is refused, for the reason `percentDecode` gives. -/
def Req.json (r : Req) : Except String Json := do
  unless mediaType ((r.header "content-type").getD "") == "application/json" do
    throw "the body must be application/json"
  match Json.parse (← r.bodyText) with
  | .ok j =>
    if jsonHasNul j then throw "the body contains a NUL character"
    return j
  | .error _ => throw "the body is not valid JSON"

end Http
end Pyle