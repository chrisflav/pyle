import Std.Http
import Lean.Data.Json

/-!
# Requests and replies

What a handler sees of a request and what it answers, as plain data.  The
server adapts `Std.Http` to and from these (`Pyle.Server`), and everything in
between — routing, the `Origin` check, cookies, the handlers themselves — is a
function of a `Req` that the tests can call without a socket.
-/

namespace Pyle
namespace Http

open Lean (Json)
open Std.Http (Method Status)

/-- What a handler needs of a request. -/
structure Req where
  /-- The method. -/
  method : Method
  /-- The path, without the query string, still percent-encoded. -/
  path : String
  /-- The query string, without the `?`, still percent-encoded. -/
  query : String := ""
  /-- The headers, names lower-cased, in the order they arrived. -/
  headers : List (String × String) := []
  /-- The body. -/
  body : ByteArray := .empty
  /-- The client's address: the socket peer, or what a trusted proxy says it
  is (`Http.clientAddress`).  This is what rate limits and the audit log
  record. -/
  clientAddress : String := ""
  /-- The socket peer the request arrived from, before any `X-Forwarded-For`
  is read: what forward authentication checks against the trusted proxies,
  since only a trusted proxy's `X-Forwarded-Host` may be believed. -/
  peer : String := ""
  /-- The values of the route pattern's `:name` segments, filled in by the
  router. -/
  params : List (String × String) := []

instance : Inhabited Req := ⟨{ method := .get, path := "/" }⟩

/-- The first value of a header, by case-insensitive name. -/
def Req.header (r : Req) (name : String) : Option String :=
  let n := name.toLower
  (r.headers.find? (·.1 == n)).map (·.2)

/-- A route parameter by name. -/
def Req.param (r : Req) (name : String) : Option String :=
  (r.params.find? (·.1 == name)).map (·.2)

/-- A request, for tests and for the server: header names are lower-cased
here so that lookups need not care. -/
def Req.mk' (method : Method) (target : String) (headers : List (String × String) := [])
    (body : ByteArray := .empty) (clientAddress : String := "127.0.0.1") : Req :=
  let (path, query) := match target.splitOn "?" with
    | [] => ("/", "")
    | p :: rest => (p, "?".intercalate rest)
  { method, path, query, headers := headers.map fun (k, v) => (k.toLower, v), body,
    clientAddress }

/-- What a handler answers. -/
structure Reply where
  /-- The status. -/
  status : Status
  /-- The body. -/
  body : ByteArray := .empty
  /-- The `Content-Type`, or empty for none. -/
  contentType : String := ""
  /-- Further headers.  The router adds the security headers to every reply;
  a handler adds what is particular to it. -/
  headers : List (String × String) := []

instance : Inhabited Reply := ⟨{ status := .ok }⟩

namespace Reply

/-- Add a header. -/
def withHeader (r : Reply) (name value : String) : Reply :=
  { r with headers := r.headers ++ [(name, value)] }

/-- The first value of a header this reply carries, by case-insensitive name. -/
def header (r : Reply) (name : String) : Option String :=
  let n := name.toLower
  if n == "content-type" && !r.contentType.isEmpty then some r.contentType
  else (r.headers.find? (·.1.toLower == n)).map (·.2)

/-- A JSON reply. -/
def json (j : Json) (status : Status := .ok) : Reply :=
  { status, body := j.compress.toUTF8, contentType := "application/json" }

/-- A JSON error, `{"error": code, "error_description": description}`: the
shape OAuth 2.0 uses (RFC 6749 §5.2), so that every error pyle answers reads
the same way.  The description is for people and never quotes a secret or the
internals of a failure. -/
def error (status : Status) (code : String) (description : String := "") : Reply :=
  let fields := [("error", Json.str code)] ++
    (if description.isEmpty then [] else [("error_description", Json.str description)])
  json (Json.mkObj fields) status

/-- A plain-text reply. -/
def text (s : String) (status : Status := .ok) : Reply :=
  { status, body := s.toUTF8, contentType := "text/plain; charset=utf-8" }

/-- An empty reply. -/
def noContent : Reply := { status := .noContent }

/-- A redirect to `location` with `303 See Other`, so that the browser follows
it with a `GET` whatever the request was. -/
def redirect (location : String) : Reply :=
  { status := .seeOther, headers := [("Location", location)] }

/-- The body as text, or empty if it is not UTF-8; for tests. -/
def bodyText (r : Reply) : String := (String.fromUTF8? r.body).getD ""

end Reply

end Http
end Pyle