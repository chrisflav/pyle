import Pyle.Session.Policy
import Pyle.Oidc.Jwk

/-!
# What the protocol endpoints share

URL building, the redirect to sign in, the `acr` of a session, the subject
identifier, bearer values, and the small HTML pages the device grant and
logout show.

**Signing in is not done here.**  Anything that needs a signed-in user and has
none sends the browser to `/signin?return=<path and query>` (303), adding
`max_age=<seconds>` when the session must have authenticated recently and
`acr=phr` when it must have used a phishing-resistant authenticator; the
sign-in pages accept only a relative `return` on this issuer and come back to
it once the session satisfies both.  The protocol endpoints read the session
with `Session.current` and never create or change one.
-/

namespace Pyle
namespace Oidc

open Http
open Lean (Json)

/-- Percent-encode everything but RFC 3986's unreserved characters, for a
query parameter's name or value. -/
def urlEncode (s : String) : String :=
  s.toUTF8.foldl (init := "") fun out b =>
    let c := Char.ofNat b.toNat
    if c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~' then out.push c
    else
      let hex := "0123456789ABCDEF".toList
      out.push '%' |>.push (hex.getD (b.toNat / 16) '0') |>.push (hex.getD (b.toNat % 16) '0')

/-- A query string from name–value pairs, each part percent-encoded. -/
def queryString (ps : List (String × String)) : String :=
  "&".intercalate (ps.map fun (k, v) => s!"{urlEncode k}={urlEncode v}")

/-- A URI with parameters added to its query: after `?` if it has no query,
after `&` if it has one.  The URI is not otherwise changed, so a registered
redirect URI keeps its own parameters (RFC 6749 §3.1.2). -/
def addQuery (uri : String) (ps : List (String × String)) : String :=
  if ps.isEmpty then uri
  else uri ++ (if uri.contains '?' then "&" else "?") ++ queryString ps

/-- The words of a space-separated parameter. -/
def words (s : String) : List String := (s.splitOn " ").filter (!·.isEmpty)

/-- The path and query of a request, as the `return` of a sign-in redirect. -/
def Req.pathAndQuery (r : Req) : String :=
  if r.query.isEmpty then r.path else r.path ++ "?" ++ r.query

/-- The URL of the sign-in page that comes back to `returnTo`, a path and query
on this issuer, once the session has authenticated within `maxAge` seconds (if
given) and with a phishing-resistant authenticator (if `phr`). -/
def signinUrl (returnTo : String) (maxAge : Option Nat := none) (phr : Bool := false) :
    String :=
  "/signin?" ++ queryString ([("return", returnTo)] ++
    (maxAge.map fun a => [("max_age", toString a)]).getD [] ++
    (if phr then [("acr", "phr")] else []))

/-- Send the browser to sign in, and back to `returnTo` afterwards. -/
def signinRedirect (returnTo : String) (maxAge : Option Nat := none) (phr : Bool := false) :
    Reply :=
  Reply.redirect (signinUrl returnTo maxAge phr)

/-- The `sub` pyle gives a user: the base64url of the account's random user
handle, stable for the account's life and saying nothing about its name. -/
def subjectOf (u : Store.User) : String := Jose.b64urlEncode u.handle

/-- A fresh bearer value: 32 random bytes in unpadded base64url. -/
def randomToken : IO String := return Jose.b64urlEncode (← Crypto.randomBytes 32)

/-- The hash a bearer value is stored under. -/
def tokenHash (token : String) : Store.SecretHash := .of token.toUTF8

/-- Escape text for HTML. -/
def htmlEscape (s : String) : String :=
  s.foldl (init := "") fun out c =>
    match c with
    | '&' => out ++ "&amp;"
    | '<' => out ++ "&lt;"
    | '>' => out ++ "&gt;"
    | '"' => out ++ "&quot;"
    | '\'' => out ++ "&#39;"
    | c => out.push c

/-- A plain HTML page with a title and a body, which must already be escaped.
It takes its style from `/assets/pyle.css` and runs no script, so it satisfies
the strict Content Security Policy every reply carries. -/
def page (title body : String) (status : Std.Http.Status := .ok) : Reply :=
  let html := "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n" ++
    "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n" ++
    s!"<title>{htmlEscape title} · pyle</title>\n" ++
    "<link rel=\"stylesheet\" href=\"/assets/pyle.css\">\n</head>\n<body>\n<main>\n" ++
    s!"<h1>{htmlEscape title}</h1>\n{body}\n</main>\n</body>\n</html>"
  { status, body := html.toUTF8, contentType := "text/html; charset=utf-8" }

/-- A JSON reply that no cache may keep, as RFC 6749 §5.1 requires of token
responses: `Cache-Control: no-store` and `Pragma: no-cache`. -/
def noStore (r : Reply) : Reply :=
  (r.withHeader "Cache-Control" "no-store").withHeader "Pragma" "no-cache"

/-- An OAuth error reply (RFC 6749 §5.2) that no cache may keep. -/
def oauthError (code : String) (description : String := "")
    (status : Std.Http.Status := .badRequest) : Reply :=
  noStore (Reply.error status code description)

/-- The absolute URL of a path on this issuer. -/
def issuerUrl (ctx : Ctx) (path : String) : String := ctx.config.issuer ++ path

end Oidc
end Pyle