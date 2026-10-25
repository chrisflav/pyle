import Pyle.Oidc.Client
import Pyle.Oidc.Pkce

/-!
# The authorization endpoint

`GET /authorize` runs the authorization-code flow of OpenID Connect Core §3.1
with the constraints of DESIGN.md §5.1, and nothing else: `response_type=code`
only, PKCE with `S256` required of every client, redirect URIs compared byte
for byte.

The checks go in the order RFC 6749 §4.1.2.1 prescribes.  As long as the
client or the redirect URI is in doubt, the error is shown to the user and the
browser is not redirected anywhere, since redirecting to an unverified URI is
an open redirector.  Once both are known, every error is sent back to the
client at its redirect URI.

Every response sent back to the client — a code or an error — carries `iss`
(RFC 9207), so a client that talks to several providers can tell which one
answered.

**The session.**  The user must be signed in, and the request may ask for more:

* `prompt=login` — a fresh authentication now;
* `max_age=n` — one within the last `n` seconds;
* `acr_values` naming `phr` — a phishing-resistant one.

When the session does not satisfy them, the browser is sent to sign in and back
here (`Oidc.signinRedirect`), or, under `prompt=none`, the client gets
`login_required`.  `max_age=0` means the same as `prompt=login`.  When the
authentication is too old — `prompt=login`, or older than `max_age` — the way
back carries, instead of `prompt` and `max_age`, the parameter
`pyle_auth_after` with the time of the request, so that the authentication that
just happened satisfies it and the request does not loop, however many seconds
sign-in takes.  The client still sees `auth_time` in the ID token and checks
`max_age` against it.  A client that sends `pyle_auth_after` itself only asks
for a fresher authentication than it needs.

A code is good once, for 60 seconds, and only for the client, redirect URI and
code challenge it was issued with (the store binds them, `/token` checks them).
-/

namespace Pyle
namespace Oidc

open Http
open Store

/-- How long an authorization code is accepted, in seconds. -/
def codeSeconds : Nat := 60

/-- An error shown to the user rather than sent to the client, because the
client or its redirect URI could not be verified. -/
def authorizeErrorPage (message : String) : Reply :=
  page "Sign-in request refused"
    s!"<p>{htmlEscape message}</p>\n<p>Go back to the service you came from and try again.</p>"
    .badRequest

/-- Send an authorization error back to the client (RFC 6749 §4.1.2.1), with
`state` if the request had one and `iss` (RFC 9207). -/
def errorRedirect (ctx : Ctx) (redirectUri : String) (state : Option String)
    (code description : String) : Reply :=
  Reply.redirect <| addQuery redirectUri <|
    [("error", code), ("error_description", description)] ++
    (state.map fun s => [("state", s)]).getD [] ++ [("iss", ctx.config.issuer)]

/-- What the session must satisfy for a request. -/
structure Requirements where
  /-- Authenticated no earlier than this time. -/
  notBefore : Option Nat := none
  /-- Authenticated within this many seconds. -/
  maxAge : Option Nat := none
  /-- With a phishing-resistant authenticator. -/
  phr : Bool := false

/-- Whether a session satisfies the requirements at `now`. -/
def Requirements.satisfied (q : Requirements) (s : Session) (now : Nat) : Bool :=
  q.notBefore.all (· ≤ s.authTime) && q.maxAge.all (fun a => now ≤ s.authTime + a) &&
    (!q.phr || Policy.acr s.amr == "phr")

/-- The `max_age` to ask sign-in for: zero for a fresh authentication. -/
def Requirements.signinMaxAge (q : Requirements) : Option Nat :=
  if q.notBefore.isSome then some 0 else q.maxAge

/-- Answer an authorization request with parameters `ps`. -/
def authorizeParams (ctx : Ctx) (r : Req) (ps : List (String × String)) : IO Reply := do
  let some clientId := lookupOnce ps "client_id"
    | return authorizeErrorPage "The request does not name a client."
  let some client ← ctx.store.findClient clientId
    | return authorizeErrorPage "The request names a client pyle does not know."
  let some redirectUri := lookupOnce ps "redirect_uri"
    | return authorizeErrorPage "The request does not name a redirect URI."
  unless client.redirectUris.contains redirectUri do
    return authorizeErrorPage "The redirect URI is not one registered for this client."
  -- From here on, errors go back to the client.
  let state := lookupOnce ps "state"
  let fail := errorRedirect ctx redirectUri state
  let names := ps.map (·.1)
  if names.eraseDups.length != names.length then
    return fail "invalid_request" "a parameter is repeated"
  if (lookupOnce ps "request").isSome then
    return fail "request_not_supported" "request objects are not supported"
  if (lookupOnce ps "request_uri").isSome then
    return fail "request_uri_not_supported" "request objects are not supported"
  if (lookupOnce ps "registration").isSome then
    return fail "registration_not_supported" "registration is not supported"
  match lookupOnce ps "response_type" with
  | none => return fail "invalid_request" "response_type is required"
  | some "code" => pure ()
  | some _ => return fail "unsupported_response_type" "only the code flow is supported"
  if (lookupOnce ps "response_mode").any (· != "query") then
    return fail "invalid_request" "only response_mode=query is supported"
  let scopes := words ((lookupOnce ps "scope").getD "")
  unless scopes.contains "openid" do
    return fail "invalid_scope" "the scope must include openid"
  unless scopes.all client.scopes.contains do
    return fail "invalid_scope" "the client may not ask for that scope"
  unless lookupOnce ps "code_challenge_method" == some "S256" do
    return fail "invalid_request" "PKCE with code_challenge_method=S256 is required"
  let some challenge := lookupOnce ps "code_challenge"
    | return fail "invalid_request" "PKCE with code_challenge_method=S256 is required"
  unless Pkce.validChallenge challenge do
    return fail "invalid_request" "the code challenge is not an S256 challenge"
  let prompt := words ((lookupOnce ps "prompt").getD "")
  if prompt.contains "none" && prompt.length > 1 then
    return fail "invalid_request" "prompt=none cannot be combined with other prompts"
  let maxAge ← match lookupOnce ps "max_age" with
    | none => pure none
    | some a => match a.toNat? with
      | some n => pure (some n)
      | none => return fail "invalid_request" "max_age must be a number of seconds"
  let authAfter ← match lookupOnce ps "pyle_auth_after" with
    | none => pure none
    | some a => match a.toNat? with
      | some n => pure (some n)
      | none => return fail "invalid_request" "pyle_auth_after must be a time"
  let nonce := lookupOnce ps "nonce"
  if nonce.any (·.length > 512) then return fail "invalid_request" "the nonce is too long"
  let phr := words ((lookupOnce ps "acr_values").getD "") |>.contains "phr"
  let now ← ctx.clock
  -- `prompt=login` and `max_age=0` ask for an authentication now.
  let login := prompt.contains "login" || maxAge == some 0
  let req : Requirements :=
    { notBefore := if login then some now else authAfter,
      maxAge := if login then none else maxAge, phr }
  let session ← Session.current ctx r
  let some s := session.filter (req.satisfied · now)
    | if prompt.contains "none" then
        return fail "login_required" "the user must sign in"
      -- An authentication too old for the request is renewed at sign-in, and the
      -- way back asks only for one no older than now, which the renewed one is,
      -- so the request cannot loop however long sign-in takes.
      let freshness : Requirements := { req with phr := false }
      let stale := (req.notBefore.isSome || req.maxAge.isSome) &&
        !session.any (freshness.satisfied · now)
      if stale then
        let kept := ps.filter fun (k, _) =>
          k != "prompt" && k != "max_age" && k != "pyle_auth_after"
        return signinRedirect
          ("/authorize?" ++ queryString (kept ++ [("pyle_auth_after", toString now)]))
          req.signinMaxAge phr
      return signinRedirect (Req.pathAndQuery r) none phr
  let some user ← ctx.store.findUser s.user
    | return fail "server_error" "the account is gone"
  let code ← randomToken
  ctx.store.addCode (tokenHash code)
    { clientId, redirectUri, codeChallenge := challenge, user := user.id,
      scope := " ".intercalate scopes, nonce, amr := s.amr, authTime := s.authTime,
      expires := now + codeSeconds }
  ctx.store.setCodeSession (tokenHash code) s.idHash
  return Reply.redirect <| addQuery redirectUri <|
    [("code", code)] ++ (state.map fun st => [("state", st)]).getD [] ++
    [("iss", ctx.config.issuer)]

/-- `GET /authorize`. -/
def authorize : Handler := fun ctx r => do
  match r.queryParams with
  | .ok ps => authorizeParams ctx r ps
  | .error _ => return authorizeErrorPage "The request is not well-formed."

/-- `POST /authorize`, which OpenID Connect Core §3.1.2.1 requires alongside
`GET`: the form is sent back as a `GET` with the same parameters (303), so the
request is answered by the one handler that reads the session.  The route is
exempt from the `Origin` check, since a relying party's page posts it; it
changes nothing. -/
def authorizePost : Handler := fun _ r => do
  match r.form with
  | .ok ps => return Reply.redirect ("/authorize?" ++ queryString ps)
  | .error _ => return authorizeErrorPage "The request is not well-formed."

end Oidc
end Pyle