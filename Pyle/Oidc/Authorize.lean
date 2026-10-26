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

**The session.**  The user must be signed in, at the client's minimum level
or better (`ClientSettings.minAcr`, `pyle client add --min-acr`; `mfa` unless
set), and the request may ask for more:

* `prompt=login` — a fresh authentication now;
* `max_age=n` — one within the last `n` seconds;
* `acr_values` — a level, as a space-separated list of `acr` values in order
  of preference (OpenID Connect Core §3.1.2.1): the four of `Acr`, and the
  aliases `Acr.ofIdentifier?` reads.  Any of those listed will do, so the
  session must reach the weakest of them; values pyle does not know are
  ignored, as the parameter is voluntary;
* the `claims` parameter (§5.5) asking for the ID token's `acr`, with
  `value` or `values`: read as `acr_values` is, and when it is `essential`
  (§5.5.1.1) the ID token's `acr` is the first of those values, in the order
  given, that the session meets, and a request none of whose values pyle knows
  is refused with `unmet_authentication_requirements`.  The `claims`
  parameter, when it asks about `acr`, takes the place of `acr_values`.

A request can only add to the client's minimum, never lower it: the request
comes through the browser, and whoever controls the browser could otherwise
ask for less than the client relies on (`Acr.satisfies_max`).  Otherwise the
ID token's `acr` is the session's own level, which may be more than was asked.

When the session does not satisfy them, the browser is sent to sign in and back
here (`Oidc.signinRedirect`) with the level it needs, or, under `prompt=none`,
the client gets `login_required` (no session, or too old) or
`interaction_required` (a level too low).  `max_age=0` means the same as
`prompt=login`.  When the
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
open Lean (Json)

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
  /-- At this level or better. -/
  level : Acr := .sfa

/-- Whether a session satisfies the requirements at `now`. -/
def Requirements.satisfied (q : Requirements) (s : Session) (now : Nat) : Bool :=
  q.notBefore.all (· ≤ s.authTime) && q.maxAge.all (fun a => now ≤ s.authTime + a) &&
    s.level.satisfies q.level

/-- What a request asks of the `acr`: the values it names that pyle knows, in
its order of preference, each with the level it names, and whether it asked
for them as an essential claim. -/
structure AcrRequest where
  /-- The values, as sent, with their levels. -/
  values : List (String × Acr) := []
  /-- Whether the `claims` parameter marked `acr` essential. -/
  essential : Bool := false
  /-- Whether it named values, known or not. -/
  named : Bool := false

/-- The values of a list that name a level pyle knows, with their levels. -/
def knownAcrValues (vs : List String) : List (String × Acr) :=
  vs.filterMap fun v => (Acr.ofIdentifier? v).map (v, ·)

/-- The `acr` request of an `acr_values` parameter. -/
def acrValuesRequest (s : String) : AcrRequest :=
  { values := knownAcrValues (words s), named := !(words s).isEmpty }

/-- The `acr` request in a `claims` parameter (OpenID Connect Core §5.5): its
`id_token` member's `acr`, if it has one.  `none` when it says nothing about
`acr`; an error when it is not the JSON object §5.5 describes. -/
def claimsAcrRequest (claims : String) : Except String (Option AcrRequest) := do
  let j ← Json.parse claims
  let .obj _ := j | throw "claims must be a JSON object"
  let some idToken := (j.getObjVal? "id_token").toOption | return none
  match idToken.getObjVal? "acr" with
  | .error _ => return none
  | .ok .null => return some {}
  | .ok acr =>
    let essential := (acr.getObjValAs? Bool "essential").toOption.getD false
    let vs := match acr.getObjValAs? String "value", acr.getObjValAs? (Array String) "values" with
      | .ok v, _ => [v]
      | _, .ok vs => vs.toList
      | _, _ => []
    return some { values := knownAcrValues vs, essential, named := !vs.isEmpty }

/-- The weakest level a request names, if it names any pyle knows: any of
them will do. -/
def AcrRequest.level (q : AcrRequest) : Option Acr :=
  q.values.foldl (fun m (_, a) => some (match m with | some b => Acr.min a b | none => a)) none

/-- The `acr` an ID token states for a session at `level`, when the request
made it an essential claim with values: the first value, in the order given,
that the level meets.  `none` otherwise — the token then states the session's
own level. -/
def AcrRequest.claim (q : AcrRequest) (level : Acr) : Option String :=
  if q.essential then (q.values.find? fun (_, a) => level.satisfies a).map (·.1) else none

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
  let fromClaims ← match (lookupOnce ps "claims").map claimsAcrRequest with
    | none => pure none
    | some (.ok q) => pure q
    | some (.error e) => return fail "invalid_request" s!"the claims parameter is malformed: {e}"
  let acrReq := fromClaims.getD (acrValuesRequest ((lookupOnce ps "acr_values").getD ""))
  if acrReq.essential && acrReq.named && acrReq.values.isEmpty then
    return fail "unmet_authentication_requirements" "pyle knows none of the acr values asked for"
  let settings := (← ctx.store.clientSettings clientId).getD {}
  let level := Acr.max settings.minAcr (acrReq.level.getD .sfa)
  let now ← ctx.clock
  -- `prompt=login` and `max_age=0` ask for an authentication now.
  let login := prompt.contains "login" || maxAge == some 0
  let req : Requirements :=
    { notBefore := if login then some now else authAfter,
      maxAge := if login then none else maxAge, level }
  let session ← Session.current ctx r
  let some s := session.filter (req.satisfied · now)
    | -- An authentication too old for the request is renewed at sign-in, and the
      -- way back asks only for one no older than now, which the renewed one is,
      -- so the request cannot loop however long sign-in takes.
      let freshness : Requirements := { req with level := .sfa }
      let stale := !session.any (freshness.satisfied · now)
      if prompt.contains "none" then
        if stale then return fail "login_required" "the user must sign in"
        return fail "interaction_required"
          s!"the user must sign in again at {level.identifier} or better"
      if stale && (req.notBefore.isSome || req.maxAge.isSome) then
        let kept := ps.filter fun (k, _) =>
          k != "prompt" && k != "max_age" && k != "pyle_auth_after"
        return signinRedirect
          ("/authorize?" ++ queryString (kept ++ [("pyle_auth_after", toString now)]))
          req.signinMaxAge level
      return signinRedirect (Req.pathAndQuery r) none level
  let some user ← ctx.store.findUser s.user
    | return fail "server_error" "the account is gone"
  let code ← randomToken
  ctx.store.addCode (tokenHash code)
    { clientId, redirectUri, codeChallenge := challenge, user := user.id,
      scope := " ".intercalate scopes, nonce, amr := s.amr, authTime := s.authTime,
      expires := now + codeSeconds, acr := acrReq.claim s.level }
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