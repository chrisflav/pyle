import Pyle.Oidc.Client
import Pyle.Oidc.IdToken
import Pyle.Audit

/-!
# RP-initiated logout

`/end_session` is the end-session endpoint of OpenID Connect RP-Initiated
Logout 1.0, answering `GET` and, as §2 requires, `POST`: the form is sent back
as a `GET` with the same parameters (303), as `POST /authorize` is, so the
route can be exempt from the `Origin` check — a relying party's page posts
it — and the one handler that reads the session answers.  A relying party
sends the browser here with any of
`id_token_hint`, `client_id`, `post_logout_redirect_uri` and `state`:

* an `id_token_hint` must be an ID token pyle signed for this issuer — its
  `exp` is not checked, as the specification asks (§2) — and names the client;
  a `client_id` given with it must match its audience;
* a `post_logout_redirect_uri` must be one registered for that client, byte for
  byte, or the request is refused without redirecting anywhere (§3); with
  neither a hint nor a `client_id` there is no client to check it against, and
  it is refused too.

Signing out changes state, and a `GET` that anyone can link to must not, so
when the browser has a session pyle asks: the page shows a form that posts to
`POST /end_session/confirm`, under the `Origin` check, which ends the session
(and with it, through the schema's triggers, every refresh-token family tied
to it), revokes the refresh tokens the user holds at that client, and answers
with a page saying so and linking to the registered URI with `state`.  It links
rather than redirects because the Content Security Policy's
`form-action 'self'` would stop a browser following a redirect from a form
submission to another origin.  Without a session there is nothing to end, and
the browser is redirected at once.
-/

namespace Pyle
namespace Oidc

open Http
open Lean (Json)

/-- The protected header of a compact JWS, unverified, to find the key it
names. -/
def jwsHeader (token : String) : Option Json := do
  let h ← (token.splitOn ".").head?
  let bytes ← Jose.b64urlDecode? h
  let text ← String.fromUTF8? bytes
  (Json.parse text).toOption

/-- Verify an ID token pyle issued, ignoring its expiry: the key its `kid`
names must be a published ID-token key, its signature must verify under it,
and its `iss` must be this issuer.  Its claims. -/
def verifyIdTokenHint (ctx : Ctx) (token : String) : IO (Option Json) := do
  let some header := jwsHeader token | return none
  let .ok kid := header.getObjValAs? String "kid" | return none
  let keys := (← Keys.published ctx.store .idTokenEs256) ++
    (← Keys.published ctx.store .idTokenRs256)
  let some k := keys.find? (·.kid == kid) | return none
  let some alg := Crypto.SigningAlgorithm.ofJoseName? k.algorithm | return none
  let .ok claims := Jwt.verify alg k.publicKey token | return none
  match claims.getObjValAs? String "iss" with
  | .ok iss => if iss != ctx.config.issuer then return none
  | .error _ => return none
  return some claims

/-- The audience of ID-token claims: a string, or the first of an array. -/
def audienceOf (claims : Json) : Option String :=
  match claims.getObjVal? "aud" with
  | .ok (Json.str a) => some a
  | .ok (Json.arr as) => match as[0]? with
    | some (Json.str a) => some a
    | _ => none
  | _ => none

/-- A logout request, checked. -/
structure LogoutRequest where
  /-- The client it came from, if it named one. -/
  client : Option String
  /-- Where to send the browser afterwards, already checked against the
  client's registration. -/
  redirect : Option String
  /-- The relying party's `state`, to hand back. -/
  state : Option String

/-- Check a logout request's parameters. -/
def checkLogout (ctx : Ctx) (ps : List (String × String)) : IO (Except String LogoutRequest) := do
  let hinted ← match lookupOnce ps "id_token_hint" with
    | none => pure none
    | some t => match ← verifyIdTokenHint ctx t with
      | some claims => pure (some (audienceOf claims))
      | none => return .error "The sign-out request carries an ID token pyle did not issue."
  let given := lookupOnce ps "client_id"
  let client ← match hinted, given with
    | some (some a), some g =>
      if a != g then return .error "The sign-out request names two different clients."
      else pure (some a)
    | some (some a), none => pure (some a)
    | some none, _ => return .error "The ID token in the sign-out request names no client."
    | none, g => pure g
  let redirect ← match lookupOnce ps "post_logout_redirect_uri" with
    | none => pure none
    | some uri =>
      let some c := client
        | return .error "The sign-out request names a return address but no client."
      let some settings ← ctx.store.clientSettings c
        | return .error "The sign-out request names a client pyle does not know."
      unless settings.postLogoutRedirectUris.contains uri do
        return .error "The return address is not one registered for this client."
      pure (some uri)
  return .ok { client, redirect, state := lookupOnce ps "state" }

/-- Where to go once signed out: the registered URI with `state`, or a page. -/
def afterLogout (l : LogoutRequest) : Reply :=
  match l.redirect with
  | some uri => Reply.redirect (addQuery uri ((l.state.map fun s => [("state", s)]).getD []))
  | none => page "Signed out" "<p>You are signed out of pyle.</p>"

/-- The page that asks whether to sign out. -/
def confirmPage (clientName : Option String) (l : LogoutRequest) : Reply :=
  let hidden (k : String) (v : Option String) : String :=
    (v.map fun v => s!"<input type=\"hidden\" name=\"{k}\" value=\"{htmlEscape v}\">\n").getD ""
  let who := (clientName.map fun n => s!" {htmlEscape n} asks you to sign out.").getD ""
  page "Sign out" <|
    s!"<p>{who} Sign out of pyle on this browser?</p>\n" ++
    "<form method=\"post\" action=\"/end_session/confirm\">\n" ++
    hidden "client_id" l.client ++ hidden "post_logout_redirect_uri" l.redirect ++
    hidden "state" l.state ++ "<button type=\"submit\">Sign out</button>\n</form>"

/-- `GET /end_session`. -/
def endSession : Handler := fun ctx r => do
  let .ok ps := r.queryParams
    | return page "Sign out" "<p>The request is malformed.</p>" .badRequest
  match ← checkLogout ctx ps with
  | .error msg => return page "Sign out" s!"<p>{htmlEscape msg}</p>" .badRequest
  | .ok l =>
    if (← Session.current ctx r).isNone then return afterLogout l
    let clientName ← match l.client with
      | some c => pure ((← ctx.store.findClient c).map (·.name))
      | none => pure none
    return confirmPage clientName l

/-- `POST /end_session`: the form as a `GET` (303). -/
def endSessionPost : Handler := fun _ r => do
  match r.form with
  | .ok ps => return Reply.redirect ("/end_session?" ++ queryString ps)
  | .error _ => return page "Sign out" "<p>The request is malformed.</p>" .badRequest

/-- The page after signing out: a link back to the relying party, if it gave a
registered address. -/
def signedOutPage (l : LogoutRequest) : Reply :=
  let back := (l.redirect.map fun uri =>
    let target := addQuery uri ((l.state.map fun s => [("state", s)]).getD [])
    let name := htmlEscape (l.client.getD "the service")
    s!"\n<p><a href=\"{htmlEscape target}\">Return to {name}</a></p>"
    ).getD ""
  page "Signed out" ("<p>You are signed out of pyle.</p>" ++ back)

/-- `POST /end_session/confirm`: end the session and the client's refresh
tokens, then show where to go next. -/
def confirmLogout : Handler := fun ctx r => do
  let .ok form := r.form | return page "Sign out" "<p>The form is malformed.</p>" .badRequest
  match ← checkLogout ctx form with
  | .error msg => return page "Sign out" s!"<p>{htmlEscape msg}</p>" .badRequest
  | .ok l =>
    if let some s ← Session.current ctx r then
      discard <| ctx.store.endSession s.idHash
      if let some c := l.client then
        discard <| ctx.store.revokeUserClientFamilies s.user c (← ctx.clock)
      let name := (← ctx.store.findUser s.user).map (·.name)
      Audit.log ctx r .signOut .success (userName := name)
        (detail := (l.client.map (s!"requested by {·}")).getD "")
    return (signedOutPage l).clearSession

end Oidc
end Pyle