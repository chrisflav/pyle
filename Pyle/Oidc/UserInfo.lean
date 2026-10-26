import Pyle.Oidc.IdToken
import Pyle.Token.Biscuit

/-!
# The userinfo endpoint

`GET` or `POST /userinfo` (OpenID Connect Core §5.3) with an access token in
the `Authorization: Bearer` header (RFC 6750 §2.1) answers the claims about
its user: `sub`, and `name` and `groups` when the token's scope includes
`profile` and `groups` (`scopedClaims`, as in the ID token).  The access
token is a biscuit, verified here as any service verifies one
(`Token.verify`), for the audience `pyle`, which every access token pyle
issues includes.  The account is read afresh, so a disabled one gets nothing.

A missing or bad token is answered `401` with a `WWW-Authenticate` challenge,
naming `invalid_token` when there was a token (RFC 6750 §3).
-/

namespace Pyle
namespace Oidc

open Http
open Lean (Json)

/-- The bearer token of a request's `Authorization` header. -/
def bearerToken (r : Req) : Option String := do
  let h ← r.header "authorization"
  let parts := (h.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
  let [scheme, token] := parts | none
  guard (scheme.toLower == "bearer")
  return token

/-- A `401` for a request without a usable bearer token. -/
def bearerChallenge (invalid : Bool) : Reply :=
  let challenge := if invalid then "Bearer realm=\"pyle\", error=\"invalid_token\""
    else "Bearer realm=\"pyle\""
  (noStore (Reply.error .unauthorized (if invalid then "invalid_token" else "invalid_request")))
    |>.withHeader "WWW-Authenticate" challenge

/-- The live account an access token presented to pyle speaks for. -/
def bearerUser (ctx : Ctx) (r : Req) : IO (Except Reply (Store.User × Token.Identity)) := do
  let some t := bearerToken r | return .error (bearerChallenge false)
  match ← Token.verifyForPyle ctx.store t (← ctx.clock) with
  | .error _ => return .error (bearerChallenge true)
  | .ok identity =>
    match ← ctx.store.findUserByName identity.user with
    | some u =>
      if u.disabled then return .error (bearerChallenge true) else return .ok (u, identity)
    | none => return .error (bearerChallenge true)

/-- `GET /userinfo` and `POST /userinfo`. -/
def userinfo : Handler := fun ctx r => do
  match ← bearerUser ctx r with
  | .error reply => return reply
  | .ok (u, identity) =>
    return noStore <| Reply.json <| Json.mkObj <|
      [("sub", Json.str (subjectOf u))] ++ accountClaims (← Policy.accountLevel ctx u.id) ++
        scopedClaims u identity.scopes

end Oidc
end Pyle