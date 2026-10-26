import Pyle.Oidc.UserInfo
import Pyle.Audit

/-!
# Attesting a user to kleis

A kleis grant can name a person rather than a string an owner typed
(DESIGN.md §5.4):

```
check if user($u), ["alice"].contains($u) trusting ed25519/<pyle's biscuit root key>;
```

The holder of a kleis biscuit asks it for a third-party block request, sends
that request here, and appends the block pyle returns.  The block states
`user`, the `amr` and `acr` of the sign-in and the user's `group`s, and checks
that it is used within `attestationSeconds`; it is signed by pyle's biscuit
root key through OpenSSL, and covers the request's previous signature, so it is good in
that one token only.

Two routes answer, because they authenticate differently:

* `POST /kleis/attest` with a pyle access token (`Authorization: Bearer`), as a
  command-line client holding one from the device grant calls it.  The token
  must have been granted the scope `kleis`: every relying party receives access
  tokens, and an ordinary one must not be able to turn the user's token into a
  kleis attestation.  The route is exempt from the `Origin` check and never sees
  a cookie; the attested `amr` is the token's.
* `POST /kleis/attest/session` from a signed-in browser, under the `Origin`
  check; the attested `amr` is the session's.

Either attests only a sign-in at `kleisMinAcr` or better (`mfa` unless
configured), and answers `403 insufficient_acr` otherwise: a kleis grant that
trusts pyle's `user` fact must not be met by a password alone.  A token issued
before pyle stated levels has no `acr` and counts as `mfa`, which every
session then reached.

Either takes a form with `request`, the request in base64url, and answers
`{"block": …, "public_key": "ed25519/…", "expires": …}`, the block being the
serialised third-party block contents in base64url.
-/

namespace Pyle
namespace Token

open Http
open Oidc
open Lean (Json)

/-- The scope an access token needs for `POST /kleis/attest`. -/
def kleisScope : String := "kleis"

/-- Read a third-party block request in base64url, padded or not. -/
def decodeRequest (s : String) : Option LeanBiscuit.Proto.ThirdPartyBlockRequest := do
  let bytes ← LeanBiscuit.Base64.decode? s.trimAscii.toString
  (LeanBiscuit.Proto.Schema.decodeThirdPartyBlockRequest bytes).toOption

/-- Attest a user in answer to the request in a form. -/
def attestReply (ctx : Ctx) (r : Req) (user : Store.User) (amr : List String) : IO Reply := do
  let .ok form := r.form | return oauthError "invalid_request" "the body must be a form"
  let some raw := lookupOnce form "request"
    | return oauthError "invalid_request" "request is required"
  let some request := decodeRequest raw
    | return oauthError "invalid_request" "request is not a third-party block request"
  let now ← ctx.clock
  let expires := now + ctx.config.attestationSeconds
  let (contents, key) ← attest ctx.store ctx.rootKey request user.name amr user.groups now expires
    (Acr.ofAmr amr).identifier
  Audit.log ctx r .tokenIssued .success (userName := some user.name) (detail := "kleis attestation")
  return noStore <| Reply.json <| Json.mkObj
    [("block", Json.str (LeanBiscuit.Base64.encode
        (LeanBiscuit.Proto.Schema.encodeThirdPartyBlockContents contents))),
     ("public_key", Json.str key.print), ("expires", (expires : Json))]

/-- `403`, for a sign-in below `kleisMinAcr`. -/
def levelTooLow (need : Acr) : Reply :=
  noStore <| Reply.error .forbidden "insufficient_acr"
    s!"a kleis attestation needs a sign-in at {need.identifier} or better"

/-- The level a token states, read as `mfa` for a token from before pyle
stated levels: every session then was at least that. -/
def tokenLevel (identity : Identity) : Acr :=
  (identity.acr.bind Acr.ofIdentifier?).getD .mfa

/-- `POST /kleis/attest`, with a pyle access token. -/
def attestBearer : Handler := fun ctx r => do
  match ← bearerUser ctx r with
  | .error reply => return reply
  | .ok (u, identity) =>
    unless identity.scopes.contains kleisScope do
      return (noStore (Reply.error .forbidden "insufficient_scope"
        "the access token was not granted the kleis scope")).withHeader "WWW-Authenticate"
        "Bearer realm=\"pyle\", error=\"insufficient_scope\", scope=\"kleis\""
    unless (tokenLevel identity).satisfies ctx.config.kleisMinAcr do
      return levelTooLow ctx.config.kleisMinAcr
    attestReply ctx r u identity.amr

/-- `POST /kleis/attest/session`, from a signed-in browser. -/
def attestSession : Handler := fun ctx r => do
  let some s ← Session.current ctx r
    | return Reply.error .unauthorized "login_required" "sign in first"
  let some u ← ctx.store.findUser s.user
    | return Reply.error .unauthorized "login_required" "sign in first"
  unless s.level.satisfies ctx.config.kleisMinAcr do return levelTooLow ctx.config.kleisMinAcr
  attestReply ctx r u s.amr

end Token
end Pyle