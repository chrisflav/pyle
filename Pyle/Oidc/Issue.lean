import Pyle.Oidc.IdToken
import Pyle.Token.Biscuit
import Pyle.Audit

/-!
# Token responses

What every successful grant at `/token` answers (RFC 6749 §5.1, OpenID Connect
Core §3.1.3.3): an access token, which is a biscuit (DESIGN.md §5.2), its
lifetime, the granted scope, an ID token when the scope includes `openid`, and
a refresh token when the grant issued one.  The access token's audience is the
client and pyle itself, so that the client can present it at `/userinfo`.
-/

namespace Pyle
namespace Oidc

open Http
open Lean (Json)

/-- The family of the refresh tokens descending from an authorization code: a
function of the code, so that a code presented a second time can name the
family its first use began and have it revoked (RFC 6749 §4.1.2). -/
def familyOfCode (codeHash : Store.SecretHash) : ByteArray :=
  LeanBiscuit.Sha256.hash ("pyle refresh family v1".toUTF8 ++ codeHash.bytes)

/-- Issue an access token, and an ID token if `openid` is in `scope`, for a
user at a client, and answer with them and the refresh token `refresh`.

The level of the sign-in is read back from its `amr` (`Acr.ofAmr`), and an
`amr` that reads as no level — which nothing pyle writes does — is refused
with `invalid_grant` rather than given one; the access
token states it as `acr`, and the ID token too, unless the authorization asked
for an essential `acr` claim, whose answer is `acrClaim`.  Both state the
account's own strongest level, read afresh, as `account_acr` and
`pyle_account_acr`. -/
def tokenResponse (ctx : Ctx) (r : Req) (client : Store.Client) (user : Store.User)
    (scope : String) (amr : List String) (authTime : Nat) (nonce : Option String)
    (refresh : Option String) (grant : String) (acrClaim : Option String := none) :
    IO Reply := do
  let now ← ctx.clock
  let expires := now + ctx.config.accessTokenSeconds
  let some level := Acr.ofAmr amr
    | return oauthError "invalid_grant" "the sign-in behind this grant states no level"
  let account ← Policy.accountLevel ctx user.id
  let access ← Token.issue ctx.store ctx.rootKey
    { user := user.name, subject := some (subjectOf user), amr, acr := level.identifier, accountAcr := account.map (·.identifier),
      authTime, groups := user.groups, client := client.id,
      audience := [client.id, Token.pyleAudience], scopes := words scope } now expires
  let idToken ← if (words scope).contains "openid" then
      let settings := (← ctx.store.clientSettings client.id).getD {}
      let claims := idTokenClaims ctx.config.issuer client.id user (words scope) amr
        (acrClaim.getD level.identifier) account (some authTime) nonce now
        (now + ctx.config.idTokenSeconds)
      some <$> signIdToken ctx.store ctx.rootKey settings claims now
    else pure none
  Audit.log ctx r .tokenIssued .success (userName := some user.name)
    (detail := s!"{grant} for {client.id}, acr {level.identifier}")
  return noStore <| Reply.json <| Json.mkObj <|
    [("access_token", Json.str access), ("token_type", "Bearer"),
     ("expires_in", (ctx.config.accessTokenSeconds : Json)), ("scope", Json.str scope)] ++
    (idToken.map fun t => [("id_token", Json.str t)]).getD [] ++
    (refresh.map fun t => [("refresh_token", Json.str t)]).getD []

/-- The scope that unties a refresh-token family from the browser session. -/
def offlineAccess : String := "offline_access"

/-- Start a refresh-token family for a grant and return its first token.

The family expires `refreshTokenSeconds` from now however often it is
rotated.  Unless the scope includes `offline_access`, it is tied to `session`,
the pyle session the grant came from, and is revoked when that session ends —
by sign-out, from the account page, by being replaced, or by expiring. -/
def startRefresh (ctx : Ctx) (family : ByteArray) (client : Store.Client) (user : Store.User)
    (scope : String) (amr : List String) (authTime : Nat) (session : Option Store.SecretHash)
    (acr : Option String := none) : IO String := do
  let now ← ctx.clock
  let token ← randomToken
  let expires := now + ctx.config.refreshTokenSeconds
  ctx.store.startRefreshFamily (tokenHash token)
    { family, clientId := client.id, user := user.id, scope, amr, authTime, expires, acr } now
  let tie := if (words scope).contains offlineAccess then none else session
  ctx.store.addRefreshFamily family expires tie now
  return token

end Oidc
end Pyle