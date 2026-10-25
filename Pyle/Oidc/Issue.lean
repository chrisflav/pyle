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
user at a client, and answer with them and the refresh token `refresh`. -/
def tokenResponse (ctx : Ctx) (r : Req) (client : Store.Client) (user : Store.User)
    (scope : String) (amr : List String) (authTime : Nat) (nonce : Option String)
    (refresh : Option String) (grant : String) : IO Reply := do
  let now ← ctx.clock
  let expires := now + ctx.config.accessTokenSeconds
  let access ← Token.issue ctx.store ctx.rootKey
    { user := user.name, amr, authTime, groups := user.groups, client := client.id,
      audience := [client.id, Token.pyleAudience], scopes := words scope } now expires
  let idToken ← if (words scope).contains "openid" then
      let settings := (← ctx.store.clientSettings client.id).getD {}
      let claims := idTokenClaims ctx.config.issuer client.id user amr (some authTime) nonce now
        (now + ctx.config.idTokenSeconds)
      some <$> signIdToken ctx.store ctx.rootKey settings claims now
    else pure none
  Audit.log ctx r .tokenIssued .success (userName := some user.name)
    (detail := s!"{grant} for {client.id}")
  return noStore <| Reply.json <| Json.mkObj <|
    [("access_token", Json.str access), ("token_type", "Bearer"),
     ("expires_in", (ctx.config.accessTokenSeconds : Json)), ("scope", Json.str scope)] ++
    (idToken.map fun t => [("id_token", Json.str t)]).getD [] ++
    (refresh.map fun t => [("refresh_token", Json.str t)]).getD []

/-- Start a refresh-token family for a grant and return its first token. -/
def startRefresh (ctx : Ctx) (family : ByteArray) (client : Store.Client) (user : Store.User)
    (scope : String) (amr : List String) (authTime : Nat) : IO String := do
  let now ← ctx.clock
  let token ← randomToken
  ctx.store.startRefreshFamily (tokenHash token)
    { family, clientId := client.id, user := user.id, scope, amr, authTime,
      expires := now + ctx.config.refreshTokenSeconds } now
  return token

end Oidc
end Pyle