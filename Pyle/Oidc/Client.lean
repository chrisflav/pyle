import Pyle.Oidc.Common
import Pyle.Store.Protocols

/-!
# Clients

Registering OpenID Connect clients, and authenticating them at the token and
device-authorization endpoints.

A client is confidential, holding a secret, or public, holding none; PKCE is
required of both (DESIGN.md §5.1).  The secret is 32 random bytes shown once
when the client is registered; the store keeps its SHA-256, and a presented
secret is hashed and compared with `ctEqual`.

Three ways of authenticating are accepted (RFC 6749 §2.3, OpenID Connect Core
§9): `client_secret_basic` (HTTP Basic, with the identifier and secret each
form-encoded first), `client_secret_post` (both in the body), and `none` for
a public client, which only names itself with `client_id`.  A request using
more than one method is refused, as is a secret presented for a public client.
-/

namespace Pyle
namespace Oidc

open Http
open Store

/-- Whether a client identifier is acceptable: 1 to 64 characters from ASCII
letters, digits, `-`, `_` and `.`.  Identifiers appear in tokens, URLs and
datalog, and a narrow alphabet keeps each of those encodings trivial. -/
def validClientId (id : String) : Bool :=
  !id.isEmpty && id.length ≤ 64 &&
    id.all fun c => c.isAlphanum || c == '-' || c == '_' || c == '.'

/-- The host of an absolute URI, if it has an authority. -/
def uriHost (uri : String) : Option String := do
  let [_, rest] := uri.splitOn "://" | none
  let authority := (rest.splitOn "/").headD ""
  let authority := (authority.splitOn "?").headD ""
  let hostPort := ((authority.splitOn "@").getLast?).getD authority
  if hostPort.startsWith "[" then
    return ((hostPort.splitOn "]").headD "") ++ "]"
  return (hostPort.splitOn ":").headD ""

/-- Whether a redirect URI may be registered (RFC 6749 §3.1.2, RFC 8252): an
absolute URI with no fragment, and `http` only for the loopback interface.  A
private-use scheme (`com.example.app:/callback`) is accepted for native
clients. -/
def validRedirectUri (uri : String) : Bool :=
  let scheme := (uri.splitOn ":").headD ""
  !uri.contains '#' && !uri.any Char.isWhitespace && uri.contains ':' && !scheme.isEmpty &&
    scheme.all (fun c => c.isAlphanum || c == '+' || c == '-' || c == '.') &&
    (scheme.front.isAlpha) &&
    (scheme != "http" ||
      (uriHost uri).any fun h => h == "localhost" || h == "127.0.0.1" || h == "[::1]") &&
    (scheme != "https" || (uriHost uri).any (!·.isEmpty))

/-- The scopes a client gets when it is registered without naming any.  Not
`email`: a client that is to learn addresses is registered with it named
(`--scope email`), as `offline_access` and `kleis` are. -/
def defaultScopes : List String := ["openid", "profile", "groups"]

/-- Check what a client is registered or changed with: at least one redirect
URI, each of them and each post-logout address acceptable
(`validRedirectUri`), and scopes that include `openid` and are all ones pyle
knows (`scopesSupported`).  Throws the reason. -/
def checkClient (redirectUris postLogout scopes : List String) : IO Unit := do
  if redirectUris.isEmpty then throw (.userError "a client needs at least one redirect URI")
  for u in redirectUris ++ postLogout do
    unless validRedirectUri u do
      throw (.userError s!"'{u}' is not an acceptable redirect URI (absolute, no fragment, \
        http only for the loopback)")
  for s in scopes do
    unless scopesSupported.contains s do
      throw (.userError s!"'{s}' is not a scope pyle knows (it knows \
        {", ".intercalate scopesSupported})")
  unless scopes.contains "openid" do throw (.userError "a client's scopes include openid")

/-- The client and settings a registration stores, checked
(`validClientId`, `checkClient`, the ID-token algorithm), with its new
secret: none for a public client, and otherwise to be shown once, as only
its hash is stored.  No scopes means `defaultScopes`. -/
def newClient (id name : String) (redirectUris scopes : List String) (isPublic : Bool)
    (settings : ClientSettings) (now : Nat) : IO (Client × Option String) := do
  unless validClientId id do
    throw (.userError s!"'{id}' is not a valid client id (letters, digits, '-', '_', '.')")
  let scopes := if scopes.isEmpty then defaultScopes else scopes
  checkClient redirectUris settings.postLogoutRedirectUris scopes
  unless settings.idTokenAlg == "ES256" || settings.idTokenAlg == "RS256" do
    throw (.userError "ID tokens are signed with ES256 or RS256")
  let secret ← if isPublic then pure none else some <$> randomToken
  return ({ id, name, secretHash := secret.map tokenHash, redirectUris, scopes, created := now },
    secret)

/-- Register a client, or replace the one with the same identifier — what
`pyle client add` does, so that registering a client again gives it a new
secret.  Returns the new secret for a confidential client — to be shown
once, as it is stored only as a hash — and `none` for a public one. -/
def registerClient (store : Store) (id name : String) (redirectUris scopes : List String)
    (isPublic : Bool) (settings : ClientSettings) (now : Nat) : IO (Option String) := do
  let (client, secret) ← newClient id name redirectUris scopes isPublic settings now
  store.putClient client
  discard <| store.setClientSettings id settings
  return secret

/-- Register a client only if its id is not taken, checked as
`registerClient` checks it, the check and the insertion in one transaction
(`Store.addClient`): what the administration pages do, which never replace a
client.  `none` if the id is taken; otherwise the secret, as for
`registerClient`. -/
def addClient (store : Store) (id name : String) (redirectUris scopes : List String)
    (isPublic : Bool) (settings : ClientSettings) (now : Nat) : IO (Option (Option String)) := do
  let (client, secret) ← newClient id name redirectUris scopes isPublic settings now
  if ← store.addClient client settings then return some secret
  return none

/-- Change a registered client's name, redirect URIs, scopes, post-logout
addresses and minimum level, checked as `registerClient` checks them.  The
scopes are taken as given: no scopes is refused (they must include
`openid`), rather than read as the defaults.  Its id, secret and ID-token
algorithm stay, and so do the grants it holds: a scope taken away still
reaches refresh-token families granted before.  Whether the client exists. -/
def updateClient (store : Store) (id name : String)
    (redirectUris scopes postLogout : List String) (minAcr : Acr) : IO Bool := do
  checkClient redirectUris postLogout scopes
  store.updateClient id name redirectUris scopes postLogout minAcr

/-- How a request authenticated its client. -/
inductive ClientAuth where
  /-- With a secret, in the `Authorization` header or the body. -/
  | secret (basic : Bool)
  /-- A public client naming itself. -/
  | none
  deriving BEq

/-- Why client authentication failed: the OAuth error and its description, and
whether the request used HTTP Basic, in which case the reply must be `401` with
`WWW-Authenticate` (RFC 6749 §5.2). -/
structure ClientError where
  /-- `invalid_client` or `invalid_request`. -/
  code : String
  /-- For people. -/
  description : String
  /-- Whether the request used HTTP Basic. -/
  basic : Bool := false

/-- The reply for a client authentication failure. -/
def ClientError.reply (e : ClientError) : Reply :=
  if e.code == "invalid_client" then
    let r := oauthError e.code e.description .unauthorized
    if e.basic then r.withHeader "WWW-Authenticate" "Basic realm=\"pyle\"" else r
  else oauthError e.code e.description

/-- The identifier and secret of an `Authorization: Basic` header, each
form-decoded (RFC 6749 §2.3.1).  `none` if the header is not Basic or is
malformed. -/
def basicCredentials (header : String) : Option (String × String) := do
  let parts := (header.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
  let [scheme, encoded] := parts | none
  guard (scheme.toLower == "basic")
  let urlSafe := (encoded.map fun c => if c == '+' then '-' else if c == '/' then '_' else c)
  let unpadded := String.ofList (urlSafe.toList.filter (· != '='))
  let bytes ← Jose.b64urlDecode? unpadded
  let text ← String.fromUTF8? bytes
  match text.splitOn ":" with
  | id :: rest => return (← percentDecode id, ← percentDecode (":".intercalate rest))
  | [] => none

/-- Authenticate the client of a token or device-authorization request from
its `Authorization` header and form.  The client, and how it authenticated. -/
def authenticateClient (store : Store) (r : Req) (form : List (String × String)) :
    IO (Except ClientError (Client × ClientAuth)) := do
  let header := r.header "authorization"
  let bodyId := lookupOnce form "client_id"
  let bodySecret := lookupOnce form "client_secret"
  if (form.filter (·.1 == "client_id")).length > 1 ||
      (form.filter (·.1 == "client_secret")).length > 1 then
    return .error { code := "invalid_request", description := "a parameter is repeated" }
  let (id, secret, basic) ← match header with
    | some h =>
      match basicCredentials h with
      | some (id, secret) =>
        if bodySecret.isSome then
          return .error { code := "invalid_request",
                          description := "use one client authentication method" }
        if bodyId.any (· != id) then
          return .error { code := "invalid_request",
                          description := "client_id does not match the credentials" }
        pure (id, some secret, true)
      | none =>
        return .error { code := "invalid_client", description := "unsupported authorization" }
    | none =>
      match bodyId with
      | some id => pure (id, bodySecret, false)
      | none => return .error { code := "invalid_client", description := "no client given" }
  let fail := ClientError.mk "invalid_client" "client authentication failed" basic
  let some client ← store.findClient id | return .error fail
  match client.secretHash, secret with
  | some stored, some s =>
    if Crypto.ctEqual stored.bytes (tokenHash s).bytes then return .ok (client, .secret basic)
    else return .error fail
  | none, none => return .ok (client, .none)
  | _, _ => return .error fail

end Oidc
end Pyle