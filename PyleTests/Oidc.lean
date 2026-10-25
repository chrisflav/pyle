import PyleTests.Web

/-!
# OpenID Connect

The provider end to end through `Server.route`, without a socket: discovery
and the JWKS, the authorization-code flow from `/authorize` to `/token` to
`/userinfo`, refresh-token rotation and reuse, and RP-initiated logout; then
the negatives — PKCE, redirect URIs, client authentication, prompts — and the
signing-key lifecycle.  ID tokens are verified with `Jwt.verify` against the
key the JWKS publishes.

Sessions are made through the sign-in endpoints (`signedIn`, `weakFor`): the
protocol endpoints only read them.
-/

namespace PyleTests

open Pyle Pyle.Http Pyle.Oidc
open Lean (Json)

/-- Comparing JSON in tests, by its compact form. -/
instance : BEq Json := ⟨fun a b => a.compress == b.compress⟩

/-- Comparing results in tests. -/
instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

/-- The issuer of the test configuration. -/
def issuer : String := "https://auth.example.org"

/-- The registered redirect URI of the test client. -/
def appRedirect : String := "https://app.example.org/cb"

/-- A session for `user`, signed in with a fresh passkey through the sign-in
endpoints (`sessionFor`): its `amr` is `["hwk", "user"]`.  The cookie value. -/
def signedIn (ctx : Ctx) (user : Store.User) : IO String :=
  return (← sessionFor ctx user).1

/-- A session for `user` that is not phishing-resistant: a security key without
user verification and a TOTP code, through `Policy.establish`.  Its `amr` is
`["hwk", "otp", "mfa"]` and its `acr` `mfa`.  The cookie value. -/
def weakFor (ctx : Ctx) (user : Store.User) : IO String := do
  let k ← SoftKey.new (uv := false)
  enrol ctx user k "no-uv key"
  let secret ← giveTotp ctx user
  let ch ← match ← SignIn.newChallenge ctx (Req.mk' .post "/") .authenticate none with
    | .ok ch => pure ch
    | .error _ => throw (.userError "weakFor: no challenge")
  let cred ← k.assert (SignIn.requestOptions ctx ch [] "discouraged")
  let resp ← IO.ofExcept (SignIn.parseAssertion cred)
  let .ok ca ← Policy.checkAssertion ctx .authenticate resp
    | throw (.userError "weakFor: the assertion was refused")
  let .ok totp ← Policy.checkTotp ctx user.id (totpAt secret (← ctx.clock))
    | throw (.userError "weakFor: the TOTP code was refused")
  let some sa := Policy.StrongAuthentication.ofFactors [ca.factor, totp]
    | throw (.userError "weakFor: the factors do not satisfy the policy")
  return (← Policy.establish ctx (Req.mk' .post "/") sa).2

/-- A `GET` through the server, with a session cookie if one is given. -/
def get (ctx : Ctx) (target : String) (cookie : Option String := none)
    (headers : List (String × String) := []) : IO Reply :=
  Server.route ctx (Req.mk' .get target
    ((cookie.map fun c => [("Cookie", s!"{sessionCookieName}={c}")]).getD [] ++ headers))

/-- A form `POST` through the server. -/
def postForm (ctx : Ctx) (path : String) (form : List (String × String))
    (headers : List (String × String) := []) (cookie : Option String := none) : IO Reply :=
  Server.route ctx (Req.mk' .post path
    ([("Content-Type", "application/x-www-form-urlencoded")] ++
      (cookie.map fun c => [("Cookie", s!"{sessionCookieName}={c}")]).getD [] ++ headers)
    (queryString form).toUTF8)

/-- The `Origin` header of a same-origin form. -/
def sameOrigin : List (String × String) := [("Origin", issuer)]

/-- The `Location` of a reply, or empty. -/
def location (r : Reply) : String := (r.header "location").getD ""

/-- The decoded query parameters of a URL. -/
def queryOf (url : String) : List (String × String) :=
  match url.splitOn "?" with
  | _ :: q :: _ => ((parseUrlEncoded q).getD [])
  | _ => []

/-- One query parameter of a URL. -/
def param (url name : String) : Option String := lookupOnce (queryOf url) name

/-- The JSON body of a reply, or `null`. -/
def bodyJson (r : Reply) : Json := (Json.parse r.bodyText).toOption.getD .null

/-- A string member of a reply's JSON body. -/
def jsonStr (r : Reply) (k : String) : Option String :=
  (bodyJson r).getObjValAs? String k |>.toOption

/-- HTTP Basic credentials. -/
def basic (id secret : String) : List (String × String) :=
  [("Authorization", "Basic " ++ LeanBiscuit.Base64.encode s!"{id}:{secret}".toUTF8 |>.map
    fun c => if c == '-' then '+' else if c == '_' then '/' else c)]

/-- A PKCE verifier and its challenge. -/
def pkce : String × String :=
  let v := "dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk"
  (v, Pkce.s256 v)

/-- An authorization request URL for `client` with the test PKCE challenge. -/
def authorizeUrl (client : String) (extra : List (String × String) := [])
    (redirect : String := appRedirect) (scope : String := "openid profile groups") : String :=
  "/authorize?" ++ queryString ([("response_type", "code"), ("client_id", client),
    ("redirect_uri", redirect), ("scope", scope), ("state", "st4te"),
    ("nonce", "n0nce"), ("code_challenge", pkce.2), ("code_challenge_method", "S256")] ++ extra)

/-- Register the test clients: `app`, confidential, with a logout URI; `cli`,
public; `legacy`, confidential with RS256 ID tokens.  The secrets of `app`
and `legacy`. -/
def addClients (ctx : Ctx) : IO (String × String) := do
  let some appSecret ← registerClient ctx.store "app" "The App" [appRedirect] [] false
      { postLogoutRedirectUris := ["https://app.example.org/bye"] } 1
    | throw (.userError "no secret")
  discard <| registerClient ctx.store "cli" "A CLI" ["http://127.0.0.1/cb"] [] true {} 1
  let some legacySecret ← registerClient ctx.store "legacy" "Legacy" [appRedirect] [] false
      { idTokenAlg := "RS256" } 1
    | throw (.userError "no secret")
  return (appSecret, legacySecret)

/-- Run an authorization request with a session and return the code. -/
def obtainCode (ctx : Ctx) (cookie : String) (client : String := "app")
    (extra : List (String × String) := []) (scope : String := "openid profile groups") :
    IO String := do
  let r ← get ctx (authorizeUrl client extra (scope := scope)) cookie
  return (param (location r) "code").getD ""

/-- Exchange a code with HTTP Basic client authentication. -/
def exchange (ctx : Ctx) (code secret : String) (client : String := "app")
    (verifier : String := pkce.1) (redirect : String := appRedirect) : IO Reply :=
  postForm ctx "/token" [("grant_type", "authorization_code"), ("code", code),
    ("redirect_uri", redirect), ("code_verifier", verifier)] (basic client secret)

/-- The compressed P-256 point of an EC JWK, as `Jwt.verify` takes it. -/
def jwkP256 (jwk : Json) : Option ByteArray := do
  let x ← (jwk.getObjValAs? String "x").toOption >>= Jose.b64urlDecode?
  let y ← (jwk.getObjValAs? String "y").toOption >>= Jose.b64urlDecode?
  guard (x.size == 32 && y.size == 32)
  let parity := (y.get! 31).toNat % 2
  return ⟨#[UInt8.ofNat (2 + parity)]⟩ ++ x

/-- The JWK the JWKS publishes under a `kid`. -/
def jwkFor (ctx : Ctx) (kid : String) : IO (Option Json) := do
  let r ← get ctx "/jwks"
  let .ok keys := (bodyJson r).getObjValAs? (Array Json) "keys" | return none
  return keys.find? fun k => k.getObjValAs? String "kid" == .ok kid

/-- Verify an ES256 ID token against the JWKS, by its `kid`. -/
def verifyEs256 (ctx : Ctx) (token : String) : IO (Except String Json) := do
  let some header := jwsHeader token | return .error "no header"
  let .ok kid := header.getObjValAs? String "kid" | return .error "no kid"
  let some jwk ← jwkFor ctx kid | return .error "the kid is not in the JWKS"
  let some key := jwkP256 jwk | return .error "not a P-256 JWK"
  return Jwt.verify .es256 key token

/-- Discovery and the JWKS. -/
def discoveryTests : IO Unit := withCtx fun ctx _ => do
  group "oidc: discovery"
  let r ← get ctx "/.well-known/openid-configuration"
  checkEq "discovery answers" r.status.toCode 200
  checkEq "the issuer" (jsonStr r "issuer") (some issuer)
  checkEq "the token endpoint" (jsonStr r "token_endpoint") (some s!"{issuer}/token")
  checkEq "the device endpoint" (jsonStr r "device_authorization_endpoint")
    (some s!"{issuer}/device_authorization")
  check "code flow only" ((bodyJson r).getObjVal? "response_types_supported" ==
    .ok (Json.arr #["code"]))
  check "S256 only" ((bodyJson r).getObjVal? "code_challenge_methods_supported" ==
    .ok (Json.arr #["S256"]))
  check "iss in the response"
    ((bodyJson r).getObjVal? "authorization_response_iss_parameter_supported" ==
      .ok (Json.bool true))
  check "no request objects" ((bodyJson r).getObjVal? "request_uri_parameter_supported" ==
    .ok (Json.bool false))
  let j ← get ctx "/jwks"
  let keys := ((bodyJson j).getObjValAs? (Array Json) "keys").toOption.getD #[]
  checkEq "the JWKS has an ES256 and an RS256 key"
    (keys.map (·.getObjValAs? String "alg" |>.toOption)) #[some "ES256", some "RS256"]
  check "every JWK is a public signing key" (keys.all fun k =>
    k.getObjValAs? String "use" == .ok "sig" && (k.getObjVal? "d").toOption.isNone)
  let b ← get ctx "/biscuit/keys"
  let bkeys := ((bodyJson b).getObjValAs? (Array Json) "keys").toOption.getD #[]
  check "the biscuit root key is published apart, as ed25519/<hex>" (bkeys.size == 1 &&
    bkeys.all fun k =>
      ((k.getObjValAs? String "public_key").toOption.getD "").startsWith "ed25519/")
  check "and not in the JWKS" (!keys.any fun k => k.getObjValAs? String "alg" == .ok "EdDSA")

/-- The whole authorization-code flow. -/
def codeFlowTests : IO Unit := withCtx fun ctx clock => do
  group "oidc: authorization-code flow"
  let alice ← ctx.store.addUser "alice" ["admin", "ops"] 1
  let (secret, _) ← addClients ctx
  -- Without a session, the browser is sent to sign in and back.
  let r ← get ctx (authorizeUrl "app")
  checkEq "no session: 303" r.status.toCode 303
  check "to sign in" ((location r).startsWith "/signin?")
  checkEq "and back to this very request" (param (location r) "return") (some (authorizeUrl "app"))
  -- Signed in, a code comes back.
  let cookie ← signedIn ctx alice
  let r ← get ctx (authorizeUrl "app") cookie
  checkEq "signed in: 303" r.status.toCode 303
  check "to the redirect URI" ((location r).startsWith (appRedirect ++ "?"))
  checkEq "with the state" (param (location r) "state") (some "st4te")
  checkEq "and iss (RFC 9207)" (param (location r) "iss") (some issuer)
  let some code := param (location r) "code" | check "a code" false
  -- The exchange.
  let t ← exchange ctx code secret
  checkEq "the code exchanges" t.status.toCode 200
  check "the token response is not cached" (hasHeader t "Cache-Control" "no-store" &&
    hasHeader t "Pragma" "no-cache")
  checkEq "Bearer" (jsonStr t "token_type") (some "Bearer")
  checkEq "the granted scope" (jsonStr t "scope") (some "openid profile groups")
  let some idToken := jsonStr t "id_token" | check "an ID token" false
  let some access := jsonStr t "access_token" | check "an access token" false
  let some refresh := jsonStr t "refresh_token" | check "a refresh token" false
  -- The ID token, verified against the JWKS.
  match ← verifyEs256 ctx idToken with
  | .error e => check "the ID token verifies against the JWKS" false e
  | .ok claims =>
    check "the ID token verifies against the JWKS" true
    let now ← clock.get
    let str (k : String) := (claims.getObjValAs? String k).toOption
    let nat (k : String) := (claims.getObjValAs? Nat k).toOption
    checkEq "iss" (str "iss") (some issuer)
    checkEq "aud" (str "aud") (some "app")
    checkEq "sub is the user handle, not the name" (str "sub")
      (some (Jose.b64urlEncode alice.handle))
    checkEq "nonce" (str "nonce") (some "n0nce")
    checkEq "iat" (nat "iat") (some now)
    checkEq "exp" (nat "exp") (some (now + ctx.config.idTokenSeconds))
    checkEq "auth_time" (nat "auth_time") (some now)
    checkEq "name" (str "name") (some "alice")
    check "groups" (claims.getObjVal? "groups" == .ok (Json.arr #["admin", "ops"]))
    check "amr" (claims.getObjVal? "amr" == .ok (Json.arr #["hwk", "user"]))
    checkEq "acr" (str "acr") (some "phr")
  check "a tampered ID token does not verify"
    ((← verifyEs256 ctx (idToken.dropEnd 2 |>.toString)) matches .error _)
  -- userinfo, with the access token.
  let u ← get ctx "/userinfo" (headers := [("Authorization", s!"Bearer {access}")])
  checkEq "userinfo answers" u.status.toCode 200
  checkEq "userinfo's sub matches the ID token's" (jsonStr u "sub")
    (some (Jose.b64urlEncode alice.handle))
  checkEq "and the name" (jsonStr u "name") (some "alice")
  let u ← Server.route ctx (Req.mk' .post "/userinfo" [("Authorization", s!"Bearer {access}")])
  checkEq "POST /userinfo answers too" u.status.toCode 200
  let u ← get ctx "/userinfo"
  checkEq "no token: 401" u.status.toCode 401
  check "with a Bearer challenge" (hasHeader u "WWW-Authenticate" "Bearer realm=\"pyle\"")
  let u ← get ctx "/userinfo" (headers := [("Authorization", "Bearer bogus")])
  checkEq "a bad token: 401" u.status.toCode 401
  check "invalid_token" (hasHeader u "WWW-Authenticate"
    "Bearer realm=\"pyle\", error=\"invalid_token\"")
  -- Refresh rotation.
  clock.modify (· + 60)
  let refreshWith (rt : String) := postForm ctx "/token"
    [("grant_type", "refresh_token"), ("refresh_token", rt)] (basic "app" secret)
  let t2 ← refreshWith refresh
  checkEq "the refresh token rotates" t2.status.toCode 200
  let some refresh2 := jsonStr t2 "refresh_token" | check "a new refresh token" false
  check "to a new value" (refresh2 != refresh)
  match jsonStr t2 "id_token" with
  | none => check "an ID token on refresh" false
  | some it =>
    let claims := (← verifyEs256 ctx it).toOption.getD .null
    checkEq "the refreshed ID token keeps auth_time"
      (claims.getObjValAs? Nat "auth_time" |>.toOption) (some ((← clock.get) - 60))
    check "and has no nonce" (claims.getObjVal? "nonce" |>.toOption).isNone
  let narrowed ← postForm ctx "/token" [("grant_type", "refresh_token"),
    ("refresh_token", refresh2), ("scope", "openid")] (basic "app" secret)
  checkEq "a narrower scope may be asked for" (jsonStr narrowed "scope") (some "openid")
  let some refresh3 := jsonStr narrowed "refresh_token" | check "a third refresh token" false
  let wider ← postForm ctx "/token" [("grant_type", "refresh_token"),
    ("refresh_token", refresh3), ("scope", "openid admin")] (basic "app" secret)
  checkEq "a wider one is refused" (jsonStr wider "error") (some "invalid_scope")
  let reuse ← refreshWith refresh
  checkEq "reusing a refresh token is refused" (jsonStr reuse "error") (some "invalid_grant")
  let log ← Audit.entries ctx.store
  check "and audited" (log.any (·.event == "refresh-reuse"))
  let after ← refreshWith refresh3
  checkEq "and revokes the whole family" (jsonStr after "error") (some "invalid_grant")
  -- A code is good once, and a second use revokes what the first began.
  let code2 ← obtainCode ctx cookie
  let t3 ← exchange ctx code2 secret
  let some refresh4 := jsonStr t3 "refresh_token" | check "a refresh token" false
  let again ← exchange ctx code2 secret
  checkEq "a code is good once" (jsonStr again "error") (some "invalid_grant")
  checkEq "and its reuse revokes the tokens it gave" (jsonStr (← refreshWith refresh4) "error")
    (some "invalid_grant")
  -- Codes expire after 60 seconds.
  let code3 ← obtainCode ctx cookie
  clock.modify (· + 61)
  checkEq "an expired code is refused" (jsonStr (← exchange ctx code3 secret) "error")
    (some "invalid_grant")
  -- client_secret_post, and a public client with PKCE alone.
  let code4 ← obtainCode ctx cookie
  let t4 ← postForm ctx "/token" [("grant_type", "authorization_code"), ("code", code4),
    ("redirect_uri", appRedirect), ("code_verifier", pkce.1), ("client_id", "app"),
    ("client_secret", secret)]
  checkEq "client_secret_post" t4.status.toCode 200
  let code5 ← obtainCode ctx cookie "cli" [("redirect_uri", "http://127.0.0.1/cb")]
  let r5 ← get ctx (authorizeUrl "cli" (redirect := "http://127.0.0.1/cb")) cookie
  let code5 := if code5.isEmpty then (param (location r5) "code").getD "" else code5
  let t5 ← postForm ctx "/token" [("grant_type", "authorization_code"), ("code", code5),
    ("redirect_uri", "http://127.0.0.1/cb"), ("code_verifier", pkce.1), ("client_id", "cli")]
  checkEq "a public client authenticates with none" t5.status.toCode 200
  -- A disabled account gets nothing more.
  let code6 ← obtainCode ctx cookie
  discard <| ctx.store.setUserDisabled alice.id true
  checkEq "a disabled account's code is refused" (jsonStr (← exchange ctx code6 secret) "error")
    (some "invalid_grant")
  checkEq "and its access token no longer reads userinfo"
    (← get ctx "/userinfo" (headers := [("Authorization", s!"Bearer {access}")])).status.toCode 401

/-- What `/authorize` and `/token` refuse. -/
def negativeTests : IO Unit := withCtx fun ctx _ => do
  group "oidc: refusals"
  let alice ← ctx.store.addUser "alice" [] 1
  let (secret, _) ← addClients ctx
  let cookie ← signedIn ctx alice
  -- The client and redirect URI are checked before anything is redirected.
  let r ← get ctx (authorizeUrl "nobody") cookie
  checkEq "an unknown client: 400" r.status.toCode 400
  check "and no redirect" (r.header "location").isNone
  let r ← get ctx (authorizeUrl "app" (redirect := "https://evil.example/cb")) cookie
  checkEq "an unregistered redirect URI: 400" r.status.toCode 400
  check "and no redirect there" (r.header "location").isNone
  let r ← get ctx (authorizeUrl "app" (redirect := appRedirect ++ "/")) cookie
  checkEq "redirect URIs compare byte for byte" r.status.toCode 400
  -- Then errors go back to the client, with state and iss.
  let errorOf (r : Reply) := param (location r) "error"
  let r ← get ctx ("/authorize?" ++ queryString [("response_type", "code"),
    ("client_id", "app"), ("redirect_uri", appRedirect), ("scope", "openid"), ("state", "s")])
    cookie
  checkEq "no PKCE: invalid_request" (errorOf r) (some "invalid_request")
  checkEq "with the state" (param (location r) "state") (some "s")
  checkEq "and iss" (param (location r) "iss") (some issuer)
  let r ← get ctx (authorizeUrl "app" [("code_challenge_method", "plain")]) cookie
  checkEq "plain PKCE is refused" (errorOf r) (some "invalid_request")
  let r ← get ctx (authorizeUrl "app" [("response_type", "token")]) cookie
  checkEq "a repeated parameter is refused" (errorOf r) (some "invalid_request")
  let r ← get ctx ("/authorize?" ++ queryString [("response_type", "token"),
    ("client_id", "app"), ("redirect_uri", appRedirect), ("scope", "openid"),
    ("code_challenge", pkce.2), ("code_challenge_method", "S256")]) cookie
  checkEq "the implicit flow is refused" (errorOf r) (some "unsupported_response_type")
  let r ← get ctx ("/authorize?" ++ queryString [("response_type", "code"),
    ("client_id", "app"), ("redirect_uri", appRedirect), ("scope", "profile"),
    ("code_challenge", pkce.2), ("code_challenge_method", "S256")]) cookie
  checkEq "a scope without openid is refused" (errorOf r) (some "invalid_scope")
  let r ← get ctx (authorizeUrl "app" [("request", "eyJ...")]) cookie
  checkEq "request objects are refused" (errorOf r) (some "request_not_supported")
  -- POST /authorize becomes a GET.
  let r ← postForm ctx "/authorize" (queryOf (authorizeUrl "app"))
    [("Origin", "https://app.example.org")]
  checkEq "POST /authorize is answered with a GET" (location r) (authorizeUrl "app")
  -- PKCE at the token endpoint.
  let code ← obtainCode ctx cookie
  checkEq "a wrong verifier is refused"
    (jsonStr (← exchange ctx code secret (verifier := "x" ++ (pkce.1.drop 1).toString)) "error")
    (some "invalid_grant")
  checkEq "and the code is gone after it" (jsonStr (← exchange ctx code secret) "error")
    (some "invalid_grant")
  let code ← obtainCode ctx cookie
  checkEq "a short verifier is refused" (jsonStr (← exchange ctx code secret (verifier := "abc"))
    "error") (some "invalid_grant")
  let code ← obtainCode ctx cookie
  checkEq "a different redirect_uri is refused"
    (jsonStr (← exchange ctx code secret (redirect := "https://app.example.org/other")) "error")
    (some "invalid_grant")
  let code ← obtainCode ctx cookie
  let r ← postForm ctx "/token" [("grant_type", "authorization_code"), ("code", code),
    ("redirect_uri", appRedirect), ("code_verifier", pkce.1), ("client_id", "cli")]
  checkEq "another client cannot redeem the code" (jsonStr r "error") (some "invalid_grant")
  -- Client authentication.
  let code ← obtainCode ctx cookie
  let r ← exchange ctx code "wrong-secret"
  checkEq "a wrong secret: 401" r.status.toCode 401
  checkEq "invalid_client" (jsonStr r "error") (some "invalid_client")
  check "with a Basic challenge" (hasHeader r "WWW-Authenticate" "Basic realm=\"pyle\"")
  let r ← postForm ctx "/token" [("grant_type", "authorization_code"), ("code", code),
    ("redirect_uri", appRedirect), ("code_verifier", pkce.1), ("client_id", "app")]
  checkEq "a confidential client without its secret" (jsonStr r "error") (some "invalid_client")
  let r ← postForm ctx "/token" [("grant_type", "authorization_code"), ("code", code),
    ("client_id", "cli"), ("client_secret", "anything")]
  checkEq "a public client with a secret" (jsonStr r "error") (some "invalid_client")
  let r ← postForm ctx "/token" [("grant_type", "authorization_code"), ("client_secret", secret)]
    (basic "app" secret)
  checkEq "two authentication methods at once" (jsonStr r "error") (some "invalid_request")
  let r ← postForm ctx "/token" [("grant_type", "password")] (basic "app" secret)
  checkEq "the password grant is not there" (jsonStr r "error") (some "unsupported_grant_type")
  let r ← Server.route ctx (Req.mk' .post "/token" [("Content-Type", "application/json")]
    "{}".toUTF8)
  checkEq "a JSON body is refused" (jsonStr r "error") (some "invalid_request")
  let r ← postForm ctx "/token" [("grant_type", "authorization_code")] (basic "app" secret)
    (cookie := some cookie)
  checkEq "the token endpoint ignores the session" (jsonStr r "error") (some "invalid_request")

/-- `prompt`, `max_age` and `acr_values`. -/
def promptTests : IO Unit := withCtx fun ctx clock => do
  group "oidc: prompt, max_age and acr"
  let alice ← ctx.store.addUser "alice" [] 1
  let (secret, legacySecret) ← addClients ctx
  let r ← get ctx (authorizeUrl "app" [("prompt", "none")])
  checkEq "prompt=none without a session: login_required" (param (location r) "error")
    (some "login_required")
  checkEq "sent to the client" ((location r).startsWith appRedirect) true
  let (cookie, key) ← sessionFor ctx alice
  clock.modify (· + 1000)
  -- prompt=login: a fresh authentication, and back without looping.
  let r ← get ctx (authorizeUrl "app" [("prompt", "login")]) cookie
  check "prompt=login sends to sign in" ((location r).startsWith "/signin?")
  checkEq "asking for a fresh authentication" (param (location r) "max_age") (some "0")
  let some back := param (location r) "return" | check "a way back" false
  check "the way back has no prompt" ((param back "prompt").isNone)
  checkEq "but the time of the request" (param back "pyle_auth_after")
    (some (toString (← clock.get)))
  let r ← get ctx back cookie
  check "until the user authenticates again, it still asks" ((location r).startsWith "/signin?")
  -- Sign-in takes a few seconds; the step-up goes through the real endpoints.
  clock.modify (· + 3)
  let some cookie := sessionCookieOf (← stepUpVia ctx key (some cookie))
    | check "the step-up succeeds" false
  let r ← get ctx back cookie
  check "afterwards the code comes" ((param (location r) "code").isSome)
  -- max_age=0 is prompt=login.
  clock.modify (· + 10)
  let r ← get ctx (authorizeUrl "app" [("max_age", "0")]) cookie
  checkEq "max_age=0 asks for a fresh authentication" (param (location r) "max_age") (some "0")
  let some back0 := param (location r) "return" | check "a way back" false
  check "and the way back has no max_age" (param back0 "max_age").isNone
  check "but pyle_auth_after" (param back0 "pyle_auth_after").isSome
  -- max_age: an old authentication is renewed, and the way back does not loop.
  clock.modify (· + 500)
  let r ← get ctx (authorizeUrl "app" [("max_age", "100"), ("prompt", "none")]) cookie
  checkEq "an old authentication with prompt=none: login_required" (param (location r) "error")
    (some "login_required")
  let r ← get ctx (authorizeUrl "app" [("max_age", "100")]) cookie
  checkEq "an old authentication with max_age goes to sign in" (param (location r) "max_age")
    (some "100")
  let some backAged := param (location r) "return" | check "a way back" false
  check "the way back drops max_age" (param backAged "max_age").isNone
  checkEq "for the time of the request" (param backAged "pyle_auth_after")
    (some (toString (← clock.get)))
  clock.modify (· + 2)
  let some cookie := sessionCookieOf (← stepUpVia ctx key (some cookie))
    | check "the step-up succeeds" false
  let r ← get ctx backAged cookie
  check "a sign-in that crossed a second boundary still gives a code"
    ((param (location r) "code").isSome)
  let r ← get ctx (authorizeUrl "app" [("max_age", "1000")]) cookie
  check "a recent enough one gives a code" ((param (location r) "code").isSome)
  checkEq "max_age must be a number" (param (location (← get ctx
    (authorizeUrl "app" [("max_age", "soon")]) cookie)) "error") (some "invalid_request")
  -- acr_values=phr.
  let weak ← weakFor ctx alice
  let r ← get ctx (authorizeUrl "app" [("acr_values", "phr")]) weak
  checkEq "acr_values=phr without a passkey goes to sign in with acr=phr"
    (param (location r) "acr") (some "phr")
  let r ← get ctx (authorizeUrl "app" [("acr_values", "phr")]) cookie
  check "with a passkey, a code" ((param (location r) "code").isSome)
  let code ← obtainCode ctx weak
  let t ← exchange ctx code secret
  let claims := (← verifyEs256 ctx ((jsonStr t "id_token").getD "")).toOption.getD .null
  checkEq "a security key without UV and TOTP is acr mfa"
    (claims.getObjValAs? String "acr").toOption (some "mfa")
  checkEq "with its amr" (claims.getObjVal? "amr" |>.toOption.map (·.compress))
    (some "[\"hwk\",\"otp\",\"mfa\"]")
  -- RS256 for the client that needs it.
  let code ← obtainCode ctx cookie "legacy"
  let t ← exchange ctx code legacySecret (client := "legacy")
  let token := (jsonStr t "id_token").getD ""
  let header := (jwsHeader token).getD .null
  checkEq "the RS256 client's ID token is RS256" (header.getObjValAs? String "alg").toOption
    (some "RS256")
  let kid := (header.getObjValAs? String "kid").toOption.getD ""
  let published ← Keys.published ctx.store .idTokenRs256
  match published.find? (·.kid == kid), ← jwkFor ctx kid with
  | some k, some jwk =>
    check "its key is in the JWKS" (jwk.getObjValAs? String "kty" == .ok "RSA")
    check "and verifies it" ((Jwt.verify .rs256 k.publicKey token) matches .ok _)
  | _, _ => check "its key is in the JWKS" false

/-- RP-initiated logout. -/
def rpLogoutTests : IO Unit := withCtx fun ctx _ => do
  group "oidc: logout"
  let alice ← ctx.store.addUser "alice" [] 1
  let (secret, _) ← addClients ctx
  let cookie ← signedIn ctx alice
  let t ← exchange ctx (← obtainCode ctx cookie) secret
  let idToken := (jsonStr t "id_token").getD ""
  let refresh := (jsonStr t "refresh_token").getD ""
  let bye := "https://app.example.org/bye"
  let q := queryString [("id_token_hint", idToken), ("post_logout_redirect_uri", bye),
    ("state", "x1")]
  let r ← get ctx s!"/end_session?{q}" cookie
  checkEq "with a session, logout asks first" r.status.toCode 200
  check "with a form to confirm"
    ((r.bodyText.splitOn "action=\"/end_session/confirm\"").length == 2)
  check "and the session is still there" ((← Session.current ctx (withCookie cookie)).isSome)
  let r ← postForm ctx "/end_session" (queryOf s!"/end_session?{q}")
    [("Origin", "https://app.example.org")]
  checkEq "a POST from the relying party becomes a GET" (location r) s!"/end_session?{q}"
  let r ← get ctx s!"/end_session?{queryString [("client_id", "app"),
    ("post_logout_redirect_uri", "https://evil.example/")]}" cookie
  checkEq "an unregistered return address is refused" r.status.toCode 400
  check "without redirecting" (r.header "location").isNone
  let r ← get ctx s!"/end_session?{queryString [("id_token_hint", idToken),
    ("client_id", "cli")]}" cookie
  checkEq "a client_id that is not the hint's audience is refused" r.status.toCode 400
  let r ← get ctx s!"/end_session?{queryString [("id_token_hint", "a.b.c")]}" cookie
  checkEq "a hint pyle did not sign is refused" r.status.toCode 400
  let crossSite ← postForm ctx "/end_session/confirm" [("client_id", "app")]
    [("Origin", "https://evil.example")] (cookie := some cookie)
  checkEq "a cross-site confirmation is refused" crossSite.status.toCode 403
  let r ← postForm ctx "/end_session/confirm" [("client_id", "app"),
    ("post_logout_redirect_uri", bye), ("state", "x1")] sameOrigin (cookie := some cookie)
  checkEq "confirming answers with a page, not a redirect (form-action 'self')"
    r.status.toCode 200
  check "which links back to the registered address with the state"
    ((r.bodyText.splitOn s!"href=\"{bye}?state=x1\"").length == 2)
  check "and clears the cookie" (hasHeader r "Set-Cookie" clearSessionCookie)
  check "the session is over" ((← Session.current ctx (withCookie cookie)).isNone)
  let rt ← postForm ctx "/token" [("grant_type", "refresh_token"), ("refresh_token", refresh)]
    (basic "app" secret)
  checkEq "and the client's refresh tokens are revoked" (jsonStr rt "error") (some "invalid_grant")
  let r ← get ctx s!"/end_session?{q}"
  checkEq "without a session, straight back" (location r) s!"{bye}?state=x1"

/-- Which claims a scope releases, and refresh-token families: their absolute
expiry, and their tie to the session. -/
def scopeAndFamilyTests : IO Unit := withCtx fun ctx clock => do
  group "oidc: scopes and refresh families"
  let alice ← ctx.store.addUser "alice" ["admin"] 1
  let (secret, _) ← addClients ctx
  let some offSecret ← registerClient ctx.store "offline" "Offline" [appRedirect]
      ["openid", "offline_access"] false {} 1
    | check "an offline client" false
  let (cookie, key) ← sessionFor ctx alice
  -- Scopes.
  let t ← exchange ctx (← obtainCode ctx cookie (scope := "openid")) secret
  let claims := (← verifyEs256 ctx ((jsonStr t "id_token").getD "")).toOption.getD .null
  check "without profile, no name" (claims.getObjVal? "name").toOption.isNone
  check "without groups, no groups" (claims.getObjVal? "groups").toOption.isNone
  let u ← get ctx "/userinfo"
    (headers := [("Authorization", s!"Bearer {(jsonStr t "access_token").getD ""}")])
  check "nor from userinfo" ((jsonStr u "name").isNone &&
    ((bodyJson u).getObjVal? "groups").toOption.isNone && (jsonStr u "sub").isSome)
  let t ← exchange ctx (← obtainCode ctx cookie (scope := "openid profile")) secret
  let claims := (← verifyEs256 ctx ((jsonStr t "id_token").getD "")).toOption.getD .null
  checkEq "profile releases the name" (claims.getObjValAs? String "name").toOption (some "alice")
  check "and only the name" (claims.getObjVal? "groups").toOption.isNone
  let d ← get ctx "/.well-known/openid-configuration"
  check "discovery offers offline_access"
    (((bodyJson d).getObjValAs? (Array String) "scopes_supported").toOption.getD #[]
      |>.contains "offline_access")
  checkEq "and the end-session endpoint" (jsonStr d "end_session_endpoint")
    (some s!"{issuer}/end_session")
  -- A family survives a step-up of its session.
  let refreshWith (rt client sec : String) := postForm ctx "/token"
    [("grant_type", "refresh_token"), ("refresh_token", rt)] (basic client sec)
  let bound := (jsonStr (← exchange ctx (← obtainCode ctx cookie) secret) "refresh_token").getD ""
  let offline := (jsonStr (← exchange ctx (← obtainCode ctx cookie "offline"
    (scope := "openid offline_access")) offSecret (client := "offline")) "refresh_token").getD ""
  let some cookie := sessionCookieOf (← stepUpVia ctx key (some cookie))
    | check "the step-up succeeds" false
  let r ← refreshWith bound "app" secret
  checkEq "a family survives its session's step-up" r.status.toCode 200
  let bound := (jsonStr r "refresh_token").getD ""
  -- Signing out ends the families tied to the session, not offline ones.
  let out ← Server.route ctx (withCookie cookie .post "/logout" sameOrigin)
  check "signing out works" (out.status.toCode < 400)
  checkEq "signing out revokes the session's family" (jsonStr (← refreshWith bound "app" secret)
    "error") (some "invalid_grant")
  let r ← refreshWith offline "offline" offSecret
  checkEq "but not an offline_access one" r.status.toCode 200
  -- The absolute expiry.
  let start ← clock.get
  let some rt := jsonStr r "refresh_token" | check "a token" false
  clock.set (start + ctx.config.refreshTokenSeconds - 10)
  let r ← refreshWith rt "offline" offSecret
  checkEq "rotating just before the family expires works" r.status.toCode 200
  let some rt := jsonStr r "refresh_token" | check "a token" false
  clock.set (start + ctx.config.refreshTokenSeconds + 1)
  checkEq "but rotation does not extend the family" (jsonStr (← refreshWith rt "offline"
    offSecret) "error") (some "invalid_grant")
  -- Unused codes are purged.
  let fresh ← signedIn ctx alice
  discard <| obtainCode ctx fresh
  clock.modify (· + codeSeconds + 1)
  Server.purge ctx
  checkEq "the purge removes codes never exchanged" ((← ctx.store.run fun c =>
    Store.query c "SELECT 1 FROM codes" #[] (Store.colInt · 0)).size) 0

/-- Signing keys: sealing, rotation, publication. -/
def keyTests : IO Unit := withCtx fun ctx clock => do
  group "oidc: signing keys"
  let alice ← ctx.store.addUser "alice" [] 1
  let (secret, _) ← addClients ctx
  let cookie ← signedIn ctx alice
  let now ← clock.get
  let (kid1, _) ← Keys.current ctx.store ctx.rootKey .idTokenEs256 now
  let stored := (← Keys.published ctx.store .idTokenEs256).toList
  check "one current key to begin with" (stored.map (·.state) == [.current])
  let some row := stored.head? | check "a row" false
  check "the private key is sealed, not stored" ((Keys.open ctx.rootKey row) matches .ok _)
  check "it does not open under another root key"
    ((Keys.open (← Crypto.randomBytes 32) row) matches .error _)
  check "nor moved to another kid" ((Keys.open ctx.rootKey { row with kid := "other" }) matches
    .error _)
  let kidOf (r : Reply) : String :=
    ((jwsHeader ((jsonStr r "id_token").getD "")).bind
      (·.getObjValAs? String "kid" |>.toOption)).getD ""
  checkEq "ID tokens are signed with it" (kidOf (← exchange ctx (← obtainCode ctx cookie) secret))
    kid1
  -- The first rotation only announces.
  let rot1 ← Keys.rotate ctx.store ctx.rootKey .idTokenEs256 (now + 1)
  checkEq "the first rotation promotes nothing" rot1.promoted none
  check "the next key is published at once" ((← jwkFor ctx rot1.announced).isSome)
  checkEq "but does not sign yet" (kidOf (← exchange ctx (← obtainCode ctx cookie) secret)) kid1
  -- The second promotes it.
  let rot2 ← Keys.rotate ctx.store ctx.rootKey .idTokenEs256 (now + 2)
  checkEq "the second promotes the announced key" rot2.promoted (some rot1.announced)
  let t ← exchange ctx (← obtainCode ctx cookie) secret
  checkEq "which now signs" (kidOf t) rot1.announced
  check "and verifies against the JWKS" ((← verifyEs256 ctx ((jsonStr t "id_token").getD ""))
    matches .ok _)
  check "the previous key stays published" ((← jwkFor ctx kid1).isSome)
  let es := (← Keys.published ctx.store .idTokenEs256).toList.map (·.state)
  check "next, current and previous" (es.length == 3 && es.contains .next && es.contains .current
    && es.contains .previous)
  -- The third retires the first.
  discard <| Keys.rotate ctx.store ctx.rootKey .idTokenEs256 (now + 3)
  check "a third rotation retires the oldest" ((← jwkFor ctx kid1).isNone)
  check "rotation leaves the other uses alone"
    ((← Keys.published ctx.store .idTokenRs256).all (·.state == .current))

/-- The OpenID Connect tests. -/
def providerTests : IO Unit := do
  discoveryTests
  codeFlowTests
  negativeTests
  promptTests
  rpLogoutTests
  scopeAndFamilyTests
  keyTests

end PyleTests