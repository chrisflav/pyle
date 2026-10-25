import PyleTests.Oidc

/-!
# Biscuits

The access tokens `/token` issues, verified as a service verifies them
(`Pyle.Token.Verify`): their authority block, the audience and expiry checks,
attenuation by a holder, rotation of the root key, and the kleis attestation
of a user in a third-party block.

The root key signs through OpenSSL; every token here is read back with
`lean-biscuit`'s verifier, so each test is also the check DESIGN.md §6.2 asks
for, that the FFI signer's output verifies under the Lean verifier.
-/

namespace PyleTests

open Pyle Pyle.Http Pyle.Oidc
open LeanBiscuit LeanBiscuit.Token
open Lean (Json)

/-- Sign a user in and take an access token for `app` from `/token`. -/
def accessToken (ctx : Ctx) (cookie secret : String) : IO String := do
  let t ← exchange ctx (← obtainCode ctx cookie) secret
  return (jsonStr t "access_token").getD ""

/-- Access tokens and their verification. -/
def accessTokenTests : IO Unit := withCtx fun ctx clock => do
  group "token: access tokens"
  let alice ← ctx.store.addUser "alice" ["admin", "ops"] 1
  let (secret, _) ← addClients ctx
  let cookie ← signIn ctx alice.id ["hwk", "user"]
  let access ← accessToken ctx cookie secret
  let roots ← Pyle.Token.publishedRoots ctx.store
  let now ← clock.get
  match Pyle.Token.verify roots "app" now access with
  | .error e => check "the access token verifies for its client" false e
  | .ok id =>
    check "the access token verifies for its client" true
    checkEq "user" id.user "alice"
    checkEq "amr" id.amr ["hwk", "user"]
    checkEq "groups" id.groups ["admin", "ops"]
    checkEq "client" id.client (some "app")
    checkEq "auth_time" id.authTime (some now)
    checkEq "scopes" id.scopes ["openid", "profile", "groups"]
  check "and for pyle" ((Pyle.Token.verify roots "pyle" now access) matches .ok _)
  check "not for another service"
    ((Pyle.Token.verify roots "orchestra" now access) matches .error _)
  check "not after it expires" ((Pyle.Token.verify roots "app"
    (now + ctx.config.accessTokenSeconds) access) matches .error _)
  check "not under another root key"
    ((Pyle.Token.verify [⟨.ed25519, ← Crypto.randomBytes 32⟩] "app" now access) matches .error _)
  -- The authority block, as datalog.
  let some b := (Biscuit.ofBase64 access (roots.headD default)).toOption
    | check "the token parses" false
  checkEq "one block" b.blockCount 1
  check "it can still be attenuated" (!b.isSealed)
  -- A service's own policy.
  check "a service policy can refuse"
    ((Pyle.Token.verify roots "app" now access "allow if group(\"finance\");") matches .error _)
  check "or allow" ((Pyle.Token.verify roots "app" now access "allow if group(\"ops\");")
    matches .ok _)
  -- Attenuation by the holder, as orchestra hands a task to an agent.
  let some narrowing := (BlockBuilder.code {}
    "check if audience(\"app\");\ncheck if pull_request(\"chrisflav/kleis\", 7);").toOption
    | check "the block parses" false
  let some attenuated := (b.append ⟨.ed25519, ← Crypto.randomBytes 32⟩ narrowing).toOption
    | check "attenuation" false
  let att := attenuated.toBase64
  check "the attenuated token still verifies where its checks hold"
    ((Pyle.Token.verify roots "app" now att
      "pull_request(\"chrisflav/kleis\", 7);\nallow if user($u);") matches .ok _)
  check "but not on another pull request"
    ((Pyle.Token.verify roots "app" now att
      "pull_request(\"chrisflav/kleis\", 8);\nallow if user($u);") matches .error _)
  check "nor for another audience the original allowed"
    ((Pyle.Token.verify roots "pyle" now att
      "pull_request(\"chrisflav/kleis\", 7);\nallow if user($u);") matches .error _)
  -- A block cannot claim to be someone else.
  let some impostor := (BlockBuilder.code {} "user(\"root\");\ngroup(\"finance\");").toOption
    | check "the block parses" false
  let some forged := (b.append ⟨.ed25519, ← Crypto.randomBytes 32⟩ impostor).toOption
    | check "appending" false
  match Pyle.Token.verify roots "app" now forged.toBase64 "allow if group(\"finance\");" with
  | .ok _ => check "facts of an appended block are not believed" false
  | .error _ => check "facts of an appended block are not believed" true
  checkEq "the identity is the authority block's" ((Pyle.Token.verify roots "app" now
    forged.toBase64).toOption.map (·.user)) (some "alice")
  -- Root key rotation: tokens under the previous key keep verifying.
  discard <| Keys.rotate ctx.store ctx.rootKey .biscuitRoot now
  discard <| Keys.rotate ctx.store ctx.rootKey .biscuitRoot now
  let roots ← Pyle.Token.publishedRoots ctx.store
  checkEq "three root keys are published" roots.length 3
  check "a token from before the rotation still verifies"
    ((Pyle.Token.verify roots "app" now access) matches .ok _)
  let fresh ← accessToken ctx cookie secret
  let (_, current) ← Keys.current ctx.store ctx.rootKey .biscuitRoot now
  check "a new one is signed by the new current key"
    ((Biscuit.ofBase64 fresh (Pyle.Token.rootPublicKey current)) matches .ok _)
  -- Datalog quoting.
  checkEq "quotes and backslashes are escaped" (Pyle.Token.quote "a\"b\\c\nd")
    "\"a\\\"b\\\\c\\nd\""
  match Parser.parseBlock s!"user({Pyle.Token.quote "x\"); check if false; user(\"y"});" with
  | .ok src => checkEq "a hostile name stays one fact" (src.facts.length, src.checks.length) (1, 0)
  | .error _ => check "a hostile name stays one fact" false

/-- The kleis attestation. -/
def attestTests : IO Unit := withCtx fun ctx clock => do
  group "token: kleis attestation"
  let alice ← ctx.store.addUser "alice" ["admin"] 1
  let (secret, _) ← addClients ctx
  let cookie ← signIn ctx alice.id ["hwk", "user"]
  let some agentSecret ← registerClient ctx.store "agent" "An agent" [appRedirect]
      ["openid", "kleis"] false {} 1
    | check "an agent client" false
  let code ← obtainCode ctx cookie "agent" (scope := "openid kleis")
  let access := (jsonStr (← exchange ctx code agentSecret (client := "agent")) "access_token"
    ).getD ""
  let ordinary ← accessToken ctx cookie secret
  let now ← clock.get
  let (_, pyleRoot) ← Keys.current ctx.store ctx.rootKey .biscuitRoot now
  let pyleKey := Pyle.Token.rootPublicKey pyleRoot
  -- A kleis token whose grant names alice through pyle; kleis's key is a test key.
  let kleisRoot : PrivateKey := ⟨.ed25519, ← Crypto.randomBytes 32⟩
  let some kleisPublic := kleisRoot.publicKey.toOption | check "a kleis key" false
  let some grant := (BlockBuilder.code {}
    s!"right(\"github\");\ncheck if user($u), \{\"alice\"}.contains($u) trusting {pyleKey.print};"
    ).toOption | check "the grant parses" false
  let some kleisToken := (Biscuit.create kleisRoot ⟨.ed25519, ← Crypto.randomBytes 32⟩ grant
    ).toOption | check "a kleis token" false
  let authorize (t : Token.Biscuit) : Bool :=
    match AuthorizerBuilder.code {} s!"time({Pyle.Token.date now});\nallow if right(\"github\");"
    with
    | .ok b => (Authorizer.authorizeToken b t).toOption.isSome
    | .error _ => false
  check "without the attestation the grant refuses" (!authorize kleisToken)
  let request := Base64.encode (Proto.Schema.encodeThirdPartyBlockRequest
    (Biscuit.thirdPartyRequest kleisToken))
  let attestWith (headers : List (String × String)) (path : String := "/kleis/attest")
      (cookie : Option String := none) :=
    postForm ctx path [("request", request)] headers cookie
  let r ← attestWith [("Authorization", s!"Bearer {access}")]
  checkEq "pyle attests with an access token" r.status.toCode 200
  checkEq "naming its key as a kleis grant does" (jsonStr r "public_key") (some pyleKey.print)
  let some contents := (jsonStr r "block").bind Base64.decode? |>.bind
      (Proto.Schema.decodeThirdPartyBlockContents · |>.toOption)
    | check "the block decodes" false
  let some withBlock := (kleisToken.appendThirdParty ⟨.ed25519, ← Crypto.randomBytes 32⟩
    contents).toOption | check "the block appends" false
  let some withBlock := (Biscuit.ofBytes withBlock.toBytes kleisPublic).toOption
    | check "the attested token verifies" false
  check "with the attestation the grant allows" (authorize withBlock)
  let late (t : Token.Biscuit) : Bool :=
    match AuthorizerBuilder.code {} s!"time({Pyle.Token.date (now + 3600)});\nallow if true;" with
    | .ok b => (Authorizer.authorizeToken b t).toOption.isSome
    | .error _ => false
  check "the attestation expires" (!late withBlock)
  -- Bound to that one token.
  let some other := (Biscuit.create kleisRoot ⟨.ed25519, ← Crypto.randomBytes 32⟩ grant).toOption
    | check "another token" false
  let moved := (other.appendThirdParty ⟨.ed25519, ← Crypto.randomBytes 32⟩ contents).toOption
  check "the block does not verify in another token" (moved.all fun t =>
    (Biscuit.ofBytes t.toBytes kleisPublic).toOption.isNone)
  -- The session form, and refusals.
  let r ← attestWith sameOrigin "/kleis/attest/session" (some cookie)
  checkEq "pyle attests for a signed-in browser" r.status.toCode 200
  let r ← attestWith [("Origin", "https://evil.example")] "/kleis/attest/session" (some cookie)
  checkEq "but not cross-site" r.status.toCode 403
  let r ← attestWith [] "/kleis/attest" (some cookie)
  checkEq "the bearer route ignores the session" r.status.toCode 401
  let r ← postForm ctx "/kleis/attest" [("request", "garbage")]
    [("Authorization", s!"Bearer {access}")]
  checkEq "a malformed request is refused" (jsonStr r "error") (some "invalid_request")
  let r ← attestWith [("Authorization", s!"Bearer {ordinary}")]
  checkEq "a token without the kleis scope is refused" r.status.toCode 403
  checkEq "insufficient_scope" (jsonStr r "error") (some "insufficient_scope")

/-- Biscuits. -/
def tokenTests : IO Unit := do
  accessTokenTests
  attestTests

end PyleTests