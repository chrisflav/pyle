import PyleTests.ForwardAuth

/-!
# Assurance levels

What each level is worth to the services behind pyle (DESIGN.md §1, §5): the
default `mfa` floor sends a single-factor session to step up, and a client or
a protected host can ask for more or opt down; `acr_values` and the `claims`
parameter are read in order, with their aliases, ignoring what pyle does not
know; `prompt=none` answers `login_required` or `interaction_required`; the ID
token, the access token, `/userinfo` and the forward-auth policy all state the
session's level and the account's strongest one; the device grant still
needs `phr`; and a change to the account needs the level its own factors
allow, or `mfa`.

Single-factor sessions are made here as everywhere, through a checked factor:
`sfaFor` signs in with a security key touched without user verification,
through `Policy.checkAssertion` and `Policy.establish`.
-/

namespace PyleTests

open Pyle Pyle.Http Pyle.Oidc
open Lean (Json)

/-- A session for `user` at `sfa`: a fresh security key that does not verify
the user, alone.  The cookie value. -/
def sfaFor (ctx : Ctx) (user : Store.User) : IO String := do
  let k ← SoftKey.new (uv := false)
  enrol ctx user k "touch-only key"
  let ch ← match ← SignIn.newChallenge ctx (Req.mk' .post "/") .authenticate none with
    | .ok ch => pure ch
    | .error _ => throw (.userError "sfaFor: no challenge")
  let cred ← k.assert (SignIn.requestOptions ctx ch [] "discouraged")
  let resp ← IO.ofExcept (SignIn.parseAssertion cred)
  let .ok ca ← Policy.checkAssertion ctx .authenticate resp
    | throw (.userError "sfaFor: the assertion was refused")
  let some a := Policy.Authentication.ofFactors [ca.factor]
    | throw (.userError "sfaFor: no authentication")
  return (← Policy.establish ctx (Req.mk' .post "/") a).2

/-- The claims of a verified ID token from a token response, or `null`. -/
def idClaims (ctx : Ctx) (t : Reply) : IO Json :=
  return (← verifyEs256 ctx ((jsonStr t "id_token").getD "")).toOption.getD .null

/-- A string claim. -/
def claimStr (claims : Json) (k : String) : Option String := (claims.getObjValAs? String k).toOption

/-- Levels through OpenID Connect. -/
def oidcAssuranceTests : IO Unit := withCtx fun ctx _ => do
  group "assurance: OpenID Connect"
  let alice ← ctx.store.addUser "alice" [] 1
  let (secret, _) ← addClients ctx
  let d := bodyJson (← get ctx "/.well-known/openid-configuration")
  check "discovery lists the four levels" (d.getObjVal? "acr_values_supported" ==
    .ok (Json.arr #["https://refeds.org/profile/sfa", "https://refeds.org/profile/mfa", "phr",
      "phrh"]))
  check "and supports the claims parameter"
    (d.getObjVal? "claims_parameter_supported" == .ok (Json.bool true))
  check "and names the account claim"
    (((d.getObjValAs? (List String) "claims_supported").toOption.getD []).contains
      "pyle_account_acr")
  -- The default floor.
  let sfa ← sfaFor ctx alice
  let r ← get ctx (authorizeUrl "app") sfa
  check "an sfa session is sent to sign in" ((location r).startsWith "/signin?")
  checkEq "for mfa, the default floor" (param (location r) "acr") (some "mfa")
  checkEq "and back to the request" (param (location r) "return") (some (authorizeUrl "app"))
  let page ← get ctx ((location r).drop 0 |>.toString) sfa
  check "where the sign-in page steps the session up"
    (containsStr page.bodyText "data-mode=\"stepup\"" &&
      containsStr page.bodyText "data-acr=\"mfa\"")
  let r ← get ctx (authorizeUrl "app" [("prompt", "none")]) sfa
  checkEq "under prompt=none: interaction_required" (param (location r) "error")
    (some "interaction_required")
  let r ← get ctx (authorizeUrl "app" [("acr_values", "https://refeds.org/profile/sfa")]) sfa
  checkEq "asking for sfa does not lower the floor" (param (location r) "acr") (some "mfa")
  -- Per-client minimums.
  let some kioskSecret ← registerClient ctx.store "kiosk" "Kiosk" [appRedirect] [] false
      { minAcr := .sfa } 1
    | check "kiosk registers" false
  let some vaultSecret ← registerClient ctx.store "vault" "Vault" [appRedirect] [] false
      { minAcr := .phr } 1
    | check "vault registers" false
  checkEq "the minimum is stored" ((← ctx.store.clientSettings "vault").map (·.minAcr))
    (some .phr)
  let code ← obtainCode ctx sfa "kiosk"
  let claims ← idClaims ctx (← exchange ctx code kioskSecret (client := "kiosk"))
  checkEq "a client that opts down to sfa takes the session"
    (claimStr claims "acr") (some "https://refeds.org/profile/sfa")
  checkEq "with its amr" (claims.getObjVal? "amr" |>.toOption.map (·.compress))
    (some "[\"hwk\"]")
  checkEq "and the account's own level" (claimStr claims "pyle_account_acr")
    (some "https://refeds.org/profile/sfa")
  let weak ← weakFor ctx alice
  let r ← get ctx (authorizeUrl "vault") weak
  checkEq "a client with phr as its minimum sends an mfa session to sign in"
    (param (location r) "acr") (some "phr")
  check "the default client takes it" (param (location (← get ctx (authorizeUrl "app") weak))
    "code").isSome
  -- acr_values: in order of preference, with aliases, unknown values ignored.
  for (values, want) in [("gold phr", "phr"), ("phrh phr", "phr"), ("phr phrh", "phr"),
      ("https://refeds.org/profile/mfa/phr", "phr"), ("phrh", "phrh")] do
    let r ← get ctx (authorizeUrl "app" [("acr_values", values)]) weak
    checkEq s!"acr_values={values} sends an mfa session to sign in for {want}"
      (param (location r) "acr") (some want)
  for values in ["mfa", "https://refeds.org/profile/mfa", "gold", "phr mfa",
      "https://refeds.org/profile/sfa"] do
    let r ← get ctx (authorizeUrl "app" [("acr_values", values)]) weak
    check s!"acr_values={values} is met by an mfa session" (param (location r) "code").isSome
  let code ← obtainCode ctx weak "app" [("acr_values", "mfa")]
  checkEq "whose ID token states its own level"
    (claimStr (← idClaims ctx (← exchange ctx code secret)) "acr")
    (some "https://refeds.org/profile/mfa")
  -- A passkey session: phrh, and the account now reaches phrh.
  let cookie ← signedIn ctx alice
  let code ← obtainCode ctx cookie "vault" [("acr_values", "https://refeds.org/profile/mfa")]
  let t ← exchange ctx code vaultSecret (client := "vault")
  let claims ← idClaims ctx t
  checkEq "the ID token states the session's level, above what was asked"
    (claimStr claims "acr") (some "phrh")
  checkEq "and the account's" (claimStr claims "pyle_account_acr") (some "phrh")
  let access := (jsonStr t "access_token").getD ""
  let roots ← Token.publishedRoots ctx.store
  checkEq "the access token states both"
    ((Token.verify roots "vault" (← ctx.clock) access).toOption.map fun i => (i.acr, i.accountAcr))
    (some (some "phrh", some "phrh"))
  let u ← get ctx "/userinfo" (headers := [("Authorization", s!"Bearer {access}")])
  checkEq "and /userinfo the account's" (jsonStr u "pyle_account_acr") (some "phrh")
  -- The claims parameter.
  let essential (vs : List String) : String :=
    (Json.mkObj [("id_token", Json.mkObj [("acr", Json.mkObj [("essential", Json.bool true),
      ("values", Json.arr (vs.map Json.str).toArray)])])]).compress
  let code ← obtainCode ctx cookie "app"
    [("claims", essential ["https://refeds.org/profile/mfa", "phr"])]
  let t ← exchange ctx code secret
  checkEq "an essential acr is answered with the first value the session meets"
    (claimStr (← idClaims ctx t) "acr") (some "https://refeds.org/profile/mfa")
  let refreshed ← postForm ctx "/token"
    [("grant_type", "refresh_token"), ("refresh_token", (jsonStr t "refresh_token").getD "")]
    (basic "app" secret)
  checkEq "and still after a refresh" (claimStr (← idClaims ctx refreshed) "acr")
    (some "https://refeds.org/profile/mfa")
  let r ← get ctx (authorizeUrl "app" [("claims", essential ["phrh"])]) weak
  checkEq "an essential phrh sends an mfa session to sign in" (param (location r) "acr")
    (some "phrh")
  let r ← get ctx (authorizeUrl "app" [("claims", essential ["gold"])]) cookie
  checkEq "an essential acr pyle does not know is refused" (param (location r) "error")
    (some "unmet_authentication_requirements")
  let voluntary := (Json.mkObj [("id_token", Json.mkObj [("acr", Json.mkObj
    [("values", Json.arr #["phr"])])])]).compress
  let r ← get ctx (authorizeUrl "app" [("claims", voluntary), ("acr_values", "mfa")]) weak
  checkEq "the claims parameter takes the place of acr_values" (param (location r) "acr")
    (some "phr")
  let r ← get ctx (authorizeUrl "app" [("claims", "not json")]) cookie
  checkEq "a malformed claims parameter is refused" (param (location r) "error")
    (some "invalid_request")
  let r ← get ctx (authorizeUrl "app" [("claims", "{\"userinfo\":{}}")]) weak
  check "one that says nothing about acr changes nothing" (param (location r) "code").isSome
  -- prompt=none.
  let r ← get ctx (authorizeUrl "app" [("prompt", "none"), ("acr_values", "phr")]) weak
  checkEq "prompt=none with too low a level: interaction_required" (param (location r) "error")
    (some "interaction_required")
  let r ← get ctx (authorizeUrl "app" [("prompt", "none"), ("acr_values", "phr")]) cookie
  check "and with a level that is high enough, a code" (param (location r) "code").isSome

/-- The levels as functions: the order, reading identifiers and the `amr`. -/
def acrTests : IO Unit := do
  group "assurance: levels"
  checkEq "lowest first" (Acr.all.map (·.rank)) [0, 1, 2, 3]
  for a in Acr.all do
    check s!"{a} is read back" (Acr.ofIdentifier? a.identifier == some a)
    check s!"{a.shortName} is read back" (Acr.ofName? a.shortName == some a)
    for b in Acr.all do
      check s!"{a} satisfies {b} exactly when it is at least as strong"
        (a.satisfies b == decide (b.rank ≤ a.rank))
  checkEq "the bare mfa is an alias" (Acr.ofIdentifier? "mfa") (some .mfa)
  checkEq "REFEDS phishing-resistant MFA is phr"
    (Acr.ofIdentifier? "https://refeds.org/profile/mfa/phr") (some .phr)
  checkEq "the short sfa is for people only" (Acr.ofIdentifier? "sfa", Acr.ofName? "sfa")
    (none, some .sfa)
  checkEq "an unknown value is none" (Acr.ofIdentifier? "gold") none
  checkEq "the weakest value named"
    ((acrValuesRequest "phrh gold https://refeds.org/profile/mfa").level) (some .mfa)
  checkEq "no value named" (acrValuesRequest "gold").level none
  checkEq "an essential claim answers in the order given"
    ({ values := [("phrh", .phrh), ("phr", .phr)], essential := true : AcrRequest }.claim .phr)
    (some "phr")
  checkEq "a voluntary one does not"
    ({ values := [("phr", .phr)] : AcrRequest }.claim .phrh) none
  -- The account-change rule.
  for (c, need) in [(({ password := true } : Acr.Capabilities), Acr.sfa),
      ({ webauthn := true }, .sfa), ({ webauthn := true, totp := true }, .mfa),
      ({ verifying := true, webauthn := true }, .mfa),
      ({ verifyingDeviceBound := true, verifying := true, webauthn := true }, .mfa),
      ({ totp := true }, .mfa), ({}, .mfa)] do
    check s!"a change to {repr c} needs {need}" (c.changeLevel == need)

/-- A change to the account needs the level its own factors allow, or `mfa`. -/
def accountChangeTests : IO Unit :=
    withSignInCtx (fun c => { c with allowPasswords := true }) fun ctx _ => do
  group "assurance: changes to the account"
  -- An account with only a password manages itself with it.
  let pia ← ctx.store.addUser "pia" [] 1
  ctx.store.setPassword pia.id (← Factor.Password.hash "correct horse battery") 1
  let s ← postJson ctx "/signin/codes"
    (Json.mkObj [("name", "pia"), ("password", "correct horse battery")])
  let some pid := sessionCookieOf s | check "pia signs in" false
  let b ← postJson ctx "/account/authenticators/register/begin" emptyObj (some pid)
  checkEq "a password-only account adds a passkey with its password" b.status.toCode 200
  let k ← SoftKey.new
  let f ← postJson ctx "/account/authenticators/register/finish"
    (Json.mkObj [("credential", ← k.create (replyJson b))]) (some pid)
  checkEq "and the passkey is registered" f.status.toCode 201
  check "verifying the user" ((← ctx.store.listCredentials pia.id).toList.map (·.userVerified)
    == [true])
  let again ← postJson ctx "/account/authenticators/register/begin" emptyObj (some pid)
  checkEq "now that it has a passkey, the password alone is no longer enough"
    (again.status.toCode, errorOf again, jstr (replyJson again) "acr")
    (403, "step_up_required", "mfa")
  let rm ← postJson ctx "/account/password/remove" emptyObj (some pid)
  checkEq "nor for removing the password" rm.status.toCode 403
  -- The password of an account that has nothing else stays.
  let quin ← ctx.store.addUser "quin" [] 1
  ctx.store.setPassword quin.id (← Factor.Password.hash "correct horse battery") 1
  let qs ← postJson ctx "/signin/codes"
    (Json.mkObj [("name", "quin"), ("password", "correct horse battery")])
  let some qid := sessionCookieOf qs | check "quin signs in" false
  let last ← postJson ctx "/account/password/remove" emptyObj (some qid)
  checkEq "the password of an account with nothing else cannot be removed"
    (last.status.toCode, errorOf last) (409, "last_way_in")
  -- An account with two factors needs two.
  let ray ← ctx.store.addUser "ray" [] 1
  let (rid, _) ← sessionFor ctx ray
  discard <| giveTotp ctx ray
  let sfa ← sfaFor ctx ray
  let r ← postJson ctx "/account/recovery-codes" emptyObj (some sfa)
  checkEq "an account with a passkey refuses an sfa session"
    (r.status.toCode, jstr (replyJson r) "acr") (403, "mfa")
  let r ← postJson ctx "/account/recovery-codes" emptyObj (some rid)
  checkEq "and takes a passkey's" r.status.toCode 200
  let page ← getPage ctx "/account" (some rid)
  check "whose page says it is well protected"
    (containsStr page.bodyText "<p id=\"safety\">This account can sign in with a security key \
      that verifies you and keeps its key on the device")
  check "and knows it has a passkey" (containsStr page.bodyText "data-passkey=\"true\"")

/-- The device grant still needs `phr`, and its tokens state the level. -/
def deviceAssuranceTests : IO Unit := withCtx fun ctx clock => do
  group "assurance: the device grant"
  let alice ← ctx.store.addUser "alice" [] 1
  discard <| addClients ctx
  let r ← deviceCodes ctx
  let deviceCode := (jsonStr r "device_code").getD ""
  let userCode := (jsonStr r "user_code").getD ""
  let page := s!"/device?{queryString [("user_code", userCode)]}"
  let sfa ← sfaFor ctx alice
  checkEq "an sfa session is sent to sign in for phr" (param (location (← get ctx page sfa)) "acr")
    (some "phr")
  let weak ← weakFor ctx alice
  checkEq "and so is an mfa one" (param (location (← get ctx page weak)) "acr") (some "phr")
  let post ← postForm ctx "/device" [("user_code", userCode), ("decision", "approve")] sameOrigin
    (cookie := some weak)
  check "which cannot approve either" ((location post).startsWith "/signin?")
  let cookie ← signedIn ctx alice
  discard <| postForm ctx "/device" [("user_code", userCode), ("decision", "approve")] sameOrigin
    (cookie := some cookie)
  clock.modify (· + ctx.config.devicePollSeconds + 1)
  let t ← pollDevice ctx deviceCode
  let roots ← Token.publishedRoots ctx.store
  checkEq "the tokens state the approving session's level"
    ((Token.verify roots "cli" (← clock.get) ((jsonStr t "access_token").getD "")).toOption.map
      (·.acr)) (some (some "phrh"))
  checkEq "the ID token too" (claimStr (← idClaims ctx t) "acr") (some "phrh")

/-- Forward authentication: per-host minimums and the sign-in facts. -/
def forwardAuthAssuranceTests : IO Unit := withCtx fun ctx0 _ => do
  group "assurance: forward authentication"
  let base := withForwardAuth ctx0
  let ctx := { base with config := { base.config with
    forwardAuthHosts := base.config.forwardAuthHosts ++
      [("open.example.org", "allow if user($u);"),
       ("vault.example.org", "allow if amr(\"user\"), acr(\"phrh\");"),
       ("acct.example.org", "allow if account_acr(\"phrh\");")],
    forwardAuthMinAcr := [("open.example.org", .sfa), ("vault.example.org", .phr),
      ("acct.example.org", .sfa)] } }
  let alice ← ctx.store.addUser "alice" ["admin"] 1
  let sfa ← sfaFor ctx alice
  let some openCookie ← forwardSignIn ctx sfa "open.example.org" "/"
    | check "an sfa session reaches a host whose minimum is sfa" false
  checkEq "an sfa session reaches a host whose minimum is sfa"
    (← askProxy ctx "open.example.org" "/" (cookies := [openCookie])).status.toCode 200
  let begun ← askProxy ctx "app.example.org" "/"
  let g ← get ctx ((location begun).drop issuer.length |>.toString) sfa
  check "a plain policy has the mfa floor: the grant sends an sfa session to sign in"
    ((location g).startsWith "/signin?")
  checkEq "for mfa" (param (location g) "acr") (some "mfa")
  let raised := { ctx with config := { ctx.config with
    forwardAuthMinAcr := [("open.example.org", .mfa)] } }
  let r ← askProxy raised "open.example.org" "/x" (cookies := [openCookie])
  checkEq "a cookie whose session is below the host's minimum goes round the grant again"
    r.status.toCode 302
  check "to the grant" ((location r).startsWith s!"{issuer}/forward-auth/grant?")
  let r ← askProxy raised "open.example.org" "/x" "POST" (cookies := [openCookie])
  checkEq "and a POST is 401" r.status.toCode 401
  let weak ← weakFor ctx alice
  let begun ← askProxy ctx "vault.example.org" "/"
  let g ← get ctx ((location begun).drop issuer.length |>.toString) weak
  checkEq "a host whose minimum is phr sends an mfa session to sign in for phr"
    (param (location g) "acr") (some "phr")
  let cookie ← signedIn ctx alice
  let some vaultCookie ← forwardSignIn ctx cookie "vault.example.org" "/"
    | check "a passkey session reaches it" false
  checkEq "a policy over acr and amr lets a passkey session in"
    (← askProxy ctx "vault.example.org" "/" (cookies := [vaultCookie])).status.toCode 200
  let some acctCookie ← forwardSignIn ctx sfa "acct.example.org" "/"
    | check "an sfa session of an account with a passkey reaches acct" false
  checkEq "account_acr is the account's, not the session's"
    (← askProxy ctx "acct.example.org" "/" (cookies := [acctCookie])).status.toCode 200
  let bob ← ctx.store.addUser "bob" [] 1
  let bobSfa ← sfaFor ctx bob
  let g ← throughGrant ctx bobSfa "acct.example.org" "/"
  check "an account without one is refused" (forwardCookie g).isNone
  -- The configuration's two forms.
  let parse (hosts : String) := (Json.parse ("{\"issuer\":\"https://a.example\",\
    \"rpId\":\"a.example\",\"origins\":[\"https://a.example\"],\
    \"forwardAuthSecret\":\"0123456789abcdef\",\"forwardAuthHosts\":" ++ hosts ++ "}")).toOption
    |>.map (Config.ofJson · "/etc/pyle")
  match parse "{\"a.example\":\"allow if user($u);\",\
      \"b.example\":{\"policy\":\"allow if user($u);\",\"minAcr\":\"phr\"}}" with
  | some (.ok c) =>
    checkEq "both forms are read" (c.forwardAuthHosts.map (·.1)) ["a.example", "b.example"]
    check "with the minimum of the object form"
      (c.forwardAuthMinAcr == [("b.example", Acr.phr)])
  | _ => check "both forms are read" false
  for (bad, what) in [("{\"b.example\":{\"policy\":\"allow if user($u);\",\"minAcr\":\"gold\"}}",
        "an unknown level"),
      ("{\"b.example\":{\"minAcr\":\"phr\"}}", "an object without a policy"),
      ("{\"b.example\":{\"policy\":\"allow if user($u);\",\"min\":\"phr\"}}", "an unknown key"),
      ("{\"b.example\":7}", "a number")] do
    check s!"{what} is refused" (match parse bad with | some (.error _) => true | _ => false)

/-- The assurance tests. -/
def assuranceTests : IO Unit := do
  acrTests
  oidcAssuranceTests
  accountChangeTests
  deviceAssuranceTests
  forwardAuthAssuranceTests

end PyleTests