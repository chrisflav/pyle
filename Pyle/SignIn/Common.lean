import Pyle.Session.Policy
import Pyle.Audit
import Pyle.Crypto.X509

/-!
# What every sign-in endpoint shares

The JSON the browser and pyle exchange for a WebAuthn ceremony, the checks of
a `return` address, the rate limit, and the step-up window.

**The wire format.**  Every binary value travels as base64url without
padding.  The options pyle sends are shaped like the browser's own
`PublicKeyCredentialRequestOptions` and `…CreationOptions`, so the page's
script only has to turn the base64url fields into `ArrayBuffer`s.  What the
browser sends back is flat:

```
assertion:    {"id", "clientDataJSON", "authenticatorData", "signature", "userHandle"}
registration: {"id", "clientDataJSON", "attestationObject", "transports"}
```

**Where to go afterwards.**  A sign-in ends by sending the browser back to the
`return` address it came with, and an identity provider that redirects
anywhere it is told is a phishing tool.  `safeReturn` accepts only a path on
this origin: it starts with one `/`, its second character is neither `/` nor
`\` (browsers read both `//host` and `/\host` as another host), and it has no
backslash, control character or space anywhere.  `safeReturn_spec` states
that.
-/

namespace Pyle
namespace SignIn

open Http Store
open Lean (Json ToJson toJson)

/-! ## Return addresses -/

/-- Whether a character may appear in a return address: printable ASCII other
than space and backslash. -/
def returnChar (c : Char) : Bool := c.toNat > 0x20 && c.toNat < 0x7f && c != '\\'

/-- Whether a character list is a same-origin path: `/` first, then not `/`
or `\` (or nothing), and only `returnChar`s. -/
def returnPath : List Char → Bool
  | ['/'] => true
  | '/' :: c :: rest => c != '/' && c != '\\' && returnChar c && rest.all returnChar
  | _ => false

/-- The longest return address accepted. -/
def maxReturnLength : Nat := 2048

/-- A return address, if it is a path on this origin (see the module
documentation). -/
def safeReturn (s : String) : Option String :=
  if s.length ≤ maxReturnLength && returnPath s.toList then some s else none

/-- What `returnPath` accepts: `/`, then neither `/` nor `\`, and nothing but
`returnChar`s. -/
theorem returnPath_spec {cs : List Char} (h : returnPath cs = true) :
    ∃ rest, cs = '/' :: rest ∧ rest.head? ≠ some '/' ∧ rest.head? ≠ some '\\' ∧
      ∀ c ∈ rest, returnChar c = true := by
  unfold returnPath at h
  split at h
  · exact ⟨[], rfl, by simp, by simp, by simp⟩
  · rename_i c rest
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    refine ⟨c :: rest, rfl, by simpa using h.1.1.1, by simpa using h.1.1.2, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1.2
    · exact List.all_eq_true.mp h.2 x hx
  · cases h

/-- What `safeReturn` accepts: the address as given, starting with `/` and
not with `//` or `/\`, with no space, backslash or control character
anywhere. -/
theorem safeReturn_spec {s t : String} (h : safeReturn s = some t) :
    t = s ∧ ∃ rest, s.toList = '/' :: rest ∧ rest.head? ≠ some '/' ∧
      rest.head? ≠ some '\\' ∧ ∀ c ∈ rest, returnChar c = true := by
  unfold safeReturn at h
  split at h
  · rename_i hc
    cases h
    exact ⟨rfl, returnPath_spec ((Bool.and_eq_true _ _).mp hc).2⟩
  · cases h

/-- Where a sign-in goes when it was not given anywhere. -/
def defaultReturn : String := "/account"

/-! ## JSON -/

/-- A string member of a JSON object. -/
def strField (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption

/-- A base64url member, decoded. -/
def bytesField (j : Json) (k : String) : Except String ByteArray := do
  let some s := strField j k | throw s!"'{k}' is missing"
  let some b := Encoding.Base64Url.decode s | throw s!"'{k}' is not base64url"
  return b

/-- An assertion as the page posts it. -/
def parseAssertion (j : Json) : Except String WebAuthn.AssertionResponse := do
  let userHandle ← match j.getObjVal? "userHandle" with
    | .ok .null | .error _ => pure none
    | .ok _ => some <$> bytesField j "userHandle"
  return { credentialId := ← bytesField j "id", clientDataJSON := ← bytesField j "clientDataJSON",
           authenticatorData := ← bytesField j "authenticatorData",
           signature := ← bytesField j "signature", userHandle }

/-- The transports a browser may report, kept as hints. -/
def knownTransports : List String := ["usb", "nfc", "ble", "internal", "hybrid", "smart-card"]

/-- A registration as the page posts it.  Unknown transports are dropped. -/
def parseRegistration (j : Json) : Except String WebAuthn.RegistrationResponse := do
  let transports := match j.getObjValAs? (Array String) "transports" with
    | .ok ts => ts.toList.filter knownTransports.contains |>.eraseDups
    | .error _ => []
  return { clientDataJSON := ← bytesField j "clientDataJSON",
           attestationObject := ← bytesField j "attestationObject", transports }

/-- base64url, as every binary value is sent. -/
def b64 (b : ByteArray) : String := Encoding.Base64Url.encode b

/-- How long a ceremony may take, in seconds; the challenge expires then. -/
def challengeSeconds : Nat := 300

/-- `429` with `Retry-After`. -/
def rateLimited (wait : Nat) : Reply :=
  (Reply.error .tooManyRequests "rate_limited" s!"try again in {wait} seconds").withHeader
    "Retry-After" (toString wait)

/-- How many challenges one client address (an IPv6 client's /64) may have
pending: each lives `challengeSeconds`, so this bounds how fast one address
can begin ceremonies it does not finish. -/
def maxPendingPerClient : Nat := 20

/-- How many challenges may be pending overall. -/
def maxPendingChallenges : Nat := 10000

/-- Issue a challenge for a ceremony asked for by the request `r`, or the
reply refusing it: `429` when the client has `maxPendingPerClient` pending,
`503` when the table is at `maxPendingChallenges`.  A challenge that is
finished is deleted, so only begins without finishes count. -/
def newChallenge (ctx : Ctx) (r : Req) (purpose : ChallengePurpose) (user : Option UserId)
    (perClient : Nat := maxPendingPerClient) (total : Nat := maxPendingChallenges) :
    IO (Except Reply ByteArray) := do
  let value ← Crypto.randomBytes 32
  let now ← ctx.clock
  match ← ctx.store.addChallengeCapped { value, purpose, user, expires := now + challengeSeconds }
      (addressPrefix r.clientAddress) perClient total now with
  | .added => return .ok value
  | .clientFull => return .error (rateLimited challengeSeconds)
  | .full =>
    return .error (Reply.error .serviceUnavailable "unavailable" "too many sign-ins are pending")

/-- A `PublicKeyCredentialDescriptor` for a credential. -/
def descriptor (id : ByteArray) (transports : List String) : Json :=
  Json.mkObj ([("type", Json.str "public-key"), ("id", Json.str (b64 id))] ++
    (if transports.isEmpty then [] else [("transports", toJson transports)]))

/-- Options for `navigator.credentials.get`. -/
def requestOptions (ctx : Ctx) (challenge : ByteArray) (allow : List Json)
    (userVerification : String) : Json :=
  Json.mkObj [("challenge", b64 challenge), ("rpId", ctx.config.rpId),
    ("timeout", toJson (challengeSeconds * 1000)), ("userVerification", userVerification),
    ("allowCredentials", Json.arr allow.toArray)]

/-- Options for `navigator.credentials.create`, offering ES256 and EdDSA
(§2.2).  Attestation is asked for only when an AAGUID allow-list needs it. -/
def creationOptions (ctx : Ctx) (challenge handle : ByteArray) (name : String)
    (exclude : List Json) (residentKey userVerification : String) : Json :=
  Json.mkObj [("challenge", b64 challenge),
    ("rp", Json.mkObj [("id", ctx.config.rpId), ("name", "pyle")]),
    ("user", Json.mkObj [("id", b64 handle), ("name", name), ("displayName", name)]),
    ("pubKeyCredParams", Json.arr #[
      Json.mkObj [("type", "public-key"), ("alg", toJson (-7 : Int))],
      Json.mkObj [("type", "public-key"), ("alg", toJson (-8 : Int))]]),
    ("timeout", toJson (challengeSeconds * 1000)),
    ("attestation", if ctx.config.aaguidAllowList.isEmpty then "none" else "direct"),
    ("authenticatorSelection", Json.mkObj [("residentKey", residentKey),
      ("requireResidentKey", toJson (residentKey == "required")),
      ("userVerification", userVerification)]),
    ("excludeCredentials", Json.arr exclude.toArray)]

/-! ## Replies -/

/-- `400`, for a request that is not what the endpoint takes. -/
def badRequest (description : String) : Reply :=
  Reply.error .badRequest "invalid_request" description

/-- `401`, for a factor that did not check out.  It says no more than that. -/
def authenticationFailed : Reply :=
  Reply.error .unauthorized "authentication_failed" "the sign-in did not succeed"

/-- `401`, for an endpoint that needs a session. -/
def signInRequired : Reply :=
  Reply.error .unauthorized "sign_in_required" "sign in first"

/-- `403`, for a change that needs a step-up within the window, at level
`need` or better; the level is in the answer's `acr`, as a short name, for the
page to ask for. -/
def stepUpRequired (need : Acr) : Reply :=
  .json (Json.mkObj [("error", "step_up_required"), ("error_description", "confirm it is you first"),
    ("acr", need.shortName)]) .forbidden

/-- The body as JSON, or the `400` to answer.  An empty body is `{}`. -/
def jsonBody (r : Req) : Except Reply Json :=
  if r.body.isEmpty then .ok (Json.mkObj []) else
  match r.json with
  | .ok j => .ok j
  | .error e => .error (badRequest e)

/-! ## Rate limits -/

/-- Run `act` as one attempt against the limiter, for `account` (if the
attempt names one) and the client address.  If the limiter says wait, answer
`429` and record the refusal in the audit log as `event`. -/
def limited (ctx : Ctx) (r : Req) (event : Audit.Event) (account : Option String)
    (act : RateLimiter → Attempt → IO Reply) : IO Reply := do
  match ← ctx.limiter.tryAcquire account r.clientAddress (← ctx.clock) with
  | .error wait =>
    Audit.log ctx r event .refused (userName := account) (detail := "rate limited")
    return rateLimited wait
  | .ok attempt => act ctx.limiter attempt

/-! ## Sessions and step-up -/

/-- How recent an authentication must be for a change to an account, in
seconds (§4: five minutes). -/
def stepUpSeconds : Nat := 300

/-- The request's session, or the `401` to answer. -/
def requireSession (ctx : Ctx) (r : Req) : IO (Except Reply Session) := do
  match ← Session.current ctx r with
  | some s => return .ok s
  | none => return .error signInRequired

/-- The level a change to a user's account needs (DESIGN §4): the account's
own best level or `mfa`, whichever is lower (`Acr.Capabilities.changeLevel`). -/
def changeLevel (ctx : Ctx) (user : UserId) : IO Acr :=
  return (← Policy.capabilities ctx user).changeLevel

/-- The request's session if it authenticated within the step-up window at
the level a change to the account needs (`changeLevel`), or the `401` or `403`
to answer. -/
def requireStepUp (ctx : Ctx) (r : Req) : IO (Except Reply Session) := do
  match ← Session.current ctx r with
  | none => return .error signInRequired
  | some s =>
    let need ← changeLevel ctx s.user
    if Session.authenticatedWithin s (← ctx.clock) stepUpSeconds && s.level.satisfies need then
      return .ok s
    return .error (stepUpRequired need)

/-- The name of a session's user, for the audit log. -/
def userName (ctx : Ctx) (u : UserId) : IO (Option String) :=
  return (← ctx.store.findUser u).map (·.name)

/-! ## Passwords -/

/-- The shortest password accepted, in characters: REFEDS SFA Profile 1.0
§4.1.1 asks twelve of a memorised secret drawn from the letters alone. -/
def minPasswordLength : Nat := 12

/-- The longest, so that hashing one costs a bounded amount. -/
def maxPasswordLength : Nat := 1024

/-- Why a new password is not acceptable, if it is not. -/
def passwordProblem (pw : String) : Option Reply :=
  if pw.length < minPasswordLength then
    some (Reply.error .badRequest "password_too_short"
      s!"a password has at least {minPasswordLength} characters")
  else if pw.length > maxPasswordLength then
    some (Reply.error .badRequest "password_too_long"
      s!"a password has at most {maxPasswordLength} characters")
  else none

/-! ## Registration -/

/-- The certificates of a DER or PEM file: a PEM file may hold several. -/
def readCertificates (path : System.FilePath) : IO (List ByteArray) := do
  let bytes ← IO.FS.readBinFile path
  let some text := String.fromUTF8? bytes | return [bytes]
  if !(text.splitOn "-----BEGIN CERTIFICATE-----").length > 1 then return [bytes]
  let blocks := (text.splitOn "-----BEGIN CERTIFICATE-----").drop 1
  blocks.mapM fun block => do
    let body := (block.splitOn "-----END CERTIFICATE-----").headD ""
    let b64text := String.ofList (body.toList.filter fun c => !c.isWhitespace && c != '=')
    match Factor.Password.b64Decode b64text with
    | some der => return der
    | none => throw (.userError s!"{path}: a certificate is not base64")

/-- Whether a new credential's attestation is acceptable under the
configuration (§2.2).  Without an AAGUID allow-list, `none` and `packed`
self-attestation are accepted, and a full attestation chain is validated
against `attestationRoots` if any are configured (and counts for nothing
otherwise).  With an allow-list, only a full attestation whose chain is valid
and whose AAGUID is listed is accepted: without a verified chain the AAGUID is
the authenticator's own word. -/
def checkAttestationPolicy (ctx : Ctx) (c : WebAuthn.NewCredential) :
    IO (Except String Unit) := do
  let allow := ctx.config.aaguidAllowList
  let roots ← ctx.config.attestationRoots.flatMapM readCertificates
  match c.attestation with
  | .none | .packedSelf =>
    if allow.isEmpty then return .ok ()
    return .error "this deployment admits only attested authenticator models"
  | .packedFull chain =>
    if roots.isEmpty then
      if allow.isEmpty then return .ok ()
      return .error "no attestation roots are configured"
    match ← Crypto.verifyChain chain roots with
    | .error e => return .error s!"the attestation chain does not verify: {e}"
    | .ok _ =>
      if allow.isEmpty || allow.contains (LeanBiscuit.Bytes.toHex c.aaguid) then return .ok ()
      return .error "this authenticator model is not on the allow-list"

/-- The row for a newly registered credential. -/
def credentialRow (c : WebAuthn.NewCredential) (user : UserId) (name : String)
    (transports : List String) (now : Nat) : Credential :=
  { id := c.id, user, algorithm := c.publicKey.algorithm.toInt, publicKey := c.publicKey.bytes,
    signCount := c.signCount.toNat, backupEligible := c.backupEligible,
    backupState := c.backupState, aaguid := c.aaguid, transports, name, created := now,
    lastUsed := none, userVerified := c.userVerified }

/-- The longest name an authenticator may be given. -/
def maxCredentialName : Nat := 64

/-- A name for an authenticator as the user typed it: trimmed, without
control characters, at most `maxCredentialName` characters, and a default when
that leaves nothing. -/
def credentialName (s : Option String) (dflt : String) : String :=
  let n := Audit.clean maxCredentialName ((s.getD "").trimAscii.toString)
  if n.isEmpty then dflt else n

/-- Consume the challenge a registration names, for `purpose`.  The challenge
and the pending row, if both were good. -/
def consumeRegistrationChallenge (ctx : Ctx) (r : WebAuthn.RegistrationResponse) :
    IO (Option (ByteArray × Challenge)) := do
  let some challenge := Policy.challengeOf r.clientDataJSON | return none
  let some ch ← ctx.store.consumeChallenge challenge .register (← ctx.clock) | return none
  return some (challenge, ch)

/-- Run the checks of DESIGN §2.2 on a registration, and the attestation
policy.  The new credential, or a reason for the audit log. -/
def verifyNewCredential (ctx : Ctx) (challenge : ByteArray) (r : WebAuthn.RegistrationResponse)
    (requireUserVerification : Bool) : IO (Except String WebAuthn.NewCredential) := do
  match WebAuthn.verifyRegistration (Policy.relyingParty ctx.config requireUserVerification)
      challenge [.es256, .edDsa] r with
  | .error e => return .error s!"registration refused: {reprStr e}"
  | .ok c =>
    match ← checkAttestationPolicy ctx c with
    | .error e => return .error e
    | .ok () => return .ok c

end SignIn
end Pyle