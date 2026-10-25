import Pyle.Encoding.Base64Url
import Pyle.WebAuthn.Assertion
import Pyle.WebAuthn.Attestation

/-!
# Registration

The relying party's side of `navigator.credentials.create` (WebAuthn §7.1,
DESIGN §2.2): the client-data checks of an assertion, for type
`webauthn.create`, and then the attestation object, which carries the new
credential inside its authenticator data.  The flags must show the user was
present (and verified, if the policy requires it) and that a credential is
attached; its algorithm must be one the relying party offered; and the
attestation statement must be one of the formats of `Attestation`.

As with `VerifiedAssertion`, a `NewCredential` can only come out of
`verifyRegistration`, and the checks are written down twice: as
`verifyRegistration` and as `RegistrationChecks`, and
`verifyRegistration_sound` says the first never accepts what the second does
not describe.  One check of §2.2 needs the store and is the caller's: that
the credential id is not already registered to anyone.  So does binding the
registration to a challenge the server issued: see `RegistrationChecks`.
-/

namespace Pyle
namespace WebAuthn

open Pyle.Encoding
open LeanBiscuit

/-- A registration as the browser posts it, base64url-decoded. -/
structure RegistrationResponse where
  /-- The client data, as the browser serialised it. -/
  clientDataJSON : ByteArray
  /-- The attestation object, CBOR. -/
  attestationObject : ByteArray
  /-- The transports the browser reported, kept as hints for later
  ceremonies. -/
  transports : List String

/-- A credential that passed registration.  Only `verifyRegistration` makes
these. -/
structure NewCredential where private mk ::
  /-- The credential id. -/
  id : ByteArray
  /-- The credential public key. -/
  publicKey : PublicKey
  /-- The initial signature counter. -/
  signCount : UInt32
  /-- The authenticator model's AAGUID; all zeros when it does not say. -/
  aaguid : ByteArray
  /-- Whether the authenticator verified the user. -/
  userVerified : Bool
  /-- Whether the credential may be backed up, which must never change. -/
  backupEligible : Bool
  /-- Whether it is backed up now. -/
  backupState : Bool
  /-- What the attestation statement showed. -/
  attestation : AttestationKind

/-- Why a registration was refused. -/
inductive RegistrationError where
  /-- The client data does not parse. -/
  | clientData (reason : String)
  /-- The client data is not from `navigator.credentials.create`. -/
  | wrongType
  /-- The client data names another challenge. -/
  | challengeMismatch
  /-- The page was not one of ours. -/
  | originMismatch
  /-- The ceremony ran in a cross-origin frame. -/
  | crossOrigin
  /-- The attestation object is not the CBOR map WebAuthn describes. -/
  | attestationObject (reason : String)
  /-- The authenticator data does not parse. -/
  | authenticatorData (reason : String)
  /-- The credential is scoped to another relying party. -/
  | rpIdHashMismatch
  /-- The user was not present. -/
  | userNotPresent
  /-- The user was not verified, and the policy requires it. -/
  | userNotVerified
  /-- The authenticator data carries no credential. -/
  | noAttestedCredential
  /-- The credential's algorithm is not one we offered. -/
  | algorithmNotOffered
  /-- The attestation statement was refused. -/
  | attestation (reason : String)
  deriving Repr

/-- The parts of an attestation object (WebAuthn §6.5.4). -/
structure AttestationObject where
  /-- The attestation statement format. -/
  fmt : String
  /-- The attestation statement. -/
  attStmt : Cbor
  /-- The raw authenticator data. -/
  authData : ByteArray

/-- Read an attestation object: a CBOR map with exactly the text keys `fmt`,
`attStmt` and `authData`. -/
def AttestationObject.parse (b : ByteArray) : Except String AttestationObject := do
  let some (.map entries) := Cbor.decode b | throw "not a CBOR map"
  if entries.length != 3 then throw "expected exactly fmt, attStmt and authData"
  let some (.text fmt) ← Cbor.lookup entries (.text "fmt") | throw "fmt missing"
  let some attStmt ← Cbor.lookup entries (.text "attStmt") | throw "attStmt missing"
  let some (.bytes authData) ← Cbor.lookup entries (.text "authData") | throw "authData missing"
  pure { fmt, attStmt, authData }

/-- Run the checks of DESIGN §2.2 on a registration for a pending challenge,
given the algorithms the relying party offered. -/
def verifyRegistration (rp : RelyingParty) (challenge : ByteArray)
    (algorithms : List CoseAlgorithm) (r : RegistrationResponse) :
    Except RegistrationError NewCredential :=
  match ClientData.parse r.clientDataJSON with
  | .error e => .error (.clientData e)
  | .ok cd =>
  if cd.type ≠ "webauthn.create" then .error .wrongType else
  if cd.challenge ≠ Base64Url.encode challenge then .error .challengeMismatch else
  if cd.origin ∉ rp.origins then .error .originMismatch else
  if ¬ ((cd.topOrigin = none → cd.crossOrigin ≠ some true) ∧
      ∀ t ∈ cd.topOrigin, cd.crossOrigin = some true ∧ t ∈ rp.allowedTopOrigins) then
    .error .crossOrigin else
  match AttestationObject.parse r.attestationObject with
  | .error e => .error (.attestationObject e)
  | .ok obj =>
  match AuthenticatorData.parse obj.authData with
  | .error e => .error (.authenticatorData e)
  | .ok ad =>
  if ad.rpIdHash ≠ rp.idHash then .error .rpIdHashMismatch else
  if ad.userPresent ≠ true then .error .userNotPresent else
  if rp.requireUserVerification = true ∧ ad.userVerified ≠ true then
    .error .userNotVerified else
  match ad.attestedCredential with
  | none => .error .noAttestedCredential
  | some cred =>
  if cred.publicKey.algorithm ∉ algorithms then .error .algorithmNotOffered else
  match verifyAttestation obj.fmt obj.attStmt obj.authData (Sha256.hash r.clientDataJSON) cred with
  | .error e => .error (.attestation e)
  | .ok attestation =>
  .ok ⟨cred.credentialId, cred.publicKey, ad.signCount, cred.aaguid, ad.userVerified,
    ad.backupEligible, ad.backupState, attestation⟩

/-- The checks of DESIGN §2.2, as a proposition about an accepted registration
`v`, one conjunct per item, numbered as the steps of WebAuthn Level 3 §7.1
they implement: the client data, the attestation object and its authenticator
data parse, each item holds of them, and `v` reports the credential they
carry.  Step 11 (`topOrigin`) is folded into step 10.

What two of the conjuncts are worth:

* step 8 says the client data names `challenge`, canonically encoded.  The
  server takes `challenge` from the same client data (`Policy.challengeOf`),
  so it is the caller that binds the registration to a challenge it issued:
  `SignIn.consumeRegistrationChallenge` goes on only if
  `Store.consumeChallenge` hands back a pending row for it;
* step 22 is the implementation's own `verifyAttestation` call, written down
  rather than restated; step 21 follows from it
  (`verifyAttestation_format`).

Steps of §7.1 that are not here: 12 (the client data hash) is computed, not
checked; 18 and 19 evaluate the backup flags, which `v` reports for the
caller's policy; 23 and 24 (trust anchors and the attestation's
trustworthiness) are the caller's attestation policy; 26 (the credential id
is not registered to anyone) needs the store and is the caller's; and 28
(extensions) is not acted on, since pyle asks for no extensions. -/
def RegistrationChecks (rp : RelyingParty) (challenge : ByteArray)
    (algorithms : List CoseAlgorithm) (r : RegistrationResponse) (v : NewCredential) : Prop :=
  ∃ cd obj ad cred, ClientData.parse r.clientDataJSON = .ok cd ∧
    -- 13. the attestation object and its authenticator data decode
    AttestationObject.parse r.attestationObject = .ok obj ∧
    AuthenticatorData.parse obj.authData = .ok ad ∧
    -- 7. the client data is from `navigator.credentials.create`
    cd.type = "webauthn.create" ∧
    -- 8. with our challenge
    cd.challenge = Base64Url.encode challenge ∧
    -- 9. from one of our origins
    cd.origin ∈ rp.origins ∧
    -- 10, 11. not from a cross-origin frame, unless the browser names the
    --     top-level origin and the deployment allows framing by it
    ((cd.topOrigin = none → cd.crossOrigin ≠ some true) ∧
      ∀ t ∈ cd.topOrigin, cd.crossOrigin = some true ∧ t ∈ rp.allowedTopOrigins) ∧
    -- 14. the credential is scoped to our relying party id
    ad.rpIdHash = Sha256.hash rp.id.toUTF8 ∧
    -- 15. the user was present
    ad.userPresent = true ∧
    -- 16. and verified, if the policy says so
    (rp.requireUserVerification = true → ad.userVerified = true) ∧
    -- 17. the backup state is not set without backup eligibility
    (ad.backupEligible = false → ad.backupState = false) ∧
    -- 13. the attested-credential flag is set and the data it announces is there
    ad.attestedCredential = some cred ∧
    -- 20. the credential's algorithm is one we offered
    cred.publicKey.algorithm ∈ algorithms ∧
    -- 21. the attestation statement is of a format we accept
    (obj.fmt = "none" ∨ obj.fmt = "packed") ∧
    -- 22. and verifies over the authenticator data and the client data hash
    verifyAttestation obj.fmt obj.attStmt obj.authData (Sha256.hash r.clientDataJSON) cred =
      .ok v.attestation ∧
    -- 25. the credential id is at most 1023 bytes
    cred.credentialId.size ≤ 1023 ∧
    -- and the result reports the credential and the authenticator data
    (v.id = cred.credentialId ∧ v.publicKey = cred.publicKey ∧ v.signCount = ad.signCount ∧
      v.aaguid = cred.aaguid ∧ v.userVerified = ad.userVerified ∧
      v.backupEligible = ad.backupEligible ∧ v.backupState = ad.backupState)

/-- **Registration soundness**: `verifyRegistration` accepts only
registrations for which every check of §2.2 holds. -/
theorem verifyRegistration_sound {rp : RelyingParty} {challenge : ByteArray}
    {algorithms : List CoseAlgorithm} {r : RegistrationResponse} {v : NewCredential}
    (h : verifyRegistration rp challenge algorithms r = .ok v) :
    RegistrationChecks rp challenge algorithms r v := by
  rw [verifyRegistration] at h
  cases hcd : ClientData.parse r.clientDataJSON with
  | error e => rw [hcd] at h; cases h
  | ok cd =>
  rw [hcd] at h
  dsimp only at h
  obtain ⟨c7, h⟩ := ok_of_ite_error h
  obtain ⟨c8, h⟩ := ok_of_ite_error h
  obtain ⟨c9, h⟩ := ok_of_ite_error h
  obtain ⟨c10, h⟩ := ok_of_ite_error h
  cases hobj : AttestationObject.parse r.attestationObject with
  | error e => rw [hobj] at h; cases h
  | ok obj =>
  rw [hobj] at h
  dsimp only at h
  cases had : AuthenticatorData.parse obj.authData with
  | error e => rw [had] at h; cases h
  | ok ad =>
  rw [had] at h
  dsimp only at h
  obtain ⟨c14, h⟩ := ok_of_ite_error h
  obtain ⟨c15, h⟩ := ok_of_ite_error h
  obtain ⟨c16, h⟩ := ok_of_ite_error h
  cases hcred : ad.attestedCredential with
  | none => rw [hcred] at h; cases h
  | some cred =>
  rw [hcred] at h
  dsimp only at h
  obtain ⟨c20, h⟩ := ok_of_ite_error h
  cases hatt : verifyAttestation obj.fmt obj.attStmt obj.authData
      (Sha256.hash r.clientDataJSON) cred with
  | error e => rw [hatt] at h; cases h
  | ok attestation =>
  rw [hatt] at h
  cases h
  simp only [ne_eq, Decidable.not_not] at c7 c8 c9 c10 c14 c15 c20
  have c16 : rp.requireUserVerification = true → ad.userVerified = true :=
    fun hr => Decidable.byContradiction fun hu => c16 ⟨hr, hu⟩
  exact ⟨cd, obj, ad, cred, hcd, hobj, had, c7, c8, c9, c10, c14, c15, c16,
    AuthenticatorData.parse_backup had, hcred, c20, verifyAttestation_format hatt, hatt,
    AuthenticatorData.parse_credentialId had hcred, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The stored form of a new credential, for the user with the given handle. -/
def NewCredential.toStored (c : NewCredential) (userHandle : ByteArray) : StoredCredential :=
  { id := c.id, userHandle, publicKey := c.publicKey, signCount := c.signCount
    backupEligible := c.backupEligible }

end WebAuthn
end Pyle