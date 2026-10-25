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
`verifyRegistration`.  One check of §2.2 needs the store and is the caller's:
that the credential id is not already registered to anyone.
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
    Except RegistrationError NewCredential := do
  let cd ← (ClientData.parse r.clientDataJSON).mapError .clientData
  if cd.type ≠ "webauthn.create" then throw .wrongType
  if cd.challenge ≠ Base64Url.encode challenge then throw .challengeMismatch
  if cd.origin ∉ rp.origins then throw .originMismatch
  if ¬ (rp.allowCrossOrigin = true ∨ (cd.crossOrigin ≠ some true ∧ cd.topOrigin = none)) then
    throw .crossOrigin
  let obj ← (AttestationObject.parse r.attestationObject).mapError .attestationObject
  let ad ← (AuthenticatorData.parse obj.authData).mapError .authenticatorData
  if ad.rpIdHash ≠ rp.idHash then throw .rpIdHashMismatch
  if ad.userPresent ≠ true then throw .userNotPresent
  if rp.requireUserVerification = true ∧ ad.userVerified ≠ true then throw .userNotVerified
  let some cred := ad.attestedCredential | throw .noAttestedCredential
  if cred.publicKey.algorithm ∉ algorithms then throw .algorithmNotOffered
  let attestation ← (verifyAttestation obj.fmt obj.attStmt obj.authData
    (Sha256.hash r.clientDataJSON) cred).mapError .attestation
  pure ⟨cred.credentialId, cred.publicKey, ad.signCount, cred.aaguid, ad.userVerified,
    ad.backupEligible, ad.backupState, attestation⟩

/-- The stored form of a new credential, for the user with the given handle. -/
def NewCredential.toStored (c : NewCredential) (userHandle : ByteArray) : StoredCredential :=
  { id := c.id, userHandle, publicKey := c.publicKey, signCount := c.signCount
    backupEligible := c.backupEligible }

end WebAuthn
end Pyle