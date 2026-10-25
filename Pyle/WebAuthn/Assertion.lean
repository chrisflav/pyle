import Pyle.Encoding.Base64Url
import Pyle.WebAuthn.AuthenticatorData
import Pyle.WebAuthn.ClientData

/-!
# Authentication

The relying party's side of `navigator.credentials.get` (WebAuthn §7.2,
DESIGN §2.1).  The checks are written down twice: once as `verifyAssertion`,
which runs them, and once as `AssertionChecks`, a proposition with one
conjunct per item of DESIGN §2.1 that can be read on its own.
`verifyAssertion_sound` says the first never accepts what the second does
not describe.

A `VerifiedAssertion` can only be made here, by `verifyAssertion`: its
constructor is private.  Code that takes one as an argument therefore takes
it as evidence that the checks passed, without being able to call them
wrongly or forget one.

Two things are left to the caller, because they need the store.  Looking up
the credential by the id the browser sent is the first half of check 1; the
second half, that the stored credential is the one the browser named, is
checked here.  And the challenge must be consumed by the first attempt that
names it, whatever the outcome.
-/

namespace Pyle
namespace WebAuthn

open Pyle.Encoding
open LeanBiscuit

/-- Membership of a byte string in a list, decided by `ByteArray`'s decidable
equality: the core library decides list membership through `BEq`, and has no
`LawfulBEq ByteArray` to connect the two. -/
instance decidableMemByteArray (x : ByteArray) : (l : List ByteArray) → Decidable (x ∈ l)
  | [] => isFalse (by simp)
  | y :: ys =>
    if h : x = y then isTrue (by simp [h])
    else
      match decidableMemByteArray x ys with
      | isTrue h' => isTrue (List.mem_cons_of_mem _ h')
      | isFalse h' => isFalse (by simp [h, h'])

/-- A registered credential, as the store keeps it. -/
structure StoredCredential where
  /-- The credential id. -/
  id : ByteArray
  /-- The user handle of the user it belongs to. -/
  userHandle : ByteArray
  /-- The credential public key. -/
  publicKey : PublicKey
  /-- The signature counter last seen. -/
  signCount : UInt32
  /-- Whether the credential was backup-eligible when it was registered. -/
  backupEligible : Bool

/-- An assertion as the browser posts it, with every field base64url-decoded. -/
structure AssertionResponse where
  /-- The id of the credential the authenticator used. -/
  credentialId : ByteArray
  /-- The client data, as the browser serialised it. -/
  clientDataJSON : ByteArray
  /-- The authenticator data. -/
  authenticatorData : ByteArray
  /-- The signature over the authenticator data and the client data hash. -/
  signature : ByteArray
  /-- The user handle, which a discoverable credential always returns. -/
  userHandle : Option ByteArray

/-- What a successful assertion establishes.  Only `verifyAssertion` makes
these. -/
structure VerifiedAssertion where private mk ::
  /-- The credential that signed. -/
  credentialId : ByteArray
  /-- The user it belongs to. -/
  userHandle : ByteArray
  /-- Whether the authenticator verified the user. -/
  userVerified : Bool
  /-- Whether the credential is currently backed up. -/
  backupState : Bool
  /-- The new signature counter, to be stored. -/
  signCount : UInt32

/-- Why an assertion was refused, one constructor per check. -/
inductive AssertionError where
  /-- Check 1: the response names a different credential. -/
  | credentialMismatch
  /-- Check 1: the credential is not one of a non-empty `allowCredentials`. -/
  | credentialNotAllowed
  /-- Check 2: the flow requires a user handle and there is none. -/
  | userHandleMissing
  /-- Check 2: the user handle is not the credential owner's. -/
  | userHandleMismatch
  /-- Check 3: the client data does not parse. -/
  | clientData (reason : String)
  /-- Check 3: the client data is not from `navigator.credentials.get`. -/
  | wrongType
  /-- Check 3: the client data names another challenge. -/
  | challengeMismatch
  /-- Check 3: the page was not one of ours. -/
  | originMismatch
  /-- Check 4: the ceremony ran in a cross-origin frame. -/
  | crossOrigin
  /-- The authenticator data does not parse. -/
  | authenticatorData (reason : String)
  /-- Check 5: the credential is scoped to another relying party. -/
  | rpIdHashMismatch
  /-- Check 6: the user was not present. -/
  | userNotPresent
  /-- Check 6: the user was not verified, and the policy requires it. -/
  | userNotVerified
  /-- Check 7: backup eligibility changed since registration. -/
  | backupEligibilityChanged
  /-- Check 8: the signature does not verify. -/
  | badSignature
  /-- Check 9: the counter did not increase; the credential may be cloned. -/
  | possiblyCloned
  deriving Repr, DecidableEq

/-- SHA-256 of the relying party id, which the authenticator data must
carry. -/
def RelyingParty.idHash (rp : RelyingParty) : ByteArray := Sha256.hash rp.id.toUTF8

/-- The bytes an assertion signature covers: the authenticator data followed by
the SHA-256 of the client data. -/
def signedBytes (authenticatorData clientDataJSON : ByteArray) : ByteArray :=
  authenticatorData ++ Sha256.hash clientDataJSON

/-- Run the checks of DESIGN §2.1 on an assertion for a stored credential and a
pending challenge.

`allowCredentials` is the list sent to the browser, if any; an empty list
means the same as none, as it does to the browser (WebAuthn §5.5).  In the
discoverable flow, where the user is identified by the credential alone, pass
`requireUserHandle := true`: the browser must then return the user handle
(WebAuthn §7.2 step 6). -/
def verifyAssertion (rp : RelyingParty) (challenge : ByteArray)
    (allowCredentials : Option (List ByteArray)) (cred : StoredCredential)
    (r : AssertionResponse) (requireUserHandle : Bool := false) :
    Except AssertionError VerifiedAssertion :=
  if r.credentialId ≠ cred.id then .error .credentialMismatch else
  if ¬ (∀ l ∈ allowCredentials, l ≠ [] → r.credentialId ∈ l) then
    .error .credentialNotAllowed else
  if ¬ (requireUserHandle = true → r.userHandle.isSome = true) then
    .error .userHandleMissing else
  if ¬ (∀ h ∈ r.userHandle, h = cred.userHandle) then .error .userHandleMismatch else
  match ClientData.parse r.clientDataJSON with
  | .error e => .error (.clientData e)
  | .ok cd =>
  if cd.type ≠ "webauthn.get" then .error .wrongType else
  if cd.challenge ≠ Base64Url.encode challenge then .error .challengeMismatch else
  if cd.origin ∉ rp.origins then .error .originMismatch else
  if ¬ ((cd.topOrigin = none → cd.crossOrigin ≠ some true) ∧
      ∀ t ∈ cd.topOrigin, cd.crossOrigin = some true ∧ t ∈ rp.allowedTopOrigins) then
    .error .crossOrigin else
  match AuthenticatorData.parse r.authenticatorData with
  | .error e => .error (.authenticatorData e)
  | .ok ad =>
  if ad.rpIdHash ≠ rp.idHash then .error .rpIdHashMismatch else
  if ad.userPresent ≠ true then .error .userNotPresent else
  if ¬ (rp.requireUserVerification = true → ad.userVerified = true) then
    .error .userNotVerified else
  if ad.backupEligible ≠ cred.backupEligible then .error .backupEligibilityChanged else
  if ¬ SignatureValid cred.publicKey (signedBytes r.authenticatorData r.clientDataJSON)
      r.signature then .error .badSignature else
  if ¬ ((cred.signCount ≠ 0 ∨ ad.signCount ≠ 0) → cred.signCount < ad.signCount) then
    .error .possiblyCloned else
  .ok ⟨cred.id, cred.userHandle, ad.userVerified, ad.backupState, ad.signCount⟩

/-- The checks of DESIGN §2.1, as a proposition about an accepted assertion
`v`: the client data and authenticator data parse, each numbered item holds of
them, and `v` reports what they say. -/
def AssertionChecks (rp : RelyingParty) (challenge : ByteArray)
    (allowCredentials : Option (List ByteArray)) (cred : StoredCredential)
    (r : AssertionResponse) (requireUserHandle : Bool) (v : VerifiedAssertion) : Prop :=
  ∃ cd ad, ClientData.parse r.clientDataJSON = .ok cd ∧
    AuthenticatorData.parse r.authenticatorData = .ok ad ∧
    -- 1. the credential is the stored one, and among those allowed if a
    --    non-empty list was sent
    (r.credentialId = cred.id ∧ ∀ l ∈ allowCredentials, l ≠ [] → r.credentialId ∈ l) ∧
    -- 2. the user handle is present if the flow requires it, and when present
    --    is the owner's
    ((requireUserHandle = true → r.userHandle.isSome = true) ∧
      ∀ h ∈ r.userHandle, h = cred.userHandle) ∧
    -- 3. the client data is for `get`, with our challenge, from one of our origins
    (cd.type = "webauthn.get" ∧ cd.challenge = Base64Url.encode challenge ∧
      cd.origin ∈ rp.origins) ∧
    -- 4. not from a cross-origin frame, unless the browser names the top-level
    --    origin and the deployment allows framing by it
    ((cd.topOrigin = none → cd.crossOrigin ≠ some true) ∧
      ∀ t ∈ cd.topOrigin, cd.crossOrigin = some true ∧ t ∈ rp.allowedTopOrigins) ∧
    -- 5. the credential is scoped to our relying party id
    ad.rpIdHash = Sha256.hash rp.id.toUTF8 ∧
    -- 6. the user was present, and verified if the policy says so
    (ad.userPresent = true ∧ (rp.requireUserVerification = true → ad.userVerified = true)) ∧
    -- 7. backup eligibility is what it was at registration
    ad.backupEligible = cred.backupEligible ∧
    -- 8. the signature verifies under the stored key
    SignatureValid cred.publicKey (r.authenticatorData ++ Sha256.hash r.clientDataJSON)
      r.signature ∧
    -- 9. a counter in use strictly increased
    ((cred.signCount ≠ 0 ∨ ad.signCount ≠ 0) → cred.signCount < ad.signCount) ∧
    -- and the result reports the credential, its owner and the authenticator data
    (v.credentialId = cred.id ∧ v.userHandle = cred.userHandle ∧
      v.userVerified = ad.userVerified ∧ v.backupState = ad.backupState ∧
      v.signCount = ad.signCount)

/-- A step of a verifier: if a refusal guarded by `c` led to acceptance, `c`
was false and the rest of the verifier accepted. -/
theorem ok_of_ite_error {ε α : Type} {c : Prop} [Decidable c] {e : ε} {k : Except ε α} {v : α}
    (h : (if c then .error e else k) = .ok v) : ¬ c ∧ k = .ok v := by
  by_cases hc : c
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

/-- **Assertion soundness** (DESIGN §9.1): `verifyAssertion` accepts only
assertions for which every check of §2.1 holds. -/
theorem verifyAssertion_sound {rp : RelyingParty} {challenge : ByteArray}
    {allowCredentials : Option (List ByteArray)} {cred : StoredCredential}
    {r : AssertionResponse} {requireUserHandle : Bool} {v : VerifiedAssertion}
    (h : verifyAssertion rp challenge allowCredentials cred r requireUserHandle = .ok v) :
    AssertionChecks rp challenge allowCredentials cred r requireUserHandle v := by
  rw [verifyAssertion] at h
  obtain ⟨c1, h⟩ := ok_of_ite_error h
  obtain ⟨c1', h⟩ := ok_of_ite_error h
  obtain ⟨c2, h⟩ := ok_of_ite_error h
  obtain ⟨c2', h⟩ := ok_of_ite_error h
  cases hcd : ClientData.parse r.clientDataJSON with
  | error e => rw [hcd] at h; cases h
  | ok cd =>
  rw [hcd] at h
  dsimp only at h
  obtain ⟨c3, h⟩ := ok_of_ite_error h
  obtain ⟨c3', h⟩ := ok_of_ite_error h
  obtain ⟨c3'', h⟩ := ok_of_ite_error h
  obtain ⟨c4, h⟩ := ok_of_ite_error h
  cases had : AuthenticatorData.parse r.authenticatorData with
  | error e => rw [had] at h; cases h
  | ok ad =>
  rw [had] at h
  dsimp only at h
  obtain ⟨c5, h⟩ := ok_of_ite_error h
  obtain ⟨c6, h⟩ := ok_of_ite_error h
  obtain ⟨c6', h⟩ := ok_of_ite_error h
  obtain ⟨c7, h⟩ := ok_of_ite_error h
  obtain ⟨c8, h⟩ := ok_of_ite_error h
  obtain ⟨c9, h⟩ := ok_of_ite_error h
  cases h
  simp only [ne_eq, Decidable.not_not] at c1 c2 c2' c3 c3' c3'' c4 c5 c6 c6' c7 c8 c9 c1'
  exact ⟨cd, ad, hcd, had, ⟨c1, c1'⟩, ⟨c2, c2'⟩, ⟨c3, c3', c3''⟩, c4, c5, ⟨c6, c6'⟩, c7, c8, c9,
    rfl, rfl, rfl, rfl, rfl⟩

end WebAuthn
end Pyle