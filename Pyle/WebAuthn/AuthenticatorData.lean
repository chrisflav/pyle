import Pyle.WebAuthn.Cose

/-!
# Authenticator data

The bytes an authenticator signs over, besides the hash of the client data
(WebAuthn §6.1):

| bytes | field |
| --- | --- |
| 32 | `rpIdHash`, SHA-256 of the relying party id |
| 1 | flags: UP `0x01`, UV `0x04`, BE `0x08`, BS `0x10`, AT `0x40`, ED `0x80` |
| 4 | the signature counter, big-endian |
| if AT | the attested credential: AAGUID (16), id length (2), id, COSE key |
| if ED | the extensions, a CBOR map |

The parser is strict: it reads all of its input and nothing past it, refuses
an attested credential or extensions that the flags do not announce, a
credential id longer than the 1023 bytes WebAuthn allows, and the backup state
bit without the backup eligibility bit (§6.1.3: a credential that cannot be
backed up is not backed up).
-/

namespace Pyle
namespace WebAuthn

open Pyle.Encoding

/-- The credential an authenticator attests to when it creates one. -/
structure AttestedCredential where
  /-- The authenticator model's AAGUID, 16 bytes. -/
  aaguid : ByteArray
  /-- The credential id. -/
  credentialId : ByteArray
  /-- The credential public key. -/
  publicKey : PublicKey

/-- Parsed authenticator data. -/
structure AuthenticatorData where
  /-- SHA-256 of the relying party id the authenticator scoped the credential
  to. -/
  rpIdHash : ByteArray
  /-- The flags byte. -/
  flags : UInt8
  /-- The signature counter. -/
  signCount : UInt32
  /-- The attested credential, present exactly when the AT flag is set. -/
  attestedCredential : Option AttestedCredential
  /-- The extension outputs, present exactly when the ED flag is set. -/
  extensions : Option Cbor

namespace AuthenticatorData

/-- The user-present flag: someone touched the authenticator. -/
def userPresent (d : AuthenticatorData) : Bool := d.flags &&& 0x01 != 0

/-- The user-verified flag: the authenticator checked a PIN or a biometric. -/
def userVerified (d : AuthenticatorData) : Bool := d.flags &&& 0x04 != 0

/-- The backup-eligible flag: the credential may be synced to other devices.
It is fixed when the credential is created. -/
def backupEligible (d : AuthenticatorData) : Bool := d.flags &&& 0x08 != 0

/-- The backup-state flag: the credential is currently backed up. -/
def backupState (d : AuthenticatorData) : Bool := d.flags &&& 0x10 != 0

/-- The attested-credential-data flag. -/
def hasAttestedCredential (flags : UInt8) : Bool := flags &&& 0x40 != 0

/-- The extension-data flag. -/
def hasExtensions (flags : UInt8) : Bool := flags &&& 0x80 != 0

/-- The longest credential id WebAuthn allows (§6.1.2, `credentialIdLength`). -/
def maxCredentialIdLength : Nat := 1023

/-- A big-endian number from bytes. -/
def beNat (b : ByteArray) : Nat := b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- Parse the attested credential data and whatever follows it, which is the
extensions if the ED flag is set and nothing otherwise. -/
def parseAttested (rest : ByteArray) : Except String (AttestedCredential × ByteArray) := do
  if rest.size < 18 then throw "authenticator data: attested credential data too short"
  let aaguid := rest.extract 0 16
  let idLength := beNat (rest.extract 16 18)
  if idLength > maxCredentialIdLength then throw "authenticator data: credential id too long"
  if rest.size < 18 + idLength then throw "authenticator data: credential id truncated"
  let credentialId := rest.extract 18 (18 + idLength)
  let some (key, after) := Cbor.decodePrefix (rest.extract (18 + idLength) rest.size)
    | throw "authenticator data: credential public key is not CBOR"
  let publicKey ← PublicKey.ofCose key
  pure ({ aaguid, credentialId, publicKey }, after)

/-- Parse authenticator data. -/
def parse (b : ByteArray) : Except String AuthenticatorData := do
  if b.size < 37 then throw "authenticator data: shorter than 37 bytes"
  let rpIdHash := b.extract 0 32
  let flags := b[32]?.getD 0
  let signCount := (beNat (b.extract 33 37)).toUInt32
  if flags &&& 0x10 != 0 && flags &&& 0x08 == 0 then
    throw "authenticator data: backed up but not backup-eligible"
  let rest := b.extract 37 b.size
  let (attestedCredential, rest) ←
    if hasAttestedCredential flags then do
      let (a, rest) ← parseAttested rest
      pure (some a, rest)
    else pure (none, rest)
  let extensions ←
    if hasExtensions flags then
      match Cbor.decode rest with
      | some (.map es) => pure (some (Cbor.map es))
      | _ => throw "authenticator data: extensions are not a CBOR map"
    else if rest.size != 0 then throw "authenticator data: trailing bytes"
    else pure none
  pure { rpIdHash, flags, signCount, attestedCredential, extensions }

/-- What every successful parse guarantees: the flags are the byte at offset
32, the backup state is not set without backup eligibility, and an attested
credential is what `parseAttested` read after the fixed header. -/
theorem parse_spec {b : ByteArray} {ad : AuthenticatorData} (h : parse b = .ok ad) :
    ad.flags = b[32]?.getD 0 ∧
      ¬(b[32]?.getD 0 &&& 0x10 != 0 && b[32]?.getD 0 &&& 0x08 == 0) = true ∧
      ∀ c, ad.attestedCredential = some c →
        ∃ r, parseAttested (b.extract 37 b.size) = .ok (c, r) := by
  unfold parse at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hf
  rcases hp : parseAttested (b.extract 37 b.size) with e | ⟨c, r⟩ <;> simp only [hp] at h <;>
    refine ⟨?_, hf, ?_⟩ <;>
    repeat' (first | (split at h) | cases h)
  all_goals
    first
    | rfl
    | (intro c' hc; cases hc; exact ⟨_, rfl⟩)
    | (intro c' hc; cases hc; done)

/-- An attested credential's id is at most `maxCredentialIdLength` bytes. -/
theorem parseAttested_size {rest : ByteArray} {c : AttestedCredential} {r : ByteArray}
    (h : parseAttested rest = .ok (c, r)) : c.credentialId.size ≤ maxCredentialIdLength := by
  unfold parseAttested at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  repeat' (first | (split at h) | cases h)
  all_goals
    simp only [ByteArray.size_extract]
    omega

/-- Parsed authenticator data never shows the backup state without backup
eligibility (WebAuthn L3 §6.1.3). -/
theorem parse_backup {b : ByteArray} {ad : AuthenticatorData} (h : parse b = .ok ad) :
    ad.backupEligible = false → ad.backupState = false := by
  obtain ⟨hfl, hf, -⟩ := parse_spec h
  intro hbe
  simp only [backupEligible, backupState, hfl] at hbe ⊢
  revert hf hbe
  generalize (b[32]?.getD 0 &&& 0x08) = x
  generalize (b[32]?.getD 0 &&& 0x10) = y
  intro hf hbe
  cases hx : x == 0 <;> cases hy : y == 0 <;> simp_all [bne]

/-- The id of a parsed attested credential is at most 1023 bytes. -/
theorem parse_credentialId {b : ByteArray} {ad : AuthenticatorData} (h : parse b = .ok ad)
    {c : AttestedCredential} (hc : ad.attestedCredential = some c) :
    c.credentialId.size ≤ maxCredentialIdLength := by
  obtain ⟨-, -, hp⟩ := parse_spec h
  obtain ⟨r, hr⟩ := hp c hc
  exact parseAttested_size hr

end AuthenticatorData
end WebAuthn
end Pyle