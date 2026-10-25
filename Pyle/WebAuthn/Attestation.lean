import Pyle.Encoding.Der
import Pyle.WebAuthn.AuthenticatorData

/-!
# Attestation statements

An authenticator may prove what it is when it creates a credential, by signing
the new authenticator data with a key of its own (WebAuthn §6.5, §8).  pyle does
not ask for this by default (DESIGN §2.2), so most registrations carry the
`none` format.  Two forms of `packed` (§8.2) are checked when they are sent:

- *self attestation*, with no certificate: the credential key signs its own
  creation, which proves only that the authenticator holds the key;
- *full attestation*, with a certificate chain `x5c`: the leaf certificate's
  key signs, and the leaf must meet the requirements of §8.2.1.

Full attestation is only worth something if the chain ends in a root the
deployment trusts.  That is not decided here: the chain is returned in
`AttestationKind.packedFull` for the caller to validate (with OpenSSL, DESIGN
§6.1) when an AAGUID allow-list is configured.  What is decided here is that
the leaf's key made the signature, so the chain at least belongs to this
attestation.

Every other format is refused.
-/

namespace Pyle
namespace WebAuthn

open Pyle.Encoding
open LeanBiscuit

/-- What an attestation statement showed. -/
inductive AttestationKind where
  /-- No attestation (`none`). -/
  | none
  /-- `packed` self attestation, signed by the credential key itself. -/
  | packedSelf
  /-- `packed` full attestation, signed by the leaf of `x5c`.  The chain, leaf
  first and in DER, is still to be validated against configured roots. -/
  | packedFull (x5c : List ByteArray)
  deriving Inhabited

/-- The organisational unit WebAuthn requires of a `packed` attestation
certificate (§8.2.1). -/
def attestationOrganizationalUnit : String := "Authenticator Attestation"

/-- A field of an attestation statement. -/
def statementField (entries : List (Cbor × Cbor)) (name : String) :
    Except String (Option Cbor) :=
  Cbor.lookup entries (.text name)

/-- Check a leaf attestation certificate against §8.2.1 and the authenticator
data, and return its key in compressed form. -/
def checkAttestationCertificate (der : ByteArray) (aaguid : ByteArray) :
    Except String ByteArray := do
  let some cert := Der.parseCertificate der | throw "attestation: leaf certificate does not parse"
  if cert.version != 2 then throw "attestation: leaf certificate is not version 3"
  let some units := cert.subjectAttribute Der.oidOrganizationalUnit
    | throw "attestation: leaf certificate subject does not parse"
  if units != [attestationOrganizationalUnit] then
    throw "attestation: leaf certificate subject OU is not \"Authenticator Attestation\""
  for (oid, name) in [(Der.oidCountry, "C"), (Der.oidOrganization, "O"),
      (Der.oidCommonName, "CN")] do
    match cert.subjectAttribute oid with
    | some (_ :: _) => pure ()
    | _ => throw s!"attestation: leaf certificate subject has no {name}"
  match cert.isCa with
  | some false => pure ()
  | some true => throw "attestation: leaf certificate is a CA"
  | none => throw "attestation: leaf certificate basic constraints do not parse"
  match cert.aaguid with
  | some none => pure ()
  | some (some named) =>
    if named != aaguid then throw "attestation: certificate AAGUID differs from authenticator data"
  | none => throw "attestation: certificate AAGUID extension is malformed"
  let some point := cert.p256Point | throw "attestation: leaf key is not a P-256 key"
  let some key := compressUncompressedP256 point | throw "attestation: leaf key is not on P-256"
  pure key

/-- Verify an attestation statement of format `fmt` for a new credential.
`authData` is the raw authenticator data and `clientDataHash` the SHA-256 of
the client data: together they are what an attestation signs. -/
def verifyAttestation (fmt : String) (attStmt : Cbor) (authData clientDataHash : ByteArray)
    (cred : AttestedCredential) : Except String AttestationKind := do
  let .map entries := attStmt | throw "attestation: statement is not a map"
  match fmt with
  | "none" =>
    if !entries.isEmpty then throw "attestation: a none statement must be empty"
    pure .none
  | "packed" =>
    let some algItem ← statementField entries "alg" | throw "attestation: alg missing"
    let some alg := algItem.toInt? | throw "attestation: alg is not an integer"
    let some (.bytes sig) ← statementField entries "sig" | throw "attestation: sig missing"
    if (← statementField entries "ecdaaKeyId").isSome then
      throw "attestation: ECDAA is not supported"
    let signed := authData ++ clientDataHash
    match ← statementField entries "x5c" with
    | none =>
      if CoseAlgorithm.ofInt? alg != some cred.publicKey.algorithm then
        throw "attestation: alg differs from the credential's algorithm"
      if !decide (SignatureValid cred.publicKey signed sig) then
        throw "attestation: self-attestation signature does not verify"
      pure .packedSelf
    | some (.array certs) =>
      let chain ← certs.mapM fun
        | .bytes b => pure b
        | _ => throw "attestation: x5c holds a non-bytes item"
      let leaf :: _ := chain | throw "attestation: x5c is empty"
      if alg != CoseAlgorithm.es256.toInt then
        throw "attestation: only ES256 attestation certificates are supported"
      let key ← checkAttestationCertificate leaf cred.aaguid
      match P256.verify key signed sig with
      | .ok () => pure (.packedFull chain)
      | .error _ => throw "attestation: signature does not verify under the leaf certificate"
    | some _ => throw "attestation: x5c is not an array"
  | other => throw s!"attestation: unsupported format {other}"

end WebAuthn
end Pyle