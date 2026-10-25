/-!
# Just enough DER

A `packed` attestation with a certificate chain is signed by the key in the
leaf certificate, so checking the signature needs that key, and WebAuthn
(§8.2.1) adds a few requirements on the certificate itself: a version 3
certificate, the subject's organisational unit, `CA:FALSE`, and the AAGUID
extension agreeing with the authenticator data.  Validating the chain up to a
root is not done here: that is OpenSSL's job (DESIGN §6.1).

So this is a walk over X.509 (RFC 5280) in its DER encoding, not a general
ASN.1 library: single-byte tags, definite minimal lengths up to four bytes,
and the fields of `TBSCertificate` in their fixed order.  Every function is
total and reads only within its input.
-/

namespace Pyle
namespace Encoding
namespace Der

/-- Read a DER length at `i`, returning it and the offset of the contents.
The long form must be minimal, and the indefinite form is refused. -/
def readLength (data : ByteArray) (i : Nat) : Option (Nat × Nat) := do
  let b₀ ← data[i]?
  if b₀ < 0x80 then return (b₀.toNat, i + 1)
  let count := b₀.toNat - 0x80
  if count == 0 || count > 4 || i + 1 + count > data.size then none
  let bytes := data.extract (i + 1) (i + 1 + count)
  let len := bytes.foldl (fun acc b => acc * 256 + b.toNat) 0
  if len < 0x80 || bytes[0]? == some 0 then none
  return (len, i + 1 + count)

/-- Read one tag-length-value at `i`: the tag, the contents, and the offset
after them.  High tag numbers (a first byte of `0x1f` in its low bits) never
occur in a certificate and are refused. -/
def readTlv (data : ByteArray) (i : Nat) : Option (UInt8 × ByteArray × Nat) := do
  let tag ← data[i]?
  if tag &&& 0x1f == 0x1f then none
  let (len, start) ← readLength data (i + 1)
  if start + len > data.size then none
  return (tag, data.extract start (start + len), start + len)

/-- Read a run of tag-length-values that fills `data` exactly, as the contents
of a `SEQUENCE` or `SET` are. -/
def elements (data : ByteArray) : Option (List (UInt8 × ByteArray)) :=
  go data.size 0
where
  /-- Read from offset `i`; `fuel` bounds the recursion by the input size,
  since every element takes at least two bytes. -/
  go (fuel i : Nat) : Option (List (UInt8 × ByteArray)) :=
    if i == data.size then some []
    else match fuel with
      | 0 => none
      | fuel + 1 => do
        let (tag, contents, next) ← readTlv data i
        let rest ← go fuel next
        return (tag, contents) :: rest

/-- Read exactly one tag-length-value with the expected tag, filling `data`. -/
def single (tag : UInt8) (data : ByteArray) : Option ByteArray := do
  let (t, contents, next) ← readTlv data 0
  if t != tag || next != data.size then none
  return contents

/-- The tag of a `BOOLEAN`. -/
def tagBoolean : UInt8 := 0x01
/-- The tag of an `INTEGER`. -/
def tagInteger : UInt8 := 0x02
/-- The tag of a `BIT STRING`. -/
def tagBitString : UInt8 := 0x03
/-- The tag of an `OCTET STRING`. -/
def tagOctetString : UInt8 := 0x04
/-- The tag of an `OBJECT IDENTIFIER`. -/
def tagOid : UInt8 := 0x06
/-- The tag of a `SEQUENCE`. -/
def tagSequence : UInt8 := 0x30
/-- The tag of a `SET`. -/
def tagSet : UInt8 := 0x31

/-- The contents of the object identifier `1.2.840.10045.2.1`,
`id-ecPublicKey`. -/
def oidEcPublicKey : ByteArray := ⟨#[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01]⟩

/-- The contents of the object identifier `1.2.840.10045.3.1.7`,
`prime256v1` (P-256). -/
def oidPrime256v1 : ByteArray := ⟨#[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]⟩

/-- The contents of the object identifier `2.5.4.6`, the country of a name. -/
def oidCountry : ByteArray := ⟨#[0x55, 0x04, 0x06]⟩

/-- The contents of the object identifier `2.5.4.10`, the organisation of a
name. -/
def oidOrganization : ByteArray := ⟨#[0x55, 0x04, 0x0a]⟩

/-- The contents of the object identifier `2.5.4.3`, the common name of a
name. -/
def oidCommonName : ByteArray := ⟨#[0x55, 0x04, 0x03]⟩

/-- The contents of the object identifier `2.5.4.11`, the organisational unit
of a name. -/
def oidOrganizationalUnit : ByteArray := ⟨#[0x55, 0x04, 0x0b]⟩

/-- The contents of the object identifier `2.5.29.19`, basic constraints. -/
def oidBasicConstraints : ByteArray := ⟨#[0x55, 0x1d, 0x13]⟩

/-- The contents of the object identifier `1.3.6.1.4.1.45724.1.1.4`, the FIDO
AAGUID extension. -/
def oidFidoAaguid : ByteArray :=
  ⟨#[0x2b, 0x06, 0x01, 0x04, 0x01, 0x82, 0xe5, 0x1c, 0x01, 0x01, 0x04]⟩

/-- One certificate extension. -/
structure Extension where
  /-- The contents of its object identifier. -/
  oid : ByteArray
  /-- Whether it is marked critical. -/
  critical : Bool
  /-- The contents of its `extnValue` octet string. -/
  value : ByteArray

/-- The parts of a certificate attestation needs. -/
structure Certificate where
  /-- The version number as written: 2 means version 3. -/
  version : Nat
  /-- The contents of the subject `Name`. -/
  subject : ByteArray
  /-- The contents of the `SubjectPublicKeyInfo` algorithm identifier. -/
  publicKeyAlgorithm : ByteArray
  /-- The public key bits, without the unused-bits byte. -/
  publicKey : ByteArray
  /-- The extensions, in order. -/
  extensions : List Extension

/-- Read one `Extension ::= SEQUENCE { extnID, critical DEFAULT FALSE,
extnValue }`. -/
def parseExtension (data : ByteArray) : Option Extension := do
  match ← elements data with
  | [(0x06, oid), (0x04, value)] => return { oid, critical := false, value }
  | [(0x06, oid), (0x01, flag), (0x04, value)] =>
    -- DER writes TRUE as 0xff and never writes the default FALSE
    if flag.data != #[0xff] then none
    return { oid, critical := true, value }
  | _ => none

/-- Read a certificate's `TBSCertificate`, from its version to its
extensions. -/
def parseCertificate (der : ByteArray) : Option Certificate := do
  let cert ← single tagSequence der
  let (tbsTag, tbs) :: _ :: _ :: [] ← elements cert | none
  if tbsTag != tagSequence then none
  let fields ← elements tbs
  -- `[0] EXPLICIT Version DEFAULT v1`
  let (version, fields) ← match fields with
    | (0xa0, v) :: rest => do
      let body ← single tagInteger v
      let n := body.foldl (fun acc b => acc * 256 + b.toNat) 0
      pure (n, rest)
    | rest => pure (0, rest)
  let _serial :: _signature :: _issuer :: _validity :: (0x30, subject) :: (0x30, spki) :: rest
    := fields | none
  let [(0x30, algorithm), (0x03, bits)] ← elements spki | none
  if bits[0]? != some 0 then none
  let publicKey := bits.extract 1 bits.size
  let extensions ← match rest.find? (·.1 == 0xa3) with
    | none => pure []
    | some (_, wrapped) => do
      let list ← single tagSequence wrapped
      let items ← elements list
      items.mapM fun (tag, body) => if tag != tagSequence then none else parseExtension body
  return { version, subject, publicKeyAlgorithm := algorithm, publicKey, extensions }

/-- The uncompressed point of a P-256 public key (65 bytes, starting `04`), if
the certificate holds one. -/
def Certificate.p256Point (c : Certificate) : Option ByteArray := do
  let [(0x06, alg), (0x06, curve)] ← elements c.publicKeyAlgorithm | none
  if alg != oidEcPublicKey || curve != oidPrime256v1 then none
  if c.publicKey.size != 65 || c.publicKey[0]? != some 4 then none
  return c.publicKey

/-- The string values of every attribute of the subject with the given type.
`UTF8String` and `PrintableString` are read; other string types are not used
for the attributes attestation looks at. -/
def Certificate.subjectAttribute (c : Certificate) (oid : ByteArray) : Option (List String) := do
  let rdns ← elements c.subject
  let values ← rdns.mapM fun (tag, rdn) => do
    if tag != tagSet then none
    let atvs ← elements rdn
    atvs.mapM fun (tag, atv) => do
      if tag != tagSequence then none
      let [(0x06, type), (stringTag, value)] ← elements atv | none
      if type != oid then return none
      if stringTag != 0x0c && stringTag != 0x13 then none
      return String.fromUTF8? value
  return values.flatten.filterMap id

/-- The extension with the given identifier, if there is exactly one. -/
def Certificate.extension? (c : Certificate) (oid : ByteArray) : Option (Option Extension) :=
  match c.extensions.filter (·.oid == oid) with
  | [] => some none
  | [e] => some (some e)
  | _ => none

/-- Whether the basic constraints say this is a certificate authority. An
absent extension, or an absent `cA` field, means it is not. -/
def Certificate.isCa (c : Certificate) : Option Bool := do
  match ← c.extension? oidBasicConstraints with
  | none => return false
  | some e =>
    let fields ← elements (← single tagSequence e.value)
    match fields with
    | (0x01, flag) :: _ =>
      -- DER writes a BOOLEAN as exactly 0x00 or 0xff; anything else is refused
      if flag.data == #[0xff] then return true
      else if flag.data == #[0x00] then return false
      else none
    | _ => return false

/-- The AAGUID the certificate names, if it carries the FIDO extension: an
`OCTET STRING` of sixteen bytes inside `extnValue`. -/
def Certificate.aaguid (c : Certificate) : Option (Option ByteArray) := do
  match ← c.extension? oidFidoAaguid with
  | none => return none
  | some e =>
    if e.critical then none
    let inner ← single tagOctetString e.value
    if inner.size != 16 then none
    return some inner

end Der
end Encoding
end Pyle