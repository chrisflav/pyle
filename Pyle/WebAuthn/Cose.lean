import Pyle.Encoding.Cbor
import LeanBiscuit.Crypto.P256
import LeanBiscuit.Crypto.Ed25519

/-!
# COSE public keys

An authenticator hands over its new public key as a COSE_Key (RFC 9052 §7,
RFC 9053): a CBOR map with integer labels.  Two kinds are accepted, the two
the relying party offers (DESIGN §2.2):

| | `kty` (1) | `alg` (3) | `crv` (-1) | `x` (-2) | `y` (-3) |
| --- | --- | --- | --- | --- | --- |
| ES256 | 2, EC2 | -7 | 1, P-256 | 32 bytes | 32 bytes |
| EdDSA | 1, OKP | -8 | 6, Ed25519 | 32 bytes | |

A key is stored in the form `lean-biscuit`'s verifiers take: a P-256 key as
its 33-byte compressed SEC1 encoding, an Ed25519 key as its 32 bytes.  The
compression is where a P-256 point is checked to be on the curve, so a stored
key is always a point the verifier can use; an Ed25519 key is checked to
decompress.

Signature verification is here too, since it is the one thing a key is for.
-/

namespace Pyle
namespace WebAuthn

open Pyle.Encoding
open LeanBiscuit

/-- A signature algorithm the relying party accepts. -/
inductive CoseAlgorithm where
  /-- ECDSA over P-256 with SHA-256, COSE algorithm -7. -/
  | es256
  /-- EdDSA, which WebAuthn uses only with Ed25519; COSE algorithm -8. -/
  | edDsa
  deriving DecidableEq, Repr, Inhabited

/-- The COSE algorithm identifier. -/
def CoseAlgorithm.toInt : CoseAlgorithm → Int
  | .es256 => -7
  | .edDsa => -8

/-- The algorithm with a COSE identifier, if it is one we accept. -/
def CoseAlgorithm.ofInt? : Int → Option CoseAlgorithm
  | -7 => some .es256
  | -8 => some .edDsa
  | _ => none

/-- A credential public key in the form the verifiers take. -/
structure PublicKey where
  /-- The algorithm the key signs with. -/
  algorithm : CoseAlgorithm
  /-- ES256: the 33-byte compressed SEC1 point; EdDSA: the 32-byte key. -/
  bytes : ByteArray
  deriving DecidableEq, Inhabited

/-- Whether `signature` is a valid signature over `message` under `key`, as
`lean-biscuit`'s verifiers decide it.  ES256 signatures are DER encoded, as
WebAuthn sends them. -/
def SignatureValid (key : PublicKey) (message signature : ByteArray) : Prop :=
  match key.algorithm with
  | .es256 => P256.verify key.bytes message signature = .ok ()
  | .edDsa => Ed25519.verify key.bytes message signature = .ok ()

/-- Whether a verifier's verdict is acceptance. -/
def decideOk {ε : Type} (r : Except ε Unit) : Decidable (r = .ok ()) :=
  match r with
  | .ok () => isTrue rfl
  | .error _ => isFalse (by simp)

instance (key : PublicKey) (message signature : ByteArray) :
    Decidable (SignatureValid key message signature) := by
  unfold SignatureValid
  split
  · exact decideOk _
  · exact decideOk _

/-! ## P-256 points -/

/-- Whether affine coordinates `(x, y)` lie on P-256: both below the field
characteristic and `y² = x³ - 3x + b`. -/
def p256OnCurve (x y : Nat) : Bool :=
  let rhs := P256.F.add (P256.F.sub (P256.F.mul x (P256.F.mul x x)) (P256.F.mul 3 x)) P256.b
  x < P256.p && y < P256.p && P256.F.mul y y == rhs

/-- The compressed SEC1 encoding of a P-256 point given by its 32-byte
coordinates, if it is on the curve. -/
def compressP256 (x y : ByteArray) : Option ByteArray :=
  if x.size != 32 || y.size != 32 then none
  else
    let xn := Bytes.toNatBE x
    let yn := Bytes.toNatBE y
    if !p256OnCurve xn yn then none
    else some (ByteArray.mk #[if yn % 2 == 1 then 3 else 2] ++ x)

/-- The compressed SEC1 encoding of an uncompressed one (65 bytes starting
`04`), if the point is on the curve. -/
def compressUncompressedP256 (point : ByteArray) : Option ByteArray :=
  if point.size != 65 || point[0]? != some 4 then none
  else compressP256 (point.extract 1 33) (point.extract 33 65)

/-! ## Reading and writing COSE keys -/

/-- An integer-labelled field of a COSE key, which must be present. -/
def coseField (entries : List (Cbor × Cbor)) (label : Int) : Except String Cbor := do
  match ← Cbor.lookup entries (.int label) with
  | some v => pure v
  | none => throw s!"COSE key: missing label {label}"

/-- A byte-string field of a COSE key. -/
def coseBytes (entries : List (Cbor × Cbor)) (label : Int) : Except String ByteArray := do
  match ← coseField entries label with
  | .bytes b => pure b
  | _ => throw s!"COSE key: label {label} is not a byte string"

/-- An integer field of a COSE key. -/
def coseInt (entries : List (Cbor × Cbor)) (label : Int) : Except String Int := do
  match (← coseField entries label).toInt? with
  | some i => pure i
  | none => throw s!"COSE key: label {label} is not an integer"

/-- Read a COSE_Key, accepting only ES256 on P-256 and EdDSA on Ed25519, and
only consistent combinations of key type, algorithm and curve. -/
def PublicKey.ofCose (key : Cbor) : Except String PublicKey := do
  let .map entries := key | throw "COSE key: not a map"
  let kty ← coseInt entries 1
  let alg ← coseInt entries 3
  let some algorithm := CoseAlgorithm.ofInt? alg
    | throw s!"COSE key: unsupported algorithm {alg}"
  let crv ← coseInt entries (-1)
  match algorithm with
  | .es256 =>
    if kty != 2 then throw "COSE key: ES256 needs key type EC2"
    if crv != 1 then throw "COSE key: ES256 needs curve P-256"
    let x ← coseBytes entries (-2)
    let y ← coseBytes entries (-3)
    let some compressed := compressP256 x y | throw "COSE key: not a point on P-256"
    pure { algorithm, bytes := compressed }
  | .edDsa =>
    if kty != 1 then throw "COSE key: EdDSA needs key type OKP"
    if crv != 6 then throw "COSE key: EdDSA needs curve Ed25519"
    let x ← coseBytes entries (-2)
    if x.size != 32 then throw "COSE key: an Ed25519 key is 32 bytes"
    if (Ed25519.decompress x).isNone then throw "COSE key: not a point on Ed25519"
    pure { algorithm, bytes := x }

/-- The COSE_Key of a P-256 point given by its coordinates, as an
authenticator writes it. -/
def coseEs256 (x y : ByteArray) : Cbor :=
  .map [(.unsigned 1, .unsigned 2), (.unsigned 3, .negative 6), (.negative 0, .unsigned 1),
    (.negative 1, .bytes x), (.negative 2, .bytes y)]

/-- The COSE_Key of an Ed25519 public key, as an authenticator writes it. -/
def coseEdDsa (x : ByteArray) : Cbor :=
  .map [(.unsigned 1, .unsigned 1), (.unsigned 3, .negative 7), (.negative 0, .unsigned 6),
    (.negative 1, .bytes x)]

end WebAuthn
end Pyle