import Pyle.WebAuthn.Cose

/-!
# The COSE key round trip

DESIGN.md §9.7, for COSE: a key written as an authenticator writes it —
`coseEs256` for a P-256 point, `coseEdDsa` for an Ed25519 key — is read back
by `PublicKey.ofCose` as the key it stands for, and survives the trip through
CBOR bytes on the way.

The trip starts from the coordinates rather than from a stored `PublicKey`:
a stored P-256 key is the compressed point, and writing it out again would
need the square root that recovers `y`, which pyle never computes.  For
Ed25519 the stored key is the coordinate, so the trip is the whole one.
-/

namespace Pyle
namespace Proofs

open Pyle.Encoding WebAuthn LeanBiscuit

section

variable (x y : ByteArray)

private theorem es256_kty :
    coseInt [(.unsigned 1, .unsigned 2), (.unsigned 3, .negative 6), (.negative 0, .unsigned 1),
      (.negative 1, .bytes x), (.negative 2, .bytes y)] 1 = .ok 2 := rfl

private theorem es256_alg :
    coseInt [(.unsigned 1, .unsigned 2), (.unsigned 3, .negative 6), (.negative 0, .unsigned 1),
      (.negative 1, .bytes x), (.negative 2, .bytes y)] 3 = .ok (-7) := rfl

private theorem es256_crv :
    coseInt [(.unsigned 1, .unsigned 2), (.unsigned 3, .negative 6), (.negative 0, .unsigned 1),
      (.negative 1, .bytes x), (.negative 2, .bytes y)] (-1) = .ok 1 := rfl

private theorem es256_x :
    coseBytes [(.unsigned 1, .unsigned 2), (.unsigned 3, .negative 6), (.negative 0, .unsigned 1),
      (.negative 1, .bytes x), (.negative 2, .bytes y)] (-2) = .ok x := rfl

private theorem es256_y :
    coseBytes [(.unsigned 1, .unsigned 2), (.unsigned 3, .negative 6), (.negative 0, .unsigned 1),
      (.negative 1, .bytes x), (.negative 2, .bytes y)] (-3) = .ok y := rfl

private theorem edDsa_kty :
    coseInt [(.unsigned 1, .unsigned 1), (.unsigned 3, .negative 7), (.negative 0, .unsigned 6),
      (.negative 1, .bytes x)] 1 = .ok 1 := rfl

private theorem edDsa_alg :
    coseInt [(.unsigned 1, .unsigned 1), (.unsigned 3, .negative 7), (.negative 0, .unsigned 6),
      (.negative 1, .bytes x)] 3 = .ok (-8) := rfl

private theorem edDsa_crv :
    coseInt [(.unsigned 1, .unsigned 1), (.unsigned 3, .negative 7), (.negative 0, .unsigned 6),
      (.negative 1, .bytes x)] (-1) = .ok 6 := rfl

private theorem edDsa_x :
    coseBytes [(.unsigned 1, .unsigned 1), (.unsigned 3, .negative 7), (.negative 0, .unsigned 6),
      (.negative 1, .bytes x)] (-2) = .ok x := rfl

end

/-- A P-256 point that compresses is read back from its COSE key as the
compressed point. -/
theorem ofCose_coseEs256 {x y c : ByteArray} (h : compressP256 x y = some c) :
    PublicKey.ofCose (coseEs256 x y) = .ok ⟨.es256, c⟩ := by
  simp only [coseEs256, PublicKey.ofCose, es256_kty, es256_alg, es256_crv, es256_x, es256_y,
    bind, Except.bind]
  show (match compressP256 x y with
    | some compressed => pure { algorithm := .es256, bytes := compressed }
    | _ => throw "COSE key: not a point on P-256" : Except String PublicKey) = _
  rw [h]
  rfl

/-- An Ed25519 key of 32 bytes that decompresses is read back from its COSE
key as itself. -/
theorem ofCose_coseEdDsa {x : ByteArray} (hs : x.size = 32)
    (hd : (Ed25519.decompress x).isSome = true) :
    PublicKey.ofCose (coseEdDsa x) = .ok ⟨.edDsa, x⟩ := by
  have hn : (Ed25519.decompress x).isNone = false := by
    cases h : Ed25519.decompress x <;> simp_all
  simp only [coseEdDsa, PublicKey.ofCose, edDsa_kty, edDsa_alg, edDsa_crv, edDsa_x, bind,
    Except.bind, hs, hn]
  rfl

/-- Both coordinates of a point that compresses are 32 bytes. -/
theorem compressP256_size {x y c : ByteArray} (h : compressP256 x y = some c) :
    x.size = 32 ∧ y.size = 32 := by
  unfold compressP256 at h
  by_cases hs : (x.size != 32 || y.size != 32) = true
  · simp [hs] at h
  · simpa using hs

/-- The COSE key of a P-256 point with 32-byte coordinates survives CBOR. -/
theorem decode_encode_coseEs256 {x y : ByteArray} (hx : x.size = 32) (hy : y.size = 32) :
    Cbor.decode (Cbor.encode (coseEs256 x y)) = some (coseEs256 x y) := by
  apply Cbor.decode_encode
  · simp [coseEs256, Cbor.WellFormed, Cbor.EntriesWellFormed, hx, hy]
  · simp [coseEs256, Cbor.depth, Cbor.entriesDepth, Cbor.maxDepth]
  · have hx' : x.data.size = 32 := hx
    have hy' : y.data.size = 32 := hy
    simp only [coseEs256, Cbor.encode, Cbor.encodeList, Cbor.encodeEntries, Cbor.encodeHead,
      Cbor.maxSize]
    simp [ByteArray.size, hx', hy', Cbor.length_beBytes]

/-- The COSE key of a 32-byte Ed25519 key survives CBOR. -/
theorem decode_encode_coseEdDsa {x : ByteArray} (hx : x.size = 32) :
    Cbor.decode (Cbor.encode (coseEdDsa x)) = some (coseEdDsa x) := by
  apply Cbor.decode_encode
  · simp [coseEdDsa, Cbor.WellFormed, Cbor.EntriesWellFormed, hx]
  · simp [coseEdDsa, Cbor.depth, Cbor.entriesDepth, Cbor.maxDepth]
  · have hx' : x.data.size = 32 := hx
    simp only [coseEdDsa, Cbor.encode, Cbor.encodeList, Cbor.encodeEntries, Cbor.encodeHead,
      Cbor.maxSize]
    simp [ByteArray.size, hx', Cbor.length_beBytes]

/-- **COSE round trip, P-256**: the bytes an authenticator writes for a point
on the curve are read back as that point, compressed. -/
theorem cose_roundTrip_es256 {x y c : ByteArray} (h : compressP256 x y = some c) :
    (Cbor.decode (Cbor.encode (coseEs256 x y))).map PublicKey.ofCose = some (.ok ⟨.es256, c⟩) := by
  obtain ⟨hx, hy⟩ := compressP256_size h
  rw [decode_encode_coseEs256 hx hy, Option.map_some, ofCose_coseEs256 h]

/-- **COSE round trip, Ed25519**: a stored Ed25519 key, written as an
authenticator writes it, is read back as itself. -/
theorem cose_roundTrip_edDsa {k : PublicKey} (ha : k.algorithm = .edDsa)
    (hs : k.bytes.size = 32) (hd : (Ed25519.decompress k.bytes).isSome = true) :
    (Cbor.decode (Cbor.encode (coseEdDsa k.bytes))).map PublicKey.ofCose = some (.ok k) := by
  rw [decode_encode_coseEdDsa hs, Option.map_some, ofCose_coseEdDsa hs hd]
  cases k
  cases ha
  rfl

end Proofs
end Pyle