/-!
# Base64url

The URL- and filename-safe alphabet of RFC 4648 §5, without padding, which is
how WebAuthn writes every binary value it puts into JSON: the challenge inside
`clientDataJSON`, and the credential ids, signatures and authenticator data the
browser posts back.

The decoder is strict.  It accepts only the canonical encoding of a byte
string: no padding, no whitespace, no characters outside the alphabet, and no
non-zero bits left over in the last character.  With that, decoding is the
inverse of encoding in both directions (`decode_encode` and `encode_decode`),
so two strings that decode to the same bytes are the same string, and
comparing a challenge as text is the same as comparing it as bytes.

The work is done on lists, where the round trip is a short induction, and
lifted to `ByteArray` and `String` at the edges.  The bit fiddling is written
as division and remainder by powers of two, so that `omega` proves it and the
proof rests on no evaluation outside the kernel.
-/

namespace Pyle
namespace Encoding
namespace Base64Url

/-- The character for a six-bit value. -/
def encodeChar (n : Nat) : Char :=
  if n < 26 then Char.ofNat (n + 65)
  else if n < 52 then Char.ofNat (n - 26 + 97)
  else if n < 62 then Char.ofNat (n - 52 + 48)
  else if n == 62 then '-'
  else '_'

/-- The six-bit value of a character of the alphabet, or `none` for any other
character. -/
def decodeChar (c : Char) : Option Nat :=
  let v := c.toNat
  if 65 ≤ v ∧ v ≤ 90 then some (v - 65)
  else if 97 ≤ v ∧ v ≤ 122 then some (v - 97 + 26)
  else if 48 ≤ v ∧ v ≤ 57 then some (v - 48 + 52)
  else if v == 45 then some 62
  else if v == 95 then some 63
  else none

/-- Encode bytes, three at a time into four characters; a final group of one
or two bytes becomes two or three characters, without padding. -/
def encodeList : List UInt8 → List Char
  | a :: b :: c :: rest =>
    encodeChar (a.toNat / 4) :: encodeChar (a.toNat % 4 * 16 + b.toNat / 16)
      :: encodeChar (b.toNat % 16 * 4 + c.toNat / 64) :: encodeChar (c.toNat % 64)
      :: encodeList rest
  | [a, b] =>
    [encodeChar (a.toNat / 4), encodeChar (a.toNat % 4 * 16 + b.toNat / 16),
      encodeChar (b.toNat % 16 * 4)]
  | [a] => [encodeChar (a.toNat / 4), encodeChar (a.toNat % 4 * 16)]
  | [] => []

/-- Decode characters four at a time.  A final group of one character cannot
come from any byte string and is refused, as is a final group of two or three
whose unused low bits are not zero. -/
def decodeList : List Char → Option (List UInt8)
  | c₀ :: c₁ :: c₂ :: c₃ :: rest => do
    let n₀ ← decodeChar c₀
    let n₁ ← decodeChar c₁
    let n₂ ← decodeChar c₂
    let n₃ ← decodeChar c₃
    let tail ← decodeList rest
    pure (UInt8.ofNat (n₀ * 4 + n₁ / 16) :: UInt8.ofNat (n₁ % 16 * 16 + n₂ / 4)
      :: UInt8.ofNat (n₂ % 4 * 64 + n₃) :: tail)
  | [c₀, c₁, c₂] => do
    let n₀ ← decodeChar c₀
    let n₁ ← decodeChar c₁
    let n₂ ← decodeChar c₂
    if n₂ % 4 != 0 then none
    else pure [UInt8.ofNat (n₀ * 4 + n₁ / 16), UInt8.ofNat (n₁ % 16 * 16 + n₂ / 4)]
  | [c₀, c₁] => do
    let n₀ ← decodeChar c₀
    let n₁ ← decodeChar c₁
    if n₁ % 16 != 0 then none
    else pure [UInt8.ofNat (n₀ * 4 + n₁ / 16)]
  | [_] => none
  | [] => some []

/-- The base64url encoding of a byte string, without padding. -/
def encode (b : ByteArray) : String :=
  String.ofList (encodeList b.data.toList)

/-- Decode a base64url string, or `none` if it is not the canonical unpadded
encoding of any byte string. -/
def decode (s : String) : Option ByteArray :=
  (decodeList s.toList).map fun l => ⟨l.toArray⟩

/-! ## The round trip -/

/-- Every six-bit value survives the trip through its character, checked by
evaluation on all sixty-four of them. -/
theorem decodeChar_encodeChar_fin :
    ∀ k : Fin 64, decodeChar (encodeChar k.val) = some k.val := by
  decide

/-- Every six-bit value survives the trip through its character. -/
theorem decodeChar_encodeChar (n : Nat) (h : n < 64) :
    decodeChar (encodeChar n) = some n :=
  decodeChar_encodeChar_fin ⟨n, h⟩

/-- A byte is the byte of its value. -/
theorem ofNat_eq (a : UInt8) (n : Nat) (h : n = a.toNat) : UInt8.ofNat n = a := by
  subst h
  simp

/-- Decoding the encoding of a byte list gives the list back. -/
theorem decodeList_encodeList (l : List UInt8) :
    decodeList (encodeList l) = some l := by
  fun_induction encodeList l with
  | case1 a b c rest ih =>
    have ha := UInt8.toNat_lt a
    have hb := UInt8.toNat_lt b
    have hc := UInt8.toNat_lt c
    simp only [decodeList]
    rw [decodeChar_encodeChar _ (by omega), decodeChar_encodeChar _ (by omega),
      decodeChar_encodeChar _ (by omega), decodeChar_encodeChar _ (by omega), ih]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rw [ofNat_eq a _ (by omega), ofNat_eq b _ (by omega), ofNat_eq c _ (by omega)]
  | case2 a b =>
    have ha := UInt8.toNat_lt a
    have hb := UInt8.toNat_lt b
    simp only [decodeList]
    rw [decodeChar_encodeChar _ (by omega), decodeChar_encodeChar _ (by omega),
      decodeChar_encodeChar _ (by omega)]
    have h : b.toNat % 16 * 4 % 4 = 0 := by omega
    simp only [Option.bind_eq_bind, Option.bind_some, h, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, Option.pure_def]
    rw [ofNat_eq a _ (by omega), ofNat_eq b _ (by omega)]
  | case3 a =>
    have ha := UInt8.toNat_lt a
    simp only [decodeList]
    rw [decodeChar_encodeChar _ (by omega), decodeChar_encodeChar _ (by omega)]
    have h : a.toNat % 4 * 16 % 16 = 0 := by omega
    simp only [Option.bind_eq_bind, Option.bind_some, h, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, Option.pure_def]
    rw [ofNat_eq a _ (by omega)]
  | case4 => rfl

/-- Decoding the encoding of a byte string gives the byte string back. -/
theorem decode_encode (b : ByteArray) : decode (encode b) = some b := by
  simp [decode, encode, String.toList_ofList, decodeList_encodeList]

/-- A character that decodes is the character of the value it decodes to. -/
theorem encodeChar_decodeChar {c : Char} {n : Nat} (h : decodeChar c = some n) :
    n < 64 ∧ encodeChar n = c := by
  have back : ∀ m, m = c.toNat → Char.ofNat m = c := by
    intro m hm
    subst hm
    exact Char.ofNat_toNat c
  unfold decodeChar at h
  dsimp only at h
  split at h
  · cases h
    refine ⟨by omega, ?_⟩
    simp only [encodeChar, show c.toNat - 65 < 26 by omega, ↓reduceIte]
    exact back _ (by omega)
  split at h
  · cases h
    refine ⟨by omega, ?_⟩
    simp only [encodeChar, show ¬ c.toNat - 97 + 26 < 26 by omega,
      show c.toNat - 97 + 26 < 52 by omega, ↓reduceIte]
    exact back _ (by omega)
  split at h
  · cases h
    refine ⟨by omega, ?_⟩
    simp only [encodeChar, show ¬ c.toNat - 48 + 52 < 26 by omega,
      show ¬ c.toNat - 48 + 52 < 52 by omega, show c.toNat - 48 + 52 < 62 by omega, ↓reduceIte]
    exact back _ (by omega)
  split at h
  · cases h
    refine ⟨by omega, ?_⟩
    simp only [encodeChar, beq_iff_eq] at *
    exact (back 45 (by omega)).symm ▸ rfl
  split at h
  · cases h
    refine ⟨by omega, ?_⟩
    simp only [encodeChar, beq_iff_eq] at *
    exact (back 95 (by omega)).symm ▸ rfl
  · cases h

/-- Encoding what a string decodes to gives the string back: the decoder
accepts only canonical encodings, so text and bytes compare alike. -/
theorem encodeList_decodeList {cs : List Char} {l : List UInt8} (h : decodeList cs = some l) :
    encodeList l = cs := by
  fun_induction decodeList cs generalizing l with
  | case1 c₀ c₁ c₂ c₃ rest ih =>
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
    obtain ⟨n₀, h₀, n₁, h₁, n₂, h₂, n₃, h₃, tail, ht, hl⟩ := h
    cases hl
    obtain ⟨b₀, e₀⟩ := encodeChar_decodeChar h₀
    obtain ⟨b₁, e₁⟩ := encodeChar_decodeChar h₁
    obtain ⟨b₂, e₂⟩ := encodeChar_decodeChar h₂
    obtain ⟨b₃, e₃⟩ := encodeChar_decodeChar h₃
    simp only [encodeList, UInt8.toNat_ofNat', ih ht, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← e₀]; congr 1; omega
    · rw [← e₁]; congr 1; omega
    · rw [← e₂]; congr 1; omega
    · rw [← e₃]; congr 1; omega
  | case2 c₀ c₁ c₂ =>
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
    obtain ⟨n₀, h₀, n₁, h₁, n₂, h₂, h⟩ := h
    split at h
    · cases h
    rename_i hz
    cases h
    obtain ⟨b₀, e₀⟩ := encodeChar_decodeChar h₀
    obtain ⟨b₁, e₁⟩ := encodeChar_decodeChar h₁
    obtain ⟨b₂, e₂⟩ := encodeChar_decodeChar h₂
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hz
    simp only [encodeList, UInt8.toNat_ofNat', List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_⟩
    · rw [← e₀]; congr 1; omega
    · rw [← e₁]; congr 1; omega
    · rw [← e₂]; congr 1; omega
  | case3 c₀ c₁ =>
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
    obtain ⟨n₀, h₀, n₁, h₁, h⟩ := h
    split at h
    · cases h
    rename_i hz
    cases h
    obtain ⟨b₀, e₀⟩ := encodeChar_decodeChar h₀
    obtain ⟨b₁, e₁⟩ := encodeChar_decodeChar h₁
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hz
    simp only [encodeList, UInt8.toNat_ofNat', List.cons.injEq, and_true]
    refine ⟨?_, ?_⟩
    · rw [← e₀]; congr 1; omega
    · rw [← e₁]; congr 1; omega
  | case4 => cases h
  | case5 => cases h; rfl

/-- Encoding what a string decodes to gives the string back. -/
theorem encode_decode {s : String} {b : ByteArray} (h : decode s = some b) : encode b = s := by
  simp only [decode, Option.map_eq_some_iff] at h
  obtain ⟨l, hl, rfl⟩ := h
  have := encodeList_decodeList hl
  simp [encode, this]

end Base64Url
end Encoding
end Pyle