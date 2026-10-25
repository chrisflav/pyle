/-!
# CBOR

The part of RFC 8949 that WebAuthn uses: the attestation object, the
attestation statement and the COSE public key are all CBOR, and all of it
arrives from the browser, so all of it is read here by a total function.

Only definite lengths and the minimal ("preferred") encoding of every length
and integer are accepted, which is the deterministic encoding of RFC 8949
§4.2.1 that CTAP2 authenticators emit.  Of the major types, everything but tags
and floating-point numbers is supported: unsigned and negative integers, byte
and text strings, arrays, maps, and the simple values below 24 (`false`,
`true`, `null`, `undefined`).  Anything else is refused rather than skipped.

Decoding is bounded in two ways.  Nesting deeper than `maxDepth` is refused,
so the recursion is bounded by a constant rather than by the input; and an
array or map whose announced length exceeds the bytes left is refused before
any of it is read, since every item takes at least one byte.  The whole input
is limited to `maxSize` bytes.

Map keys are neither sorted nor checked for duplicates by the decoder; the
lookups in `Cbor.Map` refuse a key that appears more than once, which is where
a duplicate could change the meaning of a message.

The decoder works on lists of bytes, which makes the round trip
`decode (encode c) = some c` a structural induction (`decode_encode`).
-/

namespace Pyle
namespace Encoding

/-- A CBOR data item. -/
inductive Cbor where
  /-- Major type 0: an unsigned integer. -/
  | unsigned (n : Nat)
  /-- Major type 1: the negative integer `-1 - n`. -/
  | negative (n : Nat)
  /-- Major type 2: a byte string. -/
  | bytes (b : ByteArray)
  /-- Major type 3: a UTF-8 text string. -/
  | text (s : String)
  /-- Major type 4: an array of items. -/
  | array (items : List Cbor)
  /-- Major type 5: a map, as its entries in the order they were written. -/
  | map (entries : List (Cbor × Cbor))
  /-- Major type 7: a simple value below 24, such as `false` (20) or
  `true` (21). -/
  | simple (n : Nat)
  deriving Inhabited

namespace Cbor

/-- The deepest nesting the decoder follows.  A COSE key inside an attestation
object is three levels deep; sixteen leaves room for extensions. -/
def maxDepth : Nat := 16

/-- The largest input the decoder reads.  An attestation object with a
certificate chain is a few kilobytes. -/
def maxSize : Nat := 65536

/-- The integer an `unsigned` or `negative` item stands for. -/
def toInt? : Cbor → Option Int
  | unsigned n => some n
  | negative n => some (-1 - (n : Int))
  | _ => none

/-- The item for an integer. -/
def ofInt (i : Int) : Cbor :=
  if 0 ≤ i then unsigned i.toNat else negative (-1 - i).toNat

/-! ## Encoding -/

/-- The `k` low-order bytes of `n`, most significant first. -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => beBytes k (n / 256) ++ [UInt8.ofNat (n % 256)]

/-- The number a big-endian byte list stands for. -/
def ofBeBytes (l : List UInt8) : Nat :=
  l.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The initial byte and argument of an item of major type `major` whose
argument is `n`, in the shortest form that holds `n`. -/
def encodeHead (major n : Nat) : List UInt8 :=
  if n < 24 then [UInt8.ofNat (major * 32 + n)]
  else if n < 2 ^ 8 then UInt8.ofNat (major * 32 + 24) :: beBytes 1 n
  else if n < 2 ^ 16 then UInt8.ofNat (major * 32 + 25) :: beBytes 2 n
  else if n < 2 ^ 32 then UInt8.ofNat (major * 32 + 26) :: beBytes 4 n
  else UInt8.ofNat (major * 32 + 27) :: beBytes 8 n

mutual

/-- The encoding of an item, as a list of bytes. -/
def encodeList : Cbor → List UInt8
  | unsigned n => encodeHead 0 n
  | negative n => encodeHead 1 n
  | bytes b => encodeHead 2 b.size ++ b.data.toList
  | text s => encodeHead 3 s.toUTF8.size ++ s.toUTF8.data.toList
  | array items => encodeHead 4 items.length ++ encodeItems items
  | map entries => encodeHead 5 entries.length ++ encodeEntries entries
  | simple n => encodeHead 7 n

/-- The encodings of a list of items, one after the other. -/
def encodeItems : List Cbor → List UInt8
  | [] => []
  | c :: cs => encodeList c ++ encodeItems cs

/-- The encodings of a list of map entries, each key followed by its value. -/
def encodeEntries : List (Cbor × Cbor) → List UInt8
  | [] => []
  | (k, v) :: es => encodeList k ++ encodeList v ++ encodeEntries es

end

/-- The encoding of an item. -/
def encode (c : Cbor) : ByteArray := ⟨(encodeList c).toArray⟩

/-! ## Well-formedness and depth -/

mutual

/-- Whether an item can be written at all: every integer, length and count
fits in 64 bits, and every simple value is below 24. -/
def WellFormed : Cbor → Prop
  | unsigned n => n < 2 ^ 64
  | negative n => n < 2 ^ 64
  | bytes b => b.size < 2 ^ 64
  | text s => s.toUTF8.size < 2 ^ 64
  | array items => items.length < 2 ^ 64 ∧ ItemsWellFormed items
  | map entries => entries.length < 2 ^ 64 ∧ EntriesWellFormed entries
  | simple n => n < 24

/-- Every item of a list is well-formed. -/
def ItemsWellFormed : List Cbor → Prop
  | [] => True
  | c :: cs => WellFormed c ∧ ItemsWellFormed cs

/-- Every key and value of a list of entries is well-formed. -/
def EntriesWellFormed : List (Cbor × Cbor) → Prop
  | [] => True
  | (k, v) :: es => WellFormed k ∧ WellFormed v ∧ EntriesWellFormed es

end

mutual

/-- The nesting depth of an item: one for a scalar, one more than the deepest
element for an array or a map. -/
def depth : Cbor → Nat
  | array items => itemsDepth items + 1
  | map entries => entriesDepth entries + 1
  | _ => 1

/-- The depth of the deepest item of a list, zero if it is empty. -/
def itemsDepth : List Cbor → Nat
  | [] => 0
  | c :: cs => max (depth c) (itemsDepth cs)

/-- The depth of the deepest key or value of a list of entries. -/
def entriesDepth : List (Cbor × Cbor) → Nat
  | [] => 0
  | (k, v) :: es => max (max (depth k) (depth v)) (entriesDepth es)

end

/-! ## Decoding -/

/-- Split off `k` bytes and read them as a big-endian number. -/
def takeBe (k : Nat) (l : List UInt8) : Option (Nat × List UInt8) :=
  if l.length < k then none else some (ofBeBytes (l.take k), l.drop k)

/-- Read the initial byte and argument of an item: its major type, its
argument, and the bytes after them.  Arguments in a longer form than they need
are refused, as are the reserved and indefinite-length forms. -/
def decodeHead : List UInt8 → Option (Nat × Nat × List UInt8)
  | [] => none
  | b :: rest =>
    let major := b.toNat / 32
    let info := b.toNat % 32
    if info < 24 then some (major, info, rest)
    else if info = 24 then
      match takeBe 1 rest with
      | some (n, rest) => if n < 24 then none else some (major, n, rest)
      | none => none
    else if info = 25 then
      match takeBe 2 rest with
      | some (n, rest) => if n < 2 ^ 8 then none else some (major, n, rest)
      | none => none
    else if info = 26 then
      match takeBe 4 rest with
      | some (n, rest) => if n < 2 ^ 16 then none else some (major, n, rest)
      | none => none
    else if info = 27 then
      match takeBe 8 rest with
      | some (n, rest) => if n < 2 ^ 32 then none else some (major, n, rest)
      | none => none
    else none

/-- The byte string made of a list of bytes. -/
def bytesOfList (l : List UInt8) : ByteArray := ⟨l.toArray⟩

mutual

/-- Decode one item from the front of `l`, following at most `fuel - 1`
levels of nesting, and return it with the bytes after it. -/
def decodeItem (fuel : Nat) (l : List UInt8) : Option (Cbor × List UInt8) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match decodeHead l with
    | none => none
    | some (major, n, rest) =>
      if major = 0 then some (unsigned n, rest)
      else if major = 1 then some (negative n, rest)
      else if major = 2 then
        if rest.length < n then none else some (bytes (bytesOfList (rest.take n)), rest.drop n)
      else if major = 3 then
        if rest.length < n then none else
        match String.fromUTF8? (bytesOfList (rest.take n)) with
        | some s => some (text s, rest.drop n)
        | none => none
      else if major = 4 then
        if rest.length < n then none else
        match decodeItems fuel n rest with
        | some (items, rest) => some (array items, rest)
        | none => none
      else if major = 5 then
        if rest.length < n then none else
        match decodeEntries fuel n rest with
        | some (entries, rest) => some (map entries, rest)
        | none => none
      else if major = 7 then
        if n < 24 then some (simple n, rest) else none
      else none
termination_by (fuel, 0)

/-- Decode `count` items one after the other. -/
def decodeItems (fuel : Nat) (count : Nat) (l : List UInt8) :
    Option (List Cbor × List UInt8) :=
  match count with
  | 0 => some ([], l)
  | count + 1 =>
    match decodeItem fuel l with
    | none => none
    | some (c, rest) =>
      match decodeItems fuel count rest with
      | none => none
      | some (cs, rest) => some (c :: cs, rest)
termination_by (fuel, count + 1)

/-- Decode `count` map entries, each a key followed by its value. -/
def decodeEntries (fuel : Nat) (count : Nat) (l : List UInt8) :
    Option (List (Cbor × Cbor) × List UInt8) :=
  match count with
  | 0 => some ([], l)
  | count + 1 =>
    match decodeItem fuel l with
    | none => none
    | some (k, rest) =>
      match decodeItem fuel rest with
      | none => none
      | some (v, rest) =>
        match decodeEntries fuel count rest with
        | none => none
        | some (es, rest) => some ((k, v) :: es, rest)
termination_by (fuel, count + 1)

end

/-- Decode one item from the front of a byte string and return it with the
bytes that follow, as the authenticator data needs for the public key it
carries.  Inputs longer than `maxSize` are refused. -/
def decodePrefix (b : ByteArray) : Option (Cbor × ByteArray) :=
  if b.size > maxSize then none
  else (decodeItem maxDepth b.data.toList).map fun (c, rest) => (c, bytesOfList rest)

/-- Decode a byte string that holds exactly one item and nothing after it. -/
def decode (b : ByteArray) : Option Cbor :=
  if b.size > maxSize then none
  else
    match decodeItem maxDepth b.data.toList with
    | some (c, []) => some c
    | _ => none

/-! ## Looking things up -/

/-- A map key, as WebAuthn uses them: an integer (COSE) or a text string
(attestation objects). -/
inductive Key where
  /-- An integer key. -/
  | int (i : Int)
  /-- A text key. -/
  | text (s : String)

/-- Whether an item is the given key. -/
def isKey (c : Cbor) (k : Key) : Bool :=
  match c, k with
  | text s, .text t => s == t
  | c, .int i => c.toInt? == some i
  | _, _ => false

/-- The value of a key in a map: `none` if it is missing, and an error if it
appears more than once, because two readers of a message with a repeated key
need not agree on what it says. -/
def lookup (entries : List (Cbor × Cbor)) (k : Key) : Except String (Option Cbor) :=
  match entries.filter (fun e => e.1.isKey k) with
  | [] => .ok none
  | [(_, v)] => .ok (some v)
  | _ => .error "repeated map key"

/-! ## The round trip -/

/-- `beBytes k n` has exactly `k` bytes. -/
theorem length_beBytes (k n : Nat) : (beBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [beBytes, ih]

/-- Reading one more byte shifts what was read so far by eight bits. -/
theorem ofBeBytes_append_single (l : List UInt8) (b : UInt8) :
    ofBeBytes (l ++ [b]) = ofBeBytes l * 256 + b.toNat := by
  simp [ofBeBytes, List.foldl_append]

/-- Reading back the `k` low-order bytes of `n` gives `n` modulo `256 ^ k`. -/
theorem ofBeBytes_beBytes (k n : Nat) : ofBeBytes (beBytes k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [beBytes, ofBeBytes, Nat.mod_one]
  | succ k ih =>
    rw [beBytes, ofBeBytes_append_single, ih, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256,
      Nat.mod_mul]
    have : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      simp [Nat.mod_eq_of_lt (show n % 256 < 2 ^ 8 by omega)]
    rw [this]
    rw [Nat.mul_comm]
    omega

/-- A number that fits in `k` bytes is read back from its own encoding. -/
theorem takeBe_beBytes (k n : Nat) (rest : List UInt8) (h : n < 256 ^ k) :
    takeBe k (beBytes k n ++ rest) = some (n, rest) := by
  have hl := length_beBytes k n
  simp [takeBe, hl, ofBeBytes_beBytes, Nat.mod_eq_of_lt h]

/-- A number below 256 survives the trip through a byte. -/
theorem toNat_ofNat_lt (m : Nat) (h : m < 256) : (UInt8.ofNat m).toNat = m := by
  simp [Nat.mod_eq_of_lt (show m < 2 ^ 8 by omega)]

/-- The head of an item is read back as the major type and argument it was
written from, whichever of the five forms `encodeHead` chose. -/
theorem decodeHead_encodeHead (major n : Nat) (rest : List UInt8) (hm : major < 8)
    (hn : n < 2 ^ 64) : decodeHead (encodeHead major n ++ rest) = some (major, n, rest) := by
  unfold encodeHead
  by_cases h0 : n < 24
  · simp only [h0, ↓reduceIte, List.cons_append, List.nil_append, decodeHead]
    rw [toNat_ofNat_lt _ (by omega)]
    have h1 : (major * 32 + n) / 32 = major := by omega
    have h2 : (major * 32 + n) % 32 = n := by omega
    simp [h1, h2, h0]
  by_cases h1 : n < 2 ^ 8
  · simp only [h0, h1, ↓reduceIte, List.cons_append, decodeHead]
    rw [toNat_ofNat_lt _ (by omega), takeBe_beBytes _ _ _ (by omega)]
    have e1 : (major * 32 + 24) / 32 = major := by omega
    have e2 : (major * 32 + 24) % 32 = 24 := by omega
    simp [e1, e2, h0]
  by_cases h2 : n < 2 ^ 16
  · simp only [h0, h1, h2, ↓reduceIte, List.cons_append, decodeHead]
    rw [toNat_ofNat_lt _ (by omega), takeBe_beBytes _ _ _ (by omega)]
    have e1 : (major * 32 + 25) / 32 = major := by omega
    have e2 : (major * 32 + 25) % 32 = 25 := by omega
    simp [e1, e2, h1]
  by_cases h3 : n < 2 ^ 32
  · simp only [h0, h1, h2, h3, ↓reduceIte, List.cons_append, decodeHead]
    rw [toNat_ofNat_lt _ (by omega), takeBe_beBytes _ _ _ (by omega)]
    have e1 : (major * 32 + 26) / 32 = major := by omega
    have e2 : (major * 32 + 26) % 32 = 26 := by omega
    simp [e1, e2, h2]
  · simp only [h0, h1, h2, h3, ↓reduceIte, List.cons_append, decodeHead]
    rw [toNat_ofNat_lt _ (by omega), takeBe_beBytes _ _ _ (by omega)]
    have e1 : (major * 32 + 27) / 32 = major := by omega
    have e2 : (major * 32 + 27) % 32 = 27 := by omega
    simp [e1, e2, h3]

/-- A head is never empty. -/
theorem encodeHead_ne_nil (major n : Nat) : encodeHead major n ≠ [] := by
  unfold encodeHead
  split <;> try split <;> try split <;> try split
  all_goals simp

/-- Every item takes at least one byte, which is what lets the decoder refuse
a count larger than the input before reading any of it. -/
theorem encodeList_ne_nil (c : Cbor) : encodeList c ≠ [] := by
  cases c <;> simp [encodeList, encodeHead_ne_nil]

/-- A list of items takes at least as many bytes as it has items. -/
theorem length_encodeItems (cs : List Cbor) : cs.length ≤ (encodeItems cs).length := by
  induction cs with
  | nil => simp [encodeItems]
  | cons c cs ih =>
    have := List.length_pos_iff.mpr (encodeList_ne_nil c)
    simp [encodeItems]
    omega

/-- A list of entries takes at least as many bytes as it has entries. -/
theorem length_encodeEntries (es : List (Cbor × Cbor)) :
    es.length ≤ (encodeEntries es).length := by
  induction es with
  | nil => simp [encodeEntries]
  | cons e es ih =>
    obtain ⟨k, v⟩ := e
    have := List.length_pos_iff.mpr (encodeList_ne_nil k)
    simp [encodeEntries]
    omega

/-- A byte string survives the trip through a list. -/
theorem bytesOfList_data (b : ByteArray) : bytesOfList b.data.toList = b := by
  simp [bytesOfList]

/-- The UTF-8 bytes of a string decode to that string. -/
theorem fromUTF8?_toByteArray (s : String) : String.fromUTF8? s.toByteArray = some s := by
  simp [String.fromUTF8?, s.isValidUTF8]
  rfl

/-- The main induction: an item no deeper than `fuel` decodes from its own
encoding, followed by anything at all, and leaves exactly that anything. -/
theorem decodeItem_encodeList (fuel : Nat) :
    ∀ (c : Cbor) (rest : List UInt8), WellFormed c → depth c ≤ fuel →
      decodeItem fuel (encodeList c ++ rest) = some (c, rest) := by
  induction fuel with
  | zero =>
    intro c rest _ hd
    cases c <;> simp [depth] at hd
  | succ fuel ih =>
    -- the items of an array decode one by one
    have items : ∀ (cs : List Cbor) (rest : List UInt8), ItemsWellFormed cs →
        itemsDepth cs ≤ fuel →
        decodeItems fuel cs.length (encodeItems cs ++ rest) = some (cs, rest) := by
      intro cs
      induction cs with
      | nil => intro rest _ _; simp [encodeItems, decodeItems]
      | cons c cs ihc =>
        intro rest hw hd
        simp only [ItemsWellFormed] at hw
        simp only [itemsDepth, Nat.max_le] at hd
        simp only [encodeItems, List.append_assoc, List.length_cons]
        rw [decodeItems, ih c _ hw.1 hd.1]
        simp only
        rw [ihc rest hw.2 hd.2]
    have entries : ∀ (es : List (Cbor × Cbor)) (rest : List UInt8), EntriesWellFormed es →
        entriesDepth es ≤ fuel →
        decodeEntries fuel es.length (encodeEntries es ++ rest) = some (es, rest) := by
      intro es
      induction es with
      | nil => intro rest _ _; simp [encodeEntries, decodeEntries]
      | cons e es ihe =>
        obtain ⟨k, v⟩ := e
        intro rest hw hd
        simp only [EntriesWellFormed] at hw
        simp only [entriesDepth, Nat.max_le] at hd
        simp only [encodeEntries, List.append_assoc, List.length_cons]
        rw [decodeEntries, ih k _ hw.1 hd.1.1]
        simp only
        rw [ih v _ hw.2.1 hd.1.2]
        simp only
        rw [ihe rest hw.2.2 hd.2]
    intro c rest hw hd
    cases c with
    | unsigned n =>
      simp only [encodeList]
      rw [decodeItem, decodeHead_encodeHead _ _ _ (by omega) hw]
      simp
    | negative n =>
      simp only [encodeList]
      rw [decodeItem, decodeHead_encodeHead _ _ _ (by omega) hw]
      simp
    | bytes b =>
      simp only [encodeList, List.append_assoc]
      rw [decodeItem, decodeHead_encodeHead _ _ _ (by omega) hw]
      simp [bytesOfList_data]
    | text s =>
      simp only [encodeList, List.append_assoc]
      rw [decodeItem, decodeHead_encodeHead _ _ _ (by omega) hw]
      have hs : bytesOfList s.toByteArray.data.toList = s.toByteArray := bytesOfList_data _
      simp [hs, fromUTF8?_toByteArray]
    | array cs =>
      simp only [WellFormed] at hw
      simp only [depth] at hd
      simp only [encodeList, List.append_assoc]
      rw [decodeItem, decodeHead_encodeHead _ _ _ (by omega) hw.1]
      have hl := length_encodeItems cs
      have hlen : ¬ (encodeItems cs ++ rest).length < cs.length := by simp; omega
      simp only [show (4 : Nat) ≠ 0 from by decide, show (4 : Nat) ≠ 1 from by decide,
        show (4 : Nat) ≠ 2 from by decide, show (4 : Nat) ≠ 3 from by decide, ↓reduceIte,
        hlen]
      rw [items cs rest hw.2 (by omega)]
    | map es =>
      simp only [WellFormed] at hw
      simp only [depth] at hd
      simp only [encodeList, List.append_assoc]
      rw [decodeItem, decodeHead_encodeHead _ _ _ (by omega) hw.1]
      have hl := length_encodeEntries es
      have hlen : ¬ (encodeEntries es ++ rest).length < es.length := by simp; omega
      simp only [show (5 : Nat) ≠ 0 from by decide, show (5 : Nat) ≠ 1 from by decide,
        show (5 : Nat) ≠ 2 from by decide, show (5 : Nat) ≠ 3 from by decide,
        show (5 : Nat) ≠ 4 from by decide, ↓reduceIte, hlen]
      rw [entries es rest hw.2 (by omega)]
    | simple n =>
      simp only [WellFormed] at hw
      simp only [encodeList]
      rw [decodeItem, decodeHead_encodeHead _ _ _ (by omega) (by omega)]
      simp [hw]

/-- Decoding the encoding of a well-formed item gives the item back, provided
it is within the decoder's depth and size bounds. -/
theorem decode_encode (c : Cbor) (hw : WellFormed c) (hd : depth c ≤ maxDepth)
    (hs : (encode c).size ≤ maxSize) : decode (encode c) = some c := by
  have h := decodeItem_encodeList maxDepth c [] hw hd
  simp only [List.append_nil] at h
  have hs' : ¬ (encode c).size > maxSize := by omega
  simp only [decode, hs', ↓reduceIte]
  simp [encode, h]

end Cbor
end Encoding
end Pyle