/-!
# QR codes

A QR Code Model 2 encoder (ISO/IEC 18004:2015), enough to put an `otpauth://`
URI on the account page as something a phone can scan (DESIGN.md §3).  It
encodes in byte mode only, which every URI fits, at any of the four error
correction levels (`medium` by default), and picks the smallest of the forty
versions that holds the data.  The symbol is rendered as SVG here too, so the
page needs no library and no script beyond its own (`toSvg`, `toDataUrl`).

The steps are those of §7.1 of the standard, each a function of its own: the
bit stream with its mode indicator, character count, terminator and pad
codewords (`dataCodewords`); the error correction codewords, Reed–Solomon over
GF(256) with the field polynomial `0x11D`, one block at a time, and the blocks
interleaved (`interleave`); the function patterns, the codewords placed in the
two-column zigzag, and the eight masks, of which the one with the lowest
penalty under the four rules of §7.8.3 is kept (`encode`).

Everything is total.  Arrays are read with `getD` and written with
`setIfInBounds`, so no index can panic, and data too long for version 40 is
`none` rather than an error.
-/

namespace Pyle
namespace Encoding
namespace QrCode

/-- The four error correction levels, recovering about 7%, 15%, 25% and 30% of
the codewords. -/
inductive Level where
  | low
  | medium
  | quartile
  | high
  deriving BEq, Repr, Inhabited

/-- The level's row in the tables below. -/
def Level.index : Level → Nat
  | .low => 0
  | .medium => 1
  | .quartile => 2
  | .high => 3

/-- The two bits the format information gives a level (Table 12), which are
not in the order of the levels. -/
def Level.formatBits : Level → Nat
  | .low => 1
  | .medium => 0
  | .quartile => 3
  | .high => 2

/-- A symbol: its rows from top to bottom, each from left to right, `true` for
a dark module. -/
abbrev Matrix := Array (Array Bool)

/-! ## The tables -/

/-- The error correction codewords in each block, by level and version
(Table 9).  Entry 0 of each row stands for no version. -/
def eccPerBlockTable : Array (Array Nat) := #[
  #[0, 7, 10, 15, 20, 26, 18, 20, 24, 30, 18, 20, 24, 26, 30, 22, 24, 28, 30, 28, 28,
    28, 28, 30, 30, 26, 28, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30],
  #[0, 10, 16, 26, 18, 24, 16, 18, 22, 22, 26, 30, 22, 22, 24, 24, 28, 28, 26, 26, 26,
    26, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28],
  #[0, 13, 22, 18, 26, 18, 24, 18, 22, 20, 24, 28, 26, 24, 20, 30, 24, 28, 28, 26, 30,
    28, 30, 30, 30, 30, 28, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30],
  #[0, 17, 28, 22, 16, 22, 28, 26, 26, 24, 28, 24, 28, 22, 24, 24, 30, 28, 28, 26, 28,
    30, 24, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30]]

/-- The number of error correction blocks, by level and version (Table 9). -/
def blocksTable : Array (Array Nat) := #[
  #[0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 4, 4, 4, 6, 6, 6, 6, 7, 8,
    8, 9, 9, 10, 12, 12, 12, 13, 14, 15, 16, 17, 18, 19, 19, 20, 21, 22, 24, 25],
  #[0, 1, 1, 1, 2, 2, 4, 4, 4, 5, 5, 5, 8, 9, 9, 10, 10, 11, 13, 14, 16,
    17, 17, 18, 20, 21, 23, 25, 26, 28, 29, 31, 33, 35, 37, 38, 40, 43, 45, 47, 49],
  #[0, 1, 1, 2, 2, 4, 4, 6, 6, 8, 8, 8, 10, 12, 16, 12, 17, 16, 18, 21, 20,
    23, 23, 25, 27, 29, 34, 34, 35, 38, 40, 43, 45, 48, 51, 53, 56, 59, 62, 65, 68],
  #[0, 1, 1, 2, 4, 4, 4, 5, 6, 8, 8, 11, 11, 16, 16, 18, 16, 19, 21, 25, 25,
    25, 34, 30, 32, 35, 37, 40, 42, 45, 48, 51, 54, 57, 60, 63, 66, 70, 74, 77, 81]]

/-- Error correction codewords per block. -/
def eccPerBlock (level : Level) (version : Nat) : Nat :=
  (eccPerBlockTable.getD level.index #[]).getD version 0

/-- The number of blocks, never zero. -/
def numBlocks (level : Level) (version : Nat) : Nat :=
  max 1 ((blocksTable.getD level.index #[]).getD version 1)

/-- The width of a symbol, in modules. -/
def size (version : Nat) : Nat := 4 * version + 17

/-- How many modules of a symbol carry codewords: everything but the function
patterns and the format and version information.  The closed form counts the
finder patterns, timing patterns and format information (the 64 + 128 + 16
terms), the alignment patterns that do not overlap them, and from version 7 on
the two 18-module blocks of version information. -/
def rawModules (version : Nat) : Nat :=
  let base := (16 * version + 128) * version + 64
  if version < 2 then base else
    let n := version / 7 + 2
    let base := base - ((25 * n - 10) * n - 55)
    if version < 7 then base else base - 36

/-- All codewords of a symbol, data and error correction (Table 1). -/
def totalCodewords (version : Nat) : Nat := rawModules version / 8

/-- The data codewords of a symbol at a level. -/
def dataCapacity (level : Level) (version : Nat) : Nat :=
  totalCodewords version - eccPerBlock level version * numBlocks level version

/-- The centres of the alignment patterns along either axis (Annex E): from 6
to the seventh module from the far edge, evenly spaced but for the first gap,
which takes up whatever does not divide. -/
def alignmentPositions (version : Nat) : List Nat :=
  if version < 2 then [] else
    let n := version / 7 + 2
    let step := (version * 8 + n * 3 + 5) / (n * 4 - 4) * 2
    6 :: ((List.range (n - 1)).reverse.map fun i => size version - 7 - i * step)

/-! ## The bit stream -/

/-- Append the `len` low bits of `value`, most significant first. -/
def appendBits (bits : Array Bool) (value len : Nat) : Array Bool := Id.run do
  let mut bits := bits
  for i in [0:len] do
    bits := bits.push (value.testBit (len - 1 - i))
  return bits

/-- Bits, a multiple of eight of them, as bytes. -/
def packBits (bits : Array Bool) : Array Nat := Id.run do
  let mut out := #[]
  for i in [0:bits.size / 8] do
    let mut byte := 0
    for j in [0:8] do
      byte := byte * 2 + if bits.getD (8 * i + j) false then 1 else 0
    out := out.push byte
  return out

/-- The width of the character count in byte mode (Table 3). -/
def countBits (version : Nat) : Nat := if version < 10 then 8 else 16

/-- Whether `n` bytes fit a symbol in byte mode: the four-bit mode indicator,
the count, and eight bits a byte. -/
def fits (level : Level) (version n : Nat) : Bool :=
  n < 2 ^ countBits version && 4 + countBits version + 8 * n ≤ 8 * dataCapacity level version

/-- The smallest version that holds `n` bytes, if any does. -/
def chooseVersion (level : Level) (n : Nat) : Option Nat :=
  (List.range 40).map (· + 1) |>.find? (fits level · n)

/-- The data codewords (§7.4): mode indicator `0100`, the count, the bytes, a
terminator of up to four zero bits, zero bits to the next byte, and then the
pad codewords `0xEC` and `0x11` in turn until the symbol is full. -/
def dataCodewords (level : Level) (version : Nat) (data : ByteArray) : Array Nat := Id.run do
  let capacity := 8 * dataCapacity level version
  let mut bits := appendBits #[] 4 4
  bits := appendBits bits data.size (countBits version)
  for b in data do
    bits := appendBits bits b.toNat 8
  bits := appendBits bits 0 (min 4 (capacity - bits.size))
  bits := appendBits bits 0 ((8 - bits.size % 8) % 8)
  let mut out := packBits bits
  let mut pad := 0xEC
  while out.size < capacity / 8 do
    out := out.push pad
    pad := if pad == 0xEC then 0x11 else 0xEC
  return out

/-! ## Reed–Solomon -/

/-- Multiplication in GF(256) modulo `x⁸ + x⁴ + x³ + x² + 1`, that is `0x11D`
(§7.5.2), on values below 256. -/
def gfMul (x y : Nat) : Nat := Id.run do
  let mut z := 0
  for i in [0:8] do
    z := (z <<< 1) ^^^ ((z >>> 7) * 0x11D)
    if y.testBit (7 - i) then z := z ^^^ x
  return z

/-- The generator polynomial of the given degree, `∏ (x - αⁱ)` for `i < degree`
with `α = 2`, as its coefficients from the highest power down without the
leading 1. -/
def generator (degree : Nat) : Array Nat := Id.run do
  let mut coeffs : Array Nat := (Array.replicate (degree - 1) 0).push 1
  let mut root := 1
  for _ in [0:degree] do
    for j in [0:degree] do
      let c := gfMul (coeffs.getD j 0) root
      coeffs := coeffs.setIfInBounds j (c ^^^ coeffs.getD (j + 1) 0)
    root := gfMul root 2
  return coeffs

/-- The error correction codewords of a block: the remainder of the data,
times `x^degree`, divided by the generator polynomial. -/
def eccCodewords (gen : Array Nat) (data : Array Nat) : Array Nat := Id.run do
  let mut rem : Array Nat := Array.replicate gen.size 0
  for b in data do
    let factor := b ^^^ rem.getD 0 0
    rem := (rem.extract 1 rem.size).push 0
    for i in [0:gen.size] do
      rem := rem.setIfInBounds i (rem.getD i 0 ^^^ gfMul (gen.getD i 0) factor)
  return rem

/-- The final sequence of codewords (§7.6): the data split into blocks, the
shorter blocks first and the longer ones a codeword longer, each block's error
correction computed, and then the data codewords of all blocks interleaved,
followed by the error correction codewords interleaved. -/
def interleave (level : Level) (version : Nat) (data : Array Nat) : Array Nat := Id.run do
  let blocks := numBlocks level version
  let eccLen := eccPerBlock level version
  let total := totalCodewords version
  let short := total / blocks - eccLen
  let numShort := blocks - total % blocks
  let gen := generator eccLen
  let mut datas : Array (Array Nat) := #[]
  let mut eccs : Array (Array Nat) := #[]
  let mut k := 0
  for i in [0:blocks] do
    let len := if i < numShort then short else short + 1
    let d := data.extract k (k + len)
    k := k + len
    datas := datas.push d
    eccs := eccs.push (eccCodewords gen d)
  let mut out := #[]
  for i in [0:short + 1] do
    for d in datas do
      if h : i < d.size then out := out.push d[i]
  for i in [0:eccLen] do
    for e in eccs do
      out := out.push (e.getD i 0)
  return out

/-! ## Format and version information -/

/-- The 15 bits of format information for a level and mask (§7.9.1): the five
data bits, ten bits of the (15, 5) BCH code with generator `0x537`, the whole
XORed with `0x5412` so that it is never all zero. -/
def formatInfo (level : Level) (mask : Nat) : Nat :=
  let data := level.formatBits <<< 3 ||| mask % 8
  let rem := (List.range 10).foldl (fun r _ => (r <<< 1) ^^^ ((r >>> 9) * 0x537)) data
  ((data <<< 10) ||| rem) ^^^ 0x5412

/-- The 18 bits of version information (§7.10): the version in six bits and
twelve bits of the (18, 6) Golay code with generator `0x1F25`. -/
def versionInfo (version : Nat) : Nat :=
  let rem := (List.range 12).foldl (fun r _ => (r <<< 1) ^^^ ((r >>> 11) * 0x1F25)) version
  (version <<< 12) ||| rem

/-! ## The symbol -/

/-- A symbol being built: its width, its modules row by row, and which of them
belong to function patterns and so carry no data and are not masked. -/
structure Grid where
  size : Nat
  dark : Array Bool
  function : Array Bool

namespace Grid

/-- A light symbol with nothing reserved. -/
def empty (size : Nat) : Grid :=
  ⟨size, Array.replicate (size * size) false, Array.replicate (size * size) false⟩

/-- The module in column `x` of row `y`; light outside the symbol. -/
def get (g : Grid) (x y : Nat) : Bool :=
  x < g.size && g.dark.getD (y * g.size + x) false

/-- Whether the module in column `x` of row `y` is a function module. -/
def isFunction (g : Grid) (x y : Nat) : Bool :=
  x < g.size && g.function.getD (y * g.size + x) false

/-- Set a function module; nothing happens outside the symbol. -/
def setFunction (g : Grid) (x y : Nat) (b : Bool) : Grid :=
  if x < g.size then
    let ⟨n, dark, fn⟩ := g
    ⟨n, dark.setIfInBounds (y * n + x) b, fn.setIfInBounds (y * n + x) true⟩
  else g

/-- `setFunction` at integer coordinates, so that patterns can be drawn
across an edge and clipped. -/
def setAt (g : Grid) (x y : Int) (b : Bool) : Grid :=
  if 0 ≤ x ∧ 0 ≤ y then g.setFunction x.toNat y.toNat b else g

/-- A finder pattern centred on `(x, y)` with its separator: the dark ring at
distance 3, the light one at 2, the dark 3×3 centre, and the light separator
at distance 4, clipped at the edges. -/
def finder (g : Grid) (x y : Int) : Grid := Id.run do
  let mut g := g
  for i in [0:9] do
    for j in [0:9] do
      let dx : Int := i - 4
      let dy : Int := j - 4
      let d := max dx.natAbs dy.natAbs
      g := g.setAt (x + dx) (y + dy) (d != 2 && d != 4)
  return g

/-- An alignment pattern centred on `(x, y)`: a dark centre, a light ring and
a dark ring. -/
def alignment (g : Grid) (x y : Int) : Grid := Id.run do
  let mut g := g
  for i in [0:5] do
    for j in [0:5] do
      let dx : Int := i - 2
      let dy : Int := j - 2
      g := g.setAt (x + dx) (y + dy) (max dx.natAbs dy.natAbs != 1)
  return g

/-- Both copies of the format information (§7.9.1, Figure 25), and the dark
module beside the lower one. -/
def drawFormat (g : Grid) (bits : Nat) : Grid := Id.run do
  let n := g.size
  let mut g := g
  for i in [0:6] do
    g := g.setFunction 8 i (bits.testBit i)
  g := g.setFunction 8 7 (bits.testBit 6)
  g := g.setFunction 8 8 (bits.testBit 7)
  g := g.setFunction 7 8 (bits.testBit 8)
  for i in [9:15] do
    g := g.setFunction (14 - i) 8 (bits.testBit i)
  for i in [0:8] do
    g := g.setFunction (n - 1 - i) 8 (bits.testBit i)
  for i in [8:15] do
    g := g.setFunction 8 (n - 15 + i) (bits.testBit i)
  g := g.setFunction 8 (n - 8) true
  return g

/-- Both copies of the version information (§7.10, Figure 27), from version 7
on: six rows of three above the lower left finder, and the transpose beside
the upper right one. -/
def drawVersion (g : Grid) (version : Nat) : Grid := Id.run do
  if version < 7 then return g
  let bits := versionInfo version
  let mut g := g
  for i in [0:18] do
    let a := g.size - 11 + i % 3
    let b := i / 3
    g := g.setFunction a b (bits.testBit i)
    g := g.setFunction b a (bits.testBit i)
  return g

/-- Every function pattern of a version: the timing patterns, the three
finders, the alignment patterns that do not collide with a finder, the format
information (reserved, with a placeholder, until the mask is known) and the
version information. -/
def functionPatterns (version : Nat) : Grid := Id.run do
  let n := QrCode.size version
  let mut g := empty n
  for i in [0:n] do
    g := g.setFunction 6 i (i % 2 == 0)
    g := g.setFunction i 6 (i % 2 == 0)
  g := g.finder 3 3
  g := g.finder (n - 4 : Nat) 3
  g := g.finder 3 (n - 4 : Nat)
  let pos := alignmentPositions version
  let last := pos.length - 1
  for (x, i) in pos.zipIdx do
    for (y, j) in pos.zipIdx do
      unless (i == 0 && j == 0) || (i == 0 && j == last) || (i == last && j == 0) do
        g := g.alignment x y
  g := g.drawFormat 0
  g := g.drawVersion version
  return g

/-- Place the codewords (§7.7.3): in pairs of columns from the right, skipping
the vertical timing column, upwards and downwards in turn, right module before
left, over every module that is not a function module.  The remainder bits
left over at the end stay light. -/
def placeCodewords (g : Grid) (codewords : Array Nat) : Grid := Id.run do
  let n := g.size
  let total := codewords.size * 8
  let mut g := g
  let mut k := 0
  for p in [0:n / 2] do
    let right := if n - 1 - 2 * p ≤ 6 then n - 2 - 2 * p else n - 1 - 2 * p
    let upward := (right + 1) &&& 2 == 0
    for v in [0:n] do
      let y := if upward then n - 1 - v else v
      for j in [0:2] do
        let x := right - j
        if !g.isFunction x y && k < total then
          let bit := (codewords.getD (k / 8) 0).testBit (7 - k % 8)
          let ⟨s, dark, fn⟩ := g
          g := ⟨s, dark.setIfInBounds (y * s + x) bit, fn⟩
          k := k + 1
  return g

/-- Whether mask `m` (Table 10) inverts the module in row `i`, column `j`. -/
def maskBit (m i j : Nat) : Bool :=
  match m with
  | 0 => (i + j) % 2 == 0
  | 1 => i % 2 == 0
  | 2 => j % 3 == 0
  | 3 => (i + j) % 3 == 0
  | 4 => (i / 2 + j / 3) % 2 == 0
  | 5 => (i * j) % 2 + (i * j) % 3 == 0
  | 6 => ((i * j) % 2 + (i * j) % 3) % 2 == 0
  | _ => ((i + j) % 2 + (i * j) % 3) % 2 == 0

/-- Apply a mask to every module that is not a function module.  Applying it
twice undoes it. -/
def applyMask (g : Grid) (m : Nat) : Grid := Id.run do
  let ⟨n, dark, fn⟩ := g
  let mut dark := dark
  for y in [0:n] do
    for x in [0:n] do
      let idx := y * n + x
      if !fn.getD idx false && maskBit m y x then
        dark := dark.setIfInBounds idx (!dark.getD idx false)
  return ⟨n, dark, fn⟩

/-- The runs of equal modules along a line, as colour and length. -/
def runs (line : Array Bool) : Array (Bool × Nat) := Id.run do
  let mut out : Array (Bool × Nat) := #[]
  for b in line do
    match out.back? with
    | some (c, len) =>
      if c == b then out := out.pop.push (c, len + 1) else out := out.push (b, 1)
    | none => out := out.push (b, 1)
  return out

/-- The penalty of one row or column under rules 1 and 3 (§7.8.3, Table 11).
Rule 1: a run of five or more equal modules scores 3, and 1 more for each
module beyond five.  Rule 3: dark, light, dark, light, dark runs in the
proportion 1:1:3:1:1 with a light run at least four times the unit on either
side score 40, once for each such pattern.  Outside the symbol is the light
quiet zone, so a pattern at the edge has its four light modules there. -/
def linePenalty (line : Array Bool) : Nat := Id.run do
  let rs := runs line
  let mut score := 0
  for (_, len) in rs do
    if len ≥ 5 then score := score + len - 2
  -- The quiet zone on both sides, as long a light run as can matter.
  let edge := 4 * line.size + 4
  let mut padded : Array (Bool × Nat) := #[(false, edge)]
  for (c, len) in rs do
    match padded.back?, c with
    | some (false, l), false => padded := padded.pop.push (false, l + len)
    | _, _ => padded := padded.push (c, len)
  match padded.back? with
  | some (false, l) => padded := padded.pop.push (false, l + edge)
  | _ => padded := padded.push (false, edge)
  let len (i : Nat) : Nat := (padded.getD i (false, 0)).2
  for i in [3:padded.size - 3] do
    let (c, l) := padded.getD i (false, 0)
    if c && l % 3 == 0 && l > 0 then
      let u := l / 3
      if len (i - 2) == u && len (i - 1) == u && len (i + 1) == u && len (i + 2) == u &&
          (len (i - 3) ≥ 4 * u || len (i + 3) ≥ 4 * u) then
        score := score + 40
  return score

/-- The penalty of a symbol (§7.8.3): rules 1 and 3 along every row and
column; rule 2, 3 for each 2×2 block of equal modules, overlapping blocks
counted separately; and rule 4, 10 for each full 5% by which the proportion
of dark modules differs from one half. -/
def penalty (g : Grid) : Nat := Id.run do
  let n := g.size
  let mut score := 0
  for y in [0:n] do
    score := score + linePenalty ((Array.range n).map fun x => g.get x y)
  for x in [0:n] do
    score := score + linePenalty ((Array.range n).map fun y => g.get x y)
  for y in [0:n - 1] do
    for x in [0:n - 1] do
      let c := g.get x y
      if g.get (x + 1) y == c && g.get x (y + 1) == c && g.get (x + 1) (y + 1) == c then
        score := score + 3
  let dark := g.dark.foldl (fun k b => if b then k + 1 else k) 0
  let total := max 1 (n * n)
  let diff := if 20 * dark ≥ 10 * total then 20 * dark - 10 * total else 10 * total - 20 * dark
  return score + 10 * (diff / total)

/-- The symbol's rows. -/
def toMatrix (g : Grid) : Matrix :=
  (Array.range g.size).map fun y => (Array.range g.size).map fun x => g.get x y

end Grid

/-- The symbol for a version and level with the data codewords placed, before
masking. -/
def unmasked (level : Level) (version : Nat) (data : ByteArray) : Grid :=
  (Grid.functionPatterns version).placeCodewords
    (interleave level version (dataCodewords level version data))

/-- The symbol with mask `m` and its format information. -/
def withMask (level : Level) (g : Grid) (m : Nat) : Grid :=
  (g.applyMask m).drawFormat (formatInfo level m)

/-- The mask with the lowest penalty, the first of them on a tie. -/
def bestMask (level : Level) (g : Grid) : Nat := Id.run do
  let mut best := 0
  let mut bestScore := (withMask level g 0).penalty
  for m in [1:8] do
    let s := (withMask level g m).penalty
    if s < bestScore then
      best := m
      bestScore := s
  return best

/-- Encode bytes in the smallest version that holds them at `level`, with the
mask the penalty rules choose, or with mask `mask` if one is given; `none` if
the data is too long for any version. -/
def encode (data : ByteArray) (level : Level := .medium) (mask : Option Nat := none) :
    Option Matrix := do
  let version ← chooseVersion level data.size
  let g := unmasked level version data
  let m := mask.getD (bestMask level g) % 8
  return (withMask level g m).toMatrix

/-- Encode a string as its UTF-8 bytes. -/
def encodeText (s : String) (level : Level := .medium) : Option Matrix :=
  encode s.toUTF8 level

/-! ## SVG -/

/-- A symbol as SVG: a white square with the four-module quiet zone (§6.3.8)
and one path for the dark modules, one rectangle for each horizontal run, in
units of a module.  `crispEdges` keeps scaled modules from blurring into one
another. -/
def toSvg (m : Matrix) : String := Id.run do
  let dim := m.size + 8
  let mut d := ""
  for (row, y) in m.zipIdx do
    let mut x := 0
    while x < row.size do
      if row.getD x false then
        let mut e := x
        while e < row.size && row.getD e false do
          e := e + 1
        d := d ++ s!"M{x + 4},{y + 4}h{e - x}v1h-{e - x}z"
        x := e
      else
        x := x + 1
  return s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {dim} {dim}\" \
    shape-rendering=\"crispEdges\"><rect width=\"{dim}\" height=\"{dim}\" fill=\"#fff\"/>\
    <path fill=\"#000\" d=\"{d}\"/></svg>"

/-- The standard base64 alphabet of RFC 4648 §4, which `data:` URLs use. -/
def base64Alphabet : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

/-- Standard base64, with padding. -/
def base64 (b : ByteArray) : String := Id.run do
  let ch (n : Nat) : Char := base64Alphabet.getD (n % 64) 'A'
  let mut out := ""
  for i in [0:(b.size + 2) / 3] do
    let k := 3 * i
    let x := (b.data.getD k 0).toNat
    let y := (b.data.getD (k + 1) 0).toNat
    let z := (b.data.getD (k + 2) 0).toNat
    let n := (x * 256 + y) * 256 + z
    out := out.push (ch (n >>> 18)) |>.push (ch (n >>> 12))
    out := out.push (if k + 1 < b.size then ch (n >>> 6) else '=')
    out := out.push (if k + 2 < b.size then ch n else '=')
  return out

/-- A symbol as a `data:` URL of its SVG, for the `src` of an image, which the
Content Security Policy allows (`img-src 'self' data:`). -/
def toDataUrl (m : Matrix) : String :=
  "data:image/svg+xml;base64," ++ base64 (toSvg m).toUTF8

end QrCode
end Encoding
end Pyle