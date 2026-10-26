import PyleTests.Harness
import Pyle.Encoding.QrCode
import Pyle.Factor.Totp

/-!
# QR codes

The encoder's parts against published values: format information from the
table in Annex C of ISO/IEC 18004, the version information for version 7, and
the error correction codewords of the worked example in Annex I.  Then the
whole symbol against libqrencode: for several hundred inputs, from one byte to
the capacity of version 40, `qrencode -8` (byte mode, so that both choose the
same segmentation) must give exactly the same modules.  Where the two choose
different masks, the symbol is compared again with the mask qrencode chose
forced, and the inputs are listed; a symbol that differs even then fails.  If
`qrencode` is not installed, that comparison is skipped with a note.
-/

namespace PyleTests

open Pyle.Encoding.QrCode

/-- The level's letter for `qrencode -l`. -/
def levelLetter : Level → String
  | .low => "L"
  | .medium => "M"
  | .quartile => "Q"
  | .high => "H"

/-- The published parts. -/
def qrUnitTests : IO Unit := do
  group "qr: format and version information, Reed–Solomon"
  for (level, mask, bits) in [(Level.low, 0, 0x77C4), (.low, 4, 0x662F), (.medium, 0, 0x5412),
      (.medium, 5, 0x40CE), (.quartile, 0, 0x355F), (.high, 0, 0x1689), (.high, 7, 0x083B)] do
    checkEq s!"format information {levelLetter level}-{mask}" (formatInfo level mask) bits
  checkEq "version information 7" (versionInfo 7) 0x07C94
  checkEq "version information 40" (versionInfo 40) 0x28C69
  -- "01234567" in numeric mode at 1-M (Annex I.2 and I.3).
  let data := #[0x10, 0x20, 0x0C, 0x56, 0x61, 0x80, 0xEC, 0x11, 0xEC, 0x11, 0xEC, 0x11,
    0xEC, 0x11, 0xEC, 0x11]
  checkEq "Annex I error correction codewords" (eccCodewords (generator 10) data)
    #[0xA5, 0x24, 0xD4, 0xC1, 0xED, 0x36, 0xC7, 0x87, 0x2C, 0x55]
  checkEq "the Annex I data fills 1-M" (dataCapacity .medium 1) 16
  checkEq "1-M holds 14 bytes" (chooseVersion .medium 14) (some 1)
  checkEq "but not 15" (chooseVersion .medium 15) (some 2)
  checkEq "40-M holds 2331 bytes" (chooseVersion .medium 2331) (some 40)
  checkEq "and no more" (chooseVersion .medium 2332) none
  checkEq "40-L holds 2953 bytes" (chooseVersion .low 2953) (some 40)
  checkEq "the alignment patterns of version 32" (alignmentPositions 32) [6, 34, 60, 86, 112, 138]
  checkEq "total codewords of version 40" (totalCodewords 40) 3706
  match encode ByteArray.empty with
  | some m => checkEq "the empty string is a version 1 symbol" m.size 21
  | none => check "the empty string encodes" false
  match encodeText "otpauth://totp/a" with
  | some m =>
    let svg := toSvg m
    check "the SVG is one path" ((svg.splitOn "<path").length == 2)
    check "with a quiet zone in its view box"
      ((svg.splitOn s!"viewBox=\"0 0 {m.size + 8} {m.size + 8}\"").length == 2)
    check "and crisp edges" ((svg.splitOn "shape-rendering=\"crispEdges\"").length == 2)
    check "the data URL" ((toDataUrl m).startsWith "data:image/svg+xml;base64,PHN2Zy")
  | none => check "a short URI encodes" false
  checkEq "base64 with padding" (base64 "any carnal pleas".toUTF8) "YW55IGNhcm5hbCBwbGVhcw=="
  checkEq "base64 of two bytes" (base64 "ab".toUTF8) "YWI="

/-- qrencode's symbol for some bytes, with no margin, as a matrix; `none` if
it refuses them. -/
def qrencode (file : System.FilePath) (data : ByteArray) (level : Level) :
    IO (Option Matrix) := do
  IO.FS.writeBinFile file data
  let args := #["-8", "-l", levelLetter level, "-t", "ASCII", "-m", "0", "-r", file.toString,
    "-o", "-"]
  let out ← IO.Process.output { cmd := "qrencode", args }
  if out.exitCode != 0 then return none
  let rows := (out.stdout.splitOn "\n").filter (!·.isEmpty)
  return some <| rows.toArray.map fun row =>
    let cs := row.toList.toArray
    (Array.range (cs.size / 2)).map fun i => cs.getD (2 * i) ' ' == '#'

/-- The mask a symbol's format information names. -/
def maskOf (m : Matrix) : Nat :=
  let at_ (x y : Nat) : Bool := (m.getD y #[]).getD x false
  let pos := (List.range 6).map (fun i => (8, i)) ++ [(8, 7), (8, 8), (7, 8)] ++
    (List.range 6).map fun i => (5 - i, 8)
  let bits := pos.zipIdx.foldl (fun acc ((x, y), i) => if at_ x y then acc ||| 1 <<< i else acc) 0
  ((bits ^^^ 0x5412) >>> 10) &&& 7

/-- A deterministic stream of bytes, for inputs that look random. -/
def pseudoRandom (seed n : Nat) : ByteArray := Id.run do
  let mut s := seed
  let mut out := ByteArray.empty
  for _ in [0:n] do
    s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    out := out.push (s >>> 56).toUInt8
  return out

/-- Printable ASCII of length `n`, cycling through the characters. -/
def asciiOf (n : Nat) : ByteArray :=
  ⟨(Array.range n).map fun i => (33 + (i * 7) % 94).toUInt8⟩

/-- The inputs compared with qrencode, each with a name and a level. -/
def qrInputs : Array (String × ByteArray × Level) := Id.run do
  let mut out := #[]
  for b in [0, 10, 13, 0x41, 0x7F, 0x80, 0xFF] do
    out := out.push (s!"the byte {b}", ByteArray.empty.push b.toUInt8, Level.medium)
  for n in [1:301] do
    out := out.push (s!"{n} ASCII bytes", asciiOf n, .medium)
  for level in [Level.low, .medium, .quartile, .high] do
    for v in [1:41] do
      let cap := dataCapacity level v * 8 - 4 - countBits v
      let n := cap / 8
      for k in [n, n + 1] do
        out := out.push (s!"{k} bytes at the edge of {v}-{levelLetter level}",
          pseudoRandom (v * 7 + level.index) k, level)
  for i in [0:60] do
    let n := (i * 37) % 400 + 1
    out := out.push (s!"{n} random bytes ({i})", pseudoRandom (1000 + i) n, .medium)
  for (issuer, user) in [("id.example.org", "alice"), ("pyle.merten.dev", "christian"),
      ("a.example", "someone with a long name & symbols?"), ("x", "ü日本")] do
    for i in [0:3] do
      let uri := Pyle.Factor.Totp.uri issuer user (pseudoRandom (77 + i) 20)
      out := out.push (s!"the URI {uri}", uri.toUTF8, .medium)
  return out

/-- The comparison with qrencode. -/
def qrencodeTests : IO Unit := do
  group "qr: against qrencode"
  let present ← try
      let r ← IO.Process.output { cmd := "qrencode", args := #["--version"] }
      pure (r.exitCode == 0)
    catch _ => pure false
  if !present then
    say "  note: qrencode is not installed, so the comparison is skipped"
    return
  let file ← IO.FS.createTempFile >>= fun (h, p) => do h.flush; pure p
  let mut same := 0
  let mut tried := 0
  let mut maskOnly : Array String := #[]
  for (name, data, level) in qrInputs do
    let theirs? ← qrencode file data level
    let some mine := encode data level
      | check s!"{name}: too long for both" theirs?.isNone
    let some theirs := theirs?
      | check s!"qrencode encodes {name}" false
    tried := tried + 1
    if mine == theirs then
      same := same + 1
    else
      let m := maskOf theirs
      let forced := encode data level (some m)
      check s!"{name} with qrencode's mask {m}" (forced == some theirs)
        s!"ours has {mine.size} rows and mask {maskOf mine}, qrencode's {theirs.size}"
      maskOnly := maskOnly.push s!"{name}: mask {maskOf mine}, qrencode {m}"
  IO.FS.removeFile file
  say s!"  {same} of {tried} symbols identical to qrencode's"
  for s in maskOnly do say s!"  a different mask: {s}"
  checkEq "the masks qrencode chose" maskOnly.size 0

/-- All of them. -/
def qrCodeTests : IO Unit := do
  qrUnitTests
  qrencodeTests

end PyleTests