import PyleTests.Harness

/-!
# Second factors that are not WebAuthn

Base32 against RFC 4648 §10, HOTP against RFC 4226 Appendix D, TOTP against
RFC 6238 Appendix B, the replay rule of DESIGN.md §3, recovery codes, and
password hashing against the Argon2id vectors of the reference implementation
(`src/test.c` of github.com/P-H-C/phc-winner-argon2).
-/

namespace PyleTests

open Pyle
open Pyle.Factor

/-- RFC 4648 §10, and what the decoder must refuse. -/
private def base32Tests : IO Unit := do
  group "factor: base32 (RFC 4648)"
  let vectors := [("", ""), ("f", "MY======"), ("fo", "MZXQ===="), ("foo", "MZXW6==="),
    ("foob", "MZXW6YQ="), ("fooba", "MZXW6YTB"), ("foobar", "MZXW6YTBOI======")]
  for (plain, encoded) in vectors do
    checkEq s!"encode {plain.quote}" (base32Encode plain.toUTF8) encoded
    checkEq s!"decode {encoded.quote}" ((base32Decode encoded).map String.fromUTF8!) (some plain)
    let bare := String.ofList (encoded.toList.filter (· != '='))
    checkEq s!"decode {bare.quote} unpadded, lower case"
      ((base32Decode bare.toLower).map String.fromUTF8!) (some plain)
  check "rejects 0, 1, 8 and 9" (base32Decode "MZXW6YT0").isNone
  check "rejects padding in the middle" (base32Decode "MY==MZXQ").isNone
  check "rejects an impossible length" (base32Decode "MZX").isNone
  check "rejects non-zero trailing bits" (base32Decode "MZ").isNone
  check "rejects padding to a wrong length" (base32Decode "MY=").isNone
  let random ← Crypto.randomBytes 20
  checkEq "round trip" ((base32Decode (base32Encode random)).map (·.toList)) (some random.toList)

/-- RFC 4226 Appendix D and RFC 6238 Appendix B (the SHA-1 rows), then the
acceptance window and the replay rule. -/
private def totpTests : IO Unit := do
  group "factor: TOTP (RFC 4226, RFC 6238)"
  let secret := "12345678901234567890".toUTF8
  let hotp := ["755224", "287082", "359152", "969429", "338314", "254676", "287922", "162583",
    "399871", "520489"]
  for (expected, counter) in hotp.zipIdx do
    checkEq s!"RFC 4226 count {counter}" (Totp.hotp secret counter 6) expected
  let totp := [(59, "94287082"), (1111111109, "07081804"), (1111111111, "14050471"),
    (1234567890, "89005924"), (2000000000, "69279037"), (20000000000, "65353130")]
  for (time, expected) in totp do
    checkEq s!"RFC 6238 T = {time}, 8 digits" (Totp.hotp secret (Totp.stepOf time) 8) expected
    checkEq s!"RFC 6238 T = {time}, 6 digits" (Totp.code secret (Totp.stepOf time))
      (expected.drop 2).toString
  let now := 1111111111
  let step := Totp.stepOf now
  let codeAt (s : Nat) := Totp.code secret s
  checkEq "current step accepted" (Totp.verify secret now (codeAt step) none) (some step)
  checkEq "previous step accepted" (Totp.verify secret now (codeAt (step - 1)) none)
    (some (step - 1))
  checkEq "next step accepted" (Totp.verify secret now (codeAt (step + 1)) none) (some (step + 1))
  checkEq "two steps back refused" (Totp.verify secret now (codeAt (step - 2)) none) none
  checkEq "two steps ahead refused" (Totp.verify secret now (codeAt (step + 2)) none) none
  checkEq "replay of the same code refused" (Totp.verify secret now (codeAt step) (some step))
    none
  checkEq "earlier step after a later one refused"
    (Totp.verify secret now (codeAt (step - 1)) (some step)) none
  checkEq "later step after an earlier one accepted"
    (Totp.verify secret now (codeAt (step + 1)) (some step)) (some (step + 1))
  checkEq "wrong code refused" (Totp.verify secret now "000000" none)
    (if [step - 1, step, step + 1].any (codeAt · == "000000") then some step else none)
  checkEq "too short refused" (Totp.verify secret now ((codeAt step).drop 1).toString none) none
  checkEq "other secret refused"
    (Totp.verify "12345678901234567891".toUTF8 now (codeAt step) none) none
  checkEq "secret length" (← Totp.generateSecret).size 20
  checkEq "otpauth URI" (Totp.uri "pyle example" "alice@example.org" secret)
    ("otpauth://totp/pyle%20example:alice%40example.org" ++
      "?secret=GEZDGNBVGY3TQOJQGEZDGNBVGY3TQOJQ&issuer=pyle%20example" ++
      "&algorithm=SHA1&digits=6&period=30")

/-- Generation, shape and normalisation of recovery codes. -/
private def recoveryCodeTests : IO Unit := do
  group "factor: recovery codes"
  let codes ← RecoveryCode.generate
  checkEq "ten codes" codes.length 10
  checkEq "pairwise distinct" codes.eraseDups.length 10
  check "each well formed" (codes.all RecoveryCode.wellFormed)
  check "each eleven characters with the separator" (codes.all (·.length == 11))
  let key ← Crypto.randomBytes 32
  let digest := RecoveryCode.digest key "ABCDE-FGHIJ"
  check "case and separators do not matter"
    (Crypto.ctEqual digest (RecoveryCode.digest key " abcde fghij "))
  check "another code differs" (!Crypto.ctEqual digest (RecoveryCode.digest key "ABCDE-FGHIK"))
  check "another key differs"
    (!Crypto.ctEqual digest (RecoveryCode.digest (← Crypto.randomBytes 32) "ABCDE-FGHIJ"))
  checkEq "digest is HMAC-SHA256" digest.size 32
  check "wrong length is not well formed" (!RecoveryCode.wellFormed "ABCDE-FGHI")
  check "wrong alphabet is not well formed" (!RecoveryCode.wellFormed "ABCDE-FGHI1")

/-- RFC 4648 §10 for the PHC base64, the reference implementation's Argon2id
vectors through `verify`, and a fresh hash with the recommended parameters. -/
private def passwordTests : IO Unit := do
  group "factor: passwords (Argon2id)"
  let b64 := [("", ""), ("f", "Zg"), ("fo", "Zm8"), ("foo", "Zm9v"), ("foob", "Zm9vYg"),
    ("fooba", "Zm9vYmE"), ("foobar", "Zm9vYmFy")]
  for (plain, encoded) in b64 do
    checkEq s!"base64 {plain.quote}" (Password.b64Encode plain.toUTF8) encoded
    checkEq s!"unbase64 {encoded.quote}" ((Password.b64Decode encoded).map String.fromUTF8!)
      (some plain)
  check "PHC base64 rejects padding" (Password.b64Decode "Zg==").isNone
  try
    -- github.com/P-H-C/phc-winner-argon2, src/test.c, the Argon2id cases with
    -- 256 KiB of memory (the 64 MiB ones are left to the hash below).
    let reference := [
      "$argon2id$v=19$m=256,t=2,p=1$c29tZXNhbHQ$nf65EOgLrQMR/uIPnA4rEsF5h7TKyQwu9U1bMCHGi/4",
      "$argon2id$v=19$m=256,t=2,p=2$c29tZXNhbHQ$bQk8UB/VmZZF4Oo79iDXuL5/0ttZwg2f/5U52iv1cDc"]
    for phc in reference do
      check s!"reference {phc.take 31}… accepts \"password\"" (← Password.verify phc "password")
      check s!"reference {phc.take 31}… refuses \"Password\"" !(← Password.verify phc "Password")
    let phc ← Password.hash "correct horse battery staple"
    check "PHC prefix" (phc.startsWith "$argon2id$v=19$m=65536,t=3,p=4$")
    check "parses back to the recommended parameters"
      ((Password.parse? phc).map (·.1) == some Password.recommended)
    check "right password" (← Password.verify phc "correct horse battery staple")
    check "wrong password" !(← Password.verify phc "correct horse battery stapler")
    check "fresh salt" ((← Password.hash "x") != (← Password.hash "x"))
    check "malformed string" !(← Password.verify "$argon2id$v=19$m=256,t=2,p=1$c29tZXNhbHQ" "")
    check "Argon2i refused"
      !(← Password.verify
        "$argon2i$v=19$m=256,t=2,p=1$c29tZXNhbHQ$nf65EOgLrQMR/uIPnA4rEsF5h7TKyQwu9U1bMCHGi/4"
        "password")
    check "excessive memory refused without computing"
      !(← Password.verify
        "$argon2id$v=19$m=4194304,t=2,p=1$c29tZXNhbHQ$nf65EOgLrQMR/uIPnA4rEsF5h7TKyQwu9U1bMCHGi/4"
        "password")
    check "leading zeros refused"
      !(← Password.verify
        "$argon2id$v=19$m=0256,t=2,p=1$c29tZXNhbHQ$nf65EOgLrQMR/uIPnA4rEsF5h7TKyQwu9U1bMCHGi/4"
        "password")
  catch e =>
    check "Argon2id is available in the linked OpenSSL" false (toString e)

/-- Every test of the non-WebAuthn factors. -/
def factorTests : IO Unit := do
  base32Tests
  totpTests
  recoveryCodeTests
  passwordTests

end PyleTests