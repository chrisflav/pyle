import PyleTests.Harness
import LeanBiscuit.Crypto.Ed25519
import LeanBiscuit.Crypto.P256

/-!
# The constant-time boundary

The FFI shim and the Lean code around it, exercised through their Lean
declarations, against published vectors wherever there are some: RFC 2202
(HMAC-SHA1), RFC 5869 (HKDF), RFC 8439 (ChaCha20-Poly1305), RFC 8032
(Ed25519), RFC 9106 (Argon2id), RFC 7515 and RFC 8037 (JWS and JWK).

Signing is randomised for ES256 and has no published output to compare
against, so every ES256 and EdDSA signature the FFI makes here is checked
against `lean-biscuit`'s verifiers instead (DESIGN.md §6.2).
-/

namespace PyleTests

open Pyle
open Pyle.Crypto
open Pyle.Oidc
open Lean (Json)

/-- Bytes from hexadecimal.  A malformed literal is a bug in this file and
gives empty bytes, which the check using it then reports. -/
private def hex (s : String) : ByteArray := (LeanBiscuit.Bytes.ofHex? s).getD .empty

/-- Bytes as lower-case hexadecimal, for comparing and printing. -/
private def toHex (b : ByteArray) : String := LeanBiscuit.Bytes.toHex b

/-- The UTF-8 bytes of a string. -/
private def ascii (s : String) : ByteArray := s.toUTF8

/-- `n` copies of a byte. -/
private def repeatByte (b : UInt8) (n : Nat) : ByteArray := ⟨Array.replicate n b⟩

/-- A result as text: the hexadecimal bytes, or the error. -/
private def showBytes : Except String ByteArray → String
  | .ok b => toHex b
  | .error e => s!"error: {e}"

/-- Whether a result is an error. -/
private def isError : Except String α → Bool
  | .ok _ => false
  | .error _ => true

/-- Flip the lowest bit of the byte at `i`. -/
private def flip (b : ByteArray) (i : Nat) : ByteArray :=
  if i < b.size then b.set! i (b.get! i ^^^ 1) else b

/-- Whether `lean-biscuit` accepts a signature made by the FFI. -/
private def leanVerifies (alg : SigningAlgorithm) (publicKey message signature : ByteArray) :
    Bool :=
  match alg with
  | .es256 => (LeanBiscuit.P256.verify publicKey message signature).isOk
  | .edDsa => (LeanBiscuit.Ed25519.verify publicKey message signature).isOk
  | .rs256 => Ffi.rs256Verify publicKey message signature

/-- The RSA key of RFC 7515 Appendix A.2 as DER PKCS#8.  Derived from the JWK
printed there (`n`, `e`, `d`, `p`, `q`, `dp`, `dq`, `qi`) with Python's
`cryptography`; the test that its signature matches the RFC's byte for byte,
and that its JWK has the RFC's `n` and `e`, checks the derivation. -/
private def rfc7515RsaKey : ByteArray := hex <|
  "308204bd020100300d06092a864886f70d0101010500048204a7308204a30201000282010100a1f8" ++
  "160ae2e3c9b465ce8d2d656263362b927dbe29e1f02477fc1625cc90a136e38bd93497c5b6ea63dd" ++
  "7711e67c7429f956b0fb8a8f089adc4b69893cc1333f53edd019b87784252fec914fe4857769594b" ++
  "ea4280d32c0f55bf62944f130396bc6e9bdf6ebdd2bda3678eeca0c668f701b38dbffb38c8342ce2" ++
  "fe6d27fade4a5a4874979dd4b9cf9adec4c75b05852c2c0f5ef8a5c1750392f944e8ed64c110c6b6" ++
  "47609aa4783aeb9c6c9ad755313050638b83665c6f6f7a82a396702a1f641b82d3ebf2392219491f" ++
  "b686872c5716f50af8358d9a8b9d17c340728f7f87d89a18d8fcab67ad84590c2ecf759339363c07" ++
  "034d6f606f9e21e05456cae5e9a102030100010282010012ae71a469cd0a2bc37e526c4500571f1d" ++
  "61751d64e949707b62590f9d0ba57c963c401e3fcf2f2cd3bdec88e503bfc6439b0b28c82f7d3797" ++
  "671f5213eed8c15a25d8d5cea0025ee3ab2e8b7f79216fc63bea562753b40644c6a15127d9b29545" ++
  "40a0bbe1a30556982d4e9fde5f6425f14d4b713441b55dc73b9b4aedcc92ace3927e37f57d0cfd5e" ++
  "7581fa512c8f4961a9eb0b80f8a80746728a55ff46471f3425063b9d53642f5ede1e84d613081afa" ++
  "5c22d051285bd63b943b565d898a05685413e53c3c6c6525ff1fe34e3ddc70f0d56450fda48ba12e" ++
  "104e9deb9fb81881e1c4bdf25d9247f450c865927968e77334f4414f75a750e139546e3a8a739d02" ++
  "818100e01cc410eb48a6655d54464d0aa4bb6da0b872b774a6a9d11ffe480778f0ddb7311a7e902e" ++
  "f9c4b5f75476262ba8176cb35979f014372a1a2829e4136bd001d07c3f3f2e4f25d4c934f63c7109" ++
  "fba2e67628a0dc9a73c6058e6def22dcd50950e711ddc16d5586f2a7fa75ea8494c18083e0b65742" ++
  "f8a0d5e73fb2d970f0194702818100b903c47e0995b632f4532cb1f3c199145d5f3ae9c7dfeedc7a" ++
  "92a6b47e29c61b42a07aa95a64fc600999c5a7b01e01c08cb62ca756527bbcc56078fb0baba5ed38" ++
  "de2d07990ff6300faeadeb6c039a97bf1e507e4e7040fa78db8257c8b112ed5e59c3cd092fe5d4e5" ++
  "b51275d41281072a5e785ebaf3dae3709203133f5159d702818007029f577024ab9fcc1590c56429" ++
  "d6fb0ce5f820a8f375a866f9cb430093783bfcbb396e4529e6ef52374022dd86ba84d9ef58931bee" ++
  "c5d05fa53fcf23b633f8538a9eed51e87b097830a39f5d92937be6024b55db36f7e0c09dcbb72975" ++
  "387f615afbb6cb36bbabe7793c2b03ceab66dbb931baf50b55ec9af9311d001d628d0281810087ff" ++
  "7afa62b547fee0961b2e9bcd5d6718d39d8ca73db6691f38998de78771762c5da68cc243a5383b16" ++
  "6bb23dc570e84706ca801ef5f6bae6236a0aafa3770e8f54d1a8da1c5f8d2899f082331ddb0f5c8f" ++
  "3dfffa4c8d97102bdafe082a118da6633988880e4b55599ce67af26ebfa5b2c14a9de7b2c4dd96ab" ++
  "ddd2d2224c7502818021877b0c73a1ad6bf19303d0b11336b4e82b8db72b7efb50262a5df8395cc7" ++
  "256eb8cf6c40b7608d5936a32dba174126a527062ead8ca305fb7e177f409437c9dcb9718ed82018" ++
  "bcef0f7720a2c475f9db26da0e3cb516d084eb25178e828d5cabd49bb3161ac0181fa7f821e80e7a" ++
  "d37936f9943054ad092921ee2c592e4375"

/-- A test root CA (P-256, valid 2025 to 2125), made with the `openssl` command. -/
private def testRoot : ByteArray := hex <|
  "308201993082013fa003020102021429d4ebf9fa399194e94c5ec165bb8538a89c7d28300a06082a" ++
  "8648ce3d04030230193117301506035504030c0e70796c65207465737420726f6f743020170d3235" ++
  "303130313030303030305a180f32313235303130313030303030305a30193117301506035504030c" ++
  "0e70796c65207465737420726f6f743059301306072a8648ce3d020106082a8648ce3d0301070342" ++
  "000430aa912771b1ec07344083d77cb70d7452785d15588335b9ab4d0d9e7b428beccfaff0971489" ++
  "7612566619d7e50d97eb0470438d262732bce47bbde37e1c17dea3633061301d0603551d0e041604" ++
  "14b3353db18996e3148f314a80e6e8d61dc7d6c0f0301f0603551d23041830168014b3353db18996" ++
  "e3148f314a80e6e8d61dc7d6c0f0300f0603551d130101ff040530030101ff300e0603551d0f0101" ++
  "ff040403020106300a06082a8648ce3d04030203480030450220120186605ff6b09db32b336974fb" ++
  "7ded2f6e1853af8dedd422cd23874938e2fc022100913e2997f82279346319b27f8c7498ef4f0ea1" ++
  "e8b54d89580e74c174d91eebe1"

/-- An intermediate CA issued by `testRoot`. -/
private def testIntermediate : ByteArray := hex <|
  "3082018e30820134a003020102020102300a06082a8648ce3d04030230193117301506035504030c" ++
  "0e70796c65207465737420726f6f743020170d3235303130313030303030305a180f323132353031" ++
  "30313030303030305a3021311f301d06035504030c1670796c65207465737420696e7465726d6564" ++
  "696174653059301306072a8648ce3d020106082a8648ce3d03010703420004175334ac35bb9f5f2a" ++
  "8c19a278db4cbdbd4973d1321a2f0dccf9ed2693c88696247c0dcc0e95843e3eb8f2a2b6daf5c088" ++
  "53d7cfc3741015fe8bf99256e5ce1aa3633061300f0603551d130101ff040530030101ff300e0603" ++
  "551d0f0101ff040403020106301d0603551d0e04160414b820cb9f32ed42eac9ff65b61e98dddc5c" ++
  "536025301f0603551d23041830168014b3353db18996e3148f314a80e6e8d61dc7d6c0f0300a0608" ++
  "2a8648ce3d0403020348003045022100f40f5346a80f583f0745115d08f5f01c309bfbbaece6a367" ++
  "a7db5fc8dd2af68402201f3651663eb614ea9588c43a856d7b59f3a62c6fc5f02b5e0a8969d83296" ++
  "088b"

/-- A leaf certificate issued by `testIntermediate`. -/
private def testLeaf : ByteArray := hex <|
  "3082018930820131a003020102020103300a06082a8648ce3d0403023021311f301d06035504030c" ++
  "1670796c65207465737420696e7465726d6564696174653020170d3235303130313030303030305a" ++
  "180f32313235303130313030303030305a30193117301506035504030c0e70796c65207465737420" ++
  "6c6561663059301306072a8648ce3d020106082a8648ce3d03010703420004f7986d66164e8e9e04" ++
  "5ace892dcc0597724a8e3c2fbbbc2742c33ce0b1600974b517be0ef0dcefad85a451326e58e39942" ++
  "6efdad869f31c30111b75f0d629330a360305e300c0603551d130101ff04023000300e0603551d0f" ++
  "0101ff040403020780301d0603551d0e04160414b59ccf82e9194e16076cbc1553ce6db5a9292df7" ++
  "301f0603551d23041830168014b820cb9f32ed42eac9ff65b61e98dddc5c536025300a06082a8648" ++
  "ce3d0403020346003043021f65e655777139b0515dc203b6b4e65ca72b837508d57204808dc7f379" ++
  "fbf82b0220580901d6b66dfd76588898c4a58ef57ab747185a4faab7ebad3e64682af09fd9"

/-- A root CA unrelated to the others. -/
private def unrelatedRoot : ByteArray := hex <|
  "308201a330820149a00302010202143d0062460ab9570da19cc29830bb77fad1b836b9300a06082a" ++
  "8648ce3d040302301e311c301a06035504030c1370796c6520756e72656c6174656420726f6f7430" ++
  "20170d3235303130313030303030305a180f32313235303130313030303030305a301e311c301a06" ++
  "035504030c1370796c6520756e72656c6174656420726f6f743059301306072a8648ce3d02010608" ++
  "2a8648ce3d0301070342000427f6d4161b734dd46a0198fd869c1195a302aeb75be6232071f2617e" ++
  "3abf2625d8c47753c77b4f59cb6280c1dcf7c82ed1023d4947515c9ecd6ffef628a00941a3633061" ++
  "301d0603551d0e04160414f456e16bb7ecebafa4f2481bd777a17bf8727a43301f0603551d230418" ++
  "30168014f456e16bb7ecebafa4f2481bd777a17bf8727a43300f0603551d130101ff040530030101" ++
  "ff300e0603551d0f0101ff040403020106300a06082a8648ce3d0403020348003045022021e2e0e9" ++
  "1fd3d0116d2f63fc5de05fc6406f0afa26d3c63edcbad53c6884031f022100eadc218e850aca6093" ++
  "5d1de547a216d1239fbfa393754ec8f5c8811f29f58e70"


/-- Randomness and constant-time comparison. -/
private def primitiveTests : IO Unit := do
  group "crypto: ffi"
  let a ← randomBytes 32
  let b ← randomBytes 32
  checkEq "random bytes have the requested length" a.size 32
  check "two draws differ" (a != b)
  check "ctEqual: equal" (ctEqual a (a.extract 0 32))
  check "ctEqual: different" (!ctEqual a b)
  check "ctEqual: different lengths" (!ctEqual a (a.extract 0 31))
  checkEq "zero bytes" (← randomBytes 0).size 0

/-- RFC 2202 §3, all seven test cases. -/
private def hmacSha1Tests : IO Unit := do
  group "crypto: HMAC-SHA1 (RFC 2202)"
  let cases : List (String × ByteArray × ByteArray × String) := [
    ("1", repeatByte 0x0b 20, ascii "Hi There", "b617318655057264e28bc0b6fb378c8ef146be00"),
    ("2", ascii "Jefe", ascii "what do ya want for nothing?",
      "effcdf6ae5eb2fa2d27416d5f184df9c259a7c79"),
    ("3", repeatByte 0xaa 20, repeatByte 0xdd 50, "125d7342b9ac11cd91a39af48aa17b4f63f175d3"),
    ("4", hex "0102030405060708090a0b0c0d0e0f10111213141516171819", repeatByte 0xcd 50,
      "4c9007f4026250c6bc8414f9bf50c86c2d7235da"),
    ("5", repeatByte 0x0c 20, ascii "Test With Truncation",
      "4c1a03424b55e07fe7f27be1d58bb9324a9a5a04"),
    ("6", repeatByte 0xaa 80, ascii "Test Using Larger Than Block-Size Key - Hash Key First",
      "aa4ae5e15272d00e95705637ce8a3b55ed402112"),
    ("7", repeatByte 0xaa 80,
      ascii "Test Using Larger Than Block-Size Key and Larger Than One Block-Size Data",
      "e8e99d0f45237d786d6bbaa7965c7808bbff1a91")]
  for (n, key, data, digest) in cases do
    checkEq s!"test case {n}" (toHex (hmacSha1 key data)) digest

/-- RFC 5869 Appendix A, the three SHA-256 test cases. -/
private def hkdfTests : IO Unit := do
  group "crypto: HKDF-SHA256 (RFC 5869)"
  checkEq "A.1" (toHex (hkdfSha256 (repeatByte 0x0b 22) (hex "000102030405060708090a0b0c")
      (hex "f0f1f2f3f4f5f6f7f8f9") 42))
    ("3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf" ++
      "34007208d5b887185865")
  let range (lo : Nat) : ByteArray := ⟨(Array.range 80).map fun i => UInt8.ofNat (lo + i)⟩
  checkEq "A.2" (toHex (hkdfSha256 (range 0x00) (range 0x60) (range 0xb0) 82))
    ("b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c" ++
      "59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71" ++
      "cc30c58179ec3e87c14c01d5c1f3434f1d87")
  checkEq "A.3" (toHex (hkdfSha256 (repeatByte 0x0b 22) .empty .empty 42))
    ("8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d" ++
      "9d201395faa4b61a96c8")
  checkEq "A.1 extract" (toHex (hkdfSha256Extract (hex "000102030405060708090a0b0c")
      (repeatByte 0x0b 22)))
    "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"
  checkEq "output is capped at 255 blocks" (hkdfSha256 (repeatByte 1 32) .empty .empty 9000).size
    hkdfSha256MaxLength

/-- RFC 8439 §2.8.2, and the ways a sealed value must fail to open. -/
private def aeadTests : IO Unit := do
  group "crypto: ChaCha20-Poly1305 (RFC 8439)"
  let key := hex "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
  let nonce := hex "070000004041424344454647"
  let ad := hex "50515253c0c1c2c3c4c5c6c7"
  let plaintext := ascii ("Ladies and Gentlemen of the class of '99: If I could offer you " ++
    "only one tip for the future, sunscreen would be it.")
  let expected := "070000004041424344454647" ++
    "d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d6" ++
    "3dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b36" ++
    "92ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc" ++
    "3ff4def08e4b7a9de576d26586cec64b6116" ++
    "1ae10b594f09e26a7e902ecbd0600691"
  let sealed := sealWithNonce key nonce ad plaintext
  checkEq "§2.8.2: nonce, ciphertext and tag" (showBytes sealed) expected
  checkEq "§2.8.2: opens" (showBytes (sealed >>= «open» key ad)) (toHex plaintext)
  let key ← randomBytes 32
  let s ← «seal» key (ascii "row 7") (ascii "a secret")
  checkEq "seal adds nonce and tag" s.size (8 + 28)
  checkEq "round trip" (showBytes («open» key (ascii "row 7") s)) (toHex (ascii "a secret"))
  check "fresh nonce every time" ((← «seal» key .empty .empty) != (← «seal» key .empty .empty))
  checkEq "empty plaintext seals to 28 bytes" (← «seal» key .empty .empty).size 28
  check "empty plaintext round trip"
    (!isError («open» key .empty (← «seal» key .empty .empty)))
  check "other associated data fails" (isError («open» key (ascii "row 8") s))
  check "other key fails" (isError («open» (flip key 0) (ascii "row 7") s))
  check "modified nonce fails" (isError («open» key (ascii "row 7") (flip s 0)))
  check "modified ciphertext fails" (isError («open» key (ascii "row 7") (flip s 13)))
  check "modified tag fails" (isError («open» key (ascii "row 7") (flip s (s.size - 1))))
  check "truncated fails" (isError («open» key (ascii "row 7") (s.extract 0 27)))
  check "short key fails" (isError (sealWithNonce (key.extract 0 31) nonce .empty .empty))
  check "short nonce fails" (isError (sealWithNonce key (nonce.extract 0 11) .empty .empty))

/-- RFC 8032 §7.1, tests 1 to 3: Ed25519 is deterministic, so the FFI's
signatures must equal the published ones. -/
private def ed25519Tests : IO Unit := do
  group "crypto: Ed25519 (RFC 8032)"
  let vectors : List (String × String × String × String × String) := [
    ("1", "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
      "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a", "",
      "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155" ++
        "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"),
    ("2", "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
      "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c", "72",
      "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da" ++
        "085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00"),
    ("3", "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7",
      "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025", "af82",
      "6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac" ++
        "18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a")]
  for (n, seed, pub, msg, sig) in vectors do
    match SigningKey.ofEd25519Seed (hex seed) with
    | .error e => check s!"test {n}: key" false e
    | .ok k =>
      checkEq s!"test {n}: public key" (toHex k.publicKey) pub
      let s ← k.sign (hex msg)
      checkEq s!"test {n}: signature" (toHex s) sig
      check s!"test {n}: lean-biscuit verifies" (leanVerifies .edDsa k.publicKey (hex msg) s)

/-- Fresh keys of every algorithm: signatures verify (ES256 and EdDSA in Lean),
fail on another message, and survive serialisation. -/
private def keyTests : IO Unit := do
  group "crypto: signing keys"
  for alg in [SigningAlgorithm.es256, .edDsa, .rs256] do
    let k ← SigningKey.generate alg
    let name := alg.joseName
    let expectedSize := match alg with | .es256 => 33 | .edDsa => 32 | .rs256 => 294
    checkEq s!"{name}: public key size" k.publicKey.size expectedSize
    for i in [0:4] do
      let msg ← randomBytes (USize.ofNat (i * 41))
      let sig ← k.sign msg
      check s!"{name}: signature {i} verifies" (leanVerifies alg k.publicKey msg sig)
      check s!"{name}: signature {i} fails on another message"
        (!leanVerifies alg k.publicKey (msg.push 0) sig)
    match SigningKey.deserialize k.serialize with
    | .error e => check s!"{name}: deserialize" false e
    | .ok k' =>
      checkEq s!"{name}: same public key after round trip" (toHex k'.publicKey)
        (toHex k.publicKey)
      check s!"{name}: deserialised key signs" (leanVerifies alg k.publicKey
        (ascii "again") (← k'.sign (ascii "again")))
    let other := match alg with | .es256 => SigningAlgorithm.edDsa | _ => .es256
    check s!"{name}: refused as {other.joseName}" (isError (SigningKey.ofPkcs8 other k.pkcs8))
  check "empty serialised key" (isError (SigningKey.deserialize .empty))
  check "unknown algorithm code" (isError (SigningKey.deserialize (hex "07")))
  check "garbage" (isError (SigningKey.deserialize (hex "00300100")))
  check "short seed" (isError (SigningKey.ofEd25519Seed (repeatByte 1 31)))

/-- RFC 9106 §5.3, and the vectors of the reference implementation, which
`PyleTests.Factor` checks through `Password.verify`. -/
private def argon2Tests : IO Unit := do
  group "crypto: Argon2id (RFC 9106)"
  try
    let tag ← Ffi.argon2id (repeatByte 1 32) (repeatByte 2 16) (repeatByte 3 8) (repeatByte 4 12)
      3 32 4 32
    checkEq "§5.3" (toHex tag)
      "0d640df58d78766c08c037a34a8b53c9d01ef0452d75b65eb52520e96b01e659"
  catch e =>
    check "Argon2id is available in the linked OpenSSL" false (toString e)

/-- X.509 path validation over a three-certificate test PKI. -/
private def x509Tests : IO Unit := do
  group "crypto: X.509 chains"
  checkEq "leaf, intermediate, root" (showBytes (← verifyChain [testLeaf, testIntermediate]
    [testRoot])) (toHex testLeaf)
  checkEq "among several roots" (showBytes (← verifyChain [testLeaf, testIntermediate]
    [unrelatedRoot, testRoot])) (toHex testLeaf)
  checkEq "at a time inside the validity period" (showBytes (← verifyChainAt
    [testLeaf, testIntermediate] [testRoot] (some 1767225600))) (toHex testLeaf)
  check "before the validity period" (isError (← verifyChainAt [testLeaf, testIntermediate]
    [testRoot] (some 0)))
  check "after the validity period" (isError (← verifyChainAt [testLeaf, testIntermediate]
    [testRoot] (some 5000000000)))
  check "missing intermediate" (isError (← verifyChain [testLeaf] [testRoot]))
  check "unrelated root" (isError (← verifyChain [testLeaf, testIntermediate] [unrelatedRoot]))
  check "no roots" (isError (← verifyChain [testLeaf, testIntermediate] []))
  check "empty chain" (isError (← verifyChain [] [testRoot]))
  check "not DER" (isError (← verifyChain [hex "3000", testIntermediate] [testRoot]))
  check "trailing bytes" (isError (← verifyChain [testLeaf.push 0, testIntermediate] [testRoot]))

/-- The payload of RFC 7515's examples, with its CR LF line breaks. -/
private def rfc7515Payload : String :=
  "eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ"

/-- RFC 7515 Appendices A.2 and A.3, RFC 8037 Appendices A.2 to A.4, and
round trips through fresh keys of every algorithm. -/
private def joseTests : IO Unit := do
  group "crypto: JWS and JWK (RFC 7515, RFC 8037)"
  let payload := (Jose.b64urlDecode? rfc7515Payload).getD .empty
  checkEq "base64url round trip" (Jose.b64urlEncode payload) rfc7515Payload
  check "base64url rejects padding" (Jose.b64urlDecode? "Zg==").isNone
  -- RFC 7515 A.2: RS256 is deterministic.
  match SigningKey.ofPkcs8 .rs256 rfc7515RsaKey with
  | .error e => check "A.2: key" false e
  | .ok k =>
    let token ← Jwt.signBytes k (ascii "{\"alg\":\"RS256\"}") payload
    checkEq "A.2: JWS" token ("eyJhbGciOiJSUzI1NiJ9." ++ rfc7515Payload ++ "." ++
      "cC4hiUPoj9Eetdgtv3hF80EGrhuB__dzERat0XF9g2VtQgr9PJbu3XOiZj5RZmh7" ++
      "AAuHIm4Bh-0Qc_lF5YKt_O8W2Fp5jujGbds9uJdbF9CUAr7t1dnZcAcQjbKBYNX4" ++
      "BAynRFdiuB--f_nZLgrnbyTyWzO75vRK5h6xBArLIARNPvkSjtQBMHlb1L07Qe7K" ++
      "0GarZRmB_eSN9383LcOLn6_dO--xi12jzDwusC-eOkHWEsqtFZESc6BfI7noOPqv" ++
      "hJ1phCnvWh6IeYI2w9QOYEUipUTI8np6LbgGY9Fs98rqVt5AXLIhWkWywlVmtVrB" ++
      "p0igcN_IoypGlUPQGe77Rw")
    check "A.2: verifies" (!isError (Jwt.verifyBytes .rs256 k.publicKey token))
    match Jwk.ofSigningKey k with
    | .error e => check "A.2: JWK" false e
    | .ok jwk =>
      checkEq "A.2: JWK n" (jwk.getObjValAs? String "n" |>.toOption |>.getD "")
        ("ofgWCuLjybRlzo0tZWJjNiuSfb4p4fAkd_wWJcyQoTbji9k0l8W26mPddxHmfHQp-Vaw-4qPCJrcS2mJPMEzP1" ++
          "Pt0Bm4d4QlL-yRT-SFd2lZS-pCgNMsD1W_YpRPEwOWvG6b32690r2jZ47soMZo9wGzjb_7OMg0LOL-bSf63kp" ++
          "aSHSXndS5z5rexMdbBYUsLA9e-KXBdQOS-UTo7WTBEMa2R2CapHg665xsmtdVMTBQY4uDZlxvb3qCo5ZwKh9k" ++
          "G4LT6_I5IhlJH7aGhyxXFvUK-DWNmoudF8NAco9_h9iaGNj8q2ethFkMLs91kzk2PAcDTW9gb54h4FRWyuXpoQ")
      checkEq "A.2: JWK e" (jwk.getObjValAs? String "e" |>.toOption |>.getD "") "AQAB"
  -- RFC 7515 A.3: ES256 is randomised, so the published token is verified.
  let d := (Jose.b64urlDecode? "jpsQnnGQmL-YBIffH1136cspYG6-0iY7X1fCE9-E9LI").getD .empty
  match SigningKey.ofP256Scalar d with
  | .error e => check "A.3: key" false e
  | .ok k =>
    let token := "eyJhbGciOiJFUzI1NiJ9." ++ rfc7515Payload ++ "." ++
      "DtEhU3ljbEg8L38VWAfUAqOyKAM6-Xx-F4GawxaepmXFCgfTjDxw5djxLa8ISlSApmWQxfKTUJqPP3-Kg6NU1Q"
    check "A.3: published JWS verifies" (!isError (Jwt.verifyBytes .es256 k.publicKey token))
    check "A.3: but not as EdDSA" (isError (Jwt.verifyBytes .edDsa k.publicKey token))
    let ours ← Jwt.signBytes k (ascii "{\"alg\":\"ES256\"}") payload
    check "A.3: our JWS verifies in Lean" (!isError (Jwt.verifyBytes .es256 k.publicKey ours))
    match Jwk.ofSigningKey k with
    | .error e => check "A.3: JWK" false e
    | .ok jwk =>
      checkEq "A.3: JWK x" (jwk.getObjValAs? String "x" |>.toOption |>.getD "")
        "f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU"
      checkEq "A.3: JWK y" (jwk.getObjValAs? String "y" |>.toOption |>.getD "")
        "x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0"
  -- RFC 8037 A.1 to A.4: Ed25519 is deterministic.
  match SigningKey.ofEd25519Seed
      (hex "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60") with
  | .error e => check "RFC 8037: key" false e
  | .ok k =>
    checkEq "RFC 8037 A.3: thumbprint" (Jwk.keyId k |>.toOption |>.getD "")
      "kPrK_qmxVWaYVA9wwBF6Iuo3vVzz7TxHCTwXBygrS4k"
    match Jwk.ofSigningKey k with
    | .error e => check "RFC 8037 A.2: JWK" false e
    | .ok jwk =>
      checkEq "RFC 8037 A.2: JWK x" (jwk.getObjValAs? String "x" |>.toOption |>.getD "")
        "11qYAYKxCrfVS_7TyWQHOg7hcvPapiMlrwIaaPcHURo"
      checkEq "RFC 8037 A.2: JWK crv" (jwk.getObjValAs? String "crv" |>.toOption |>.getD "")
        "Ed25519"
    let token ← Jwt.signBytes k (ascii "{\"alg\":\"EdDSA\"}") (ascii "Example of Ed25519 signing")
    checkEq "RFC 8037 A.4: JWS" token
      ("eyJhbGciOiJFZERTQSJ9.RXhhbXBsZSBvZiBFZDI1NTE5IHNpZ25pbmc." ++
        "hgyY0il_MGCjP0JzlnLWG1PPOt7-09PGcvMg3AIbQR6dWbhijcNR4ki4iylGjg5BhVsPt9g7sVvpAr_MuM0KAg")
    check "RFC 8037 A.5: verifies" (!isError (Jwt.verifyBytes .edDsa k.publicKey token))
  -- Fresh keys: sign, verify, and every way a token must be refused.
  let claims := Json.mkObj [("iss", "https://auth.example.org"), ("sub", "alice"),
    ("aud", "client"), ("exp", (1300819380 : Nat))]
  let mut keys := []
  for alg in [SigningAlgorithm.es256, .edDsa, .rs256] do
    let k ← SigningKey.generate alg
    keys := keys ++ [k]
    let name := alg.joseName
    let kid := (Jwk.keyId k).toOption.getD ""
    let token ← Jwt.sign k kid claims
    match Jwt.verifyBytes alg k.publicKey token with
    | .error e => check s!"{name}: verifies" false e
    | .ok (header, _) =>
      checkEq s!"{name}: header alg" (header.getObjValAs? String "alg" |>.toOption |>.getD "")
        name
      checkEq s!"{name}: header kid" (header.getObjValAs? String "kid" |>.toOption |>.getD "")
        kid
    checkEq s!"{name}: claims" ((Jwt.verify alg k.publicKey token).toOption.map (·.compress))
      (some claims.compress)
    let other := match alg with | .es256 => SigningAlgorithm.edDsa | _ => .es256
    check s!"{name}: refused as {other.joseName}"
      (isError (Jwt.verify other k.publicKey token))
    let parts := token.splitOn "."
    let forged := ".".intercalate [parts[0]!, Jose.b64urlEncode (ascii "{\"sub\":\"mallory\"}"),
      parts[2]!]
    check s!"{name}: modified payload refused" (isError (Jwt.verify alg k.publicKey forged))
    let unsigned := ".".intercalate [Jose.b64urlEncode (ascii "{\"alg\":\"none\"}"), parts[1]!, ""]
    check s!"{name}: alg none refused" (isError (Jwt.verify alg k.publicKey unsigned))
    check s!"{name}: two parts refused"
      (isError (Jwt.verify alg k.publicKey (parts[0]! ++ "." ++ parts[1]!)))
    check s!"{name}: another key refused"
      (isError (Jwt.verify alg (← SigningKey.generate alg).publicKey token))
  match Jwk.set keys with
  | .error e => check "JWKS" false e
  | .ok set =>
    checkEq "JWKS has every key"
      ((set.getObjValAs? (Array Json) "keys").toOption.map (·.size)) (some 3)

/-- Every test of the cryptographic boundary. -/
def cryptoTests : IO Unit := do
  primitiveTests
  hmacSha1Tests
  hkdfTests
  aeadTests
  ed25519Tests
  keyTests
  argon2Tests
  x509Tests
  joseTests

end PyleTests