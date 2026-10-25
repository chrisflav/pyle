import PyleTests.Harness
import PyleTests.WebAuthnVectors

/-!
# WebAuthn

The encodings first, against their RFCs' examples; then the W3C test vectors,
each registered and then used to sign in; then assertions made here with
`lean-biscuit`'s signers (in tests only, DESIGN §6.2), one accepted and one
broken for every check of DESIGN §2.1, so each check is seen to refuse on its
own.
-/

namespace PyleTests

open Pyle Pyle.Encoding Pyle.WebAuthn LeanBiscuit
open PyleTests.WebAuthnVectors

/-- Bytes from hex, which every vector is written in. -/
def hex (s : String) : ByteArray := (Bytes.ofHex? s).getD .empty

/-- Bytes as hex, for messages. -/
def toHex (b : ByteArray) : String := Bytes.toHex b

/-! ## Base64url -/

/-- RFC 4648 §10, whose examples use no character that differs between the
two alphabets, and the two that do. -/
def base64UrlTests : IO Unit := do
  group "webauthn: base64url"
  for (plain, enc) in [("", ""), ("f", "Zg"), ("fo", "Zm8"), ("foo", "Zm9v"), ("foob", "Zm9vYg"),
      ("fooba", "Zm9vYmE"), ("foobar", "Zm9vYmFy")] do
    checkEq s!"encode {plain.quote}" (Base64Url.encode plain.toUTF8) enc
    checkEq s!"decode {enc.quote}" ((Base64Url.decode enc).map toHex) (some (toHex plain.toUTF8))
  checkEq "the url-safe characters" (Base64Url.encode (hex "fbff")) "-_8"
  checkEq "decode the url-safe characters" ((Base64Url.decode "-_8").map toHex) (some "fbff")
  for bad in ["Z", "Zh", "Zm9", "Zg==", "Zm9v+", "Zm9v/", "Zm 9v", "Zm9vY"] do
    check s!"refuse {bad.quote}" (Base64Url.decode bad).isNone
  -- every byte value, at every position modulo three
  let all := ByteArray.mk ((List.range 256).map UInt8.ofNat).toArray
  for k in [0, 1, 2] do
    let b := all.extract k all.size
    checkEq s!"round trip of 256 - {k} bytes" ((Base64Url.decode (Base64Url.encode b)).map toHex)
      (some (toHex b))

/-! ## CBOR -/

/-- RFC 8949 Appendix A, for the items this decoder supports. -/
def cborExamples : List (Cbor × String) := [
  (.unsigned 0, "00"), (.unsigned 1, "01"), (.unsigned 10, "0a"), (.unsigned 23, "17"),
  (.unsigned 24, "1818"), (.unsigned 25, "1819"), (.unsigned 100, "1864"),
  (.unsigned 1000, "1903e8"), (.unsigned 1000000, "1a000f4240"),
  (.unsigned 1000000000000, "1b000000e8d4a51000"),
  (.unsigned 18446744073709551615, "1bffffffffffffffff"),
  (.negative 0, "20"), (.negative 9, "29"), (.negative 99, "3863"), (.negative 999, "3903e7"),
  (.negative 18446744073709551615, "3bffffffffffffffff"),
  (.simple 20, "f4"), (.simple 21, "f5"), (.simple 22, "f6"), (.simple 23, "f7"),
  (.simple 16, "f0"),
  (.bytes .empty, "40"), (.bytes (hex "01020304"), "4401020304"),
  (.text "", "60"), (.text "a", "6161"), (.text "IETF", "6449455446"),
  (.text "\"\\", "62225c"), (.text "ü", "62c3bc"), (.text "水", "63e6b0b4"),
  (.array [], "80"), (.array [.unsigned 1, .unsigned 2, .unsigned 3], "83010203"),
  (.array [.unsigned 1, .array [.unsigned 2, .unsigned 3], .array [.unsigned 4, .unsigned 5]],
    "8301820203820405"),
  (.array ((List.range 25).map fun i => .unsigned (i + 1)),
    "98190102030405060708090a0b0c0d0e0f101112131415161718181819"),
  (.map [], "a0"), (.map [(.unsigned 1, .unsigned 2), (.unsigned 3, .unsigned 4)], "a201020304"),
  (.map [(.text "a", .unsigned 1), (.text "b", .array [.unsigned 2, .unsigned 3])],
    "a26161016162820203"),
  (.array [.text "a", .map [(.text "b", .text "c")]], "826161a161626163"),
  (.map [(.text "a", .text "A"), (.text "b", .text "B"), (.text "c", .text "C"),
    (.text "d", .text "D"), (.text "e", .text "E")],
    "a56161614161626142616361436164614461656145")]

/-- Inputs the decoder must refuse, with the reason. -/
def cborRefused : List (String × String) := [
  ("", "empty input"), ("18", "truncated argument"), ("1817", "non-minimal one-byte argument"),
  ("190017", "non-minimal two-byte argument"), ("1c", "reserved additional information"),
  ("5f42010243030405ff", "indefinite-length byte string"), ("9f018202039f0405ffff",
    "indefinite-length array"), ("f97c00", "half-precision float"),
  ("fb3ff199999999999a", "double-precision float"), ("f820", "two-byte simple value"),
  ("c074323031332d30332d32315432303a30343a30305a", "tag"), ("0101", "trailing byte"),
  ("62c3", "truncated text"), ("62c328", "invalid UTF-8"), ("4401", "truncated bytes"),
  ("9bffffffffffffffff", "array longer than the input"),
  ("bbffffffffffffffff", "map longer than the input"),
  (String.join (List.replicate 20 "81") ++ "00", "nesting deeper than the bound"),
  ("a10102a1", "trailing incomplete item")]

/-- The CBOR tests. -/
def cborTests : IO Unit := do
  group "webauthn: cbor"
  for (c, h) in cborExamples do
    checkEq s!"encode {h}" (toHex (Cbor.encode c)) h
    checkEq s!"decode {h}" ((Cbor.decode (hex h)).map fun c => toHex (Cbor.encode c)) (some h)
  for (h, why) in cborRefused do
    check s!"refuse: {why}" (Cbor.decode (hex h)).isNone
  check "sixteen levels decode"
    (Cbor.decode (hex (String.join (List.replicate 15 "81") ++ "00"))).isSome
  check "seventeen levels do not"
    (Cbor.decode (hex (String.join (List.replicate 16 "81") ++ "00"))).isNone
  let entries := [(Cbor.unsigned 1, Cbor.unsigned 2), (.unsigned 1, .unsigned 3)]
  check "a repeated key is refused by lookup"
    ((Cbor.lookup entries (.int 1)) matches Except.error _)
  check "a missing key is none" ((Cbor.lookup entries (.int 2)) matches Except.ok none)
  check "a negative key is found"
    ((Cbor.lookup [(.negative 0, .unsigned 7)] (.int (-1))) matches Except.ok (some (.unsigned 7)))

/-! ## DER -/

/-- The attestation root of §16.1 is a P-256 CA certificate. -/
def derTests : IO Unit := do
  group "webauthn: der"
  match Der.parseCertificate (hex attestationCaCert) with
  | none => check "the §16.1 root certificate parses" false
  | some c =>
    checkEq "version 3" c.version 2
    check "a P-256 key" c.p256Point.isSome
    check "on the curve" (c.p256Point.bind compressUncompressedP256).isSome
    check "a CA" (c.isCa == some true)
    checkEq "subject OU" (c.subjectAttribute Der.oidOrganizationalUnit)
      (some ["Authenticator Attestation CA"])
  check "truncated certificate"
    (Der.parseCertificate ((hex attestationCaCert).extract 0 300)).isNone
  check "empty input" (Der.parseCertificate .empty).isNone

/-! ## The W3C vectors -/

/-- The relying party every vector was made for.  Not every vector's
authenticator verified the user, so verification is not required here; the
vectors that did are checked again with it required. -/
def exampleRp : RelyingParty :=
  { id := "example.org", origins := ["https://example.org"], requireUserVerification := false }

/-- A short name for an attestation kind. -/
def kindName : AttestationKind → String
  | .none => "none"
  | .packedSelf => "packed self"
  | .packedFull x5c => s!"packed full ({x5c.length} certificates)"

/-- An outcome of registration, with the reason in the parse errors left out. -/
def regOutcome : Except RegistrationError NewCredential → String
  | .ok c => s!"ok, {kindName c.attestation}"
  | .error (.clientData _) => "clientData"
  | .error (.attestationObject _) => "attestationObject"
  | .error (.authenticatorData _) => "authenticatorData"
  | .error (.attestation _) => "attestation"
  | .error e => reprStr e

/-- The reason an attestation statement was refused, or `""` if it was not. -/
def attestationReason : Except RegistrationError NewCredential → String
  | .error (.attestation reason) => reason
  | _ => ""

/-- Whether `needle` occurs in `s`. -/
def mentions (s needle : String) : Bool := (s.splitOn needle).length > 1

/-- An outcome of authentication, likewise. -/
def assertOutcome : Except AssertionError VerifiedAssertion → String
  | .ok _ => "ok"
  | .error (.clientData _) => "clientData"
  | .error (.authenticatorData _) => "authenticatorData"
  | .error e => reprStr e

/-- The registration a vector describes. -/
def WebAuthnVectors.Vector.registration (v : Vector) : RegistrationResponse :=
  { clientDataJSON := hex v.regClientDataJSON, attestationObject := hex v.attestationObject,
    transports := [] }

/-- The assertion a vector describes, for a credential registered from it. -/
def WebAuthnVectors.Vector.assertion (v : Vector) (id : ByteArray) : AssertionResponse :=
  { credentialId := id, clientDataJSON := hex v.authClientDataJSON,
    authenticatorData := hex v.authenticatorData, signature := hex v.signature,
    userHandle := none }

/-- Register a vector, check what registration found against what the vector
says, and sign in with it. -/
def acceptVector (v : Vector) (alg : CoseAlgorithm) (kind : String) : IO Unit := do
  let name := s!"§{v.section_}"
  match verifyRegistration exampleRp (hex v.regChallenge) [.es256, .edDsa] v.registration with
  | .error e => check s!"{name}: registration" false (reprStr e)
  | .ok c =>
    checkEq s!"{name}: attestation" (kindName c.attestation) kind
    checkEq s!"{name}: credential id" (toHex c.id) v.credentialId
    checkEq s!"{name}: aaguid" (toHex c.aaguid) v.aaguid
    let expected := match alg with
      | .es256 => P256.publicKeyOfSecret (hex v.privateKey)
      | .edDsa => Ed25519.publicKeyOfSecret (hex v.privateKey)
    checkEq s!"{name}: public key is the private key's" (some (toHex c.publicKey.bytes))
      (expected.map toHex)
    check s!"{name}: algorithm" (c.publicKey.algorithm == alg)
    let stored := c.toStored (hex "01")
    let r := verifyAssertion exampleRp (hex v.authChallenge) (some [c.id]) stored (v.assertion c.id)
    checkEq s!"{name}: authentication" (assertOutcome r) "ok"
    let wrong := verifyAssertion exampleRp (hex v.regChallenge) none stored (v.assertion c.id)
    checkEq s!"{name}: authentication against another challenge" (assertOutcome wrong)
      (reprStr AssertionError.challengeMismatch)

/-- Expect a vector's registration to be refused. -/
def refuseVector (v : Vector) (rp : RelyingParty) (why expected : String) : IO Unit :=
  checkEq s!"§{v.section_}: refused, {why}"
    (regOutcome (verifyRegistration rp (hex v.regChallenge) [.es256, .edDsa] v.registration))
    expected

/-- Replace the first occurrence of a hex fragment. -/
def patchHex (h old new : String) : String := h.replace old new

/-- The vector tests. -/
def vectorTests : IO Unit := do
  group "webauthn: W3C test vectors"
  acceptVector noneEs256 .es256 "none"
  acceptVector packedSelfEs256 .es256 "packed self"
  acceptVector noneEs256LongCredentialId .es256 "none"
  acceptVector packedEs256 .es256 "packed full (1 certificates)"
  acceptVector packedEdDsa .edDsa "packed full (1 certificates)"
  -- §16.4 and §16.5 come from cross-origin frames: refused unless the browser
  -- names the top-level origin and it is allowed, which §16.4 does not
  refuseVector noneEs256CrossOrigin exampleRp "crossOrigin" (reprStr RegistrationError.crossOrigin)
  refuseVector noneEs256TopOrigin exampleRp "topOrigin" (reprStr RegistrationError.crossOrigin)
  let framed := { exampleRp with allowedTopOrigins := ["https://example.com"] }
  refuseVector noneEs256CrossOrigin framed "crossOrigin without a topOrigin"
    (reprStr RegistrationError.crossOrigin)
  refuseVector noneEs256TopOrigin { exampleRp with allowedTopOrigins := ["https://example.net"] }
    "a topOrigin that is not allowed" (reprStr RegistrationError.crossOrigin)
  for v in [noneEs256TopOrigin] do
    match verifyRegistration framed (hex v.regChallenge) [.es256] v.registration with
    | .error e => check s!"§{v.section_}: registration when framing is allowed" false (reprStr e)
    | .ok c =>
      let stored := c.toStored (hex "01")
      checkEq s!"§{v.section_}: authentication when framing is allowed"
        (assertOutcome (verifyAssertion framed (hex v.authChallenge) none stored
          (v.assertion c.id)))
        "ok"
      checkEq s!"§{v.section_}: authentication when framing is not allowed"
        (assertOutcome (verifyAssertion exampleRp (hex v.authChallenge) none stored
          (v.assertion c.id))) (reprStr AssertionError.crossOrigin)
  -- algorithms we do not support never get as far as the attestation
  for v in [packedEs384, packedEs512, packedRs256, packedEd448] do
    refuseVector v exampleRp "unsupported credential algorithm" "authenticatorData"
  -- nor do attestation formats we do not accept
  for v in [tpmEs256, androidKeyEs256, appleEs256, fidoU2fEs256] do
    refuseVector v exampleRp "unsupported attestation format" "attestation"
  -- the policy and the offer
  refuseVector noneEs256 { exampleRp with requireUserVerification := true } "user not verified"
    (reprStr RegistrationError.userNotVerified)
  checkEq "§16.2: refused when only EdDSA was offered"
    (regOutcome (verifyRegistration exampleRp (hex noneEs256.regChallenge) [.edDsa]
      noneEs256.registration)) (reprStr RegistrationError.algorithmNotOffered)
  refuseVector noneEs256 { exampleRp with id := "example.com" } "another relying party id"
    (reprStr RegistrationError.rpIdHashMismatch)
  refuseVector noneEs256 { exampleRp with origins := ["https://example.com"] } "another origin"
    (reprStr RegistrationError.originMismatch)
  checkEq "§16.2: refused for another challenge"
    (regOutcome (verifyRegistration exampleRp (hex noneEs256.authChallenge) [.es256]
      noneEs256.registration)) (reprStr RegistrationError.challengeMismatch)
  checkEq "§16.2: the authentication client data is not a registration's"
    (regOutcome (verifyRegistration exampleRp (hex noneEs256.authChallenge) [.es256]
      { noneEs256.registration with clientDataJSON := hex noneEs256.authClientDataJSON }))
    (reprStr RegistrationError.wrongType)
  -- a self attestation over other client data no longer verifies
  checkEq "§16.3: self attestation over altered client data"
    (regOutcome (verifyRegistration exampleRp (hex packedSelfEs256.regChallenge) [.es256]
      { packedSelfEs256.registration with
        clientDataJSON := hex packedSelfEs256.regClientDataJSON ++ hex "20" }))
    "attestation"
  -- altered authenticator data under a full attestation: the §16.7 leaf has no
  -- AAGUID extension, so it is the signature that fails (the AAGUID check is
  -- tested on hand-built certificates below)
  let otherAaguid := patchHex packedEs256.attestationObject packedEs256.aaguid
    "00000000000000000000000000000000"
  check "§16.7: altered authenticator data fails the leaf signature"
    (mentions (attestationReason (verifyRegistration exampleRp (hex packedEs256.regChallenge)
      [.es256] { packedEs256.registration with attestationObject := hex otherAaguid }))
      "does not verify under the leaf certificate")
  -- a none statement must be empty
  let notEmpty := patchHex noneEs256.attestationObject "6761747453746d74a0"
    "6761747453746d74a1616101"
  checkEq "§16.2: a none statement with content"
    (regOutcome (verifyRegistration exampleRp (hex noneEs256.regChallenge) [.es256]
      { noneEs256.registration with attestationObject := hex notEmpty })) "attestation"
  -- the attestation object must be well-formed and have nothing extra
  checkEq "§16.2: an attestation object with trailing bytes"
    (regOutcome (verifyRegistration exampleRp (hex noneEs256.regChallenge) [.es256]
      { noneEs256.registration with
        attestationObject := hex noneEs256.attestationObject ++ hex "00" }))
    "attestationObject"
  -- the user-verifying vectors pass when verification is required
  let uvRp := { exampleRp with requireUserVerification := true }
  match verifyRegistration uvRp (hex packedSelfEs256.regChallenge) [.es256]
      packedSelfEs256.registration with
  | .error e => check "§16.3: registration with verification required" false (reprStr e)
  | .ok c =>
    check "§16.3: the user was verified at registration" c.userVerified
    let stored := c.toStored (hex "01")
    -- the assertion of §16.3 did not verify the user
    checkEq "§16.3: authentication without verification, when required"
      (assertOutcome (verifyAssertion uvRp (hex packedSelfEs256.authChallenge) none stored
        (packedSelfEs256.assertion c.id))) (reprStr AssertionError.userNotVerified)

/-! ## Generated assertions -/

/-- The P-256 key of RFC 6979 §A.2.5, used here only to sign test assertions. -/
def p256Secret : ByteArray := hex "c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721"

/-- The Ed25519 key of RFC 8032 §7.1, test 1, likewise. -/
def ed25519Secret : ByteArray :=
  hex "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"

/-- The relying party of the generated tests. -/
def testRp : RelyingParty := { id := "auth.example.org", origins := ["https://auth.example.org"] }

/-- The pending challenge of the generated tests. -/
def testChallenge : ByteArray :=
  hex "6a7d43b1e8ad0a7e3f4f5c6d7e8f90a1b2c3d4e5f60718293a4b5c6d7e8f9001"

/-- The credential id of the generated tests. -/
def testCredentialId : ByteArray := hex "c0ffee00c0ffee00c0ffee00c0ffee00"

/-- The user handle of the generated tests. -/
def testUserHandle : ByteArray :=
  hex "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"

/-- What a generated assertion says, each field ready to be broken. -/
structure Gen where
  /-- The relying party id the authenticator hashes. -/
  rpId : String := "auth.example.org"
  /-- The flags: user present and verified, by default. -/
  flags : UInt8 := 0x05
  /-- The counter. -/
  signCount : Nat := 7
  /-- The client data type. -/
  type : String := "webauthn.get"
  /-- The challenge, before encoding. -/
  challenge : ByteArray := testChallenge
  /-- The origin. -/
  origin : String := "https://auth.example.org"
  /-- Further members of the client data, each starting with a comma. -/
  extra : String := ""
  /-- The credential id the browser reports. -/
  credentialId : ByteArray := testCredentialId
  /-- The user handle the authenticator returns. -/
  userHandle : Option ByteArray := some testUserHandle

/-- The client data of a generated assertion. -/
def Gen.clientData (g : Gen) : ByteArray :=
  let challenge := Base64Url.encode g.challenge
  s!"\{\"type\":\"{g.type}\",\"challenge\":\"{challenge}\",\"origin\":\"{g.origin}\"{g.extra}}"
    |>.toUTF8

/-- The authenticator data of a generated assertion. -/
def Gen.authData (g : Gen) : ByteArray :=
  Sha256.hash g.rpId.toUTF8 ++ ByteArray.mk #[g.flags] ++ Bytes.ofNatBE 4 g.signCount

/-- Sign a generated assertion with a secret key. -/
def Gen.sign (g : Gen) (alg : CoseAlgorithm) (secret : ByteArray) : AssertionResponse :=
  let ad := g.authData
  let cd := g.clientData
  let message := ad ++ Sha256.hash cd
  let signature := match alg with
    | .es256 => (P256.sign secret message).getD .empty
    | .edDsa => (Ed25519.sign secret message).getD .empty
  { credentialId := g.credentialId, clientDataJSON := cd, authenticatorData := ad, signature,
    userHandle := g.userHandle }

/-- The stored credential of a secret key. -/
def storedFor (alg : CoseAlgorithm) (secret : ByteArray) (signCount : UInt32 := 6)
    (backupEligible : Bool := false) : StoredCredential :=
  let bytes := match alg with
    | .es256 => (P256.publicKeyOfSecret secret).getD .empty
    | .edDsa => (Ed25519.publicKeyOfSecret secret).getD .empty
  { id := testCredentialId, userHandle := testUserHandle, publicKey := { algorithm := alg, bytes },
    signCount, backupEligible }

/-- Check the outcome of an assertion. -/
def expectAssertion (name : String) (r : Except AssertionError VerifiedAssertion)
    (expected : String) : IO Unit :=
  checkEq name (assertOutcome r) expected

/-- One accepted assertion and one refusal per check of DESIGN §2.1. -/
def generatedTests : IO Unit := do
  group "webauthn: generated assertions"
  let es := storedFor .es256 p256Secret
  let ed := storedFor .edDsa ed25519Secret
  let verify (g : Gen) (cred : StoredCredential := es) (rp := testRp)
      (allow : Option (List ByteArray) := none) (secret := p256Secret)
      (alg := CoseAlgorithm.es256) (requireUserHandle := false) :=
    verifyAssertion rp testChallenge allow cred (g.sign alg secret) requireUserHandle
  let err (e : AssertionError) := reprStr e
  -- accepted
  match verify {} with
  | .error e => check "ES256: accepted" false (reprStr e)
  | .ok v =>
    checkEq "ES256: the credential" (toHex v.credentialId) (toHex testCredentialId)
    checkEq "ES256: the user" (toHex v.userHandle) (toHex testUserHandle)
    check "ES256: user verified" v.userVerified
    checkEq "ES256: the new counter" v.signCount 7
  expectAssertion "EdDSA: accepted" (verify {} ed (secret := ed25519Secret) (alg := .edDsa)) "ok"
  expectAssertion "accepted from an allowed credential"
    (verify {} (allow := some [hex "00", testCredentialId])) "ok"
  expectAssertion "accepted without a user handle" (verify { userHandle := none }) "ok"
  expectAssertion "accepted with crossOrigin false" (verify { extra := ",\"crossOrigin\":false" })
    "ok"
  expectAssertion "accepted with members a later browser may add"
    (verify { extra := ",\"other\":[1,{\"a\":null}]" }) "ok"
  expectAssertion "accepted without verification when the policy allows"
    (verify { flags := 0x01 } (rp := { testRp with requireUserVerification := false })) "ok"
  expectAssertion "accepted with both counters zero"
    (verify { signCount := 0 } (storedFor .es256 p256Secret 0)) "ok"
  expectAssertion "accepted when backed up and backup-eligible"
    (verify { flags := 0x1d } (storedFor .es256 p256Secret (backupEligible := true))) "ok"
  -- 1. the credential
  expectAssertion "1: another credential id" (verify { credentialId := hex "c0ffee01" })
    (err .credentialMismatch)
  expectAssertion "1: not among allowCredentials" (verify {} (allow := some [hex "00"]))
    (err .credentialNotAllowed)
  expectAssertion "1: an empty allowCredentials means none" (verify {} (allow := some []))
    "ok"
  -- 2. the user handle
  expectAssertion "2: discoverable flow with a user handle"
    (verify {} (requireUserHandle := true)) "ok"
  expectAssertion "2: discoverable flow without a user handle"
    (verify { userHandle := none } (requireUserHandle := true)) (err .userHandleMissing)
  expectAssertion "2: another user handle" (verify { userHandle := some (hex "0011") })
    (err .userHandleMismatch)
  -- 3. the client data
  let broken : AssertionResponse :=
    { ((Gen.sign {} .es256 p256Secret)) with clientDataJSON := "{\"type\":".toUTF8 }
  expectAssertion "3: client data that does not parse"
    (verifyAssertion testRp testChallenge none es broken) "clientData"
  expectAssertion "3: client data without a challenge"
    (verifyAssertion testRp testChallenge none es
      { broken with clientDataJSON := "{\"type\":\"webauthn.get\",\"origin\":\"x\"}".toUTF8 })
    "clientData"
  expectAssertion "3: the type of a registration" (verify { type := "webauthn.create" })
    (err .wrongType)
  expectAssertion "3: another challenge" (verify { challenge := hex "00" })
    (err .challengeMismatch)
  expectAssertion "3: another origin" (verify { origin := "https://evil.example" })
    (err .originMismatch)
  expectAssertion "3: an origin that only starts like ours"
    (verify { origin := "https://auth.example.org.evil.example" }) (err .originMismatch)
  -- 4. cross-origin frames
  expectAssertion "4: crossOrigin true" (verify { extra := ",\"crossOrigin\":true" })
    (err .crossOrigin)
  expectAssertion "4: a topOrigin" (verify { extra := ",\"topOrigin\":\"https://a.example\"" })
    (err .crossOrigin)
  let framedRp := { testRp with allowedTopOrigins := ["https://a.example"] }
  expectAssertion "4: an allowed topOrigin from a cross-origin frame"
    (verify { extra := ",\"crossOrigin\":true,\"topOrigin\":\"https://a.example\"" }
      (rp := framedRp)) "ok"
  expectAssertion "4: an allowed topOrigin without crossOrigin"
    (verify { extra := ",\"topOrigin\":\"https://a.example\"" } (rp := framedRp))
    (err .crossOrigin)
  expectAssertion "4: an allowed topOrigin with crossOrigin false"
    (verify { extra := ",\"crossOrigin\":false,\"topOrigin\":\"https://a.example\"" }
      (rp := framedRp)) (err .crossOrigin)
  expectAssertion "4: a topOrigin that is not allowed"
    (verify { extra := ",\"crossOrigin\":true,\"topOrigin\":\"https://b.example\"" }
      (rp := framedRp)) (err .crossOrigin)
  expectAssertion "4: crossOrigin without a topOrigin, even with framing allowed"
    (verify { extra := ",\"crossOrigin\":true" } (rp := framedRp)) (err .crossOrigin)
  -- client data the strict reader handles without evaluating anything
  let t₀ ← IO.monoMsNow
  expectAssertion "an exponent of a billion is skipped, not evaluated"
    (verify { extra := ",\"x\":1e1000000000" }) "ok"
  let t₁ ← IO.monoMsNow
  check "and quickly" (t₁ - t₀ < 2000) s!"{t₁ - t₀} ms"
  expectAssertion "3: a repeated challenge"
    (verify { extra := ",\"challenge\":\"AAAA\"" }) "clientData"
  expectAssertion "3: a repeated type" (verify { extra := ",\"type\":\"webauthn.get\"" })
    "clientData"
  expectAssertion "4: crossOrigin that is not a boolean"
    (verify { extra := ",\"crossOrigin\":\"false\"" }) "clientData"
  -- 5. the relying party id
  expectAssertion "5: another relying party id" (verify { rpId := "example.org" })
    (err .rpIdHashMismatch)
  -- 6. presence and verification
  expectAssertion "6: user not present" (verify { flags := 0x04 }) (err .userNotPresent)
  expectAssertion "6: user not verified" (verify { flags := 0x01 }) (err .userNotVerified)
  -- 7. backup eligibility
  expectAssertion "7: became backup-eligible" (verify { flags := 0x0d })
    (err .backupEligibilityChanged)
  expectAssertion "7: stopped being backup-eligible"
    (verify {} (storedFor .es256 p256Secret (backupEligible := true)))
    (err .backupEligibilityChanged)
  expectAssertion "backed up without being backup-eligible" (verify { flags := 0x15 })
    "authenticatorData"
  -- 8. the signature
  let good := Gen.sign {} .es256 p256Secret
  expectAssertion "8: signature over other authenticator data"
    (verifyAssertion testRp testChallenge none es
      { good with authenticatorData := (Gen.authData { signCount := 8 }) }) (err .badSignature)
  expectAssertion "8: signature over other client data"
    (verifyAssertion testRp testChallenge none es
      { good with clientDataJSON := Gen.clientData { extra := ",\"x\":1" } }) (err .badSignature)
  expectAssertion "8: signature by another key"
    (verify {} (secret := hex "0000000000000000000000000000000000000000000000000000000000000001"))
    (err .badSignature)
  expectAssertion "8: an empty signature"
    (verifyAssertion testRp testChallenge none es { good with signature := .empty })
    (err .badSignature)
  expectAssertion "8: EdDSA signature over other client data"
    (verifyAssertion testRp testChallenge none ed
      { Gen.sign {} .edDsa ed25519Secret with clientDataJSON := Gen.clientData { extra := " " } })
    (err .badSignature)
  expectAssertion "8: an ES256 signature under an EdDSA key"
    (verifyAssertion testRp testChallenge none ed good) (err .badSignature)
  -- 9. the counter
  expectAssertion "9: the counter did not move" (verify { signCount := 6 }) (err .possiblyCloned)
  expectAssertion "9: the counter went back" (verify { signCount := 2 }) (err .possiblyCloned)
  expectAssertion "9: the counter went to zero" (verify { signCount := 0 }) (err .possiblyCloned)
  -- malformed authenticator data
  expectAssertion "authenticator data that is too short"
    (verifyAssertion testRp testChallenge none es
      { good with authenticatorData := good.authenticatorData.extract 0 36 }) "authenticatorData"
  expectAssertion "authenticator data with trailing bytes"
    (verifyAssertion testRp testChallenge none es
      { good with authenticatorData := good.authenticatorData ++ hex "00" }) "authenticatorData"

/-! ## Generated registrations -/

/-- The affine coordinates of the public key of a P-256 secret, as 32-byte
strings. -/
def p256Coordinates (secret : ByteArray) : ByteArray × ByteArray :=
  let q := P256.Point.smul (Bytes.toNatBE secret) P256.Point.base
  let zi := P256.F.inv q.Z
  let x := P256.F.mul q.X (P256.F.mul zi zi)
  let y := P256.F.mul q.Y (P256.F.mul zi (P256.F.mul zi zi))
  (Bytes.ofNatBE 32 x, Bytes.ofNatBE 32 y)

/-- An attestation object of format `none` around authenticator data. -/
def noneAttestationOf (authData : ByteArray) : ByteArray :=
  Cbor.encode (.map [(.text "fmt", .text "none"), (.text "attStmt", .map []),
    (.text "authData", .bytes authData)])

/-- Authenticator data for `auth.example.org` carrying a credential with a
COSE key, as an authenticator would make it. -/
def attestedAuthData (key : Cbor) (flags : UInt8 := 0x45) (aaguid := ByteArray.mk
    (Array.replicate 16 0)) : ByteArray :=
  Sha256.hash "auth.example.org".toUTF8 ++ ByteArray.mk #[flags]
    ++ Bytes.ofNatBE 4 0 ++ aaguid ++ Bytes.ofNatBE 2 16 ++ testCredentialId ++ Cbor.encode key

/-- An attestation object of format `none` for a COSE key. -/
def noneAttestation (key : Cbor) (flags : UInt8 := 0x45) : ByteArray :=
  noneAttestationOf (attestedAuthData key flags)

/-- Registrations made here, through the COSE encodings of keys whose
compressed form is known. -/
def registrationTests : IO Unit := do
  group "webauthn: generated registrations"
  let cd := Gen.clientData { type := "webauthn.create" }
  let register (key : Cbor) (flags : UInt8 := 0x45) :=
    verifyRegistration testRp testChallenge [.es256, .edDsa]
      { clientDataJSON := cd, attestationObject := noneAttestation key flags, transports := [] }
  let (x, y) := p256Coordinates p256Secret
  match register (coseEs256 x y) with
  | .error e => check "ES256 COSE key: registration" false (reprStr e)
  | .ok c =>
    checkEq "ES256 COSE key: compressed as lean-biscuit would"
      (toHex c.publicKey.bytes) (toHex ((P256.publicKeyOfSecret p256Secret).getD .empty))
    checkEq "ES256 COSE key: the credential id" (toHex c.id) (toHex testCredentialId)
    -- and the credential then signs in
    let stored := { c.toStored testUserHandle with signCount := 6 }
    expectAssertion "ES256 COSE key: authentication"
      (verifyAssertion testRp testChallenge none stored (Gen.sign {} .es256 p256Secret)) "ok"
  let edKey := (Ed25519.publicKeyOfSecret ed25519Secret).getD .empty
  match register (coseEdDsa edKey) with
  | .error e => check "EdDSA COSE key: registration" false (reprStr e)
  | .ok c =>
    checkEq "EdDSA COSE key: kept as is" (toHex c.publicKey.bytes) (toHex edKey)
  let yPlusOne := Bytes.ofNatBE 32 (Bytes.toNatBE y + 1)
  checkEq "a point off the curve" (regOutcome (register (coseEs256 x yPlusOne)))
    "authenticatorData"
  checkEq "a short coordinate" (regOutcome (register (coseEs256 (x.extract 0 31) y)))
    "authenticatorData"
  checkEq "ES256 with the Ed25519 curve"
    (regOutcome (register (.map [(.unsigned 1, .unsigned 2), (.unsigned 3, .negative 6),
      (.negative 0, .unsigned 6), (.negative 1, .bytes x), (.negative 2, .bytes y)])))
    "authenticatorData"
  checkEq "a repeated label"
    (regOutcome (register (.map [(.unsigned 1, .unsigned 2), (.unsigned 3, .negative 6),
      (.negative 0, .unsigned 1), (.negative 1, .bytes x), (.negative 2, .bytes y),
      (.unsigned 3, .negative 7)])))
    "authenticatorData"
  checkEq "AT flag clear but credential data present"
    (regOutcome (register (coseEs256 x y) 0x05)) "authenticatorData"
  let bare := Sha256.hash "auth.example.org".toUTF8 ++ ByteArray.mk #[0x05] ++ Bytes.ofNatBE 4 0
  checkEq "no attested credential: 37 bytes of authenticator data"
    (regOutcome (verifyRegistration testRp testChallenge [.es256, .edDsa]
      { clientDataJSON := cd, attestationObject := noneAttestationOf bare, transports := [] }))
    (reprStr RegistrationError.noAttestedCredential)
  checkEq "user not present" (regOutcome (register (coseEs256 x y) 0x44))
    (reprStr RegistrationError.userNotPresent)
  checkEq "user not verified" (regOutcome (register (coseEs256 x y) 0x41))
    (reprStr RegistrationError.userNotVerified)

/-! ## Bounds on hostile input -/

/-- CBOR and client data are read before any signature is checked, so their
cost is the attacker's to choose; both must stay small and linear. -/
def boundsTests : IO Unit := do
  group "webauthn: bounds"
  -- an array announcing 65000 items, each an empty byte string: over the cap
  let big := hex "99fde8" ++ ByteArray.mk (Array.replicate 65000 0x40)
  let t₀ ← IO.monoMsNow
  check "CBOR over 16 KiB is refused" (Cbor.decode big).isNone
  check "CBOR over 16 KiB is refused as a prefix too" (Cbor.decodePrefix big).isNone
  let t₁ ← IO.monoMsNow
  check "and at once" (t₁ - t₀ < 100) s!"{t₁ - t₀} ms"
  -- the same shape at exactly 16 KiB, the worst the cap lets through
  let worst := hex "993ffd" ++ ByteArray.mk (Array.replicate 16381 0x40)
  checkEq "the worst case is 16 KiB" worst.size Cbor.maxSize
  let t₂ ← IO.monoMsNow
  let decoded := Cbor.decode worst
  let t₃ ← IO.monoMsNow
  check "the worst case decodes" (match decoded with
    | some (.array items) => items.length == 16381
    | _ => false)
  check "and quickly" (t₃ - t₂ < 500) s!"{t₃ - t₂} ms"
  -- the same through an assertion whose authenticator data claims a credential
  let ad := Sha256.hash "auth.example.org".toUTF8 ++ hex "45" ++ Bytes.ofNatBE 4 7
    ++ ByteArray.mk (Array.replicate 16 0) ++ Bytes.ofNatBE 2 16 ++ testCredentialId
    ++ hex "993ffd" ++ ByteArray.mk (Array.replicate 16300 0x40)
  let r := { Gen.sign {} .es256 p256Secret with authenticatorData := ad }
  let t₄ ← IO.monoMsNow
  expectAssertion "a large CBOR item in the authenticator data is refused"
    (verifyAssertion testRp testChallenge none (storedFor .es256 p256Secret) r)
    "authenticatorData"
  let t₅ ← IO.monoMsNow
  check "before the signature, and quickly" (t₅ - t₄ < 500) s!"{t₅ - t₄} ms"

/-- The strict JSON reader of client data. -/
def jsonTests : IO Unit := do
  group "webauthn: client data JSON"
  let text := "{\"a\":\"q\\\"b\\\\s\\/\\b\\f\\n\\r\\t\\u00e9\\ud83d\\ude00\",\"b\":true," ++
    "\"c\":false,\"d\":null,\"e\":-1.5e+3,\"f\":[1,{\"g\":[]}],\"h\":{}, \"i\" : 0 }"
  match Json.readObject text.toUTF8 with
  | .error e => check "a full object reads" false e
  | .ok members =>
    checkEq "keys" (members.map (·.1)) ["a", "b", "c", "d", "e", "f", "h", "i"]
    check "escapes" (members.head? == some ("a", .str "q\"b\\s/\x08\x0c\n\r\té😀"))
    let get (k : String) := List.lookup k members
    check "booleans" ((get "b" == some (.bool true)) && (get "c" == some (.bool false)))
    check "the rest is other" ((["d", "e", "f", "h", "i"].map get).all
      (· == some Json.Value.other))
  let refused : List (String × String) := [
    ("", "empty"), ("[]", "not an object"), ("{", "unterminated"), ("{\"a\":1,}", "trailing comma"),
    ("{\"a\":01}", "leading zero"), ("{\"a\":1.}", "no fraction digits"),
    ("{\"a\":-}", "bare minus"),
    ("{\"a\":1e}", "no exponent digits"), ("{\"a\":+1}", "plus sign"), ("{\"a\":.5}", "no integer"),
    ("{\"a\":1}x", "trailing characters"), ("{\"a\":\"\\ud800\"}", "lone high surrogate"),
    ("{\"a\":\"\\udc00\"}", "lone low surrogate"), ("{\"a\":\"\\x\"}", "unknown escape"),
    ("{\"a\":\"\x01\"}", "raw control character"), ("{\"a\":tru}", "bad literal"),
    ("{\"a\":1,\"a\":2}", "repeated key"), ("{\"a\":{\"b\":1,\"b\":2}}", "repeated nested key"),
    ("{a:1}", "unquoted key"), ("{\"a\" 1}", "no colon"),
    ("{\"a\":[1,]}", "trailing comma in array"),
    ("{\"a\":" ++ String.ofList (List.replicate 9 '[') ++
      String.ofList (List.replicate 9 ']') ++ "}",
      "nesting nine deep")]
  for (t, why) in refused do
    check s!"refuse: {why}" ((Json.readObject t.toUTF8) matches Except.error _)
  check "nesting eight deep is read"
    ((Json.readObject ("{\"a\":" ++ String.ofList (List.replicate 8 '[') ++
      String.ofList (List.replicate 8 ']') ++ "}").toUTF8) matches Except.ok _)
  let long := "{\"a\":\"" ++ String.ofList (List.replicate 4096 'x') ++ "\"}"
  check "refuse more than 4 KiB" ((Json.readObject long.toUTF8) matches Except.error _)
  let t₀ ← IO.monoMsNow
  let r := ClientData.parse
    "{\"type\":\"webauthn.get\",\"challenge\":\"\",\"origin\":\"a\",\"x\":1e1000000000}".toUTF8
  let t₁ ← IO.monoMsNow
  check "a huge exponent is skipped" (r matches Except.ok _)
  check "without evaluating it" (t₁ - t₀ < 100) s!"{t₁ - t₀} ms"
  check "client data with a repeated key is refused"
    ((ClientData.parse
      "{\"type\":\"webauthn.get\",\"challenge\":\"\",\"origin\":\"a\",\"origin\":\"b\"}".toUTF8)
      matches Except.error _)

/-! ## Attestation certificates -/

/-- A DER length. -/
def derLength (n : Nat) : ByteArray :=
  if n < 0x80 then ByteArray.mk #[n.toUInt8]
  else
    let body := Bytes.ofNatBE (if n < 256 then 1 else 2) n
    ByteArray.mk #[(0x80 + body.size).toUInt8] ++ body

/-- A DER tag-length-value. -/
def tlv (tag : UInt8) (contents : ByteArray) : ByteArray :=
  ByteArray.mk #[tag] ++ derLength contents.size ++ contents

/-- A DER `SEQUENCE`. -/
def derSeq (items : List ByteArray) : ByteArray := tlv 0x30 (Bytes.concat items)

/-- The `ecdsa-with-SHA256` algorithm identifier. -/
def ecdsaSha256 : ByteArray := derSeq [tlv 0x06 (hex "2a8648ce3d040302")]

/-- A `Name` from attributes, one per relative distinguished name. -/
def derName (attrs : List (ByteArray × UInt8 × String)) : ByteArray :=
  derSeq (attrs.map fun (oid, tag, value) =>
    tlv 0x31 (derSeq [tlv 0x06 oid, tlv tag value.toUTF8]))

/-- The subject a `packed` attestation certificate must have. -/
def goodSubject : List (ByteArray × UInt8 × String) :=
  [(Der.oidCountry, 0x13, "AA"), (Der.oidOrganization, 0x0c, "pyle tests"),
    (Der.oidOrganizationalUnit, 0x0c, "Authenticator Attestation"),
    (Der.oidCommonName, 0x0c, "pyle test authenticator")]

/-- The `SubjectPublicKeyInfo` of the P-256 test key. -/
def p256Spki : ByteArray :=
  let (x, y) := p256Coordinates p256Secret
  derSeq [derSeq [tlv 0x06 Der.oidEcPublicKey, tlv 0x06 Der.oidPrime256v1],
    tlv 0x03 (hex "0004" ++ x ++ y)]

/-- The `SubjectPublicKeyInfo` of the Ed25519 test key. -/
def ed25519Spki : ByteArray :=
  derSeq [derSeq [tlv 0x06 (hex "2b6570")],
    tlv 0x03 (hex "00" ++ (Ed25519.publicKeyOfSecret ed25519Secret).getD .empty)]

/-- An extension; `critical` is the raw BOOLEAN contents, if written. -/
def derExtension (oid : ByteArray) (critical : Option ByteArray) (value : ByteArray) :
    ByteArray :=
  derSeq ([tlv 0x06 oid] ++ (critical.map (tlv 0x01 ·)).toList ++ [tlv 0x04 value])

/-- Basic constraints with the given raw `cA` BOOLEAN, or none. -/
def basicConstraints (ca : Option ByteArray) : ByteArray :=
  derExtension Der.oidBasicConstraints (some (hex "ff")) (derSeq (ca.map (tlv 0x01 ·)).toList)

/-- The FIDO AAGUID extension. -/
def aaguidExtension (aaguid : ByteArray) (critical : Bool := false) : ByteArray :=
  derExtension Der.oidFidoAaguid (if critical then some (hex "ff") else none) (tlv 0x04 aaguid)

/-- The AAGUID of the hand-built certificates. -/
def testAaguid : ByteArray := hex "f00df00df00df00df00df00df00df00d"

/-- What a hand-built certificate is made of. -/
structure CertSpec where
  /-- Whether to write the version (v3). -/
  version : Bool := true
  /-- The subject. -/
  subject : List (ByteArray × UInt8 × String) := goodSubject
  /-- The key. -/
  spki : ByteArray := p256Spki
  /-- The extensions. -/
  extensions : List ByteArray := [basicConstraints none, aaguidExtension testAaguid]

/-- Build a certificate.  Its own signature is zeros: attestation leaves that
to chain validation. -/
def CertSpec.build (c : CertSpec) : ByteArray :=
  let tbs := derSeq ((if c.version then [tlv 0xa0 (tlv 0x02 (hex "02"))] else []) ++
    [tlv 0x02 (hex "01"), ecdsaSha256, derName [(Der.oidCommonName, 0x0c, "pyle test CA")],
      derSeq [tlv 0x17 "240101000000Z".toUTF8, tlv 0x17 "340101000000Z".toUTF8],
      derName c.subject, c.spki] ++
    (if c.extensions.isEmpty then [] else [tlv 0xa3 (derSeq c.extensions)]))
  derSeq [tbs, ecdsaSha256, tlv 0x03 (hex "00" ++ ByteArray.mk (Array.replicate 8 0))]

/-- The reason a certificate was refused, or `""`. -/
def certReason (c : CertSpec) : String :=
  match checkAttestationCertificate c.build testAaguid with
  | .ok _ => ""
  | .error e => e

/-- Hand-built `packed` attestation certificates, one broken for each
requirement of WebAuthn §8.2.1, and statements around them. -/
def attestationCertTests : IO Unit := do
  group "webauthn: packed attestation certificates"
  let compressed := (P256.publicKeyOfSecret p256Secret).getD .empty
  let keyOf (c : CertSpec) : String :=
    match checkAttestationCertificate c.build testAaguid with
    | .ok k => toHex k
    | .error e => e
  checkEq "a good leaf yields its compressed key" (keyOf {}) (toHex compressed)
  checkEq "a leaf without the AAGUID extension is fine" (keyOf { extensions := [] })
    (toHex compressed)
  let without (oid : ByteArray) := goodSubject.filter (·.1 != oid)
  let cases : List (String × CertSpec × String) := [
    ("version 1", { version := false }, "not version 3"),
    ("no OU", { subject := without Der.oidOrganizationalUnit }, "OU"),
    ("another OU", { subject := (without Der.oidOrganizationalUnit) ++
      [(Der.oidOrganizationalUnit, 0x0c, "Something Else")] }, "OU"),
    ("no C", { subject := without Der.oidCountry }, "has no C"),
    ("no O", { subject := without Der.oidOrganization }, "has no O"),
    ("no CN", { subject := without Der.oidCommonName }, "has no CN"),
    ("CA:TRUE", { extensions := [basicConstraints (some (hex "ff"))] }, "is a CA"),
    ("a non-DER BOOLEAN in basic constraints",
      { extensions := [basicConstraints (some (hex "01"))] },
      "basic constraints do not parse"),
    ("a critical AAGUID extension", { extensions := [aaguidExtension testAaguid true] },
      "malformed"),
    ("another AAGUID", { extensions := [aaguidExtension (hex "00112233445566778899aabbccddeeff")] },
      "differs from authenticator data"),
    ("a short AAGUID", { extensions := [aaguidExtension (hex "0011")] }, "malformed"),
    ("an Ed25519 key", { spki := ed25519Spki }, "not a P-256 key")]
  for (why, spec, reason) in cases do
    let got := certReason spec
    check s!"refuse a leaf with {why}" (mentions got reason) s!"reason: {got}"
  -- whole statements around a good leaf
  let authData := attestedAuthData (coseEs256 (p256Coordinates p256Secret).1
    (p256Coordinates p256Secret).2) (aaguid := testAaguid)
  let clientHash := Sha256.hash "client data".toUTF8
  let sig := (P256.sign p256Secret (authData ++ clientHash)).getD .empty
  let cred : AttestedCredential :=
    { aaguid := testAaguid, credentialId := testCredentialId,
      publicKey := { algorithm := .es256, bytes := compressed } }
  let leaf := ({} : CertSpec).build
  let statement (alg : Cbor) (extra : List (Cbor × Cbor) := []) (sig := sig) :=
    Cbor.map ([(.text "alg", alg), (.text "sig", .bytes sig),
      (.text "x5c", .array [.bytes leaf])] ++ extra)
  let reason (r : Except String AttestationKind) : String :=
    match r with
    | .ok k => s!"ok: {kindName k}"
    | .error e => e
  checkEq "full attestation under a good leaf"
    (reason (verifyAttestation "packed" (statement (.negative 6)) authData clientHash cred))
    "ok: packed full (1 certificates)"
  check "alg -8 with x5c is refused"
    (mentions (reason (verifyAttestation "packed" (statement (.negative 7)) authData clientHash
      cred)) "only ES256")
  check "ecdaaKeyId is refused"
    (mentions (reason (verifyAttestation "packed"
      (statement (.negative 6) [(.text "ecdaaKeyId", .bytes (hex "00"))]) authData clientHash
      cred)) "ECDAA")
  check "a signature over other data is refused"
    (mentions (reason (verifyAttestation "packed" (statement (.negative 6)) authData
      (Sha256.hash "other".toUTF8) cred)) "does not verify under the leaf")
  check "the AAGUID must match the authenticator data's"
    (mentions (reason (verifyAttestation "packed" (statement (.negative 6)) authData clientHash
      { cred with aaguid := hex "00000000000000000000000000000000" })) "differs")
  check "an empty x5c is refused"
    (mentions (reason (verifyAttestation "packed"
      (Cbor.map [(.text "alg", .negative 6), (.text "sig", .bytes sig), (.text "x5c", .array [])])
      authData clientHash cred)) "x5c is empty")

/-- All the WebAuthn tests. -/
def webAuthnTests : IO Unit := do
  base64UrlTests
  cborTests
  derTests
  vectorTests
  boundsTests
  jsonTests
  attestationCertTests
  generatedTests
  registrationTests

end PyleTests