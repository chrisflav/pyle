import Lean.Data.Json
import LeanBiscuit.Crypto.Ed25519
import LeanBiscuit.Crypto.P256
import Pyle.Crypto.Keys
import Pyle.Oidc.Jwk

/-!
# JSON Web Tokens

ID tokens are JWS compact serialisations (RFC 7515 §7.1) because every OpenID
Connect client library expects them.  Signing goes through
`Pyle.Crypto.SigningKey`, so the private key stays behind the FFI boundary.

The one conversion of substance is for ES256: OpenSSL, WebAuthn and
`lean-biscuit` write ECDSA signatures as DER `SEQUENCE { r, s }`, while JWS
writes them as the fixed 64 bytes `r ‖ s` (RFC 7518 §3.4).

The verifier exists for the tests, and for any later code that must check a
token pyle issued.  It takes the algorithm from the caller, not from the
token, and refuses a token whose header names a different one; `none` and the
HMAC algorithms are never accepted.  ES256 and EdDSA are verified in Lean by
`lean-biscuit`, RS256 by OpenSSL, since pyle has no RSA in Lean.
-/

namespace Pyle
namespace Oidc
namespace Jwt

open Lean (Json)
open Pyle.Crypto

/-- An ECDSA signature in DER form as the 64-byte `r ‖ s` of JWS. -/
def derToRaw (der : ByteArray) : Except String ByteArray := do
  let some (r, s) := LeanBiscuit.P256.Der.parseSignature der
    | throw "not a DER ECDSA signature"
  if r ≥ 2 ^ 256 || s ≥ 2 ^ 256 then throw "ECDSA signature component out of range"
  pure (LeanBiscuit.Bytes.ofNatBE 32 r ++ LeanBiscuit.Bytes.ofNatBE 32 s)

/-- A 64-byte JWS ECDSA signature `r ‖ s` in DER form. -/
def rawToDer (raw : ByteArray) : Except String ByteArray :=
  if raw.size != 64 then .error "an ES256 signature is 64 bytes"
  else .ok (LeanBiscuit.P256.Der.encodeSignature (LeanBiscuit.Bytes.toNatBE (raw.extract 0 32))
    (LeanBiscuit.Bytes.toNatBE (raw.extract 32 64)))

/-- The JWS signing input: the encoded header and payload joined by a dot. -/
def signingInput (header payload : ByteArray) : String :=
  Jose.b64urlEncode header ++ "." ++ Jose.b64urlEncode payload

/-- A JWS compact serialisation of exactly these header and payload bytes.
`sign` is the usual entry point; this one exists so that published examples,
whose bytes are not what `Json.compress` would write, can be reproduced. -/
def signBytes (k : SigningKey) (header payload : ByteArray) : IO String := do
  let input := signingInput header payload
  let signature ← k.sign input.toUTF8
  let signature ← match k.algorithm with
    | .es256 => IO.ofExcept (derToRaw signature)
    | .edDsa | .rs256 => pure signature
  pure (input ++ "." ++ Jose.b64urlEncode signature)

/-- The protected header pyle writes: the algorithm, the key's `kid` and
`typ: JWT`. -/
def header (algorithm : SigningAlgorithm) (kid : String) : Json :=
  Json.mkObj [("alg", algorithm.joseName), ("kid", kid), ("typ", "JWT")]

/-- Sign a set of claims as a JWT with the given key, naming it by `kid`. -/
def sign (k : SigningKey) (kid : String) (claims : Json) : IO String :=
  signBytes k (header k.algorithm kid).compress.toUTF8 claims.compress.toUTF8

/-- Whether `signature` is valid on `input` under a public key, as
`SigningKey.publicKey` writes it, for the algorithm. -/
def verifySignature (algorithm : SigningAlgorithm) (publicKey input signature : ByteArray) :
    Except String Unit :=
  match algorithm with
  | .es256 => do
    let der ← rawToDer signature
    match LeanBiscuit.P256.verify publicKey input der with
    | .ok () => pure ()
    | .error _ => throw "bad ES256 signature"
  | .edDsa =>
    match LeanBiscuit.Ed25519.verify publicKey input signature with
    | .ok () => pure ()
    | .error _ => throw "bad EdDSA signature"
  | .rs256 =>
    if Crypto.Ffi.rs256Verify publicKey input signature then pure ()
    else throw "bad RS256 signature"

/-- Verify a JWS compact serialisation under a public key for `algorithm`.  The
header must be a JSON object whose `alg` is that algorithm and which has no
`crit` member; the result is the protected header and the payload bytes. -/
def verifyBytes (algorithm : SigningAlgorithm) (publicKey : ByteArray) (token : String) :
    Except String (Json × ByteArray) := do
  let [h, p, s] := token.splitOn "." | throw "a JWS has three parts"
  let some headerBytes := Jose.b64urlDecode? h | throw "bad header encoding"
  let some payload := Jose.b64urlDecode? p | throw "bad payload encoding"
  let some signature := Jose.b64urlDecode? s | throw "bad signature encoding"
  let some headerText := String.fromUTF8? headerBytes | throw "header is not UTF-8"
  let header ← Json.parse headerText
  let .ok alg := header.getObjValAs? String "alg" | throw "header has no alg"
  if alg != algorithm.joseName then throw s!"unexpected alg {alg}"
  if (header.getObjVal? "crit").isOk then throw "critical header parameters are not supported"
  verifySignature algorithm publicKey (h ++ "." ++ p).toUTF8 signature
  pure (header, payload)

/-- Verify a JWT as `verifyBytes` does and parse its claims. -/
def verify (algorithm : SigningAlgorithm) (publicKey : ByteArray) (token : String) :
    Except String Json := do
  let (_, payload) ← verifyBytes algorithm publicKey token
  let some text := String.fromUTF8? payload | throw "payload is not UTF-8"
  Json.parse text

end Jwt
end Oidc
end Pyle