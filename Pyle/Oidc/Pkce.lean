import Pyle.Oidc.Jwk
import LeanBiscuit.Crypto.Hash

/-!
# Proof Key for Code Exchange

Every authorization request carries a PKCE code challenge, and only the
`S256` method is accepted (RFC 7636, DESIGN.md §5.1): the client sends
`BASE64URL(SHA-256(code_verifier))` with the request and the verifier with the
code, so a code intercepted on its way back to the client is useless without
the verifier.  `plain` is refused, since it protects nothing a network observer
of the authorization request does not already see.
-/

namespace Pyle
namespace Oidc
namespace Pkce

/-- RFC 7636 §4.1's unreserved characters, which a verifier is made of. -/
def isUnreserved (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~'

/-- Whether a code verifier is well formed: 43 to 128 unreserved characters
(RFC 7636 §4.1). -/
def validVerifier (v : String) : Bool :=
  43 ≤ v.length && v.length ≤ 128 && v.all isUnreserved

/-- Whether an `S256` code challenge is well formed: the unpadded base64url of
a SHA-256 digest, 43 characters. -/
def validChallenge (c : String) : Bool :=
  c.length == 43 && (Jose.b64urlDecode? c).any (·.size == 32)

/-- The `S256` challenge of a verifier: `BASE64URL(SHA-256(ASCII(verifier)))`
(RFC 7636 §4.2). -/
def s256 (verifier : String) : String :=
  Jose.b64urlEncode (LeanBiscuit.Sha256.hash verifier.toUTF8)

/-- Whether a verifier answers a challenge (RFC 7636 §4.6): it is well formed
and its `S256` challenge is the one recorded. -/
def verifies (verifier challenge : String) : Bool :=
  validVerifier verifier && s256 verifier == challenge

end Pkce
end Oidc
end Pyle