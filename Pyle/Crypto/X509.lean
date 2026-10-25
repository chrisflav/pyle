import Pyle.Crypto.Ffi

/-!
# X.509 certificate chains

A WebAuthn registration with full attestation carries a certificate chain, and
an operator who wants to admit only certain authenticator models configures the
roots to check it against.  Path validation — signatures, validity periods,
basic constraints, key usage — is OpenSSL's: it is the part of X.509 that is
easy to get subtly wrong and has nothing pyle-specific in it.  Reading the
AAGUID extension out of the leaf stays in Lean, with the WebAuthn code.
-/

namespace Pyle
namespace Crypto

/-- Validate a chain of DER certificates against the given DER trust anchors,
at the current time or, if `at?` is given, at that Unix time.  On success the
result is the leaf certificate's DER. -/
def verifyChainAt (chain roots : List ByteArray) (at? : Option Nat) :
    IO (Except String ByteArray) := do
  match chain with
  | [] => pure (.error "the certificate chain is empty")
  | leaf :: _ =>
    let (flag, time) := match at? with
      | some t => ((1 : UInt8), UInt64.ofNat t)
      | none => (0, 0)
    pure <| (← Ffi.x509Verify chain.toArray roots.toArray flag time).map fun () => leaf

/-- Validate a chain of DER certificates, leaf first and the intermediates
after it in any order, against DER trust anchors at the current time.  On
success the result is the leaf certificate's DER, whose public key and
extensions the caller can then trust as far as it trusts the roots. -/
def verifyChain (chain roots : List ByteArray) : IO (Except String ByteArray) :=
  verifyChainAt chain roots none

end Crypto
end Pyle