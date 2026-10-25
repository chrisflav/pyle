import Pyle.Crypto.Ffi

/-!
# X.509 certificate chains

A WebAuthn registration with full attestation carries a certificate chain, and
an operator who wants to admit only certain authenticator models configures the
roots to check it against.  Path validation is OpenSSL's: it is the part of
X.509 that is easy to get subtly wrong and has nothing pyle-specific in it.
Reading the AAGUID extension out of the leaf stays in Lean, with the WebAuthn
code.

A chain is accepted exactly when all of the following hold:

* it has between one and five certificates, leaf first, every one of them
  DER with nothing after it;
* the leaf is not a CA certificate (OpenSSL's `X509_check_ca` is zero);
* OpenSSL builds a path from the leaf through the given intermediates to one
  of the given roots, checking every signature, every validity period at the
  time of verification, the basic constraints and path lengths of the issuers,
  and that each issuer's key usage, if present, allows certificate signing;
* every key and signature on that path meets OpenSSL's security level 2, that
  is at least 112 bits of security, which rules out RSA keys below 2048 bits
  and SHA-1 signatures.

No purpose or extended key usage is required, and revocation is not checked.
-/

namespace Pyle
namespace Crypto

/-- Validate a chain of DER certificates against the given DER trust anchors,
as the module documentation lists, at the current time or, if `at?` is given,
at that Unix time.  On success the
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
after it in any order, against DER trust anchors at the current time, as the
module documentation lists.  On
success the result is the leaf certificate's DER, whose public key and
extensions the caller can then trust as far as it trusts the roots. -/
def verifyChain (chain roots : List ByteArray) : IO (Except String ByteArray) :=
  verifyChainAt chain roots none

end Crypto
end Pyle