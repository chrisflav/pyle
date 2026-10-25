import Pyle.Crypto.Aead
import Pyle.Crypto.Hkdf
import Pyle.Store.Users

/-!
# Keys derived from the root key

The root key (DESIGN §6.3) is never used directly.  Each purpose gets its own
32-byte key, derived with HKDF-SHA256 under a fixed `info` string, so that
the key sealing TOTP secrets is not the key that MACs recovery codes and a
weakness in one use says nothing about another:

| `info` | used for |
| --- | --- |
| `pyle totp v1` | sealing TOTP secrets, with the user id as associated data |
| `pyle recovery-code v1` | the HMAC under which recovery codes are stored |
| `pyle invitation-handle v1` | the WebAuthn user handle of an invited account |
| `pyle decoy-credential v1` | the credential ids offered for unknown names |

The associated data of a sealed TOTP secret is the user's row id in decimal,
so a sealed secret copied into another user's row no longer opens.  A secret
in the middle of being enrolled, handed to the browser and back, is sealed
with `pending ` in front of the id and the time it was issued inside, so it
can neither be stored as another user's nor kept for later.
-/

namespace Pyle
namespace SignIn
namespace Secrets

/-- The key for one purpose: HKDF-SHA256 of the root key with an empty salt
and `info`, 32 bytes. -/
def derive (rootKey : ByteArray) (info : String) : ByteArray :=
  (Crypto.hkdfSha256 rootKey .empty info.toUTF8 32).getD .empty

/-- The key sealing TOTP secrets. -/
def totpKey (rootKey : ByteArray) : ByteArray := derive rootKey "pyle totp v1"

/-- The key recovery codes are stored under. -/
def recoveryKey (rootKey : ByteArray) : ByteArray := derive rootKey "pyle recovery-code v1"

/-- The key that turns a registration challenge into an invited account's
user handle. -/
def invitationHandleKey (rootKey : ByteArray) : ByteArray :=
  derive rootKey "pyle invitation-handle v1"

/-- The key decoy credential ids are made under. -/
def decoyKey (rootKey : ByteArray) : ByteArray := derive rootKey "pyle decoy-credential v1"

/-- The associated data of a user's sealed TOTP secret: the row id in
decimal. -/
def userAd (user : Store.UserId) : ByteArray := (toString user.val).toUTF8

/-- Seal a TOTP secret for storage in a user's row. -/
def sealTotp (rootKey : ByteArray) (user : Store.UserId) (secret : ByteArray) :
    IO ByteArray :=
  Crypto.«seal» (totpKey rootKey) (userAd user) secret

/-- Open a user's stored TOTP secret. -/
def openTotp (rootKey : ByteArray) (user : Store.UserId) (sealedSecret : ByteArray) :
    Except String ByteArray :=
  Crypto.«open» (totpKey rootKey) (userAd user) sealedSecret

/-- The associated data of a secret being enrolled. -/
def pendingAd (user : Store.UserId) : ByteArray := ("pending " ++ toString user.val).toUTF8

/-- A number as 8 bytes, big-endian. -/
def be64 (n : Nat) : ByteArray :=
  ⟨(List.range 8).reverse.toArray.map fun i => UInt8.ofNat (n >>> (8 * i))⟩

/-- A big-endian number back. -/
def ofBe64 (b : ByteArray) : Nat := b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- Seal a TOTP secret being enrolled, with the time it was issued, for the
browser to hand back with its first code. -/
def sealPending (rootKey : ByteArray) (user : Store.UserId) (secret : ByteArray) (now : Nat) :
    IO ByteArray :=
  Crypto.«seal» (totpKey rootKey) (pendingAd user) (be64 now ++ secret)

/-- Open a secret being enrolled: the secret and when it was issued, if it
was sealed for this user by `sealPending`. -/
def openPending (rootKey : ByteArray) (user : Store.UserId) (sealedSecret : ByteArray) :
    Option (ByteArray × Nat) := do
  let plain ← (Crypto.«open» (totpKey rootKey) (pendingAd user) sealedSecret).toOption
  guard (plain.size > 8)
  return (plain.extract 8 plain.size, ofBe64 (plain.extract 0 8))

/-- The user handle of an account created through an invitation: the HMAC of
the registration challenge.  The account does not exist while the browser
creates the credential, and the handle must be known then; deriving it from
the challenge means nothing has to be remembered between the two requests. -/
def invitationHandle (rootKey challenge : ByteArray) : ByteArray :=
  LeanBiscuit.Hmac.sha256 (invitationHandleKey rootKey) challenge

/-- The credential id offered for a name that has no credentials: the same
for the same name every time, so that asking twice does not tell an unknown
name from a known one by a change in the answer. -/
def decoyCredentialId (rootKey : ByteArray) (name : String) : ByteArray :=
  (LeanBiscuit.Hmac.sha256 (decoyKey rootKey) name.toUTF8).extract 0 16

end Secrets
end SignIn
end Pyle