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
| `pyle decoy-credential v1` | the padding credential ids of a named sign-in |

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

/-- The lengths a padding credential id may have.  Authenticators choose
their own ids, and these are the lengths common ones use (16 bytes for many
security keys, 32 and 64 for platform passkeys), so a padding id does not
stand out by its length. -/
def paddingIdLengths : List Nat := [16, 32, 48, 64]

/-- The `i`-th padding credential id for a name: an HMAC of the name and `i`,
of a length chosen by the HMAC too.  The same for the same name and `i` every
time, so asking twice does not tell a padded answer from a real one by a
change in it. -/
def paddingCredentialId (rootKey : ByteArray) (name : String) (i : Nat) : ByteArray :=
  let k := decoyKey rootKey
  let block (j : Nat) := LeanBiscuit.Hmac.sha256 k (s!"{i}:{j}:".toUTF8 ++ name.toUTF8)
  let first := block 0
  let len := paddingIdLengths.getD ((first.get! 0).toNat % paddingIdLengths.length) 16
  ((List.range 3).foldl (fun acc j => acc ++ block (j + 1)) first).extract 0 len

end Secrets
end SignIn
end Pyle