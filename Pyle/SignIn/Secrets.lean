import Pyle.Crypto.Aead
import Pyle.Crypto.Hkdf
import Pyle.Store.Users
import Pyle.Factor.Totp

/-!
# Keys derived from the root key

The root key (DESIGN §6.3) is never used directly.  Each purpose gets its own
32-byte key, derived with HKDF-SHA256 under a fixed `info` string, so that
the key sealing TOTP secrets is not the key that MACs recovery codes and a
weakness in one use says nothing about another:

| `info` | used for |
| --- | --- |
| `pyle totp v1` | sealing TOTP secrets, with the user and the app as associated data |
| `pyle recovery-code v1` | the HMAC under which recovery codes are stored |
| `pyle invitation-handle v1` | the WebAuthn user handle of an invited account, for a registration begun before migration 9 |
| `pyle decoy-credential v1` | the padding credential ids of a named sign-in |

Two more keys come from the root key elsewhere: `Keys.sealingKey`, under
`pyle signing-key v1`, seals the signing keys, and `ForwardAuth.macKey`,
under `pyle forward-auth v1`, MACs the protected hosts' cookies.  The root
key's fingerprint (`Store.rootKeyId`) has an `info` of its own too.

When the root key is replaced (`RootKey.rotate`), every TOTP secret is
re-sealed under the new one, in the transaction that records it.  Recovery
codes cannot be: only their HMACs are stored, and whoever has the old key and
a copy of the database can search all 2⁵⁰ codes against them, so a rotation
deletes them and the account page asks for new ones.  A pending enrolment
sealed under the old key no longer opens and has to be begun again, and the
padding ids of a name change.

The associated data of a sealed TOTP secret names its row: `totp `, the
user's row id and the app's row id, in decimal (`appAd`).  A sealed secret
copied into another user's row, or into another of the same user's apps, no
longer opens.  The one secret an account had before it could have several
was sealed with the user's row id alone (`userAd`); migration 6 made it an
app with the `legacy_ad` flag set, and `openTotpApp` accepts that associated
data only for a row with the flag — which nothing but that migration sets —
and only for its own user.  The first code such an app accepts re-seals it
with `appAd` and clears the flag.

A secret in the middle of being enrolled, handed to the browser and back, is
sealed with `pending ` in front of the user id and, inside, the time it was
issued and the name the app is to have, so it can neither be stored as
another user's nor kept for later.
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

/-- The associated data a user's single TOTP secret was sealed with before
migration 6: the user's row id in decimal. -/
def userAd (user : Store.UserId) : ByteArray := (toString user.val).toUTF8

/-- The associated data of an authenticator app's sealed secret: `totp `,
the user's row id and the app's, in decimal. -/
def appAd (user : Store.UserId) (app : Int) : ByteArray :=
  s!"totp {user.val} {app}".toUTF8

/-- Seal a TOTP secret for the row of app `app` of `user`. -/
def sealTotpApp (rootKey : ByteArray) (user : Store.UserId) (app : Int) (secret : ByteArray) :
    IO ByteArray :=
  Crypto.«seal» (totpKey rootKey) (appAd user app) secret

/-- Open the sealed secret of app `app` of `user`.  It opens with the
associated data of its own row, or — for a row migration 6 made of the
account's one secret, `legacy` — with the user id alone. -/
def openTotpApp (rootKey : ByteArray) (user : Store.UserId) (app : Int)
    (sealedSecret : ByteArray) (legacy : Bool := false) : Except String ByteArray :=
  match Crypto.«open» (totpKey rootKey) (appAd user app) sealedSecret with
  | .ok secret => .ok secret
  | .error e =>
    if legacy then Crypto.«open» (totpKey rootKey) (userAd user) sealedSecret
    else .error e

/-- The associated data of a secret being enrolled. -/
def pendingAd (user : Store.UserId) : ByteArray := ("pending " ++ toString user.val).toUTF8

/-- A number as 8 bytes, big-endian. -/
def be64 (n : Nat) : ByteArray :=
  ⟨(List.range 8).reverse.toArray.map fun i => UInt8.ofNat (n >>> (8 * i))⟩

/-- A big-endian number back. -/
def ofBe64 (b : ByteArray) : Nat := b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- A secret being enrolled, as `openPending` gives it back. -/
structure Pending where
  /-- The new secret. -/
  secret : ByteArray
  /-- When it was issued. -/
  issued : Nat
  /-- The name the app was to have when it was issued; empty if none. -/
  name : String

/-- Seal a TOTP secret being enrolled, with the time it was issued and the
name the app is to have, for the browser to hand back with its first code.
The plaintext is the time in eight bytes, the secret, then the name. -/
def sealPending (rootKey : ByteArray) (user : Store.UserId) (secret : ByteArray) (now : Nat)
    (name : String := "") : IO ByteArray :=
  Crypto.«seal» (totpKey rootKey) (pendingAd user) (be64 now ++ secret ++ name.toUTF8)

/-- Open a secret being enrolled, if it was sealed for this user by
`sealPending`. -/
def openPending (rootKey : ByteArray) (user : Store.UserId) (sealedSecret : ByteArray) :
    Option Pending := do
  let plain ← (Crypto.«open» (totpKey rootKey) (pendingAd user) sealedSecret).toOption
  let n := Factor.Totp.secretLength
  guard (plain.size ≥ 8 + n)
  let name ← String.fromUTF8? (plain.extract (8 + n) plain.size)
  return { secret := plain.extract 8 (8 + n), issued := ofBe64 (plain.extract 0 8), name }

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