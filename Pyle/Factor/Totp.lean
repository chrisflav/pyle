import Pyle.Crypto.Ffi
import Pyle.Crypto.HmacSha1
import Pyle.Factor.Base32

/-!
# TOTP

Time-based one-time passwords (RFC 6238) with the parameters every
authenticator app supports: HMAC-SHA1, 30-second steps, six digits.  A code is
accepted for the current step and one step either side, to allow for clocks
that disagree and for the time it takes to type.

What RFC 6238 §5.2 recommends and most implementations forget is that a code
must be good at most once.  The caller stores the step of the last accepted
code, and `verify` only ever accepts a strictly later step; that is the theorem
`verify_increasing`, DESIGN.md §9 property 5 for a single user.  An attacker
who watches a code being typed therefore cannot replay it, not even within the
same 30 seconds.  With several apps the rule holds for each app on its own
(`verifyAny`).

The comparison of the submitted code with each expected one goes through the
constant-time primitive, since the expected code is derived from the secret
(DESIGN.md §6.2).
-/

namespace Pyle
namespace Factor
namespace Totp

/-- The length of a time step, in seconds. -/
def period : Nat := 30

/-- The number of digits in a code. -/
def digits : Nat := 6

/-- The length of a freshly generated secret, in bytes: 160 bits, as RFC 4226
§4 recommends. -/
def secretLength : Nat := 20

/-- The eight-byte big-endian counter HOTP feeds to HMAC. -/
def counterBytes (counter : Nat) : ByteArray :=
  ⟨(List.range 8).reverse.map (fun i => UInt8.ofNat (counter / 256 ^ i % 256)) |>.toArray⟩

/-- `n` in decimal, left-padded with zeros to `width` digits. -/
def zeroPad (width n : Nat) : String :=
  let s := toString n
  "".pushn '0' (width - s.length) ++ s

/-- HOTP (RFC 4226 §5.3): HMAC-SHA1 of the counter, dynamically truncated to
31 bits, reduced to the given number of decimal digits. -/
def hotp (secret : ByteArray) (counter : Nat) (digits : Nat) : String :=
  let mac := Crypto.hmacSha1 secret (counterBytes counter)
  let byte (i : Nat) : Nat := (mac.data.getD i 0).toNat
  let offset := byte 19 % 16
  let binary := (byte offset % 128) * 2 ^ 24 + byte (offset + 1) * 2 ^ 16 +
    byte (offset + 2) * 2 ^ 8 + byte (offset + 3)
  zeroPad digits (binary % 10 ^ digits)

/-- The time step a Unix time falls in. -/
def stepOf (unixTime : Nat) : Nat := unixTime / period

/-- The six-digit code for a time step. -/
def code (secret : ByteArray) (step : Nat) : String := hotp secret step digits

/-- Whether a step is later than the last one accepted, if any. -/
def fresh (lastStep : Option Nat) (step : Nat) : Bool :=
  match lastStep with
  | none => true
  | some last => decide (last < step)

/-- Check a submitted code at a Unix time.  The candidates are the current step
and its two neighbours, earliest first; a candidate counts only if it is later
than `lastStep`, the step of the last code this user had accepted.  The result
is the step the code was accepted for, which the caller stores as the new
`lastStep`, or `none`. -/
def verify (secret : ByteArray) (unixTime : Nat) (code : String) (lastStep : Option Nat) :
    Option Nat :=
  let now := stepOf unixTime
  let submitted := code.toUTF8
  [now - 1, now, now + 1].find? fun step =>
    fresh lastStep step && Crypto.ctEqual submitted (Totp.code secret step).toUTF8

/-- A code is never accepted for the step of the last accepted code or an
earlier one: accepted steps strictly increase, so every code is good at most
once. -/
theorem verify_increasing {s : ByteArray} {t : Nat} {c : String} {l n : Nat}
    (h : verify s t c (some l) = some n) : l < n := by
  unfold verify at h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, fresh, decide_eq_true_eq] at hp
  exact hp.1

/-- The step a code is accepted for is within one step of the current time. -/
theorem verify_near {s : ByteArray} {t : Nat} {c : String} {last : Option Nat} {n : Nat}
    (h : verify s t c last = some n) :
    n = stepOf t - 1 ∨ n = stepOf t ∨ n = stepOf t + 1 := by
  unfold verify at h
  have hm := List.mem_of_find?_eq_some h
  simpa using hm

/-! ## Several apps

An account may have several authenticator apps, each with its own secret and
its own last accepted step.  A submitted code is checked against each in turn
(`verifyAny`), and counts for the first one it verifies for: it uses up that
app's step and no other's.  A code from one app says nothing about another
app's secret, so there is nothing to use up there; and since every app's
accepted steps strictly increase on their own (`verify_increasing`), a code
accepted for an app is never accepted for that app again.  What
`verifyAny` decides is stated in `Pyle.Proofs.Decisions`. -/

/-- Check a submitted code against several apps, each given as an id, its
secret and the step of the last code it accepted: the first app the code
verifies for (`verify`), with the step it was accepted for. -/
def verifyAny {α : Type} (apps : List (α × ByteArray × Option Nat)) (unixTime : Nat)
    (code : String) : Option (α × Nat) :=
  apps.findSome? fun (id, secret, lastStep) => (verify secret unixTime code lastStep).map (id, ·)

/-- A fresh 20-byte secret from the operating system's generator. -/
def generateSecret : IO ByteArray := Crypto.randomBytes secretLength.toUSize

/-- Percent-encode everything but RFC 3986's unreserved characters. -/
def percentEncode (s : String) : String :=
  s.toUTF8.foldl (init := "") fun out b =>
    let c := Char.ofNat b.toNat
    if c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~' then out.push c
    else
      let hex := "0123456789ABCDEF".toList
      out.push '%' |>.push (hex.getD (b.toNat / 16) '0') |>.push (hex.getD (b.toNat % 16) '0')

/-- The `otpauth://` URI an authenticator app scans to enrol a secret: the
label is `issuer:account`, and the parameters repeat the issuer and spell out
the defaults, which some apps need to see.  The secret is unpadded base32. -/
def uri (issuer account : String) (secret : ByteArray) : String :=
  let b32 := (base32Encode secret).toList.filter (· != '=') |> String.ofList
  s!"otpauth://totp/{percentEncode issuer}:{percentEncode account}?secret={b32}" ++
    s!"&issuer={percentEncode issuer}&algorithm=SHA1&digits={digits}&period={period}"

end Totp
end Factor
end Pyle