import Pyle.Session.Session
import Pyle.Store.SignIn
import Pyle.SignIn.Secrets
import Pyle.WebAuthn.Registration
import Pyle.Factor.Totp
import Pyle.Factor.RecoveryCode
import Pyle.Factor.Password

/-!
# The assurance policy

DESIGN §1: a session is *strong* if it was established by a WebAuthn
assertion with user verification, or by any two distinct factors; only strong
sessions exist.  A password alone, or a TOTP code alone, produces no session
at all — it is only a step.

The policy is enforced by a type rather than by a check each handler must
remember (§9.3, in the style of kleis's `AuthorizedRequest`):

* A `Factor` is evidence that one factor was checked, for one user, just now.
  Its constructor is private to this file, and the only functions that make
  one are the checks below — `checkAssertion`, `checkTotp`, `checkRecovery`,
  `checkPassword` — each of which does the whole check against the store,
  including what makes it single-use: consuming the WebAuthn challenge and
  recording the signature counter, accepting the TOTP step, spending the
  recovery code.
* A `StrongAuthentication` is a list of factors for one user that satisfies
  the policy, with the proof (`StrongAuthentication.strong`) carried along.
  Its constructor is private too; `StrongAuthentication.ofFactors` is the one
  way to make one, and it decides the policy.
* `establish`, which inserts a session row, and `stepUp`, which records a
  fresh authentication on one, take a `StrongAuthentication`.  The SQL that
  does either is private to this file, and nothing else in pyle inserts a
  session row or changes what one is worth.

So "no session without the policy" is not a theorem to keep up to date: a
session row is only ever written with a `StrongAuthentication` in hand, and a
`StrongAuthentication` only exists for factors that satisfy `Satisfies`.  The
theorems at the end say what that rules out: one factor that is not WebAuthn
with user verification, or two of the same kind.

**`amr` and `acr`.**  The authentication method references (RFC 8176) are
computed from the factors: WebAuthn gives `hwk` for a device-bound credential
and `swk` for one that may be synced (backup-eligible), with `user` when the
user was verified; TOTP gives `otp`, a password `pwd`, and a recovery code the
private value `rec` (RFC 8176 has none for it).  Two distinct kinds of factor
add `mfa`.  `acr` is `phr` (phishing-resistant) when the `amr` has `user` and a
WebAuthn key, and `mfa` otherwise.
-/

namespace Pyle

open Http Store

/-- User ids are compared by their row ids. -/
instance : DecidableEq Store.UserId := fun a b =>
  if h : a.val = b.val then isTrue (by cases a; cases b; cases h; rfl)
  else isFalse (fun e => h (congrArg Store.UserId.val e))

namespace Policy

/-! ## Factors -/

/-- The kinds of factor DESIGN §1 names.  Two factors are distinct when their
kinds are. -/
inductive FactorKind where
  /-- A WebAuthn assertion: a passkey or a security key. -/
  | webauthn
  /-- A TOTP code. -/
  | totp
  /-- A recovery code. -/
  | recovery
  /-- A password. -/
  | password
  deriving DecidableEq, Repr

/-- Evidence that one factor was checked for one user.  Only the checks in
this file make these. -/
structure Factor where private mk ::
  /-- Whose factor it is. -/
  user : UserId
  /-- What kind of factor. -/
  kind : FactorKind
  /-- For WebAuthn, whether the authenticator verified the user. -/
  userVerified : Bool
  /-- For WebAuthn, whether the credential may be synced (`swk` rather than
  `hwk`). -/
  backupEligible : Bool
  /-- The authenticator used, for the session list: `webauthn:<credential id
  in base64url>`, `totp`, `recovery` or `password`. -/
  label : String

/-- A WebAuthn assertion with user verification: on its own, enough. -/
def Factor.PhishingResistant (f : Factor) : Prop := f.kind = .webauthn ∧ f.userVerified = true

instance (f : Factor) : Decidable f.PhishingResistant := by
  unfold Factor.PhishingResistant; infer_instance

/-- The policy of DESIGN §1, over the factors of one sign-in: one WebAuthn
assertion with user verification, or two factors of distinct kinds. -/
def Satisfies (fs : List Factor) : Prop :=
  (∃ f ∈ fs, f.PhishingResistant) ∨ (∃ f ∈ fs, ∃ g ∈ fs, f.kind ≠ g.kind)

instance (fs : List Factor) : Decidable (Satisfies fs) := by
  unfold Satisfies; infer_instance

/-- The `amr` values of one factor. -/
def Factor.amr (f : Factor) : List String :=
  match f.kind with
  | .webauthn =>
    [if f.backupEligible then "swk" else "hwk"] ++ (if f.userVerified then ["user"] else [])
  | .totp => ["otp"]
  | .recovery => ["rec"]
  | .password => ["pwd"]

/-- The `amr` of a sign-in: each factor's values, without repeats, and `mfa`
when two kinds of factor were used. -/
def amr (fs : List Factor) : List String :=
  let base := (fs.flatMap Factor.amr).eraseDups
  if (fs.map (·.kind)).eraseDups.length ≥ 2 then base ++ ["mfa"] else base

/-- The `acr` of an `amr`: `phr` when it has `user` and a WebAuthn key, `mfa`
otherwise. -/
def acr (amr : List String) : String :=
  if amr.contains "user" && (amr.contains "hwk" || amr.contains "swk") then "phr" else "mfa"

/-! ## Strong authentication -/

/-- Factors of one user that satisfy the policy.  Only `ofFactors` makes
these, and a session is only ever created or stepped up with one. -/
structure StrongAuthentication where private mk ::
  /-- Whose authentication it is. -/
  user : UserId
  /-- The factors. -/
  factors : List Factor
  /-- They satisfy the policy of DESIGN §1. -/
  strong : Satisfies factors
  /-- They are all the same user's. -/
  sameUser : ∀ f ∈ factors, f.user = user

namespace StrongAuthentication

/-- The strong authentication these factors amount to, if they are all one
user's and satisfy the policy. -/
def ofFactors : List Factor → Option StrongAuthentication
  | [] => none
  | f :: fs =>
    if h : Satisfies (f :: fs) ∧ ∀ g ∈ f :: fs, g.user = f.user then
      some ⟨f.user, f :: fs, h.1, h.2⟩
    else none

/-- The `amr` of the authentication. -/
def amr (sa : StrongAuthentication) : List String := Policy.amr sa.factors

/-- The labels of the authenticators used. -/
def labels (sa : StrongAuthentication) : List String := (sa.factors.map (·.label)).eraseDups

/-- Whether it is phishing-resistant: some factor is WebAuthn with user
verification. -/
def phishingResistant (sa : StrongAuthentication) : Bool :=
  sa.factors.any fun f => decide f.PhishingResistant

end StrongAuthentication

/-! ## What the policy rules out -/

/-- `ofFactors` keeps the factors it was given. -/
theorem ofFactors_factors {fs : List Factor} {sa : StrongAuthentication}
    (h : StrongAuthentication.ofFactors fs = some sa) : sa.factors = fs := by
  cases fs with
  | nil => simp [StrongAuthentication.ofFactors] at h
  | cons f fs =>
    simp only [StrongAuthentication.ofFactors] at h
    split at h
    · cases h; rfl
    · cases h

/-- One factor that is not a WebAuthn assertion with user verification is no
strong authentication. -/
theorem ofFactors_single {f : Factor} (h : ¬ f.PhishingResistant) :
    StrongAuthentication.ofFactors [f] = none := by
  simp only [StrongAuthentication.ofFactors]
  rw [dif_neg]
  intro ⟨hs, _⟩
  rcases hs with ⟨g, hg, hp⟩ | ⟨g, hg, g', hg', hne⟩
  · simp only [List.mem_singleton] at hg
    exact h (hg ▸ hp)
  · simp only [List.mem_singleton] at hg hg'
    exact hne (by rw [hg, hg'])

/-- **A password alone never yields a session.** -/
theorem password_alone {f : Factor} (h : f.kind = .password) :
    StrongAuthentication.ofFactors [f] = none :=
  ofFactors_single fun hp => by simp [Factor.PhishingResistant, h] at hp

/-- **A TOTP code alone never yields a session.** -/
theorem totp_alone {f : Factor} (h : f.kind = .totp) :
    StrongAuthentication.ofFactors [f] = none :=
  ofFactors_single fun hp => by simp [Factor.PhishingResistant, h] at hp

/-- **A recovery code alone never yields a session.** -/
theorem recovery_alone {f : Factor} (h : f.kind = .recovery) :
    StrongAuthentication.ofFactors [f] = none :=
  ofFactors_single fun hp => by simp [Factor.PhishingResistant, h] at hp

/-- Two factors of the same kind, neither of them WebAuthn with user
verification, are no strong authentication: two passwords, or the same
security key twice, are one factor. -/
theorem ofFactors_same_kind {f g : Factor} (hk : f.kind = g.kind) (hf : ¬ f.PhishingResistant)
    (hg : ¬ g.PhishingResistant) : StrongAuthentication.ofFactors [f, g] = none := by
  simp only [StrongAuthentication.ofFactors]
  rw [dif_neg]
  intro ⟨hs, _⟩
  rcases hs with ⟨x, hx, hp⟩ | ⟨x, hx, y, hy, hne⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hf hp
    · exact hg hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all

/-- Factors of two different users are no strong authentication, whatever
they are. -/
theorem ofFactors_two_users {f g : Factor} (h : f.user ≠ g.user) :
    StrongAuthentication.ofFactors [f, g] = none := by
  simp only [StrongAuthentication.ofFactors]
  rw [dif_neg]
  intro ⟨_, hu⟩
  exact h (hu g (by simp)).symm

/-- Every strong authentication has a phishing-resistant factor or two
factors of distinct kinds.  (This is the field `strong`; stated again so that
it can be read without the structure.) -/
theorem strong (sa : StrongAuthentication) :
    (∃ f ∈ sa.factors, f.PhishingResistant) ∨
      (∃ f ∈ sa.factors, ∃ g ∈ sa.factors, f.kind ≠ g.kind) :=
  sa.strong

/-! ## The checks

Each check does everything that makes its factor good once: there is no way
to obtain a `Factor` without the store recording that it was used. -/

/-- The WebAuthn relying party of a configuration.  User verification is not
required by the ceremony itself: an assertion without it is a factor, just not
one that suffices alone, and the policy decides. -/
def relyingParty (c : Config) (requireUserVerification : Bool := false) :
    WebAuthn.RelyingParty :=
  { id := c.rpId, origins := c.origins, requireUserVerification }

/-- A stored credential in the form the ceremony takes. -/
def toStoredCredential (cred : Credential) (handle : ByteArray) :
    Option WebAuthn.StoredCredential := do
  let algorithm ← WebAuthn.CoseAlgorithm.ofInt? cred.algorithm
  return { id := cred.id, userHandle := handle, publicKey := { algorithm, bytes := cred.publicKey },
           signCount := cred.signCount.toUInt32, backupEligible := cred.backupEligible }

/-- The challenge a client data names, decoded; `none` if the client data
does not parse or the challenge is not base64url. -/
def challengeOf (clientDataJSON : ByteArray) : Option ByteArray := do
  let cd ← (WebAuthn.ClientData.parse clientDataJSON).toOption
  Encoding.Base64Url.decode cd.challenge

/-- Why an assertion was refused. -/
inductive AssertionRefusal where
  /-- The client data names no challenge that could be read. -/
  | malformed
  /-- The challenge is not pending, was for another purpose, or expired. -/
  | unknownChallenge
  /-- No credential has that id. -/
  | unknownCredential
  /-- The challenge was issued to another user than the credential's. -/
  | wrongUser
  /-- The account is disabled. -/
  | disabled
  /-- A check of DESIGN §2.1 failed. -/
  | failed (e : WebAuthn.AssertionError)
  /-- Another assertion with the same counter was recorded first. -/
  | raced
  deriving Repr

/-- A short reason for the audit log. -/
def AssertionRefusal.reason : AssertionRefusal → String
  | .malformed => "malformed client data"
  | .unknownChallenge => "unknown or expired challenge"
  | .unknownCredential => "unknown credential"
  | .wrongUser => "challenge issued to another user"
  | .disabled => "account disabled"
  | .failed .possiblyCloned => "possibly cloned: the counter did not increase"
  | .failed e => s!"assertion refused: {reprStr e}"
  | .raced => "counter raced"

/-- A checked assertion: the factor, and the account and credential it was
for. -/
structure CheckedAssertion where
  /-- The factor. -/
  factor : Factor
  /-- The account. -/
  user : User
  /-- The credential, as it was before this assertion. -/
  credential : Credential

/-- Check a WebAuthn assertion for a ceremony begun with `purpose`.

The challenge is read from the client data and consumed first, so the first
attempt that names it uses it up whatever happens next (§2.1).  If the
challenge was issued to a user, the credential must be theirs and among their
credentials (the `allowCredentials` of that ceremony); if it was not — the
discoverable flow — the browser must return the user handle.  On success the
new counter is recorded by compare-and-set, so two assertions racing with one
counter cannot both count, and a counter that did not increase refuses the
assertion as possibly cloned. -/
def checkAssertion (ctx : Ctx) (purpose : ChallengePurpose) (r : WebAuthn.AssertionResponse) :
    IO (Except AssertionRefusal CheckedAssertion) := do
  let some challenge := challengeOf r.clientDataJSON | return .error .malformed
  let now ← ctx.clock
  let some ch ← ctx.store.consumeChallenge challenge purpose now
    | return .error .unknownChallenge
  let some cred ← ctx.store.findCredential r.credentialId | return .error .unknownCredential
  if let some u := ch.user then
    if u != cred.user then return .error .wrongUser
  let some user ← ctx.store.findUser cred.user | return .error .unknownCredential
  if user.disabled then return .error .disabled
  let allow ← match ch.user with
    | some u => pure (some ((← ctx.store.listCredentials u).toList.map (·.id)))
    | none => pure none
  let some stored := toStoredCredential cred user.handle | return .error .unknownCredential
  match WebAuthn.verifyAssertion (relyingParty ctx.config) challenge allow stored r
      (requireUserHandle := ch.user.isNone) with
  | .error e => return .error (.failed e)
  | .ok v =>
    unless ← ctx.store.recordCredentialUse cred.id cred.signCount v.signCount.toNat
        v.backupState now do
      return .error .raced
    let factor : Factor :=
      ⟨user.id, .webauthn, v.userVerified, cred.backupEligible,
        "webauthn:" ++ Encoding.Base64Url.encode cred.id⟩
    return .ok { factor, user, credential := cred }

/-- Why a TOTP code was refused. -/
inductive TotpRefusal where
  /-- The user has no TOTP secret. -/
  | notEnrolled
  /-- TOTP is locked for this account until the given time (§7). -/
  | locked (lockedUntil : Nat)
  /-- The code is wrong or was used before; if this failure locked TOTP, until
  when. -/
  | wrong (lockedUntil : Option Nat)
  deriving Repr, BEq

/-- A code as typed: spaces removed. -/
def normaliseCode (code : String) : String := String.ofList (code.toList.filter (!·.isWhitespace))

/-- Check a TOTP code for a user (§3).  Accepted only for a step later than
the last accepted one, and recorded in the same conditional `UPDATE` that
checks that; a wrong code counts towards the lock of §7, five failures
locking TOTP for fifteen minutes. -/
def checkTotp (ctx : Ctx) (user : UserId) (code : String) : IO (Except TotpRefusal Factor) := do
  let now ← ctx.clock
  let some rec ← ctx.store.findTotp user | return .error .notEnrolled
  if now < rec.lockedUntil then return .error (.locked rec.lockedUntil)
  let secret ← IO.ofExcept (SignIn.Secrets.openTotp ctx.rootKey user rec.sealedSecret
    |>.mapError fun _ => "the stored TOTP secret does not open under the root key")
  let code := normaliseCode code
  match Factor.Totp.verify secret now code rec.lastStep with
  | some step =>
    if ← ctx.store.acceptTotpStep user step now then
      return .ok ⟨user, .totp, false, false, "totp"⟩
    return .error (.wrong (← ctx.store.recordTotpFailure user now))
  | none => return .error (.wrong (← ctx.store.recordTotpFailure user now))

/-- Whether a recovery code is one of the user's unspent ones, without
spending it: for checking it before a factor whose failures count (TOTP), so
that a guess at the code cannot be used to lock TOTP. -/
def recoveryCodeValid (ctx : Ctx) (user : UserId) (code : String) : IO Bool := do
  if !Factor.RecoveryCode.wellFormed code then return false
  ctx.store.hasRecoveryCode user
    (Factor.RecoveryCode.digest (SignIn.Secrets.recoveryKey ctx.rootKey) code)

/-- Check a recovery code for a user, spending it (§3).  A code is good once. -/
def checkRecovery (ctx : Ctx) (user : UserId) (code : String) : IO (Option Factor) := do
  if !Factor.RecoveryCode.wellFormed code then return none
  let digest := Factor.RecoveryCode.digest (SignIn.Secrets.recoveryKey ctx.rootKey) code
  if ← ctx.store.spendRecoveryCode user digest (← ctx.clock) then
    return some ⟨user, .recovery, false, false, "recovery"⟩
  return none

/-- A well-formed Argon2id hash that no password matches in practice: what a
password is checked against when there is no stored one, so that the answer
takes as long as a real check (§7). -/
def decoyPasswordHash : String :=
  "$argon2id$v=19$m=65536,t=3,p=4$AAAAAAAAAAAAAAAAAAAAAA$" ++ String.ofList (List.replicate 43 'A')

/-- Check a password for a user, if passwords are enabled and they have
one.  Without one, the password is still hashed (against
`decoyPasswordHash`), so the time taken does not say which accounts have a
password. -/
def checkPassword (ctx : Ctx) (user : Option UserId) (password : String) :
    IO (Option Factor) := do
  if !ctx.config.allowPasswords then return none
  let phc ← match user with
    | some u => ctx.store.findPassword u
    | none => pure none
  let some u := user | discard <| Factor.Password.verify decoyPasswordHash password; return none
  let some phc := phc | discard <| Factor.Password.verify decoyPasswordHash password; return none
  if ← Factor.Password.verify phc password then
    return some ⟨u, .password, false, false, "password"⟩
  return none

/-! ## Sessions

The two statements that write what a session is worth, private to this file,
and the two functions that run them. -/

/-- Insert a session row. -/
private def insertSession (s : Store) (r : SessionRow) : IO Unit := s.run fun c => do
  discard <| exec c
    s!"INSERT INTO sessions ({sessionColumns}) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)"
    #[r.idHash, r.user, encodeList r.amr, encodeList r.factors, r.authTime, r.created,
      r.lastSeen, r.clientAddress, r.userAgent]

/-- Give a session a new identifier and record a fresh authentication on it.
Whether it applied. -/
private def reauthenticateSession (s : Store) (old new : SecretHash) (amr factors : List String)
    (now : Nat) : IO Bool := s.run fun c => do
  return (← exec c
    "UPDATE sessions SET id_hash = ?, amr = ?, factors = ?, auth_time = ?, last_seen = ? \
      WHERE id_hash = ?"
    #[new, encodeList amr, encodeList factors, now, now, old]) > 0

/-- Start a session for a strong authentication, from the request `r`.
Returns the session and the identifier to set as its cookie.

The session the request already carries, if any, is ended first: signing in
replaces it rather than leaving it live beside the new one, so an identifier
planted in the browser before sign-in is worthless after it.

This is the only function that creates a session. -/
def establish (ctx : Ctx) (r : Req) (sa : StrongAuthentication) : IO (Session × String) := do
  if let some old := (r.cookie sessionCookieName).bind Session.decodeId then
    discard <| ctx.store.endSession (.of old)
  let id ← Crypto.randomBytes Session.idBytes.toUSize
  let now ← ctx.clock
  let row : SessionRow :=
    { idHash := .of id, user := sa.user, amr := sa.amr, factors := sa.labels, authTime := now,
      created := now, lastSeen := now, clientAddress := r.clientAddress,
      userAgent := ((r.header "user-agent").getD "").take 256 |>.toString }
  insertSession ctx.store row
  return (Session.ofRow row, Session.encodeId id)

/-- Record a fresh strong authentication on a session (the step-up of §4),
rotating its identifier: `auth_time` becomes now, and the `amr` and
authenticators become this authentication's.  `none` if the authentication is
another user's, or the session had already been rotated or ended. -/
def stepUp (ctx : Ctx) (s : Session) (sa : StrongAuthentication) :
    IO (Option (Session × String)) := do
  if sa.user != s.user then return none
  let id ← Crypto.randomBytes Session.idBytes.toUSize
  let now ← ctx.clock
  let newHash := SecretHash.of id
  if ← reauthenticateSession ctx.store s.idHash newHash sa.amr sa.labels now then
    return some ({ s with idHash := newHash, amr := sa.amr, factors := sa.labels,
                          authTime := now, lastSeen := now }, Session.encodeId id)
  return none

/-- Whether a session satisfies a request for a fresh or strong sign-in: its
`auth_time` is within `maxAge` seconds of `now`, if one is given, and its
`acr` is `phr`, if that is asked for. -/
def satisfies (s : Session) (now : Nat) (maxAge : Option Nat) (wantPhr : Bool) : Bool :=
  (maxAge.all fun m => now ≤ s.authTime + m) && (!wantPhr || acr s.amr == "phr")

end Policy
end Pyle