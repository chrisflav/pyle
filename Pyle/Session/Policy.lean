import Pyle.Session.Session
import Pyle.Store.SignIn
import Pyle.SignIn.Secrets
import Pyle.WebAuthn.Registration
import Pyle.Factor.Totp
import Pyle.Factor.RecoveryCode
import Pyle.Factor.Password

/-!
# The assurance policy

DESIGN §1: a sign-in reaches an assurance level (`Acr`), computed from the
factors it used, and the session records it; each relying service decides
what it needs.  The levels, lowest first:

* `sfa` — one factor alone: a password (only where `allowPasswords` is on), or
  a WebAuthn assertion without user verification (a security key touched,
  with no PIN or fingerprint);
* `mfa` — two factors of distinct kinds;
* `phr` — a WebAuthn assertion with user verification;
* `phrh` — the same from a credential that is not backup-eligible, so its key
  is held by the authenticator and never synced.

A TOTP code alone and a recovery code alone reach no level at all: they are
only ever a second factor.

The policy is enforced by a type rather than by a check each handler must
remember (§9.3, in the style of kleis's `AuthorizedRequest`):

* A `Factor` is evidence that one factor was checked, for one user, just now.
  Its constructor is private to this file, and the only functions that make
  one are the checks below — `checkAssertion`, `checkTotp`, `checkRecovery`,
  `checkPassword` — each of which does the whole check against the store,
  including what makes it single-use: consuming the WebAuthn challenge and
  recording the signature counter, accepting the TOTP step, spending the
  recovery code.
* An `Authentication` is a list of factors for one user that the policy
  admits (`Admissible`), with the proof carried along.  Its constructor is
  private too; `Authentication.ofFactors` is the one way to make one, and it
  decides the policy.  Its level, `Authentication.level`, is computed from the
  factors (`level`); no caller supplies it.
* `establish`, which inserts a session row, and `stepUp`, which records a
  fresh authentication on one, take an `Authentication`.  The SQL that does
  either is private to this file, and nothing else in pyle inserts a session
  row or changes what one is worth.

A session row keeps the `amr` of the authentication, and the session's level
is read back from it (`Session.level`, `Acr.ofAmr`).  `level_eq_ofAmr` proves
that this gives exactly the level the factors reach, so the level recorded is
the level justified.  The theorems at the end say what the policy rules out
and what each level needs: TOTP alone and a recovery code alone give no
authentication (`totp_alone`, `recovery_alone`); `sfa` comes only from a
password or a security key without user verification, alone (`level_sfa`);
`phr` needs WebAuthn with user verification (`level_phr`), and `phrh` the
same from a device-bound credential (`level_phrh`).

**`amr`.**  The authentication method references (RFC 8176) are computed from
the factors: WebAuthn gives `hwk` for a device-bound credential and `swk` for
one that may be synced (backup-eligible), with `user` when the user was
verified; TOTP gives `otp`, a password `pwd`, and a recovery code the private
value `rec` (RFC 8176 has none for it).  Two distinct kinds of factor add
`mfa`.  OpenID Connect EAP ACR Values 1.0 §3 defines `pop` for a
proof-of-possession key whose storage is unknown; pyle always knows which of
`hwk` and `swk` applies, so it never needs `pop`.

**One factor of each kind.**  An authentication uses each kind of factor at
most once: two passwords, or the same security key twice, are one factor, and
two WebAuthn assertions in one sign-in are not something any endpoint asks
for.  This is what lets the level be read back from the `amr`.
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

/-- Whether a factor of this kind may be used alone, at `sfa`: a WebAuthn
assertion or a password, but never a TOTP code or a recovery code. -/
def FactorKind.alone : FactorKind → Bool
  | .webauthn => true
  | .password => true
  | .totp => false
  | .recovery => false

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

/-- A WebAuthn assertion with user verification: phishing-resistant. -/
def Factor.PhishingResistant (f : Factor) : Prop := f.kind = .webauthn ∧ f.userVerified = true

instance (f : Factor) : Decidable f.PhishingResistant := by
  unfold Factor.PhishingResistant; infer_instance

/-- A phishing-resistant factor from a device-bound credential. -/
def Factor.HardwareBound (f : Factor) : Prop :=
  f.kind = .webauthn ∧ f.userVerified = true ∧ f.backupEligible = false

instance (f : Factor) : Decidable f.HardwareBound := by
  unfold Factor.HardwareBound; infer_instance

/-- Whether factors of two distinct kinds are among `fs`. -/
def TwoKinds (fs : List Factor) : Prop := ∃ f ∈ fs, ∃ g ∈ fs, f.kind ≠ g.kind

instance (fs : List Factor) : Decidable (TwoKinds fs) := by
  unfold TwoKinds; infer_instance

/-- The level factors reach (DESIGN §1): `phrh` with a phishing-resistant
factor from a device-bound credential, `phr` with any phishing-resistant
factor, `mfa` with two kinds of factor, and `sfa` otherwise. -/
def level (fs : List Factor) : Acr :=
  if ∃ f ∈ fs, f.HardwareBound then .phrh
  else if ∃ f ∈ fs, f.PhishingResistant then .phr
  else if TwoKinds fs then .mfa
  else .sfa

/-- The factors the policy admits as one authentication: at least one, each
kind at most once, and, if they reach only `sfa`, a kind that may stand
alone. -/
def Admissible (fs : List Factor) : Prop :=
  fs ≠ [] ∧ (fs.map (·.kind)).Nodup ∧ (level fs = .sfa → ∀ f ∈ fs, f.kind.alone = true)

instance (fs : List Factor) : Decidable (Admissible fs) := by
  unfold Admissible; infer_instance

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
  if TwoKinds fs then base ++ ["mfa"] else base

/-! ## Authentications -/

/-- Factors of one user that the policy admits.  Only `ofFactors` makes these,
and a session is only ever created or stepped up with one. -/
structure Authentication where private mk ::
  /-- Whose authentication it is. -/
  user : UserId
  /-- The factors. -/
  factors : List Factor
  /-- The policy of DESIGN §1 admits them. -/
  admissible : Admissible factors
  /-- They are all the same user's. -/
  sameUser : ∀ f ∈ factors, f.user = user

namespace Authentication

/-- The authentication these factors amount to, if they are all one user's
and the policy admits them. -/
def ofFactors : List Factor → Option Authentication
  | [] => none
  | f :: fs =>
    if h : Admissible (f :: fs) ∧ ∀ g ∈ f :: fs, g.user = f.user then
      some ⟨f.user, f :: fs, h.1, h.2⟩
    else none

/-- The level the authentication reaches, computed from its factors. -/
def level (a : Authentication) : Acr := Policy.level a.factors

/-- The `amr` of the authentication. -/
def amr (a : Authentication) : List String := Policy.amr a.factors

/-- The labels of the authenticators used. -/
def labels (a : Authentication) : List String := (a.factors.map (·.label)).eraseDups

end Authentication

/-! ## What the policy rules out, and what each level needs -/

/-- `ofFactors` keeps the factors it was given. -/
theorem ofFactors_factors {fs : List Factor} {a : Authentication}
    (h : Authentication.ofFactors fs = some a) : a.factors = fs := by
  cases fs with
  | nil => simp [Authentication.ofFactors] at h
  | cons f fs =>
    simp only [Authentication.ofFactors] at h
    split at h
    · cases h; rfl
    · cases h

/-- One factor alone reaches `sfa` unless it is phishing-resistant. -/
theorem level_single {f : Factor} (h : ¬ f.PhishingResistant) : level [f] = .sfa := by
  have h1 : ¬ ∃ g ∈ [f], g.HardwareBound := by
    rintro ⟨g, hg, hk, hv, -⟩
    simp only [List.mem_singleton] at hg
    exact h (hg ▸ ⟨hk, hv⟩)
  have h2 : ¬ ∃ g ∈ [f], g.PhishingResistant := by
    rintro ⟨g, hg, hp⟩
    simp only [List.mem_singleton] at hg
    exact h (hg ▸ hp)
  have h3 : ¬ TwoKinds [f] := by
    rintro ⟨g, hg, g', hg', hne⟩
    simp only [List.mem_singleton] at hg hg'
    exact hne (by rw [hg, hg'])
  simp only [level, if_neg h1, if_neg h2, if_neg h3]

/-- One factor of a kind that may not stand alone is no authentication. -/
theorem ofFactors_single_not_alone {f : Factor} (h : f.kind.alone = false) :
    Authentication.ofFactors [f] = none := by
  have hp : ¬ f.PhishingResistant := fun ⟨hk, _⟩ => by rw [hk] at h; cases h
  simp only [Authentication.ofFactors]
  rw [dif_neg]
  rintro ⟨⟨-, -, hs⟩, -⟩
  have := hs (level_single hp) f (by simp)
  rw [h] at this
  cases this

/-- **A TOTP code alone never yields a session.** -/
theorem totp_alone {f : Factor} (h : f.kind = .totp) :
    Authentication.ofFactors [f] = none :=
  ofFactors_single_not_alone (by rw [h]; rfl)

/-- **A recovery code alone never yields a session.** -/
theorem recovery_alone {f : Factor} (h : f.kind = .recovery) :
    Authentication.ofFactors [f] = none :=
  ofFactors_single_not_alone (by rw [h]; rfl)

/-- One factor of a kind that may stand alone is an authentication, at the
level it reaches. -/
theorem ofFactors_single_alone {f : Factor} (h : f.kind.alone = true) :
    ∃ a, Authentication.ofFactors [f] = some a ∧ a.factors = [f] := by
  simp only [Authentication.ofFactors]
  rw [dif_pos]
  · exact ⟨_, rfl, rfl⟩
  · refine ⟨⟨by simp, by simp, fun _ g hg => ?_⟩, fun g hg => ?_⟩
    · simp only [List.mem_singleton] at hg
      rw [hg]; exact h
    · simp only [List.mem_singleton] at hg
      rw [hg]

/-- **A password alone signs in at `sfa`** (where passwords are allowed at
all: `checkPassword` makes no factor otherwise). -/
theorem password_alone {f : Factor} (h : f.kind = .password) :
    ∃ a, Authentication.ofFactors [f] = some a ∧ a.level = .sfa := by
  obtain ⟨a, ha, hf⟩ := ofFactors_single_alone (f := f) (by rw [h]; rfl)
  refine ⟨a, ha, ?_⟩
  simp only [Authentication.level, hf]
  exact level_single fun ⟨hk, _⟩ => by rw [h] at hk; cases hk

/-- **A security key touched without user verification signs in at
`sfa`.** -/
theorem key_alone {f : Factor} (hk : f.kind = .webauthn) (hv : f.userVerified = false) :
    ∃ a, Authentication.ofFactors [f] = some a ∧ a.level = .sfa := by
  obtain ⟨a, ha, hf⟩ := ofFactors_single_alone (f := f) (by rw [hk]; rfl)
  refine ⟨a, ha, ?_⟩
  simp only [Authentication.level, hf]
  exact level_single fun ⟨_, hv'⟩ => by rw [hv] at hv'; cases hv'

/-- Two factors of the same kind are no authentication: two passwords, or the
same security key twice, are one factor. -/
theorem ofFactors_same_kind {f g : Factor} (hk : f.kind = g.kind) :
    Authentication.ofFactors [f, g] = none := by
  simp only [Authentication.ofFactors]
  rw [dif_neg]
  rintro ⟨⟨-, hn, -⟩, -⟩
  simp [hk] at hn

/-- Factors of two different users are no authentication, whatever they
are. -/
theorem ofFactors_two_users {f g : Factor} (h : f.user ≠ g.user) :
    Authentication.ofFactors [f, g] = none := by
  simp only [Authentication.ofFactors]
  rw [dif_neg]
  intro ⟨_, hu⟩
  exact h (hu g (by simp)).symm

/-- Factors of distinct kinds reach at least `mfa`. -/
theorem mfa_le_level {fs : List Factor} (h : TwoKinds fs) : Acr.mfa ≤ level fs := by
  unfold level
  by_cases h1 : ∃ f ∈ fs, f.HardwareBound
  · rw [if_pos h1]; decide
  · rw [if_neg h1]
    by_cases h2 : ∃ f ∈ fs, f.PhishingResistant
    · rw [if_pos h2]; decide
    · rw [if_neg h2, if_pos h]; exact Acr.le_refl _

/-- **`sfa` comes only from one factor that may stand alone**: a password, or
a WebAuthn assertion without user verification. -/
theorem level_sfa (a : Authentication) (h : a.level = .sfa) :
    ∃ f, a.factors = [f] ∧
      (f.kind = .password ∨ (f.kind = .webauthn ∧ f.userVerified = false)) := by
  have h' : level a.factors = .sfa := h
  obtain ⟨hne, hn, halone⟩ := a.admissible
  have hp : ¬ ∃ f ∈ a.factors, f.PhishingResistant := by
    intro hp
    unfold level at h'
    by_cases h1 : ∃ f ∈ a.factors, f.HardwareBound
    · rw [if_pos h1] at h'; cases h'
    · rw [if_neg h1, if_pos hp] at h'; cases h'
  have ht : ¬ TwoKinds a.factors := fun ht => by
    have := mfa_le_level ht
    rw [h'] at this
    exact absurd this (by decide)
  have hall := halone h'
  clear halone h h'
  generalize a.factors = fs at hne hn hall hp ht ⊢
  rcases fs with _ | ⟨f, _ | ⟨g, rest⟩⟩
  · exact absurd rfl hne
  · refine ⟨f, rfl, ?_⟩
    have hf := hall f (by simp)
    have hpf : ¬ f.PhishingResistant := fun hpf => hp ⟨f, by simp, hpf⟩
    revert hf hpf
    obtain ⟨u, k, uv, be, l⟩ := f
    cases k <;> cases uv <;> simp [FactorKind.alone, Factor.PhishingResistant]
  · exfalso
    apply ht
    refine ⟨f, by simp, g, by simp, fun hk => ?_⟩
    simp [hk] at hn

/-- **`phr` needs WebAuthn with user verification.** -/
theorem level_phr (a : Authentication) (h : Acr.phr ≤ a.level) :
    ∃ f ∈ a.factors, f.kind = .webauthn ∧ f.userVerified = true := by
  revert h
  simp only [Authentication.level, level]
  split
  · rename_i hh
    obtain ⟨f, hf, hk, hv, -⟩ := hh
    exact fun _ => ⟨f, hf, hk, hv⟩
  · split
    · rename_i hp
      obtain ⟨f, hf, hk, hv⟩ := hp
      exact fun _ => ⟨f, hf, hk, hv⟩
    · split <;> intro h <;> exact absurd h (by decide)

/-- **`phrh` needs WebAuthn with user verification from a device-bound
credential** (one that is not backup-eligible). -/
theorem level_phrh (a : Authentication) (h : a.level = .phrh) :
    ∃ f ∈ a.factors, f.kind = .webauthn ∧ f.userVerified = true ∧ f.backupEligible = false := by
  revert h
  simp only [Authentication.level, level]
  split
  · rename_i hh
    exact fun _ => hh
  · split
    · nofun
    · split <;> nofun

/-- **`mfa` or better needs a phishing-resistant factor or two kinds of
factor.** -/
theorem level_mfa (a : Authentication) (h : Acr.mfa ≤ a.level) :
    (∃ f ∈ a.factors, f.PhishingResistant) ∨ TwoKinds a.factors := by
  revert h
  simp only [Authentication.level, level]
  split
  · rename_i hh
    obtain ⟨f, hf, hk, hv, -⟩ := hh
    exact fun _ => .inl ⟨f, hf, hk, hv⟩
  · split
    · rename_i hp
      exact fun _ => .inl hp
    · split
      · rename_i ht
        exact fun _ => .inr ht
      · intro h; cases h

/-! ## The level read back from the `amr` -/

/-- Two factors of one kind in a list whose kinds do not repeat are the same
factor. -/
theorem eq_of_kind_eq : ∀ {fs : List Factor}, (fs.map (·.kind)).Nodup →
    ∀ {f g : Factor}, f ∈ fs → g ∈ fs → f.kind = g.kind → f = g
  | [], _, _, _, hf, _, _ => by simp at hf
  | x :: xs, hn, f, g, hf, hg, hk => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hf with hf' | hf' <;> rcases List.mem_cons.mp hg with hg' | hg'
    · rw [hf', hg']
    · subst hf'
      exact absurd (List.mem_map.mpr ⟨g, hg', hk.symm⟩) hn.1
    · subst hg'
      exact absurd (List.mem_map.mpr ⟨f, hf', hk⟩) hn.1
    · exact eq_of_kind_eq hn.2 hf' hg' hk

/-- What is in the `amr` of factors: what one of them gives, or `mfa` for two
kinds. -/
theorem mem_amr {fs : List Factor} {s : String} :
    s ∈ amr fs ↔ (∃ f ∈ fs, s ∈ f.amr) ∨ (s = "mfa" ∧ TwoKinds fs) := by
  unfold amr
  split
  · rename_i ht
    simp [List.mem_eraseDups, List.mem_flatMap, ht]
  · rename_i ht
    simp [List.mem_eraseDups, List.mem_flatMap, ht]

theorem user_mem_amr {f : Factor} : "user" ∈ f.amr ↔ f.kind = .webauthn ∧ f.userVerified = true := by
  obtain ⟨u, k, uv, be, l⟩ := f
  cases k <;> cases uv <;> cases be <;> simp [Factor.amr]

theorem hwk_mem_amr {f : Factor} : "hwk" ∈ f.amr ↔ f.kind = .webauthn ∧ f.backupEligible = false := by
  obtain ⟨u, k, uv, be, l⟩ := f
  cases k <;> cases uv <;> cases be <;> simp [Factor.amr]

theorem swk_mem_amr {f : Factor} : "swk" ∈ f.amr ↔ f.kind = .webauthn ∧ f.backupEligible = true := by
  obtain ⟨u, k, uv, be, l⟩ := f
  cases k <;> cases uv <;> cases be <;> simp [Factor.amr]

theorem mfa_not_mem_amr {f : Factor} : "mfa" ∉ f.amr := by
  obtain ⟨u, k, uv, be, l⟩ := f
  cases k <;> cases uv <;> cases be <;> simp [Factor.amr]

/-- **The level read back from the `amr` is the level the factors reach**,
for factors whose kinds do not repeat — every authentication's. -/
theorem level_eq_ofAmr {fs : List Factor} (hn : (fs.map (·.kind)).Nodup) :
    Acr.ofAmr (amr fs) = level fs := by
  have hu : "user" ∈ amr fs ↔ ∃ f ∈ fs, f.PhishingResistant := by
    simp only [mem_amr, user_mem_amr, Factor.PhishingResistant]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact h
      · exact absurd h (by decide)
    · exact .inl
  have hh : "hwk" ∈ amr fs ↔ ∃ f ∈ fs, f.kind = .webauthn ∧ f.backupEligible = false := by
    simp only [mem_amr, hwk_mem_amr]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact h
      · exact absurd h (by decide)
    · exact .inl
  have hs : "swk" ∈ amr fs ↔ ∃ f ∈ fs, f.kind = .webauthn ∧ f.backupEligible = true := by
    simp only [mem_amr, swk_mem_amr]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact h
      · exact absurd h (by decide)
    · exact .inl
  have hm : "mfa" ∈ amr fs ↔ TwoKinds fs := by
    simp only [mem_amr]
    constructor
    · rintro (⟨f, -, hf⟩ | ⟨-, h⟩)
      · exact absurd hf mfa_not_mem_amr
      · exact h
    · exact fun h => .inr ⟨by trivial, h⟩
  have e1 : ("user" ∈ amr fs ∧ "hwk" ∈ amr fs) ↔ ∃ f ∈ fs, f.HardwareBound := by
    rw [hu, hh]
    constructor
    · rintro ⟨⟨f, hf, hk, hv⟩, ⟨g, hg, hk', hb⟩⟩
      have := eq_of_kind_eq hn hf hg (hk.trans hk'.symm)
      subst this
      exact ⟨f, hf, hk, hv, hb⟩
    · rintro ⟨f, hf, hk, hv, hb⟩
      exact ⟨⟨f, hf, hk, hv⟩, ⟨f, hf, hk, hb⟩⟩
  have e2 : (¬ ∃ f ∈ fs, f.HardwareBound) →
      (("user" ∈ amr fs ∧ "swk" ∈ amr fs) ↔ ∃ f ∈ fs, f.PhishingResistant) := by
    intro h1
    rw [hu, hs]
    constructor
    · exact fun h => h.1
    · rintro ⟨f, hf, hk, hv⟩
      refine ⟨⟨f, hf, hk, hv⟩, ⟨f, hf, hk, ?_⟩⟩
      cases hb : f.backupEligible
      · exact absurd ⟨f, hf, hk, hv, hb⟩ h1
      · rfl
  unfold Acr.ofAmr level
  simp only [List.contains_iff_mem, Bool.and_eq_true]
  by_cases h1 : ∃ f ∈ fs, f.HardwareBound
  · rw [if_pos (e1.mpr h1), if_pos h1]
  · rw [if_neg (fun h => h1 (e1.mp h)), if_neg h1]
    by_cases h2 : ∃ f ∈ fs, f.PhishingResistant
    · rw [if_pos ((e2 h1).mpr h2), if_pos h2]
    · rw [if_neg (fun h => h2 ((e2 h1).mp h)), if_neg h2]
      by_cases h3 : TwoKinds fs
      · rw [if_pos (hm.mpr h3), if_pos h3]
      · rw [if_neg (fun h => h3 (hm.mp h)), if_neg h3]

/-- **The level a session records is the level its authentication reached**:
a session keeps the `amr` (`establish`, `stepUp`), and `Session.level` reads
the level back from it. -/
theorem Authentication.level_eq_ofAmr (a : Authentication) : Acr.ofAmr a.amr = a.level :=
  Policy.level_eq_ofAmr a.admissible.2.1
/-! ## The checks

Each check does everything that makes its factor good once: there is no way
to obtain a `Factor` without the store recording that it was used. -/

/-- The WebAuthn relying party of a configuration.  User verification is not
required by the ceremony itself: an assertion without it is a factor that
reaches only `sfa` alone, and the policy decides. -/
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
  unless ch.admits cred.user do return .error .wrongUser
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
        v.backupState v.userVerified now do
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

/-- Start a session for an authentication, from the request `r`.  Returns the
session and the identifier to set as its cookie.  The session records the
authentication's `amr`, from which its level is read back
(`Authentication.level_eq_ofAmr`).

The session the request already carries, if any, is ended first: signing in
replaces it rather than leaving it live beside the new one, so an identifier
planted in the browser before sign-in is worthless after it.

This is the only function that creates a session. -/
def establish (ctx : Ctx) (r : Req) (a : Authentication) : IO (Session × String) := do
  if let some old := (r.cookie sessionCookieName).bind Session.decodeId then
    discard <| ctx.store.endSession (.of old)
  let id ← Crypto.randomBytes Session.idBytes.toUSize
  let now ← ctx.clock
  let row : SessionRow :=
    { idHash := .of id, user := a.user, amr := a.amr, factors := a.labels, authTime := now,
      created := now, lastSeen := now, clientAddress := r.clientAddress,
      userAgent := ((r.header "user-agent").getD "").take 256 |>.toString }
  insertSession ctx.store row
  return (Session.ofRow row, Session.encodeId id)

/-- Record a fresh authentication on a session (the step-up of §4), rotating
its identifier: `auth_time` becomes now, and the `amr` — and so the level —
and authenticators become this authentication's.  The level is replaced, not
combined: a step-up says how the user authenticated just now, which may be
more or less than before, and the sign-in page asks for one that reaches what
the request needs.  `none` if the authentication is another user's, or the
session had already been rotated or ended. -/
def stepUp (ctx : Ctx) (s : Session) (a : Authentication) :
    IO (Option (Session × String)) := do
  if a.user != s.user then return none
  let id ← Crypto.randomBytes Session.idBytes.toUSize
  let now ← ctx.clock
  let newHash := SecretHash.of id
  if ← reauthenticateSession ctx.store s.idHash newHash a.amr a.labels now then
    return some ({ s with idHash := newHash, amr := a.amr, factors := a.labels,
                          authTime := now, lastSeen := now }, Session.encodeId id)
  return none

/-- Whether a session satisfies a request for a fresh or strong sign-in: its
`auth_time` is within `maxAge` seconds of `now`, if one is given, and its level
meets `want`. -/
def satisfies (s : Session) (now : Nat) (maxAge : Option Nat) (want : Acr) : Bool :=
  (maxAge.all fun m => now ≤ s.authTime + m) && s.level.satisfies want

/-! ## What an account could reach -/

/-- The kinds of factor an account has registered (DESIGN §1): its
credentials, whether they verify the user and are device-bound, a TOTP
secret, a password where passwords are allowed, and unspent recovery codes. -/
def capabilities (ctx : Ctx) (user : UserId) : IO Acr.Capabilities := do
  let creds ← ctx.store.listCredentials user
  let password := ctx.config.allowPasswords && (← ctx.store.findPassword user).isSome
  return { verifyingDeviceBound := creds.any fun c => c.userVerified && !c.backupEligible,
           verifying := creds.any (·.userVerified), webauthn := !creds.isEmpty,
           totp := (← ctx.store.findTotp user).isSome, password,
           recovery := (← ctx.store.unspentRecoveryCodes user) > 0 }

/-- The strongest level an account could sign in at, if any
(`Acr.Capabilities.level`): what services receive as `pyle_account_acr`. -/
def accountLevel (ctx : Ctx) (user : UserId) : IO (Option Acr) :=
  return (← capabilities ctx user).level

end Policy
end Pyle
