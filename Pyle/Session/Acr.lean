/-!
# Assurance levels

What a sign-in is worth, as the `acr` (authentication context class
reference) a relying service receives (DESIGN.md §1).  pyle records four
levels, each a published identifier, lowest first:

| level | identifier | means |
| --- | --- | --- |
| `sfa` | `https://refeds.org/profile/sfa` | one factor (REFEDS SFA Profile 1.0) |
| `mfa` | `https://refeds.org/profile/mfa` | two factors of distinct kinds (REFEDS MFA Profile) |
| `phr` | `phr` | phishing-resistant (OpenID Connect EAP ACR Values 1.0 §2) |
| `phrh` | `phrh` | phishing-resistant, the key held in hardware (the same, §2) |

Each level satisfies every level below it (`satisfies`), and the order is a
total order (`le_total`, `le_antisymm`, `le_trans`).  For pyle, `phr` is a
WebAuthn assertion with user verification — the browser binds it to the
origin, so a party in the middle learns nothing it can replay elsewhere — and
`phrh` is one from a credential that is not backup-eligible, whose private key
therefore never leaves the authenticator.  The policy that decides which
factors reach which level is `Pyle.Policy`; this module only knows the
levels, how they are written, and how to read one back from the `amr` values
a sign-in recorded (`ofAmr`).

**Identifiers on the wire.**  `ofIdentifier?` reads what a relying party may
send in `acr_values` or the `claims` parameter: the four identifiers, the bare
`mfa` pyle answered with before levels existed, and REFEDS MFA 2.0's
`https://refeds.org/profile/mfa/phr`, which asks for two factors one of which
is phishing-resistant and is met by a passkey that verifies the user.
`ofName?` also reads the short names `sfa`, `mfa`, `phr`, `phrh`, for the
command line, the configuration and pyle's own sign-in links.
-/

namespace Pyle

/-- The assurance levels pyle records, lowest first. -/
inductive Acr where
  /-- One factor: a password, or a security key that did not verify the user. -/
  | sfa
  /-- Two factors of distinct kinds. -/
  | mfa
  /-- Phishing-resistant: WebAuthn with user verification. -/
  | phr
  /-- Phishing-resistant from a device-bound credential: WebAuthn with user
  verification from a credential that is not backup-eligible. -/
  | phrh
  deriving DecidableEq, Repr, Inhabited

namespace Acr

/-- The position of a level in the order. -/
def rank : Acr → Nat
  | .sfa => 0
  | .mfa => 1
  | .phr => 2
  | .phrh => 3

/-- `a ≤ b` when `b` is at least as strong as `a`. -/
instance : LE Acr := ⟨fun a b => a.rank ≤ b.rank⟩

instance (a b : Acr) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.rank ≤ b.rank))

/-- Every level, lowest first. -/
def all : List Acr := [.sfa, .mfa, .phr, .phrh]

/-- The identifier a level is written as in tokens and discovery. -/
def identifier : Acr → String
  | .sfa => "https://refeds.org/profile/sfa"
  | .mfa => "https://refeds.org/profile/mfa"
  | .phr => "phr"
  | .phrh => "phrh"

/-- The short name of a level, for people and for pyle's own links. -/
def shortName : Acr → String
  | .sfa => "sfa"
  | .mfa => "mfa"
  | .phr => "phr"
  | .phrh => "phrh"

instance : ToString Acr := ⟨identifier⟩

/-- A level as a relying party names it: one of the four identifiers, the bare
`mfa` of earlier versions of pyle, or REFEDS MFA 2.0's phishing-resistant MFA
(see the module documentation).  Anything else is not a level pyle knows. -/
def ofIdentifier? : String → Option Acr
  | "https://refeds.org/profile/sfa" => some .sfa
  | "https://refeds.org/profile/mfa" => some .mfa
  | "mfa" => some .mfa
  | "https://refeds.org/profile/mfa/phr" => some .phr
  | "phr" => some .phr
  | "phrh" => some .phrh
  | _ => none

/-- A level as an administrator or pyle's own pages name it: what
`ofIdentifier?` reads, or a short name. -/
def ofName? (s : String) : Option Acr :=
  if s == "sfa" then some .sfa else ofIdentifier? s

/-- The stronger of two levels. -/
def max (a b : Acr) : Acr := if a ≤ b then b else a

/-- The weaker of two levels. -/
def min (a b : Acr) : Acr := if a ≤ b then a else b

/-- Whether a sign-in at level `got` meets a demand for level `want`. -/
def satisfies (got want : Acr) : Bool := decide (want ≤ got)

/-- The level a list of `amr` values (RFC 8176) records: `phrh` with `user`
and `hwk`, `phr` with `user` and `swk`, `mfa` with `mfa`, and `sfa`
otherwise.  `Policy.Authentication.level_eq_ofAmr` proves that for every
authentication pyle accepts this gives back the level its factors reach, so a
session, a code or a token that keeps the `amr` keeps the level. -/
def ofAmr (amr : List String) : Acr :=
  if amr.contains "user" && amr.contains "hwk" then .phrh
  else if amr.contains "user" && amr.contains "swk" then .phr
  else if amr.contains "mfa" then .mfa
  else .sfa

/-! ## The order -/

theorem le_iff {a b : Acr} : a ≤ b ↔ a.rank ≤ b.rank := Iff.rfl

theorem le_refl (a : Acr) : a ≤ a := Nat.le_refl _

theorem le_trans {a b c : Acr} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := Nat.le_trans h₁ h₂

theorem le_total (a b : Acr) : a ≤ b ∨ b ≤ a := Nat.le_total _ _

theorem rank_injective {a b : Acr} (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [rank] at h)

theorem le_antisymm {a b : Acr} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
  rank_injective (Nat.le_antisymm h₁ h₂)

/-- `sfa` is the least level. -/
theorem sfa_le (a : Acr) : Acr.sfa ≤ a := Nat.zero_le _

/-- `phrh` is the greatest level. -/
theorem le_phrh (a : Acr) : a ≤ Acr.phrh := by cases a <;> decide

theorem le_max_left (a b : Acr) : a ≤ max a b := by
  unfold max; split
  · assumption
  · exact le_refl a

theorem le_max_right (a b : Acr) : b ≤ max a b := by
  unfold max; split
  · exact le_refl b
  · rcases le_total a b with h | h
    · contradiction
    · exact h

theorem min_le_left (a b : Acr) : min a b ≤ a := by
  unfold min; split
  · exact le_refl a
  · rcases le_total a b with h | h
    · contradiction
    · exact h

theorem min_le_right (a b : Acr) : min a b ≤ b := by
  unfold min; split
  · assumption
  · exact le_refl b

/-! ## Satisfying a demand -/

theorem satisfies_iff {h w : Acr} : satisfies h w = true ↔ w ≤ h := by
  simp [satisfies]

/-- Every level satisfies itself. -/
theorem satisfies_refl (a : Acr) : satisfies a a = true := satisfies_iff.mpr (le_refl a)

/-- **`satisfies` is monotone**: a stronger sign-in meets every demand a weaker
one meets, and a sign-in that meets a demand meets every weaker demand. -/
theorem satisfies_mono {h h' w w' : Acr} (hs : satisfies h w = true) (hh : h ≤ h')
    (hw : w' ≤ w) : satisfies h' w' = true :=
  satisfies_iff.mpr (le_trans hw (le_trans (satisfies_iff.mp hs) hh))

/-- Meeting the stronger of two demands meets both: a demand a request adds
to a floor never lowers the floor. -/
theorem satisfies_max {h a b : Acr} (hs : satisfies h (max a b) = true) :
    satisfies h a = true ∧ satisfies h b = true :=
  ⟨satisfies_mono hs (le_refl h) (le_max_left a b),
   satisfies_mono hs (le_refl h) (le_max_right a b)⟩

/-- Every level is read back from its identifier. -/
theorem ofIdentifier_identifier (a : Acr) : ofIdentifier? a.identifier = some a := by
  cases a <;> rfl

/-- Every level is read back from its short name. -/
theorem ofName_shortName (a : Acr) : ofName? a.shortName = some a := by
  cases a <;> rfl

/-! ## What an account could reach -/

/-- What kinds of factor an account has registered, for working out the
strongest level it could sign in at (`level`). -/
structure Capabilities where
  /-- A WebAuthn credential that verifies the user and is not backup-eligible. -/
  verifyingDeviceBound : Bool := false
  /-- A WebAuthn credential that verifies the user. -/
  verifying : Bool := false
  /-- Any WebAuthn credential. -/
  webauthn : Bool := false
  /-- A TOTP secret. -/
  totp : Bool := false
  /-- A password, in a deployment that allows them. -/
  password : Bool := false
  /-- Unspent recovery codes. -/
  recovery : Bool := false
  deriving Repr, BEq, Inhabited

/-- The strongest level an account with these factors could sign in at:
`phrh` or `phr` with a credential that verifies the user (device-bound for
`phrh`), `mfa` with two kinds of factor, `sfa` with a security key or a
password alone, and none with neither (a TOTP secret or recovery codes alone
are never enough). -/
def Capabilities.level (c : Capabilities) : Option Acr :=
  if c.verifyingDeviceBound then some .phrh
  else if c.verifying then some .phr
  else if [c.webauthn, c.totp, c.password, c.recovery].count true ≥ 2 then some .mfa
  else if c.webauthn || c.password then some .sfa
  else none

/-- The level a change to an account's authenticators needs (DESIGN §4): the
account's own best level, or `mfa`, whichever is lower.  An account that can
only sign in with one factor can still manage itself with that factor; one
that has two kinds of factor, or a passkey, needs two factors or the passkey,
as before levels existed.  An account with no way in at all needs `mfa`,
which it cannot give. -/
def Capabilities.changeLevel (c : Capabilities) : Acr := min (c.level.getD .mfa) .mfa

/-- A change never needs more than `mfa`. -/
theorem Capabilities.changeLevel_le_mfa (c : Capabilities) : c.changeLevel ≤ .mfa :=
  min_le_right _ _

/-- An account that could sign in at `mfa` or better needs `mfa` for a change:
levels do not lower the protection an account with two factors had. -/
theorem Capabilities.changeLevel_eq_mfa {c : Capabilities} {a : Acr} (h : c.level = some a)
    (ha : Acr.mfa ≤ a) : c.changeLevel = .mfa := by
  unfold changeLevel min
  rw [h]
  simp only [Option.getD_some]
  split
  · exact le_antisymm (by assumption) ha
  · rfl

end Acr
end Pyle