import Pyle.Oidc.Token

/-!
# What the consume-once decisions guarantee

The token endpoint, the device grant and the WebAuthn ceremonies each hand
the row the store deleted or read to a pure function that decides what
happens: `Oidc.codeDecision`, `Store.refreshDecision`, `Store.deviceDecision`
and `Store.challengeDecision`, together with `Store.Challenge.admits`; and
`Policy.checkTotp` hands an account's authenticator apps to
`Factor.Totp.verifyAny`.  These
functions are the code path — the store and the handlers do nothing but read
the row, call them, and carry out what they return — so what is proved here
of them is what the server does with a row (DESIGN.md §9.2, §9.4).

That a row, once consumed, is never handed to them again is the business of
the state-machine models of `Pyle.Proofs.SingleUse`.
-/

namespace Pyle
namespace Proofs

open Store

/-! ## Authorization codes (§9.4) -/

/-- **Authorization codes**: tokens are issued for a code only if the store
handed back its row, it was issued to the client exchanging it, for the
`redirect_uri` of the request, the code verifier is well formed and hashes to
its `S256` challenge, and it has not expired. -/
theorem codeDecision_issue {row : Option AuthCode} {clientId redirectUri verifier : String}
    {now : Nat} {a : AuthCode}
    (h : Oidc.codeDecision row clientId redirectUri verifier now = .issue a) :
    row = some a ∧ a.clientId = clientId ∧ a.redirectUri = redirectUri ∧
      Oidc.Pkce.validVerifier verifier = true ∧ Oidc.Pkce.s256 verifier = a.codeChallenge ∧
      now < a.expires := by
  unfold Oidc.codeDecision at h
  rcases row with _ | b
  · cases h
  · dsimp only at h
    split at h
    · cases h
    rename_i hexp
    split at h
    · cases h
    rename_i hbind
    split at h
    · cases h
    rename_i hpkce
    cases h
    simp only [not_or, Decidable.not_not] at hexp hbind
    simp only [Oidc.Pkce.verifies, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_false] at hpkce
    exact ⟨rfl, hbind.1, hbind.2, hpkce.1, hpkce.2, hexp⟩

/-- A code the store did not hand back — unknown, or consumed before — is
unusable. -/
theorem codeDecision_none (clientId redirectUri verifier : String) (now : Nat) :
    Oidc.codeDecision none clientId redirectUri verifier now = .unusable := rfl

/-! ## Refresh tokens (§5.1, §9.2) -/

/-- A refresh token is rotated only if it is this client's, has not been used,
has not expired, and its family has not been revoked; the successor carries
its grant with the new expiry. -/
theorem refreshDecision_rotate {row : Option RefreshRow} {clientId : String}
    {now expires : Nat} {g : RefreshGrant}
    (h : refreshDecision row clientId now expires = .rotate g) :
    ∃ r, row = some r ∧ r.grant.clientId = clientId ∧ r.usedAt = none ∧
      r.familyRevoked = false ∧ now < r.grant.expires ∧ g = { r.grant with expires } := by
  unfold refreshDecision at h
  rcases row with _ | r
  · cases h
  · dsimp only at h
    split at h
    · cases h
    rename_i hc
    split at h
    · cases h
    rename_i hu
    split at h
    · cases h
    rename_i hv
    cases h
    simp only [Decidable.not_not] at hc
    simp only [not_or, Decidable.not_not, Bool.not_eq_true] at hv
    simp only [Option.isSome_iff_ne_none, Decidable.not_not] at hu
    exact ⟨r, rfl, hc, hu, hv.1, hv.2, rfl⟩

/-- **Reuse**: a refresh token of this client that was used before revokes its
family — whether or not it has expired since, and whether or not the family
is revoked already — and is never rotated. -/
theorem refreshDecision_reused {r : RefreshRow} {clientId : String} {now expires : Nat}
    (hc : r.grant.clientId = clientId) (hu : r.usedAt.isSome = true) :
    refreshDecision (some r) clientId now expires = .revoke r.grant.family := by
  simp [refreshDecision, hc, hu]

/-- A token whose family has been revoked is never rotated. -/
theorem refreshDecision_revoked {r : RefreshRow} {clientId : String} {now expires : Nat}
    (hr : r.familyRevoked = true) (g : RefreshGrant) :
    refreshDecision (some r) clientId now expires ≠ .rotate g := by
  intro h
  obtain ⟨r', hr', -, -, hf, -⟩ := refreshDecision_rotate h
  cases hr'
  simp [hr] at hf

/-- A token presented by another client changes nothing: it neither rotates
nor revokes. -/
theorem refreshDecision_otherClient {r : RefreshRow} {clientId : String} {now expires : Nat}
    (hc : r.grant.clientId ≠ clientId) :
    refreshDecision (some r) clientId now expires = .invalid := by
  simp [refreshDecision, hc]

/-- Only a used token revokes, and only its own family. -/
theorem refreshDecision_revoke {row : Option RefreshRow} {clientId : String}
    {now expires : Nat} {f : ByteArray}
    (h : refreshDecision row clientId now expires = .revoke f) :
    ∃ r, row = some r ∧ r.grant.clientId = clientId ∧ r.usedAt.isSome = true ∧
      f = r.grant.family := by
  unfold refreshDecision at h
  rcases row with _ | r
  · cases h
  · dsimp only at h
    split at h
    · cases h
    rename_i hc
    split at h
    · cases h
      simp only [Decidable.not_not] at hc
      rename_i hu
      exact ⟨r, rfl, hc, hu, rfl⟩
    split at h <;> cases h

/-! ## Device codes (RFC 8628) -/

/-- A device code yields an approval only for the client it was issued to,
before it expires, once a user has approved it; the approval names that user
and the client. -/
theorem deviceDecision_approved {row : Option DeviceRow} {clientId : String} {now : Nat}
    {cid scope : String} {user : UserId} {amr : List String} {authTime : Nat}
    (h : deviceDecision row clientId now = .collect (.approved cid scope user amr authTime)) :
    ∃ r, row = some r ∧ r.clientId = clientId ∧ cid = clientId ∧ now < r.expires ∧
      r.status = "approved" ∧ r.user = some user ∧ r.authTime = some authTime ∧
      r.scope = scope ∧ r.amr = amr := by
  unfold deviceDecision at h
  rcases row with _ | r
  · cases h
  · dsimp only at h
    split at h
    · cases h
    rename_i hc
    split at h
    · cases h
    rename_i hx
    simp only [Decidable.not_not] at hc hx
    split at h
    · rename_i st u t hs hu ht
      cases h
      exact ⟨r, rfl, hc, hc, hx, hs, hu, ht, rfl, rfl⟩
    all_goals first | cases h | (split at h <;> cases h)

/-- A device code is collected — deleted, with an outcome — only by the
client it was issued to, and before it expires. -/
theorem deviceDecision_collect {row : Option DeviceRow} {clientId : String} {now : Nat}
    {o : DevicePoll} (h : deviceDecision row clientId now = .collect o) :
    ∃ r, row = some r ∧ r.clientId = clientId ∧ now < r.expires := by
  unfold deviceDecision at h
  rcases row with _ | r
  · cases h
  · dsimp only at h
    split at h
    · cases h
    rename_i hc
    split at h
    · cases h
    rename_i hx
    simp only [Decidable.not_not] at hc hx
    exact ⟨r, rfl, hc, hx⟩

/-- A poll by another client changes nothing and learns nothing about the
code's state. -/
theorem deviceDecision_otherClient {r : DeviceRow} {clientId : String} {now : Nat}
    (hc : r.clientId ≠ clientId) : deviceDecision (some r) clientId now = .otherClient := by
  simp [deviceDecision, hc]

/-- A device code the store no longer has yields nothing. -/
theorem deviceDecision_none (clientId : String) (now : Nat) :
    deviceDecision none clientId now = .expired := rfl

/-! ## WebAuthn challenges -/

/-- A consumed challenge is accepted only if the store handed back its row, it
was issued for this purpose, and it has not expired; what comes back is that
row. -/
theorem challengeDecision_some {value : ByteArray} {purpose : ChallengePurpose} {now : Nat}
    {row : Option ChallengeRow} {ch : Challenge}
    (h : challengeDecision value purpose now row = some ch) :
    ∃ r, row = some r ∧ r.purpose = purpose.toString ∧ now < r.expires ∧
      ch.value = value ∧ ch.purpose = purpose ∧ ch.expires = r.expires ∧
      ch.user = r.user.map (⟨·⟩) := by
  rcases row with _ | r
  · cases h
  · simp only [challengeDecision] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      exact ⟨r, rfl, hc.1, hc.2, rfl, rfl, rfl, rfl⟩
    · cases h

/-- A challenge the store did not hand back — unknown, or consumed before —
is refused. -/
theorem challengeDecision_none (value : ByteArray) (purpose : ChallengePurpose) (now : Nat) :
    challengeDecision value purpose now none = none := rfl

/-- A challenge issued to a user admits only that user's credentials. -/
theorem Challenge.admits_user {ch : Challenge} {u v : UserId} (hu : ch.user = some u)
    (h : ch.admits v = true) : u = v := by
  simpa [Challenge.admits, hu] using h

/-! ## TOTP codes across several apps (§9 property 5)

`Policy.checkTotp` hands the account's apps — id, opened secret and last
accepted step — to `Factor.Totp.verifyAny`, and stores only what it returns:
the step, for that app, by `Store.acceptTotpStep`, which applies only if the
step is later than the one the app has stored.  The account's lock is checked
first and a failure counts once, whatever the number of apps. -/

/-- A code is accepted only for one of the apps it was checked against, for a
step that code verifies for with that app's secret and last step. -/
theorem verifyAny_mem {α : Type} {apps : List (α × ByteArray × Option Nat)} {t : Nat}
    {c : String} {a : α} {n : Nat} (h : Factor.Totp.verifyAny apps t c = some (a, n)) :
    ∃ secret lastStep, (a, secret, lastStep) ∈ apps ∧
      Factor.Totp.verify secret t c lastStep = some n := by
  unfold Factor.Totp.verifyAny at h
  obtain ⟨⟨id, secret, lastStep⟩, hm, hv⟩ := List.exists_of_findSome?_eq_some h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hv
  obtain ⟨m, hm', rfl, rfl⟩ := hv
  exact ⟨secret, lastStep, hm, hm'⟩

/-- **Replay, per app**: a code accepted for an app is for a step later than
the last one that app accepted.  Once the store records that step, the same
code — or any code for that step or an earlier one — is never accepted for
that app again. -/
theorem verifyAny_increasing {α : Type} {apps : List (α × ByteArray × Option Nat)} {t : Nat}
    {c : String} {a : α} {n : Nat} (h : Factor.Totp.verifyAny apps t c = some (a, n)) :
    ∃ secret lastStep, (a, secret, lastStep) ∈ apps ∧ ∀ l, lastStep = some l → l < n := by
  obtain ⟨secret, lastStep, hm, hv⟩ := verifyAny_mem h
  refine ⟨secret, lastStep, hm, fun l hl => ?_⟩
  subst hl
  exact Factor.Totp.verify_increasing hv

/-- The apps after the store recorded step `n` for app `a`, as
`Store.acceptTotpStep` does: that app's last step becomes `n`, and no other
app changes. -/
def acceptStep {α : Type} [DecidableEq α] (apps : List (α × ByteArray × Option Nat)) (a : α)
    (n : Nat) : List (α × ByteArray × Option Nat) :=
  apps.map fun (id, secret, lastStep) => if id = a then (id, secret, some n) else (id, secret, lastStep)

/-- **A code is good once per app**: once step `n` is recorded for app `a`,
every code later accepted for `a` is for a step after `n` — the code that was
just accepted, sent again, is not, whatever the other apps hold. -/
theorem verifyAny_acceptStep {α : Type} [DecidableEq α] {apps : List (α × ByteArray × Option Nat)}
    {a : α} {n t : Nat} {c : String} {m : Nat}
    (h : Factor.Totp.verifyAny (acceptStep apps a n) t c = some (a, m)) : n < m := by
  obtain ⟨secret, lastStep, hm, hv⟩ := verifyAny_mem h
  unfold acceptStep at hm
  obtain ⟨⟨id, s, l⟩, -, he⟩ := List.mem_map.mp hm
  by_cases hid : id = a
  · simp only [hid, if_true, Prod.mk.injEq] at he
    obtain ⟨-, -, rfl⟩ := he
    exact Factor.Totp.verify_increasing hv
  · simp only [hid, if_false, Prod.mk.injEq] at he
    exact he.1.elim

/-- Recording a step for one app leaves what every other app accepts as it
was. -/
theorem acceptStep_other {α : Type} [DecidableEq α] {apps : List (α × ByteArray × Option Nat)}
    {a b : α} {n : Nat} {secret : ByteArray} {lastStep : Option Nat} (hb : b ≠ a)
    (h : (b, secret, lastStep) ∈ apps) : (b, secret, lastStep) ∈ acceptStep apps a n := by
  unfold acceptStep
  exact List.mem_map.mpr ⟨(b, secret, lastStep), h, by simp [hb]⟩

/-- The step a code is accepted for is within one step of the current time,
whichever app accepted it. -/
theorem verifyAny_near {α : Type} {apps : List (α × ByteArray × Option Nat)} {t : Nat}
    {c : String} {a : α} {n : Nat} (h : Factor.Totp.verifyAny apps t c = some (a, n)) :
    n = Factor.Totp.stepOf t - 1 ∨ n = Factor.Totp.stepOf t ∨ n = Factor.Totp.stepOf t + 1 := by
  obtain ⟨_, _, _, hv⟩ := verifyAny_mem h
  exact Factor.Totp.verify_near hv

/-- No apps, no code accepted. -/
theorem verifyAny_nil {α : Type} (t : Nat) (c : String) :
    Factor.Totp.verifyAny ([] : List (α × ByteArray × Option Nat)) t c = none := rfl

end Proofs
end Pyle