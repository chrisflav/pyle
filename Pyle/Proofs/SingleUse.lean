import Pyle.Proofs.Decisions

/-!
# Single use, as state machines

DESIGN.md §9.2: the challenge, code and refresh-token stores are state
machines, and a value that has been consumed is never accepted again, over
every sequence of operations.  The tables live in SQLite, about which nothing
can be proved in Lean; what is proved here is the property of two abstract
machines, each with a stated assumption that links it to the SQL that
implements it.

* `Table` is a consume-once table: a finite map with `add`, `update`, `take`
  and `purge`, where `take` returns a row and removes it.  It models the
  challenges, authorization codes, forward-authentication codes, invitations
  and device codes.  `Table.run_nodup`: from the empty table, no key is
  returned twice by any sequence of operations.
* `Families` is the refresh-token store, whose rotation step calls
  `Store.refreshDecision` itself.  `Families.run_rotated_nodup`: no token is
  rotated twice; `Families.run_revoked`: a revoked family stays revoked and
  never has a token again.

What the server does with a row it is handed is not modelled: that is decided
by the functions of `Pyle.Proofs.Decisions`, which are the code path.

Both machines assume what no proof can give: that values handed out are never
handed out again.  Each is 32 bytes from the system's random source.  A
challenge is stored as it is; a code, refresh token, device code, invitation
or forward-authentication code is stored as its SHA-256.  The models refuse to
add a key that has ever been added, which is the assumption that 32 random
bytes do not repeat — and, for the hashed values, that SHA-256 has no
collisions among them.
-/

namespace Pyle
namespace Proofs

/-! ## Consume-once tables -/

/-- A consume-once table with keys `κ` and rows `ν`: the rows present, and —
as a ghost, not a column — every key ever added.

**Assumption linking it to the SQL.**  Each operation below is one statement,
or one `BEGIN IMMEDIATE` transaction under the store's lock (`Store.run`,
`Store.atomically`), and so happens atomically, in some order:

* `add` is the `INSERT` of `Store.addChallengeCapped` (`challenges`),
  `Store.addCode` (`codes`), `Store.addForwardAuthCode`
  (`forward_auth_codes`), `Store.addInvitation` (`invitations`) or
  `Store.addDeviceCode` (`device_codes`); a key added once is never added
  again (see the module documentation);
* `take k (fun _ => true)` is the `DELETE … WHERE … = ? RETURNING …` of
  `Store.consumeChallenge` (`challenges`), `Store.consumeCode` (`codes`) and
  `Store.consumeForwardAuthCode` (`forward_auth_codes`), which deletes the
  row and hands it back whatever is then decided about it;
* `take k p` with `p` the rows `Store.deviceDecision` collects is
  `Store.pollDeviceCodeFor`: one `BEGIN IMMEDIATE` transaction that reads the
  `device_codes` row and deletes it if it is collected;
* `take k p` with `p` "live, its name, handle and email address free and the
  credential id unused" is `Store.redeemInvitation`: one `BEGIN IMMEDIATE` transaction
  that reads the `invitations` row, checks it, and deletes it only if every
  check passes (the account it then creates is not modelled);
* `update` is a statement that changes a row in place without deleting it:
  approving or denying a device code, or recording a poll;
* `purge` is a `DELETE … WHERE expires <= ?`, which removes rows and returns
  nothing. -/
structure Table (κ ν : Type) where
  /-- The row under each key, if there is one. -/
  rows : κ → Option ν
  /-- Whether a key has ever been added. -/
  seen : κ → Bool

/-- An operation on a consume-once table. -/
inductive Table.Op (κ ν : Type) where
  /-- Insert a row under a new key. -/
  | add (k : κ) (v : ν)
  /-- Change a row in place. -/
  | update (k : κ) (f : ν → ν)
  /-- Delete the row under `k` and return it, if it is there and `p` holds of
  it. -/
  | take (k : κ) (p : ν → Bool)
  /-- Delete every row `p` holds of. -/
  | purge (p : ν → Bool)

namespace Table

variable {κ ν : Type} [DecidableEq κ]

/-- The table with no rows, as a fresh database has it. -/
def empty : Table κ ν := ⟨fun _ => none, fun _ => false⟩

/-- One operation: the table after it, and the row it returned, if any.  An
`add` under a key added before is refused and changes nothing. -/
def step (t : Table κ ν) : Op κ ν → Table κ ν × Option (κ × ν)
  | .add k v =>
    if t.seen k then (t, none)
    else (⟨fun j => if j = k then some v else t.rows j, fun j => j = k || t.seen j⟩, none)
  | .update k f => (⟨fun j => if j = k then (t.rows j).map f else t.rows j, t.seen⟩, none)
  | .take k p =>
    match t.rows k with
    | some v =>
      if p v then (⟨fun j => if j = k then none else t.rows j, t.seen⟩, some (k, v))
      else (t, none)
    | none => (t, none)
  | .purge p => (⟨fun j => (t.rows j).filter (fun v => !p v), t.seen⟩, none)

/-- A sequence of operations: the table after it, and every row returned, in
order. -/
def run (t : Table κ ν) : List (Op κ ν) → Table κ ν × List (κ × ν)
  | [] => (t, [])
  | o :: os => ((t.step o).1.run os |>.1, (t.step o).2.toList ++ ((t.step o).1.run os).2)

/-- Every key with a row has been added. -/
def Valid (t : Table κ ν) : Prop := ∀ k, (t.rows k).isSome = true → t.seen k = true

/-- A key that may still be returned: it has a row, or has never been added. -/
def Live (t : Table κ ν) (k : κ) : Prop := (t.rows k).isSome = true ∨ t.seen k = false

omit [DecidableEq κ] in
theorem valid_empty : Valid (empty : Table κ ν) := fun _ h => by simp [empty] at h

theorem valid_step {t : Table κ ν} (ht : Valid t) (o : Op κ ν) : Valid (t.step o).1 := by
  intro j hj
  cases o with
  | add k v =>
    by_cases hk : t.seen k = true
    · simp only [step, hk, ↓reduceIte] at hj ⊢; exact ht j hj
    · simp only [step, hk, Bool.false_eq_true, ↓reduceIte] at hj ⊢
      by_cases hjk : j = k
      · simp [hjk]
      · simp only [hjk, ↓reduceIte] at hj
        simp [hjk, ht j hj]
  | update k f =>
    simp only [step] at hj ⊢
    by_cases hjk : j = k
    · subst hjk; simp only [↓reduceIte, Option.isSome_map] at hj; exact ht j hj
    · simp only [hjk, ↓reduceIte] at hj; exact ht j hj
  | take k p =>
    rcases hv : t.rows k with _ | v
    · simp only [step, hv] at hj ⊢; exact ht j hj
    · by_cases hp : p v = true
      · simp only [step, hv, hp, ↓reduceIte] at hj ⊢
        by_cases hjk : j = k
        · simp [hjk] at hj
        · simp only [hjk, ↓reduceIte] at hj; exact ht j hj
      · simp only [step, hv, hp, Bool.false_eq_true, ↓reduceIte] at hj ⊢; exact ht j hj
  | purge p =>
    simp only [step] at hj ⊢
    exact ht j (Option.isSome_filter_of_isSome hj)
where
  Option.isSome_filter_of_isSome {o : Option ν} {q : ν → Bool}
      (h : (o.filter q).isSome = true) : o.isSome = true := by
    cases o <;> simp_all

/-- No step brings a key back to life. -/
theorem live_of_step {t : Table κ ν} {o : Op κ ν} {j : κ} (h : Live (t.step o).1 j) :
    Live t j := by
  unfold Live at h ⊢
  cases o with
  | add k v =>
    simp only [step] at h
    split at h
    · exact h
    · rename_i hk
      by_cases hjk : j = k
      · subst hjk; exact .inr (by simpa using hk)
      · simpa [hjk] using h
  | update k f =>
    simp only [step] at h
    by_cases hjk : j = k
    · simpa [hjk] using h
    · simpa [hjk] using h
  | take k p =>
    simp only [step] at h
    split at h
    · split at h
      · by_cases hjk : j = k
        · simp only [hjk, ↓reduceIte] at h; simp_all
        · simpa [hjk] using h
      · exact h
    · exact h
  | purge p =>
    simp only [step] at h
    rcases h with h | h
    · exact .inl (valid_step.Option.isSome_filter_of_isSome h)
    · exact .inr h

/-- A row returned by a step was live before it and is dead after it. -/
theorem step_returned {t : Table κ ν} (ht : Valid t) {o : Op κ ν} {r : κ × ν}
    (h : (t.step o).2 = some r) : Live t r.1 ∧ ¬ Live (t.step o).1 r.1 := by
  cases o with
  | add k v => simp only [step] at h; split at h <;> cases h
  | update k f => simp only [step] at h; cases h
  | purge p => simp only [step] at h; cases h
  | take k p =>
    simp only [step] at h ⊢
    split at h
    · rename_i v hv
      split at h
      · cases h
        rename_i hp
        simp only [hp, ↓reduceIte]
        have hs := ht k (by simp [hv])
        refine ⟨.inl (by simp [hv]), ?_⟩
        simp [Live, hs]
      · cases h
    · cases h

/-- What a run returns: rows whose keys were live at the start and are dead at
the end, no key twice. -/
theorem run_returned (t : Table κ ν) (ht : Valid t) (ops : List (Op κ ν)) :
    (∀ r ∈ (t.run ops).2, Live t r.1 ∧ ¬ Live (t.run ops).1 r.1) ∧
      ((t.run ops).2.map Prod.fst).Nodup := by
  induction ops generalizing t with
  | nil => simp [run]
  | cons o os ih =>
    obtain ⟨ih1, ih2⟩ := ih (t.step o).1 (valid_step ht o)
    have dead : ∀ {j}, ¬ Live (t.step o).1 j → ¬ Live ((t.step o).1.run os).1 j := by
      intro j hj hl
      exact hj (live_after hl)
    simp only [run]
    rcases hr : (t.step o).2 with _ | r
    · simp only [Option.toList_none, List.nil_append]
      exact ⟨fun r hr' => ⟨live_of_step (ih1 r hr').1, (ih1 r hr').2⟩, ih2⟩
    · obtain ⟨h1, h2⟩ := step_returned ht hr
      simp only [Option.toList_some, List.singleton_append, List.mem_cons, List.map_cons,
        List.nodup_cons]
      refine ⟨?_, ?_, ih2⟩
      · rintro r' (rfl | hr')
        · exact ⟨h1, dead h2⟩
        · exact ⟨live_of_step (ih1 r' hr').1, (ih1 r' hr').2⟩
      · intro hm
        obtain ⟨r', hr', hk⟩ := List.mem_map.1 hm
        exact h2 (hk ▸ (ih1 r' hr').1)
where
  live_after {t : Table κ ν} {os : List (Op κ ν)} {j : κ} (h : Live (t.run os).1 j) :
      Live t j := by
    induction os generalizing t with
    | nil => exact h
    | cons o os ih => exact live_of_step (ih h)

/-- **Single use**: from the empty table, no sequence of operations returns
the same key twice — a challenge, code, invitation or device code, once
consumed, is never handed back again. -/
theorem run_nodup (ops : List (Op κ ν)) : ((empty.run ops).2.map Prod.fst).Nodup :=
  (run_returned empty valid_empty ops).2

/-- **Single use**, split at a consumption: a key returned by some run from
the empty table is returned by no run that follows it. -/
theorem run_consumed {ops : List (Op κ ν)} {k : κ} {v : ν}
    (h : (k, v) ∈ (empty.run ops).2) (later : List (Op κ ν)) (w : ν) :
    (k, w) ∉ ((empty.run ops).1.run later).2 := by
  intro hw
  have hv := ((run_returned empty valid_empty ops).1 _ h).2
  exact hv ((run_returned _ (valid_run valid_empty ops) later).1 _ hw).1
where
  valid_run {t : Table κ ν} (ht : Valid t) (os : List (Op κ ν)) : Valid (t.run os).1 := by
    induction os generalizing t with
    | nil => exact ht
    | cons o os ih => exact ih (valid_step ht o)

end Table

/-! ## Refresh-token families -/

/-- A refresh token as the model keeps it: the grant it carries and when it
was used, if it was. -/
structure Families.Token where
  /-- The grant, with the token's own expiry. -/
  grant : Store.RefreshGrant
  /-- When it was used, if it was. -/
  usedAt : Option Nat

/-- The refresh-token store: the tokens present, the revoked families, and —
as a ghost — every token ever added.

**Assumption linking it to the SQL.**  The tables are `refresh_tokens` and
`revoked_families` of migration 1; each operation is one `BEGIN IMMEDIATE`
transaction under the store's lock (`Store.atomically`), and a transaction
that raises is rolled back whole:

* `start` is `Store.startRefreshFamily`, which inserts the first token of a
  family (the model omits its check that the family is new, which only
  refuses more);
* `present` is `Store.rotateRefreshToken`: it reads the token's row, asks
  `Store.refreshDecision` — the function itself — and carries the decision
  out;
* `revoke` is the family revocation shared by `Store.rotateRefreshToken`,
  `Store.revokeRefreshFamily`, `Store.revokeUserClientFamilies`,
  `Store.addRefreshFamily` (for a family whose session has already ended)
  and the trigger `sessions_end_families` of migration 4: delete the
  family's tokens and record it in `revoked_families` with
  `INSERT OR IGNORE`;
* `purge` deletes tokens; nothing ever deletes from `revoked_families`.

Every insert into `refresh_tokens` is refused by the trigger
`refresh_tokens_not_revoked` of migration 1 when the family is revoked, and
by the assumption of the module documentation when the token's hash was
added before; in the model, as in the database, the whole operation then
changes nothing. -/
structure Families (κ : Type) where
  /-- The token under each hash, if there is one. -/
  tokens : κ → Option Families.Token
  /-- The revoked families. -/
  revoked : List ByteArray
  /-- Whether a hash has ever been added. -/
  seen : κ → Bool

/-- An operation on the refresh-token store. -/
inductive Families.Op (κ : Type) where
  /-- Issue the first token of a family. -/
  | start (k : κ) (g : Store.RefreshGrant)
  /-- Present token `old` on behalf of `clientId` at `now`, to rotate it to
  `new`, valid until `expires`. -/
  | present (old new : κ) (clientId : String) (now expires : Nat)
  /-- Revoke a family. -/
  | revoke (f : ByteArray)
  /-- Delete every token `p` holds of. -/
  | purge (p : Families.Token → Bool)

namespace Families

variable {κ : Type} [DecidableEq κ]

/-- The store with no tokens. -/
def empty : Families κ := ⟨fun _ => none, [], fun _ => false⟩

/-- The row `Store.rotateRefreshToken` reads for a token. -/
def row (s : Families κ) (k : κ) : Option Store.RefreshRow :=
  (s.tokens k).map fun t => ⟨t.grant, t.usedAt, decide (t.grant.family ∈ s.revoked)⟩

/-- Revoke family `f`: delete its tokens and record it. -/
def revokeFamily (s : Families κ) (f : ByteArray) : Families κ :=
  ⟨fun j => (s.tokens j).filter (fun t => !decide (t.grant.family = f)), f :: s.revoked, s.seen⟩

/-- Insert a token, unless the trigger or a repeated hash refuses it. -/
def insert (s : Families κ) (k : κ) (t : Token) : Option (Families κ) :=
  if s.seen k ∨ t.grant.family ∈ s.revoked then none
  else some ⟨fun j => if j = k then some t else s.tokens j, s.revoked,
    fun j => j = k || s.seen j⟩

/-- One operation: the store after it, and, for a presentation, the token
presented and the outcome reported. -/
def step (s : Families κ) : Op κ → Families κ × Option (κ × Store.RefreshOutcome)
  | .start k g => ((s.insert k ⟨g, none⟩).getD s, none)
  | .present old new clientId now expires =>
    match Store.refreshDecision (s.row old) clientId now expires with
    | .rotate g =>
      let used : Families κ := ⟨fun j => if j = old then (s.tokens j).map
        ({ · with usedAt := some now }) else s.tokens j, s.revoked, s.seen⟩
      match used.insert new ⟨g, none⟩ with
      | some s' => (s', some (old, .rotated g))
      | none => (s, none)
    | .revoke f => (s.revokeFamily f, some (old, .reused))
    | .invalid => (s, some (old, .invalid))
  | .revoke f => (s.revokeFamily f, none)
  | .purge p => (⟨fun j => (s.tokens j).filter (fun t => !p t), s.revoked, s.seen⟩, none)

/-- A sequence of operations: the store after it, and every presentation's
outcome, in order. -/
def run (s : Families κ) : List (Op κ) → Families κ × List (κ × Store.RefreshOutcome)
  | [] => (s, [])
  | o :: os => (((s.step o).1.run os).1, (s.step o).2.toList ++ ((s.step o).1.run os).2)

/-- The invariant: every token present has been added, and none is of a
revoked family. -/
def Valid (s : Families κ) : Prop :=
  ∀ k t, s.tokens k = some t → s.seen k = true ∧ t.grant.family ∉ s.revoked

/-- A token that may still be rotated: present and unused, or never added. -/
def Live (s : Families κ) (k : κ) : Prop :=
  (∃ t, s.tokens k = some t ∧ t.usedAt = none) ∨ s.seen k = false

/-- Whether an outcome is a rotation. -/
def isRotated : Store.RefreshOutcome → Bool
  | .rotated _ => true
  | _ => false

omit [DecidableEq κ] in
theorem valid_empty : Valid (empty : Families κ) := fun _ _ h => by simp [empty] at h

omit [DecidableEq κ] in
theorem valid_revokeFamily {s : Families κ} (hs : Valid s) (f : ByteArray) :
    Valid (s.revokeFamily f) := by
  intro k t h
  simp only [revokeFamily, Option.filter_eq_some_iff, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at h
  obtain ⟨h, hf⟩ := h
  obtain ⟨h1, h2⟩ := hs k t h
  refine ⟨h1, ?_⟩
  simp only [revokeFamily, List.mem_cons, not_or]
  exact ⟨hf, h2⟩

theorem valid_insert {s s' : Families κ} {k : κ} {t : Token} (hs : Valid s)
    (h : s.insert k t = some s') : Valid s' := by
  simp only [insert] at h
  split at h
  · cases h
  rename_i hn
  cases h
  simp only [not_or, Bool.not_eq_true] at hn
  intro j u hj
  by_cases hjk : j = k
  · subst hjk
    simp only [↓reduceIte, Option.some.injEq] at hj
    subst hj
    simp [hn.2]
  · simp only [hjk, ↓reduceIte] at hj
    obtain ⟨h1, h2⟩ := hs j u hj
    simp [hjk, h1, h2]

theorem valid_step {s : Families κ} (hs : Valid s) (o : Op κ) : Valid (s.step o).1 := by
  cases o with
  | start k g =>
    simp only [step]
    rcases h : s.insert k ⟨g, none⟩ with _ | s'
    · exact hs
    · exact valid_insert hs h
  | present old new clientId now expires =>
    simp only [step]
    split
    · split
      · rename_i s' h
        refine valid_insert ?_ h
        intro j u hj
        by_cases hjo : j = old
        · subst hjo
          simp only [↓reduceIte, Option.map_eq_some_iff] at hj
          obtain ⟨u', hu', rfl⟩ := hj
          exact hs j u' hu'
        · simp only [hjo, ↓reduceIte] at hj
          exact hs j u hj
      · exact hs
    · exact valid_revokeFamily hs _
    · exact hs
  | revoke f => exact valid_revokeFamily hs f
  | purge p =>
    intro k t h
    simp only [step, Option.filter_eq_some_iff] at h
    exact hs k t h.1

/-- No step makes a token rotatable again. -/
theorem live_of_step {s : Families κ} {o : Op κ} {j : κ} (h : Live (s.step o).1 j) :
    Live s j := by
  have ins : ∀ {s s' : Families κ} {k : κ} {t : Token}, s.insert k t = some s' →
      t.usedAt = none → Live s' j → Live s j := by
    intro s s' k t hi htu hl
    simp only [insert] at hi
    split at hi
    · cases hi
    rename_i hn
    cases hi
    simp only [not_or, Bool.not_eq_true] at hn
    by_cases hjk : j = k
    · subst hjk; exact .inr hn.1
    · simpa [Live, hjk] using hl
  cases o with
  | start k g =>
    simp only [step] at h
    rcases hi : s.insert k ⟨g, none⟩ with _ | s'
    · rw [hi] at h; exact h
    · rw [hi] at h; exact ins hi rfl h
  | present old new clientId now expires =>
    simp only [step] at h
    split at h
    · split at h
      · rename_i s' hi
        have h' := ins hi rfl h
        by_cases hjo : j = old
        · subst hjo
          rcases h' with ⟨u, hu, hn⟩ | hn
          · simp at hu; obtain ⟨u', -, rfl⟩ := hu; cases hn
          · exact .inr hn
        · simpa [Live, hjo] using h'
      · exact h
    · rcases h with ⟨u, hu, hn⟩ | hn
      · simp only [revokeFamily, Option.filter_eq_some_iff] at hu
        exact .inl ⟨u, hu.1, hn⟩
      · exact .inr hn
    · exact h
  | revoke f =>
    rcases h with ⟨u, hu, hn⟩ | hn
    · simp only [step, revokeFamily, Option.filter_eq_some_iff] at hu
      exact .inl ⟨u, hu.1, hn⟩
    · exact .inr hn
  | purge p =>
    rcases h with ⟨u, hu, hn⟩ | hn
    · simp only [step, Option.filter_eq_some_iff] at hu
      exact .inl ⟨u, hu.1, hn⟩
    · exact .inr hn

/-- A rotation by a step was of a live token, which is dead after it. -/
theorem step_rotated {s : Families κ} (hs : Valid s) {o : Op κ} {k : κ}
    {out : Store.RefreshOutcome} (h : (s.step o).2 = some (k, out)) (hr : isRotated out = true) :
    Live s k ∧ ¬ Live (s.step o).1 k := by
  cases o with
  | start => simp [step] at h
  | revoke => simp [step] at h
  | purge => simp [step] at h
  | present old new clientId now expires =>
    rcases hd : Store.refreshDecision (s.row old) clientId now expires with g | f | _
    · obtain ⟨r, hrow, -, hu, -, -, -⟩ := Proofs.refreshDecision_rotate hd
      simp only [row, Option.map_eq_some_iff] at hrow
      obtain ⟨t, ht, rfl⟩ := hrow
      rcases hi : (⟨fun j => if j = old then (s.tokens j).map ({ · with usedAt := some now })
          else s.tokens j, s.revoked, s.seen⟩ : Families κ).insert new ⟨g, none⟩ with _ | s'
      · simp [step, hd, hi] at h
      · simp only [step, hd, hi, Option.some.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, -⟩ := h
        refine ⟨.inl ⟨t, ht, hu⟩, ?_⟩
        simp only [insert] at hi
        split at hi
        · cases hi
        rename_i hn
        cases hi
        simp only [not_or, Bool.not_eq_true] at hn
        have hko : old ≠ new := by
          rintro rfl
          simp [(hs old t ht).1] at hn
        rintro (⟨u, hu', hn'⟩ | hn')
        · simp only [hko, ↓reduceIte, ht, Option.map_some, Option.some.injEq] at hu'
          subst hu'
          cases hn'
        · simp only [hko, decide_false, Bool.false_or] at hn'
          simp [(hs old t ht).1] at hn'
    · simp only [step, hd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [isRotated] at hr
    · simp only [step, hd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [isRotated] at hr

/-- The rotations of a run: tokens live at its start and dead at its end, no
token twice. -/
theorem run_rotated (s : Families κ) (hs : Valid s) (ops : List (Op κ)) :
    (∀ r ∈ (s.run ops).2, isRotated r.2 = true → Live s r.1 ∧ ¬ Live (s.run ops).1 r.1) ∧
      (((s.run ops).2.filter (isRotated ·.2)).map Prod.fst).Nodup := by
  induction ops generalizing s with
  | nil => simp [run]
  | cons o os ih =>
    obtain ⟨ih1, ih2⟩ := ih (s.step o).1 (valid_step hs o)
    simp only [run]
    rcases hr : (s.step o).2 with _ | ⟨k, out⟩
    · simp only [Option.toList_none, List.nil_append]
      exact ⟨fun r hr' hrot => ⟨live_of_step (ih1 r hr' hrot).1, (ih1 r hr' hrot).2⟩, ih2⟩
    · simp only [Option.toList_some, List.singleton_append, List.mem_cons]
      refine ⟨?_, ?_⟩
      · rintro r (rfl | hr') hrot
        · obtain ⟨h1, h2⟩ := step_rotated hs hr hrot
          exact ⟨h1, fun hl => h2 (live_after hl)⟩
        · exact ⟨live_of_step (ih1 r hr' hrot).1, (ih1 r hr' hrot).2⟩
      · by_cases hrot : isRotated out = true
        · simp only [List.filter_cons, hrot, ↓reduceIte, List.map_cons, List.nodup_cons]
          refine ⟨?_, ih2⟩
          intro hm
          obtain ⟨r', hr', hk⟩ := List.mem_map.1 hm
          obtain ⟨hr'1, hr'2⟩ := List.mem_filter.1 hr'
          exact (step_rotated hs hr hrot).2 (hk ▸ (ih1 r' hr'1 hr'2).1)
        · simp only [List.filter_cons, hrot, Bool.false_eq_true, ↓reduceIte]
          exact ih2
where
  live_after {s : Families κ} {os : List (Op κ)} {j : κ} (h : Live (s.run os).1 j) :
      Live s j := by
    induction os generalizing s with
    | nil => exact h
    | cons o os ih => exact live_of_step (ih h)

/-- **Single use of refresh tokens**: from the empty store, no sequence of
operations rotates the same token twice. -/
theorem run_rotated_nodup (ops : List (Op κ)) :
    (((empty.run ops).2.filter (isRotated ·.2)).map Prod.fst).Nodup :=
  (run_rotated empty valid_empty ops).2

/-- **Reuse**: presenting, on behalf of its client, a token that has been used
revokes its family and reports `reused`. -/
theorem step_reused {s : Families κ} {k new : κ} {t : Token} {now expires : Nat}
    (ht : s.tokens k = some t) (hu : t.usedAt.isSome = true) :
    s.step (.present k new t.grant.clientId now expires) =
      (s.revokeFamily t.grant.family, some (k, .reused)) := by
  have : s.row k = some ⟨t.grant, t.usedAt, decide (t.grant.family ∈ s.revoked)⟩ := by
    simp [row, ht]
  rw [step, this, Proofs.refreshDecision_reused (r := ⟨t.grant, t.usedAt, _⟩) rfl hu]

omit [DecidableEq κ] in
/-- After a family is revoked, none of its tokens remains. -/
theorem revokeFamily_tokens (s : Families κ) (f : ByteArray) (k : κ) (t : Token)
    (h : (s.revokeFamily f).tokens k = some t) : t.grant.family ≠ f := by
  simp only [revokeFamily, Option.filter_eq_some_iff, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at h
  exact h.2

/-- A step never forgets a revoked family, and never rotates into one. -/
theorem step_revoked {s : Families κ} {f : ByteArray} (hf : f ∈ s.revoked) (o : Op κ) :
    f ∈ (s.step o).1.revoked ∧ ∀ k g, (s.step o).2 = some (k, .rotated g) → g.family ≠ f := by
  have ins : ∀ {s s' : Families κ} {k : κ} {t : Token}, s.insert k t = some s' →
      s'.revoked = s.revoked ∧ t.grant.family ∉ s.revoked := by
    intro s s' k t hi
    simp only [insert] at hi
    split at hi
    · cases hi
    rename_i hn
    cases hi
    simp only [not_or] at hn
    exact ⟨rfl, hn.2⟩
  cases o with
  | start k g =>
    refine ⟨?_, by simp [step]⟩
    simp only [step]
    rcases hi : s.insert k ⟨g, none⟩ with _ | s'
    · exact hf
    · simpa [(ins hi).1] using hf
  | present old new clientId now expires =>
    rcases hd : Store.refreshDecision (s.row old) clientId now expires with g | f' | _
    · rcases hi : (⟨fun j => if j = old then (s.tokens j).map ({ · with usedAt := some now })
          else s.tokens j, s.revoked, s.seen⟩ : Families κ).insert new ⟨g, none⟩ with _ | s'
      · simp [step, hd, hi, hf]
      · simp only [step, hd, hi, Option.some.injEq, Prod.mk.injEq,
          Store.RefreshOutcome.rotated.injEq]
        obtain ⟨h1, h2⟩ := ins hi
        refine ⟨by simpa [h1] using hf, ?_⟩
        rintro k g' ⟨-, rfl⟩ rfl
        exact h2 hf
    · simp [step, hd, revokeFamily, hf]
    · simp [step, hd, hf]
  | revoke f' => simp [step, revokeFamily, hf]
  | purge p => simp [step, hf]

/-- **A revoked family accepts no new member**: once a family is revoked, it
stays revoked, no token of it is ever present again, and no presentation is
ever rotated into it. -/
theorem run_revoked {s : Families κ} (hs : Valid s) {f : ByteArray} (hf : f ∈ s.revoked)
    (ops : List (Op κ)) :
    f ∈ (s.run ops).1.revoked ∧ (∀ k t, (s.run ops).1.tokens k = some t → t.grant.family ≠ f) ∧
      ∀ k g, (k, .rotated g) ∈ (s.run ops).2 → g.family ≠ f := by
  induction ops generalizing s with
  | nil =>
    refine ⟨hf, fun k t h hft => (hs k t h).2 (hft ▸ hf), by simp [run]⟩
  | cons o os ih =>
    obtain ⟨h1, h2⟩ := step_revoked hf o
    obtain ⟨ih1, ih2, ih3⟩ := ih (valid_step hs o) h1
    refine ⟨ih1, ih2, ?_⟩
    intro k g hm
    simp only [run, List.mem_append] at hm
    rcases hm with hm | hm
    · rcases hr : (s.step o).2 with _ | r
      · simp [hr] at hm
      · simp only [hr, Option.toList_some, List.mem_singleton] at hm
        exact h2 k g (hm ▸ hr)
    · exact ih3 k g hm

end Families

end Proofs
end Pyle