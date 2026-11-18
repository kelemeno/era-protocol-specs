import EraSpec.Contracts.L1NativeTokenVault.Specs.BulkheadIsolation

/-!
# Step lemmas for the bulkhead model

Closed forms of every successful `capStep`: each call succeeds exactly when its guards hold, and
its successor is then the stated `…Post` state.  The proofs of
`EraSpec.Contracts.L1NativeTokenVault.Properties.BulkheadIsolation` use these instead of unfolding
the transcription again.  Nothing here is a property statement.
-/

namespace Contracts.L1NativeTokenVault.Bulkhead

/-! ## Small helpers -/

theorem capIte_pos {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem capIte_neg {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem capNone_iff {α : Type} {t : α} {P : Prop} (h : ¬P) : ((none : Option α) = some t) ↔ P :=
  ⟨fun h' => absurd h' (by simp), fun hp => absurd hp h⟩

theorem capSome_iff {α : Type} {t u : α} {P : Prop} (hP : P) : (some u = some t) ↔ (P ∧ t = u) :=
  ⟨fun h => ⟨hP, (Option.some.inj h).symm⟩, fun ⟨_, h⟩ => by rw [h]⟩

@[simp] theorem capUpd2_apply {β : Type} (f : ℕ → ℕ → β) (k a : ℕ) (v : β) (k' a' : ℕ) :
    capUpd2 f k a v k' a' = if k' = k ∧ a' = a then v else f k' a' := by
  unfold capUpd2
  by_cases hk : k' = k
  · subst hk
    by_cases ha : a' = a
    · subst ha; simp
    · simp [ha]
  · simp [hk]

/-- `f[k][a] += x` when the key is `some k`, nothing when it is `none`. -/
def capBump (f : ℕ → ℕ → ℕ) : Option ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | none, _, _ => f
  | some k, a, x => capUpd2 f k a (f k a + x)

@[simp] theorem capBump_none (f : ℕ → ℕ → ℕ) (a x : ℕ) : capBump f none a x = f := rfl

@[simp] theorem capBump_some (f : ℕ → ℕ → ℕ) (k a x : ℕ) :
    capBump f (some k) a x = capUpd2 f k a (f k a + x) := rfl

theorem capBump_apply (f : ℕ → ℕ → ℕ) (o : Option ℕ) (a x k' a' : ℕ) :
    capBump f o a x k' a' = f k' a' + (if o = some k' ∧ a' = a then x else 0) := by
  cases o with
  | none => simp
  | some k =>
    simp only [capBump_some, capUpd2_apply, Option.some.injEq]
    by_cases h : k' = k ∧ a' = a
    · obtain ⟨rfl, rfl⟩ := h; simp
    · have h' : ¬(k = k' ∧ a' = a) := fun ⟨h1, h2⟩ => h ⟨h1.symm, h2⟩
      simp [h, h']

theorem capBump_ge (f : ℕ → ℕ → ℕ) (o : Option ℕ) (a x k' a' : ℕ) :
    f k' a' ≤ capBump f o a x k' a' := by
  rw [capBump_apply]; omega

/-! ## Closed forms of the successors -/

/-- The successor of a successful `toChain c a x`. -/
def toChainPost (cfg : CapConfig) (s : CapState) (c a x : ℕ) : CapState :=
  { s with
    bridgedOut := if s.origin a = cfg.l1 then Function.update s.bridgedOut a (s.bridgedOut a + x)
      else s.bridgedOut
    deposited := capBump s.deposited (capTrackedKey cfg s c (s.origin a)) a x }

/-- The successor of a successful `fromChain c a x`. -/
def fromChainPost (cfg : CapConfig) (s : CapState) (c a x : ℕ) : CapState :=
  { s with
    bridgedOut := if s.origin a = cfg.l1 then Function.update s.bridgedOut a (s.bridgedOut a - x)
      else s.bridgedOut
    withdrawn := capBump s.withdrawn (capTrackedKey cfg s c (s.origin a)) a x }

/-- What a backfill entry adds to the pool for a chain already in it (`L1NTV:233-234`). -/
def setBackfillCredit (s : CapState) (c a v : ℕ) : ℕ :=
  (s.deposited c a + v - s.withdrawn c a) - (s.deposited c a - s.withdrawn c a)

/-- The successor of a successful `setBackfill c a v`. -/
def setBackfillPost (cfg : CapConfig) (s : CapState) (c a v : ℕ) : CapState :=
  { s with
    deposited := if s.inPool c a = true then
        capUpd2 s.deposited cfg.pool a (s.deposited cfg.pool a + setBackfillCredit s c a v)
      else s.deposited
    backfill := capUpd2 s.backfill c a v }

/-- What a move adds to the pool (`L1NTV:254`). -/
def moveCredit (s : CapState) (c a : ℕ) : ℕ :=
  s.deposited c a + s.backfill c a - s.withdrawn c a

/-- The successor of a successful `moveToPool c a`. -/
def movePost (cfg : CapConfig) (s : CapState) (c a : ℕ) : CapState :=
  { s with
    inPool := capUpd2 s.inPool c a true
    deposited := capUpd2 s.deposited cfg.pool a (s.deposited cfg.pool a + moveCredit s c a) }

/-- The guards of the tracked branch of `_handleBridgeFromChain` for key `k`. -/
def capWithdrawalAllowed (s : CapState) (k a x : ℕ) : Prop :=
  s.withdrawn k a + x < capWordBound ∧
    (s.pending k = false → s.deposited k a + s.backfill k a < capWordBound ∧
      s.withdrawn k a + x ≤ s.deposited k a + s.backfill k a)

/-! ## The characterizations -/

theorem capStep_toChain {cfg : CapConfig} {s t : CapState} {c a x : ℕ} :
    capStep cfg (.toChain c a x) s = some t ↔
      (s.registered c = true ∧ x < capWordBound ∧
        (s.origin a = cfg.l1 → s.bridgedOut a + x < capWordBound) ∧
        (∀ k, capTrackedKey cfg s c (s.origin a) = some k → s.deposited k a + x < capWordBound)) ∧
      t = toChainPost cfg s c a x := by
  simp only [capStep, capHandleToChain, toChainPost]
  by_cases hg : s.registered c = true ∧ x < capWordBound
  · rw [capIte_pos hg]
    rcases hk : capTrackedKey cfg s c (s.origin a) with _ | k
    · by_cases ho : s.origin a = cfg.l1
      · rw [capIte_pos ho, capIte_pos ho]
        unfold capCreditBridgedOut
        by_cases hb : s.bridgedOut a + x < capWordBound
        · rw [capIte_pos hb]
          simp only [capBump_none]
          exact capSome_iff ⟨hg.1, hg.2, fun _ => hb, fun k hk' => by cases hk'⟩
        · rw [capIte_neg hb]
          exact capNone_iff (by rintro ⟨⟨-, -, h, -⟩, -⟩; exact hb (h ho))
      · rw [capIte_neg ho, capIte_neg ho]
        simp only [capBump_none]
        exact capSome_iff ⟨hg.1, hg.2, fun h => absurd h ho, fun k hk' => by cases hk'⟩
    · by_cases ho : s.origin a = cfg.l1
      · rw [capIte_pos ho, capIte_pos ho]
        unfold capCreditBridgedOut
        by_cases hb : s.bridgedOut a + x < capWordBound
        · rw [capIte_pos hb]
          simp only [capCreditDeposited, capBump_some]
          by_cases hd : s.deposited k a + x < capWordBound
          · rw [capIte_pos hd]
            exact capSome_iff ⟨hg.1, hg.2, fun _ => hb, fun k' hk' => by cases hk'; exact hd⟩
          · rw [capIte_neg hd]
            exact capNone_iff (by rintro ⟨⟨-, -, -, h⟩, -⟩; exact hd (h k rfl))
        · rw [capIte_neg hb]
          exact capNone_iff (by rintro ⟨⟨-, -, h, -⟩, -⟩; exact hb (h ho))
      · rw [capIte_neg ho, capIte_neg ho]
        simp only [capCreditDeposited, capBump_some]
        by_cases hd : s.deposited k a + x < capWordBound
        · rw [capIte_pos hd]
          exact capSome_iff ⟨hg.1, hg.2, fun h => absurd h ho, fun k' hk' => by cases hk'; exact hd⟩
        · rw [capIte_neg hd]
          exact capNone_iff (by rintro ⟨⟨-, -, -, h⟩, -⟩; exact hd (h k rfl))
  · rw [capIte_neg hg]
    exact capNone_iff (by rintro ⟨⟨h1, h2, -, -⟩, -⟩; exact hg ⟨h1, h2⟩)

theorem capRecordWithdrawal_eq {s t : CapState} {k a x : ℕ} :
    capRecordWithdrawal s k a x = some t ↔
      capWithdrawalAllowed s k a x ∧
        t = { s with withdrawn := capUpd2 s.withdrawn k a (s.withdrawn k a + x) } := by
  unfold capRecordWithdrawal capWithdrawalAllowed
  by_cases h1 : capWordBound ≤ s.withdrawn k a + x
  · rw [capIte_pos h1]
    exact capNone_iff (by rintro ⟨⟨h, -⟩, -⟩; omega)
  · rw [capIte_neg h1]
    by_cases hp : s.pending k = false
    · rw [capIte_pos hp]
      by_cases h2 : capWordBound ≤ s.deposited k a + s.backfill k a
      · rw [capIte_pos h2]
        exact capNone_iff (by rintro ⟨⟨-, h⟩, -⟩; have := (h hp).1; omega)
      · rw [capIte_neg h2]
        by_cases h3 : s.deposited k a + s.backfill k a < s.withdrawn k a + x
        · rw [capIte_pos h3]
          exact capNone_iff (by rintro ⟨⟨-, h⟩, -⟩; have := (h hp).2; omega)
        · rw [capIte_neg h3]
          exact capSome_iff ⟨by omega, fun _ => ⟨by omega, by omega⟩⟩
    · rw [capIte_neg hp]
      exact capSome_iff ⟨by omega, fun h => absurd h hp⟩

theorem capStep_fromChain {cfg : CapConfig} {s t : CapState} {c a x : ℕ} :
    capStep cfg (.fromChain c a x) s = some t ↔
      (s.registered c = true ∧ x < capWordBound ∧
        (s.origin a = cfg.l1 → x ≤ s.bridgedOut a) ∧
        (∀ k, capTrackedKey cfg s c (s.origin a) = some k → capWithdrawalAllowed s k a x)) ∧
      t = fromChainPost cfg s c a x := by
  simp only [capStep, capHandleFromChain, fromChainPost]
  by_cases hg : s.registered c = true ∧ x < capWordBound
  · rw [capIte_pos hg]
    by_cases ho : s.origin a = cfg.l1
    · rw [capIte_pos ho, capIte_pos ho]
      unfold capDebitBridgedOut
      by_cases hb : s.bridgedOut a < x
      · rw [capIte_pos hb]
        exact capNone_iff (by rintro ⟨⟨-, -, h, -⟩, -⟩; have := h ho; omega)
      · rw [capIte_neg hb]
        rcases hk : capTrackedKey cfg s c (s.origin a) with _ | k
        · simp only [capBump_none]
          exact capSome_iff ⟨hg.1, hg.2, fun _ => by omega, fun k' hk' => by cases hk'⟩
        · simp only [capBump_some]
          rw [capRecordWithdrawal_eq]
          constructor
          · rintro ⟨hw, rfl⟩
            exact ⟨⟨hg.1, hg.2, fun _ => by omega, fun k' hk' => by cases hk'; exact hw⟩, rfl⟩
          · rintro ⟨⟨-, -, -, hw⟩, rfl⟩
            exact ⟨hw k rfl, rfl⟩
    · rw [capIte_neg ho, capIte_neg ho]
      rcases hk : capTrackedKey cfg s c (s.origin a) with _ | k
      · simp only [capBump_none]
        exact capSome_iff ⟨hg.1, hg.2, fun h => absurd h ho, fun k' hk' => by cases hk'⟩
      · simp only [capBump_some]
        rw [capRecordWithdrawal_eq]
        constructor
        · rintro ⟨hw, rfl⟩
          exact ⟨⟨hg.1, hg.2, fun h => absurd h ho, fun k' hk' => by cases hk'; exact hw⟩, rfl⟩
        · rintro ⟨⟨-, -, -, hw⟩, rfl⟩
          exact ⟨hw k rfl, rfl⟩
  · rw [capIte_neg hg]
    exact capNone_iff (by rintro ⟨⟨h1, h2, -, -⟩, -⟩; exact hg ⟨h1, h2⟩)

theorem capStep_setBackfill {cfg : CapConfig} {s t : CapState} {c a v : ℕ} :
    capStep cfg (.setBackfill c a v) s = some t ↔
      (c ≠ cfg.pool ∧ v < capWordBound ∧ s.backfill c a = 0 ∧
        (s.inPool c a = true → s.deposited c a + v < capWordBound ∧
          s.deposited cfg.pool a + setBackfillCredit s c a v < capWordBound)) ∧
      t = setBackfillPost cfg s c a v := by
  simp only [capStep, capSetBackfillEntry, setBackfillPost]
  by_cases h1 : c = cfg.pool
  · rw [capIte_pos h1]
    exact capNone_iff (by rintro ⟨⟨h, -⟩, -⟩; exact h h1)
  · rw [capIte_neg h1]
    by_cases h2 : capWordBound ≤ v
    · rw [capIte_pos h2]
      exact capNone_iff (by rintro ⟨⟨-, h, -⟩, -⟩; omega)
    · rw [capIte_neg h2]
      by_cases h3 : s.backfill c a ≠ 0
      · rw [capIte_pos h3]
        exact capNone_iff (by rintro ⟨⟨-, -, h, -⟩, -⟩; exact h3 h)
      · rw [capIte_neg h3]
        have h3' : s.backfill c a = 0 := not_not.mp h3
        by_cases hp : s.inPool c a = true
        · rw [capIte_pos hp, capIte_pos hp]
          simp only [capNetChainBalance]
          by_cases h4 : capWordBound ≤ s.deposited c a + v
          · rw [capIte_pos h4]
            exact capNone_iff (by rintro ⟨⟨-, -, -, h⟩, -⟩; have := (h hp).1; omega)
          · rw [capIte_neg h4]
            have h5 : ¬ capWordBound ≤ s.deposited c a + 0 := by omega
            rw [capIte_neg h5]
            dsimp only
            have h6 : ¬ (s.deposited c a + v - s.withdrawn c a <
                s.deposited c a + 0 - s.withdrawn c a) := by omega
            rw [capIte_neg h6]
            simp only [capCreditDeposited, Nat.add_zero]
            by_cases h7 : s.deposited cfg.pool a + setBackfillCredit s c a v < capWordBound
            · unfold setBackfillCredit at h7
              rw [capIte_pos h7]
              exact capSome_iff ⟨h1, by omega, h3', fun _ => ⟨by omega, h7⟩⟩
            · unfold setBackfillCredit at h7
              rw [capIte_neg h7]
              exact capNone_iff (by rintro ⟨⟨-, -, -, h⟩, -⟩; exact h7 (h hp).2)
        · rw [capIte_neg hp, capIte_neg hp]
          exact capSome_iff ⟨h1, by omega, h3', fun h => absurd h hp⟩

theorem capStep_markBackfilled {cfg : CapConfig} {s t : CapState} {c : ℕ} :
    capStep cfg (.markBackfilled c) s = some t ↔
      s.pending c = true ∧ t = { s with pending := Function.update s.pending c false } := by
  simp only [capStep, capMarkBackfilled]
  by_cases h : s.pending c = true
  · rw [capIte_pos h]; exact capSome_iff h
  · rw [capIte_neg h]; exact capNone_iff (by rintro ⟨h', -⟩; exact h h')

theorem capStep_moveToPool {cfg : CapConfig} {s t : CapState} {c a : ℕ} :
    capStep cfg (.moveToPool c a) s = some t ↔
      (s.interop c = true ∧ s.pending c = false ∧ s.inPool c a = false ∧
        s.deposited c a + s.backfill c a < capWordBound ∧
        s.deposited cfg.pool a + moveCredit s c a < capWordBound) ∧
      t = movePost cfg s c a := by
  simp only [capStep, capMoveToPool, movePost]
  by_cases h1 : s.interop c = false
  · rw [capIte_pos h1]
    exact capNone_iff (by rintro ⟨⟨h, -⟩, -⟩; simp [h] at h1)
  · rw [capIte_neg h1]
    have h1' : s.interop c = true := by simpa using h1
    by_cases h2 : s.pending c = true
    · rw [capIte_pos h2]
      exact capNone_iff (by rintro ⟨⟨-, h, -⟩, -⟩; simp [h] at h2)
    · rw [capIte_neg h2]
      have h2' : s.pending c = false := by simpa using h2
      by_cases h3 : s.inPool c a = true
      · rw [capIte_pos h3]
        exact capNone_iff (by rintro ⟨⟨-, -, h, -⟩, -⟩; simp [h] at h3)
      · rw [capIte_neg h3]
        have h3' : s.inPool c a = false := by simpa using h3
        simp only [capNetChainBalance]
        by_cases h4 : capWordBound ≤ s.deposited c a + s.backfill c a
        · rw [capIte_pos h4]
          exact capNone_iff (by rintro ⟨⟨-, -, -, h, -⟩, -⟩; omega)
        · rw [capIte_neg h4]
          simp only [capCreditDeposited]
          by_cases h5 : s.deposited cfg.pool a + moveCredit s c a < capWordBound
          · unfold moveCredit at h5
            rw [capIte_pos h5]
            exact capSome_iff ⟨h1', h2', h3', by omega, h5⟩
          · unfold moveCredit at h5
            rw [capIte_neg h5]
            exact capNone_iff (by rintro ⟨⟨-, -, -, -, h⟩, -⟩; exact h5 h)

theorem capStep_initializeUpgrade {cfg : CapConfig} {s t : CapState} :
    capStep cfg .initializeUpgrade s = some t ↔
      s.upgraded = false ∧
        t = { s with upgraded := true, pending := fun c => s.registered c || s.pending c } := by
  simp only [capStep, capInitializeUpgrade]
  by_cases h : s.upgraded = true
  · rw [capIte_pos h]; exact capNone_iff (by rintro ⟨h', -⟩; simp [h'] at h)
  · rw [capIte_neg h]; exact capSome_iff (by simpa using h)

theorem capStep_enableInterop {cfg : CapConfig} {s t : CapState} {c : ℕ} :
    capStep cfg (.enableInterop c) s = some t ↔
      (s.registered c = true ∧ s.interop c = false ∧ s.pending c = false) ∧
        t = { s with interop := Function.update s.interop c true } := by
  simp only [capStep, capEnableInterop]
  by_cases h1 : s.registered c = false
  · rw [capIte_pos h1]; exact capNone_iff (by rintro ⟨⟨h, -⟩, -⟩; simp [h] at h1)
  · rw [capIte_neg h1]
    by_cases h2 : s.interop c = true
    · rw [capIte_pos h2]; exact capNone_iff (by rintro ⟨⟨-, h, -⟩, -⟩; simp [h] at h2)
    · rw [capIte_neg h2]
      by_cases h3 : s.pending c = true
      · rw [capIte_pos h3]; exact capNone_iff (by rintro ⟨⟨-, -, h⟩, -⟩; simp [h] at h3)
      · rw [capIte_neg h3]
        exact capSome_iff ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

theorem capStep_registerChain {cfg : CapConfig} {s t : CapState} {c : ℕ} :
    capStep cfg (.registerChain c) s = some t ↔
      (c ≠ 0 ∧ c < chainIdCap ∧ c ≠ cfg.l1 ∧ s.registered c = false) ∧
        t = { s with registered := Function.update s.registered c true } := by
  simp only [capStep, capRegisterChain]
  by_cases h : c = 0 ∨ chainIdCap ≤ c ∨ c = cfg.l1 ∨ s.registered c = true
  · rw [capIte_pos h]
    refine capNone_iff ?_
    rintro ⟨⟨h1, h2, h3, h4⟩, -⟩
    rcases h with h | h | h | h
    · exact h1 h
    · omega
    · exact h3 h
    · simp [h] at h4
  · rw [capIte_neg h]
    simp only [not_or] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact capSome_iff ⟨h1, by omega, h3, by simpa using h4⟩

theorem capStep_registerAsset {cfg : CapConfig} {s t : CapState} {a o : ℕ} :
    capStep cfg (.registerAsset a o) s = some t ↔
      (s.origin a = 0 ∧ o ≠ 0) ∧ t = { s with origin := Function.update s.origin a o } := by
  simp only [capStep, capRegisterAsset]
  by_cases h : s.origin a ≠ 0 ∨ o = 0
  · rw [capIte_pos h]
    refine capNone_iff ?_
    rintro ⟨⟨h1, h2⟩, -⟩
    rcases h with h | h
    · exact h h1
    · exact h2 h
  · rw [capIte_neg h]
    simp only [not_or, not_not] at h
    exact capSome_iff ⟨h.1, h.2⟩

theorem capStep_populate {cfg : CapConfig} {s t : CapState} {a L : ℕ} :
    capStep cfg (.populate a L) s = some t ↔
      (s.populated a = false ∧ s.origin a = cfg.l1 ∧ s.bridgedOut a + L < capWordBound) ∧
        t = { s with
          populated := Function.update s.populated a true
          bridgedOut := Function.update s.bridgedOut a (s.bridgedOut a + L) } := by
  simp only [capStep, capPopulate]
  by_cases h1 : s.populated a = true
  · rw [capIte_pos h1]; exact capNone_iff (by rintro ⟨⟨h, -⟩, -⟩; simp [h] at h1)
  · rw [capIte_neg h1]
    by_cases h2 : s.origin a ≠ cfg.l1
    · rw [capIte_pos h2]
      exact capNone_iff (by rintro ⟨⟨-, h, -⟩, -⟩; exact h2 h)
    · rw [capIte_neg h2]
      by_cases h3 : capWordBound ≤ s.bridgedOut a + L
      · rw [capIte_pos h3]
        exact capNone_iff (by rintro ⟨⟨-, -, h⟩, -⟩; omega)
      · rw [capIte_neg h3]
        exact capSome_iff ⟨by simpa using h1, not_not.mp h2, by omega⟩

/-! ## One-step facts -/

/-- Monotone fields and the origin's write-once shape, for every successful call. -/
theorem capStep_mono {cfg : CapConfig} {l : CapLabel} {s t : CapState}
    (h : capStep cfg l s = some t) :
    (∀ c, s.interop c = true → t.interop c = true) ∧
    (∀ c, s.registered c = true → t.registered c = true) ∧
    (s.upgraded = true → t.upgraded = true) ∧
    (∀ k a, s.deposited k a ≤ t.deposited k a) ∧
    (∀ k a, s.backfill k a ≤ t.backfill k a) ∧
    (∀ k a, s.backfill k a ≠ 0 → t.backfill k a = s.backfill k a) ∧
    (∀ k a, s.withdrawn k a ≤ t.withdrawn k a) ∧
    (∀ c a, s.inPool c a = true → t.inPool c a = true) ∧
    (∀ a, t.origin a = s.origin a ∨ s.origin a = 0) := by
  cases l with
  | toChain c a x =>
    obtain ⟨-, rfl⟩ := capStep_toChain.mp h
    refine ⟨fun _ h => h, fun _ h => h, fun h => h, fun k a' => capBump_ge _ _ _ _ _ _,
      fun _ _ => le_rfl, fun _ _ _ => rfl, fun _ _ => le_rfl, fun _ _ h => h, fun _ => Or.inl rfl⟩
  | fromChain c a x =>
    obtain ⟨-, rfl⟩ := capStep_fromChain.mp h
    refine ⟨fun _ h => h, fun _ h => h, fun h => h, fun _ _ => le_rfl,
      fun _ _ => le_rfl, fun _ _ _ => rfl, fun k a' => capBump_ge _ _ _ _ _ _, fun _ _ h => h,
      fun _ => Or.inl rfl⟩
  | setBackfill c a v =>
    obtain ⟨⟨-, -, hz, -⟩, rfl⟩ := capStep_setBackfill.mp h
    refine ⟨fun _ h => h, fun _ h => h, fun h => h, ?_, ?_, ?_, fun _ _ => le_rfl, fun _ _ h => h,
      fun _ => Or.inl rfl⟩
    · intro k a'
      simp only [setBackfillPost]
      split_ifs
      · simp only [capUpd2_apply]
        split_ifs with hk
        · obtain ⟨rfl, rfl⟩ := hk; omega
        · exact le_rfl
      · exact le_rfl
    · intro k a'
      simp only [setBackfillPost, capUpd2_apply]
      split_ifs with hk
      · obtain ⟨rfl, rfl⟩ := hk; omega
      · exact le_rfl
    · intro k a' hne
      simp only [setBackfillPost, capUpd2_apply]
      split_ifs with hk
      · obtain ⟨rfl, rfl⟩ := hk; exact absurd hz hne
      · rfl
  | markBackfilled c =>
    obtain ⟨-, rfl⟩ := capStep_markBackfilled.mp h
    exact ⟨fun _ h => h, fun _ h => h, fun h => h, fun _ _ => le_rfl, fun _ _ => le_rfl,
      fun _ _ _ => rfl, fun _ _ => le_rfl, fun _ _ h => h, fun _ => Or.inl rfl⟩
  | moveToPool c a =>
    obtain ⟨-, rfl⟩ := capStep_moveToPool.mp h
    refine ⟨fun _ h => h, fun _ h => h, fun h => h, ?_, fun _ _ => le_rfl, fun _ _ _ => rfl,
      fun _ _ => le_rfl, ?_, fun _ => Or.inl rfl⟩
    · intro k a'
      simp only [movePost, capUpd2_apply]
      split_ifs with hk
      · obtain ⟨rfl, rfl⟩ := hk; omega
      · exact le_rfl
    · intro c' a' h'
      simp only [movePost, capUpd2_apply]
      split_ifs <;> simp [h']
  | initializeUpgrade =>
    obtain ⟨-, rfl⟩ := capStep_initializeUpgrade.mp h
    exact ⟨fun _ h => h, fun _ h => h, fun _ => rfl, fun _ _ => le_rfl, fun _ _ => le_rfl,
      fun _ _ _ => rfl, fun _ _ => le_rfl, fun _ _ h => h, fun _ => Or.inl rfl⟩
  | enableInterop c =>
    obtain ⟨-, rfl⟩ := capStep_enableInterop.mp h
    refine ⟨?_, fun _ h => h, fun h => h, fun _ _ => le_rfl, fun _ _ => le_rfl,
      fun _ _ _ => rfl, fun _ _ => le_rfl, fun _ _ h => h, fun _ => Or.inl rfl⟩
    intro c' h'
    simp only [Function.update_apply]
    split_ifs <;> simp [h']
  | registerChain c =>
    obtain ⟨-, rfl⟩ := capStep_registerChain.mp h
    refine ⟨fun _ h => h, ?_, fun h => h, fun _ _ => le_rfl, fun _ _ => le_rfl,
      fun _ _ _ => rfl, fun _ _ => le_rfl, fun _ _ h => h, fun _ => Or.inl rfl⟩
    intro c' h'
    simp only [Function.update_apply]
    split_ifs <;> simp [h']
  | registerAsset a o =>
    obtain ⟨⟨hz, -⟩, rfl⟩ := capStep_registerAsset.mp h
    refine ⟨fun _ h => h, fun _ h => h, fun h => h, fun _ _ => le_rfl, fun _ _ => le_rfl,
      fun _ _ _ => rfl, fun _ _ => le_rfl, fun _ _ h => h, ?_⟩
    intro a'
    simp only [Function.update_apply]
    split_ifs with ha
    · subst ha; exact Or.inr hz
    · exact Or.inl rfl
  | populate a L =>
    obtain ⟨-, rfl⟩ := capStep_populate.mp h
    exact ⟨fun _ h => h, fun _ h => h, fun h => h, fun _ _ => le_rfl, fun _ _ => le_rfl,
      fun _ _ _ => rfl, fun _ _ => le_rfl, fun _ _ h => h, fun _ => Or.inl rfl⟩


/-- `_trackedBalance` returns the pool key or the chain itself. -/
theorem capTrackedKey_eq {cfg : CapConfig} {s : CapState} {c o k : ℕ}
    (h : capTrackedKey cfg s c o = some k) : k = cfg.pool ∨ k = c := by
  unfold capTrackedKey at h
  split_ifs at h <;> simp_all

/-- The withdrawals a call counts under `key` in `asset`. -/
def capKeyHere (cfg : CapConfig) (key asset : ℕ) (s : CapState) : CapLabel → ℕ
  | .fromChain c a x => if a = asset ∧ capTrackedKey cfg s c (s.origin a) = some key then x else 0
  | _ => 0

theorem releasedUnderKey_cons {cfg : CapConfig} {l : CapLabel} {s t : CapState}
    {ls : List CapLabel} {k a : ℕ} (h : capStep cfg l s = some t) :
    releasedUnderKey cfg k a s (l :: ls) = capKeyHere cfg k a s l + releasedUnderKey cfg k a t ls := by
  cases l <;> simp [releasedUnderKey, capKeyHere, h]

/-- **Exact accounting.**  A call adds to `withdrawn[k][a]` exactly what it counts under `k`. -/
theorem capStep_withdrawn_eq {cfg : CapConfig} {l : CapLabel} {s t : CapState}
    (h : capStep cfg l s = some t) (k a : ℕ) :
    t.withdrawn k a = s.withdrawn k a + capKeyHere cfg k a s l := by
  cases l with
  | fromChain c a' x =>
    obtain ⟨-, rfl⟩ := capStep_fromChain.mp h
    simp only [fromChainPost, capBump_apply, capKeyHere]
    by_cases ha : a' = a
    · subst ha
      by_cases hk : capTrackedKey cfg s c (s.origin a') = some k <;> simp [hk]
    · have : ¬ a = a' := fun h => ha h.symm
      simp [ha, this]
  | toChain c a' x => obtain ⟨-, rfl⟩ := capStep_toChain.mp h; simp [capKeyHere, toChainPost]
  | setBackfill c a' v =>
    obtain ⟨-, rfl⟩ := capStep_setBackfill.mp h; simp [capKeyHere, setBackfillPost]
  | markBackfilled c => obtain ⟨-, rfl⟩ := capStep_markBackfilled.mp h; simp [capKeyHere]
  | moveToPool c a' => obtain ⟨-, rfl⟩ := capStep_moveToPool.mp h; simp [capKeyHere, movePost]
  | initializeUpgrade => obtain ⟨-, rfl⟩ := capStep_initializeUpgrade.mp h; simp [capKeyHere]
  | enableInterop c => obtain ⟨-, rfl⟩ := capStep_enableInterop.mp h; simp [capKeyHere]
  | registerChain c => obtain ⟨-, rfl⟩ := capStep_registerChain.mp h; simp [capKeyHere]
  | registerAsset a' o => obtain ⟨-, rfl⟩ := capStep_registerAsset.mp h; simp [capKeyHere]
  | populate a' L => obtain ⟨-, rfl⟩ := capStep_populate.mp h; simp [capKeyHere]

/-- **The cap, one call.**  Under a non-pending key, `withdrawn` ends at most at the larger of its
old value and `deposited + backfill`. -/
theorem capStep_withdrawn_le {cfg : CapConfig} {l : CapLabel} {s t : CapState}
    (h : capStep cfg l s = some t) {k a : ℕ} (hp : s.pending k = false) :
    t.withdrawn k a ≤ max (s.withdrawn k a) (t.deposited k a + t.backfill k a) := by
  cases l with
  | fromChain c a' x =>
    obtain ⟨⟨-, -, -, hw⟩, rfl⟩ := capStep_fromChain.mp h
    simp only [fromChainPost, capBump_apply]
    split_ifs with hk
    · obtain ⟨hk1, rfl⟩ := hk
      have := ((hw k hk1).2 hp).2
      exact le_max_of_le_right this
    · simp
  | toChain c a' x => obtain ⟨-, rfl⟩ := capStep_toChain.mp h; exact le_max_left _ _
  | setBackfill c a' v => obtain ⟨-, rfl⟩ := capStep_setBackfill.mp h; exact le_max_left _ _
  | markBackfilled c => obtain ⟨-, rfl⟩ := capStep_markBackfilled.mp h; exact le_max_left _ _
  | moveToPool c a' => obtain ⟨-, rfl⟩ := capStep_moveToPool.mp h; exact le_max_left _ _
  | initializeUpgrade => obtain ⟨-, rfl⟩ := capStep_initializeUpgrade.mp h; exact le_max_left _ _
  | enableInterop c => obtain ⟨-, rfl⟩ := capStep_enableInterop.mp h; exact le_max_left _ _
  | registerChain c => obtain ⟨-, rfl⟩ := capStep_registerChain.mp h; exact le_max_left _ _
  | registerAsset a' o => obtain ⟨-, rfl⟩ := capStep_registerAsset.mp h; exact le_max_left _ _
  | populate a' L => obtain ⟨-, rfl⟩ := capStep_populate.mp h; exact le_max_left _ _

/-- A key that is not pending after the upgrade, or that can never be registered, stays so. -/
def KeyStaysClear (s : CapState) (k : ℕ) : Prop :=
  s.pending k = false ∧ (s.upgraded = true ∨ (chainIdCap ≤ k ∧ s.registered k = false))

theorem capStep_keyStaysClear {cfg : CapConfig} {l : CapLabel} {s t : CapState}
    (h : capStep cfg l s = some t) {k : ℕ} (hk : KeyStaysClear s k) : KeyStaysClear t k := by
  obtain ⟨hp, hu⟩ := hk
  cases l with
  | markBackfilled c =>
    obtain ⟨-, rfl⟩ := capStep_markBackfilled.mp h
    refine ⟨?_, hu⟩
    simp only [Function.update_apply]
    split_ifs <;> simp [hp]
  | initializeUpgrade =>
    obtain ⟨hu', rfl⟩ := capStep_initializeUpgrade.mp h
    rcases hu with hu | ⟨hcap, hr⟩
    · simp [hu] at hu'
    · exact ⟨by simp [hr, hp], Or.inl rfl⟩
  | registerChain c =>
    obtain ⟨⟨-, hc, -, -⟩, rfl⟩ := capStep_registerChain.mp h
    refine ⟨hp, ?_⟩
    rcases hu with hu | ⟨hcap, hr⟩
    · exact Or.inl hu
    · refine Or.inr ⟨hcap, ?_⟩
      have : k ≠ c := by omega
      simp [this, hr]
  | toChain c a x => obtain ⟨-, rfl⟩ := capStep_toChain.mp h; exact ⟨hp, hu⟩
  | fromChain c a x => obtain ⟨-, rfl⟩ := capStep_fromChain.mp h; exact ⟨hp, hu⟩
  | setBackfill c a v => obtain ⟨-, rfl⟩ := capStep_setBackfill.mp h; exact ⟨hp, hu⟩
  | moveToPool c a => obtain ⟨-, rfl⟩ := capStep_moveToPool.mp h; exact ⟨hp, hu⟩
  | enableInterop c => obtain ⟨-, rfl⟩ := capStep_enableInterop.mp h; exact ⟨hp, hu⟩
  | registerAsset a o => obtain ⟨-, rfl⟩ := capStep_registerAsset.mp h; exact ⟨hp, hu⟩
  | populate a L => obtain ⟨-, rfl⟩ := capStep_populate.mp h; exact ⟨hp, hu⟩

/-- **(c), one call.** -/
theorem capStep_frame {cfg : CapConfig} {l : CapLabel} {s t : CapState}
    (h : capStep cfg l s = some t) {d : ℕ} (hdp : d ≠ cfg.pool) (hdc : l.chain? ≠ some d) :
    t.deposited d = s.deposited d ∧ t.withdrawn d = s.withdrawn d ∧
      t.backfill d = s.backfill d ∧ t.inPool d = s.inPool d ∧ t.interop d = s.interop d ∧
      t.registered d = s.registered d ∧ (l ≠ .initializeUpgrade → t.pending d = s.pending d) := by
  cases l with
  | toChain c a x =>
    obtain ⟨-, rfl⟩ := capStep_toChain.mp h
    have hcd : c ≠ d := fun e => hdc (by simp [CapLabel.chain?, e])
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    funext a'
    simp only [toChainPost, capBump_apply]
    split_ifs with hk
    · rcases capTrackedKey_eq hk.1 with e | e
      · exact absurd e hdp
      · exact absurd e.symm hcd
    · simp
  | fromChain c a x =>
    obtain ⟨-, rfl⟩ := capStep_fromChain.mp h
    have hcd : c ≠ d := fun e => hdc (by simp [CapLabel.chain?, e])
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    funext a'
    simp only [fromChainPost, capBump_apply]
    split_ifs with hk
    · rcases capTrackedKey_eq hk.1 with e | e
      · exact absurd e hdp
      · exact absurd e.symm hcd
    · simp
  | setBackfill c a v =>
    obtain ⟨-, rfl⟩ := capStep_setBackfill.mp h
    have hcd : d ≠ c := fun e => hdc (by simp [CapLabel.chain?, e])
    refine ⟨?_, rfl, ?_, rfl, rfl, rfl, fun _ => rfl⟩
    · funext a'
      simp only [setBackfillPost]
      split_ifs
      · simp [capUpd2_apply, hdp]
      · rfl
    · funext a'
      simp [setBackfillPost, capUpd2_apply, hcd]
  | markBackfilled c =>
    obtain ⟨-, rfl⟩ := capStep_markBackfilled.mp h
    have hcd : d ≠ c := fun e => hdc (by simp [CapLabel.chain?, e])
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => by simp [hcd]⟩
  | moveToPool c a =>
    obtain ⟨-, rfl⟩ := capStep_moveToPool.mp h
    have hcd : d ≠ c := fun e => hdc (by simp [CapLabel.chain?, e])
    refine ⟨?_, rfl, rfl, ?_, rfl, rfl, fun _ => rfl⟩
    · funext a'; simp [movePost, capUpd2_apply, hdp]
    · funext a'; simp [movePost, capUpd2_apply, hcd]
  | initializeUpgrade =>
    obtain ⟨-, rfl⟩ := capStep_initializeUpgrade.mp h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun h => absurd rfl h⟩
  | enableInterop c =>
    obtain ⟨-, rfl⟩ := capStep_enableInterop.mp h
    have hcd : d ≠ c := fun e => hdc (by simp [CapLabel.chain?, e])
    exact ⟨rfl, rfl, rfl, rfl, by simp [hcd], rfl, fun _ => rfl⟩
  | registerChain c =>
    obtain ⟨-, rfl⟩ := capStep_registerChain.mp h
    have hcd : d ≠ c := fun e => hdc (by simp [CapLabel.chain?, e])
    exact ⟨rfl, rfl, rfl, rfl, rfl, by simp [hcd], fun _ => rfl⟩
  | registerAsset a o =>
    obtain ⟨-, rfl⟩ := capStep_registerAsset.mp h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | populate a L =>
    obtain ⟨-, rfl⟩ := capStep_populate.mp h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

end Contracts.L1NativeTokenVault.Bulkhead
