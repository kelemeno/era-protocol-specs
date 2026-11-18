import EraSpec.Contracts.L1ChainAssetHandler.Properties.SettlementLayerValidation
import EraSpec.Contracts.L1ChainAssetHandler.Proofs.SettlementLayerValidationSteps

/-!
# Proofs: `isValidSettlementLayer` against the layer that executed each batch

Proofs of `EraSpec.Contracts.L1ChainAssetHandler.Properties.SettlementLayerValidation`. The
reachable-state results go through the invariant `SLVInv` of
`EraSpec.Contracts.L1ChainAssetHandler.Proofs.SettlementLayerValidationSteps`; the witnesses and
countermodels evaluate concrete runs.
-/

namespace Contracts.L1ChainAssetHandler.SettlementLayerValidation

/-! ## The function -/

theorem IsValidUnrolled : Properties.IsValidUnrolled := by
  refine ⟨fun l1 mn ivs b X k hmn h2 => ?_, fun l1 mn ivs b X k hmn => ?_⟩
  · interval_cases mn
    · simp [isValidSettlementLayer, scanIntervals, closedForm, maxMigrations, numToSL]
    · simp only [isValidSettlementLayer, maxMigrations, numToSL, closedForm]
      simp [List.range', scanIntervals]
    · simp only [isValidSettlementLayer, maxMigrations, numToSL, closedForm]
      simp [List.range', scanIntervals, h2]
  · have : ¬ mn ≤ maxMigrations := by simp only [maxMigrations]; omega
    simp only [isValidSettlementLayer, this, ite_false]

theorem LegacyIndexZero : Properties.LegacyIndexZero := by
  refine ⟨fun l1 mn ivs ivs' b X k hivs => ?_, fun l1 mn ivs b X k h0 => ?_, ?_⟩
  · unfold isValidSettlementLayer
    have : (List.range' numToSL mn).map ivs = (List.range' numToSL mn).map ivs' := by
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range'] at hi
      exact hivs i (by simp only [numToSL] at hi; omega)
    rw [this]
  · unfold isValidSettlementLayerMain isValidSettlementLayer
    rw [List.range_eq_range', List.range'_succ]
    simp [scanIntervals, h0, numToSL]
  · refine ⟨1, fun i => if i = 0 then ⟨0, 5, 0, 10, 9, false⟩ else MigInterval.empty, 3, 9, 4,
      rfl, by decide, by decide, by decide, by decide⟩

/-- No step writes the index-0 interval. -/
lemma slv_step_ivs0 {K : ValEnv} {W : ValWorld} {s s' : ValState} {l : ValLabel}
    (h : valStep K W s l = some s') : s'.ivs 0 = s.ivs 0 := by
  cases l with
  | execL1 b => obtain ⟨_, _, _, rfl⟩ := step_execL1 h; rfl
  | execSL t b => obtain ⟨_, _, _, _, _, rfl⟩ := step_execSL h; rfl
  | slSeal t => obtain rfl := step_slSeal h; rfl
  | slExecL1 t => obtain ⟨_, _, _, rfl⟩ := step_slExecL1 h; rfl
  | burnL1 t =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := step_burnL1 h
    dsimp only
    exact upd_ne _ _ (by omega)
  | mintSL => obtain ⟨_, _, _, _, _, rfl⟩ := step_mintSL h; rfl
  | failSL => obtain ⟨_, _, _, rfl⟩ := step_failSL h; rfl
  | confirmFailure =>
    obtain ⟨_, _, _, hmn, _, rfl⟩ := step_confirmFailure h
    dsimp only
    exact upd_ne _ _ (by rw [hmn]; decide)
  | burnSL t => obtain ⟨_, _, _, _, _, rfl⟩ := step_burnSL h; rfl
  | mintL1 =>
    obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := step_mintL1 h
    dsimp only
    exact upd_ne _ _ (by decide)

/-- No run writes the index-0 interval. -/
lemma slv_run_ivs0 {K : ValEnv} {W : ValWorld} :
    ∀ {s s' : ValState} {ls : List ValLabel}, valRun K W s ls = some s' → s'.ivs 0 = s.ivs 0
  | s, s', [], h => by
    simp only [valRun, Option.some.injEq] at h
    rw [h]
  | s, s', l :: ls, h => by
    simp only [valRun] at h
    cases hs : valStep K W s l with
    | none => rw [hs] at h; simp at h
    | some s1 =>
      rw [hs] at h
      rw [slv_run_ivs0 h, slv_step_ivs0 hs]

theorem MainAgreesWithoutLegacyInterval : Properties.MainAgreesWithoutLegacyInterval := by
  intro K W s0 s ls hrun
  have h0 := slv_run_ivs0 hrun
  refine ⟨h0, fun hsl b X k => ?_⟩
  exact LegacyIndexZero.2.1 W.l1 s.mn s.ivs b X k (by rw [h0]; exact hsl)

/-! ## Reachable states -/

/-- On a state satisfying the invariant, `migrationNumber ≤ 2`. -/
theorem slvInv_mn_le {K : ValEnv} {W : ValWorld} {s : ValState} (hI : SLVInv K W s) :
    s.mn ≤ maxMigrations := by
  cases hI with
  | home _ hA => simp [hA.mn, maxMigrations]
  | pending _ _ hB => simp [hB.mn, maxMigrations]
  | onSL _ _ hO => simp [hO.mn, maxMigrations]
  | returning _ _ _ hD => simp [hD.mn, maxMigrations]
  | back _ _ hE => simp [hE.mn, maxMigrations]

/-- A whitelisted layer has a nonzero chain id in a world satisfying `ValWorld.Ok`. -/
lemma wl_ne_zero {W : ValWorld} (hW : W.Ok) {t : ℕ} (ht : W.wl t = true) : t ≠ 0 := by
  rintro rfl
  simp [ValWorld.Ok] at hW
  simp [hW] at ht

/-- The answer for an executed batch on a state satisfying the invariant. -/
theorem slv_answer {K : ValEnv} {W : ValWorld} {s : ValState} (hW : W.Ok) (hI : SLVInv K W s)
    {b : ℕ} {r : Settled} (hb : s.hist b = some r) (X k : ℕ) :
    isValidAt W s b X k = some (decide (X = r.layer ∧
      (r.layer ≠ W.l1 → (s.ivs 1).lower ≤ k ∧
        ((s.ivs 1).active = false → k ≤ (s.ivs 1).upper)))) := by
  have hC := hI.common
  have hmn := slvInv_mn_le hI
  unfold isValidAt
  rw [IsValidUnrolled.1 _ _ _ _ _ _ hmn hC.ivs2]
  have hble := hist_le_total hC.contig hb
  cases hI with
  | home _ hA =>
    have hl := hA.allL1 b r hb
    simp [closedForm, hA.mn, hl]
  | pending t _ hB =>
    have hl := hB.allL1 b r hb
    simp [closedForm, hB.mn, hB.ivSl, wl_ne_zero hW hB.wl, hB.ivTo, hble, hl]
  | onSL t _ hO =>
    by_cases hbt : b ≤ s.mrL1 W.c
    · have hl := hO.histL1 b r hb hbt
      simp [closedForm, hO.mn, hO.ivSl, wl_ne_zero hW hO.wl, hO.ivTo, hbt, hl]
    · obtain ⟨hl, -, -⟩ := hO.histSL b r hb (by omega)
      simp [closedForm, hO.mn, hO.ivSl, wl_ne_zero hW hO.wl, hO.ivTo, hbt, hl, hO.ivActive,
        hO.ne_l1]
  | returning t m _ hD =>
    by_cases hbt : b ≤ s.mrL1 W.c
    · have hl := hD.histL1 b r hb hbt
      simp [closedForm, hD.mn, hD.ivSl, wl_ne_zero hW hD.wl, hD.ivTo, hbt, hl]
    · obtain ⟨hl, -, -⟩ := hD.histSL b r hb (by omega)
      simp [closedForm, hD.mn, hD.ivSl, wl_ne_zero hW hD.wl, hD.ivTo, hbt, hl, hD.ivActive,
        hD.ne_l1]
  | back t _ hE =>
    by_cases hbt : b ≤ (s.ivs 1).toGW
    · have hl := hE.histL1 b r hb (Or.inl hbt)
      simp [closedForm, hE.mn, hE.ivSl, wl_ne_zero hW hE.wl, hbt, hl]
    · by_cases hbf : b ≤ (s.ivs 1).fromGW
      · obtain ⟨hl, -, -⟩ := hE.histSL b r hb (by omega) hbf
        simp [closedForm, hE.mn, hE.ivSl, wl_ne_zero hW hE.wl, hbt, hbf, hl, hE.ivActive,
          hE.ne_l1]
      · have hl := hE.histL1 b r hb (Or.inr (by omega))
        simp [closedForm, hE.mn, hE.ivSl, wl_ne_zero hW hE.wl, hbt, hbf, hl, hE.ivActive]

/-- The bounds on a reachable state satisfying the invariant. -/
theorem slv_bounds {K : ValEnv} {W : ValWorld} {s : ValState} (hI : SLVInv K W s)
    {b : ℕ} {r : Settled} (hb : s.hist b = some r) (hl : r.layer ≠ W.l1) :
    r.layer = (s.ivs 1).sl ∧ 1 ≤ s.mn ∧ (s.ivs 1).toGW < b ∧
      ((s.ivs 1).active = false → b ≤ (s.ivs 1).fromGW) ∧
      (K.sealedOnly = true → (s.ivs 1).lower < r.slBatch) ∧
      (K.finalizedAfterExec = true → (s.ivs 1).active = false → r.slBatch ≤ (s.ivs 1).upper) := by
  cases hI with
  | home _ hA => exact absurd (hA.allL1 b r hb) hl
  | pending _ _ hB => exact absurd (hB.allL1 b r hb) hl
  | onSL t _ hO =>
    have hbt : s.mrL1 W.c < b := by
      by_contra hbt
      exact hl (hO.histL1 b r hb (by omega))
    obtain ⟨h1, h2, _⟩ := hO.histSL b r hb hbt
    refine ⟨h1.trans hO.ivSl.symm, by simp [hO.mn], by rw [hO.ivTo]; exact hbt, ?_, h2, ?_⟩
    · intro h; simp [hO.ivActive] at h
    · intro _ h; simp [hO.ivActive] at h
  | returning t m _ hD =>
    have hbt : s.mrL1 W.c < b := by
      by_contra hbt
      exact hl (hD.histL1 b r hb (by omega))
    obtain ⟨h1, h2, _⟩ := hD.histSL b r hb hbt
    refine ⟨h1.trans hD.ivSl.symm, by simp [hD.mn], by rw [hD.ivTo]; exact hbt, ?_, h2, ?_⟩
    · intro h; simp [hD.ivActive] at h
    · intro _ h; simp [hD.ivActive] at h
  | back t _ hE =>
    have hbt : (s.ivs 1).toGW < b := by
      by_contra hbt
      exact hl (hE.histL1 b r hb (Or.inl (by omega)))
    have hbf : b ≤ (s.ivs 1).fromGW := by
      by_contra hbf
      exact hl (hE.histL1 b r hb (Or.inr (by omega)))
    obtain ⟨h1, h2, h3⟩ := hE.histSL b r hb hbt hbf
    exact ⟨h1.trans hE.ivSl.symm, by simp [hE.mn], hbt, fun _ => hbf, h2, fun hf _ => h3 hf⟩

theorem ReachableNeverReverts : Properties.ReachableNeverReverts := by
  intro K W s0 s ls h0 hrun
  have hI := slvInv_run (slvInv_init (K := K) h0) hrun
  have hmn := slvInv_mn_le hI
  refine ⟨hmn, fun b X k => ?_⟩
  simp [isValidAt, isValidSettlementLayer, hmn]

theorem CountersEqualAndAwayMeansMigrationOne :
    Properties.CountersEqualAndAwayMeansMigrationOne := by
  intro K W s0 s ls h0 hrun
  have hI := slvInv_run (slvInv_init (K := K) h0) hrun
  refine ⟨hI.common.execEq, fun haway => ?_⟩
  cases hI with
  | home _ hA => simp [hA.home] at haway
  | pending _ _ hB => exact hB.mn
  | onSL _ _ hO => exact hO.mn
  | returning _ _ _ hD => exact hD.mn
  | back _ _ hE => simp [hE.home] at haway

theorem ExecutedLogContiguous : Properties.ExecutedLogContiguous := by
  intro K W s0 s ls h0 hrun
  exact (slvInv_run (slvInv_init (K := K) h0) hrun).common.contig

theorem ExecutedBatchNeverRewritten : Properties.ExecutedBatchNeverRewritten := by
  intro K W s0 s1 s2 ls1 ls2 h0 h1 h2
  exact slv_hist_run (slvInv_run (slvInv_init (K := K) h0) h1) h2

theorem ExecutedBatchAnswer : Properties.ExecutedBatchAnswer := by
  intro K W s0 s ls hW h0 hrun b r hb X k
  exact slv_answer hW (slvInv_run (slvInv_init (K := K) h0) hrun) hb X k

theorem ExecutedBatchSound : Properties.ExecutedBatchSound := by
  intro K W s0 s ls hW h0 hrun b r X k hb hv
  rw [ExecutedBatchAnswer K W s0 s ls hW h0 hrun b r hb X k] at hv
  simp only [Option.some.injEq, decide_eq_true_eq] at hv
  exact hv.1

theorem SLBatchWithinBounds : Properties.SLBatchWithinBounds := by
  intro K W s0 s ls h0 hrun b r hb hl
  exact slv_bounds (slvInv_run (slvInv_init (K := K) h0) hrun) hb hl

theorem IntervalBatchesRanOnLayer : Properties.IntervalBatchesRanOnLayer := by
  intro K W s0 s ls h0 hrun hmn b r hb hto hfrom
  have hI := slvInv_run (slvInv_init (K := K) h0) hrun
  have hble := hist_le_total hI.common.contig hb
  cases hI with
  | home _ hA => simp [hA.mn] at hmn
  | pending t _ hB => rw [hB.ivTo] at hto; omega
  | onSL t _ hO =>
    obtain ⟨hl, -, -⟩ := hO.histSL b r hb (by rw [← hO.ivTo]; exact hto)
    exact ⟨hl.trans hO.ivSl.symm, hl ▸ hO.ne_l1⟩
  | returning t m _ hD =>
    obtain ⟨hl, -, -⟩ := hD.histSL b r hb (by rw [← hD.ivTo]; exact hto)
    exact ⟨hl.trans hD.ivSl.symm, hl ▸ hD.ne_l1⟩
  | back t _ hE =>
    obtain ⟨hl, -, -⟩ := hE.histSL b r hb hto (hfrom hE.ivActive)
    exact ⟨hl.trans hE.ivSl.symm, hl ▸ hE.ne_l1⟩

theorem ExecutedBatchComplete : Properties.ExecutedBatchComplete := by
  intro W s0 s ls hW h0 hrun b r hb
  have hI := slvInv_run (slvInv_init (K := ValEnv.real) h0) hrun
  refine ⟨?_, fun k hk hku => ?_⟩
  · rw [slv_answer hW hI hb]
    simp only [Option.some.injEq, decide_eq_true_eq, true_and]
    intro hl
    obtain ⟨_, _, _, _, hlow, hup⟩ := slv_bounds hI hb hl
    exact ⟨le_of_lt (hlow rfl), hup rfl⟩
  · rw [slv_answer hW hI hb]
    simp only [Option.some.injEq, decide_eq_true_eq, true_and]
    intro hl
    obtain ⟨_, _, _, _, hlow, _⟩ := slv_bounds hI hb hl
    exact ⟨le_of_lt (lt_of_lt_of_le (hlow rfl) hk), hku⟩

/-! ## A failed migration and the head -/

theorem FailureClassifiesAllOnL1 : Properties.FailureClassifiesAllOnL1 := by
  intro K W s s' h b X k
  obtain ⟨m, _, _, hmn, _, rfl⟩ := step_confirmFailure h
  simp [isValidAt, isValidSettlementLayer, hmn, numToSL, maxMigrations, scanIntervals]

/-- In a world with migrations disabled, a step leaves `migrationNumber` and the interval row
unchanged, or it confirms a failure and takes `migrationNumber` from 1 to 0 with interval 1
deleted. -/
lemma slv_step_disabled {K : ValEnv} {W : ValWorld} {s s' : ValState} {l : ValLabel}
    (hW : W.enabled = false) (h : valStep K W s l = some s') :
    (s'.mn = s.mn ∧ s'.ivs = s.ivs) ∨
      (s.mn = 1 ∧ s'.mn = 0 ∧ s'.ivs = upd s.ivs 1 MigInterval.empty) := by
  cases l with
  | execL1 b => obtain ⟨_, _, _, rfl⟩ := step_execL1 h; exact Or.inl ⟨rfl, rfl⟩
  | execSL t b => obtain ⟨_, _, _, _, _, rfl⟩ := step_execSL h; exact Or.inl ⟨rfl, rfl⟩
  | slSeal t => obtain rfl := step_slSeal h; exact Or.inl ⟨rfl, rfl⟩
  | slExecL1 t => obtain ⟨_, _, _, rfl⟩ := step_slExecL1 h; exact Or.inl ⟨rfl, rfl⟩
  | burnL1 t => obtain ⟨he, _⟩ := step_burnL1 h; simp [hW] at he
  | mintSL => obtain ⟨_, _, he, _⟩ := step_mintSL h; simp [hW] at he
  | failSL => obtain ⟨_, _, _, rfl⟩ := step_failSL h; exact Or.inl ⟨rfl, rfl⟩
  | confirmFailure =>
    obtain ⟨_, _, _, hmn, _, rfl⟩ := step_confirmFailure h
    have hmn1 : s.mn = 1 := hmn
    refine Or.inr ⟨hmn1, ?_, ?_⟩
    · show s.mn - 1 = 0
      rw [hmn1]
    · show upd s.ivs s.mn MigInterval.empty = upd s.ivs 1 MigInterval.empty
      rw [hmn1]
  | burnSL t => obtain ⟨_, _, he, _⟩ := step_burnSL h; simp [hW] at he
  | mintL1 => obtain ⟨_, _, he, _⟩ := step_mintL1 h; simp [hW] at he

/-- In a world with migrations disabled, along a run the classification state is the start's,
or the start had `migrationNumber` 1 and a failure confirmation reset it. -/
lemma slv_run_disabled {K : ValEnv} {W : ValWorld} (hW : W.enabled = false) (s0 : ValState) :
    ∀ {s1 s : ValState} {ls : List ValLabel},
      ((s1.mn = s0.mn ∧ s1.ivs = s0.ivs) ∨
        (s0.mn = 1 ∧ s1.mn = 0 ∧ s1.ivs = upd s0.ivs 1 MigInterval.empty)) →
      valRun K W s1 ls = some s →
      ((s.mn = s0.mn ∧ s.ivs = s0.ivs) ∨
        (s0.mn = 1 ∧ s.mn = 0 ∧ s.ivs = upd s0.ivs 1 MigInterval.empty))
  | s1, s, [], hP, h => by
    simp only [valRun, Option.some.injEq] at h
    exact h ▸ hP
  | s1, s, l :: ls, hP, h => by
    simp only [valRun] at h
    cases hs : valStep K W s1 l with
    | none => rw [hs] at h; simp at h
    | some s2 =>
      rw [hs] at h
      refine slv_run_disabled hW s0 ?_ h
      rcases slv_step_disabled hW hs with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · rw [h1, h2]; exact hP
      · rcases hP with ⟨h4, h5⟩ | ⟨_, h5, _⟩
        · exact Or.inr ⟨h4 ▸ h1, h2, by rw [h3, h5]⟩
        · rw [h5] at h1; exact absurd h1 (by decide)

theorem MigrationsDisabledOnlyHistoricalIntervals :
    Properties.MigrationsDisabledOnlyHistoricalIntervals := by
  intro K W s0 s ls hW hrun
  have hP := slv_run_disabled (K := K) hW s0 (Or.inl ⟨rfl, rfl⟩) hrun
  refine ⟨hP, fun b X k hX hv => ?_⟩
  rcases hP with ⟨h1, h2⟩ | ⟨_, h1, _⟩
  · unfold isValidAt at hv ⊢
    rw [h1, h2] at hv
    exact hv
  · simp [isValidAt, isValidSettlementLayer, h1, maxMigrations, scanIntervals, hX] at hv

theorem MigrationsDisabledEveryBatchOnL1 : Properties.MigrationsDisabledEveryBatchOnL1 := by
  intro K W s0 s ls hW h0 hrun
  have hI := slvInv_run (slvInv_init (K := K) h0) hrun
  have hmn : s.mn = 0 := by
    rcases slv_run_disabled (K := K) hW s0 (Or.inl ⟨rfl, rfl⟩) hrun with ⟨h1, _⟩ | ⟨h1, _, _⟩
    · rw [h1]; exact h0.1
    · rw [h0.1] at h1; exact absurd h1 (by decide)
  have hA : SLVHome W s := by
    cases hI with
    | home _ hA => exact hA
    | pending _ _ hB => simp [hB.mn] at hmn
    | onSL _ _ hO => simp [hO.mn] at hmn
    | returning _ _ _ hD => simp [hD.mn] at hmn
    | back _ _ hE => simp [hE.mn] at hmn
  refine ⟨hA.allL1, fun b X k => ?_⟩
  simp [isValidAt, isValidSettlementLayer, hmn, maxMigrations, scanIntervals]

/-! ## Countermodels -/

/-- The fresh state is a start state in every world. -/
lemma valInit_wFresh (W : ValWorld) : ValInit W wFresh := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro t g h; simp [wFresh] at h
  · intro t _ _; simp [wFresh]
  · intro b; simp [wFresh]; omega
  · intro b r h; simp [wFresh] at h

theorem CompletenessNeedsSealedOnly : Properties.CompletenessNeedsSealedOnly := by
  intro h
  have := h wWorld wFresh _ [.slExecL1 5, .slExecL1 5, .burnL1 5, .mintSL, .execSL 5 1]
    (rfl : wWorld.Ok) (valInit_wFresh _) rfl 1 _ rfl
  exact absurd this (by decide)

theorem CompletenessNeedsFinalizedAfterExec : Properties.CompletenessNeedsFinalizedAfterExec := by
  intro h
  obtain ⟨k, hk, hv⟩ := h wWorld wFresh _ [.burnL1 5, .mintSL, .execSL 5 1, .burnSL 5, .mintL1]
    (rfl : wWorld.Ok) (valInit_wFresh _) rfl 1 _ rfl
  simp [isValidAt, isValidSettlementLayer, upd, maxMigrations, numToSL, wWorld, wFresh] at hv hk
  simp [List.range', scanIntervals, upd, MigInterval.empty] at hv
  omega

theorem SoundnessNeedsNonzeroLayerIds : Properties.SoundnessNeedsNonzeroLayerIds := by
  intro h
  have := h ⟨true, true⟩ wWorldZero wFresh _ [.burnL1 0, .mintSL, .execSL 0 1] (valInit_wFresh _)
    rfl 1 _ 1 0 rfl rfl
  exact absurd this (by decide)

theorem ClaimBelowFirstContainingBatchAccepted :
    Properties.ClaimBelowFirstContainingBatchAccepted := by
  intro h
  have := h wWorld wFresh _ wRoundTrip (rfl : wWorld.Ok) (valInit_wFresh _) rfl 3 _ 1 rfl rfl
  exact absurd this (by decide)

/-! ## Witnesses -/

theorem RoundTripWitness : Properties.RoundTripWitness :=
  ⟨rfl, rfl, valInit_wFresh _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem FailedMigrationWitness : Properties.FailedMigrationWitness :=
  ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem MigrationsDisabledWitness : Properties.MigrationsDisabledWitness :=
  ⟨rfl, valInit_wFresh _, ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩,
    ⟨_, _, rfl, rfl, rfl, rfl⟩⟩

end Contracts.L1ChainAssetHandler.SettlementLayerValidation
