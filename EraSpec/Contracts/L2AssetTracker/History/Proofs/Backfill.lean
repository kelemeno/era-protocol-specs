import EraSpec.Contracts.L2AssetTracker.Proofs.Accounting
import EraSpec.Contracts.L2AssetTracker.History.Properties.Backfill

/-! # Proofs: the tracker's base-token backfill at the pin (History) -/

namespace Contracts.L2AssetTracker.History

theorem BackfillOnlyBaseFromZero : Properties.BackfillOnlyBaseFromZero := by
  intro cfg sys sys' amount h
  simp only [exec, Option.map_eq_some_iff] at h
  obtain ⟨st', h, rfl⟩ := h
  unfold backFillZKSyncOSBaseTokenV31MigrationData at h
  rw [ite_eq_right (not_not.2 rfl)] at h
  by_cases h1 : sys.st.needBaseTokenTotalSupplyBackfill = false
  · rw [ite_eq_left h1] at h; cases h
  rw [ite_eq_right h1] at h
  by_cases h2 : sys.st.isAssetRegistered sys.st.baseTokenAssetId = false
  · rw [ite_eq_left h2] at h; cases h
  rw [ite_eq_right h2] at h
  by_cases h3 : (sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId).isSaved = false
  · rw [ite_eq_left h3] at h; cases h
  rw [ite_eq_right h3] at h
  by_cases h4 : (sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId).amount ≠ 0
  · rw [ite_eq_left h4] at h; cases h
  rw [ite_eq_right h4] at h
  cases h
  have hs : (sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId).isSaved = true := by
    simpa using h3
  have ha : (sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId).amount = 0 := by
    simpa using h4
  refine ⟨by simpa using h2, ?_, by simpa using h1, rfl, rfl, rfl⟩
  cases hsnap : sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId
  rw [hsnap] at hs ha
  simp only at hs ha
  rw [hs, ha]

/-- Once `initL2` has run and the flag is clear, both stay so. -/
theorem exec_keeps_flag_clear {cfg : Config} {sys sys' : Sys} {op : Op}
    (h : exec cfg sys op = some sys') (hg : sys.st.guardInitialized = true)
    (hn : sys.st.needBaseTokenTotalSupplyBackfill = false) :
    sys'.st.guardInitialized = true ∧ sys'.st.needBaseTokenTotalSupplyBackfill = false := by
  have flow : ∀ {st' : Storage} {x : AssetId}, Frame sys.st st' x →
      st'.guardInitialized = true ∧ st'.needBaseTokenTotalSupplyBackfill = false :=
    fun hf => ⟨hf.guard.trans hg, hf.need.trans hn⟩
  cases op with
  | registerNewToken x =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold registerNewTokenIfNeeded at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    by_cases hx : sys.st.isAssetRegistered x = true
    · rw [ite_eq_left hx] at h; cases h; exact ⟨hg, hn⟩
    rw [ite_eq_right hx] at h
    by_cases hc : cfg.ntvOriginChainId x = cfg.thisChain
    · rw [ite_eq_left hc] at h; cases h; exact ⟨hg, hn⟩
    · rw [ite_eq_right hc] at h; cases h; exact ⟨hg, hn⟩
  | registerBaseDuringUpgrade =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold registerBaseTokenDuringUpgrade at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    by_cases hx : sys.st.isAssetRegistered sys.st.baseTokenAssetId = true
    · rw [ite_eq_left hx] at h; cases h
    rw [ite_eq_right hx] at h
    cases h
    exact ⟨hg, hn⟩
  | registerLegacy reads x =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    exact flow (registerLegacyTokenIfNeeded_frame (registerLegacyToken_eq h))
  | initiate reads toChain x amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleInitiateBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact flow (initiateInner_frame h)
  | initiateBase reads toChain amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleInitiateBaseTokenBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact flow (initiateInner_frame h)
  | finalize reads fromChain x amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleFinalizeBridgingOnL2 at h
    rw [ite_eq_right (not_not.2 rfl)] at h
    exact flow (finalizeInner_frame h)
  | finalizeBase reads caller fromChain amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold handleFinalizeBaseTokenBridgingOnL2 at h
    by_cases hc : caller ≠ cfg.baseTokenHolder ∧ caller ≠ cfg.l2BaseToken
    · rw [ite_eq_left hc] at h; cases h
    rw [ite_eq_right hc] at h
    by_cases h0 : amount = 0
    · rw [ite_eq_left h0] at h; cases h; exact ⟨hg, hn⟩
    rw [ite_eq_right h0] at h
    by_cases hb : sys.st.baseTokenAssetId = 0
    · rw [ite_eq_left hb] at h; cases h
    rw [ite_eq_right hb] at h
    exact flow (finalizeInner_frame h)
  | backfill amount =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold backFillZKSyncOSBaseTokenV31MigrationData at h
    rw [ite_eq_right (not_not.2 rfl), ite_eq_left hn] at h
    cases h
  | initL2 need =>
    simp only [exec, Option.map_eq_some_iff] at h
    obtain ⟨st', h, rfl⟩ := h
    unfold initL2 at h
    rw [ite_eq_left hg] at h
    cases h
  | setSettlementLayer c =>
    simp only [exec, Option.some.injEq] at h
    subst h
    exact ⟨hg, hn⟩

theorem BackfillAtMostOnce : Properties.BackfillAtMostOnce := by
  intro cfg sys₀ sys₁ sys₂ amount amount' hinv h₁ hreach
  obtain ⟨_, _, hneed, hst, _, _⟩ := BackfillOnlyBaseFromZero cfg sys₀ sys₁ amount h₁
  have hg₀ : sys₀.st.guardInitialized = true := by
    by_contra hg
    have := hinv.backfillNeedsInit (by simpa using hg)
    rw [this] at hneed
    cases hneed
  have hclear : sys₁.st.guardInitialized = true ∧ sys₁.st.needBaseTokenTotalSupplyBackfill = false := by
    rw [hst]; exact ⟨hg₀, rfl⟩
  have hclear₂ : sys₂.st.guardInitialized = true ∧
      sys₂.st.needBaseTokenTotalSupplyBackfill = false := by
    induction hreach with
    | refl => exact hclear
    | tail _ hstep ih =>
      obtain ⟨op, hop⟩ := hstep
      exact exec_keeps_flag_clear hop ih.1 ih.2
  simp only [exec, backFillZKSyncOSBaseTokenV31MigrationData, ne_eq, not_true_eq_false,
    ite_false, hclear₂.2, ite_true, Option.map_none]

open Contracts.L2AssetTracker.AccountingExample in
theorem BackfillSatisfiable : Properties.BackfillSatisfiable :=
  ⟨cfgEx, 100, _, _, _, 42, cfgEx_fresh_inv 100, by decide, rfl, rfl,
    AccountingInvariant cfgEx _ _ (cfgEx_fresh_inv 100)
      (Relation.ReflTransGen.tail (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
        ⟨.initL2 true, rfl⟩) ⟨.registerBaseDuringUpgrade, rfl⟩), rfl⟩

end Contracts.L2AssetTracker.History
