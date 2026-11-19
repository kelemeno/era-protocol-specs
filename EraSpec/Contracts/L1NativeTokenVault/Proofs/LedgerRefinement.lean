import EraSpec.Contracts.L1NativeTokenVault.Properties.LedgerRefinement

/-! # Proofs: the `b17415d20` vault ledger refines the `bridgedOut`-only models -/

namespace Contracts.L1NativeTokenVault.LedgerRefinement

open Contracts.L1NativeTokenVault.InteropPool

/-! ## What a successful hook does to `bridgedOut` -/

theorem toChain_spec {l1 : ChainId} {s s' : PoolSys} {c a : ChainId} {x : UInt256} {o : ChainId}
    (h : handleBridgeToChain l1 s c a x o = some s') :
    (o = l1 → s.bridgedOut a + x.val < UInt256.size) ∧
    ∀ b, s'.bridgedOut b = if o = l1 ∧ b = a then s.bridgedOut a + x.val else s.bridgedOut b := by
  unfold handleBridgeToChain at h
  dsimp only at h
  by_cases ho : o = l1
  · have hfit : s.bridgedOut a + x.val < UInt256.size := by
      by_contra hc
      rw [if_pos ⟨ho, Nat.le_of_not_lt hc⟩] at h
      cases h
    rw [if_neg (fun hc => absurd hc.2 (Nat.not_le_of_lt hfit))] at h
    refine ⟨fun _ => hfit, fun b => ?_⟩
    split_ifs at h <;> cases h <;> simp [setAt, ho]
  · rw [if_neg (fun hc => ho hc.1)] at h
    refine ⟨fun hc => absurd hc ho, fun b => ?_⟩
    split_ifs at h <;> cases h <;> simp [ho]

theorem fromChain_spec {l1 : ChainId} {s s' : PoolSys} {c a : ChainId} {x : UInt256} {o : ChainId}
    (h : handleBridgeFromChain l1 s c a x o = some s') :
    (o = l1 → x.val ≤ s.bridgedOut a) ∧
    ∀ b, s'.bridgedOut b = if o = l1 ∧ b = a then s.bridgedOut a - x.val else s.bridgedOut b := by
  unfold handleBridgeFromChain at h
  dsimp only at h
  by_cases ho : o = l1
  · have hle : x.val ≤ s.bridgedOut a := by
      by_contra hc
      rw [if_pos ⟨ho, Nat.lt_of_not_le hc⟩] at h
      cases h
    rw [if_neg (fun hc => absurd hc.2 (Nat.not_lt_of_le hle))] at h
    refine ⟨fun _ => hle, fun b => ?_⟩
    split_ifs at h <;> cases h <;> simp [setAt, ho]
  · rw [if_neg (fun hc => ho hc.1)] at h
    refine ⟨fun hc => absurd hc ho, fun b => ?_⟩
    split_ifs at h <;> cases h <;> simp [ho]

/-! ## `L1Ledger` -/

theorem PoolToChainIsL1ToChain : Properties.PoolToChainIsL1ToChain := by
  intro l1 s s' c a x o acc hm ho h
  obtain ⟨hfit, hb⟩ := toChain_spec h
  unfold NativeTokenVaultBase.l1ToChain
  by_cases hol : o = l1
  · rw [if_pos (ho.trans hol)]
    have hfit' := hfit hol
    have hc : L2AssetTracker.checkedAdd (acc.bridgedOut a) x =
        some ⟨s.bridgedOut a + x.val, hfit'⟩ := by
      unfold L2AssetTracker.checkedAdd
      rw [dif_pos (by rw [hm a]; exact hfit')]
      simp [hm a]
    rw [hc]
    refine ⟨_, rfl, rfl, fun b => ?_⟩
    dsimp only
    rw [hb b]
    by_cases hba : b = a
    · subst hba
      rw [if_pos ⟨hol, rfl⟩, Function.update_self]
    · rw [if_neg (fun hc => hba hc.2), Function.update_of_ne hba]
      exact hm b
  · rw [if_neg (by rw [ho]; exact hol)]
    exact ⟨acc, rfl, rfl, fun b => by rw [hb b, if_neg (fun hc => hol hc.1)]; exact hm b⟩

theorem PoolFromChainIsL1FromChain : Properties.PoolFromChainIsL1FromChain := by
  intro l1 s s' c a x o acc hm ho h
  obtain ⟨hle, hb⟩ := fromChain_spec h
  unfold NativeTokenVaultBase.l1FromChain
  by_cases hol : o = l1
  · rw [if_pos (ho.trans hol)]
    have hle' := hle hol
    have hc : L2AssetTracker.checkedSub (acc.bridgedOut a) x =
        some ⟨s.bridgedOut a - x.val, by have := (acc.bridgedOut a).isLt; rw [hm a] at this; omega⟩ := by
      unfold L2AssetTracker.checkedSub
      rw [dif_pos (by rw [hm a]; exact hle')]
      simp [hm a]
    rw [hc]
    refine ⟨_, rfl, rfl, fun b => ?_⟩
    dsimp only
    rw [hb b]
    by_cases hba : b = a
    · subst hba
      rw [if_pos ⟨hol, rfl⟩, Function.update_self]
    · rw [if_neg (fun hc => hba hc.2), Function.update_of_ne hba]
      exact hm b
  · rw [if_neg (by rw [ho]; exact hol)]
    exact ⟨acc, rfl, rfl, fun b => by rw [hb b, if_neg (fun hc => hol hc.1)]; exact hm b⟩

/-! ## The registry model -/

theorem PoolHooksAreRegistryLedgerSteps : Properties.PoolHooksAreRegistryLedgerSteps := by
  intro l1 s s' c a x o W ho hm
  unfold RegistryLedgerMatches at hm ⊢
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨_, hb⟩ := toChain_spec h
    funext b
    rw [hb b]
    unfold NativeTokenVault.bridgeOut NativeTokenVault.Native
    by_cases hol : o = l1
    · rw [if_pos (ho.trans hol)]
      simp only [NativeTokenVault.upd, hol, true_and, hm]
    · rw [if_neg (by rw [ho]; exact hol), if_neg (fun hc => hol hc.1), hm]
  · obtain ⟨hle, hb⟩ := fromChain_spec h
    refine ⟨fun hn => ?_, ?_⟩
    · rw [hm]; exact hle (ho.symm.trans hn)
    · funext b
      rw [hb b]
      unfold NativeTokenVault.bridgeIn NativeTokenVault.Native
      by_cases hol : o = l1
      · rw [if_pos (ho.trans hol)]
        simp only [NativeTokenVault.upd, hol, true_and, hm]
      · rw [if_neg (by rw [ho]; exact hol), if_neg (fun hc => hol hc.1), hm]

theorem PoolPopulateIsPopulateAtHead : Properties.PoolPopulateIsPopulateAtHead := by
  intro s s' a amount W legacy hl hm h
  unfold RegistryLedgerMatches at hm ⊢
  unfold populateBridgedOutEntry at h
  split_ifs at h
  cases h
  funext b
  simp only [NativeTokenVault.populateAtHead, NativeTokenVault.upd, setAt, hl, hm]

theorem PoolOtherCallsKeepBridgedOut : Properties.PoolOtherCallsKeepBridgedOut := by
  intro l1 call s s' hw h
  cases call with
  | toChain => exact absurd trivial hw
  | fromChain => exact absurd trivial hw
  | populateBridgedOut => exact absurd trivial hw
  | setBackfill c a x =>
    simp only [poolCall, setChainBalanceBackfill] at h
    split_ifs at h <;> cases h <;> rfl
  | markBackfilled c =>
    simp only [poolCall, markBackfilled] at h
    split_ifs at h <;> cases h <;> rfl
  | move c a =>
    simp only [poolCall, moveChainBalanceToInteropPool] at h
    split_ifs at h <;> cases h <;> rfl
  | enableInterop c =>
    simp only [poolCall, enableInterop] at h
    split_ifs at h <;> cases h <;> rfl
  | initializeUpgrade =>
    simp only [poolCall, initializeUpgrade] at h
    split_ifs at h <;> cases h <;> rfl
  | register c =>
    simp only [poolCall, registerChain] at h
    split_ifs at h <;> cases h <;> rfl

/-! ## Countermodel and witness -/

/-- A ledger with `3` of every asset bridged out and nothing else. -/
def poolEx : PoolSys :=
  ⟨fun _ => 3, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => false, fun _ => false, 2,
    fun _ => false, fun _ => false, fun _ => 0⟩

/-- The `L1Ledger` agreeing with `poolEx`, every asset native to chain `1`. -/
def accEx : NativeTokenVaultBase.L1Ledger := ⟨fun _ => 1, fun _ => 3⟩

theorem PerChainCapIsStricterThanL1Ledger : Properties.PerChainCapIsStricterThanL1Ledger :=
  ⟨1, poolEx, 6, 1, 3, accEx, fun _ => rfl, rfl, by decide, rfl, rfl⟩

theorem LedgerRefinementWitness : Properties.LedgerRefinementWitness :=
  ⟨1, poolEx, _, 6, 1, 3, accEx, fun _ => rfl, rfl, by decide, rfl, by decide⟩

end Contracts.L1NativeTokenVault.LedgerRefinement
