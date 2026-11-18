import EraSpec.Protocol.FlowAtomicityPerChain.Properties.Model
import EraSpec.Contracts.IndexedMerkleTree.Proofs.Model

/-!
# Proofs: flow atomicity with one commitment history per source chain

Certificates for `EraSpec.Protocol.FlowAtomicityPerChain.Properties.Model`.  The per-chain
statements apply `evolution_keys_mono` and `guardedEvolution_reclaimable_iff_absent` to each
leg's own chain; the countermodel is two one-insert histories.
-/

namespace AttackVectors.FlowAtomicityPerChain

open IMTAbstract

/-! ## The per-chain statements -/

theorem legs_present_at_later_snapshots_per_chain {S : ChainHistories}
    (hevo : ∀ c, Evolution (S c)) (flow : List ChainLeg) {n : UInt256 → ℕ}
    (hall : ∀ leg ∈ flow, leg.value ∈ keys (S leg.chain (n leg.chain))) :
    ∀ leg ∈ flow, ∀ j, n leg.chain ≤ j → leg.value ∈ keys (S leg.chain j) :=
  fun leg hleg _ hj => evolution_keys_mono (hevo leg.chain) hj (hall leg hleg)

theorem flow_outcome_dichotomy_per_chain {S : ChainHistories}
    (hge : ∀ c, GuardedEvolution (S c)) (hgen : ∀ c, S c 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    (flow : List ChainLeg) (hnz : ∀ leg ∈ flow, leg.value ≠ 0) (j : UInt256 → ℕ) :
    ∀ leg ∈ flow,
      (leg.value ∈ keys (S leg.chain (j leg.chain))
          ∨ ∃ W ∈ S leg.chain (j leg.chain), W.key < leg.value
              ∧ (W.nextKey = 0 ∨ leg.value < W.nextKey))
        ∧ ¬ (leg.value ∈ keys (S leg.chain (j leg.chain))
          ∧ ∃ W ∈ S leg.chain (j leg.chain), W.key < leg.value
              ∧ (W.nextKey = 0 ∨ leg.value < W.nextKey)) := by
  intro leg hleg
  have hiff := guardedEvolution_reclaimable_iff_absent (hge leg.chain) (hgen leg.chain)
    (j := j leg.chain) (hnz leg hleg)
  constructor
  · by_cases hmem : leg.value ∈ keys (S leg.chain (j leg.chain))
    · exact Or.inl hmem
    · exact Or.inr (hiff.mpr hmem)
  · rintro ⟨hmem, hwit⟩
    exact hiff.mp hwit hmem

/-! ## The two-chain instance -/

lemma oneInsertHistory_succ (v : UInt256) (k : ℕ) :
    oneInsertHistory v (k + 1) = imtInsert {⟨0, 0⟩} ⟨0, 0⟩ v := rfl

lemma not_mem_keys_genesis {v : UInt256} (hv : v ≠ 0) :
    v ∉ keys ({⟨0, 0⟩} : Finset AbsLeaf) := by
  intro hmem
  obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_singleton] at hL
  rw [hL] at hLkey
  exact hv hLkey.symm

lemma oneInsertHistory_guarded {v : UInt256} (hv : v ≠ 0) :
    GuardedEvolution (oneInsertHistory v) := by
  intro n
  cases n with
  | zero =>
    right
    exact ⟨⟨0, 0⟩, v, Finset.mem_singleton_self _, Fin.pos_of_ne_zero hv, Or.inl rfl,
      not_mem_keys_genesis hv, rfl⟩
  | succ k =>
    left
    rfl

lemma oneInsertHistory_evolution {v : UInt256} (hv : v ≠ 0) :
    Evolution (oneInsertHistory v) := by
  intro n
  cases n with
  | zero =>
    right
    exact ⟨⟨0, 0⟩, v, Finset.mem_singleton_self _, Fin.pos_of_ne_zero hv, Or.inl rfl, rfl⟩
  | succ k =>
    left
    rfl

lemma mem_keys_oneInsertHistory_one {v w : UInt256} (hw : w ≠ 0) :
    w ∈ keys (oneInsertHistory v 1) ↔ w = v := by
  rw [oneInsertHistory_succ v 0]
  constructor
  · intro hmem
    rcases (mem_keys_imtInsert (Finset.mem_singleton_self _)).mp hmem with heq | hmem0
    · exact heq
    · exact absurd hmem0 (not_mem_keys_genesis hw)
  · rintro rfl
    exact imtInsert_key_mem (Finset.mem_singleton_self _)

lemma twoChainHistories_zero (a b : UInt256) : twoChainHistories a b 0 = oneInsertHistory a := by
  simp [twoChainHistories]

lemma twoChainHistories_other {a b c : UInt256} (hc : c ≠ 0) :
    twoChainHistories a b c = oneInsertHistory b := by
  simp [twoChainHistories, hc]

theorem shared_history_misreads_two_chain_flow {a b : UInt256} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ≠ b) :
    (∀ c, GuardedEvolution (twoChainHistories a b c) ∧ Evolution (twoChainHistories a b c)
        ∧ twoChainHistories a b c 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
      ∧ (∀ leg ∈ twoChainFlow a b, leg.value ≠ 0
          ∧ leg.value ∈ keys (twoChainHistories a b leg.chain 1))
      ∧ b ∉ keys (twoChainHistories a b 0 1)
      ∧ (∃ W ∈ twoChainHistories a b 0 1, W.key < b ∧ (W.nextKey = 0 ∨ b < W.nextKey))
      ∧ twoChainHistories a b 0 ≠ twoChainHistories a b 1 := by
  have h10 : (1 : UInt256) ≠ 0 := by decide
  have hb0 : b ∉ keys (twoChainHistories a b 0 1) := by
    rw [twoChainHistories_zero]
    intro hmem
    exact hab ((mem_keys_oneInsertHistory_one hb).mp hmem).symm
  refine ⟨?_, ?_, hb0, ?_, ?_⟩
  · intro c
    by_cases hc : c = 0
    · subst hc
      rw [twoChainHistories_zero]
      exact ⟨oneInsertHistory_guarded ha, oneInsertHistory_evolution ha, rfl⟩
    · rw [twoChainHistories_other hc]
      exact ⟨oneInsertHistory_guarded hb, oneInsertHistory_evolution hb, rfl⟩
  · intro leg hleg
    simp only [twoChainFlow, List.mem_cons, List.not_mem_nil, or_false] at hleg
    rcases hleg with rfl | rfl
    · refine ⟨ha, ?_⟩
      show a ∈ keys (twoChainHistories a b 0 1)
      rw [twoChainHistories_zero]
      exact (mem_keys_oneInsertHistory_one ha).mpr rfl
    · refine ⟨hb, ?_⟩
      show b ∈ keys (twoChainHistories a b 1 1)
      rw [twoChainHistories_other h10]
      exact (mem_keys_oneInsertHistory_one hb).mpr rfl
  · have hgen : twoChainHistories a b 0 0 = ({⟨0, 0⟩} : Finset AbsLeaf) := by
      rw [twoChainHistories_zero]; rfl
    have hge : GuardedEvolution (twoChainHistories a b 0) := by
      rw [twoChainHistories_zero]; exact oneInsertHistory_guarded ha
    exact (guardedEvolution_reclaimable_iff_absent hge hgen hb).mpr hb0
  · intro heq
    have h1 := congrFun heq 1
    rw [twoChainHistories_zero, twoChainHistories_other h10] at h1
    have hmem : a ∈ keys (oneInsertHistory a 1) := (mem_keys_oneInsertHistory_one ha).mpr rfl
    rw [h1] at hmem
    exact hab ((mem_keys_oneInsertHistory_one ha).mp hmem)

end AttackVectors.FlowAtomicityPerChain

/-! ## Certificates -/

namespace AttackVectors.FlowAtomicityPerChain

theorem LegsPresentAtLaterSnapshotsPerChain : Properties.LegsPresentAtLaterSnapshotsPerChain :=
  fun _ hevo flow _ hall => legs_present_at_later_snapshots_per_chain hevo flow hall
theorem FlowOutcomeDichotomyPerChain : Properties.FlowOutcomeDichotomyPerChain :=
  fun _ hge hgen flow hnz j => flow_outcome_dichotomy_per_chain hge hgen flow hnz j
theorem SharedHistoryMisreadsTwoChainFlow : Properties.SharedHistoryMisreadsTwoChainFlow :=
  fun _ _ ha hb hab => shared_history_misreads_two_chain_flow ha hb hab

end AttackVectors.FlowAtomicityPerChain
