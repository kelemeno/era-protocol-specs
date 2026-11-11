import EraSpec.Contracts.AtomicInteropProof.Properties.TimeoutSoundnessStrong
import EraSpec.Contracts.AtomicInteropProof.Proofs.TimeoutSoundness
import Mathlib.Tactic

/-!
# Proofs: the dangerous root swap, with every end-branch premise in place

Certificates for `EraSpec.Contracts.AtomicInteropProof.Properties.TimeoutSoundnessStrong`.  The
soundness directions are the existing `TimeoutSoundness` theorems applied to the gate.  The
countermodels all live on one explicit history, `rootSwapHistory`.  It is append-only and
time-ordered, so neither of those premises explains the failure.
-/

namespace AttackVectors.TimeoutSoundness


/-! ## The countermodel history -/

private lemma rootSwapHistory_appendOnly : AppendOnly rootSwapHistory := by
  intro n
  cases n <;> simp [rootSwapHistory]

private lemma rootSwapHistory_timeOrdered : TimeOrdered rootSwapHistory := by
  intro a b hab
  simp only [rootSwapHistory]
  split_ifs <;> omega

private lemma rootSwapHistory_time_one : rootSwapHistory.time 1 = 0 := by
  simp [rootSwapHistory]

private lemma rootSwapHistory_time_late {m : ℕ} (hm : 1 < m) : rootSwapHistory.time m = 5 := by
  simp only [rootSwapHistory]
  split_ifs <;> omega

/-- Every batch after `1` settles at the root time `5`: `hlast` holds for `B = 1`, `T = 5`. -/
private lemma rootSwapHistory_hlast : ∀ m, 1 < m → 5 ≤ rootSwapHistory.time m := by
  intro m hm
  rw [rootSwapHistory_time_late hm]

private lemma rootSwapHistory_begin_one : beginSet rootSwapHistory 1 = ∅ := by
  simp [beginSet, rootSwapHistory]

private lemma rootSwapHistory_end_one : rootSwapHistory.endSet 1 = {0} := by
  simp [rootSwapHistory]

private lemma rootSwapHistory_begin_two : beginSet rootSwapHistory 2 = {0} := by
  simp [beginSet, rootSwapHistory]

private lemma one_ne_zero_word : (1 : UInt256) ≠ 0 := by decide

/-- Every END set of the countermodel is inside `{0}`. -/
private lemma rootSwapHistory_endSet_sub (n : ℕ) : rootSwapHistory.endSet n ⊆ {0} := by
  simp only [rootSwapHistory]
  split_ifs <;> simp

/-- Value `0` finalizes by deadline `0`: it is in batch `1`'s END set, and batch `1` settles at `0`. -/
private lemma rootSwapHistory_finalized_zero : FinalizedBy rootSwapHistory 0 0 :=
  ⟨1, by rw [rootSwapHistory_time_one], by rw [rootSwapHistory_end_one]; exact Finset.mem_singleton_self _⟩

/-- Value `1` is never inserted, so it never finalizes. -/
private lemma rootSwapHistory_not_finalized_one (D : ℕ) : ¬ FinalizedBy rootSwapHistory D 1 := by
  rintro ⟨B, -, hmem⟩
  exact one_ne_zero_word (Finset.mem_singleton.mp (rootSwapHistory_endSet_sub B hmem))

/-- The swapped gate (end flag, begin leaf) accepts batch `1` for EVERY value `v`: batch `1`'s
begin set is empty. -/
private lemma rootSwapHistory_swapped_gate (v : UInt256) :
    TimeoutGateAt rootSwapHistory 0 5 false .beginRoot 1 v := by
  refine ⟨by norm_num, ⟨?_, rootSwapHistory_hlast⟩, ?_⟩
  · rw [rootSwapHistory_time_one]
  · show v ∉ beginSet rootSwapHistory 1
    rw [rootSwapHistory_begin_one]
    exact Finset.notMem_empty v


/-! ## The swap with every end-branch premise -/

theorem end_branch_begin_root_admits_finalized :
    Properties.end_branch_begin_root_admits_finalized := by
  unfold Properties.end_branch_begin_root_admits_finalized
  refine ⟨rootSwapHistory, 0, 5, 0, 1, rootSwapHistory_appendOnly, rootSwapHistory_timeOrdered,
    ?_, by norm_num, rootSwapHistory_hlast, ?_, ?_⟩
  · rw [rootSwapHistory_time_one]
  · rw [rootSwapHistory_begin_one]
    exact Finset.notMem_empty _
  · rw [rootSwapHistory_end_one]
    exact Finset.mem_singleton_self _


theorem end_branch_begin_root_passes_onchain_checks :
    Properties.end_branch_begin_root_passes_onchain_checks := by
  unfold Properties.end_branch_begin_root_passes_onchain_checks
  refine ⟨rootSwapHistory, 1, 2, 2, 0, 5, 0, rootSwapHistory_appendOnly,
    rootSwapHistory_timeOrdered, by norm_num, ?_, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · rw [rootSwapHistory_time_one]
  · -- `RightEmpty 1 2 2`: at level `0` leaf `1` is a RIGHT child, so nothing is checked there.
    -- At level `1` its parent (node `0`) is a LEFT child, and the right sibling subtree, leaves
    -- `[2, 4)`, is checked and found unfilled.  So the zero-cascade check does real work here.
    intro k hk hleft j hj1 hj2
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · norm_num at hleft
    · norm_num at hj1
      exact hj1
  · -- every batch outside the root (index `≥ 2`) settles at the root time `5`
    intro m hm
    exact rootSwapHistory_hlast m (by simp only [not_lt] at hm; omega)
  · rw [rootSwapHistory_begin_one]
    exact Finset.notMem_empty _
  · rw [rootSwapHistory_end_one]
    exact Finset.mem_singleton_self _


/-! ## Why the original witness does not isolate the swap -/

private lemma allInTimeHistory_appendOnly : AppendOnly allInTimeHistory := by
  intro n
  cases n <;> simp [allInTimeHistory]

private lemma allInTimeHistory_timeOrdered : TimeOrdered allInTimeHistory := by
  intro a b _
  simp [allInTimeHistory]


theorem end_branch_needs_hlast :
    Properties.end_branch_needs_hlast := by
  unfold Properties.end_branch_needs_hlast
  -- the correct END root of batch `0` lacks `0`, but the in-time batch `1` contains it
  refine ⟨allInTimeHistory_appendOnly, allInTimeHistory_timeOrdered, 0, 1, 0, 0,
    by simp [allInTimeHistory], by norm_num, by simp [allInTimeHistory],
    ⟨1, by simp [allInTimeHistory], by simp [allInTimeHistory]⟩⟩


theorem allInTimeHistory_no_hlast :
    Properties.allInTimeHistory_no_hlast := by
  unfold Properties.allInTimeHistory_no_hlast
  intro B D T hDT hlast
  -- the batch after `B` settles at time `0`, which is not after the deadline
  have hnext := hlast (B + 1) (Nat.lt_succ_self B)
  simp only [allInTimeHistory] at hnext
  omega


/-! ## The gate-level statements -/

theorem timeoutGate_end_flag_begin_leaf_admits_finalized :
    Properties.timeoutGate_end_flag_begin_leaf_admits_finalized := by
  unfold Properties.timeoutGate_end_flag_begin_leaf_admits_finalized
  refine ⟨rootSwapHistory, 0, 5, 1, 0, rootSwapHistory_appendOnly, rootSwapHistory_timeOrdered,
    rootSwapHistory_swapped_gate 0, rootSwapHistory_finalized_zero, ?_⟩
  -- the deployed gate authenticates the END leaf for the end flag, and `0` is in batch `1`'s end
  rintro ⟨-, -, habs⟩
  apply habs
  show (0 : UInt256) ∈ rootSwapHistory.endSet 1
  rw [rootSwapHistory_end_one]
  exact Finset.mem_singleton_self _


theorem timeoutGate_end_flag_begin_leaf_iff_batch_insertion {H : BatchHistory}
    (hao : AppendOnly H) (D T n : ℕ) (v : UInt256) :
    Properties.timeoutGate_end_flag_begin_leaf_iff_batch_insertion (H := H) hao D T n v := by
  unfold Properties.timeoutGate_end_flag_begin_leaf_iff_batch_insertion
  constructor
  · rintro ⟨⟨hroot, ⟨hintime, hlast⟩, habs⟩, ⟨B', hB', hmem'⟩⟩
    -- a value that finalized in time is in the END set of the last in-time batch `n`
    have hend : v ∈ H.endSet n :=
      finalized_blocks_end_timeout hao hintime hroot hlast hB' hmem'
    exact ⟨hroot, ⟨hintime, hlast⟩, Finset.mem_sdiff.mpr ⟨hend, habs⟩⟩
  · rintro ⟨hroot, ⟨hintime, hlast⟩, hsd⟩
    obtain ⟨hend, hbegin⟩ := Finset.mem_sdiff.mp hsd
    exact ⟨⟨hroot, ⟨hintime, hlast⟩, hbegin⟩, ⟨n, hintime, hend⟩⟩


theorem timeoutGate_end_flag_begin_leaf_iff_witness :
    Properties.timeoutGate_end_flag_begin_leaf_iff_witness := by
  unfold Properties.timeoutGate_end_flag_begin_leaf_iff_witness
  exact ⟨rootSwapHistory, 0, 5, 1, 0, 1, rootSwapHistory_appendOnly, rootSwapHistory_timeOrdered,
    rootSwapHistory_swapped_gate 0, rootSwapHistory_finalized_zero,
    rootSwapHistory_swapped_gate 1, rootSwapHistory_not_finalized_one 0⟩


/-- The three sound combinations, proved once: the deployed begin branch, the harmless swap,
and the deployed end branch. -/
private lemma timeoutGate_sound_of_ne {b : Bool} {leaf : ImtRootLeaf}
    (hcomb : b = true ∨ leaf = .endRoot) {H : BatchHistory} (hao : AppendOnly H)
    (hto : TimeOrdered H) {D T n : ℕ} {v : UInt256}
    (hacc : TimeoutGateAt H D T b leaf n v) : ¬ FinalizedBy H D v := by
  rintro ⟨B, hB, hmem⟩
  obtain ⟨hroot, hchecks, habs⟩ := hacc
  cases b with
  | true =>
    -- the begin branch: a late batch, against either leaf
    have hlate : D < H.time n := hchecks
    cases leaf with
    | beginRoot =>
      exact begin_absence_implies_never_finalized hao hto hlate habs B hB hmem
    | endRoot =>
      exact begin_branch_with_end_root_sound hao hto hlate habs B hB hmem
  | false =>
    -- the end branch: only the END leaf is allowed here
    have hleaf : leaf = .endRoot := by
      rcases hcomb with h | h
      · exact absurd h (by decide)
      · exact h
    subst hleaf
    obtain ⟨hintime, hlast⟩ := hchecks
    exact end_absence_implies_never_finalized hao hintime hroot hlast habs B hB hmem


theorem timeoutGate_deployed_leaf_sound {H : BatchHistory}
    (hao : AppendOnly H) (hto : TimeOrdered H) {D T n : ℕ} {b : Bool} {v : UInt256}
    (hacc : TimeoutGateAt H D T b (deployedLeaf b) n v) :
    Properties.timeoutGate_deployed_leaf_sound (H := H) hao hto (D := D) (T := T) (n := n)
      (b := b) (v := v) hacc := by
  unfold Properties.timeoutGate_deployed_leaf_sound
  refine timeoutGate_sound_of_ne ?_ hao hto hacc
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl


theorem timeoutGate_deployed_leaf_not_dead :
    Properties.timeoutGate_deployed_leaf_not_dead := by
  unfold Properties.timeoutGate_deployed_leaf_not_dead
  refine ⟨rootSwapHistory, 0, 5, 1, 0, rootSwapHistory_appendOnly, rootSwapHistory_timeOrdered,
    ⟨2, ?_⟩, ⟨1, ?_⟩, rootSwapHistory_not_finalized_one 0, rootSwapHistory_finalized_zero⟩
  · -- begin branch against the late batch `2`, whose begin set is `{0}`
    refine ⟨by norm_num, ?_, ?_⟩
    · show 0 < rootSwapHistory.time 2
      rw [rootSwapHistory_time_late (by norm_num)]
      norm_num
    · show (1 : UInt256) ∉ beginSet rootSwapHistory 2
      rw [rootSwapHistory_begin_two, Finset.mem_singleton]
      exact one_ne_zero_word
  · -- end branch against the last in-time batch `1`, whose end set is `{0}`
    refine ⟨by norm_num, ⟨?_, rootSwapHistory_hlast⟩, ?_⟩
    · rw [rootSwapHistory_time_one]
    · show (1 : UInt256) ∉ rootSwapHistory.endSet 1
      rw [rootSwapHistory_end_one, Finset.mem_singleton]
      exact one_ne_zero_word


theorem timeoutGate_sound_iff_not_end_flag_begin_leaf (b : Bool) (leaf : ImtRootLeaf) :
    Properties.timeoutGate_sound_iff_not_end_flag_begin_leaf b leaf := by
  unfold Properties.timeoutGate_sound_iff_not_end_flag_begin_leaf
  constructor
  · intro hsound
    by_contra hcomb
    have hb : b = false := by
      cases b
      · rfl
      · exact absurd (Or.inl rfl) hcomb
    have hleaf : leaf = .beginRoot := by
      cases leaf
      · rfl
      · exact absurd (Or.inr rfl) hcomb
    subst hb
    subst hleaf
    exact hsound rootSwapHistory 0 5 1 0 rootSwapHistory_appendOnly rootSwapHistory_timeOrdered
      (rootSwapHistory_swapped_gate 0) rootSwapHistory_finalized_zero
  · intro hcomb H D T n v hao hto hacc
    exact timeoutGate_sound_of_ne hcomb hao hto hacc


end AttackVectors.TimeoutSoundness
