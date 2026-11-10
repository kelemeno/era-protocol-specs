import EraSpec.Contracts.L2InteropCommitmentTree.Properties.HintSearch
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Model
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Reaches

/-! # Proofs: the hint search -/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-! ### Termination

The measure: the occupied leaves whose value lies strictly between the current
leaf's value and `v`.  Each hop lands on one of them and removes it, because the
interval's lower endpoint rises to that leaf's own value. -/

/-- The termination measure. -/
private def above (T : Tree) (v : UInt256) (i : ℕ) : Finset ℕ :=
  (Finset.range T.leafCount).filter
    (fun k => (T.leaf i).value < (T.leaf k).value ∧ (T.leaf k).value < v)

private lemma mem_above {T : Tree} {v : UInt256} {i k : ℕ} :
    k ∈ above T v i ↔
      k < T.leafCount ∧ (T.leaf i).value < (T.leaf k).value ∧ (T.leaf k).value < v := by
  simp [above, Finset.mem_filter, Finset.mem_range, and_assoc]

private lemma above_card_le (T : Tree) (v : UInt256) (i : ℕ) :
    (above T v i).card ≤ T.leafCount := by
  have h : above T v i ⊆ Finset.range T.leafCount :=
    fun k hk => Finset.mem_range.mpr (mem_above.mp hk).1
  simpa using Finset.card_le_card h

/-- The hop target is one of the leaves the measure counts: `linkAgree` puts it in
range with value `nextValue`, and `WindowPos` puts that value above the current
leaf's own. -/
private lemma next_mem_above {T : Tree} (hV : Valid T) {v : UInt256} {i : ℕ}
    (hi : i < T.leafCount) (hnz : (T.leaf i).nextValue ≠ 0)
    (hlt : (T.leaf i).nextValue < v) : (T.leaf i).nextIndex ∈ above T v i := by
  obtain ⟨hb, hval⟩ := hV.linkAgree i hi hnz
  have hpos : (T.leaf i).value < (T.leaf i).nextValue := by
    rcases hV.absSound.2.2.2 (lowAbs T i) (lowAbs_mem hi) with h0 | hgt
    · exact absurd (h0 : (T.leaf i).nextValue = 0) hnz
    · exact hgt
  exact mem_above.mpr ⟨hb, by rw [hval]; exact hpos, by rw [hval]; exact hlt⟩

/-- …and the measure strictly decreases, because the target is above the current
leaf but not above itself. -/
private lemma above_card_lt {T : Tree} (hV : Valid T) {v : UInt256} {i : ℕ}
    (hi : i < T.leafCount) (hnz : (T.leaf i).nextValue ≠ 0)
    (hlt : (T.leaf i).nextValue < v) :
    (above T v (T.leaf i).nextIndex).card < (above T v i).card := by
  have hn := next_mem_above hV hi hnz hlt
  have hsub : above T v (T.leaf i).nextIndex ⊆ above T v i := by
    intro k hk
    obtain ⟨hk1, hk2, hk3⟩ := mem_above.mp hk
    exact mem_above.mpr ⟨hk1, lt_trans (mem_above.mp hn).2.1 hk2, hk3⟩
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_of_subset hsub]
  exact ⟨(T.leaf i).nextIndex, hn, fun hmem => absurd (mem_above.mp hmem).2.1 (lt_irrefl _)⟩

/-- **THE SEARCH RETURNS WHENEVER THE FUEL COVERS THE MEASURE.** -/
theorem lowSearch_of_fuel_ge {T : Tree} (hV : Valid T) {v : UInt256} :
    ∀ (fuel i : ℕ), i < T.leafCount → (above T v i).card ≤ fuel →
      ∃ j, lowSearch T v fuel i = some j := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hi hcard
    unfold lowSearch
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · exfalso
      have hpos : 0 < (above T v i).card :=
        Finset.card_pos.mpr ⟨_, next_mem_above hV hi hc.1 hc.2⟩
      omega
    · rw [if_neg hc]; exact ⟨i, rfl⟩
  | succ fuel ih =>
    intro i hi hcard
    unfold lowSearch
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [if_pos hc]
      obtain ⟨hb, _⟩ := hV.linkAgree i hi hc.1
      have hdec := above_card_lt hV hi hc.1 hc.2
      exact ih _ hb (by omega)
    · rw [if_neg hc]; exact ⟨i, rfl⟩

/-- **THE SEARCH TERMINATES.**  `leafCount` hops always suffice. -/
theorem lowSearch_terminates {T : Tree} (hV : Valid T) (v : UInt256) (i : ℕ)
    (hi : i < T.leafCount) : ∃ j, lowSearch T v T.leafCount i = some j :=
  lowSearch_of_fuel_ge hV _ i hi (above_card_le T v i)

/-- **THE REVERT IS REACHABLE.**  Minimal witness that a fixed fuel is not enough
in general: with zero hops the walk reverts, with one it succeeds. -/
theorem lowSearch_can_revert {a v : UInt256} (ha : 0 < a) (hav : a < v) :
    lowSearch (insert setup a 0) v 0 0 = none
      ∧ lowSearch (insert setup a 0) v 1 0 = some 1 := by
  have h0 : ((insert setup a 0).leaf 0).nextValue = a := by simp [insert, setup]
  have h0i : ((insert setup a 0).leaf 0).nextIndex = 1 := by simp [insert, setup]
  have h1 : ((insert setup a 0).leaf 1).nextValue = 0 := by simp [insert, setup]
  have hcond : ((insert setup a 0).leaf 0).nextValue ≠ 0
      ∧ ((insert setup a 0).leaf 0).nextValue < v := by
    rw [h0]; exact ⟨ne_of_gt ha, hav⟩
  refine ⟨?_, ?_⟩
  · unfold lowSearch; rw [if_pos hcond]
  · unfold lowSearch
    rw [if_pos hcond, h0i]
    unfold lowSearch
    rw [if_neg (by simp [h1])]

/-- The contract's `insert` flow establishes the guard at the index the search
returns. -/
theorem search_yields_guard {T : Tree} (hV : Valid T) {v : UInt256} {fuel i j : ℕ}
    (hinit : Initialized T) (hv : v ≠ 0) (hfresh : T.valueToIndex v = 0)
    (hi : i < T.leafCount) (hlow : (T.leaf i).value < v) (hs : lowSearch T v fuel i = some j) :
    InsertGuard T v j :=
  ⟨hinit, hv, hfresh, (lowSearch_sound hV fuel i j hi hlow hs).1,
   (lowSearch_sound hV fuel i j hi hlow hs).2, lowSearch_window fuel i j hs⟩

/-- The genesis insert: any nonzero value goes in through the sentinel. -/
theorem setup_insertGuard {a : UInt256} (ha : 0 < a) : InsertGuard setup a 0 := by
  refine ⟨?_, (ne_of_lt ha).symm, rfl, ?_, ha, Or.inl rfl⟩
  · show (1 : ℕ) ≠ 0; omega
  · show (0 : ℕ) < 1; omega

theorem SearchYieldsGuard : Properties.SearchYieldsGuard := @search_yields_guard
theorem LowSearchTerminates : Properties.LowSearchTerminates := @lowSearch_terminates
theorem LowSearchCanRevert : Properties.LowSearchCanRevert := @lowSearch_can_revert


private lemma chain_guard (n : ℕ) (hn : n < 6) :
    InsertGuard (chainTree n) ((n + 1 : ℕ) : UInt256) n := by
  interval_cases n <;> exact ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, by decide⟩

private lemma chain_reaches : ∀ n, n ≤ 6 → Reaches setup (chainTree n)
  | 0, _ => .refl
  | n + 1, hn => .tail (chain_reaches n (by omega)) (chain_guard n (by omega))

theorem HonestInsertRevertsAtDeployedFuel : Properties.HonestInsertRevertsAtDeployedFuel :=
  ⟨chain_reaches 6 le_rfl, by decide, by decide, by decide, by decide,
    ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, by decide⟩⟩

end Contracts.InteropCommitmentTree
