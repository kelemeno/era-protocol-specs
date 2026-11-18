import EraSpec.Contracts.L2InteropCommitmentTree.Properties.UnboundedSearchAtV35
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.HintSearch
import EraSpec.Contracts.IndexedMerkleTree.Proofs.UnboundedSearchAtV35

/-!
# Proofs: the v35 `insert` on the indexed list state

Proofs of `../Properties/UnboundedSearchAtV35.lean`.

* The lift of the loop is by induction: on the fuel for `SearchIsWalkV35`, on the walk for
  `WalkIsSearchV35`.  A concrete hop goes to `nextIndex`, which `Valid.linkAgree` puts in range
  with value `nextValue`; an abstract hop goes to a leaf with key `nextValue`, which is the leaf at
  `nextIndex` because the projection has unique keys.
* The fuel needed is the gap: an exiting run is a walk, whose length is the gap
  (`IMTAbstract.WalkLengthIsGapV35`); conversely the abstract walk exists
  (`IMTAbstract.WalkTerminatesV35`) and is a run with that much fuel, and more fuel changes
  nothing.
* The call results reduce to `search_yields_guard`, `insert_projects`, `insert_preserves_valid`
  and `dedup_gate_sound`.  An insert keeps every occupied index's value, which gives the
  hint-index results.
* The witnesses are computed by `decide` on the pin's `chainTree`.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-! ## The fuelled loop -/

private theorem lowSearch_zero_unboundedV35 (T : Tree) (v : UInt256) (i : ℕ) :
    lowSearch T v 0 i
      = if (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v then none else some i := rfl

private theorem lowSearch_succ_unboundedV35 (T : Tree) (v : UInt256) (fuel i : ℕ) :
    lowSearch T v (fuel + 1) i
      = if (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
          then lowSearch T v fuel (T.leaf i).nextIndex else some i := rfl

/-- One more hop of fuel does not change a returned index. -/
private theorem lowSearch_succ_of_some_unboundedV35 {T : Tree} {v : UInt256} :
    ∀ (fuel i j : ℕ), lowSearch T v fuel i = some j → lowSearch T v (fuel + 1) i = some j := by
  intro fuel
  induction fuel with
  | zero =>
    intro i j h
    rw [lowSearch_zero_unboundedV35] at h
    rw [lowSearch_succ_unboundedV35]
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [ite_eq_left hc] at h
      cases h
    · rw [ite_eq_right hc] at h ⊢
      exact h
  | succ fuel ih =>
    intro i j h
    rw [lowSearch_succ_unboundedV35] at h
    rw [lowSearch_succ_unboundedV35]
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [ite_eq_left hc] at h ⊢
      exact ih _ _ h
    · rw [ite_eq_right hc] at h ⊢
      exact h

/-- More fuel does not change a returned index. -/
private theorem lowSearch_mono_unboundedV35 {T : Tree} {v : UInt256} {f f' i j : ℕ}
    (h : lowSearch T v f i = some j) (hle : f ≤ f') : lowSearch T v f' i = some j := by
  induction hle with
  | refl => exact h
  | step _ ih => exact lowSearch_succ_of_some_unboundedV35 _ _ _ ih

theorem SearchExitsDeterministicV35 : Properties.SearchExitsDeterministicV35 := by
  rintro T v i j j' ⟨f₁, h₁⟩ ⟨f₂, h₂⟩
  rcases le_total f₁ f₂ with h | h
  · rw [lowSearch_mono_unboundedV35 h₁ h] at h₂
    exact Option.some.inj h₂
  · rw [lowSearch_mono_unboundedV35 h₂ h] at h₁
    exact (Option.some.inj h₁).symm

/-! ## The lift of the loop -/

theorem SearchIsWalkV35 : Properties.SearchIsWalkV35 := by
  intro T v fuel
  induction fuel with
  | zero =>
    intro i j hV hi h
    rw [lowSearch_zero_unboundedV35] at h
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [ite_eq_left hc] at h
      cases h
    · rw [ite_eq_right hc] at h
      cases h
      refine ⟨0, le_rfl, WalkV35.exit ?_⟩
      by_cases h0 : (T.leaf i).nextValue = 0
      · exact Or.inl h0
      · exact Or.inr (not_lt.mp fun hlt => hc ⟨h0, hlt⟩)
  | succ fuel ih =>
    intro i j hV hi h
    rw [lowSearch_succ_unboundedV35] at h
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [ite_eq_left hc] at h
      obtain ⟨hb, hval⟩ := hV.linkAgree i hi hc.1
      obtain ⟨n, hn, hw⟩ := ih _ _ hV hb h
      exact ⟨n + 1, by omega, WalkV35.hop hc.1 hc.2 (lowAbs_mem hb) hval hw⟩
    · rw [ite_eq_right hc] at h
      cases h
      refine ⟨0, Nat.zero_le _, WalkV35.exit ?_⟩
      by_cases h0 : (T.leaf i).nextValue = 0
      · exact Or.inl h0
      · exact Or.inr (not_lt.mp fun hlt => hc ⟨h0, hlt⟩)

/-- `WalkIsSearchV35`, with the walk's start generalised. -/
private theorem walk_is_search_unboundedV35 {T : Tree} (hV : Valid T) {v : UInt256} :
    ∀ {n : ℕ} {X W : AbsLeaf}, WalkV35 (toAbs T) v n X W →
      ∀ i, i < T.leafCount → lowAbs T i = X →
        ∃ j, j < T.leafCount ∧ lowSearch T v n i = some j ∧ lowAbs T j = W := by
  intro n X W hw
  induction hw with
  | exit hx =>
    intro i hi hX
    subst hX
    refine ⟨i, hi, ?_, rfl⟩
    rw [lowSearch_zero_unboundedV35, ite_eq_right]
    rintro ⟨hnz, hlt⟩
    rcases hx with h | h
    · exact hnz h
    · exact absurd hlt (not_lt.mpr h)
  | @hop m Y L Z hnz hlt hL hkey _ ih =>
    intro i hi hY
    subst hY
    have hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v := ⟨hnz, hlt⟩
    obtain ⟨hb, hval⟩ := hV.linkAgree i hi hnz
    have hLeq : lowAbs T (T.leaf i).nextIndex = L := by
      apply hV.absSound.2.1 _ (lowAbs_mem hb) _ hL
      show (T.leaf (T.leaf i).nextIndex).value = L.key
      rw [hval, hkey]
      rfl
    obtain ⟨j, hj, hs, hjW⟩ := ih _ hb hLeq
    exact ⟨j, hj, by rw [lowSearch_succ_unboundedV35, ite_eq_left hc]; exact hs, hjW⟩

theorem WalkIsSearchV35 : Properties.WalkIsSearchV35 := fun _ _ _ i _ hV hi hw =>
  walk_is_search_unboundedV35 hV hw i hi rfl

theorem SearchFuelIsGapV35 : Properties.SearchFuelIsGapV35 := by
  intro T v fuel i hV hi
  have hs := hV.absSound
  have hmem := lowAbs_mem (T := T) hi
  constructor
  · rintro ⟨j, h⟩
    obtain ⟨n, hn, hw⟩ := SearchIsWalkV35 T v fuel i j hV hi h
    have hgap := WalkLengthIsGapV35 _ v n _ _ hs.1 hs.2.2.2 hmem hw
    have : (gapKeysV35 (toAbs T) (T.leaf i).value v).card = n := hgap.symm
    omega
  · intro hle
    obtain ⟨n, W, hw, _⟩ := WalkTerminatesV35 _ v _ hs.2.2.1 hs.2.2.2 hmem
    have hgap := WalkLengthIsGapV35 _ v n _ _ hs.1 hs.2.2.2 hmem hw
    obtain ⟨j, _, h, _⟩ := WalkIsSearchV35 T v n i W hV hi hw
    have hn : n ≤ fuel := by
      have : (gapKeysV35 (toAbs T) (T.leaf i).value v).card = n := hgap.symm
      omega
    exact ⟨j, lowSearch_mono_unboundedV35 h hn⟩

/-! ## The call -/

theorem InsertCallProjectsV35 : Properties.InsertCallProjectsV35 := by
  intro T T' v hint hV hc
  obtain ⟨j, ⟨fuel, hs⟩, _, rfl⟩ := hc.exits
  have hg : InsertGuard T v j :=
    search_yields_guard hV hc.initialized hc.nonzero hc.fresh hc.inBounds hc.hintBelow hs
  obtain ⟨n, _, hw⟩ := SearchIsWalkV35 T v fuel hint j hV hc.inBounds hs
  have hins : InsertV35 (toAbs T) v (lowAbs T hint) (imtInsert (toAbs T) (lowAbs T j) v) :=
    InsertV35.mk hc.nonzero (dedup_gate_sound hV hc.nonzero hc.fresh) (lowAbs_mem hc.inBounds)
      hc.hintBelow hw
  have hproj : toAbs (insert T v j) = imtInsert (toAbs T) (lowAbs T j) v := insert_projects hV hg
  rw [hproj]
  exact ⟨hins, insert_preserves_valid hV hg⟩

theorem InsertCallSucceedsV35 : Properties.InsertCallSucceedsV35 := by
  intro T v hint hV hv0 hfresh hhint hbelow
  obtain ⟨j, hs⟩ := (SearchFuelIsGapV35 T v _ hint hV hhint).2 le_rfl
  have hinit : Initialized T := by
    unfold Initialized
    have := hV.occupied
    omega
  exact ⟨j, hs, ⟨hinit, hv0, hfresh, hhint, hbelow,
    ⟨j, ⟨_, hs⟩, (lowSearch_sound hV _ hint j hhint hbelow hs).1, rfl⟩⟩⟩

theorem RunCallProjectsV35 : Properties.RunCallProjectsV35 := by
  intro R hR h0
  have hvalid : ∀ n, Valid (R n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ m ih =>
      rcases hR m with heq | ⟨v, hint, hc⟩
      · rw [heq]; exact ih
      · exact (InsertCallProjectsV35 _ _ v hint ih hc).2
  refine ⟨hvalid, fun n => ?_⟩
  rcases hR n with heq | ⟨v, hint, hc⟩
  · exact Or.inl (by simp only [heq])
  · exact Or.inr ⟨v, lowAbs (R n) hint, (InsertCallProjectsV35 _ _ v hint (hvalid n) hc).1⟩

/-! ## Hint indices -/

theorem SentinelIndexAlwaysWorksV35 : Properties.SentinelIndexAlwaysWorksV35 := by
  intro R hR hgen n v hv0 hfresh
  have hV : Valid (R n) := (RunCallProjectsV35 R hR (by rw [hgen]; exact setup_valid)).1 n
  have hbelow : ((R n).leaf 0).value < v := by
    rw [hV.sentinel]
    exact Fin.pos_of_ne_zero hv0
  obtain ⟨j, _, hc⟩ := InsertCallSucceedsV35 (R n) v 0 hV hv0 hfresh hV.occupied hbelow
  exact ⟨_, hc⟩

/-- A successful call appends one leaf and keeps the value of every occupied index. -/
private theorem insertCall_keeps_values_unboundedV35 {T T' : Tree} {v : UInt256} {hint : ℕ}
    (hc : InsertCallV35 T v hint T') :
    T'.leafCount = T.leafCount + 1 ∧ ∀ k, k < T.leafCount → (T'.leaf k).value = (T.leaf k).value := by
  obtain ⟨j, _, _, rfl⟩ := hc.exits
  refine ⟨rfl, fun k hk => ?_⟩
  show (if k = j then { T.leaf j with nextIndex := T.leafCount, nextValue := v }
      else if k = T.leafCount then ⟨v, (T.leaf j).nextIndex, (T.leaf j).nextValue⟩
      else T.leaf k).value = (T.leaf k).value
  by_cases hkj : k = j
  · rw [ite_eq_left hkj, hkj]
  · rw [ite_eq_right hkj, ite_eq_right (by omega)]

theorem OnceValidHintIndexStaysValidV35 : Properties.OnceValidHintIndexStaysValidV35 := by
  intro R hR h0 i j h v hij hh hbelow hv0 hfresh
  have hvalid := (RunCallProjectsV35 R hR h0).1
  -- the hint index stays occupied with the same value
  have hkeep : ∀ m, i ≤ m → h < (R m).leafCount ∧ ((R m).leaf h).value = ((R i).leaf h).value := by
    intro m him
    induction him with
    | refl => exact ⟨hh, rfl⟩
    | @step m _ ih =>
      show h < (R (m + 1)).leafCount ∧ ((R (m + 1)).leaf h).value = ((R i).leaf h).value
      obtain ⟨hlt, hval⟩ := ih
      rcases hR m with heq | ⟨w, hint, hc⟩
      · rw [heq]; exact ⟨hlt, hval⟩
      · obtain ⟨hcount, hvals⟩ := insertCall_keeps_values_unboundedV35 hc
        refine ⟨by omega, ?_⟩
        rw [hvals h hlt, hval]
  obtain ⟨hlt, hval⟩ := hkeep j hij
  refine ⟨hlt, hval, ?_⟩
  obtain ⟨k, _, hc⟩ := InsertCallSucceedsV35 (R j) v h (hvalid j) hv0 hfresh hlt
    (by rw [hval]; exact hbelow)
  exact ⟨_, hc⟩

/-! ## Witnesses -/

theorem ChainTreeProjectsV35 : Properties.ChainTreeProjectsV35 := by
  intro k hk
  interval_cases k <;> decide

/-- Step `n < 7` of the pin's honest run, made as a v35 call from the hint `0`. -/
private theorem chainTree_call_unboundedV35 (n : ℕ) (hn : n < 7) :
    InsertCallV35 (chainTree n) ((n + 1 : ℕ) : UInt256) 0 (chainTree (n + 1)) := by
  have hs : lowSearch (chainTree n) ((n + 1 : ℕ) : UInt256) n 0 = some n := by
    interval_cases n <;> decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨n, ⟨n, hs⟩, ?_, rfl⟩⟩
  · unfold Initialized
    interval_cases n <;> decide
  all_goals interval_cases n <;> decide

private theorem chainTreeRunV35_of_le {n : ℕ} (h : n ≤ 7) : chainTreeRunV35 n = chainTree n := by
  unfold chainTreeRunV35
  rw [Nat.min_eq_left h]

private theorem chainTreeRunV35_of_ge {n : ℕ} (h : 7 ≤ n) : chainTreeRunV35 n = chainTree 7 := by
  unfold chainTreeRunV35
  rw [Nat.min_eq_right h]

theorem ChainTreeRunCallsV35 : Properties.ChainTreeRunCallsV35 := by
  have hcalls : ∀ n, n < 7 →
      InsertCallV35 (chainTreeRunV35 n) ((n + 1 : ℕ) : UInt256) 0 (chainTreeRunV35 (n + 1)) := by
    intro n hn
    rw [chainTreeRunV35_of_le (by omega), chainTreeRunV35_of_le (by omega)]
    exact chainTree_call_unboundedV35 n hn
  have hidle : ∀ n, 7 ≤ n → chainTreeRunV35 (n + 1) = chainTreeRunV35 n := by
    intro n hn
    rw [chainTreeRunV35_of_ge (by omega), chainTreeRunV35_of_ge hn]
  have hrun : RunCallV35 chainTreeRunV35 := by
    intro n
    by_cases hn : n < 7
    · exact Or.inr ⟨_, 0, hcalls n hn⟩
    · exact Or.inl (hidle n (by omega))
  have h6 : chainTreeRunV35 6 = chainTree 6 := chainTreeRunV35_of_le (by omega)
  have hproj : toAbs (chainTree 6) = chainSetV35 6 := ChainTreeProjectsV35 6 (by omega)
  have hlow : lowAbs (chainTree 6) 0 = ⟨0, 1⟩ := by decide
  have hwalk : WalkV35 (toAbs (chainTreeRunV35 6)) 7 6 (lowAbs (chainTreeRunV35 6) 0) ⟨6, 0⟩ := by
    rw [h6, hproj, hlow]
    exact PinBoundRevertsWhereV35InsertsV35.2.2.2.2.1
  have hreach : Reaches setup (chainTreeRunV35 6) := by
    rw [h6]
    exact HonestInsertRevertsAtDeployedFuel.1
  refine ⟨hrun, rfl, hcalls, hidle, hreach, reaches_valid hreach setup_valid, by decide, by decide,
    by decide, by decide, hwalk, by decide, by decide, by decide, by decide⟩

end Contracts.InteropCommitmentTree
