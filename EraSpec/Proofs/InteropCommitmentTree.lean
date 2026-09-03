import EraSpec.Properties.InteropCommitmentTree

/-!
# Proofs: the commitment tree

Proofs of `EraSpec.Properties.InteropCommitmentTree`, over the model in
`EraSpec.Contracts.InteropCommitmentTree`.  The theorems keep their working names
in the model's namespace; the `Certificates` section at the end restates each
property as a theorem of exactly the property's type.

A reviewer does not need to read this file.  The audit (`scripts/audit-axioms.sh`)
confirms nothing here rests on `sorry` or a declared axiom, and
`scripts/check-properties.sh` confirms every property has a certificate.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-! ## The projection -/

lemma mem_toAbs {T : Tree} {X : AbsLeaf} :
    X ∈ toAbs T ↔ ∃ i < T.leafCount, (T.leaf i).value = X.key ∧ (T.leaf i).nextValue = X.nextKey := by
  unfold toAbs
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, hEq⟩
    exact ⟨i, hi, by rw [← hEq], by rw [← hEq]⟩
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨i, hi, by cases X; simp_all⟩

@[simp] lemma toAbs_setup : toAbs setup = ({⟨0, 0⟩} : Finset AbsLeaf) := by
  unfold toAbs setup
  simp

lemma lowAbs_mem {T : Tree} {low : ℕ} (h : low < T.leafCount) :
    lowAbs T low ∈ toAbs T :=
  mem_toAbs.mpr ⟨low, h, rfl, rfl⟩

/-! ## `setup` -/

/-- **`setup` ESTABLISHES A VALID STATE.** -/
theorem setup_valid : Valid setup := by
  refine ⟨by simp [setup], by norm_num [setup], ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj _
    simp only [setup] at hi hj
    omega
  · intro i hi hlt
    simp only [setup] at hlt
    omega
  · intro v hv
    simp only [setup] at hv
    exact absurd rfl hv
  · intro i hi h
    simp only [setup] at h
    exact absurd rfl h
  · rw [toAbs_setup]; exact genesis_soundState

/-! ## The dedup gate -/

/-- **THE STORAGE DEDUP GATE IMPLIES SET-LEVEL FRESHNESS.**  `v ≠ 0` rules out the
SENTINEL, the one occupied leaf deliberately left unregistered.  Without it the
lemma is false — `valueToIndex[0] = 0` while `0` *is* a key. -/
theorem dedup_gate_sound {T : Tree} (hV : Valid T) {v : UInt256}
    (hv0 : v ≠ 0) (hgate : T.valueToIndex v = 0) : v ∉ keys (toAbs T) := by
  intro hmem
  unfold keys at hmem
  obtain ⟨X, hX, hXv⟩ := Finset.mem_image.mp hmem
  obtain ⟨i, hi, hival, _⟩ := mem_toAbs.mp hX
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · exact hv0 (by rw [← hXv, ← hival, hV.sentinel])
  · have := hV.vtiAgree i hipos hi
    rw [hival, hXv, hgate] at this
    omega

theorem registered_is_key {T : Tree} (hV : Valid T) {v : UInt256}
    (hreg : T.valueToIndex v ≠ 0) : v ∈ keys (toAbs T) := by
  obtain ⟨hlt, hval⟩ := hV.vtiSound v hreg
  exact Finset.mem_image.mpr
    ⟨⟨v, (T.leaf (T.valueToIndex v)).nextValue⟩,
     mem_toAbs.mpr ⟨T.valueToIndex v, hlt, hval, rfl⟩, rfl⟩

theorem gate_iff_absent {T : Tree} (hV : Valid T) {v : UInt256} (hv0 : v ≠ 0) :
    T.valueToIndex v = 0 ↔ v ∉ keys (toAbs T) := by
  constructor
  · exact dedup_gate_sound hV hv0
  · intro hnot
    by_contra hreg
    exact hnot (registered_is_key hV hreg)

/-! ## The bounded search loop -/

theorem lowSearch_window {T : Tree} {v : UInt256} :
    ∀ (fuel i j : ℕ), lowSearch T v fuel i = some j →
      (T.leaf j).nextValue = 0 ∨ v ≤ (T.leaf j).nextValue := by
  intro fuel
  induction fuel with
  | zero =>
    intro i j h
    unfold lowSearch at h
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [if_pos hc] at h; exact absurd h (by simp)
    · rw [if_neg hc] at h
      cases Option.some.inj h
      rcases not_and_or.mp hc with h1 | h2
      · exact Or.inl (by simpa using h1)
      · exact Or.inr (le_of_not_lt h2)
  | succ fuel ih =>
    intro i j h
    unfold lowSearch at h
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [if_pos hc] at h; exact ih _ _ h
    · rw [if_neg hc] at h
      cases Option.some.inj h
      rcases not_and_or.mp hc with h1 | h2
      · exact Or.inl (by simpa using h1)
      · exact Or.inr (le_of_not_lt h2)

theorem lowSearch_sound {T : Tree} (hV : Valid T) {v : UInt256} :
    ∀ (fuel i j : ℕ), i < T.leafCount → (T.leaf i).value < v →
      lowSearch T v fuel i = some j →
      j < T.leafCount ∧ (T.leaf j).value < v := by
  intro fuel
  induction fuel with
  | zero =>
    intro i j hi hlow h
    unfold lowSearch at h
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [if_pos hc] at h; exact absurd h (by simp)
    · rw [if_neg hc] at h
      cases Option.some.inj h
      exact ⟨hi, hlow⟩
  | succ fuel ih =>
    intro i j hi hlow h
    unfold lowSearch at h
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [if_pos hc] at h
      obtain ⟨hnz, hlt⟩ := hc
      obtain ⟨hbound, hval⟩ := hV.linkAgree i hi hnz
      exact ih _ _ hbound (by rw [hval]; exact hlt) h
    · rw [if_neg hc] at h
      cases Option.some.inj h
      exact ⟨hi, hlow⟩

/-- The contract's `insert` flow establishes the guard at the index the search
returns. -/
theorem search_yields_guard {T : Tree} (hV : Valid T) {v : UInt256} {fuel i j : ℕ}
    (hinit : Initialized T) (hv : v ≠ 0) (hfresh : T.valueToIndex v = 0)
    (hi : i < T.leafCount) (hlow : (T.leaf i).value < v) (hs : lowSearch T v fuel i = some j) :
    InsertGuard T v j :=
  ⟨hinit, hv, hfresh, (lowSearch_sound hV fuel i j hi hlow hs).1,
   (lowSearch_sound hV fuel i j hi hlow hs).2, lowSearch_window fuel i j hs⟩

/-! ## `insert` projects to `imtInsert` -/

/-- The proof needs `idxInj` — without distinct values at distinct indices,
erasing the low leaf from the projection could remove a *different* index's image
too.  That is why `idxInj` is a `Valid` field rather than a convenience. -/
theorem insert_projects {T : Tree} (hV : Valid T) {v : UInt256} {low : ℕ}
    (hg : InsertGuard T v low) :
    toAbs (insert T v low) = imtInsert (toAbs T) (lowAbs T low) v := by
  have hlowlt := hg.inBounds
  apply Finset.ext
  intro X
  rw [mem_toAbs]
  unfold imtInsert
  simp only [Finset.mem_insert, Finset.mem_erase, mem_toAbs, lowAbs]
  constructor
  · rintro ⟨i, hi, hval, hnext⟩
    simp only [insert] at hi hval hnext
    by_cases hilow : i = low
    · subst hilow
      simp only [if_pos rfl] at hval hnext
      left
      cases X; simp_all
    · by_cases hin : i = T.leafCount
      · subst hin
        rw [if_neg hilow, if_pos rfl] at hval hnext
        right; left
        cases X; simp_all
      · rw [if_neg hilow, if_neg hin] at hval hnext
        right; right
        refine ⟨?_, ⟨i, by omega, hval, hnext⟩⟩
        intro hXlow
        apply hilow
        refine hV.idxInj i (by omega) low hlowlt ?_
        rw [hval, hXlow]
  · rintro (rfl | rfl | ⟨hXne, i, hi, hval, hnext⟩)
    · refine ⟨low, ?_, ?_, ?_⟩
      · simp only [insert]; omega
      · simp [insert]
      · simp [insert]
    · refine ⟨T.leafCount, ?_, ?_, ?_⟩
      · simp only [insert]; omega
      · simp only [insert]
        rw [if_neg (by omega : ¬ T.leafCount = low)]
        simp
      · simp only [insert]
        rw [if_neg (by omega : ¬ T.leafCount = low)]
        simp
    · refine ⟨i, by simp only [insert]; omega, ?_, ?_⟩
      · simp only [insert]
        rw [if_neg ?hne, if_neg (by omega : ¬ i = T.leafCount)]
        · exact hval
        case hne =>
          intro hil
          apply hXne
          subst hil
          cases X; simp_all
      · simp only [insert]
        rw [if_neg ?hne, if_neg (by omega : ¬ i = T.leafCount)]
        · exact hnext
        case hne =>
          intro hil
          apply hXne
          subst hil
          cases X; simp_all

/-! ### Field-wise computation of `insert` -/

@[simp] lemma insert_leafCount {T : Tree} {v : UInt256} {low : ℕ} :
    (insert T v low).leafCount = T.leafCount + 1 := rfl

@[simp] lemma insert_vti_self {T : Tree} {v : UInt256} {low : ℕ} :
    (insert T v low).valueToIndex v = T.leafCount := by simp [insert]

lemma insert_vti_other {T : Tree} {v w : UInt256} {low : ℕ} (h : w ≠ v) :
    (insert T v low).valueToIndex w = T.valueToIndex w := by simp [insert, h]

lemma insert_leaf_low {T : Tree} {v : UInt256} {low : ℕ} :
    (insert T v low).leaf low
      = { T.leaf low with nextIndex := T.leafCount, nextValue := v } := by
  simp [insert]

lemma insert_leaf_new {T : Tree} {v : UInt256} {low : ℕ} (h : low < T.leafCount) :
    (insert T v low).leaf T.leafCount
      = ⟨v, (T.leaf low).nextIndex, (T.leaf low).nextValue⟩ := by
  simp only [insert]
  rw [if_neg (by omega : ¬ T.leafCount = low)]
  simp

lemma insert_leaf_other {T : Tree} {v : UInt256} {low i : ℕ}
    (hlow : i ≠ low) (hnew : i ≠ T.leafCount) :
    (insert T v low).leaf i = T.leaf i := by
  simp only [insert]
  rw [if_neg hlow, if_neg hnew]

/-- The dedup gate, in index form: no occupied leaf already carries `v`. -/
lemma fresh_value {T : Tree} (hV : Valid T) {v : UInt256} {low : ℕ}
    (hg : InsertGuard T v low) : ∀ i < T.leafCount, (T.leaf i).value ≠ v := by
  intro i hi hEq
  refine dedup_gate_sound hV hg.nonzero hg.fresh (Finset.mem_image.mpr ?_)
  exact ⟨⟨v, (T.leaf i).nextValue⟩, mem_toAbs.mpr ⟨i, hi, hEq, rfl⟩, rfl⟩

/-! ## The insert is sound -/

theorem insert_sound_step {T : Tree} (hV : Valid T) {v : UInt256} {low : ℕ}
    (hg : InsertGuard T v low) :
    SoundState (toAbs (insert T v low))
      ∧ keys (toAbs (insert T v low)) = Insert.insert v (keys (toAbs T)) := by
  have hstep := guarded_insert_sound_step hV.absSound (lowAbs_mem hg.inBounds)
    hg.lowBelow hg.window (dedup_gate_sound hV hg.nonzero hg.fresh)
  rw [insert_projects hV hg]
  exact hstep

/-- The `linkAgree` case for the appended leaf is the one with real content: the
new leaf inherits the low leaf's `nextIndex`, and showing that index still
resolves correctly needs `nextIndex ≠ low`, which follows from `WindowPos`. -/
theorem insert_preserves_valid {T : Tree} (hV : Valid T) {v : UInt256} {low : ℕ}
    (hg : InsertGuard T v low) : Valid (insert T v low) := by
  have hlow := hg.inBounds
  have hfresh := fresh_value hV hg
  have hv0 := hg.nonzero
  refine ⟨?sent, ?occ, ?inj, ?vtiA, ?vtiS, ?link, (insert_sound_step hV hg).1⟩
  case sent =>
    by_cases h0 : (0 : ℕ) = low
    · rw [← h0] at hlow ⊢
      rw [insert_leaf_low]
      simpa using hV.sentinel
    · rw [insert_leaf_other h0 (by omega)]
      exact hV.sentinel
  case occ => simp only [insert_leafCount]; omega
  case inj =>
    intro i hi j hj hEq
    simp only [insert_leafCount] at hi hj
    have hval : ∀ k, k < T.leafCount + 1 → ((insert T v low).leaf k).value
        = if k = T.leafCount then v else (T.leaf k).value := by
      intro k hk
      by_cases hkn : k = T.leafCount
      · subst hkn; rw [insert_leaf_new hlow]; simp
      · rw [if_neg hkn]
        by_cases hkl : k = low
        · subst hkl; rw [insert_leaf_low]
        · rw [insert_leaf_other hkl hkn]
    rw [hval i hi, hval j hj] at hEq
    by_cases hin : i = T.leafCount <;> by_cases hjn : j = T.leafCount
    · omega
    · rw [if_pos hin, if_neg hjn] at hEq
      exact absurd hEq.symm (hfresh j (by omega))
    · rw [if_neg hin, if_pos hjn] at hEq
      exact absurd hEq (hfresh i (by omega))
    · rw [if_neg hin, if_neg hjn] at hEq
      exact hV.idxInj i (by omega) j (by omega) hEq
  case vtiA =>
    intro i hipos hi
    simp only [insert_leafCount] at hi
    by_cases hin : i = T.leafCount
    · subst hin; rw [insert_leaf_new hlow]; simpa using insert_vti_self
    · have hlt : i < T.leafCount := by omega
      have hne : (T.leaf i).value ≠ v := hfresh i hlt
      by_cases hil : i = low
      · subst hil
        rw [insert_leaf_low]
        simpa [insert_vti_other hne] using hV.vtiAgree i hipos hlt
      · rw [insert_leaf_other hil hin, insert_vti_other hne]
        exact hV.vtiAgree i hipos hlt
  case vtiS =>
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      refine ⟨by rw [insert_vti_self, insert_leafCount]; omega, ?_⟩
      rw [insert_vti_self, insert_leaf_new hlow]
    · rw [insert_vti_other hwv] at hw ⊢
      obtain ⟨hlt, hval⟩ := hV.vtiSound w hw
      refine ⟨by simp only [insert_leafCount]; omega, ?_⟩
      by_cases hidl : T.valueToIndex w = low
      · rw [hidl, insert_leaf_low]; rw [hidl] at hval; exact hval
      · rw [insert_leaf_other hidl (by omega)]; exact hval
  case link =>
    intro i hi hnz
    simp only [insert_leafCount] at hi
    by_cases hil : i = low
    · subst hil
      rw [insert_leaf_low] at hnz ⊢
      refine ⟨by simp only [insert_leafCount]; omega, ?_⟩
      rw [insert_leaf_new hlow]
    · by_cases hin : i = T.leafCount
      · subst hin
        rw [insert_leaf_new hlow] at hnz ⊢
        obtain ⟨hb, hv⟩ := hV.linkAgree low hlow (by simpa using hnz)
        have hne : (T.leaf low).nextIndex ≠ low := by
          intro hEq
          rw [hEq] at hv
          rcases hV.absSound.2.2.2 (lowAbs T low) (lowAbs_mem hlow) with h0 | hlt
          · exact absurd (by simpa [lowAbs] using h0) (by simpa using hnz)
          · simp only [lowAbs] at hlt
            rw [hv] at hlt
            exact absurd hlt (lt_irrefl _)
        refine ⟨by simp only [insert_leafCount]; omega, ?_⟩
        rw [insert_leaf_other hne (by omega)]
        exact hv
      · rw [insert_leaf_other hil hin] at hnz ⊢
        obtain ⟨hb, hv⟩ := hV.linkAgree i (by omega) hnz
        refine ⟨by simp only [insert_leafCount]; omega, ?_⟩
        by_cases hnl : (T.leaf i).nextIndex = low
        · rw [hnl, insert_leaf_low]; rw [hnl] at hv; exact hv
        · rw [insert_leaf_other hnl (by omega)]; exact hv

/-! ## Contract runs refine to `GuardedEvolution` -/

theorem run_valid {R : ℕ → Tree} (hR : Run R) (h0 : Valid (R 0)) : ∀ n, Valid (R n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rcases hR n with heq | ⟨v, low, hg, heq⟩
    · rw [heq]; exact ih
    · rw [heq]; exact insert_preserves_valid ih hg

theorem run_isGuardedEvolution {R : ℕ → Tree} (hR : Run R) (h0 : Valid (R 0)) :
    GuardedEvolution (fun n => toAbs (R n)) := by
  intro n
  rcases hR n with heq | ⟨v, low, hg, heq⟩
  · left
    show toAbs (R (n + 1)) = toAbs (R n)
    rw [heq]
  · right
    refine ⟨lowAbs (R n) low, v, lowAbs_mem hg.inBounds, hg.lowBelow, hg.window, ?_, ?_⟩
    · exact dedup_gate_sound (run_valid hR h0 n) hg.nonzero hg.fresh
    · show toAbs (R (n + 1)) = imtInsert (toAbs (R n)) (lowAbs (R n) low) v
      rw [heq]
      exact insert_projects (run_valid hR h0 n) hg

theorem genesis_run_reclaimable_iff_absent {R : ℕ → Tree}
    (hR : Run R) (h0 : R 0 = setup) (n : ℕ) (v : UInt256) (hv : v ≠ 0) :
    (∃ W ∈ toAbs (R n), W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
      ↔ v ∉ keys (toAbs (R n)) := by
  have hvalid0 : Valid (R 0) := by rw [h0]; exact setup_valid
  have hgen : toAbs (R 0) = ({⟨0, 0⟩} : Finset AbsLeaf) := by rw [h0, toAbs_setup]
  exact guardedEvolution_reclaimable_iff_absent
    (run_isGuardedEvolution hR hvalid0) hgen hv

end Contracts.InteropCommitmentTree

/-! ## Certificates

One theorem per property in `EraSpec.Properties.InteropCommitmentTree`, each of
exactly the property's type.  `scripts/check-properties.sh` finds these. -/

namespace Proofs.InteropCommitmentTree

open Contracts.InteropCommitmentTree

theorem SetupValid : Properties.InteropCommitmentTree.SetupValid := setup_valid
theorem InsertPreservesValid : Properties.InteropCommitmentTree.InsertPreservesValid :=
  @insert_preserves_valid
theorem RunValid : Properties.InteropCommitmentTree.RunValid := @run_valid
theorem DedupGateSound : Properties.InteropCommitmentTree.DedupGateSound := @dedup_gate_sound
theorem RegisteredIsKey : Properties.InteropCommitmentTree.RegisteredIsKey := @registered_is_key
theorem GateIffAbsent : Properties.InteropCommitmentTree.GateIffAbsent := @gate_iff_absent
theorem LowSearchWindow : Properties.InteropCommitmentTree.LowSearchWindow := @lowSearch_window
theorem LowSearchSound : Properties.InteropCommitmentTree.LowSearchSound := @lowSearch_sound
theorem SearchYieldsGuard : Properties.InteropCommitmentTree.SearchYieldsGuard :=
  @search_yields_guard
theorem InsertProjects : Properties.InteropCommitmentTree.InsertProjects := @insert_projects
theorem InsertSoundStep : Properties.InteropCommitmentTree.InsertSoundStep := @insert_sound_step
theorem RunIsGuardedEvolution : Properties.InteropCommitmentTree.RunIsGuardedEvolution :=
  @run_isGuardedEvolution
theorem GenesisRunReclaimableIffAbsent :
    Properties.InteropCommitmentTree.GenesisRunReclaimableIffAbsent :=
  @genesis_run_reclaimable_iff_absent

end Proofs.InteropCommitmentTree
