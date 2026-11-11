import EraSpec.Contracts.L2InteropCommitmentTree.Properties.RunHeight
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.TreeRoot
import EraSpec.Contracts.FullMerkle.Proofs.CapacityInvariant

/-!
# Proofs: the capacity premise, discharged by the run

Proofs of `EraSpec.Contracts.L2InteropCommitmentTree.Properties.RunHeight`.  The capacity
arithmetic is `AttackVectors.CapacityInvariant` (`count_after`, `cap_at_size`); what this
file adds is that the dimensions carried along a run are exactly
`push^[leafCount] ⟨0, 0⟩`, and the restatement of the `TreeRoot` headlines at that
height.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier AttackVectors.CapacityInvariant

/-! ## `fmHeight` -/

/-- After `n` pushes the dimensions are `(n, fmHeight n)`. -/
lemma iterate_push_zero (n : ℕ) : push^[n] (⟨0, 0⟩ : TreeDims) = ⟨n, fmHeight n⟩ := by
  have hc : (push^[n] (⟨0, 0⟩ : TreeDims)).count = n := count_after n
  show push^[n] ⟨0, 0⟩ = ⟨n, (push^[n] (⟨0, 0⟩ : TreeDims)).height⟩
  generalize push^[n] (⟨0, 0⟩ : TreeDims) = d at hc ⊢
  cases d
  simp only at hc
  subst hc
  rfl

/-- One more push from the source dimensions of `n` leaves gives those of `n + 1`. -/
lemma push_dimsOf (n : ℕ) : push ⟨n, fmHeight n⟩ = ⟨n + 1, fmHeight (n + 1)⟩ := by
  rw [← iterate_push_zero, ← iterate_push_zero, Function.iterate_succ_apply']

lemma fmHeight_succ (n : ℕ) :
    fmHeight (n + 1) = if n = 2 ^ fmHeight n then fmHeight n + 1 else fmHeight n := by
  rw [show fmHeight (n + 1) = (push ⟨n, fmHeight n⟩).height from
    (congrArg TreeDims.height (push_dimsOf n)).symm]
  unfold push
  dsimp only
  split_ifs <;> rfl

theorem fmHeight_capacity (n : ℕ) : n ≤ 2 ^ fmHeight n := cap_at_size n

theorem fmHeight_tight (n : ℕ) (hn : 0 < n) : 2 ^ fmHeight n < 2 * n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [fmHeight_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · decide
    · have ih := ih hpos
      split_ifs with hfull
      · rw [pow_succ]; omega
      · omega

lemma setupDims_eq : setupDims = ⟨1, fmHeight 1⟩ := push_dimsOf 0

/-- `hInsert` on a state carrying its source dimensions carries the source dimensions. -/
lemma hInsert_dimsOf (T : Tree) (v : UInt256) (low : ℕ) :
    hInsert ⟨T, ⟨T.leafCount, fmHeight T.leafCount⟩⟩ v low
      = ⟨insert T v low, ⟨(insert T v low).leafCount, fmHeight (insert T v low).leafCount⟩⟩ := by
  unfold hInsert
  rw [push_dimsOf]
  rfl

/-! ## Dimensions along `HReaches` and `HRun` -/

private lemma hReaches_dims_of {S U : HState} (hR : HReaches S U)
    (h0 : S.dims = ⟨S.tree.leafCount, fmHeight S.tree.leafCount⟩) :
    U.dims = ⟨U.tree.leafCount, fmHeight U.tree.leafCount⟩ := by
  induction hR with
  | refl => exact h0
  | tail _ _ ih =>
    unfold hInsert
    simp only
    rw [ih, push_dimsOf]
    rfl

theorem hReaches_trans {S U W : HState} (h₁ : HReaches S U) (h₂ : HReaches U W) :
    HReaches S W := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hg ih => exact HReaches.tail ih hg

theorem hReaches_dims {S : HState} (hR : HReaches hSetup S) :
    S.dims = ⟨S.tree.leafCount, fmHeight S.tree.leafCount⟩ :=
  hReaches_dims_of hR setupDims_eq

theorem hReaches_capacity {S : HState} (hR : HReaches hSetup S) :
    S.tree.leafCount ≤ 2 ^ S.height := by
  unfold HState.height
  rw [hReaches_dims hR]
  exact fmHeight_capacity _

theorem hRun_reaches {R : ℕ → HState} (hR : HRun R) (h0 : R 0 = hSetup) (n : ℕ) :
    HReaches hSetup (R n) := by
  induction n with
  | zero => exact h0 ▸ HReaches.refl
  | succ n ih =>
    rcases hR n with heq | ⟨v, low, hg, heq⟩
    · rw [heq]; exact ih
    · rw [heq]; exact HReaches.tail ih hg

theorem hRun_dims {R : ℕ → HState} (hR : HRun R) (h0 : R 0 = hSetup) (n : ℕ) :
    (R n).dims = ⟨(R n).tree.leafCount, fmHeight (R n).tree.leafCount⟩ :=
  hReaches_dims (hRun_reaches hR h0 n)

theorem hRun_capacity {R : ℕ → HState} (hR : HRun R) (h0 : R 0 = hSetup) (n : ℕ) :
    (R n).tree.leafCount ≤ 2 ^ (R n).height :=
  hReaches_capacity (hRun_reaches hR h0 n)

/-! ## Projections and lifts -/

theorem hRun_projects {R : ℕ → HState} (hR : HRun R) : Run (fun n => (R n).tree) := by
  intro n
  rcases hR n with heq | ⟨v, low, hg, heq⟩
  · exact Or.inl (congrArg HState.tree heq)
  · exact Or.inr ⟨v, low, hg, by show (R (n + 1)).tree = _; rw [heq]; rfl⟩

theorem run_lifts_to_hRun {R : ℕ → Tree} (hR : Run R) (h0 : R 0 = setup) :
    ∃ D : ℕ → TreeDims, HRun (fun n => ⟨R n, D n⟩) ∧ D 0 = setupDims := by
  refine ⟨fun n => ⟨(R n).leafCount, fmHeight (R n).leafCount⟩, ?_, ?_⟩
  · intro n
    rcases hR n with heq | ⟨v, low, hg, heq⟩
    · exact Or.inl (by simp only [heq])
    · exact Or.inr ⟨v, low, hg, by simp only [heq, hInsert_dimsOf]⟩
  · simp only [h0, setupDims_eq]; rfl

theorem hReaches_projects {S U : HState} (hR : HReaches S U) : Reaches S.tree U.tree := by
  induction hR with
  | refl => exact Reaches.refl
  | tail _ hg ih => exact Reaches.tail ih hg

theorem reaches_lifts {T U : Tree} (hR : Reaches T U) :
    HReaches ⟨T, ⟨T.leafCount, fmHeight T.leafCount⟩⟩ ⟨U, ⟨U.leafCount, fmHeight U.leafCount⟩⟩ := by
  induction hR with
  | refl => exact HReaches.refl
  | tail _ hg ih => simpa only [hInsert_dimsOf] using HReaches.tail ih hg

/-! ## Fold correspondence at the source's heights -/

theorem insert_below_own_capacity {S : HState} (v : UInt256) (low : ℕ) (hR : HReaches hSetup S) :
    S.tree.leafCount < 2 ^ (hInsert S v low).height := by
  show S.tree.leafCount < 2 ^ (push S.dims).height
  rw [hReaches_dims hR, push_dimsOf]
  have := fmHeight_capacity (S.tree.leafCount + 1)
  show S.tree.leafCount < 2 ^ fmHeight (S.tree.leafCount + 1)
  omega

theorem root_after_updateLeaf_own_height (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState)
    (low : ℕ) (x : UInt256) (hR : HReaches hSetup S) (hlow : low < S.tree.leafCount) :
    rootOf h z0 ((leafHashes hl S.tree).set low x) S.height
      = walkPure h (honestSibs h z0 (leafHashes hl S.tree) low) 0 S.height low x :=
  root_after_updateLeaf hlow (hReaches_capacity hR)

theorem root_after_insert_own_height (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState)
    (v : UInt256) (low : ℕ) (hR : HReaches hSetup S) (hg : InsertGuard S.tree v low) :
    (hInsert S v low).root h z0 hl
      = walkPure h
          (honestSibs h z0
            ((leafHashes hl S.tree).set low
              (hl { S.tree.leaf low with nextIndex := S.tree.leafCount, nextValue := v }))
            S.tree.leafCount)
          0 (hInsert S v low).height S.tree.leafCount
          (hl ⟨v, (S.tree.leaf low).nextIndex, (S.tree.leaf low).nextValue⟩) :=
  root_after_insert (T := S.tree) hg.inBounds (insert_below_own_capacity v low hR)

/-! ## The headlines at the run's own height -/

/-- Completeness of non-inclusion, exposing the occupied index of the honest low leaf. -/
private lemma non_inclusion_complete_at {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
    (hV : Valid T) {height : ℕ} (hcap : T.leafCount ≤ 2 ^ height)
    {v : UInt256} (hv : v ≠ 0) (habs : v ∉ keys (toAbs T)) :
    ∃ i < T.leafCount,
      NonInclusionAccepted h hl (root h z0 hl T height) v (T.leaf i) i
        (honestSibs h z0 (leafHashes hl T) i) height := by
  obtain ⟨_, _, hnc, hwp⟩ := hV.absSound
  have hbelow : ∃ X ∈ toAbs T, X.key < v :=
    ⟨⟨(T.leaf 0).value, (T.leaf 0).nextValue⟩,
     mem_toAbs.mpr ⟨0, hV.occupied, rfl, rfl⟩,
     by show (T.leaf 0).value < v; rw [hV.sentinel]; exact Fin.pos_of_ne_zero hv⟩
  obtain ⟨W, hW, hlow, hwin⟩ := gap_witness_exists hnc hwp hbelow habs
  obtain ⟨i, hi, hval, hnext⟩ := mem_toAbs.mp hW
  refine ⟨i, hi, hv, by rwa [hval], by rwa [hnext],
    ⟨lt_of_lt_of_le hi hcap, ?_⟩⟩
  have := honest_walk_root h z0 (leafHashes hl T) height i (lt_of_lt_of_le hi hcap)
  rwa [leafHashes_getD hi] at this

theorem proofs_exclusive_or_break_at_own_height (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (S : HState) (hR : HReaches hSetup S) :
    (∀ v : UInt256, v ∈ keys (toAbs S.tree) →
      ∃ i < S.tree.leafCount, (S.tree.leaf i).value = v
        ∧ InclusionAccepted h hl (S.root h z0 hl) v (S.tree.leaf i) i
            (honestSibs h z0 (leafHashes hl S.tree) i) S.height
        ∧ ¬ TreeRootBreak h z0 hl S.tree S.height (honestSibs h z0 (leafHashes hl S.tree) i)
            S.height i (S.tree.leaf i))
    ∧ (∀ v : UInt256, v ≠ 0 → v ∉ keys (toAbs S.tree) →
      ∃ i < S.tree.leafCount,
        NonInclusionAccepted h hl (S.root h z0 hl) v (S.tree.leaf i) i
            (honestSibs h z0 (leafHashes hl S.tree) i) S.height
        ∧ ¬ TreeRootBreak h z0 hl S.tree S.height (honestSibs h z0 (leafHashes hl S.tree) i)
            S.height i (S.tree.leaf i))
    ∧ (∀ (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      InclusionAccepted h hl (S.root h z0 hl) v ℓ₁ i₁ s₁ k₁ →
      NonInclusionAccepted h hl (S.root h z0 hl) v ℓ₂ i₂ s₂ k₂ →
        TreeRootBreak h z0 hl S.tree S.height s₁ k₁ i₁ ℓ₁
          ∨ TreeRootBreak h z0 hl S.tree S.height s₂ k₂ i₂ ℓ₂) := by
  have hV : Valid S.tree := reaches_valid (hReaches_projects hR) setup_valid
  have hcap := hReaches_capacity hR
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, hi, hval⟩ := mem_keys_iff_index.mp hv
    refine ⟨i, hi, hval, ?_, honest_proof_no_break h z0 hl S.tree S.height i hi⟩
    have hI := inclusion_complete (h := h) (z0 := z0) (hl := hl) hcap hi
    rwa [hval] at hI
  · intro v hv0 habs
    obtain ⟨i, hi, hN⟩ := non_inclusion_complete_at (h := h) (z0 := z0) (hl := hl) hV hcap hv0 habs
    exact ⟨i, hi, hN, honest_proof_no_break h z0 hl S.tree S.height i hi⟩
  · intro v ℓ₁ ℓ₂ i₁ i₂ s₁ s₂ k₁ k₂ hI hN
    exact proofs_exclusive_or_break hV hI hN

theorem run_roots_exclusive_or_break_at_own_height (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (R : ℕ → HState) (hR : HRun R) (h0 : R 0 = hSetup) (n : ℕ) :
    (∀ v : UInt256, v ∈ keys (toAbs (R n).tree) →
      ∃ i < (R n).tree.leafCount, ((R n).tree.leaf i).value = v
        ∧ InclusionAccepted h hl ((R n).root h z0 hl) v ((R n).tree.leaf i) i
            (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height
        ∧ ¬ TreeRootBreak h z0 hl (R n).tree (R n).height
            (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height i ((R n).tree.leaf i))
    ∧ (∀ v : UInt256, v ≠ 0 → v ∉ keys (toAbs (R n).tree) →
      ∃ i < (R n).tree.leafCount,
        NonInclusionAccepted h hl ((R n).root h z0 hl) v ((R n).tree.leaf i) i
            (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height
        ∧ ¬ TreeRootBreak h z0 hl (R n).tree (R n).height
            (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height i ((R n).tree.leaf i))
    ∧ (∀ (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      InclusionAccepted h hl ((R n).root h z0 hl) v ℓ₁ i₁ s₁ k₁ →
      NonInclusionAccepted h hl ((R n).root h z0 hl) v ℓ₂ i₂ s₂ k₂ →
        TreeRootBreak h z0 hl (R n).tree (R n).height s₁ k₁ i₁ ℓ₁
          ∨ TreeRootBreak h z0 hl (R n).tree (R n).height s₂ k₂ i₂ ℓ₂) :=
  proofs_exclusive_or_break_at_own_height h z0 hl (R n) (hRun_reaches hR h0 n)

/-! ## Anti-vacuity -/

lemma hThree_reaches {a b : UInt256} (ha : 0 < a) (hab : a < b) : HReaches hSetup (hThree a b) := by
  obtain ⟨hg1, hg2⟩ := threeLeafTree_guards ha hab
  exact HReaches.tail (HReaches.tail (HReaches.refl (S := hSetup)) (U := hSetup) hg1)
    (U := hInsert hSetup a 0) hg2

lemma hThreeRun_hRun {a b : UInt256} (ha : 0 < a) (hab : a < b) : HRun (hThreeRun a b) := by
  obtain ⟨hg1, hg2⟩ := threeLeafTree_guards ha hab
  intro n
  match n with
  | 0 => exact Or.inr ⟨a, 0, hg1, rfl⟩
  | 1 => exact Or.inr ⟨b, 1, hg2, rfl⟩
  | n + 2 => exact Or.inl (by simp [hThreeRun])

theorem hThreeRun_witness (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    HRun (hThreeRun a b) ∧ hThreeRun a b 0 = hSetup
      ∧ (∀ n, HReaches hSetup (hThreeRun a b n))
      ∧ setupDims = ⟨1, 0⟩
      ∧ (hThreeRun a b 0).height = 0 ∧ (hThreeRun a b 1).height = 1
      ∧ (hThreeRun a b 2).height = 2
      ∧ (hThreeRun a b 2).tree = threeLeafTree a b
      ∧ (hThreeRun a b 2).tree.leafCount = 3
      ∧ (hThreeRun a b 2).tree.leafCount < 2 ^ (hThreeRun a b 2).height := by
  have hR := hThreeRun_hRun ha hab
  exact ⟨hR, rfl, hRun_reaches hR rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by show (3 : ℕ) < 2 ^ 2; norm_num⟩

theorem padding_forgery_at_own_height (h : Hash) (hl : LeafHash) (a b : UInt256)
    (ha : 0 < a) (hab : a < b) :
    HReaches hSetup (hThree a b) ∧ hThreeRun a b 2 = hThree a b ∧ (hThree a b).height = 2
      ∧ InclusionAccepted h hl ((hThree a b).root h (hl ⟨0, 0, 0⟩) hl) a
          ((hThree a b).tree.leaf 1) 1
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (hThree a b).tree) 1) (hThree a b).height
      ∧ NonInclusionAccepted h hl ((hThree a b).root h (hl ⟨0, 0, 0⟩) hl) a ⟨0, 0, 0⟩ 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (hThree a b).tree) 3) (hThree a b).height
      ∧ ¬ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (hThree a b).tree (hThree a b).height
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (hThree a b).tree) 1) (hThree a b).height 1
          ((hThree a b).tree.leaf 1)
      ∧ TreeRootBreakExactly h (hl ⟨0, 0, 0⟩) hl (hThree a b).tree (hThree a b).height
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (hThree a b).tree) 3) (hThree a b).height 3
          ⟨0, 0, 0⟩ .paddingHit := by
  obtain ⟨_, hI, hN⟩ := proofs_exclusive_or_break_satisfiable h hl a b ha hab
  obtain ⟨hnb, _⟩ := padding_countermodel_locates_padding_hit h hl a b
  exact ⟨hThree_reaches ha hab, rfl, rfl, hI, hN, hnb, padding_countermodel_exactly_padding_hit h hl a b⟩

end Contracts.InteropCommitmentTree

/-! ## Certificates -/

namespace Contracts.InteropCommitmentTree

theorem HReachesDims : Properties.HReachesDims := @hReaches_dims
theorem FmHeightCapacity : Properties.FmHeightCapacity := fmHeight_capacity
theorem FmHeightTight : Properties.FmHeightTight := fmHeight_tight
theorem HReachesCapacity : Properties.HReachesCapacity := @hReaches_capacity
theorem HRunDims : Properties.HRunDims := @hRun_dims
theorem HRunCapacity : Properties.HRunCapacity := @hRun_capacity
theorem HRunReaches : Properties.HRunReaches := @hRun_reaches
theorem HRunProjects : Properties.HRunProjects := @hRun_projects
theorem RunLiftsToHRun : Properties.RunLiftsToHRun := @run_lifts_to_hRun
theorem HReachesProjects : Properties.HReachesProjects := @hReaches_projects
theorem ReachesLifts : Properties.ReachesLifts := @reaches_lifts
theorem InsertBelowOwnCapacity : Properties.InsertBelowOwnCapacity :=
  fun _ v low hR => insert_below_own_capacity v low hR
theorem RootAfterUpdateLeafOwnHeight : Properties.RootAfterUpdateLeafOwnHeight :=
  root_after_updateLeaf_own_height
theorem RootAfterInsertOwnHeight : Properties.RootAfterInsertOwnHeight :=
  root_after_insert_own_height
theorem ProofsExclusiveOrBreakAtOwnHeight : Properties.ProofsExclusiveOrBreakAtOwnHeight :=
  proofs_exclusive_or_break_at_own_height
theorem RunRootsExclusiveOrBreakAtOwnHeight : Properties.RunRootsExclusiveOrBreakAtOwnHeight :=
  run_roots_exclusive_or_break_at_own_height
theorem HThreeRunWitness : Properties.HThreeRunWitness := hThreeRun_witness
theorem PaddingForgeryAtOwnHeight : Properties.PaddingForgeryAtOwnHeight :=
  padding_forgery_at_own_height

end Contracts.InteropCommitmentTree
