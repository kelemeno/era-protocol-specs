import EraSpec.Contracts.IndexedMerkleTree.Properties.ReclaimGateFaithful
import EraSpec.Contracts.IndexedMerkleTree.Proofs.Model
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.RunHeight

/-!
# Proofs: the reclaim capstones against the deployed refund gate

Proofs of `EraSpec.Contracts.IndexedMerkleTree.Properties.ReclaimGateFaithful`.  The hash-side
content is `L2InteropCommitmentTree/Proofs/TreeRoot.lean` (`padding_collision_forges_absence`,
`non_inclusion_sound_or_break`, the run-level completeness clause) and the located-break
extractor `accept_pins_entry_any_length_or_break` (`Merkle/Proofs/PathCollision.lean`).  The
order theory is `Proofs/Model.lean` (`present_not_reclaimable`,
`guardedEvolution_delivered_available_forever`).  What this file adds is the reading of
the capstones against the deployed gate: where it fails, and the refined gate it holds for.
-/

namespace IMTAbstract.ReclaimGateFaithful

open Clear IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-! ## Run bookkeeping -/

/-- Every state reached from `hSetup` has a valid list state. -/
private lemma reached_valid {S : HState} (hR : HReaches hSetup S) : Valid S.tree :=
  reaches_valid (hReaches_projects hR) setup_valid

/-- The leaf-set projection of a run from `hSetup` is a `GuardedEvolution`. -/
private lemma absHistory_guarded {R : ℕ → HState} (hR : HRun R) (h0 : R 0 = hSetup) :
    GuardedEvolution (absHistory R) :=
  run_isGuardedEvolution (hRun_projects hR) (by show Valid (R 0).tree; rw [h0]; exact setup_valid)

/-- The leaf-set projection of a run from `hSetup` starts at the genesis singleton. -/
private lemma absHistory_genesis {R : ℕ → HState} (h0 : R 0 = hSetup) :
    absHistory R 0 = ({⟨0, 0⟩} : Finset AbsLeaf) := by
  show toAbs (R 0).tree = _
  rw [h0]
  exact toAbs_setup

/-! ## The capstones re-proved over the refined gate -/

theorem break_free_gate_implies_member_gate (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (S : HState) (v : UInt256) (hBF : BreakFreeGate h z0 hl S v) :
    MemberGate (toAbs S.tree) v := by
  obtain ⟨ℓ, idx, sibs, k, hN, hnb⟩ := hBF
  rcases non_inclusion_sound_or_break (T := S.tree) (height := S.height) hN with hW | hb
  · exact hW
  · exact absurd hb hnb

theorem deployed_gate_liveness (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → HState)
    (hR : HRun R) (h0 : R 0 = hSetup) (j : ℕ) (v : UInt256) (hv : v ≠ 0)
    (habs : v ∉ keys (absHistory R j)) :
    BreakFreeGate h z0 hl (R j) v ∧ DeployedGate h z0 hl (R j) v := by
  obtain ⟨_, hlive, _⟩ := run_roots_exclusive_or_break_at_own_height h z0 hl R hR h0 j
  obtain ⟨i, _, hN, hnb⟩ := hlive v hv habs
  exact ⟨⟨_, _, _, _, hN, hnb⟩, ⟨_, _, _, _, hN⟩⟩

theorem break_free_gate_dichotomy (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → HState)
    (hR : HRun R) (h0 : R 0 = hSetup) (j : ℕ) (v : UInt256) (hv : v ≠ 0) :
    BreakFreeGate h z0 hl (R j) v ↔ v ∉ keys (absHistory R j) := by
  constructor
  · intro hBF hmem
    have hV : Valid (R j).tree := reached_valid (hRun_reaches hR h0 j)
    exact present_not_reclaimable hV.absSound.1 hmem
      (break_free_gate_implies_member_gate h z0 hl (R j) v hBF)
  · intro habs
    exact (deployed_gate_liveness h z0 hl R hR h0 j v hv habs).1

theorem break_free_gate_matches_member_gate (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (R : ℕ → HState) (hR : HRun R) (h0 : R 0 = hSetup) (j : ℕ) (v : UInt256) (hv : v ≠ 0) :
    BreakFreeGate h z0 hl (R j) v ↔ MemberGate (absHistory R j) v := by
  rw [break_free_gate_dichotomy h z0 hl R hR h0 j v hv]
  exact (guardedEvolution_reclaimable_iff_absent (absHistory_guarded hR h0)
    (absHistory_genesis h0) hv).symm

theorem break_free_delivery_finality (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (R : ℕ → HState) (hR : HRun R) (h0 : R 0 = hSetup) (t : ℕ → UInt256) (D v : UInt256)
    (i : ℕ) (htmono : Monotone t) (hti : t i ≤ D) (hdel : v ∈ keys (absHistory R i)) :
    (∀ j : ℕ, i ≤ j → v ∈ keys (absHistory R j))
      ∧ ∀ j : ℕ, D < t (j + 1) → ¬ BreakFreeGate h z0 hl (R j) v := by
  obtain ⟨hpersist, hnoWin⟩ := guardedEvolution_delivered_available_forever
    (absHistory_guarded hR h0) (absHistory_genesis h0) htmono hti hdel
  refine ⟨hpersist, ?_⟩
  intro j hpin hBF
  obtain ⟨W, hW, hlow, hwin⟩ := break_free_gate_implies_member_gate h z0 hl (R j) v hBF
  exact hnoWin j W hpin hW hlow hwin

/-! ## No false refunds, located -/

theorem delivered_refund_locates_collision_or_padding_hit (h : Hash) (z0 : UInt256)
    (hl : LeafHash) (S : HState) (hR : HReaches hSetup S) (v : UInt256) (ℓ : Leaf) (idx : ℕ)
    (sibs : ℕ → UInt256) (k : ℕ) (hdel : v ∈ keys (toAbs S.tree))
    (hN : NonInclusionAccepted h hl (S.root h z0 hl) v ℓ idx sibs k) :
    TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .wrongLength
      ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .pathCollision
      ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .leafCollision
      ∨ (k = S.height ∧ S.tree.leafCount ≤ idx ∧ hl ℓ = z0) := by
  have hV : Valid S.tree := reached_valid hR
  rcases accept_pins_entry_any_length_or_break h z0 (leafHashes hl S.tree) sibs k S.height idx
      (hl ℓ) hN.path.inBounds hN.path.recompute with ⟨hk, hget⟩ | ⟨hk, hc⟩ | hb
  · by_cases hidx : idx < S.tree.leafCount
    · rw [leafHashes_getD hidx] at hget
      by_cases hle : S.tree.leaf idx = ℓ
      · exfalso
        refine present_not_reclaimable hV.absSound.1 hdel
          ⟨⟨ℓ.value, ℓ.nextValue⟩, ?_, hN.lowBelow, hN.window⟩
        exact mem_toAbs.mpr ⟨idx, hidx, by rw [hle], by rw [hle]⟩
      · exact Or.inr (Or.inr (Or.inl ⟨hidx, hle, hget⟩))
    · rw [getD_default _ _ _ (by rw [leafHashes_length]; omega)] at hget
      exact Or.inr (Or.inr (Or.inr ⟨hk, by omega, hget.symm⟩))
  · exact Or.inr (Or.inl ⟨hk, hc⟩)
  · exact Or.inl hb

theorem full_snapshot_refund_of_delivered_needs_collision (h : Hash) (z0 : UInt256)
    (hl : LeafHash) (S : HState) (hR : HReaches hSetup S)
    (hfull : S.tree.leafCount = 2 ^ S.height) (v : UInt256) (ℓ : Leaf) (idx : ℕ)
    (sibs : ℕ → UInt256) (k : ℕ) (hdel : v ∈ keys (toAbs S.tree))
    (hN : NonInclusionAccepted h hl (S.root h z0 hl) v ℓ idx sibs k) :
    TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .wrongLength
      ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .pathCollision
      ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .leafCollision := by
  rcases delivered_refund_locates_collision_or_padding_hit h z0 hl S hR v ℓ idx sibs k hdel hN
    with hb | hb | hb | ⟨hk, hle, _⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hb)
  · exfalso
    have hin : idx < 2 ^ k := hN.path.inBounds
    rw [hk, ← hfull] at hin
    omega

theorem dedicated_padding_refund_of_delivered_needs_collision (h : Hash) (z0 : UInt256)
    (hl : LeafHash) (S : HState) (hR : HReaches hSetup S) (v : UInt256) (ℓ : Leaf) (idx : ℕ)
    (sibs : ℕ → UInt256) (k : ℕ) (hpre : hl ℓ ≠ z0) (hdel : v ∈ keys (toAbs S.tree))
    (hN : NonInclusionAccepted h hl (S.root h z0 hl) v ℓ idx sibs k) :
    TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .wrongLength
      ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .pathCollision
      ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .leafCollision := by
  rcases delivered_refund_locates_collision_or_padding_hit h z0 hl S hR v ℓ idx sibs k hdel hN
    with hb | hb | hb | ⟨_, _, hpad⟩
  · exact Or.inl hb
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hb)
  · exact absurd hpad hpre

theorem dedicated_padding_zero_leaf_needs_path_collision (h : Hash) (z0 : UInt256)
    (hl : LeafHash) (hpad : DedicatedPadding hl z0) (S : HState) (v : UInt256) (idx : ℕ)
    (sibs : ℕ → UInt256) (hempty : S.tree.leafCount ≤ idx)
    (hN : NonInclusionAccepted h hl (S.root h z0 hl) v ⟨0, 0, 0⟩ idx sibs S.height) :
    PathCollision h z0 (leafHashes hl S.tree) sibs 0 S.height idx (hl ⟨0, 0, 0⟩) := by
  rcases accept_pins_entry_any_length_or_break h z0 (leafHashes hl S.tree) sibs S.height
      S.height idx (hl ⟨0, 0, 0⟩) hN.path.inBounds hN.path.recompute with
    ⟨_, hget⟩ | ⟨_, hc⟩ | hb
  · rw [getD_default _ _ _ (by rw [leafHashes_length]; exact hempty)] at hget
    exact absurd hget.symm hpad
  · exact hc
  · exact absurd hb (heightBreak_not_tautology.1 _ _ _ _ _ _ _)

/-! ## The countermodel at c67894b9 -/

theorem pinned_gate_accepts_every_value_below_capacity (h : Hash) (hl : LeafHash) (S : HState)
    (hcap : S.tree.leafCount < 2 ^ S.height) (v : UInt256) (hv : v ≠ 0) :
    DeployedGate h (zeroLeafHash hl) hl S v :=
  ⟨⟨0, 0, 0⟩, S.tree.leafCount, _, S.height,
    padding_collision_forges_absence h hl S.tree S.height hcap v (Fin.pos_of_ne_zero hv)⟩

theorem reached_below_capacity_iff_not_power_of_two (S : HState) (hR : HReaches hSetup S) :
    S.tree.leafCount < 2 ^ S.height ↔ ∀ k : ℕ, S.tree.leafCount ≠ 2 ^ k := by
  have hheight : S.height = fmHeight S.tree.leafCount := by
    unfold HState.height
    rw [hReaches_dims hR]
  have hpos : 0 < S.tree.leafCount := (reached_valid hR).occupied
  have hcap := fmHeight_capacity S.tree.leafCount
  have htight := fmHeight_tight S.tree.leafCount hpos
  rw [hheight]
  constructor
  · intro hlt k hk
    have hle : fmHeight S.tree.leafCount ≤ k := by
      by_contra hcon
      have hpow : 2 ^ (k + 1) ≤ 2 ^ fmHeight S.tree.leafCount :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at hpow
      omega
    have hpow : 2 ^ fmHeight S.tree.leafCount ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hle
    omega
  · intro hne
    exact lt_of_le_of_ne hcap (hne (fmHeight S.tree.leafCount))

theorem pinned_gate_accepts_every_value_off_powers_of_two (h : Hash) (hl : LeafHash)
    (S : HState) (hR : HReaches hSetup S) (hnp : ∀ k : ℕ, S.tree.leafCount ≠ 2 ^ k)
    (v : UInt256) (hv : v ≠ 0) :
    DeployedGate h (zeroLeafHash hl) hl S v :=
  pinned_gate_accepts_every_value_below_capacity h hl S
    ((reached_below_capacity_iff_not_power_of_two S hR).2 hnp) v hv

theorem pinned_counterexample_meets_capstone_hypotheses (h : Hash) (hl : LeafHash)
    (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    HRun (hThreeRun a b) ∧ hThreeRun a b 0 = hSetup
      ∧ GuardedEvolution (absHistory (hThreeRun a b))
      ∧ absHistory (hThreeRun a b) 0 = ({⟨0, 0⟩} : Finset AbsLeaf)
      ∧ a ∈ keys (absHistory (hThreeRun a b) 2)
      ∧ ¬ MemberGate (absHistory (hThreeRun a b) 2) a
      ∧ NonInclusionAccepted h hl ((hThreeRun a b 2).root h (zeroLeafHash hl) hl) a ⟨0, 0, 0⟩ 3
          (honestSibs h (zeroLeafHash hl) (leafHashes hl (hThreeRun a b 2).tree) 3)
          (hThreeRun a b 2).height
      ∧ (⟨0, 0⟩ : AbsLeaf) ∉ absHistory (hThreeRun a b) 2
      ∧ DeployedGate h (zeroLeafHash hl) hl (hThreeRun a b 2) a
      ∧ ¬ BreakFreeGate h (zeroLeafHash hl) hl (hThreeRun a b 2) a := by
  obtain ⟨hR, h0, _⟩ := hThreeRun_witness a b ha hab
  obtain ⟨_, _, _, _, hN, _⟩ := padding_forgery_at_own_height h hl a b ha hab
  obtain ⟨hV, hdel, _⟩ := padding_collision_refunds_delivered_leg h hl ha hab
  have hV2 : Valid (hThreeRun a b 2).tree := hV
  have hdel2 : a ∈ keys (absHistory (hThreeRun a b) 2) := hdel
  have hN2 : NonInclusionAccepted h hl ((hThreeRun a b 2).root h (zeroLeafHash hl) hl) a
      ⟨0, 0, 0⟩ 3 (honestSibs h (zeroLeafHash hl) (leafHashes hl (hThreeRun a b 2).tree) 3)
      (hThreeRun a b 2).height := hN
  have hnot00 : (⟨0, 0⟩ : AbsLeaf) ∉ absHistory (hThreeRun a b) 2 := by
    intro hmem
    obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hdel2
    have hgap := hV2.absSound.1 ⟨0, 0⟩ hmem L hL (by rw [hLkey]; exact ha)
    exact hgap.1 rfl
  refine ⟨hR, h0, absHistory_guarded hR h0, absHistory_genesis h0, hdel2,
    fun hW => present_not_reclaimable hV2.absSound.1 hdel2 hW, hN2, hnot00,
    ⟨_, _, _, _, hN2⟩, ?_⟩
  intro hBF
  exact (break_free_gate_dichotomy h (zeroLeafHash hl) hl (hThreeRun a b) hR h0 2 a ha.ne').1
    hBF hdel2

/-! ## Witnesses -/

theorem dedicated_padding_premise_witness :
    (∀ hl : LeafHash, ¬ DedicatedPadding hl (zeroLeafHash hl))
      ∧ DedicatedPadding toyLeafHash 1 := by
  refine ⟨fun hl hd => hd rfl, ?_⟩
  show toyLeafHash ⟨0, 0, 0⟩ ≠ 1
  decide

theorem toy_full_snapshot_refund_witness (a : UInt256) (ha : 0 < a) :
    HReaches hSetup (hInsert hSetup a 0)
      ∧ (hInsert hSetup a 0).height = 1
      ∧ (hInsert hSetup a 0).tree.leafCount = 2 ^ (hInsert hSetup a 0).height
      ∧ a ∈ keys (toAbs (hInsert hSetup a 0).tree)
      ∧ DedicatedPadding toyLeafHash 1
      ∧ NonInclusionAccepted toyNodeHash toyLeafHash
          ((hInsert hSetup a 0).root toyNodeHash 1 toyLeafHash) a ⟨0, 0, 0⟩ 0 (fun _ => 0)
          (hInsert hSetup a 0).height := by
  have hg := setup_insertGuard ha
  refine ⟨HReaches.tail (HReaches.refl (S := hSetup)) (U := hSetup) hg, rfl, rfl, ?_,
    dedicated_padding_premise_witness.2, ?_⟩
  · show a ∈ keys (toAbs (Contracts.InteropCommitmentTree.insert setup a 0))
    rw [(insert_sound_step setup_valid hg).2]
    simp
  · refine ⟨ha.ne', ha, Or.inl rfl, ⟨by show (0 : ℕ) < 2 ^ 1; norm_num, ?_⟩⟩
    simp [walkPure, HState.root, HState.height, hInsert, hSetup, setupDims,
      AttackVectors.CapacityInvariant.push, root, rootOf, levels, levelUp, zeros,
      leafHashes, toyNodeHash, toyLeafHash, Contracts.InteropCommitmentTree.insert,
      Contracts.InteropCommitmentTree.setup, List.range_succ, List.headD]

theorem toy_empty_index_refund_witness (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    HReaches hSetup (hThree a b) ∧ (hThree a b).height = 2
      ∧ (hThree a b).tree.leafCount ≤ 3
      ∧ a ∈ keys (toAbs (hThree a b).tree)
      ∧ DedicatedPadding toyLeafHash 1
      ∧ NonInclusionAccepted toyNodeHash toyLeafHash
          ((hThree a b).root toyNodeHash 1 toyLeafHash) a ⟨0, 0, 0⟩ 3
          (fun l => if l = 0 then b + 1 else -b) (hThree a b).height
      ∧ ¬ NonInclusionAccepted toyNodeHash toyLeafHash
          ((hThree a b).root toyNodeHash 1 toyLeafHash) a ⟨0, 0, 0⟩ 3
          (honestSibs toyNodeHash 1 (leafHashes toyLeafHash (hThree a b).tree) 3)
          (hThree a b).height := by
  obtain ⟨_, hdel, _⟩ := padding_collision_refunds_delivered_leg toyNodeHash toyLeafHash ha hab
  refine ⟨hThree_reaches ha hab, rfl, le_refl _, hdel, dedicated_padding_premise_witness.2, ?_, ?_⟩
  · refine ⟨ha.ne', ha, Or.inl rfl, ⟨by show (3 : ℕ) < 2 ^ 2; norm_num, ?_⟩⟩
    simp [walkPure, HState.root, HState.height, hThree, hInsert, hSetup, setupDims,
      AttackVectors.CapacityInvariant.push, root, rootOf, levels, levelUp, zeros,
      leafHashes, toyNodeHash, toyLeafHash, Contracts.InteropCommitmentTree.insert,
      Contracts.InteropCommitmentTree.setup, List.range_succ, List.headD]
    ring
  · intro hN
    have hrec := hN.path.recompute
    revert hrec
    simp [walkPure, honestSibs, sibIdx, HState.root, HState.height, hThree, hInsert, hSetup,
      setupDims, AttackVectors.CapacityInvariant.push, root, rootOf, levels, levelUp, zeros,
      leafHashes, toyNodeHash, toyLeafHash, Contracts.InteropCommitmentTree.insert,
      Contracts.InteropCommitmentTree.setup, List.range_succ, List.headD, List.getD,
      Option.getD]

theorem finality_premises_witness (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    HRun (hThreeRun a b) ∧ hThreeRun a b 0 = hSetup
      ∧ Monotone witnessClock ∧ witnessClock 2 ≤ 0
      ∧ a ∈ keys (absHistory (hThreeRun a b) 2)
      ∧ (0 : UInt256) < witnessClock (2 + 1) := by
  obtain ⟨hR, h0, _⟩ := hThreeRun_witness a b ha hab
  obtain ⟨_, hdel, _⟩ := padding_collision_refunds_delivered_leg toyNodeHash toyLeafHash ha hab
  refine ⟨hR, h0, ?_, by decide, hdel, by decide⟩
  intro m n hmn
  unfold witnessClock
  split_ifs with h1 h2 h2
  · exact le_refl _
  · decide
  · omega
  · exact le_refl _

/-! ## The readings fail at the pin -/

theorem pinned_reclaim_dichotomy_reading_fails (h : Hash) (hl : LeafHash) :
    ¬ ReclaimDichotomyReading h (zeroLeafHash hl) hl := by
  intro hread
  have h01 : (0 : UInt256) < 1 := by decide
  have h12 : (1 : UInt256) < 2 := by decide
  obtain ⟨hR, h0, _, _, hdel, _, _, _, hDep, _⟩ :=
    pinned_counterexample_meets_capstone_hypotheses h hl 1 2 h01 h12
  exact ((hread (hThreeRun 1 2) hR h0 2 1 h01.ne').1 hDep) hdel

theorem pinned_delivery_finality_reading_fails (h : Hash) (hl : LeafHash) :
    ¬ DeliveryFinalityReading h (zeroLeafHash hl) hl := by
  intro hread
  have h01 : (0 : UInt256) < 1 := by decide
  have h12 : (1 : UInt256) < 2 := by decide
  obtain ⟨hR, h0, _, _, _, _, _, _, hDep, _⟩ :=
    pinned_counterexample_meets_capstone_hypotheses h hl 1 2 h01 h12
  obtain ⟨_, _, hmono, hti, hdel, hpin⟩ := finality_premises_witness 1 2 h01 h12
  exact hread (hThreeRun 1 2) hR h0 witnessClock 0 1 2 hmono hti hdel 2 hpin hDep

end IMTAbstract.ReclaimGateFaithful

/-! ## Certificates -/

namespace IMTAbstract.ReclaimGateFaithful

theorem PinnedGateAcceptsEveryValueBelowCapacity :
    Properties.PinnedGateAcceptsEveryValueBelowCapacity :=
  pinned_gate_accepts_every_value_below_capacity
theorem ReachedBelowCapacityIffNotPowerOfTwo : Properties.ReachedBelowCapacityIffNotPowerOfTwo :=
  reached_below_capacity_iff_not_power_of_two
theorem PinnedGateAcceptsEveryValueOffPowersOfTwo :
    Properties.PinnedGateAcceptsEveryValueOffPowersOfTwo :=
  pinned_gate_accepts_every_value_off_powers_of_two
theorem PinnedCounterexampleMeetsCapstoneHypotheses :
    Properties.PinnedCounterexampleMeetsCapstoneHypotheses :=
  pinned_counterexample_meets_capstone_hypotheses
theorem PinnedReclaimDichotomyReadingFails : Properties.PinnedReclaimDichotomyReadingFails :=
  pinned_reclaim_dichotomy_reading_fails
theorem PinnedDeliveryFinalityReadingFails : Properties.PinnedDeliveryFinalityReadingFails :=
  pinned_delivery_finality_reading_fails
theorem BreakFreeGateImpliesMemberGate : Properties.BreakFreeGateImpliesMemberGate :=
  break_free_gate_implies_member_gate
theorem DeployedGateLiveness : Properties.DeployedGateLiveness := deployed_gate_liveness
theorem BreakFreeGateDichotomy : Properties.BreakFreeGateDichotomy := break_free_gate_dichotomy
theorem BreakFreeGateMatchesMemberGate : Properties.BreakFreeGateMatchesMemberGate :=
  break_free_gate_matches_member_gate
theorem BreakFreeDeliveryFinality : Properties.BreakFreeDeliveryFinality :=
  break_free_delivery_finality
theorem DeliveredRefundLocatesCollisionOrPaddingHit :
    Properties.DeliveredRefundLocatesCollisionOrPaddingHit :=
  delivered_refund_locates_collision_or_padding_hit
theorem FullSnapshotRefundOfDeliveredNeedsCollision :
    Properties.FullSnapshotRefundOfDeliveredNeedsCollision :=
  full_snapshot_refund_of_delivered_needs_collision
theorem DedicatedPaddingRefundOfDeliveredNeedsCollision :
    Properties.DedicatedPaddingRefundOfDeliveredNeedsCollision :=
  dedicated_padding_refund_of_delivered_needs_collision
theorem DedicatedPaddingZeroLeafNeedsPathCollision :
    Properties.DedicatedPaddingZeroLeafNeedsPathCollision :=
  dedicated_padding_zero_leaf_needs_path_collision
theorem DedicatedPaddingPremiseWitness : Properties.DedicatedPaddingPremiseWitness :=
  dedicated_padding_premise_witness
theorem ToyFullSnapshotRefundWitness : Properties.ToyFullSnapshotRefundWitness :=
  toy_full_snapshot_refund_witness
theorem ToyEmptyIndexRefundWitness : Properties.ToyEmptyIndexRefundWitness :=
  toy_empty_index_refund_witness
theorem FinalityPremisesWitness : Properties.FinalityPremisesWitness :=
  finality_premises_witness

end IMTAbstract.ReclaimGateFaithful
