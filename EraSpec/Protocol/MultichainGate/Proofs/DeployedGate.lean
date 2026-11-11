import EraSpec.Protocol.MultichainGate.Properties.DeployedGate
import EraSpec.Protocol.MultichainGate.Proofs.Model
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.TreeRoot
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.RunHeight
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Reaches
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.HintSearch

/-!
# The source-bound refund gate as deployed: proofs

Certificates for `EraSpec.Protocol.MultichainGate.Properties.DeployedGate`.  The
countermodel is `Contracts.InteropCommitmentTree.padding_forgery_at_own_height` lifted to
a family of chain states; the safety forms are
`Contracts.InteropCommitmentTree.verified_absence_excludes_delivered_or_break` on the
source chain's state, with the case split of `accept_pins_entry_any_length_or_break`
redone where the full-tree argument needs to know which case produced the break.
-/

namespace Contracts.Protocol

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-! ## Reading the states -/

/-- A state reached from `setup` is a valid contract state. -/
lemma deployedGate_valid_of_hReaches {S : HState} (hR : HReaches hSetup S) : Valid S.tree :=
  reaches_valid (hReaches_projects hR) setup_valid

lemma paddingStates_zero (a b : UInt256) : paddingStates a b 0 = hThree a b := by
  simp [paddingStates]

lemma paddingStates_other {a b : UInt256} {c : Chain} (hc : c ≠ 0) :
    paddingStates a b c = hSetup := by
  simp [paddingStates, hc]

lemma paddingStates_fromSetup {a b : UInt256} (ha : 0 < a) (hab : a < b) :
    StatesFromSetup (paddingStates a b) := by
  intro c
  by_cases hc : c = 0
  · subst hc
    rw [paddingStates_zero]
    exact hThree_reaches ha hab
  · rw [paddingStates_other hc]
    exact HReaches.refl

/-! ## The countermodel -/

theorem pinned_padding_deployed_gate_refunds_delivered_leg (h : Hash) (hl : LeafHash)
    (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    StatesFromSetup (paddingStates a b)
      ∧ (∀ c, Valid (paddingStates a b c).tree)
      ∧ Delivered (ofStates (paddingStates a b)) 0 a
      ∧ ¬ BoundGate (ofStates (paddingStates a b)) 0 a
      ∧ (paddingStates a b 0).height = 2
      ∧ DeployedBoundGateBy h (pinPadding hl) hl (paddingStates a b) 0 a ⟨0, 0, 0⟩ 3
          (paddingSlotSibs h hl a b) 2
      ∧ TreeRootBreakExactly h (pinPadding hl) hl (paddingStates a b 0).tree 2
          (paddingSlotSibs h hl a b) 2 3 ⟨0, 0, 0⟩ .paddingHit := by
  obtain ⟨_, _, _, _, hN, _, hex⟩ := padding_forgery_at_own_height h hl a b ha hab
  have hSt := paddingStates_fromSetup ha hab
  have hdel : Delivered (ofStates (paddingStates a b)) 0 a := by
    show a ∈ keys (toAbs (paddingStates a b 0).tree)
    rw [paddingStates_zero]
    exact (padding_collision_refunds_delivered_leg h hl ha hab).2.1
  refine ⟨hSt, fun c => deployedGate_valid_of_hReaches (hSt c), hdel, ?_, ?_, ?_, ?_⟩
  · intro hg
    exact bound_gate_excludes_delivered (deployedGate_valid_of_hReaches (hSt 0)).absSound hdel hg
  · rw [paddingStates_zero]; rfl
  · show NonInclusionAccepted h hl ((paddingStates a b 0).root h (pinPadding hl) hl) a ⟨0, 0, 0⟩ 3
      (paddingSlotSibs h hl a b) 2
    rw [paddingStates_zero]
    exact hN
  · rw [paddingStates_zero]
    exact hex

theorem chains_no_double_spend_fails_for_deployed_gate (h : Hash) (hl : LeafHash) :
    ∃ (St : ChainStates) (src : Chain) (v : UInt256),
      StatesFromSetup St ∧ Delivered (ofStates St) src v
        ∧ DeployedBoundGate h (pinPadding hl) hl St src v := by
  obtain ⟨hSt, _, hdel, _, _, hg, _⟩ :=
    pinned_padding_deployed_gate_refunds_delivered_leg h hl 1 2 (by decide) (by decide)
  exact ⟨paddingStates 1 2, 0, 1, hSt, hdel, ⟨_, _, _, _, hg⟩⟩

theorem chains_bound_gate_iff_undelivered_fails_for_deployed_gate (h : Hash) (hl : LeafHash) :
    ∃ (St : ChainStates) (src : Chain) (v : UInt256),
      StatesFromSetup St ∧ v ≠ 0
        ∧ ¬ (DeployedBoundGate h (pinPadding hl) hl St src v ↔ ¬ Delivered (ofStates St) src v) := by
  obtain ⟨hSt, _, hdel, _, _, hg, _⟩ :=
    pinned_padding_deployed_gate_refunds_delivered_leg h hl 1 2 (by decide) (by decide)
  exact ⟨paddingStates 1 2, 0, 1, hSt, by decide, fun hiff => hiff.mp ⟨_, _, _, _, hg⟩ hdel⟩

/-! ## The replacements -/

theorem deployed_bound_gate_excludes_delivered_or_break {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {St : ChainStates} {src : Chain} (hR : HReaches hSetup (St src))
    {v : UInt256} (hdel : Delivered (ofStates St) src v) {ℓ : Leaf} {idx : ℕ}
    {sibs : ℕ → UInt256} {k : ℕ} (hg : DeployedBoundGateBy h z0 hl St src v ℓ idx sibs k) :
    TreeRootBreak h z0 hl (St src).tree (St src).height sibs k idx ℓ := by
  rcases verified_absence_excludes_delivered_or_break (T := (St src).tree)
      (height := (St src).height) (deployedGate_valid_of_hReaches hR) hg with hnot | hb
  · exact absurd hdel hnot
  · exact hb

theorem deployed_bound_gate_separated_padding_needs_collision {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {St : ChainStates} {src : Chain} (hR : HReaches hSetup (St src))
    {v : UInt256} (hdel : Delivered (ofStates St) src v) {ℓ : Leaf} {idx : ℕ}
    {sibs : ℕ → UInt256} {k : ℕ} (hsep : hl ℓ ≠ z0)
    (hg : DeployedBoundGateBy h z0 hl St src v ℓ idx sibs k) :
    CollisionBreak h z0 hl (St src).tree (St src).height sibs k idx ℓ := by
  cases deployed_bound_gate_excludes_delivered_or_break hR hdel hg with
  | wrongLength hh => exact Or.inl hh
  | pathCollision hk hc => exact Or.inr (Or.inl ⟨hk, hc⟩)
  | leafCollision hi hne he => exact Or.inr (Or.inr ⟨hi, hne, he⟩)
  | paddingHit _ hz => exact absurd hz hsep

/-- On a full tree an accepted path pins the presented leaf at an occupied index, or
carries a `CollisionBreak`: the `paddingHit` branch of `accepted_path_pins_leaf_or_break`
needs an opened index past the leaf count at the tree's own length, which a full tree
does not have. -/
theorem accepted_path_full_tree_pins_leaf_or_collision {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {T : Tree} {height : ℕ} (hfull : T.leafCount = 2 ^ height)
    {sibs : ℕ → UInt256} {k idx : ℕ} {ℓ : Leaf}
    (hp : PathAccepts h (root h z0 hl T height) sibs k idx (hl ℓ)) :
    (k = height ∧ idx < T.leafCount ∧ T.leaf idx = ℓ)
      ∨ CollisionBreak h z0 hl T height sibs k idx ℓ := by
  rcases accept_pins_entry_any_length_or_break h z0 (leafHashes hl T) sibs k height idx (hl ℓ)
      hp.inBounds hp.recompute with ⟨hk, hget⟩ | ⟨hk, hc⟩ | hb
  · have hidx : idx < T.leafCount := by
      have h1 := hp.inBounds
      rw [hk, ← hfull] at h1
      exact h1
    rw [leafHashes_getD hidx] at hget
    by_cases hle : T.leaf idx = ℓ
    · exact Or.inl ⟨hk, hidx, hle⟩
    · exact Or.inr (Or.inr (Or.inr ⟨hidx, hle, hget⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hk, hc⟩))
  · exact Or.inr (Or.inl hb)

theorem deployed_bound_gate_full_tree_needs_collision {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {St : ChainStates} {src : Chain} (hR : HReaches hSetup (St src))
    (hfull : FullAtOwnHeight (St src)) {v : UInt256} (hdel : Delivered (ofStates St) src v)
    {ℓ : Leaf} {idx : ℕ} {sibs : ℕ → UInt256} {k : ℕ}
    (hg : DeployedBoundGateBy h z0 hl St src v ℓ idx sibs k) :
    CollisionBreak h z0 hl (St src).tree (St src).height sibs k idx ℓ := by
  rcases accepted_path_full_tree_pins_leaf_or_collision (z0 := z0) hfull hg.path
    with ⟨_, hidx, hleaf⟩ | hc
  · exfalso
    have hW : ∃ W ∈ toAbs (St src).tree, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey) :=
      ⟨⟨ℓ.value, ℓ.nextValue⟩, mem_toAbs.mpr ⟨idx, hidx, by rw [hleaf], by rw [hleaf]⟩,
        hg.lowBelow, hg.window⟩
    exact present_not_reclaimable (deployedGate_valid_of_hReaches hR).absSound.1 hdel hW
  · exact hc

theorem deployed_bound_gate_live_on_undelivered {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {St : ChainStates} {src : Chain} (hR : HReaches hSetup (St src)) {v : UInt256}
    (hv : v ≠ 0) (hund : ¬ Delivered (ofStates St) src v) :
    ∃ i < (St src).tree.leafCount,
      DeployedBoundGateBy h z0 hl St src v ((St src).tree.leaf i) i
          (honestSibs h z0 (leafHashes hl (St src).tree) i) (St src).height
        ∧ ¬ TreeRootBreak h z0 hl (St src).tree (St src).height
            (honestSibs h z0 (leafHashes hl (St src).tree) i) (St src).height i
            ((St src).tree.leaf i) :=
  (proofs_exclusive_or_break_at_own_height h z0 hl (St src) hR).2.1 v hv hund

theorem deployed_bound_gate_iff_abstract_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {St : ChainStates} {src : Chain} (hR : HReaches hSetup (St src)) {v : UInt256}
    (hv : v ≠ 0) :
    DeployedBoundGate h z0 hl St src v
      ↔ BoundGate (ofStates St) src v
        ∨ ∃ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
            DeployedBoundGateBy h z0 hl St src v ℓ idx sibs k
              ∧ TreeRootBreak h z0 hl (St src).tree (St src).height sibs k idx ℓ := by
  constructor
  · rintro ⟨ℓ, idx, sibs, k, hg⟩
    rcases non_inclusion_sound_or_break (T := (St src).tree) (height := (St src).height) hg
      with hW | hb
    · exact Or.inl hW
    · exact Or.inr ⟨ℓ, idx, sibs, k, hg, hb⟩
  · rintro (hB | ⟨ℓ, idx, sibs, k, hg, _⟩)
    · have hund : ¬ Delivered (ofStates St) src v := fun hdel =>
        bound_gate_excludes_delivered (deployedGate_valid_of_hReaches hR).absSound hdel hB
      obtain ⟨i, _, hg, _⟩ := deployed_bound_gate_live_on_undelivered (z0 := z0) (hl := hl) hR hv hund
      exact ⟨_, _, _, _, hg⟩
    · exact ⟨ℓ, idx, sibs, k, hg⟩

/-! ## Anti-vacuity -/

lemma twoLeafState_tree (a : UInt256) : (twoLeafState a).tree = insert setup a 0 := rfl

lemma twoLeafState_height (a : UInt256) : (twoLeafState a).height = 1 := rfl

lemma twoLeafState_reaches {a : UInt256} (ha : 0 < a) : HReaches hSetup (twoLeafState a) :=
  HReaches.tail (HReaches.refl (S := hSetup)) (U := hSetup) (setup_insertGuard ha)

lemma twoLeafState_delivered {a : UInt256} (ha : 0 < a) :
    a ∈ keys (toAbs (twoLeafState a).tree) := by
  rw [twoLeafState_tree, (insert_sound_step setup_valid (setup_insertGuard ha)).2]
  exact Finset.mem_insert_self _ _

theorem full_at_own_height_examples (a b : UInt256) (ha : 0 < a) :
    HReaches hSetup (twoLeafState a)
      ∧ FullAtOwnHeight hSetup ∧ FullAtOwnHeight (twoLeafState a)
      ∧ ¬ FullAtOwnHeight (hThree a b) := by
  refine ⟨twoLeafState_reaches ha, ?_, ?_, ?_⟩
  · show (1 : ℕ) = 2 ^ 0
    norm_num
  · show (2 : ℕ) = 2 ^ 1
    norm_num
  · show ¬ ((3 : ℕ) = 2 ^ 2)
    norm_num

theorem deployed_gate_collision_premises_satisfiable :
    HReaches hSetup (twoLeafState 2)
      ∧ FullAtOwnHeight (twoLeafState 2)
      ∧ Delivered (ofStates (fun _ => twoLeafState 2)) 0 2
      ∧ toyLeafHash toyCollidingLowLeaf ≠ pinPadding toyLeafHash
      ∧ DeployedBoundGateBy toyNodeHash (pinPadding toyLeafHash) toyLeafHash
          (fun _ => twoLeafState 2) 0 2 toyCollidingLowLeaf 0
          (honestSibs toyNodeHash (pinPadding toyLeafHash)
            (leafHashes toyLeafHash (twoLeafState 2).tree) 0) 1
      ∧ TreeRootBreakExactly toyNodeHash (pinPadding toyLeafHash) toyLeafHash
          (twoLeafState 2).tree 1
          (honestSibs toyNodeHash (pinPadding toyLeafHash)
            (leafHashes toyLeafHash (twoLeafState 2).tree) 0) 1 0 toyCollidingLowLeaf
          .leafCollision := by
  have h2 : (0 : UInt256) < 2 := by decide
  have hcount : (twoLeafState 2).tree.leafCount = 2 := rfl
  have hleaf0 : (twoLeafState 2).tree.leaf 0 = ⟨0, 1, 2⟩ := rfl
  have hcoll : toyLeafHash ((twoLeafState 2).tree.leaf 0) = toyLeafHash toyCollidingLowLeaf := by
    rw [hleaf0]
    simp only [toyLeafHash, toyCollidingLowLeaf]
    decide
  have hget : (leafHashes toyLeafHash (twoLeafState 2).tree).getD 0 (pinPadding toyLeafHash)
      = toyLeafHash toyCollidingLowLeaf := by
    rw [leafHashes_getD (by rw [hcount]; norm_num), hcoll]
  have hne : (twoLeafState 2).tree.leaf 0 ≠ toyCollidingLowLeaf := by
    rw [hleaf0]; decide
  refine ⟨twoLeafState_reaches h2, (full_at_own_height_examples 2 3 h2).2.2.1,
    twoLeafState_delivered h2, ?_, ?_, ?_⟩
  · simp only [toyLeafHash, toyCollidingLowLeaf, pinPadding]
    decide
  · refine ⟨by decide, by decide, Or.inr (by decide), ⟨by norm_num, ?_⟩⟩
    have := honest_walk_root toyNodeHash (pinPadding toyLeafHash)
      (leafHashes toyLeafHash (twoLeafState 2).tree) 1 0 (by norm_num)
    rw [hget] at this
    exact this
  · refine treeRootBreakExactly_of ⟨by rw [hcount]; norm_num, hne, hcoll⟩ ?_
    intro c' hc'
    cases c' with
    | wrongLength => exact not_wrongLength_at_height
    | pathCollision =>
        rintro ⟨_, hpc⟩
        apply honest_walk_no_collision toyNodeHash (pinPadding toyLeafHash)
          (leafHashes toyLeafHash (twoLeafState 2).tree) 1 0
        rw [hget]; exact hpc
    | leafCollision => exact absurd rfl hc'
    | paddingHit =>
        rintro ⟨hle, _⟩
        rw [hcount] at hle
        exact absurd hle (by norm_num)

end Contracts.Protocol

/-! ## Certificates -/

namespace Contracts.Protocol

theorem PinnedPaddingDeployedGateRefundsDeliveredLeg :
    Properties.PinnedPaddingDeployedGateRefundsDeliveredLeg :=
  pinned_padding_deployed_gate_refunds_delivered_leg
theorem ChainsNoDoubleSpendFailsForDeployedGate :
    Properties.ChainsNoDoubleSpendFailsForDeployedGate :=
  chains_no_double_spend_fails_for_deployed_gate
theorem ChainsBoundGateIffUndeliveredFailsForDeployedGate :
    Properties.ChainsBoundGateIffUndeliveredFailsForDeployedGate :=
  chains_bound_gate_iff_undelivered_fails_for_deployed_gate
theorem DeployedBoundGateExcludesDeliveredOrBreak :
    Properties.DeployedBoundGateExcludesDeliveredOrBreak :=
  fun _ _ _ _ _ hR _ hdel _ _ _ _ hg => deployed_bound_gate_excludes_delivered_or_break hR hdel hg
theorem DeployedBoundGateSeparatedPaddingNeedsCollision :
    Properties.DeployedBoundGateSeparatedPaddingNeedsCollision :=
  fun _ _ _ _ _ hR _ hdel _ _ _ _ hsep hg =>
    deployed_bound_gate_separated_padding_needs_collision hR hdel hsep hg
theorem DeployedBoundGateFullTreeNeedsCollision :
    Properties.DeployedBoundGateFullTreeNeedsCollision :=
  fun _ _ _ _ _ hR hfull _ hdel _ _ _ _ hg =>
    deployed_bound_gate_full_tree_needs_collision hR hfull hdel hg
theorem DeployedBoundGateLiveOnUndelivered : Properties.DeployedBoundGateLiveOnUndelivered :=
  fun _ _ _ _ _ hR _ hv hund => deployed_bound_gate_live_on_undelivered hR hv hund
theorem DeployedBoundGateIffAbstractOrBreak : Properties.DeployedBoundGateIffAbstractOrBreak :=
  fun _ _ _ _ _ hR _ hv => deployed_bound_gate_iff_abstract_or_break hR hv
theorem DeployedGateCollisionPremisesSatisfiable :
    Properties.DeployedGateCollisionPremisesSatisfiable :=
  deployed_gate_collision_premises_satisfiable
theorem FullAtOwnHeightExamples : Properties.FullAtOwnHeightExamples :=
  fun a b ha => full_at_own_height_examples a b ha

end Contracts.Protocol
