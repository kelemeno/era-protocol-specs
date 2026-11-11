import EraSpec.Contracts.L2InteropCommitmentTree.Properties.PublishedRootCommits
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.RunHeight
import EraSpec.Contracts.Merkle.Proofs.RootForgeryPinned

/-!
# Proofs: the published root commits the leaf-hash list, or a located collision

Proofs of `EraSpec.Contracts.L2InteropCommitmentTree.Properties.PublishedRootCommits`:
`MerkleSpec.Pinned.root_of_inj_or_collision` with its capacity premise discharged by
`hReaches_capacity`.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier MerkleSpec.Pinned

theorem published_root_commits_or_collision (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (S : HState) (hR : HReaches hSetup S) (L : List UInt256) (hlen : L.length = S.tree.leafCount)
    (hroot : rootOf h z0 L S.height = S.root h z0 hl) :
    L = leafHashes hl S.tree
      ∨ ∃ i < S.tree.leafCount, L.getD i z0 ≠ hl (S.tree.leaf i)
          ∧ TreeCollision h z0 L (leafHashes hl S.tree) S.height i := by
  have hcap := hReaches_capacity hR
  have hlen' : L.length = (leafHashes hl S.tree).length := by rwa [leafHashes_length]
  rcases root_of_inj_or_collision h z0 L (leafHashes hl S.tree) S.height hlen' (by omega) hroot
    with he | ⟨i, hi, hne, hc⟩
  · exact Or.inl he
  · refine Or.inr ⟨i, by omega, ?_, hc⟩
    rwa [leafHashes_getD (by omega)] at hne

theorem run_roots_commit_or_collision (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (R : ℕ → HState) (hR : HRun R) (h0 : R 0 = hSetup) (n : ℕ) (L : List UInt256)
    (hlen : L.length = (R n).tree.leafCount)
    (hroot : rootOf h z0 L (R n).height = (R n).root h z0 hl) :
    L = leafHashes hl (R n).tree
      ∨ ∃ i < (R n).tree.leafCount, L.getD i z0 ≠ hl ((R n).tree.leaf i)
          ∧ TreeCollision h z0 L (leafHashes hl (R n).tree) (R n).height i :=
  published_root_commits_or_collision h z0 hl (R n) (hRun_reaches hR h0 n) L hlen hroot

theorem published_root_commits_or_collision_satisfiable (h : Hash) (z0 : UInt256)
    (hl : LeafHash) (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    HReaches hSetup (hThree a b) ∧ HRun (hThreeRun a b) ∧ hThreeRun a b 0 = hSetup
      ∧ hThreeRun a b 2 = hThree a b ∧ (hThree a b).height = 2
      ∧ (leafHashes hl (hThree a b).tree).length = (hThree a b).tree.leafCount
      ∧ rootOf h z0 (leafHashes hl (hThree a b).tree) (hThree a b).height
          = (hThree a b).root h z0 hl
      ∧ ∀ i, ¬ TreeCollision h z0 (leafHashes hl (hThree a b).tree)
          (leafHashes hl (hThree a b).tree) (hThree a b).height i :=
  ⟨hThree_reaches ha hab, hThreeRun_hRun ha hab, rfl, rfl, rfl, leafHashes_length, rfl,
    fun i => EqualInstancesNeverCollide.1 h z0 _ _ i⟩

theorem published_root_forgery_is_located (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    HReaches hSetup (hThree a b)
      ∧ leafHashes (fun _ => 0) (hThree a b).tree = [0, 0, 0]
      ∧ ([1, 0, 0] : List UInt256).length = (hThree a b).tree.leafCount
      ∧ ([1, 0, 0] : List UInt256).length ≤ 2 ^ (hThree a b).height
      ∧ rootOf constHash 0 [1, 0, 0] (hThree a b).height
          = (hThree a b).root constHash 0 (fun _ => 0)
      ∧ ([1, 0, 0] : List UInt256) ≠ leafHashes (fun _ => 0) (hThree a b).tree
      ∧ ¬ PaddingHit 0 [1, 0, 0] (leafHashes (fun _ => 0) (hThree a b).tree)
      ∧ ([1, 0, 0] : List UInt256).getD 0 0 ≠ (fun _ => (0 : UInt256)) ((hThree a b).tree.leaf 0)
      ∧ TreeCollision constHash 0 [1, 0, 0] (leafHashes (fun _ => 0) (hThree a b).tree)
          (hThree a b).height 0 := by
  have hc : (hThree a b).tree.leafCount = 3 := rfl
  have hL : leafHashes (fun _ => 0) (hThree a b).tree = [0, 0, 0] := by
    simp [leafHashes, hc, List.range_succ]
  have hH : (hThree a b).height = 2 := rfl
  have hR : (hThree a b).root constHash 0 (fun _ => 0)
      = rootOf constHash 0 (leafHashes (fun _ => 0) (hThree a b).tree) (hThree a b).height := rfl
  refine ⟨hThree_reaches ha hab, hL, by rw [hc]; rfl, ?_⟩
  rw [hR, hL, hH]
  unfold PaddingHit TreeCollision
  beta_reduce
  decide

/-! ## Any length -/

theorem published_root_commits_any_length_or_break (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (S : HState) (hR : HReaches hSetup S) (L : List UInt256) (hcapL : L.length ≤ 2 ^ S.height)
    (hroot : rootOf h z0 L S.height = S.root h z0 hl) :
    L = leafHashes hl S.tree
      ∨ PaddingHit z0 L (leafHashes hl S.tree)
      ∨ ∃ i < max L.length S.tree.leafCount,
          L.getD i z0 ≠ (leafHashes hl S.tree).getD i z0
            ∧ TreeCollision h z0 L (leafHashes hl S.tree) S.height i := by
  have hcap : (leafHashes hl S.tree).length ≤ 2 ^ S.height := by
    rw [leafHashes_length]; exact hReaches_capacity hR
  have hb := root_commits_list_or_break h z0 L (leafHashes hl S.tree) S.height hcapL hcap hroot
  rwa [leafHashes_length] at hb

theorem run_roots_commit_any_length_or_break (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (R : ℕ → HState) (hR : HRun R) (h0 : R 0 = hSetup) (n : ℕ) (L : List UInt256)
    (hcapL : L.length ≤ 2 ^ (R n).height)
    (hroot : rootOf h z0 L (R n).height = (R n).root h z0 hl) :
    L = leafHashes hl (R n).tree
      ∨ PaddingHit z0 L (leafHashes hl (R n).tree)
      ∨ ∃ i < max L.length (R n).tree.leafCount,
          L.getD i z0 ≠ (leafHashes hl (R n).tree).getD i z0
            ∧ TreeCollision h z0 L (leafHashes hl (R n).tree) (R n).height i :=
  published_root_commits_any_length_or_break h z0 hl (R n) (hRun_reaches hR h0 n) L hcapL hroot

theorem published_root_commits_any_length_or_break_satisfiable (h : Hash) (z0 : UInt256)
    (hl : LeafHash) (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    HReaches hSetup (hThree a b) ∧ HRun (hThreeRun a b) ∧ hThreeRun a b 0 = hSetup
      ∧ hThreeRun a b 2 = hThree a b
      ∧ (leafHashes hl (hThree a b).tree).length ≤ 2 ^ (hThree a b).height
      ∧ rootOf h z0 (leafHashes hl (hThree a b).tree) (hThree a b).height
          = (hThree a b).root h z0 hl
      ∧ ¬ PaddingHit z0 (leafHashes hl (hThree a b).tree) (leafHashes hl (hThree a b).tree)
      ∧ ∀ i, ¬ TreeCollision h z0 (leafHashes hl (hThree a b).tree)
          (leafHashes hl (hThree a b).tree) (hThree a b).height i := by
  have hR := hThree_reaches ha hab
  refine ⟨hR, hThreeRun_hRun ha hab, rfl, rfl, ?_, rfl,
    EqualInstancesNeverCollide.2.2.2 z0 _, fun i => EqualInstancesNeverCollide.1 h z0 _ _ i⟩
  rw [leafHashes_length]
  exact hReaches_capacity hR

theorem published_root_padding_hit_fires (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    HReaches hSetup (hThree a b)
      ∧ (leafHashes hl (hThree a b).tree ++ [z0]).length ≤ 2 ^ (hThree a b).height
      ∧ rootOf h z0 (leafHashes hl (hThree a b).tree ++ [z0]) (hThree a b).height
          = (hThree a b).root h z0 hl
      ∧ leafHashes hl (hThree a b).tree ++ [z0] ≠ leafHashes hl (hThree a b).tree
      ∧ PaddingHit z0 (leafHashes hl (hThree a b).tree ++ [z0]) (leafHashes hl (hThree a b).tree)
      ∧ ∀ i, ¬ TreeCollision h z0 (leafHashes hl (hThree a b).tree ++ [z0])
          (leafHashes hl (hThree a b).tree) (hThree a b).height i := by
  -- Appending the padding constant changes no padded entry, so it is the same tree.
  have hsame := same_tree_of_getD_eq h z0 (leafHashes hl (hThree a b).tree ++ [z0])
    (leafHashes hl (hThree a b).tree) (getD_append_pad z0 _) (hThree a b).height
  have hc : (hThree a b).tree.leafCount = 3 := rfl
  have hH : (hThree a b).height = 2 := rfl
  refine ⟨hThree_reaches ha hab, ?_, hsame.1, ?_,
    Or.inr ⟨by simp, getD_append_singleton _ _ _⟩, hsame.2⟩
  · rw [List.length_append, leafHashes_length, hc, hH, List.length_singleton]
    decide
  · exact fun he => by simpa using congrArg List.length he

/-! ## Certificates -/

theorem PublishedRootCommitsOrCollision : Properties.PublishedRootCommitsOrCollision :=
  published_root_commits_or_collision
theorem RunRootsCommitOrCollision : Properties.RunRootsCommitOrCollision :=
  run_roots_commit_or_collision
theorem PublishedRootCommitsOrCollisionSatisfiable :
    Properties.PublishedRootCommitsOrCollisionSatisfiable :=
  published_root_commits_or_collision_satisfiable
theorem PublishedRootForgeryIsLocated : Properties.PublishedRootForgeryIsLocated :=
  published_root_forgery_is_located
theorem PublishedRootCommitsAnyLengthOrBreak : Properties.PublishedRootCommitsAnyLengthOrBreak :=
  published_root_commits_any_length_or_break
theorem RunRootsCommitAnyLengthOrBreak : Properties.RunRootsCommitAnyLengthOrBreak :=
  run_roots_commit_any_length_or_break
theorem PublishedRootCommitsAnyLengthOrBreakSatisfiable :
    Properties.PublishedRootCommitsAnyLengthOrBreakSatisfiable :=
  published_root_commits_any_length_or_break_satisfiable
theorem PublishedRootPaddingHitFires : Properties.PublishedRootPaddingHitFires :=
  published_root_padding_hit_fires

end Contracts.InteropCommitmentTree
