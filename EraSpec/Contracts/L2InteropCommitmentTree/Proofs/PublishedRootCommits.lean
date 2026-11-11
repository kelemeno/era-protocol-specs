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
  have hlen' : L.length = (leafHashes hl S.tree).length := by rw [leafHashes_length]; exact hlen
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

theorem published_root_forgery_is_located (a b : UInt256) (_ha : 0 < a) (_hab : a < b) :
    leafHashes (fun _ => 0) (hThree a b).tree = [0, 0, 0]
      ∧ rootOf constHash 0 [1, 0, 0] (hThree a b).height
          = (hThree a b).root constHash 0 (fun _ => 0)
      ∧ ([1, 0, 0] : List UInt256) ≠ leafHashes (fun _ => 0) (hThree a b).tree
      ∧ TreeCollision constHash 0 [1, 0, 0] (leafHashes (fun _ => 0) (hThree a b).tree)
          (hThree a b).height 0 := by
  have hL : leafHashes (fun _ => 0) (hThree a b).tree = [0, 0, 0] := by
    have hc : (hThree a b).tree.leafCount = 3 := rfl
    simp [leafHashes, hc, List.range_succ]
  have hH : (hThree a b).height = 2 := rfl
  have hR : (hThree a b).root constHash 0 (fun _ => 0)
      = rootOf constHash 0 (leafHashes (fun _ => 0) (hThree a b).tree) (hThree a b).height := rfl
  rw [hR, hL, hH]
  unfold TreeCollision
  decide

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

end Contracts.InteropCommitmentTree
