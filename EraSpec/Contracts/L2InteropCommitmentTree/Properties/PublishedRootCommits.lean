import EraSpec.Contracts.L2InteropCommitmentTree.Specs.PublishedRootCommits

/-!
# Properties: the published root commits the leaf-hash list, or a located collision

Statements about `EraSpec.Contracts.L2InteropCommitmentTree.Specs.PublishedRootCommits`;
proofs in `EraSpec.Contracts.L2InteropCommitmentTree.Proofs.PublishedRootCommits`.

`capacity_ok_root_commits` (FullMerkle `TreeShape`) is vacuous: it takes global
pair-injectivity.  Its pinned form is `MerkleSpec.Pinned.RootOfInjOrCollision`, which still
takes the capacity premise `L.length ≤ 2 ^ height`.  Here the height is the commitment tree's
own `_height`, so the capacity premise is discharged by the run, and the statement is about
the root the contract publishes.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier MerkleSpec.Pinned

/-- **THE PUBLISHED ROOT COMMITS THE LEAF-HASH LIST, OR A LOCATED COLLISION.**  On any state
reached from `hSetup` by guarded inserts, a list of `leafCount` hashes whose root at the
state's own `_height` is the published root IS the list of leaf hashes, or at an index where
it differs from the hash of the leaf stored there, the two trees collide on that index's path.
No capacity premise (the run supplies it) and no hash premise. -/
def Properties.PublishedRootCommitsOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState), HReaches hSetup S →
    ∀ L : List UInt256, L.length = S.tree.leafCount →
      rootOf h z0 L S.height = S.root h z0 hl →
        L = leafHashes hl S.tree
          ∨ ∃ i < S.tree.leafCount, L.getD i z0 ≠ hl (S.tree.leaf i)
              ∧ TreeCollision h z0 L (leafHashes hl S.tree) S.height i

/-- **THE SAME ALONG EVERY RUN.**  At every step `n` of every run from `hSetup`, against the
root published at that step's own `_height`. -/
def Properties.RunRootsCommitOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → HState), HRun R → R 0 = hSetup →
    ∀ (n : ℕ) (L : List UInt256), L.length = (R n).tree.leafCount →
      rootOf h z0 L (R n).height = (R n).root h z0 hl →
        L = leafHashes hl (R n).tree
          ∨ ∃ i < (R n).tree.leafCount, L.getD i z0 ≠ hl ((R n).tree.leaf i)
              ∧ TreeCollision h z0 L (leafHashes hl (R n).tree) (R n).height i

/-- **THE PREMISES ARE MET ON A STATE THE SOURCE REACHES, WITH NO COLLISION, FOR EVERY HASH.**
`hThree a b` (three leaves, at the height 2 the source grows to, one padded slot) is reached
from `hSetup`; its own leaf-hash list meets every premise of `PublishedRootCommitsOrCollision`
and no collision is located on any path.  `hThree a b` is step 2 of the run `hThreeRun a b`,
so the same instance meets the premises of `RunRootsCommitOrCollision`. -/
def Properties.PublishedRootCommitsOrCollisionSatisfiable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    HReaches hSetup (hThree a b) ∧ HRun (hThreeRun a b) ∧ hThreeRun a b 0 = hSetup
      ∧ hThreeRun a b 2 = hThree a b ∧ (hThree a b).height = 2
      ∧ (leafHashes hl (hThree a b).tree).length = (hThree a b).tree.leafCount
      ∧ rootOf h z0 (leafHashes hl (hThree a b).tree) (hThree a b).height
          = (hThree a b).root h z0 hl
      ∧ ∀ i, ¬ TreeCollision h z0 (leafHashes hl (hThree a b).tree)
          (leafHashes hl (hThree a b).tree) (hThree a b).height i

/-- **A FORGED LIST AT THE PUBLISHED ROOT IS LOCATED.**  Under the toy hashes `constHash` (every
node pair collides) and the constant leaf hash `fun _ => 0`, on the reached state `hThree a b`
at its own height 2, the list `[1, 0, 0]` differs from the leaf-hash list `[0, 0, 0]` yet has
the published root; the collision is located on index 0's path.  So the collision disjunct of
`PublishedRootCommitsOrCollision` is the one that holds there. -/
def Properties.PublishedRootForgeryIsLocated : Prop :=
  ∀ a b : UInt256, 0 < a → a < b →
    leafHashes (fun _ => 0) (hThree a b).tree = [0, 0, 0]
      ∧ rootOf constHash 0 [1, 0, 0] (hThree a b).height
          = (hThree a b).root constHash 0 (fun _ => 0)
      ∧ ([1, 0, 0] : List UInt256) ≠ leafHashes (fun _ => 0) (hThree a b).tree
      ∧ TreeCollision constHash 0 [1, 0, 0] (leafHashes (fun _ => 0) (hThree a b).tree)
          (hThree a b).height 0

end Contracts.InteropCommitmentTree
