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

Two forms:

* `PublishedRootCommitsOrCollision` / `RunRootsCommitOrCollision` — a list of exactly
  `leafCount` hashes: the leaf-hash list, or a located `TreeCollision`.
* `PublishedRootCommitsAnyLengthOrBreak` / `RunRootsCommitAnyLengthOrBreak` — a list of any
  length within the state's capacity `2 ^ _height` (the one premise the run does not supply,
  since it is about the attacker's list): the leaf-hash list, or a `PaddingHit`, or a located
  `TreeCollision`.  `PublishedRootPaddingHitFires` shows the padding hit is reached on a
  reached state for every hash: the published root does not commit `leafCount`.
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
at its own height 2, the list `[1, 0, 0]` (as many entries as the tree has leaves, within the
capacity 4) differs from the leaf-hash list `[0, 0, 0]` yet has the published root.  It is no
padding hit (equal lengths), it differs from the leaf hash at index 0, and the collision is
located on index 0's path.  So this meets the premises of `PublishedRootCommitsOrCollision` and
of `PublishedRootCommitsAnyLengthOrBreak`, and the collision disjunct is the one that holds. -/
def Properties.PublishedRootForgeryIsLocated : Prop :=
  ∀ a b : UInt256, 0 < a → a < b →
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
          (hThree a b).height 0

/-! ## Any length: the padding hit is the other way out -/

/-- **ANY LENGTH WITHIN CAPACITY: THE LEAF-HASH LIST, A PADDING HIT, OR A LOCATED COLLISION.**
`MerkleSpec.Pinned.RootCommitsListOrBreak` at the commitment tree's own `_height`.  On any
state reached from `hSetup` by guarded inserts, a list `L` of at most `2 ^ _height` hashes
whose root at that height is the published root is one of:

1. the list of leaf hashes;
2. a `PaddingHit z0 L (leafHashes hl S.tree)`: `L` is shorter and the tree's leaf hash at index
   `L.length` IS the padding constant, or `L` is longer and `L`'s entry at index `leafCount`
   IS the padding constant (the slot the tree itself pads with `z0`);
3. at an index `i` below both lengths' maximum where `L` differs from the tree's level-0 entry
   (the leaf hash, or `z0` past `leafCount`), a `TreeCollision` on `i`'s path.

The capacity of the leaf-hash list comes from the run (`HReachesCapacity`); the capacity of
`L` is a premise because `L` is the attacker's (a list longer than `2 ^ _height` has entries
the root does not commit at all).  No hash premise.

Each case is reached alone on the reached state `hThree a b`: case 1 with neither break
(`PublishedRootCommitsAnyLengthOrBreakSatisfiable`), case 2 for every hash
(`PublishedRootPaddingHitFires`), and case 3 under toy hashes (`PublishedRootForgeryIsLocated`:
the list `[1, 0, 0]` has `3 ≤ 2 ^ 2` entries, the same length as the tree, so no padding hit). -/
def Properties.PublishedRootCommitsAnyLengthOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState), HReaches hSetup S →
    ∀ L : List UInt256, L.length ≤ 2 ^ S.height →
      rootOf h z0 L S.height = S.root h z0 hl →
        L = leafHashes hl S.tree
          ∨ PaddingHit z0 L (leafHashes hl S.tree)
          ∨ ∃ i < max L.length S.tree.leafCount,
              L.getD i z0 ≠ (leafHashes hl S.tree).getD i z0
                ∧ TreeCollision h z0 L (leafHashes hl S.tree) S.height i

/-- **THE SAME ALONG EVERY RUN.**  At every step `n` of every run from `hSetup`, against the
root published at that step's own `_height`. -/
def Properties.RunRootsCommitAnyLengthOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → HState), HRun R → R 0 = hSetup →
    ∀ (n : ℕ) (L : List UInt256), L.length ≤ 2 ^ (R n).height →
      rootOf h z0 L (R n).height = (R n).root h z0 hl →
        L = leafHashes hl (R n).tree
          ∨ PaddingHit z0 L (leafHashes hl (R n).tree)
          ∨ ∃ i < max L.length (R n).tree.leafCount,
              L.getD i z0 ≠ (leafHashes hl (R n).tree).getD i z0
                ∧ TreeCollision h z0 L (leafHashes hl (R n).tree) (R n).height i

/-- **THE ANY-LENGTH PREMISES, MET WITH NEITHER BREAK, FOR EVERY HASH.**  On the reached state
`hThree a b` at its own height 2, the leaf-hash list itself (three entries, within the capacity
4) has the published root, no padding hit against itself, and no collision located on any
path.  `hThree a b` is step 2 of the run `hThreeRun a b` from `hSetup`, so the same instance
meets the premises of `RunRootsCommitAnyLengthOrBreak` at `n = 2`. -/
def Properties.PublishedRootCommitsAnyLengthOrBreakSatisfiable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    HReaches hSetup (hThree a b) ∧ HRun (hThreeRun a b) ∧ hThreeRun a b 0 = hSetup
      ∧ hThreeRun a b 2 = hThree a b
      ∧ (leafHashes hl (hThree a b).tree).length ≤ 2 ^ (hThree a b).height
      ∧ rootOf h z0 (leafHashes hl (hThree a b).tree) (hThree a b).height
          = (hThree a b).root h z0 hl
      ∧ ¬ PaddingHit z0 (leafHashes hl (hThree a b).tree) (leafHashes hl (hThree a b).tree)
      ∧ ∀ i, ¬ TreeCollision h z0 (leafHashes hl (hThree a b).tree)
          (leafHashes hl (hThree a b).tree) (hThree a b).height i

/-- **THE PUBLISHED ROOT DOES NOT COMMIT THE LEAF COUNT, FOR EVERY HASH.**  On the reached state
`hThree a b` (three leaves at height 2, one padded slot), the leaf-hash list with the padding
constant appended is within capacity, has the published root, and is not the leaf-hash list.
`PublishedRootCommitsAnyLengthOrBreak` locates this as its second case: a `PaddingHit` (the
longer list holds `z0` at index `leafCount`), and no collision is located on any index's path,
so no strength of hash prevents it.  The equal-length premise of
`PublishedRootCommitsOrCollision` is what excludes it. -/
def Properties.PublishedRootPaddingHitFires : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    HReaches hSetup (hThree a b)
      ∧ (leafHashes hl (hThree a b).tree ++ [z0]).length ≤ 2 ^ (hThree a b).height
      ∧ rootOf h z0 (leafHashes hl (hThree a b).tree ++ [z0]) (hThree a b).height
          = (hThree a b).root h z0 hl
      ∧ leafHashes hl (hThree a b).tree ++ [z0] ≠ leafHashes hl (hThree a b).tree
      ∧ PaddingHit z0 (leafHashes hl (hThree a b).tree ++ [z0]) (leafHashes hl (hThree a b).tree)
      ∧ ∀ i, ¬ TreeCollision h z0 (leafHashes hl (hThree a b).tree ++ [z0])
          (leafHashes hl (hThree a b).tree) (hThree a b).height i

end Contracts.InteropCommitmentTree
