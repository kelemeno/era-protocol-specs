import EraSpec.Contracts.FullMerkle.Specs.CachedNodes
import EraSpec.Contracts.Merkle.Specs.Verifier

/-!
# Properties: the cached-node algorithm computes the fold

Statements about `EraSpec.Contracts.FullMerkle.Specs.CachedNodes`, the line-by-line
transcription of `FullMerkle.sol`'s storage and functions.  Proofs are in
`EraSpec.Contracts.FullMerkle.Proofs.CachedNodes`.

The invariant is `Represents h z0 leaves S`: `_leafNumber` counts the leaves, the leaves
fit `2 ^ _height`, `_zeros[i] = zeros h z0 i`, and `_nodes[i]` is the abstract level
`levels h z0 leaves i`, for every `i ≤ _height`.  There are four groups:

* **The calls keep the invariant.**  `setup` on fresh storage establishes it for the
  empty tree.  `pushNewLeaf(x)` keeps it with `x` appended, never reverts, returns the
  fold over the new leaves at the new `_height`, and moves `(_leafNumber, _height)` by
  `CapacityInvariant.push`.  `updateLeaf(i, x)` with `i` occupied keeps it with leaf `i`
  replaced, never reverts, and returns the new fold.  `updateLeaf` at an index that is
  not occupied reverts, whatever the storage.
* **Reading the storage.**  `root()` is `rootOf h z0 leaves _height`, and
  `merklePath(i)` for an occupied `i` is `honestSibs h z0 leaves i` at the levels below
  `_height`: the sibling stream `InclusionComplete` and `HonestProofNoBreak` are stated
  for.  `Merkle.calculateRoot(merklePath(i), i, leaf_i)` is `root()`.
* **Along runs.**  Every storage reachable from fresh storage by `setup(z0)` and
  successful calls represents the leaves it holds, its `_height` is the one
  `CapacityInvariant.push` reaches at its leaf count, and every successful call returns
  the stored root.
* **Anti-vacuity.**  Three pushes from fresh storage satisfy every premise above, with
  the height growing twice.

No hash premise is used anywhere: every statement holds for every node hash `h` and
padding `z0`.
-/

namespace Contracts.FullMerkle

open MerkleSpec MerkleSpec.Verifier AttackVectors.CapacityInvariant

/-! ## The calls keep the invariant -/

/-- **`setup` ESTABLISHES THE INVARIANT.**  On fresh storage, `setup(z0)` caches the empty
tree at height 0 and returns its root `z0`. -/
def Properties.SetupRepresentsEmpty : Prop :=
  ∀ (h : Hash) (z0 : UInt256),
    Represents h z0 [] (setup FullTree.empty z0).1
      ∧ (setup FullTree.empty z0).2 = rootOf h z0 [] 0

/-- **`pushNewLeaf` COMPUTES THE FOLD.**  From storage caching the tree over `leaves`,
`pushNewLeaf(x)` does not revert.  It returns the fold over `leaves ++ [x]` at its new
`_height`, leaves storage caching that tree, and moves `(_leafNumber, _height)` exactly
as `CapacityInvariant.push` does.  So the growth branch (FullMerkle.sol:45-52), the
padding loop (:53-64) and the frontier zero (:84) have no off-by-one. -/
def Properties.PushNewLeafComputesRoot : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (leaves : List UInt256) (S : FullTree) (x : UInt256),
    Represents h z0 leaves S →
    ∃ S' : FullTree, pushNewLeaf h S x = some (S', rootOf h z0 (leaves ++ [x]) S'.height)
      ∧ Represents h z0 (leaves ++ [x]) S'
      ∧ (⟨S'.leafNumber, S'.height⟩ : TreeDims) = push ⟨S.leafNumber, S.height⟩

/-- **`updateLeaf` COMPUTES THE FOLD.**  From storage caching the tree over `leaves`,
`updateLeaf(idx, x)` at an occupied index does not revert.  It returns the fold over
`leaves.set idx x` at the unchanged `_height` and leaves storage caching that tree.
`_height` and `_leafNumber` are unchanged. -/
def Properties.UpdateLeafComputesRoot : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (leaves : List UInt256) (S : FullTree) (idx : ℕ) (x : UInt256),
    Represents h z0 leaves S → idx < leaves.length →
    ∃ S' : FullTree, updateLeaf h S idx x = some (S', rootOf h z0 (leaves.set idx x) S.height)
      ∧ Represents h z0 (leaves.set idx x) S'
      ∧ S'.height = S.height ∧ S'.leafNumber = S.leafNumber

/-- **`updateLeaf` OUTSIDE THE OCCUPIED RANGE HAS NO STEP.**  For any storage, an index
`≥ _leafNumber` reverts: `MerkleWrongIndex` (FullMerkle.sol:75-77), or the underflow of
`_leafNumber - 1` (:74) on an empty tree. -/
def Properties.UpdateLeafOutOfRangeReverts : Prop :=
  ∀ (h : Hash) (S : FullTree) (idx : ℕ) (x : UInt256),
    S.leafNumber ≤ idx → updateLeaf h S idx x = none

/-! ## Reading the storage -/

/-- **`root()` IS THE FOLD.**  On storage caching the tree over `leaves`,
`_nodes[_height][0]` is `rootOf h z0 leaves _height` (the empty tree included). -/
def Properties.RootIsFold : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (leaves : List UInt256) (S : FullTree),
    Represents h z0 leaves S → root S = some (rootOf h z0 leaves S.height)

/-- **`merklePath(i)` IS THE HONEST SIBLING LIST.**  On storage caching the tree over
`leaves`, for an occupied `i`, `merklePath(i)` does not revert and returns
`honestSibs h z0 leaves i l` for `l = 0, …, _height - 1`: the stream that
`MerkleSpec.Verifier.honest_walk_root`, `InclusionComplete` and `HonestProofNoBreak`
are about. -/
def Properties.MerklePathIsHonest : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (leaves : List UInt256) (S : FullTree) (i : ℕ),
    Represents h z0 leaves S → i < leaves.length →
    merklePath S i = some ((List.range S.height).map (honestSibs h z0 leaves i))

/-- **`merklePath` OUTSIDE THE OCCUPIED RANGE REVERTS.**  For any storage, an index
`≥ _leafNumber` reverts (`MerkleNothingToProve` on an empty tree, `MerkleWrongIndex`
otherwise).  The library never hands out a proof for a padded slot. -/
def Properties.MerklePathOutOfRangeReverts : Prop :=
  ∀ (S : FullTree) (i : ℕ), S.leafNumber ≤ i → merklePath S i = none

/-- **THE CONTRACT'S OWN PATH VERIFIES AGAINST ITS OWN ROOT.**  On storage caching the
tree over `leaves`, for an occupied `i`: `merklePath(i)` returns a path `p` of length
`_height` with `i < 2 ^ p.length` (the `MerkleIndexOutOfBounds` check of
`calculateRoot`), and walking it from leaf `i` (`Merkle.calculateRoot(p, i, leaf_i)`)
gives `root()`. -/
def Properties.ContractPathVerifies : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (leaves : List UInt256) (S : FullTree) (i : ℕ),
    Represents h z0 leaves S → i < leaves.length →
    ∃ (p : List UInt256) (R : UInt256), merklePath S i = some p ∧ root S = some R
      ∧ p.length = S.height ∧ i < 2 ^ p.length
      ∧ walkPure h (pathSibs p) 0 p.length i (leaves.getD i z0) = R

/-- **THE STORAGE DETERMINES THE LEAVES.**  Storage caching the tree over `leaves` holds
exactly `leaves` as the first `_leafNumber` entries of `_nodes[0]`. -/
def Properties.RepresentsLeaves : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (leaves : List UInt256) (S : FullTree),
    Represents h z0 leaves S → leavesOf S = leaves

/-- **THE INVARIANT, ENTRY BY ENTRY.**  For a nonempty tree, every `_zeros[i]` and every
`_nodes[i][j]` with `i ≤ _height` reads as the fold says (an out-of-range `j` reverts
exactly where the abstract level ends). -/
def Properties.CacheEntries : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (leaves : List UInt256) (S : FullTree),
    Represents h z0 leaves S → leaves ≠ [] →
    (∀ i, i ≤ S.height → S.zeros[i]? = some (zeros h z0 i))
      ∧ (∀ i j, i ≤ S.height → nodeAt S.nodes i j = (levels h z0 leaves i)[j]?)

/-! ## Along runs -/

/-- **EVERY REACHABLE STORAGE CACHES ITS LEAVES.**  Storage reached from fresh storage by
`setup(z0)` and successful `pushNewLeaf`/`updateLeaf` calls represents the leaves it
holds, and its `_height` is the height `CapacityInvariant.push` reaches after
`_leafNumber` pushes. -/
def Properties.ReachableRepresents : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (S : FullTree), Reachable h z0 S →
    Represents h z0 (leavesOf S) S ∧ S.height = (push^[S.leafNumber] ⟨0, 0⟩).height

/-- **ON EVERY REACHABLE STORAGE, `root()` IS THE FOLD OF ITS LEAVES.** -/
def Properties.ReachableRootIsFold : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (S : FullTree), Reachable h z0 S →
    root S = some (rootOf h z0 (leavesOf S) S.height)

/-- **EVERY SUCCESSFUL CALL RETURNS THE STORED ROOT.**  From reachable storage, the value
a successful `pushNewLeaf` or `updateLeaf` returns is what `root()` reads afterwards. -/
def Properties.CallsReturnTheStoredRoot : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (S S' : FullTree) (r : UInt256), Reachable h z0 S →
    ((∃ x, pushNewLeaf h S x = some (S', r)) ∨ (∃ i x, updateLeaf h S i x = some (S', r))) →
    root S' = some r

/-! ## Anti-vacuity -/

/-- **THE PREMISES ARE SATISFIABLE, WITH THE HEIGHT GROWING.**  For every node hash and
padding, three pushes from fresh storage succeed and reach storage that represents
`[a, b, c]` at height 2 (both later pushes take the growth branch).  Indices 0, 1 and 2
are occupied, so this meets the premises of `UpdateLeafComputesRoot`,
`MerklePathIsHonest`, `ContractPathVerifies` and `CacheEntries`; a further
`updateLeaf(0, c)` from it succeeds, which meets the premise of
`CallsReturnTheStoredRoot`. -/
def Properties.ThreePushesWitness : Prop :=
  ∀ (h : Hash) (z0 a b c : UInt256), ∃ S : FullTree,
    threePushes h z0 a b c = some S ∧ Reachable h z0 S ∧ Represents h z0 [a, b, c] S
      ∧ S.height = 2 ∧ S.leafNumber = 3
      ∧ ∃ (S' : FullTree) (r : UInt256), updateLeaf h S 0 c = some (S', r)

end Contracts.FullMerkle
