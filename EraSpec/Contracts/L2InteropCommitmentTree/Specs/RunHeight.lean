import EraSpec.Contracts.L2InteropCommitmentTree.Specs.TreeRoot
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.Reaches
import EraSpec.Contracts.FullMerkle.Specs.CapacityInvariant

/-!
# Model: `FullMerkle._height` carried along the commitment tree's runs

`TreeRoot` publishes `root h z0 hl T height` for an EXTERNAL `height`, and the
completeness results there take `T.leafCount ≤ 2 ^ height` as a premise.  In the
deployed contract the height is not external: it is `FullMerkle.FullTree._height`,
which `pushNewLeaf` grows as the tree fills.  This file carries that field next to
the list state, step for step as the source writes it, so the height at which a
run's root is published is the run's own.

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.L2InteropCommitmentTree.Properties.RunHeight`, proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.RunHeight`.

## What the source does (era-contracts `c67894b9`)

`FullMerkle.sol`:

    function setup(FullTree storage self, bytes32 zero) internal returns (bytes32 initialRoot) {
        self._zeros.push(zero);
        self._nodes.push([zero]);
        …
    function pushNewLeaf(FullTree storage self, bytes32 _leaf) internal returns (bytes32 newRoot) {
        uint256 index = self._leafNumber++;
        if (index == 1 << self._height) {
            uint256 newHeight = self._height.uncheckedInc();
            self._height = newHeight;
            …

`updateLeaf` writes neither `_height` nor `_leafNumber`.  `IndexedMerkleTree.setup`
calls `tree.setup(zeroLeafHash)` (both fields stay `0`) and then
`tree.pushNewLeaf(zeroLeafHash)`; `IndexedMerkleTree.insert` calls
`tree.updateLeaf(lowLeafIndex, …)` and then `tree.pushNewLeaf(hashLeaf(newLeaf))`.

So the pair `(_leafNumber, _height)` moves by exactly
`AttackVectors.CapacityInvariant.push` (`TreeDims` with `count = _leafNumber`): once
in `setup`, once per `insert`.

## Model boundary

* Only the two scalar fields are modelled.  `_nodes` and `_zeros` are not; the root
  is `TreeRoot.root` (the pure fold over `leafHashes`) evaluated at the modelled
  `_height`.  That the stored `_nodes[_height][0]` equals that fold is obligation O7
  in `EraSpec.Refinement`, not something proved here.
* Heights and counts are `ℕ`.  In the source `1 << self._height` is a `uint256`
  shift, which is `0` once `_height ≥ 256`; reaching that needs `2^255` leaves, so
  this file does not model it.
* That the compiled `pushNewLeaf` implements `push` is a statement about compiled
  code (as the header of `FullMerkle/Specs/CapacityInvariant.lean` records); it is
  assumed here, not proved.
-/

namespace Contracts.InteropCommitmentTree

open AttackVectors.CapacityInvariant

/-! ## The state: list state plus `FullMerkle` dimensions -/

/-- The commitment tree's list state together with its `FullMerkle` dimensions
`(_leafNumber, _height)` (as `TreeDims`, `count = _leafNumber`). -/
structure HState where
  tree : Tree
  dims : TreeDims

/-- `IndexedMerkleTree.setup`'s effect on `(_leafNumber, _height)`: `FullMerkle.setup`
leaves both `0`, then `pushNewLeaf(zeroLeafHash)` runs once. -/
def setupDims : TreeDims := push ⟨0, 0⟩

/-- `IndexedMerkleTree.setup`: the sentinel list state and its dimensions. -/
def hSetup : HState := ⟨setup, setupDims⟩

/-- `IndexedMerkleTree.insert(v, low)` after its guard: the list update `insert`, an
`updateLeaf` (no change to the dimensions), then one `pushNewLeaf` (`push`). -/
def hInsert (S : HState) (v : UInt256) (low : ℕ) : HState :=
  ⟨insert S.tree v low, push S.dims⟩

/-- The height at which the state's root is published: `_height`. -/
def HState.height (S : HState) : ℕ := S.dims.height

/-- The root `IndexedMerkleTree.root()` returns, modelled as the fold over the leaf
hashes at the state's own `_height` (see the model boundary on O7). -/
def HState.root (h : MerkleSpec.Hash) (z0 : UInt256) (hl : LeafHash) (S : HState) : UInt256 :=
  Contracts.InteropCommitmentTree.root h z0 hl S.tree S.height

/-! ## Runs and batch-sized steps -/

/-- A run of the contract with its `FullMerkle` dimensions: each step is idle or a
guarded `hInsert`.  The tree component is exactly a `Run` step. -/
def HRun (R : ℕ → HState) : Prop :=
  ∀ n, R (n + 1) = R n
    ∨ ∃ (v : UInt256) (low : ℕ), InsertGuard (R n).tree v low ∧ R (n + 1) = hInsert (R n) v low

/-- `U` is `S` after finitely many guarded inserts, dimensions included — the
`Reaches` of this state. -/
inductive HReaches : HState → HState → Prop
  | refl {S} : HReaches S S
  | tail {S U} (h : HReaches S U) {v : UInt256} {low : ℕ} (hg : InsertGuard U.tree v low) :
      HReaches S (hInsert U v low)

/-! ## The height as a function of the leaf count -/

/-- `_height` after `n` calls of `pushNewLeaf` on a freshly set-up `FullTree`. -/
def fmHeight (n : ℕ) : ℕ := (push^[n] ⟨0, 0⟩).height

/-! ## A concrete run, for the witnesses -/

/-- `hSetup; insert a at 0; insert b at 1` — the run whose list state is
`threeLeafTree a b`.  Its `_height` goes `0, 1, 2`. -/
def hThree (a b : UInt256) : HState := hInsert (hInsert hSetup a 0) b 1

/-- The run `hSetup, hInsert hSetup a 0, hThree a b, hThree a b, …`. -/
def hThreeRun (a b : UInt256) : ℕ → HState :=
  fun n => if n = 0 then hSetup else if n = 1 then hInsert hSetup a 0 else hThree a b

end Contracts.InteropCommitmentTree
