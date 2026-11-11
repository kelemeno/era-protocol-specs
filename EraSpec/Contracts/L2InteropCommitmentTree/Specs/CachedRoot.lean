import EraSpec.Contracts.L2InteropCommitmentTree.Specs.RunHeight
import EraSpec.Contracts.FullMerkle.Specs.CachedNodes

/-!
# Model: the commitment tree with `FullMerkle`'s whole storage

`RunHeight` carries `FullMerkle`'s two counters `(_leafNumber, _height)` next to the list
state, and publishes `HState.root`, the fold over the leaf hashes at `_height`.  It
records that the stored `_nodes[_height][0]` equals that fold as an assumption
(obligation O7 in `EraSpec.Refinement`).  This file carries the whole
`FullMerkle.FullTree` instead, `_nodes` and `_zeros` included.  The tree is moved by the
transcribed `FullMerkle.setup`, `updateLeaf` and `pushNewLeaf`
(`FullMerkle/Specs/CachedNodes.lean`), at exactly the points where `IndexedMerkleTree`
calls them, so `root()` and `merklePath(i)` read the storage those calls wrote.

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.L2InteropCommitmentTree.Properties.CachedRoot`, proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.CachedRoot`.  Names mirror
`RunHeight`'s: `CState`, `cSetup`, `cInsert`, `CReaches`, `CRun` (`C` for the cached
storage) beside `HState`, `hSetup`, `hInsert`, `HReaches`, `HRun`, and `CState.toH`
forgets `_nodes` and `_zeros`.

## What the source does (era-contracts `c67894b9`)

`IndexedMerkleTree.sol`:

    function setup(IMT storage self) internal {                                  // :42-51
        if (self.tree._leafNumber != 0) revert IMTAlreadyInitialized();
        bytes32 zeroLeafHash = hashLeaf(IMTLeaf({value: 0, nextIndex: 0, nextValue: 0}));
        self.tree.setup(zeroLeafHash);
        self.tree.pushNewLeaf(zeroLeafHash);
        self.leaves[0] = IMTLeaf({value: 0, nextIndex: 0, nextValue: 0});
    }
    function insert(IMT storage self, uint256 _value, uint256 _lowLeafIndex) ... { // :60-106
        ... guards and the bounded search ...
        self.tree.updateLeaf(lowLeafIndex, hashLeaf(updatedLowLeaf));           // :100
        ...
        newRoot = self.tree.pushNewLeaf(hashLeaf(newLeaf));                      // :105
    }
    function root(IMT storage self) ... { return self.tree.root(); }             // :109-111
    function merklePath(IMT storage self, uint256 _leafIndex) ... {              // :115-117
        path = self.tree.merklePath(_leafIndex);
    }

## Model boundary

* `FullMerkle.setup` is passed `hashLeaf({0,0,0})`, so the padding constant is
  `hl ⟨0, 0, 0⟩` (`zeroLeafHash`).  This is the pin's choice, and the one the padding
  countermodel `PaddingCollisionRefundsDeliveredLeg` uses.
* The list state, the guards (`InsertGuard`) and the search are as in `Specs/Model.lean`;
  `low` is the low leaf the search ends on.  `IMTAlreadyInitialized` is replaced by
  starting from fresh storage (`FullMerkle.FullTree.empty`).
* A revert inside a `FullMerkle` call is `none`.  The properties show that a guarded
  insert never hits one.
* Everything the `FullMerkle` transcription leaves out (`uint256` wrap at `2^255` leaves,
  compiled-code correspondence) is left out here too.
-/

namespace Contracts.InteropCommitmentTree

/-! ## The state -/

/-- The commitment tree's list state together with `FullMerkle`'s whole storage
`_imt.tree`. -/
structure CState where
  tree : Tree
  fm : FullMerkle.FullTree

/-- The padding constant the pinned `IndexedMerkleTree.setup` passes to
`FullMerkle.setup`: `hashLeaf({0, 0, 0})`. -/
def zeroLeafHash (hl : LeafHash) : UInt256 := hl ⟨0, 0, 0⟩

/-! ## The calls -/

/-- `IndexedMerkleTree.setup` on fresh storage: `tree.setup(zeroLeafHash)` then
`tree.pushNewLeaf(zeroLeafHash)`, with the sentinel list state. -/
def cSetup (h : MerkleSpec.Hash) (hl : LeafHash) : Option CState :=
  (FullMerkle.pushNewLeaf h (FullMerkle.setup FullMerkle.FullTree.empty (zeroLeafHash hl)).1
    (zeroLeafHash hl)).map fun r => ⟨setup, r.1⟩

/-- `IndexedMerkleTree.insert(v, low)` after its guard: `tree.updateLeaf(low, hashLeaf(updatedLowLeaf))`,
then `newRoot = tree.pushNewLeaf(hashLeaf(newLeaf))`, with the list update `insert`.
Returns the new state and `newRoot`. -/
def cInsert (h : MerkleSpec.Hash) (hl : LeafHash) (S : CState) (v : UInt256) (low : ℕ) :
    Option (CState × UInt256) := do
  let r₁ ← FullMerkle.updateLeaf h S.fm low
    (hl { S.tree.leaf low with nextIndex := S.tree.leafCount, nextValue := v })
  let r₂ ← FullMerkle.pushNewLeaf h r₁.1
    (hl ⟨v, (S.tree.leaf low).nextIndex, (S.tree.leaf low).nextValue⟩)
  pure (⟨insert S.tree v low, r₂.1⟩, r₂.2)

/-- `IndexedMerkleTree.root()`: what the storage holds at `_nodes[_height][0]`. -/
def CState.root (S : CState) : Option UInt256 := FullMerkle.root S.fm

/-- `IndexedMerkleTree.merklePath(i)`. -/
def CState.merklePath (S : CState) (i : ℕ) : Option (List UInt256) :=
  FullMerkle.merklePath S.fm i

/-- The `RunHeight` view of a state: the list state and `(_leafNumber, _height)`. -/
def CState.toH (S : CState) : HState := ⟨S.tree, ⟨S.fm.leafNumber, S.fm.height⟩⟩

/-! ## Reached states and runs -/

/-- States reached from `setup` by guarded inserts that do not revert. -/
inductive CReaches (h : MerkleSpec.Hash) (hl : LeafHash) : CState → Prop
  | init {S : CState} : cSetup h hl = some S → CReaches h hl S
  | insert {S S' : CState} {v : UInt256} {low : ℕ} {r : UInt256} :
      CReaches h hl S → InsertGuard S.tree v low → cInsert h hl S v low = some (S', r) →
      CReaches h hl S'

/-- A run with the whole storage: each step is idle or a guarded insert that does not
revert. -/
def CRun (h : MerkleSpec.Hash) (hl : LeafHash) (R : ℕ → CState) : Prop :=
  ∀ n, R (n + 1) = R n
    ∨ ∃ (v : UInt256) (low : ℕ) (r : UInt256),
        InsertGuard (R n).tree v low ∧ cInsert h hl (R n) v low = some (R (n + 1), r)

end Contracts.InteropCommitmentTree
