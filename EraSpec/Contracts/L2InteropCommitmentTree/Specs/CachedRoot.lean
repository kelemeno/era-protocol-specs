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

## What the source does (era-contracts `b17415d20`)

**Commit.** era-contracts `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`
(`b17415d20`), `l1-contracts/contracts/common/libraries/IndexedMerkleTree.sol`:

    function setup(IMT storage self) internal {                                  // :46-54
        if (self.tree._leafNumber != 0) { revert IMTAlreadyInitialized(); }
        self.tree.setup(IMT_EMPTY_LEAF_HASH);
        self.tree.pushNewLeaf(hashLeaf(IMTLeaf({value: 0, nextIndex: 0, nextValue: 0})));
        self.leaves[0] = IMTLeaf({value: 0, nextIndex: 0, nextValue: 0});
    }
    function insert(IMT storage self, uint256 _value, uint256 _lowLeafIndex) ... { // :65-107
        ... checks (:70-88) and the unbounded walk (:90-93) ...
        self.tree.updateLeaf(lowLeafIndex, hashLeaf(updatedLowLeaf));           // :101
        ...
        newRoot = self.tree.pushNewLeaf(hashLeaf(newLeaf));                      // :106
    }
    function root(IMT storage self) ... { return self.tree.root(); }             // :110-112
    function merklePath(IMT storage self, uint256 _leafIndex) ... {              // :116-118
        path = self.tree.merklePath(_leafIndex);
    }

`cSetupPad h hl ze` is `setup` with the padding constant `ze` (`IMT_EMPTY_LEAF_HASH` at
`b17415d20`), and `CReachesPad` the states reached from it; `cInsert`, `root` and `merklePath`
are the same calls at every revision.

**What differs from the interop pin.**  At `c67894b9` `setup` passed `hashLeaf({0,0,0})` to both
`FullMerkle.setup` and `pushNewLeaf`.  `cSetup`, `CReaches` and `CRun` are that instance
(`ze = zeroLeafHash hl`, `Properties.PinSetupIsPadAtZeroLeafHash`); the results stated over them
hold for the pin's constant, and their every-padding forms are `CSetupPadCaches`,
`CReachesPadRootIsPublished` and `CRunPadReaches` (`PaddingAtHead`) and the canonical machine's
`CTxRunAtV35StoredRootIsPublished`.  The padding-forgery record is
`History/Specs/PaddingForgeryPinned.lean`.

## Model boundary

* `cSetup` passes `hashLeaf({0,0,0})` to `FullMerkle.setup`, so its padding constant is
  `hl ⟨0, 0, 0⟩` (`zeroLeafHash`), the pin's choice; `cSetupPad` takes it as a parameter.
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

/-! ## `setup` with the padding constant as a parameter

`cSetup` passes the pin's `hashLeaf({0,0,0})` to `FullMerkle.setup`.  At `b17415d20`,
`IndexedMerkleTree.setup` passes `IMT_EMPTY_LEAF_HASH` there (`IndexedMerkleTree.sol:51`) and
`hashLeaf({0,0,0})` to `pushNewLeaf` (`:52`).  `cSetupPad h hl ze` is that call with the padding
constant `ze` as a parameter; `insert` makes the same `FullMerkle` calls at both revisions, so
its step is `cInsert`.  These are the v35 setup and reached states that `PaddingAtHead`,
`ReclaimGateFaithful` and `CommitmentTreeAtV35` share. -/

/-- `IndexedMerkleTree.setup` on fresh storage, padding with `ze`
(`IndexedMerkleTree.sol:46-54` at `b17415d20`): `tree.setup(ze)`, then
`tree.pushNewLeaf(hashLeaf({0,0,0}))`, with the sentinel list state.  At `b17415d20`, `ze` is
`IMT_EMPTY_LEAF_HASH`.  With `ze = hashLeaf({0,0,0})` this is the pin's `cSetup`
(`Properties.PinSetupIsPadAtZeroLeafHash`). -/
def cSetupPad (h : MerkleSpec.Hash) (hl : LeafHash) (ze : UInt256) : Option CState :=
  (FullMerkle.pushNewLeaf h (FullMerkle.setup FullMerkle.FullTree.empty ze).1 (hl ⟨0, 0, 0⟩)).map
    fun r => ⟨setup, r.1⟩

/-- States reached from `cSetupPad h hl ze` by guarded inserts that do not revert: `CReaches`
with the padding constant as a parameter; the insert step is the same `cInsert`. -/
inductive CReachesPad (h : MerkleSpec.Hash) (hl : LeafHash) (ze : UInt256) : CState → Prop
  | init {S : CState} : cSetupPad h hl ze = some S → CReachesPad h hl ze S
  | insert {S S' : CState} {v : UInt256} {low : ℕ} {r : UInt256} :
      CReachesPad h hl ze S → InsertGuard S.tree v low → cInsert h hl S v low = some (S', r) →
      CReachesPad h hl ze S'

end Contracts.InteropCommitmentTree
