import EraSpec.Contracts.L2InteropCommitmentTree.Specs.Reaches

/-!
# Contract spec: the hint search

**Commit.** era-contracts `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5` (`b17415d20`), `common/libraries/IndexedMerkleTree.sol:90-93`:
the walk from the hint has no hop bound.  `WalkExitsAtV35` and `InsertChecksAtV35` below are that
walk and the checks before it, the canonical v35 definitions.  `lowSearch` and `InsertGuard` are
in `Specs/Model.lean`.

**What differs from the interop pin.**  At `c67894b9` the walk was a counted loop that reverted
after `MAX_LOW_INDEX_SEARCH_ATTEMPTS = 5` hops; `maxLowIndexSearchAttempts` is that bound and
`HonestInsertRevertsAtDeployedFuel` its revert, kept as the comparison the v35 topics use.  The
other results of this topic hold for every fuel and so at `b17415d20`.
-/

namespace Contracts.InteropCommitmentTree

/-- `MAX_LOW_INDEX_SEARCH_ATTEMPTS` in `contracts/common/Config.sol` at the pin.  The
contract's loop allows this many hops and reverts with `IMTLowLeafNextTooSmall` when
one more is needed, which is `lowSearch` with this fuel. -/
def maxLowIndexSearchAttempts : ℕ := 5

/-- The honest run `setup; insert 1; insert 2; …; insert n`, each insert given the
correct low leaf (the previous index).  Leaf `k` carries value `k`. -/
def chainTree : ℕ → Tree
  | 0 => setup
  | n + 1 => insert (chainTree n) ((n + 1 : ℕ) : UInt256) n

/-! ## The v35 walk and insert checks

At `b17415d20` the walk has no hop bound (`IndexedMerkleTree.sol:90-93`):

    while (lowLeaf.nextValue != 0 && lowLeaf.nextValue < _value) {
        lowLeafIndex = lowLeaf.nextIndex;
        lowLeaf = self.leaves[lowLeafIndex];
    }

`lowSearch T v hops hint` runs the same exit test and hop with at most `hops` hops and returns
`none` only if it needs more, so "the loop exits at `low`" is "some number of hops of
`lowSearch` returns `low`".  A loop that never exits runs out of gas and reverts, which is no
step.  These are the walk and the checks of the canonical v35 machine
(`CommitmentTreeAtV35.CTxStepAtV35`) and of its list-state projections (`HintSearchAtHead`,
`UnboundedSearchAtV35`). -/

/-- **THE v35 LOOP EXITS AT `low`** (`IndexedMerkleTree.sol:90-93` at `b17415d20`): some number
of hops of the walk from `hint` ends on `low`. -/
def WalkExitsAtV35 (T : Tree) (v : UInt256) (hint low : ℕ) : Prop :=
  ∃ hops : ℕ, lowSearch T v hops hint = some low

/-- What a successful v35 `insert(v, hint)` has checked before it writes, at the index `low` the
walk exits on (`IndexedMerkleTree.sol:65-93` at `b17415d20`).  `FullMerkle.updateLeaf`'s range
check on `low` (`FullMerkle.sol:74-77`, reached from `IndexedMerkleTree.sol:101`) is not a field:
`CachedRoot.cInsert` returns `none` on it, and `UnboundedSearchAtV35.InsertCallV35` states it. -/
structure InsertChecksAtV35 (T : Tree) (v : UInt256) (hint low : ℕ) : Prop where
  /-- `leafNumber == 0` reverts with `IMTNotInitialized` (`:70-73`). -/
  initialized : Initialized T
  /-- `_value == 0` reverts with `IMTValueZero` (`:74-76`). -/
  nonzero : v ≠ 0
  /-- `valueToIndex[_value] != 0` reverts with `IMTValueAlreadyExists` (`:77-79`). -/
  unregistered : T.valueToIndex v = 0
  /-- `_lowLeafIndex >= leafNumber` reverts with `IMTLowLeafIndexOutOfBounds` (`:80-82`). -/
  hintInBounds : hint < T.leafCount
  /-- `leaves[_lowLeafIndex].value >= _value` reverts with `IMTLowLeafValueTooLarge` (`:84-88`). -/
  hintBelow : (T.leaf hint).value < v
  /-- The unbounded walk (`:90-93`) exits at `low`. -/
  walk : WalkExitsAtV35 T v hint low

end Contracts.InteropCommitmentTree
