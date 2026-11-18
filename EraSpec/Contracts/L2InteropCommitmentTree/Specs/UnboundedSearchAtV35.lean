import EraSpec.Contracts.L2InteropCommitmentTree.Specs.HintSearch
import EraSpec.Contracts.IndexedMerkleTree.Specs.UnboundedSearchAtV35

/-!
# Contract spec: the v35 `insert` on the indexed list state

Source: era-contracts `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`
(`b17415d20`; byte-identical to `d9f6789` for this file),
`l1-contracts/contracts/common/libraries/IndexedMerkleTree.sol:65-107`, as transcribed in
`../../IndexedMerkleTree/Specs/UnboundedSearchAtV35.lean`.  That topic states the v35 walk over
the abstract leaf set, with indices erased.  This one states the same call over this folder's
index-level list state `Tree` (`Specs/Model.lean`: `leaf`, `nextIndex`, `valueToIndex`) and
relates the two, so the abstract v35 results apply to the indexed model.

The loop (`:90-93`):

    while (lowLeaf.nextValue != 0 && lowLeaf.nextValue < _value) {
        lowLeafIndex = lowLeaf.nextIndex;
        lowLeaf = self.leaves[lowLeafIndex];
    }

`lowSearch T v f i` (`Specs/Model.lean`) runs exactly this test and this hop, from index `i`,
with at most `f` hops: it returns `some j` when the test fails at index `j` within `f` hops, and
`none` when a further hop would be needed.  With `f = MAX_LOW_INDEX_SEARCH_ATTEMPTS` it is the
pin's counted loop (`HintSearch`).

## What is modelled

* `SearchExitsV35 T v i j`: the unbounded loop started at index `i` exits at index `j`, that is,
  some fuel makes `lowSearch` return `some j`.  The fuel is a proof device; the source has no
  bound.  A loop run that never exits has no `j`.
* `InsertCallV35 T v hint T'`: a successful v35 `insert(v, hint)` leaving `T'`.  Its fields are
  the source's checks in order (`:71-88`), then the loop exit, `FullMerkle.updateLeaf`'s range
  check on the exit index (`FullMerkle.sol:74-77`, byte-identical at the pin), and the writes
  `insert T v j` (`:95-106`, the same writes as at the pin).
* `RunCallV35 R`: a history of the indexed state whose steps are no-ops or successful v35 calls.
* `chainTreeRunV35`: the indexed counterpart of `chainRunV35`, from `setup`.

## Model boundary

As in `Specs/Model.lean`: list state only (no `FullMerkle` storage, root or `_reportLeaf`), no
callers (`InitOnce` has them), indices are `ℕ`, and gas is not modelled.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-- **The v35 loop exits at index `j`** (`IndexedMerkleTree.sol:90-93` at `b17415d20`): started at
index `i`, the unbounded `while` loop ends with `lowLeafIndex = j`.  Some fuel makes the fuelled
loop `lowSearch` return `j`; any larger fuel returns the same index
(`Properties.SearchExitsDeterministicV35`). -/
def SearchExitsV35 (T : Tree) (v : UInt256) (i j : ℕ) : Prop :=
  ∃ fuel : ℕ, lowSearch T v fuel i = some j

/-- **A successful v35 `insert(v, hint)`** (`IndexedMerkleTree.sol:65-107` at `b17415d20`) on the
indexed list state `T`, leaving `T'`.  The fields are the source's checks, in source order, and
then the loop and the writes:

* `initialized`: `IMTNotInitialized` (:71-73).
* `nonzero`: `IMTValueZero` (:74-76).
* `fresh`: `IMTValueAlreadyExists` (:77-79), on `valueToIndex`.
* `inBounds`: `IMTLowLeafIndexOutOfBounds` (:80-82).
* `hintBelow`: `IMTLowLeafValueTooLarge` (:86-88).
* `exits`: the loop (:90-93) exits at some index `j`; `j` passes `FullMerkle.updateLeaf`'s own
  range check (`FullMerkle.sol:74-77`, reached from :101; on a `Valid` tree it always does); and
  `T'` is `insert T v j`: the low leaf at `j` retargeted, the new leaf appended at `leafCount`,
  `valueToIndex[v]` set (:95-106). -/
structure InsertCallV35 (T : Tree) (v : UInt256) (hint : ℕ) (T' : Tree) : Prop where
  initialized : Initialized T
  nonzero : v ≠ 0
  fresh : T.valueToIndex v = 0
  inBounds : hint < T.leafCount
  hintBelow : (T.leaf hint).value < v
  exits : ∃ j, SearchExitsV35 T v hint j ∧ j < T.leafCount ∧ T' = insert T v j

/-- **A v35 history of the indexed state.**  Each step leaves the state unchanged (a call that
does not write the tree, or one that reverts), or is a successful v35 `insert` call. -/
def RunCallV35 (R : ℕ → Tree) : Prop :=
  ∀ n, R (n + 1) = R n ∨ ∃ (v : UInt256) (hint : ℕ), InsertCallV35 (R n) v hint (R (n + 1))

/-- The indexed counterpart of `chainRunV35`: snapshot `n` is the pin's honest run
`chainTree (min n 7)` (`Specs/HintSearch.lean`), whose leaf `k` carries value `k`.
`Properties.ChainTreeRunCallsV35` shows each of its seven inserts can be made from the stale
hint `0`. -/
def chainTreeRunV35 (n : ℕ) : Tree := chainTree (min n 7)

end Contracts.InteropCommitmentTree
