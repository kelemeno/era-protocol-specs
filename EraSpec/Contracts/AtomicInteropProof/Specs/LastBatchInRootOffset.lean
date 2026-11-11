import EraSpec.Contracts.AtomicInteropProof.Specs.LastBatchInRoot

/-!
# Last batch in root, with batch numbers and leaf positions kept apart

`AttackVectors.LastBatchInRoot.end_branch_from_onchain_check` uses one `B` twice: as
the chain-tree leaf POSITION (the mask, in `RightEmpty B nBatches hDepth`) and as the
BATCH NUMBER (in `H.endSet B` and `H.time`).  Its `hout : OutsideRootLate (· < nBatches)
time T` reads the root as holding batches `0 .. nBatches - 1`.  The source keeps the two
apart:

* `MessageRootBase._addNewChain` (`core/message-root/MessageRootBase.sol:339-357`, pinned
  `c67894b9`) sets `currentChainBatchNumber[_chainId] = _startingBatchNumber` and starts
  an EMPTY chain tree ("Chains registered with a non-zero `_startingBatchNumber` ... never
  report a genesis root");
* `_recordChainBatchRoot` (`:236-239`) requires consecutive batch numbers;
  `addChainBatchRoot` (v31, `:199-205`) only records, never pushes; only
  `_pushChainBatchRoot` (`:245-258`) appends `batchLeafHash(_chainBatchRoot,
  _batchNumber, l1Timestamp)` to the chain tree;
* `seedGenesisRoot` pushes batch 0 only for ZKsync OS chains and returns early for
  EraVM chains;
* `MessageHashing.sol:189-208`: the batch number is INSIDE the leaf hash; the leaf's
  position is the prover's mask.

So leaf position `k` of chain `c`'s tree is batch `s + 1 + k`, where `s` is the last
batch number before the tree's first pushed leaf (the starting batch number, the last
record-only batch, or `s + 1 = 0` for a genesis-seeded ZKsync OS chain).  For a fresh
EraVM chain leaf `k` is batch `k + 1`.

`batchAt s p` is that map.  The re-indexed end-branch composition states
`RightEmpty` on the position, `OutsideRootLate` only for batch numbers AFTER the root's
last batch `s + n` (batches at or below `s` are outside the root yet settled earlier, so
the unrestricted form is false), and absence at the batch number `B = batchAt s p`.

**This file is definitions only.**  Results: `../Properties/LastBatchInRootOffset.lean`.
-/

namespace AttackVectors.LastBatchInRootOffset

open AttackVectors.TimeoutSoundness

/-- The batch number of chain-tree leaf position `p`, for a tree whose first leaf is
batch `s + 1`. -/
def batchAt (s p : ℕ) : ℕ := s + 1 + p

/-- A fresh EraVM chain (`s = 0`) whose first pushed batch, batch 1, commits value `1`.
Batches 0 and 1 settle at time 0, later ones at time 1. -/
def offsetHistory : BatchHistory where
  endSet := fun n => if 1 ≤ n then {1} else ∅
  time := fun n => if n ≤ 1 then 0 else 1

/-- The same clock with nothing committed: the honest-refund instance. -/
def emptyOffsetHistory : BatchHistory where
  endSet := fun _ => ∅
  time := fun n => if n ≤ 2 then 0 else 1

end AttackVectors.LastBatchInRootOffset
