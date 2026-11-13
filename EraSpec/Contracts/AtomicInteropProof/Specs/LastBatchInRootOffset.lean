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

So leaf position `k` of chain `c`'s tree is batch `f + k`, where `f` is the batch number
of the tree's first pushed leaf: `f = 0` for a genesis-seeded ZKsync OS chain
(`seedGenesisRoot` pushes batch 0), and `f = s + 1` otherwise, with `s` the starting
batch number or the last record-only batch.  For a fresh EraVM chain `f = 1` and leaf `k`
is batch `k + 1`.  With `f = 0`, `batchAt 0 p = p` and the re-indexed composition is the
original position-as-batch statement (with `OutsideRootLate` restricted to batches after
the root's last one).

**Assumption (`PROTO-CONTIGUOUS-PUSH`, ASSUMPTIONS.md).**  "Leaf `k` is batch `f + k`"
holds only if, after the first push, every batch of the chain is pushed: the chain only
calls `addChainBatchRootV32`, never falls back to the record-only `addChainBatchRoot`,
and `setMigratingChainBatchNumber` (`:177-182`) does not advance the counter past
unpushed batches.  `MessageRootBase` enforces none of this (both entry points pass
`addChainBatchRootRestriction`); `_recordChainBatchRoot` only makes the batch NUMBERS
consecutive.  The statements below take `B = batchAt f p` as a premise, so they hold
whenever that identification does; `BatchNumberBoundOrCollision` adds nothing to it.

`batchAt f p` is that map.  The re-indexed end-branch composition states
`RightEmpty` on the position, `OutsideRootLate` only for batch numbers AFTER the root's
last batch `f + n - 1` (batches below `f` are outside the root yet settled earlier, so
the unrestricted form is false for every chain with `f > 0`), and absence at the batch
number `B = batchAt f p`.

**This file is definitions only.**  Results: `../Properties/LastBatchInRootOffset.lean`.
-/

namespace AttackVectors.LastBatchInRootOffset

open AttackVectors.TimeoutSoundness

/-- The batch number of chain-tree leaf position `p`, for a tree whose first leaf is
batch `f` (under `PROTO-CONTIGUOUS-PUSH`). -/
def batchAt (f p : ℕ) : ℕ := f + p

/-- A fresh EraVM chain (`f = 1`) whose first pushed batch, batch 1, commits value `1`.
Batches 0 and 1 settle at time 0, later ones at time 1. -/
def offsetHistory : BatchHistory where
  endSet := fun n => if 1 ≤ n then {1} else ∅
  time := fun n => if n ≤ 1 then 0 else 1

/-- The same clock with nothing committed: the honest-refund instance. -/
def emptyOffsetHistory : BatchHistory where
  endSet := fun _ => ∅
  time := fun n => if n ≤ 2 then 0 else 1

end AttackVectors.LastBatchInRootOffset
