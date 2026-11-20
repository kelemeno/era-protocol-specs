import EraSpec.Contracts.AtomicInteropProof.Specs.LastBatchInRoot

/-!
# Last batch in root, with batch numbers and leaf positions kept apart

`AttackVectors.LastBatchInRoot.end_branch_from_onchain_check` uses one `B` twice: as
the chain-tree leaf POSITION (the mask, in `RightEmpty B nBatches hDepth`) and as the
BATCH NUMBER (in `H.endSet B` and `H.time`).  Its `hout : OutsideRootLate (· < nBatches)
time T` reads the root as holding batches `0 .. nBatches - 1`.  The source keeps the two
apart (era-contracts `b17415d20`, `l1-contracts/contracts/core/message-root/MessageRootBase.sol`):

* `_addNewChain` (`:275-293`) sets `currentChainBatchNumber[_chainId] = _startingBatchNumber`
  (`:282`) and starts an EMPTY chain tree (`:285`);
* `_recordChainBatchRoot` (`:183-197`) requires consecutive batch numbers (`:192-193`);
  `addChainBatchRoot` (`:164-170`) only records, never pushes; only `_pushChainBatchRoot`
  (`:201-214`) appends `batchLeafHash(_chainBatchRoot, _batchNumber, l1Timestamp)` to the chain
  tree (`:206-209`);
* `seedGenesisRoot` (`:296-314`) pushes batch 0, for a chain whose counter is still 0 and whose
  diamond stores a nonzero genesis root (`:302-313`);
* `common/libraries/MessageHashing.sol:76-82`: the batch number is INSIDE the leaf hash;
  `:198-205`: the leaf's position is the prover's mask.

So leaf position `k` of chain `c`'s tree is batch `f + k`, where `f` is the batch number
of the tree's first pushed leaf: `f = 0` for a genesis-seeded chain (`seedGenesisRoot` pushes
batch 0), and `f = s + 1` otherwise, with `s` the starting batch number or the last record-only
batch.  With `f = 0`, `batchAt 0 p = p` and the re-indexed composition is the original
position-as-batch statement.

**Which `f` occurs at `b17415d20`.**  Every flow settles on L1 (`atomic-interop/AtomicFlowManager.sol:329-333`,
checked in `append`, `requireFlowFinalized` and `authorizeRefund`), so the end branch reads L1's
chain tree.  `L1Bridgehub.createNewChain` calls `addNewChain(_chainId, 0)` and then
`seedGenesisRoot` (`core/bridgehub/L1Bridgehub.sol:134-135`) for every chain it creates, so such
a chain has `f = 0`.  A chain registered by `registerAlreadyDeployedZKChain` gets
`addNewChain(_chainId, getTotalBatchesExecuted())` (`:300`, `:316`) and no genesis leaf, so its
first pushed batch is later: there `f > 0`, and the offset form is the one that applies.  (At the
extraction pin `c67894b9` every atomic-interop source chain was a genesis-created ZKsync OS chain,
with `f = 0` on L1, as earlier rounds recorded.)

**Assumption (`PROTO-CONTIGUOUS-PUSH`, ASSUMPTIONS.md).**  "Leaf `k` is batch `f + k`"
holds only if, after the first push, every batch of the chain is pushed into this tree.
`MessageRootBase` does not enforce it; `_recordChainBatchRoot` only makes the batch
NUMBERS consecutive.  `setMigratingChainBatchNumber` (`:153-157`) can advance the counter
past batches never pushed here, and on L1 it runs when a chain returns from Gateway
(`core/chain-asset-handler/ChainAssetHandlerBase.sol:414`).  The record-only
`addChainBatchRoot` passes the same `addChainBatchRootRestriction` (`:131-136`) as
`addChainBatchRootV32`, but no executor calls it
(`state-transition/chain-deps/facets/Executor.sol:165` calls only `addChainBatchRootV32`).
The statements below take `B = batchAt f p` as a premise, so they hold whenever that
identification does; `BatchNumberBoundOrCollision` adds nothing to it.

`batchAt f p` is that map.  The re-indexed end-branch composition states
`RightEmpty` on the position, `OutsideRootLate` only for batch numbers AFTER the root's
last batch `f + n - 1`, and absence at the batch number `B = batchAt f p`.  When
`f > 0`, the batches below `f` are outside the root but may have settled before it, so
the unrestricted form can fail (`PositionAsBatchMisreads`).

**This file is definitions only.**  Results: `../Properties/LastBatchInRootOffset.lean`.
-/

namespace AttackVectors.LastBatchInRootOffset

open AttackVectors.TimeoutSoundness

/-- The batch number of chain-tree leaf position `p`, for a tree whose first leaf is
batch `f` (under `PROTO-CONTIGUOUS-PUSH`). -/
def batchAt (f p : ℕ) : ℕ := f + p

/-- An abstract chain whose first pushed batch is batch 1 (`f = 1`), and which commits
value `1` in that batch.  The instance shows what the two readings say when `f > 0` (at
`b17415d20`, for example, a chain registered by `registerAlreadyDeployedZKChain`).  Batches 0 and 1 settle at time 0, later ones at time 1. -/
def offsetHistory : BatchHistory where
  endSet := fun n => if 1 ≤ n then {1} else ∅
  time := fun n => if n ≤ 1 then 0 else 1

/-- The history `EndBranchOffsetSatisfiable` reads with first pushed batch `f = 1`, again
an abstract instance: value `7` is committed in batch 1, on time, and value `1` only in
batch 4, late.  Batches 0 to 3 settle at time 0, later ones at time 1. -/
def richOffsetHistory : BatchHistory where
  endSet := fun n => if n = 0 then ∅ else if n ≤ 3 then {7} else {7, 1}
  time := fun n => if n ≤ 3 then 0 else 1

end AttackVectors.LastBatchInRootOffset
