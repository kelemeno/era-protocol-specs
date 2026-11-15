import EraSpec.Contracts.AtomicInteropProof.Specs.LastBatchInRoot

/-!
# Last batch in root, with batch numbers and leaf positions kept apart

`AttackVectors.LastBatchInRoot.end_branch_from_onchain_check` uses one `B` twice: as
the chain-tree leaf POSITION (the mask, in `RightEmpty B nBatches hDepth`) and as the
BATCH NUMBER (in `H.endSet B` and `H.time`).  Its `hout : OutsideRootLate (· < nBatches)
time T` reads the root as holding batches `0 .. nBatches - 1`.  The source keeps the two
apart (`core/message-root/MessageRootBase.sol`, pinned `c67894b9`):

* `_addNewChain` (`:329-358`) sets `currentChainBatchNumber[_chainId] =
  _startingBatchNumber` and starts an EMPTY chain tree ("Chains registered with a non-zero
  `_startingBatchNumber` ... never report a genesis root", `:334-335`);
* `_recordChainBatchRoot` (`:228-243`) requires consecutive batch numbers (`:238-239`);
  `addChainBatchRoot` (v31, `:199-205`) only records, never pushes; only
  `_pushChainBatchRoot` (`:247-271`) appends `batchLeafHash(_chainBatchRoot,
  _batchNumber, l1Timestamp)` to the chain tree (`:257-259`);
* `seedGenesisRoot` (`:364-387`) pushes batch 0 only for ZKsync OS chains and returns
  early for EraVM chains;
* `MessageHashing.sol:189-208`: the batch number is INSIDE the leaf hash; the leaf's
  position is the prover's mask.

So leaf position `k` of chain `c`'s tree is batch `f + k`, where `f` is the batch number
of the tree's first pushed leaf: `f = 0` for a genesis-seeded ZKsync OS chain
(`seedGenesisRoot` pushes batch 0), and `f = s + 1` otherwise, with `s` the starting
batch number or the last record-only batch.  With `f = 0`, `batchAt 0 p = p` and the
re-indexed composition is the original position-as-batch statement.

**Which `f` the pin produces.**  At `c67894b9` every atomic-interop source chain is a
ZKsync OS chain that got the built-ins at its genesis upgrade, and its first pushed
batch on L1 is 0.  The commitment tree and `AtomicFlowManager` are initialised only under
`_isZKsyncOS && _isGenesisUpgrade` (`l2-upgrades/L2GenesisForceDeploymentsHelper.sol:448-461`;
`Contracts/L2InteropCommitmentTree/Specs/InitOnce.lean` records the same).  Such a chain
is created by `L1Bridgehub.createNewChain` (the chain type manager's `createNewChain` is
`onlyBridgehub`, `state-transition/ChainTypeManagerBase.sol:635-641`), which calls
`addNewChain(_chainId, 0)` and then `seedGenesisRoot` (`core/bridgehub/L1Bridgehub.sol:141-142`).
Every flow settles on L1 (`atomic-interop/AtomicFlowManager.sol:56`; `authorizeRefund`
checks it before `verifyTimeoutAbsence`, `:134-151`), so the end branch reads L1's chain
tree.  For these chains the original position-as-batch reading is exact while pushes are
contiguous.  (An EraVM chain has `f = 1` on L1, but it has no commitment tree.)  The
offset form is a generalisation that matters for a chain whose first pushed batch is
later, for example if the built-ins reach existing chains by upgrade (not verified here).
The gap the pin does have is contiguity.

**Assumption (`PROTO-CONTIGUOUS-PUSH`, ASSUMPTIONS.md).**  "Leaf `k` is batch `f + k`"
holds only if, after the first push, every batch of the chain is pushed into this tree.
`MessageRootBase` does not enforce it; `_recordChainBatchRoot` only makes the batch
NUMBERS consecutive.  `setMigratingChainBatchNumber` (`:177-183`) can advance the counter
past batches never pushed here, and on L1 it runs when a chain returns from Gateway
(`core/chain-asset-handler/ChainAssetHandlerBase.sol:386`): a Gateway round trip is the
realistic breaker at the pin.  The record-only `addChainBatchRoot` passes the same
`addChainBatchRootRestriction` (`:155-160`) as `addChainBatchRootV32`, but at the pin no
executor calls it (`state-transition/chain-deps/facets/Executor.sol:154` calls only
`addChainBatchRootV32`), so that route needs an executor facet downgrade.  The statements
below take `B = batchAt f p` as a premise, so they hold whenever that identification
does; `BatchNumberBoundOrCollision` adds nothing to it.

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
value `1` in that batch.  No atomic-interop source chain has `f = 1` at `c67894b9` (each
is genesis-seeded with batch 0 on L1); the instance shows what the two readings say when
`f > 0`.  Batches 0 and 1 settle at time 0, later ones at time 1. -/
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
