# MessageRoot

## Headline guarantees

All about `l1-contracts/contracts/core/message-root/MessageRootBase.sol` and `L1MessageRoot.sol` at
era-contracts `draft/v0.35.0` head `b17415d20`. No statement assumes anything about the hash
functions. "Reachable storage" means storage reached by a successful `initialize` on fresh storage
followed by any successful calls, from any callers, in any order, each with its own environment
(block, timestamp, and the answers of the Bridgehub and the chains' getters).

- `Contracts.MessageRoot.Properties.ChainIndexBijection`: on reachable storage, the contract's own
  chain is at index 0 and the registered chains occupy distinct slots below `chainCount`.
- `Contracts.MessageRoot.Properties.BatchRootsWriteOnce`: along any run from reachable storage, a
  nonzero recorded batch root and its timestamp never change.
- `Contracts.MessageRoot.Properties.SettledBatchRootsFrozen`: for a registered chain whose counter
  is positive or whose genesis root is recorded, every batch root at or below the counter never
  changes along any run, and for batches at or above `v31UpgradeChainBatchNumber` the final-node
  verdict never changes either.
- `Contracts.MessageRoot.Properties.ChainTreeIsOrderedLog`: on reachable storage, each chain tree
  is the batch leaves of strictly increasing recorded batches, none above the chain's counter.
- `Contracts.MessageRoot.Properties.AppendExact`: on reachable storage, a successful append was
  sent by the chain's diamond (as the Bridgehub answered in that call), for a registered chain,
  with a nonzero root at the next batch number, and writes exactly that batch and leaf.
- `Contracts.MessageRoot.Properties.ChainWritersOnly`: along a run from reachable storage with no
  call from the chain's diamond (as answered in each call) or the Bridgehub, the chain's batch
  roots, timestamps and tree are unchanged; with no call from the chain asset handler either, so
  is its counter.
- `Contracts.MessageRoot.Properties.MigrationSkippedBatchesNeverRecorded`: for a chain registered
  on reachable storage, batch numbers skipped by `setMigratingChainBatchNumber` are never recorded,
  and from `v31UpgradeChainBatchNumber` on the final proof node never accepts them.
- `Contracts.MessageRoot.Properties.ProofRootIsRecordedRoot`: on reachable storage the final proof
  node reverts on batch 0, and from `v31UpgradeChainBatchNumber` on it accepts only the nonzero
  recorded root of a batch in `1 .. counter`.
- `Contracts.MessageRoot.Properties.AggregatedRootPinsChainRootOrCollision`: two reachable storages
  with the same chain count and the same chain in a slot, and equal aggregated roots, have equal
  chain-tree roots for that chain, or a collision of `chainIdLeafHash` or of the node hash is
  located at named inputs from the two storages.
- `Contracts.MessageRoot.Properties.GenesisSeedOnce`: on reachable storage where a chain's genesis
  root is recorded, or the chain is registered with a positive counter, `seedGenesisRoot` for it
  reverts after any run.

- `Contracts.MessageRoot.Aggregation.Properties.AggregatesStrictFromMessageRoot`: in the
  ghost-instrumented view (topic `Aggregation`: caller checks and overflow omitted, blocks with
  non-decreasing or strictly increasing timestamps), every chain-tree leaf that settled strictly
  before a historical root was written is counted by that root, for the root as it stood at any
  point of a run from `initialize` and in every later state.

Witnesses for each premise group are in `Properties/Countermodels.lean`; countermodels there show
the registration premise and four source checks are needed.

## Topics

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Model (canonical) | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| Countermodels | [Specs/Countermodels.lean](Specs/Countermodels.lean) | [Properties/Countermodels.lean](Properties/Countermodels.lean) | [Proofs/Countermodels.lean](Proofs/Countermodels.lean) |
| Aggregation | [Specs/Aggregation.lean](Specs/Aggregation.lean) | [Properties/Aggregation.lean](Properties/Aggregation.lean) | [Proofs/Aggregation.lean](Proofs/Aggregation.lean) |

## Model and Countermodels (canonical)

Namespace `Contracts.MessageRoot`; statements are `Contracts.MessageRoot.Properties.*`, each proved
by the theorem of the same name without `Properties`. Every state-changing entry point of the L1
contract is modelled (`initialize`, `addNewChain`, `setMigratingChainBatchNumber`,
`addChainBatchRoot`, `addChainBatchRootV32`, `seedGenesisRoot`, `enableInterop`), and so is the
final-node check of the proof verifier. `L2MessageRoot` is not. The shared tree is the `FullMerkle`
transcription; the chain trees are abstracted to their leaf lists.

Further results: `ReachableInv` and `InvKeptByEveryCall` (the storage invariant `Inv`, from any
storage satisfying it), `ChainAddedOnce`, `AddNewChainLiveness`, `RegistrationStable`,
`AggregatedRootFormula`, `AggregatedRootDeterminedByChainTrees`, `HistoricalRootIsAggregated`,
`BatchRootsBeyondCurrentAreZero`, `ChainTreeSetUpOnce`, `ChainTreeAppendOnly`,
`CurrentBatchMonotone`, `AppendLiveness`, `GenesisSeedIsFirstLeaf`, `ChainWriteProvenance`,
`FinalNodeAcceptsIff`, `LogIdOncePerBlock`, `InteropEnabledOnce`, `NoReinitialization`.

Countermodels and checks (`Properties/Countermodels.lean`): `MigrationBeforeRegistrationIsOverwritten`,
`ChainTreePositionIsNotBatchNumber` (the breaker of `PROTO-CONTIGUOUS-PUSH`),
`RegisteredCheckLoadBearing`, `ConsecutiveCheckLoadBearing`, `MigratingCheckLoadBearing`,
`RecordRegisteredCheckLoadBearing`, `ExistsCheckRedundant`, `AggregatedRootCollisionFires`,
`FinalNodeFallbackFollowsTheChain`.

Model boundaries: chain trees as leaf lists (`MODEL-MR-DIM`); external calls return free per-call
answers and never revert (`MODEL-MR-ENV`); runs start at `initialize` (`MODEL-MR-GENESIS`); the
shared tree is the `FullMerkle` transcription (`MODEL-FULLMERKLE`). Numbers are `ℕ`, with the three
checked increments reverting at `2^256 - 1`. Events, `_getProofData` and the settlement-layer
recursion of the verifier are not modelled.

Other folders link to this model: `../ChainBatchRootTree/` topic `MessageRootLink` (every call
moves one chain's slice as `GenesisSeed`'s `seedExec` does) and `../MessageVerification/` topic
`Refinement` (the status proof against `chainBatchRoots`).

## Aggregation

Namespace `Contracts.MessageRoot.Aggregation`. The same code, `b17415d20`, seen with ghost state:
each chain tree as its pushed leaves with their preimages and push blocks, and each historical root
with the leaf counts it aggregated, under a block clock whose timestamps are non-decreasing or
strictly increasing. Caller checks and overflow are not modelled (more runs). It feeds
`../../Protocol/InteropAtomicity/` topic `SettlementRoots`. No simulation from the canonical Model
to this one is proved yet (`handoff/2026-11-19/consolidation/roots.md`).

- The registry and the trees: `ChainIndexInjective`, `ChainIndexIsAPosition`,
  `SharedLeafIsChainIdLeaf`, `FreshChainLeafIsZeroRoot`, `ChainLeavesArePushedBatches`,
  `UnrecordedAboveCurrent` (the source's invariant at `MessageRootBase.sol:89`),
  `BatchRootWriteOnce`, `UnregisteredChainHoldsNothing`.
- The clock: `LeavesOrdered`, `LeafTimeMonotone`, `LeafTimeMonotoneAsWord`.
- Historical roots: `HistoricalRootIsSnapshot`, `LastWriteInBlockWins`; every leaf that settled
  strictly before a root was written is counted by it (`AggregatesStrictFromMessageRoot`,
  `PushedAfterLastIsLate`), and under strictly increasing timestamps the non-strict form holds
  (`AggregatesFromMessageRootStrictTs`). Equal timestamps across blocks or a mid-block read break
  the non-strict form (`EqualTimestampEscapesRoot`, `MidBlockReadEscapesRoot`).
- Positions, not batch numbers: `RecordOnlyBatchNotCitable`, `RecordOnlyGap`,
  `OnboardedChainPositionsAreNotBatchNumbers`.

Witnesses: `AggregationWitness`, `AggregationRegistryWitness`, `RecordOnlyBatchNotCitableWitness`.
Model boundary: `MODEL-MESSAGE-ROOT` in `ASSUMPTIONS.md`.
