# MessageRoot

Source: `contracts/core/message-root/MessageRootBase.sol` and `L1MessageRoot.sol` at era-contracts
`draft/v0.35.0` `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`. The cited files are byte-identical at
the earlier `draft/v0.35.0` pin `d9f6789`, so the line numbers hold at both. The chain trees use
`common/libraries/DynamicIncrementalMerkle.sol` (abstracted) and the shared tree uses
`common/libraries/FullMerkle.sol`, which is the `../FullMerkle/` transcription (byte-identical to
its `c67894b9` pin). Every state-changing entry point of the L1 contract is modelled
(`initialize`, `addNewChain`, `setMigratingChainBatchNumber`, `addChainBatchRoot`,
`addChainBatchRootV32`, `seedGenesisRoot`, `enableInterop`), and so is the final-node check of
the proof verifier. `L2MessageRoot` is not.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| Countermodels | [Specs/Countermodels.lean](Specs/Countermodels.lean) | [Properties/Countermodels.lean](Properties/Countermodels.lean) | [Proofs/Countermodels.lean](Proofs/Countermodels.lean) |

Namespace `Contracts.MessageRoot`. Statements are `Contracts.MessageRoot.Properties.*`;
each certificate has the same name without the `Properties` segment. No statement takes a hash
premise: every result holds for all node, leaf and chain-tree hash functions.

`Reachable` is storage reached by a successful `initialize` on fresh storage followed by any
successful calls, from any callers, in any order, each with its own environment. `initialize`
"is used in local deployments" (`L1MessageRoot.sol:62`); for a proxy upgraded from an earlier
release the statement that applies is `InvKeptByEveryCall`, conditional on its storage
satisfying `Inv` (`MODEL-MR-GENESIS`).

- **Invariant.** Every reachable storage satisfies `Inv` (`ReachableInv`), and every successful
  call keeps `Inv` from any storage (`InvKeptByEveryCall`).
- **Registration.** The chain the contract runs on sits at index 0, `chainIndexToId` is a
  bijection onto the registered chains (`ChainIndexBijection`), a chain is added once at the next
  index, by the Bridgehub or the chain asset handler (`ChainAddedOnce`), and registrations,
  indices and slots are permanent (`RegistrationStable`). A registration of an unregistered chain
  by either caller, with no counter overflow, succeeds (`AddNewChainLiveness`).
- **The aggregated root.** `getAggregatedRoot()` is the `FullMerkle` fold over one
  `chainIdLeafHash(chain root, chain id)` per slot (`AggregatedRootFormula`), so it is determined
  by the chain trees (`AggregatedRootDeterminedByChainTrees`). Equal aggregated roots give equal
  chain-tree roots or a collision on inputs taken from the two storages
  (`AggregatedRootPinsChainRootOrCollision`). The latest historical root is the aggregated root
  (`HistoricalRootIsAggregated`).
- **Batch roots and chain trees.** No batch root beyond the chain's counter
  (`BatchRootsBeyondCurrentAreZero`); batch roots are written once (`BatchRootsWriteOnce`) and
  are final once the counter passes them (`SettledBatchRootsFrozen`); counters never decrease
  (`CurrentBatchMonotone`). Each chain tree is set up exactly once (`ChainTreeSetUpOnce`), only
  grows (`ChainTreeAppendOnly`) and is a strictly increasing log of recorded batches
  (`ChainTreeIsOrderedLog`). Appends are by the chain's diamond, consecutive and exact
  (`AppendExact`), and do not revert when correctly ordered (`AppendLiveness`). The genesis root
  is the tree's first leaf (`GenesisSeedIsFirstLeaf`) and is seeded at most once
  (`GenesisSeedOnce`).
- **Who writes.** Along a run with no call from the chain's diamond (as `getZKChain` answered in
  that call) or the Bridgehub, the chain's batch roots, timestamps and tree are unchanged, and
  with no call from the chain asset handler either, so is its counter (`ChainWritersOnly`). A
  change to the roots or the tree names a call that made it (`ChainWriteProvenance`).
- **Migration.** On a registered chain, batch numbers skipped by `setMigratingChainBatchNumber`
  never get a root here, and from `v31UpgradeChainBatchNumber` on the final proof node never
  accepts them (`MigrationSkippedBatchesNeverRecorded`).
- **Proofs.** The final proof node's verdict, exactly (`FinalNodeAcceptsIff`); from
  `v31UpgradeChainBatchNumber` on it accepts only a recorded root at a batch number in `1 ..
  counter`, and batch 0 reverts (`ProofRootIsRecordedRoot`). The rest of the verifier is not
  modelled.
- **Bookkeeping.** `interopRootLogId` advances at most once per block (`LogIdOncePerBlock`);
  interop enablement is owner-only, needs a chain the Bridgehub knows with no balance backfill
  pending, and is permanent (`InteropEnabledOnce`); `initialize` cannot run twice
  (`NoReinitialization`).

Witnesses, one per group of premises, are tabulated in `Properties/Countermodels.lean`
(`EveryEntryPointRun`, `RegistrationPremisesHold`, `AppendPremisesHold`,
`MigrationPremisesHold`, `RunPremisesHold`, `WritersOnlyPremisesHold`, `LogIdPremisesHold`,
`InteropPremisesHold`, `SameTreesPremisesHold`). They use toy arithmetic hashes. With those,
`AggregatedRootCollisionFires` shows the collision disjunct can be the only true one, and
`FinalNodeFallbackFollowsTheChain` shows the pre-v31 case of `FinalNodeAcceptsIff`, where the
verdict follows the chain's `l2LogsRootHash` answer.

Countermodels and checks:
- `MigrationBeforeRegistrationIsOverwritten`: without the registration premise, a counter set
  by `setMigratingChainBatchNumber` is reset by a later `addNewChain`, and a batch in the
  skipped range is recorded and accepted.
- `ChainTreePositionIsNotBatchNumber`: on reachable storage where every batch with a root here
  is pushed and the first pushed batch is 0, position 2 of the chain tree holds batch 6, after a
  counter move by the chain asset handler. This is the breaker of `PROTO-CONTIGUOUS-PUSH`
  (ASSUMPTIONS.md), reached in this model at `b17415d2`.
- Load-bearing source checks: `ChainExists` (`RegisteredCheckLoadBearing`), the consecutive
  batch number (`ConsecutiveCheckLoadBearing`), the `<=` of `setMigratingChainBatchNumber`
  (`MigratingCheckLoadBearing`) and `MessageRootNotRegistered` in the record-only flow
  (`RecordRegisteredCheckLoadBearing`). On reachable storage the already-exists check never
  decides the outcome (`ExistsCheckRedundant`).

Model boundaries: the chain trees are abstracted to their leaf lists (`MODEL-MR-DIM`); external
calls return free per-call answers and never revert (`MODEL-MR-ENV`); runs start at
`initialize` (`MODEL-MR-GENESIS`); the shared tree is the `FullMerkle` transcription
(`MODEL-FULLMERKLE`). Numbers are `ℕ`, with the three checked increments (`chainCount`, the
batch counter, `interopRootLogId`) reverting at `2^256 - 1`. Events, `_getProofData` and the
settlement-layer recursion of the verifier are not modelled.
