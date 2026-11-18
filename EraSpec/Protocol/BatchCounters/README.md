# BatchCounters

One settlement layer's batch counters, and one chain's two copies across a migration, at
era-contracts `draft/v0.35.0` head `b17415d20`: each diamond's `totalBatchesExecuted` (with its
`totalBatchesCommitted/Verified`, `storedBatchHashes`, `l2LogsRootHashes` and upgrade-transaction
fields) against the layer's `MessageRootBase.currentChainBatchNumber` and `chainBatchRoots`.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| MessageRootSync | [Specs/MessageRootSync.lean](Specs/MessageRootSync.lean) | [Properties/MessageRootSync.lean](Properties/MessageRootSync.lean) | [Proofs/MessageRootSync.lean](Proofs/MessageRootSync.lean) |
| MigrationContinuity | [Specs/MigrationContinuity.lean](Specs/MigrationContinuity.lean) | [Properties/MigrationContinuity.lean](Properties/MigrationContinuity.lean) | [Proofs/MigrationContinuity.lean](Proofs/MigrationContinuity.lean) |

Namespace `Contracts.BatchCounters`. Statements are `Contracts.BatchCounters.Properties.*`; each
certificate has the same name without the `Properties` segment. No statement takes a premise on
the stored-batch hash, which is an arbitrary function. Reject-only checks are omitted, so the
run-universal results cover more runs than the contracts allow; the enabledness results
(`ExecuteNeverRevertsInMessageRoot`, `ExecuteEnabledIffSynced`, `HonestArrivalsAccepted`) are
relative to the checks the model keeps (`MODEL-BATCH-COUNTERS` in `ASSUMPTIONS.md`).

## MessageRootSync: one layer

Steps are every writer of the modelled fields at `b17415d20`: `createNewChain`,
`registerAlreadyDeployedZKChain`, commit, prove, execute (with one `addChainBatchRootV32` per
batch), `_revertBatches`, the in-tree upgrade's transaction write, and the chain asset handler's
`bridgeBurn`, `bridgeMint` (onto a registered diamond or a fresh one) and failure confirmation.

- **Invariant.** The message root and the bridgehub register the same chains, an unregistered
  chain has no batch root, no batch after `currentChainBatchNumber` has a root (the NatSpec at
  `MessageRootBase.sol:89`), and every nonzero batch root is the diamond's `l2LogsRootHashes` entry
  (`HubStepPreservesInv`, `ReachableHubsSatisfyInv`); batch roots are write-once
  (`BatchRootsWriteOnce`), and an executed batch's logs root stays recorded in both places
  (`ExecutedRootsRecorded`).
- **Sync.** `currentChainBatchNumber[c] = totalBatchesExecuted` is preserved by every step whose
  mint data is consistent (`SyncedStaysSynced`, `SyncedAlongRuns`), with no premise while
  migrations are disabled (`HeadRunsKeepSync`); with migrations disabled, every chain of a layer
  reachable from the empty one is synced (`ReachableHeadHubsSynced`).
- **Liveness.** On an invariant layer, an execute passing the executor's own modelled checks with
  nonzero logs roots exists iff the counters agree (`ExecuteNeverRevertsInMessageRoot`,
  `ExecuteEnabledIffSynced`); a zero logs root is refused (`ZeroLogsRootRefused`,
  `ZeroLogsRootRefusedOnSyncedChain`).
- **Drift.** A chain whose counters disagree has no execute step (`DriftBlocksExecute`), and with
  migrations disabled both counters stay as they are (`DriftPersistsAtHead`). A chain registered
  before v31 whose v31 batch number was never saved (counter `0`, executed count positive) is such
  a chain (`LegacyUnsavedChainIsWedged`); with its counter at its executed count it executes
  (`LegacySavedChainExecutes`). At `b17415d20` nothing writes that counter for such a chain
  (`saveV31UpgradeChainBatchNumber` is removed); `protocol-docs/chain-lifecycle.md:218-223` makes
  every chain's per-chain v31 upgrade a precondition of the release, which is the premise `Synced`
  for those chains.

## MigrationContinuity: two layers

L1 and one settlement layer, each a `Hub`, and one chain `C` whose burn, mints and failure
confirmation are coupled steps passing the mint data through an honest, at-most-once channel.
Latent at `b17415d20`: `bridgeBurn` and `bridgeMint` carry `whenMigrationsEnabled` and
`CHAIN_MIGRATIONS_ENABLED = false`.

- **Mint data.** A synced chain's burn produces data whose batch number is the commitment's
  executed count, with every committed batch executed and one stored hash, the last executed
  batch's (`BurnDataConsistent`); with such data the mint never lowers the executed count or
  rewrites a stored hash below it (`ConsistentMintNeverLowersExecuted`). Countermodel: a stale
  commitment whose batch number passes `setMigratingChainBatchNumber`'s `<=` lowers
  `totalBatchesExecuted` from 10 to 5, rewrites `storedBatchHashes[7]` and `[10]`, and leaves the
  chain with no execute step (`StaleMintRewritesHistory`).
- **Two copies.** `TwoInv` holds along every run from a state satisfying it (`TwoInvInit`,
  `TwoStepPreservesInv`, `TwoRunKeepsInv`): exactly one copy settles or a migration is in flight
  (`ExactlyOneCopySettles`), pipeline steps need the settling copy (`PipelineOnlyOnSettlingCopy`),
  and an idle copy changes only by an arrival on its layer, apart from the `away` flag a failure
  confirmation clears (`IdleCopyChangesOnlyByMint`).
- **Continuity.** An arrival sets the destination's three counters and its message-root counter
  to the source's executed count `E`, writes the source's stored hash of batch `E` and no other,
  and copies the upgrade-transaction fields (`ArrivalOnL1CopiesSource`, `ArrivalOnSLCopiesSource`).
  The batch numbers executed for `C` on both layers together are exactly the next ones after its
  executed count, in order (`ExecutedLogContiguous`), and neither copy's executed count decreases
  (`CopiesNeverGoBack`). An honest arrival passes the kept checks (`HonestArrivalsAccepted`).
- **Migration numbers.** `MAX_ALLOWED_NUMBER_OF_MIGRATIONS` and the chain asset handlers'
  migration-number checks are omitted, so the model allows any number of round trips. In the
  source a chain departs from L1 only until its first return, so for a chain that starts on L1
  with migration number `0` and no settlement-layer diamond, no source run reaches the
  existing-diamond cases of `ArrivalOnSLCopiesSource` and `HonestArrivalsAccepted`
  (`Specs/MigrationContinuity.lean`, model boundaries).

Witnesses: `HubSyncWitness`, `HubUpgradeRevertWitness`, `LegacySavedChainExecutes`,
`LegacyUnsavedChainIsWedged`, `ZeroLogsRootRefusedOnSyncedChain`, `RoundTripWitness`,
`PendingUpgradeMigratesWitness`, `ReentryWitness`; each Properties module's table says which
premises each meets. `RoundTripWitness` (one round trip) and `PendingUpgradeMigratesWitness` (a
failed departure, then one round trip, carrying nonzero upgrade-transaction fields both ways) are
runs the source's migration-number checks accept; `ReentryWitness` is a run of the model only from
its second departure from L1 on.

Out of scope: the chain and shared trees and the historical roots that `_pushChainBatchRoot`
writes, `isValidSettlementLayer` and the migration interval bookkeeping, the priority tree, and the
message authentication behind the channel.
