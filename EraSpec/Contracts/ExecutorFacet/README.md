# ExecutorFacet

The batch pipeline of one ZK chain's diamond (commit, prove, execute, revert) at era-contracts
`draft/v0.35.0` `b17415d20`.

## Headline guarantees

The folder's `@[headline]` statements (see [CONSOLIDATION.md](../../../CONSOLIDATION.md)).
"Reachable" means reached from a chain right after `DiamondInit` by any interleaving of the
model's eleven calls, for any `Env` (verifier, DA validator results, dependency roots). No
statement assumes a hash injective: "unless a collision was submitted" means unless the run logged
a hash break, and the first logged break is a concrete collision of two `StoredBatchInfo` values
(`LoggedHashBreaksAreCollisions`). The return of a migration (`forwardedBridgeMint`) is not a step.

| Guarantee | Premises | Statement |
|---|---|---|
| `executed ≤ verified ≤ committed` | Reachable state | `CountersOrdered` |
| Nothing lowers the executed count; only a revert or priority-mode activation lowers committed or verified | None (any state, one call) | `OnlyRevertMovesCountersBack` |
| `_revertBatches(n)` succeeds exactly when `executed ≤ n ≤ committed`, and changes only the committed and verified counts and the upgrade batch number | None | `RevertBatchesEffect` |
| Commit, prove and execute run on the settlement layer, by a validator outside priority mode or the permissionless validator in it; a priority-mode batch carries priority transactions only | None (one call) | `OnlySettlersSettle` |
| The executed batches are exactly `1, 2, …, executed`, each once, in order | Reachable state | `ExecutedExactlyOnceInOrder` |
| The executed log only grows and the log roots of executed batches never change | A run from a reachable state | `ExecutedIsFinal` |
| Every executed batch is the `StoredBatchInfo` this chain committed for that number and was covered by a proof the verifier accepted | Reachable state; unless a collision was submitted | `ExecutedBatchesWereCommittedAndProved` |
| The verifier accepted every logged proof, and every verified, unexecuted batch has an accepted proof for its current contents | Reachable state; the second part unless a collision was submitted | `VerifiedBatchesHaveAcceptedProofs` |
| The priority operations consumed are exactly those of executed batches; each batch's items match its count and rolling hash; they are the first operations pushed, in order | Reachable state; the last part unless a Merkle break was logged (a proof `processBatch` accepted for items that are not the pushed ones) | `PriorityOpsConsumedInOrder` |
| A pending L2 upgrade transaction is in batch `executed + 1` and in no other unexecuted batch, and nothing is committed past it without it | Reachable state; unless a collision was submitted | `UpgradeTxInFirstUnexecutedBatch` |
| The next honest commit, on top of the last committed batch, by an admitted caller, is enabled | Reachable state with no hash break logged; on the settlement layer; the omitted reject-only checks can still reject it in the source | `HonestCommitEnabled` |

Witnesses (`@[witness]`): `PipelineWitness`, `RevertRecommitWitness`, `PriorityModeWitness`,
`HonestProgressWitness`, `AdminWitness`. Countermodels (`@[countermodel]`):
`WithoutCommittedCheckProofsOutrunCommits`, `WithoutProvenCheckExecutionOutrunsProofs`,
`WithoutExecutedCheckRevertRewritesAnExecutedBatch`, `UpgradeWithoutExecutedCheckSkipsABatch`,
`CollisionRewritesAnExecutedBatch`, `MerkleBreakConsumesAnUnpushedOp`. The other statements are
supporting lemmas.

## Source

The batch pipeline of one ZK chain's diamond at era-contracts `draft/v0.35.0`
commit **`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`**, under `l1-contracts/contracts/`:
`CommitterFacet.commitBatchesSharedBridge`, `ExecutorFacet`'s `proveBatchesSharedBridge`,
`executeBatchesSharedBridge` and `revertBatchesSharedBridge`, `ZKChainBase._revertBatches`,
`PriorityTree`, the priority-mode entry points and `setValidator` of `AdminFacet`, the L2
upgrade-transaction write of `BaseZkSyncUpgrade`, and the settlement-layer writes of a
migration's start and failure (`MigratorFacet`). Every `file:line` is at that commit.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those
exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Pipeline | [Specs/Pipeline.lean](Specs/Pipeline.lean) | [Properties/Pipeline.lean](Properties/Pipeline.lean) | [Proofs/Pipeline.lean](Proofs/Pipeline.lean), with [Proofs/Invariant.lean](Proofs/Invariant.lean) and [Proofs/StepFacts.lean](Proofs/StepFacts.lean) |
| Checks | [Specs/Witness.lean](Specs/Witness.lean) (concrete runs) | [Properties/Checks.lean](Properties/Checks.lean) | [Proofs/Checks.lean](Proofs/Checks.lean) |

Namespace `Contracts.ExecutorFacet`. Statements are `Contracts.ExecutorFacet.Properties.*`;
each certificate has the same name without the `Properties` segment.

## What to check

Run-level statements hold in every state `Reach env s`: reachable from a chain right after
`DiamondInit` by any interleaving of the model's eleven calls, for any `Env`. No statement
assumes a hash is injective. Where a guarantee needs `keccak256(abi.encode(StoredBatchInfo))`
to bind its preimage, it holds unless the run logged a hash break, and the first logged break
is a collision between two concrete `StoredBatchInfo` values (`LoggedHashBreaksAreCollisions`).
That break can be anywhere in the run, not necessarily at the batch the statement is about.

- **Counters.** `executed ≤ verified ≤ committed` (`CountersOrdered`). Only a revert or
  priority-mode activation lowers committed or verified, nothing lowers executed
  (`OnlyRevertMovesCountersBack`). `_revertBatches(n)` succeeds exactly when
  `executed ≤ n ≤ committed`, with an exact post-state (`RevertBatchesEffect`). Who may
  revert, when, and what activation does (`RevertEntryPoints`); who may commit, prove and
  execute, and that priority-mode batches carry priority transactions only
  (`OnlySettlersSettle`). No hash premise.
- **Executed batches.** Executed exactly once each, in order `1, 2, …`
  (`ExecutedExactlyOnceInOrder`); the executed log and the log roots of executed batches
  never change (`ExecutedIsFinal`, `ExecutedLogRootsRecorded`). No hash premise. Unless a
  hash break was logged: their stored hashes never change (`ExecutedStoredHashesFinal`), and
  each executed batch is the committed `StoredBatchInfo`, covered by an accepted proof
  (`ExecutedBatchesWereCommittedAndProved`).
- **Committed and verified batches**, unless a hash break was logged: stored hashes chain
  through `_commitOneBatch`, fee units included after a re-commit (`StoredHashesChain`); every
  verified, unexecuted batch has an accepted proof for its current contents
  (`VerifiedBatchesHaveAcceptedProofs`, whose verifier half needs no hash premise).
- **What each call processes.** `execute` takes exactly the next batches, and checks their
  priority-op count, rolling hash and dependency-roots hash (`ExecuteTakesTheNextBatches`,
  no hash premise); `prove` the next committed batches (`ProveTakesTheNextBatches`) and
  `commit` the next batch (`CommitTakesTheNextBatch`), unless a hash break was logged.
- **Honest progress.** From a reachable state with no hash break logged, the next commit by
  an admitted caller on top of the last committed batch is always enabled
  (`HonestCommitEnabled`), and the proof of the next committed batches is enabled exactly
  when the verifier accepts it (`HonestProveEnabledIff`). The checks the model omits can still
  reject these calls in the source. Execution has no such statement.
- **Priority operations.** Only `execute` consumes them, and nothing returns them
  (`PriorityOpsConsumedOnlyByExecute`). Unless a Merkle break was logged, the operations
  consumed are the first ones pushed, in order (`PriorityOpsConsumedInOrder`). A Merkle break
  is a proof `processBatch` accepted for items that are not the pushed ones
  (`LoggedMerkleBreaksAreForgeries`); the model does not say what producing one takes for the
  real tree, which `processBatch` leaves to the validity proof (`PriorityTree.sol:77-82`).
- **The L2 upgrade transaction**, unless a hash break was logged: a pending transaction is in
  batch `executed + 1` and in no other unexecuted batch, and nothing is committed past it
  without it (`UpgradeTxInFirstUnexecutedBatch`). This rests on the upgrade engines'
  `_requireAllBatchesExecuted`.

`Checks` runs concrete calls under a toy `Env`:

- **Each check is load-bearing.** Without `VerifiedBatchesExceedsCommittedBatches` a stale
  stored hash left by a revert lets a proof outrun the commits
  (`WithoutCommittedCheckProofsOutrunCommits`); without `CantExecuteUnprovenBatches` a batch
  executes unproved (`WithoutProvenCheckExecutionOutrunsProofs`); without
  `CantRevertExecutedBatch` an executed batch is reverted and its stored hash rewritten
  (`WithoutExecutedCheckRevertRewritesAnExecutedBatch`); without the engines' "all batches
  executed" guard the upgrade transaction lands in a later batch
  (`UpgradeWithoutExecutedCheckSkipsABatch`). Each run logs no break, and the source rejects
  it at that check.
- **The break disjuncts are needed.** A submitted collision rewrites an executed batch
  (`CollisionRewritesAnExecutedBatch`); a Merkle break consumes an operation never pushed
  (`MerkleBreakConsumesAnUnpushedOp`).
- **The unchecked increment.** The model's verified count is the source's `uncheckedInc`
  loop counter while the counters fit in a `uint256` (`UncheckedIncExactBelowWrap`).
- **Witnesses.** `PipelineWitness` (from `Init`, no break: three batches committed, proved
  and executed, three priority operations consumed, an upgrade transaction carried and
  cleared), `RevertRecommitWitness`, `PriorityModeWitness`, `HonestProgressWitness`,
  `AdminWitness`.

## Model boundaries

`MODEL-EXEC-PIPELINE` in [ASSUMPTIONS.md](../../../ASSUMPTIONS.md). A revert is the absence
of a step and every call is atomic (`MODEL-COMMIT`, `VM-REVERT`). Counters and batch numbers
are `ℕ`. Reject-only checks are omitted, which only adds runs: protocol version, chain config
hash, timestamps, chain ids, DA scheme, block range, `onlyL1`, priority-mode activation
conditions, the Mailbox's checks and most of the migration's. External calls are not
modelled: the DA validator, the L2 messenger, `MessageRoot.addChainBatchRootV32`, the
dependency-root lookups (only their result is an input) and the interop-fee charge. `Env`
is fixed for a run; a verifier replaced by an upgrade is covered by reading `Env.verify` as
"accepted by the verifier installed at the time", without recording which. Not modelled:
the return of a migration (`forwardedBridgeMint`), so the results cover a chain from
`DiamondInit` until such a return; upgrade code other than the L2 upgrade-transaction write;
calls whose unchecked loop counter wraps, which need at least `2^256 - verified` batches in
one call; events. That the deployed facets execute this transcription is open
(`VM-STORAGE`, `SOL-ARITH`, `SOL-ABI`).

`../AdminFacet/` transcribes the same `_revertBatches`, and the priority-mode entry points with
the checks this model omits. `RevertBatchesAgreesWithExecutorModel` there proves the two
`_revertBatches` succeed together and write the same counters; the rest of the two models is not
composed. `processBatch` is abstract here (`Env` and the Merkle-break log); the library itself is
modelled in `../PriorityTree/`.
