import EraSpec.Contracts.ExecutorFacet.Specs.Witness

/-!
# Properties: what each check and each break disjunct does, on concrete runs

Statements about the concrete environments and runs of
`EraSpec.Contracts.ExecutorFacet.Specs.Witness`. Proofs are in
`EraSpec.Contracts.ExecutorFacet.Proofs.Checks`; every run is evaluated by `decide`.

* **Each check is load-bearing.** For four checks of the source, a run that the source
  rejects at that check, and that succeeds without it (`Ablation`), reaching a state that
  falsifies a `Pipeline` statement with no break logged:
  `WithoutCommittedCheckProofsOutrunCommits`, `WithoutProvenCheckExecutionOutrunsProofs`,
  `WithoutExecutedCheckRevertRewritesAnExecutedBatch`, `UpgradeWithoutExecutedCheckSkipsABatch`.
* **The break disjuncts are needed.** Under a toy hash that ignores the batch number, a
  submitted collision rewrites an executed batch (`CollisionRewritesAnExecutedBatch`); under a
  toy Merkle function that opens the empty tree's root for any items, a batch consumes a
  priority operation that was never pushed (`MerkleBreakConsumesAnUnpushedOp`). In both the
  run logs the break, so the statements hold by their break disjunct.
* **The unchecked increment.** The model's `totalBatchesVerified + k` is the source's
  `uncheckedInc` loop counter when the counters fit in a `uint256`
  (`UncheckedIncExactBelowWrap`).
* **Witnesses.** `PipelineWitness` (from `Init`, with no break logged: three batches committed,
  proved and executed, priority operations consumed, an upgrade transaction carried and
  cleared), `RevertRecommitWitness`, `PriorityModeWitness`, `HonestProgressWitness`,
  `AdminWitness`. Together they instantiate the premises of every `Pipeline` statement with
  calls of every kind.

Source: era-contracts `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`.
-/

namespace Contracts.ExecutorFacet

/-! ## Each check is load-bearing -/

/-- **THE COMMITTED CHECK IS LOAD-BEARING** (`VerifiedBatchesExceedsCommittedBatches`,
`Ex:243-245`). `wStaleProveRun` commits batch 1, reverts it, and proves it again: the revert
left batch 1's hash in `storedBatchHashes[1]` (`_revertBatches` clears no slot,
`Base:317-337`), so the loop's hash check passes. The source runs the first two calls and
rejects the proof at the committed check. Without that check the proof is accepted, no hash
break is logged, and the chain has more verified batches than committed ones, against
`CountersOrdered`. -/
def Properties.WithoutCommittedCheckProofsOutrunCommits : Prop :=
  Init wEnv wInit ∧
  (runCalls wEnv wInit (wStaleProveRun.take 2)).isSome = true ∧
  runCalls wEnv wInit wStaleProveRun = none ∧
  ∃ s, runCallsWith { committedCheck := true } wEnv wInit wStaleProveRun = some s ∧
    s.totalBatchesCommitted < s.totalBatchesVerified ∧ s.hashBreaks = []

/-- **THE PROVEN CHECK IS LOAD-BEARING** (`CantExecuteUnprovenBatches`, `Ex:203-205`).
`wUnprovenExecRun` commits batch 1 and executes it with no proof. The source rejects the
execute. Without the check it succeeds, no hash break is logged, and the chain has more
executed batches than verified ones, against `CountersOrdered`. -/
def Properties.WithoutProvenCheckExecutionOutrunsProofs : Prop :=
  (runCalls wEnv wInit (wUnprovenExecRun.take 1)).isSome = true ∧
  runCalls wEnv wInit wUnprovenExecRun = none ∧
  ∃ s, runCallsWith { provenCheck := true } wEnv wInit wUnprovenExecRun = some s ∧
    s.totalBatchesVerified < s.totalBatchesExecuted ∧ s.hashBreaks = []

/-- **`_revertBatches`'s EXECUTED CHECK IS LOAD-BEARING** (`CantRevertExecutedBatch`,
`Base:321-323`). `wRevertExecutedRun` commits, proves and executes batch 1, reverts to batch
0, and commits a different batch 1. The source runs the first three calls and rejects the
revert. Without the check:

* right after the revert the committed count is below the executed one, against
  `CountersOrdered`;
* after the re-commit, `storedBatchHashes[1]` no longer holds the hash of the executed batch 1,
  and no hash break is logged, against `ExecutedStoredHashesFinal` and
  `ExecutedBatchesWereCommittedAndProved`. -/
def Properties.WithoutExecutedCheckRevertRewritesAnExecutedBatch : Prop :=
  (runCalls wEnv wInit (wRevertExecutedRun.take 3)).isSome = true ∧
  runCalls wEnv wInit (wRevertExecutedRun.take 4) = none ∧
  (∃ s, runCallsWith { executedCheck := true } wEnv wInit (wRevertExecutedRun.take 4) = some s ∧
    s.totalBatchesCommitted < s.totalBatchesExecuted) ∧
  ∃ s, runCallsWith { executedCheck := true } wEnv wInit wRevertExecutedRun = some s ∧
    s.totalBatchesExecuted = 1 ∧ s.executed.map (·.info) = [wPlain1] ∧
    s.storedBatchHashes 1 ≠ wEnv.hashStored wPlain1 ∧ s.hashBreaks = []

/-- **THE UPGRADE ENGINES' "ALL BATCHES EXECUTED" GUARD IS LOAD-BEARING**
(`_requireAllBatchesExecuted`, `Up:115-119`). `wEarlyUpgradeRun` commits batch 1, runs an
upgrade that sets transaction `9`, and commits batch 2. The source rejects the upgrade.
Without the guard the transaction is committed in batch 2 while batch 1 is not executed, so
the upgrade batch is not `executed + 1`, and no hash break is logged, against
`UpgradeTxInFirstUnexecutedBatch`. -/
def Properties.UpgradeWithoutExecutedCheckSkipsABatch : Prop :=
  (runCalls wEnv wInit (wEarlyUpgradeRun.take 1)).isSome = true ∧
  runCalls wEnv wInit (wEarlyUpgradeRun.take 2) = none ∧
  ∃ s, runCallsWith { upgradeExecutedCheck := true } wEnv wInit wEarlyUpgradeRun = some s ∧
    s.totalBatchesExecuted = 0 ∧ s.l2SystemContractsUpgradeBatchNumber = 2 ∧
    (s.commitArgs 2).map (·.upgradeTxHash) = some 9 ∧ s.hashBreaks = []

/-! ## The break disjuncts are needed -/

/-- **A SUBMITTED COLLISION REWRITES AN EXECUTED BATCH.** Under `wCollEnv`, whose stored-batch
hash ignores the batch number, from its fresh chain (`Init`): `wCollRun` commits, proves and
executes batch 1 and logs no break. Then `wCollCommit` presents batch 1 renumbered `0` as the
last committed batch. It hashes like batch 1, passes the check against slot `1`, and the
call writes a different batch 1 over the executed one. So the main disjunct of
`ExecutedStoredHashesFinal` fails between the two states, and its collision disjunct holds:
the call logged the pair, and the log's first entry is a genuine collision. -/
def Properties.CollisionRewritesAnExecutedBatch : Prop :=
  Init wCollEnv (wInitOf wCollEnv) ∧
  ∃ s s', runCalls wCollEnv (wInitOf wCollEnv) wCollRun = some s ∧
    step wCollEnv s wCollCommit = some s' ∧
    Reach wCollEnv s ∧ Steps wCollEnv s s' ∧
    s.totalBatchesExecuted = 1 ∧ s.hashBreaks = [] ∧
    s'.storedBatchHashes 1 ≠ s.storedBatchHashes 1 ∧
    s'.hashBreaks ≠ [] ∧ HashBreakLogged wCollEnv s'

/-- **A MERKLE BREAK CONSUMES AN OPERATION THAT WAS NEVER PUSHED.** Under `wMerkleEnv`, where
every priority-op proof opens the empty tree's root, from its fresh chain (`Init`) with no
priority operation pushed: `wMerkleRun` commits, proves and executes batch 1 carrying operation
`77`, and `processBatch` accepts it against the empty tree's root. The main disjunct of
`PriorityOpsConsumedInOrder` fails (one operation consumed, none pushed), and a genuine
Merkle break is logged. -/
def Properties.MerkleBreakConsumesAnUnpushedOp : Prop :=
  Init wMerkleEnv (wInitOf wMerkleEnv) ∧
  ∃ s, runCalls wMerkleEnv (wInitOf wMerkleEnv) wMerkleRun = some s ∧ Reach wMerkleEnv s ∧
    consumed s = [77] ∧ s.ptLeaves = [] ∧ s.ptUnprocessedIndex = 1 ∧
    s.merkleBreaks ≠ [] ∧ MerkleBreakLogged wMerkleEnv s ∧ s.hashBreaks = []

/-! ## The unchecked increment -/

/-- **THE MODEL'S VERIFIED COUNT IS THE SOURCE'S UNCHECKED COUNTER, BELOW `2^256`.**
`uncheckedIncN v k`, `k` applications of `UncheckedMath.uncheckedInc` to the `uint256` `v`, is
`v + k` when that is below `2^256`, and it wraps at `2^256` (`uncheckedInc(2^256 - 1) = 0`).
For any successful `prove` call of the model from a state whose committed count is below
`2^256`, as a `uint256` counter's is, the source's loop counter after the `k` listed batches
(`Ex:237-242`) is the model's new verified count. -/
def Properties.UncheckedIncExactBelowWrap : Prop :=
  (∀ (v : UInt256) (k : Nat), v.val + k < UInt256.size → (uncheckedIncN v k).val = v.val + k) ∧
  uncheckedIncN ((UInt256.size - 1 : Nat) : UInt256) 1 = 0 ∧
  ∀ (env : Env) (s s' : State) (c : ProveCall), prove env s c = some s' →
    s.totalBatchesCommitted < UInt256.size →
    (uncheckedIncN (s.totalBatchesVerified : UInt256) c.batches.length).val =
      s'.totalBatchesVerified

/-! ## Witnesses -/

/-- **THE PIPELINE RUNS FROM A FRESH CHAIN, WITH NO BREAK.** `wInit` satisfies `Init` and the
main run `wRun` succeeds without logging a hash or Merkle break.

* After its first seven calls (the genesis upgrade, three commits, three priority operations
  pushed, nothing proved): upgrade transaction `9` is pending in batch `1 = executed + 1`,
  which was committed with it; batches 2 and 3 were committed with upgrade hash `0`.
* After `wRunA` (state `sA`): executed `1` < verified `2` < committed `3`; executing batch 1
  consumed two priority operations and cleared the upgrade transaction.
* After `wRunB` from `sA` (state `s`, so `Steps wEnv sA s`): batches 1, 2, 3 executed in
  order, by two calls (the second with two batches); the operations consumed are
  `11, 12, 13`, the leaves pushed; the log roots recorded are `31, 32, 33`; every executed
  batch is the committed `StoredBatchInfo` and is covered by an accepted proof. -/
def Properties.PipelineWitness : Prop :=
  Init wEnv wInit ∧
  (∃ s, runCalls wEnv wInit (wRunA.take 7) = some s ∧ Reach wEnv s ∧
    s.totalBatchesExecuted = 0 ∧ s.totalBatchesCommitted = 3 ∧
    s.l2SystemContractsUpgradeTxHash = 9 ∧ s.l2SystemContractsUpgradeBatchNumber = 1 ∧
    (s.commitArgs 1).map (·.upgradeTxHash) = some 9 ∧
    (s.commitArgs 2).map (·.upgradeTxHash) = some 0 ∧
    (s.commitArgs 3).map (·.upgradeTxHash) = some 0 ∧ s.hashBreaks = []) ∧
  ∃ sA s, runCalls wEnv wInit wRunA = some sA ∧ runCalls wEnv sA wRunB = some s ∧
    Reach wEnv sA ∧ Steps wEnv sA s ∧
    sA.totalBatchesExecuted = 1 ∧ sA.totalBatchesVerified = 2 ∧
    sA.totalBatchesCommitted = 3 ∧
    sA.l2SystemContractsUpgradeTxHash = 0 ∧ sA.l2SystemContractsUpgradeBatchNumber = 0 ∧
    sA.ptUnprocessedIndex = 2 ∧ sA.hashBreaks = [] ∧ sA.merkleBreaks = [] ∧
    s.totalBatchesExecuted = 3 ∧ s.totalBatchesVerified = 3 ∧ s.totalBatchesCommitted = 3 ∧
    s.executed.map (·.info) = [wInfo1, wInfo2, wInfo3] ∧
    consumed s = [11, 12, 13] ∧ s.ptLeaves = [11, 12, 13] ∧
    s.l2LogsRootHashes 1 = 31 ∧ s.l2LogsRootHashes 2 = 32 ∧ s.l2LogsRootHashes 3 = 33 ∧
    s.hashBreaks = [] ∧ s.merkleBreaks = [] ∧
    ProvedAt s 1 wInfo1 ∧ ProvedAt s 2 wInfo2 ∧ ProvedAt s 3 wInfo3

/-- **A REVERT AND RE-COMMIT: THE UPGRADE TRANSACTION IS CARRIED AGAIN, AND THE FEE UNITS AND
THE PROOF FOLLOW THE NEW CONTENTS.** `wRecommitRun` is the main run up to the proof of batches
1 and 2, then a validator's revert to batch 0 and a re-commit of batch 1 with other contents
and no interop fee units. In the state reached, with no hash break logged:

* the revert reset the upgrade batch number, so the re-committed batch 1 carries upgrade
  transaction `9` again;
* `interopFeeUnits[1]` is `0`, no longer the reverted batch's `6` (`Co:139-140`);
* nothing is verified; the proof accepted for the old batch 1 is still logged (`ProvedAt` for
  `wInfo1`) and does not cover the new batch 1;
* a proof of the old batch 1 is now rejected, and one of the new batch 1 is accepted. -/
def Properties.RevertRecommitWitness : Prop :=
  ∃ s, runCalls wEnv wInit wRecommitRun = some s ∧ Reach wEnv s ∧
    s.totalBatchesCommitted = 1 ∧ s.totalBatchesVerified = 0 ∧
    s.l2SystemContractsUpgradeBatchNumber = 1 ∧ s.preimage 1 = wInfo1' ∧
    (s.commitArgs 1).map (·.upgradeTxHash) = some 9 ∧
    s.interopFeeUnits 1 = 0 ∧ s.hashBreaks = [] ∧
    ProvedAt s 1 wInfo1 ∧ ¬ ProvedAt s 1 wInfo1' ∧
    prove wEnv s ⟨1, 1, 1, wGenesis, [wInfo1], wProof [wInfo1]⟩ = none ∧
    ∃ s', prove wEnv s ⟨1, 1, 1, wGenesis, [wInfo1'], wProof [wInfo1']⟩ = some s' ∧
      s'.totalBatchesVerified = 1 ∧ ProvedAt s' 1 wInfo1'

/-- **PRIORITY MODE: ACTIVATION REVERTS TO THE EXECUTED BATCHES, THEN ONLY THE PERMISSIONLESS
VALIDATOR SETTLES, WITH PRIORITY TRANSACTIONS ONLY.** From the state `s0` after the main run's
first eight calls (three batches committed, two verified, none executed), anyone's
`activatePriorityMode` takes the committed and verified counts to `0` and resets the upgrade
batch number, keeping transaction `9` pending. Then:

* validator `1` can neither commit nor revert;
* the permissionless validator `3` cannot commit a batch with L2 transactions;
* `wPriorityTail`: `3` commits, proves and executes the priority-only batch 1, which carries
  upgrade transaction `9`, and the chain type manager `2` deactivates priority mode. -/
def Properties.PriorityModeWitness : Prop :=
  ∃ s0 s, runCalls wEnv wInit (wRunA.take 8) = some s0 ∧
    step wEnv s0 .activatePriorityMode = some s ∧ Reach wEnv s ∧
    s0.totalBatchesCommitted = 3 ∧ s0.totalBatchesVerified = 2 ∧ s0.totalBatchesExecuted = 0 ∧
    s.priorityModeActivated = true ∧
    s.totalBatchesCommitted = 0 ∧ s.totalBatchesVerified = 0 ∧
    s.l2SystemContractsUpgradeBatchNumber = 0 ∧ s.l2SystemContractsUpgradeTxHash = 9 ∧
    step wEnv s (.commit ⟨1, 1, 1, wGenesis, [wInP]⟩) = none ∧
    step wEnv s (.revert 1 0) = none ∧
    step wEnv s (.commit ⟨3, 1, 1, wGenesis, [wIn1]⟩) = none ∧
    ∃ s', runCalls wEnv s wPriorityTail = some s' ∧
      s'.totalBatchesExecuted = 1 ∧ s'.priorityModeActivated = false ∧
      s'.executed.map (·.info) = [wInfoP] ∧ (s'.commitArgs 1).map (·.upgradeTxHash) = some 9 ∧
      s'.l2SystemContractsUpgradeTxHash = 0 ∧ s'.hashBreaks = []

/-- **THE HONEST-PROGRESS PREMISES ARE MET, BOTH WAYS.** In the state after the main run's
first seven calls (three batches committed, none verified, no break logged), validator `1`
and `k = 2` meet every premise of `HonestProveEnabledIff`: the batches it names are `wInfo1`
and `wInfo2`, `wEnv.verify` accepts `wProof [wInfo1, wInfo2]` and rejects `[0]`. In the state
right after `activatePriorityMode` in `PriorityModeWitness` (no break logged), the
permissionless validator `3` and the priority-only batch `wInP` meet every premise of
`HonestCommitEnabled`, the priority-mode one included. -/
def Properties.HonestProgressWitness : Prop :=
  (∃ s, runCalls wEnv wInit (wRunA.take 7) = some s ∧ Reach wEnv s ∧ s.hashBreaks = [] ∧
    s.settlementLayer = 0 ∧ settlerAllowed s 1 = true ∧
    s.totalBatchesVerified + 2 ≤ s.totalBatchesCommitted ∧
    (List.range 2).map (fun j => s.preimage (s.totalBatchesVerified + 1 + j)) =
      [wInfo1, wInfo2] ∧
    wEnv.verify ([wInfo1, wInfo2].map (·.commitment)) (wProof [wInfo1, wInfo2]) = true ∧
    wEnv.verify ([wInfo1, wInfo2].map (·.commitment)) [0] = false) ∧
  ∃ s, runCalls wEnv wInit (wRunA.take 8 ++ [.activatePriorityMode]) = some s ∧
    Reach wEnv s ∧ s.hashBreaks = [] ∧ s.settlementLayer = 0 ∧ settlerAllowed s 3 = true ∧
    s.priorityModeActivated = true ∧ wInP.batchNumber = s.totalBatchesCommitted + 1 ∧
    wInP.numberOfLayer2Txs = 0 ∧ wInP.numberOfLayer1Txs ≠ 0

/-- **LEAVING, A FAILED MIGRATION, AND A NEW VALIDATOR.** After the main run, every committed
batch is executed and validator `1` can commit batch 4. `migrateOut 99` succeeds, and while
the settlement layer is `99` that commit fails. After `wAdminRun` (the migration fails, and
the chain type manager removes validator `1` and adds `4`) the settlement layer is `0` again,
the commit of batch 4 by `1` fails and the one by `4` succeeds. -/
def Properties.AdminWitness : Prop :=
  ∃ s, runCalls wEnv wInit wRun = some s ∧
    (step wEnv s (wCommit4 1)).isSome = true ∧
    (∃ s1, step wEnv s (.migrateOut 99) = some s1 ∧ s1.settlementLayer = 99 ∧
      step wEnv s1 (wCommit4 1) = none) ∧
    ∃ s2, runCalls wEnv s wAdminRun = some s2 ∧ Reach wEnv s2 ∧ s2.settlementLayer = 0 ∧
      step wEnv s2 (wCommit4 1) = none ∧
      ∃ s3, step wEnv s2 (wCommit4 4) = some s3 ∧ s3.totalBatchesCommitted = 4

end Contracts.ExecutorFacet
