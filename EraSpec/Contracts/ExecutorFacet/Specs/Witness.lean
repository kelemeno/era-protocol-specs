import EraSpec.Contracts.ExecutorFacet.Specs.Pipeline

/-!
# Concrete environments and runs for `Properties/Checks.lean`

Definitions only. A toy `Env` (`wEnv`) whose stored-batch hash is injective on the values
used here, a fresh chain (`wInitOf`), and the call lists that the witnesses and
countermodels of `Checks` run. Two variants of `wEnv` are deliberately weak: `wCollEnv`
ignores the batch number when hashing a `StoredBatchInfo`, and `wMerkleEnv` opens the empty
tree's root for every priority-op proof.

Addresses: `1` is a validator, `2` the chain type manager, `3` the permissionless validator,
`4` an address that becomes a validator in `wAdminRun`. Priority operations are `11`, `12`,
`13`. The L2 upgrade transaction hash is `9`.
-/

namespace Contracts.ExecutorFacet

/-- `2^28`, the field width of the toy stored-batch hash. -/
def wBase : Nat := 268435456

/-- A toy `hashStoredBatchInfo`: the nine fields written in base `2^28`. Injective on values
whose fields are below `2^28`, as all values in these runs are. -/
def wHashStored (b : StoredBatchInfo) : Word :=
  (((((((((b.batchNumber * wBase + b.batchHash.val) * wBase + b.indexRepeatedStorageChanges)
    * wBase + b.numberOfLayer1Txs) * wBase + b.priorityOperationsHash.val) * wBase
    + b.dependencyRootsRollingHash.val) * wBase + b.l2LogsTreeRoot.val) * wBase
    + b.timestamp) * wBase + b.commitment.val : Nat) : Word)

/-- A toy rolling hash of priority-op item hashes. -/
def wRollingHash (items : List Word) : Word :=
  ((items.foldl (fun acc x => acc * 31 + x.val) 7 % wBase : Nat) : Word)

/-- A toy root of the priority tree with these leaves. -/
def wTreeRoot (leaves : List Word) : Word :=
  ((leaves.foldl (fun acc x => acc * 37 + x.val) 3 % wBase : Nat) : Word)

/-- The toy environment. A priority-op proof is its left and right sibling leaves:
`calculateRootPaths` is the root of `left ++ items ++ right`. The verifier accepts exactly
the proof that lists the commitments of the batches. -/
def wEnv : Env where
  hashStored := wHashStored
  hashLegacy := fun b => wHashStored b + 1
  batchCommitment := fun prev b up =>
    ((prev.val * 1000 + b.newStateCommitment.val * 10 + up.val) % wBase : Nat)
  verify := fun inputs proof => decide (proof = inputs.map (·.val))
  rollingHash := wRollingHash
  treeRoot := wTreeRoot
  calculateRootPaths := fun left right _ items => wTreeRoot (left ++ items ++ right)

/-- `wEnv` with a stored-batch hash that ignores the batch number. -/
def wCollEnv : Env := { wEnv with hashStored := fun b => wHashStored { b with batchNumber := 0 } }

/-- `wEnv` where every priority-op proof opens the empty tree's root. -/
def wMerkleEnv : Env := { wEnv with calculateRootPaths := fun _ _ _ _ => wTreeRoot [] }

/-- The genesis batch, numbered `0`. -/
def wGenesis : StoredBatchInfo := ⟨0, 5, 0, 0, 0, 0, 0, 0, 0⟩

/-- A fresh chain for `env`: no batches, the genesis hash in slot `0`, an empty priority tree,
validator `1`, chain type manager `2`, permissionless validator `3`. -/
def wInitOf (env : Env) : State where
  validators := fun a => decide (a = 1)
  chainTypeManager := 2
  settlementLayer := 0
  priorityModeActivated := false
  permissionlessValidator := 3
  totalBatchesExecuted := 0
  totalBatchesVerified := 0
  totalBatchesCommitted := 0
  storedBatchHashes := fun n => if n = 0 then env.hashStored wGenesis else 0
  l2LogsRootHashes := fun _ => 0
  interopFeeUnits := fun _ => 0
  l2SystemContractsUpgradeTxHash := 0
  l2SystemContractsUpgradeBatchNumber := 0
  ptUnprocessedIndex := 0
  ptLeaves := []
  ptHistoricalRoots := fun r => decide (r = env.treeRoot [])
  preimage := fun _ => wGenesis
  commitArgs := fun _ => none
  executed := []
  verified := []
  hashBreaks := []
  merkleBreaks := []

/-- The fresh chain for `wEnv`. -/
def wInit : State := wInitOf wEnv

/-- The proof `wEnv.verify` accepts for these batches. -/
def wProof (bs : List StoredBatchInfo) : List Nat := bs.map (·.commitment.val)

/-! ## The main run: three batches, two priority-op batches, an upgrade transaction -/

/-- Batch 1: two priority operations (`11`, `12`) and four L2 transactions. -/
def wIn1 : CommitBatchInfo :=
  { batchNumber := 1, newStateCommitment := 21, numberOfLayer1Txs := 2, numberOfLayer2Txs := 4,
    priorityOperationsHash := wRollingHash [11, 12], dependencyRootsRollingHash := 0,
    l2LogsTreeRoot := 31, interopFeeUnits := 6 }

/-- Batch 2: no priority operations. -/
def wIn2 : CommitBatchInfo :=
  { batchNumber := 2, newStateCommitment := 22, numberOfLayer1Txs := 0, numberOfLayer2Txs := 3,
    priorityOperationsHash := wRollingHash [], dependencyRootsRollingHash := 0,
    l2LogsTreeRoot := 32, interopFeeUnits := 5 }

/-- Batch 3: priority operation `13` and a non-zero dependency-roots hash. -/
def wIn3 : CommitBatchInfo :=
  { batchNumber := 3, newStateCommitment := 23, numberOfLayer1Txs := 1, numberOfLayer2Txs := 2,
    priorityOperationsHash := wRollingHash [13], dependencyRootsRollingHash := 41,
    l2LogsTreeRoot := 33, interopFeeUnits := 2 }

/-- The stored batch 1, committed with upgrade transaction `9`. -/
def wInfo1 : StoredBatchInfo := storedInfoOf wEnv ⟨5, wIn1, 9⟩
/-- The stored batch 2. -/
def wInfo2 : StoredBatchInfo := storedInfoOf wEnv ⟨21, wIn2, 0⟩
/-- The stored batch 3. -/
def wInfo3 : StoredBatchInfo := storedInfoOf wEnv ⟨22, wIn3, 0⟩

/-- The first part of the main run: the genesis upgrade sets transaction `9`; two priority
operations; three commits (batch 1 carries the transaction); one more priority operation;
one proof of batches 1 and 2; execution of batch 1 with its two priority operations. -/
def wRunA : List Call :=
  [ .setUpgradeTx 9,
    .pushPriorityOp 11,
    .pushPriorityOp 12,
    .commit ⟨1, 1, 1, wGenesis, [wIn1]⟩,
    .commit ⟨1, 2, 2, wInfo1, [wIn2]⟩,
    .pushPriorityOp 13,
    .commit ⟨1, 3, 3, wInfo2, [wIn3]⟩,
    .prove ⟨1, 1, 2, wGenesis, [wInfo1, wInfo2], wProof [wInfo1, wInfo2]⟩,
    .execute ⟨1, 1, 1, [⟨wInfo1, ⟨[], [13], [11, 12]⟩, some 0⟩]⟩ ]

/-- The rest of the main run: a proof of batch 3, then execution of batches 2 and 3. -/
def wRunB : List Call :=
  [ .prove ⟨1, 3, 3, wInfo2, [wInfo3], wProof [wInfo3]⟩,
    .execute ⟨1, 2, 3, [⟨wInfo2, ⟨[], [], []⟩, some 0⟩, ⟨wInfo3, ⟨[11, 12], [], [13]⟩, some 41⟩]⟩ ]

/-- The main run. -/
def wRun : List Call := wRunA ++ wRunB

/-! ## Revert and re-commit -/

/-- Batch 1 again, with a different state commitment and no interop fee units. -/
def wIn1' : CommitBatchInfo := { wIn1 with newStateCommitment := 51, interopFeeUnits := 0 }

/-- The re-committed batch 1, which carries upgrade transaction `9` again. -/
def wInfo1' : StoredBatchInfo := storedInfoOf wEnv ⟨5, wIn1', 9⟩

/-- The main run up to the proof of batches 1 and 2, then a validator's revert to batch 0 and
a re-commit of batch 1 with other contents. -/
def wRecommitRun : List Call :=
  wRunA.take 8 ++ [.revert 1 0, .commit ⟨1, 1, 1, wGenesis, [wIn1']⟩]

/-! ## Priority mode -/

/-- Batch 1 with priority transactions only. -/
def wInP : CommitBatchInfo := { wIn1 with numberOfLayer2Txs := 0 }

/-- The stored priority-only batch 1, carrying upgrade transaction `9`. -/
def wInfoP : StoredBatchInfo := storedInfoOf wEnv ⟨5, wInP, 9⟩

/-- After `activatePriorityMode`: the permissionless validator commits, proves and executes
the priority-only batch 1; then the chain type manager deactivates priority mode. -/
def wPriorityTail : List Call :=
  [ .commit ⟨3, 1, 1, wGenesis, [wInP]⟩,
    .prove ⟨3, 1, 1, wGenesis, [wInfoP], wProof [wInfoP]⟩,
    .execute ⟨3, 1, 1, [⟨wInfoP, ⟨[], [13], [11, 12]⟩, some 0⟩]⟩,
    .deactivatePriorityMode 2 ]

/-! ## Validators and the settlement layer -/

/-- Batch 4: no priority operations. -/
def wIn4 : CommitBatchInfo :=
  { batchNumber := 4, newStateCommitment := 24, numberOfLayer1Txs := 0, numberOfLayer2Txs := 1,
    priorityOperationsHash := wRollingHash [], dependencyRootsRollingHash := 0,
    l2LogsTreeRoot := 34, interopFeeUnits := 0 }

/-- The commit of batch 4 by `caller`. -/
def wCommit4 (caller : Addr) : Call := .commit ⟨caller, 4, 4, wInfo3, [wIn4]⟩

/-- After the main run: the chain starts a migration to settlement layer `99`, the migration
fails, and the chain type manager replaces validator `1` by validator `4`. -/
def wAdminRun : List Call :=
  [ .migrateOut 99, .migrationFails, .setValidator 2 1 false, .setValidator 2 4 true ]

/-! ## Runs for the ablated checks -/

/-- Batch 1 without priority operations, committed with no upgrade transaction pending. -/
def wInPlain1 : CommitBatchInfo :=
  { batchNumber := 1, newStateCommitment := 21, numberOfLayer1Txs := 0, numberOfLayer2Txs := 4,
    priorityOperationsHash := wRollingHash [], dependencyRootsRollingHash := 0,
    l2LogsTreeRoot := 31, interopFeeUnits := 6 }

/-- `wInPlain1` with another state commitment. -/
def wInPlain1' : CommitBatchInfo := { wInPlain1 with newStateCommitment := 51 }

/-- Batch 2 after `wInPlain1`. -/
def wInPlain2 : CommitBatchInfo :=
  { batchNumber := 2, newStateCommitment := 22, numberOfLayer1Txs := 0, numberOfLayer2Txs := 3,
    priorityOperationsHash := wRollingHash [], dependencyRootsRollingHash := 0,
    l2LogsTreeRoot := 32, interopFeeUnits := 0 }

/-- The stored `wInPlain1`. -/
def wPlain1 : StoredBatchInfo := storedInfoOf wEnv ⟨5, wInPlain1, 0⟩

/-- Commit batch 1, revert it, then prove it from its stale stored hash. -/
def wStaleProveRun : List Call :=
  [ .commit ⟨1, 1, 1, wGenesis, [wInPlain1]⟩,
    .revert 1 0,
    .prove ⟨1, 1, 1, wGenesis, [wPlain1], wProof [wPlain1]⟩ ]

/-- Commit batch 1, then execute it without a proof. -/
def wUnprovenExecRun : List Call :=
  [ .commit ⟨1, 1, 1, wGenesis, [wInPlain1]⟩,
    .execute ⟨1, 1, 1, [⟨wPlain1, ⟨[], [], []⟩, some 0⟩]⟩ ]

/-- Commit, prove and execute batch 1, revert to batch 0, commit batch 1 again with other
contents. -/
def wRevertExecutedRun : List Call :=
  [ .commit ⟨1, 1, 1, wGenesis, [wInPlain1]⟩,
    .prove ⟨1, 1, 1, wGenesis, [wPlain1], wProof [wPlain1]⟩,
    .execute ⟨1, 1, 1, [⟨wPlain1, ⟨[], [], []⟩, some 0⟩]⟩,
    .revert 1 0,
    .commit ⟨1, 1, 1, wGenesis, [wInPlain1']⟩ ]

/-- Commit batch 1, run an upgrade that sets transaction `9` while batch 1 is unexecuted,
commit batch 2. -/
def wEarlyUpgradeRun : List Call :=
  [ .commit ⟨1, 1, 1, wGenesis, [wInPlain1]⟩,
    .setUpgradeTx 9,
    .commit ⟨1, 2, 2, wPlain1, [wInPlain2]⟩ ]

/-! ## Runs that log a break -/

/-- Commit, prove and execute batch 1 under `wCollEnv`. -/
def wCollRun : List Call :=
  [ .commit ⟨1, 1, 1, wGenesis, [wInPlain1]⟩,
    .prove ⟨1, 1, 1, wGenesis, [wPlain1], wProof [wPlain1]⟩,
    .execute ⟨1, 1, 1, [⟨wPlain1, ⟨[], [], []⟩, some 0⟩]⟩ ]

/-- Then a commit whose `lastCommittedBatchData` is batch 1 renumbered `0`: under `wCollEnv`
it hashes like batch 1, so it passes the check against slot `1`, and the new batch 1 is
written over the executed one. -/
def wCollCommit : Call := .commit ⟨1, 1, 1, { wPlain1 with batchNumber := 0 }, [wInPlain1']⟩

/-- Batch 1 with one priority operation `77`, never pushed. -/
def wInM1 : CommitBatchInfo :=
  { batchNumber := 1, newStateCommitment := 21, numberOfLayer1Txs := 1, numberOfLayer2Txs := 0,
    priorityOperationsHash := wRollingHash [77], dependencyRootsRollingHash := 0,
    l2LogsTreeRoot := 31, interopFeeUnits := 0 }

/-- The stored `wInM1`. -/
def wM1 : StoredBatchInfo := storedInfoOf wMerkleEnv ⟨5, wInM1, 0⟩

/-- Under `wMerkleEnv`, with an empty priority tree: commit, prove and execute batch 1,
consuming operation `77` with a proof against the empty tree's root. -/
def wMerkleRun : List Call :=
  [ .commit ⟨1, 1, 1, wGenesis, [wInM1]⟩,
    .prove ⟨1, 1, 1, wGenesis, [wM1], wProof [wM1]⟩,
    .execute ⟨1, 1, 1, [⟨wM1, ⟨[], [], [77]⟩, some 0⟩]⟩ ]

end Contracts.ExecutorFacet
