import EraSpec.Contracts.ExecutorFacet.Specs.Pipeline

/-!
# Properties: the batch pipeline (commit, prove, execute, revert)

Statements about `EraSpec.Contracts.ExecutorFacet.Specs.Pipeline`. Proofs are in
`EraSpec.Contracts.ExecutorFacet.Proofs.Pipeline`.

Every run-level statement quantifies over `Reach env s`: any state an initialized chain can
get to by any interleaving of the model's eleven calls (`commit`, `prove`, `execute`,
`revert`, `activatePriorityMode`, `deactivatePriorityMode`, `pushPriorityOp`, `setUpgradeTx`,
`setValidator`, `migrateOut`, `migrationFails`), for an arbitrary `Env` (hash functions,
Merkle functions and verifier). A chain that has come back from another settlement layer is
not covered (`Reach`). **No statement assumes a hash is injective.** Where a guarantee rests
on `keccak256(abi.encode(StoredBatchInfo))` binding its preimage, it reads

  `HashBreakLogged env s ∨ …`

and `HashBreakLogged env s` says that the first hash break logged since initialization is a
concrete collision: a `StoredBatchInfo` a caller submitted, different from the one this chain
had hashed into that slot, with the same hash. That break may have been logged at any point
of the run, not necessarily at the batch the statement is about. The priority-tree statement
uses `MerkleBreakLogged env s` the same way. With an empty log the left disjunct is false, so
the right one holds. `Properties/Checks.lean` has a run with empty logs
(`PipelineWitness`), a run in which a submitted collision falsifies the main disjunct of
`ExecutedStoredHashesFinal` (`CollisionRewritesAnExecutedBatch`), and one in which an
accepted Merkle proof for an operation never pushed falsifies that of
`PriorityOpsConsumedInOrder` (`MerkleBreakConsumesAnUnpushedOp`).

Source: era-contracts `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`;
abbreviations as in the Specs file.
-/

namespace Contracts.ExecutorFacet

/-! ## The three counters -/

/-- **EXECUTED ≤ VERIFIED ≤ COMMITTED, ALWAYS.** In every reachable state
`totalBatchesExecuted ≤ totalBatchesVerified ≤ totalBatchesCommitted`. No hash premise. -/
def Properties.CountersOrdered : Prop :=
  ∀ (env : Env) (s : State), Reach env s →
    s.totalBatchesExecuted ≤ s.totalBatchesVerified ∧
    s.totalBatchesVerified ≤ s.totalBatchesCommitted

/-- **ONLY A REVERT LOWERS A COUNTER, AND NEVER THE EXECUTED ONE.** For any state (reachable
or not) and any successful call: the executed count does not decrease; and unless the call is
`revertBatchesSharedBridge` or `activatePriorityMode`, neither the committed nor the verified
count decreases. -/
def Properties.OnlyRevertMovesCountersBack : Prop :=
  ∀ (env : Env) (s s' : State) (c : Call), step env s c = some s' →
    s.totalBatchesExecuted ≤ s'.totalBatchesExecuted ∧
    ((∃ caller n, c = .revert caller n) ∨ c = .activatePriorityMode ∨
      (s.totalBatchesCommitted ≤ s'.totalBatchesCommitted ∧
        s.totalBatchesVerified ≤ s'.totalBatchesVerified))

/-- **`_revertBatches(n)` SUCCEEDS EXACTLY WHEN `executed ≤ n ≤ committed`, AND MOVES ONLY
COMMITTED, VERIFIED AND THE UPGRADE BATCH NUMBER.** (`Base:317-337`.) From any state,
`_revertBatches(n)` succeeds iff `totalBatchesExecuted ≤ n ≤ totalBatchesCommitted`, and its
result is the state with committed count `n`, verified count `min n` of the old one, and
`l2SystemContractsUpgradeBatchNumber` reset to `0` if it was above `n`. Every other field is
unchanged, among them the executed count, the stored batch hashes, the log roots, the
interop fee units, the priority tree, the upgrade transaction hash and the ghost state. Since
the transaction hash is kept, reverting the batch that carried it makes it pending again
(`Co:105-107`; `RevertRecommitWitness` shows the next commit carrying it). -/
def Properties.RevertBatchesEffect : Prop :=
  ∀ (s s' : State) (n : Nat), revertBatches s n = some s' ↔
    (s.totalBatchesExecuted ≤ n ∧ n ≤ s.totalBatchesCommitted ∧
      s' = { s with
        totalBatchesVerified := min n s.totalBatchesVerified
        totalBatchesCommitted := n
        l2SystemContractsUpgradeBatchNumber :=
          if n < s.l2SystemContractsUpgradeBatchNumber then 0
          else s.l2SystemContractsUpgradeBatchNumber })

/-- **WHO CAN REVERT, AND WHEN.** From any state:

* `revertBatchesSharedBridge(n)` succeeds only for a validator or the chain type manager,
  only outside priority mode, only on the settlement layer, and then acts as
  `_revertBatches(n)`;
* `activatePriorityMode` succeeds only outside priority mode and on the settlement layer,
  and then acts as `_revertBatches(totalBatchesExecuted)` with the mode switched on: it
  leaves `committed = executed`, and also `verified = executed` when
  `executed ≤ verified` held before, as in every reachable state (`CountersOrdered`);
* while priority mode is active no call lowers the committed or the verified count. -/
def Properties.RevertEntryPoints : Prop :=
  (∀ (s s' : State) (caller : Addr) (n : Nat),
    revertBatchesSharedBridge s caller n = some s' →
      (s.validators caller = true ∨ caller = s.chainTypeManager) ∧
      s.priorityModeActivated = false ∧ s.settlementLayer = 0 ∧
      revertBatches s n = some s') ∧
  (∀ (s s' : State), activatePriorityMode s = some s' →
      s.priorityModeActivated = false ∧ s.settlementLayer = 0 ∧
      revertBatches { s with priorityModeActivated := true } s.totalBatchesExecuted = some s' ∧
      s'.priorityModeActivated = true ∧
      s'.totalBatchesCommitted = s.totalBatchesExecuted ∧
      (s.totalBatchesExecuted ≤ s.totalBatchesVerified →
        s'.totalBatchesVerified = s.totalBatchesExecuted)) ∧
  (∀ (env : Env) (s s' : State) (c : Call), s.priorityModeActivated = true →
    step env s c = some s' →
      s.totalBatchesCommitted ≤ s'.totalBatchesCommitted ∧
      s.totalBatchesVerified ≤ s'.totalBatchesVerified)

/-- **WHO CAN SETTLE.** From any state, a successful `commitBatchesSharedBridge`,
`proveBatchesSharedBridge` or `executeBatchesSharedBridge` runs on the settlement layer
(`settlementLayer = 0`) and was called by a validator outside priority mode, or by the
permissionless validator in priority mode (`settlerAllowed`, `Base:75-83`). A batch committed
in priority mode has no L2 transactions and at least one priority transaction
(`Co:214-216`). -/
def Properties.OnlySettlersSettle : Prop :=
  (∀ (env : Env) (s s' : State) (c : CommitCall), commit env s c = some s' →
    settlerAllowed s c.caller = true ∧ s.settlementLayer = 0 ∧
    (s.priorityModeActivated = true →
      ∀ b ∈ c.newBatches, b.numberOfLayer2Txs = 0 ∧ b.numberOfLayer1Txs ≠ 0)) ∧
  (∀ (env : Env) (s s' : State) (c : ProveCall), prove env s c = some s' →
    settlerAllowed s c.caller = true ∧ s.settlementLayer = 0) ∧
  (∀ (env : Env) (s s' : State) (c : ExecuteCall), execute env s c = some s' →
    settlerAllowed s c.caller = true ∧ s.settlementLayer = 0)

/-! ## Executed batches -/

/-- **EACH BATCH IS EXECUTED EXACTLY ONCE, IN ORDER.** In every reachable state the batch
numbers of the executed log, in execution order, are exactly `1, 2, …, totalBatchesExecuted`.
So no batch number is executed twice, none is skipped, and the count is the log's length. No
hash premise. -/
def Properties.ExecutedExactlyOnceInOrder : Prop :=
  ∀ (env : Env) (s : State), Reach env s →
    s.executed.map (·.info.batchNumber) = List.range' 1 s.totalBatchesExecuted ∧
    (s.executed.map (·.info.batchNumber)).Nodup ∧
    s.executed.length = s.totalBatchesExecuted ∧
    ∀ n, n ∈ s.executed.map (·.info.batchNumber) ↔ 1 ≤ n ∧ n ≤ s.totalBatchesExecuted

/-- **EXECUTION IS FINAL.** Across any run from a reachable state `s` to `s'`: the executed
log of `s` is a prefix of that of `s'`, the executed count does not decrease, and
`l2LogsRootHashes[n]` is unchanged for every `n ≤ totalBatchesExecuted` of `s` (the batches
already executed, and genesis). No hash premise: this holds even in a run that logs a hash
collision, because the only writer of `l2LogsRootHashes` is `_executeOneBatch`, at a batch
number above the executed count (`Ex:66-68`, `Ex:103`). -/
def Properties.ExecutedIsFinal : Prop :=
  ∀ (env : Env) (s s' : State), Reach env s → Steps env s s' →
    s.executed <+: s'.executed ∧
    s.totalBatchesExecuted ≤ s'.totalBatchesExecuted ∧
    ∀ n ≤ s.totalBatchesExecuted, s'.l2LogsRootHashes n = s.l2LogsRootHashes n

/-- **THE STORED LOG ROOT OF AN EXECUTED BATCH IS THE ONE IT WAS EXECUTED WITH.** In every
reachable state, for every record of the executed log, `l2LogsRootHashes[batchNumber]` is the
record's `l2LogsTreeRoot` (`Ex:103`). No hash premise. Unless a hash break was logged, that
record is the batch's committed `StoredBatchInfo` (`ExecutedBatchesWereCommittedAndProved`),
whose `l2LogsTreeRoot` is the commit input's (`Co:250`). -/
def Properties.ExecutedLogRootsRecorded : Prop :=
  ∀ (env : Env) (s : State), Reach env s →
    ∀ r ∈ s.executed, s.l2LogsRootHashes r.info.batchNumber = r.info.l2LogsTreeRoot

/-- **THE STORED HASH OF AN EXECUTED BATCH NEVER CHANGES, OR A COLLISION WAS SUBMITTED.**
Across any run from a reachable state `s` to `s'`: either the first hash break logged since
initialization (possibly before `s`) is a concrete collision, or `storedBatchHashes[n]` is
unchanged for every `n ≤ totalBatchesExecuted` of `s` (the batches already executed, and
genesis). The collision disjunct is needed: `CollisionRewritesAnExecutedBatch`. -/
def Properties.ExecutedStoredHashesFinal : Prop :=
  ∀ (env : Env) (s s' : State), Reach env s → Steps env s s' →
    HashBreakLogged env s' ∨
      ∀ n ≤ s.totalBatchesExecuted, s'.storedBatchHashes n = s.storedBatchHashes n

/-- **EVERY EXECUTED BATCH WAS COMMITTED AND COVERED BY AN ACCEPTED PROOF, OR A COLLISION WAS
SUBMITTED.** In every reachable state: either the first hash break logged since
initialization is a concrete collision, or for every record `r` of the executed log

* `r.info` is `preimage` of its batch number, the `StoredBatchInfo` this chain built in
  `_commitOneBatch` for that batch (`StoredHashesChain`), and its hash is the one stored;
* some accepted `proveBatchesSharedBridge` call had `r.info` at the position of that batch
  number (`ProvedAt`).

`VerifiedBatchesHaveAcceptedProofs` says the verifier returned `true` for each such call. -/
def Properties.ExecutedBatchesWereCommittedAndProved : Prop :=
  ∀ (env : Env) (s : State), Reach env s → HashBreakLogged env s ∨
    ∀ r ∈ s.executed, r.info = s.preimage r.info.batchNumber ∧
      s.storedBatchHashes r.info.batchNumber = env.hashStored r.info ∧
      ProvedAt s r.info.batchNumber r.info

/-! ## Committed and verified batches -/

/-- **STORED BATCH HASHES CHAIN, OR A COLLISION WAS SUBMITTED.** In every reachable state:
either the first hash break logged since initialization is a concrete collision, or

* for every `n ≤ totalBatchesCommitted`, `storedBatchHashes[n]` is the hash of `preimage n`,
  and `preimage n` carries batch number `n`;
* for every `1 ≤ n ≤ totalBatchesCommitted`, `preimage n` is the `StoredBatchInfo` that
  `_commitOneBatch` builds (`Co:244-259`) from a commit input and the `batchHash` of
  `preimage (n - 1)`: its `commitment` is `Env.batchCommitment` of the previous batch's state
  commitment, the input and the upgrade transaction hash used for it;
* `interopFeeUnits[n]` is that commit input's `interopFeeUnits` (`Co:140`), including after
  a revert and re-commit.

This describes the batches currently committed: after a revert and re-commit, the batch
re-committed. -/
def Properties.StoredHashesChain : Prop :=
  ∀ (env : Env) (s : State), Reach env s → HashBreakLogged env s ∨
    ((∀ n ≤ s.totalBatchesCommitted,
        s.storedBatchHashes n = env.hashStored (s.preimage n) ∧
        (s.preimage n).batchNumber = n) ∧
      ∀ n, 1 ≤ n → n ≤ s.totalBatchesCommitted → ∃ a, s.commitArgs n = some a ∧
        a.prevBatchHash = (s.preimage (n - 1)).batchHash ∧
        s.preimage n = storedInfoOf env a ∧
        s.interopFeeUnits n = a.input.interopFeeUnits)

/-- **EVERY VERIFIED BATCH HAS AN ACCEPTED PROOF FOR ITS CURRENT CONTENTS.** In every
reachable state:

* (no hash premise) `Env.verify` returned `true` for every logged
  `proveBatchesSharedBridge` call, on the commitments of exactly the batches the call listed;
* either the first hash break logged since initialization is a concrete collision, or for
  every batch number `n` with `executed < n ≤ verified`, some logged call had the *currently
  committed* batch `preimage n` at position `n`. A proof accepted for a batch that was later
  reverted and re-committed with different contents does not count for the re-committed
  batch (`RevertRecommitWitness`). -/
def Properties.VerifiedBatchesHaveAcceptedProofs : Prop :=
  ∀ (env : Env) (s : State), Reach env s →
    (∀ call ∈ s.verified, env.verify (call.batches.map (·.commitment)) call.proof = true) ∧
    (HashBreakLogged env s ∨
      ∀ n, s.totalBatchesExecuted < n → n ≤ s.totalBatchesVerified →
        ProvedAt s n (s.preimage n))

/-! ## What each call processes -/

/-- **`executeBatchesSharedBridge` EXECUTES EXACTLY THE NEXT BATCHES.** From any state, a
successful call lists at least one batch; their numbers are
`executed + 1, …, executed + k` in order, `_processFrom` and `_processTo` are the first and
last of these, `executed + k ≤ verified` held before the call, the executed count becomes
`executed + k`, the verified and committed counts are unchanged, and the executed log gains
exactly one record per listed batch, in order. Each listed batch carried as many priority-op
item hashes as its `numberOfLayer1Txs`, their rolling hash is its `priorityOperationsHash`,
and the dependency-roots check returned its `dependencyRootsRollingHash`. No hash premise. -/
def Properties.ExecuteTakesTheNextBatches : Prop :=
  ∀ (env : Env) (s s' : State) (c : ExecuteCall), execute env s c = some s' →
    c.batches ≠ [] ∧
    c.processFrom = s.totalBatchesExecuted + 1 ∧
    c.processTo = s.totalBatchesExecuted + c.batches.length ∧
    c.batches.map (·.info.batchNumber) =
      List.range' (s.totalBatchesExecuted + 1) c.batches.length ∧
    s'.totalBatchesExecuted = s.totalBatchesExecuted + c.batches.length ∧
    s.totalBatchesExecuted + c.batches.length ≤ s.totalBatchesVerified ∧
    s'.totalBatchesVerified = s.totalBatchesVerified ∧
    s'.totalBatchesCommitted = s.totalBatchesCommitted ∧
    s'.executed = s.executed ++ c.batches.map ExecBatch.record ∧
    (∀ b ∈ c.batches, b.ops.itemHashes.length = b.info.numberOfLayer1Txs ∧
      env.rollingHash b.ops.itemHashes = b.info.priorityOperationsHash ∧
      b.depRootsHash = some b.info.dependencyRootsRollingHash)

/-- **`proveBatchesSharedBridge` VERIFIES EXACTLY THE NEXT COMMITTED BATCHES, OR A COLLISION
WAS SUBMITTED.** From a reachable state, a successful call lists `k ≥ 1` batches with
`verified + k ≤ committed`, `Env.verify` accepted their commitments, and the verified count
becomes `verified + k` with the other two counters unchanged. Moreover either the first hash
break logged since initialization, up to and including this call, is a concrete collision,
or the listed batches are exactly the committed batches `verified + 1, …, verified + k`
(`preimage`), and `_processBatchFrom`, `_processBatchTo` are `verified + 1`,
`verified + k`. -/
def Properties.ProveTakesTheNextBatches : Prop :=
  ∀ (env : Env) (s s' : State) (c : ProveCall), Reach env s → prove env s c = some s' →
    c.batches ≠ [] ∧
    s.totalBatchesVerified + c.batches.length ≤ s.totalBatchesCommitted ∧
    env.verify (c.batches.map (·.commitment)) c.proof = true ∧
    s'.totalBatchesVerified = s.totalBatchesVerified + c.batches.length ∧
    s'.totalBatchesCommitted = s.totalBatchesCommitted ∧
    s'.totalBatchesExecuted = s.totalBatchesExecuted ∧
    (HashBreakLogged env s' ∨
      ((∀ j b, c.batches[j]? = some b → b = s.preimage (s.totalBatchesVerified + 1 + j)) ∧
        c.processFrom = s.totalBatchesVerified + 1 ∧
        c.processTo = s.totalBatchesVerified + c.batches.length))

/-- **`commitBatchesSharedBridge` COMMITS EXACTLY THE NEXT BATCH, OR A COLLISION WAS
SUBMITTED.** From a reachable state, a successful call carries exactly one batch and raises
the committed count by one, leaving the other two counters alone. Moreover either the first
hash break logged since initialization, up to and including this call, is a concrete
collision, or the submitted `lastCommittedBatchData` is the last committed batch
(`preimage committed`), the new batch is numbered `committed + 1` (so are `_processFrom` and
`_processTo`), the ghost `commitArgs` of that number records the input and the last
committed batch's state commitment, and `storedBatchHashes[committed + 1]` then holds the
hash of the `StoredBatchInfo` built from them and the upgrade transaction hash used. -/
def Properties.CommitTakesTheNextBatch : Prop :=
  ∀ (env : Env) (s s' : State) (c : CommitCall), Reach env s → commit env s c = some s' →
    ∃ b, c.newBatches = [b] ∧
      s'.totalBatchesCommitted = s.totalBatchesCommitted + 1 ∧
      s'.totalBatchesVerified = s.totalBatchesVerified ∧
      s'.totalBatchesExecuted = s.totalBatchesExecuted ∧
      (HashBreakLogged env s' ∨
        (c.lastCommitted = s.preimage s.totalBatchesCommitted ∧
          b.batchNumber = s.totalBatchesCommitted + 1 ∧
          c.processFrom = s.totalBatchesCommitted + 1 ∧
          c.processTo = s.totalBatchesCommitted + 1 ∧
          ∃ a, s'.commitArgs (s.totalBatchesCommitted + 1) = some a ∧ a.input = b ∧
            a.prevBatchHash = (s.preimage s.totalBatchesCommitted).batchHash ∧
            s'.storedBatchHashes (s.totalBatchesCommitted + 1) =
              env.hashStored (storedInfoOf env a)))

/-! ## Honest progress -/

/-- **AN HONEST COMMIT IS ALWAYS ENABLED.** From any reachable state with no hash break
logged, on the settlement layer, any caller `settlerAllowed` admits can commit any batch
numbered `committed + 1` on top of the last committed batch (`preimage committed`), with
`_processFrom = _processTo` its number; in priority mode the batch must have no L2
transactions and at least one priority transaction. The checks the model omits (Specs header)
can still reject such a call in the source. -/
def Properties.HonestCommitEnabled : Prop :=
  ∀ (env : Env) (s : State) (caller : Addr) (b : CommitBatchInfo), Reach env s →
    s.hashBreaks = [] → s.settlementLayer = 0 → settlerAllowed s caller = true →
    b.batchNumber = s.totalBatchesCommitted + 1 →
    (s.priorityModeActivated = true → b.numberOfLayer2Txs = 0 ∧ b.numberOfLayer1Txs ≠ 0) →
    (commit env s ⟨caller, b.batchNumber, b.batchNumber,
      s.preimage s.totalBatchesCommitted, [b]⟩).isSome = true

/-- **AN HONEST PROOF IS ENABLED EXACTLY WHEN THE VERIFIER ACCEPTS IT.** From any reachable
state with no hash break logged, on the settlement layer, for any caller `settlerAllowed`
admits and any `k ≥ 1` with `verified + k ≤ committed`: the call proving the committed batches
`verified + 1, …, verified + k` (`preimage`) on top of `preimage verified`, with
`_processBatchFrom = verified + 1` and `_processBatchTo = verified + k`, succeeds exactly when
`Env.verify` accepts their commitments with the given proof. -/
def Properties.HonestProveEnabledIff : Prop :=
  ∀ (env : Env) (s : State) (caller : Addr) (k : Nat) (proof : List Nat), Reach env s →
    s.hashBreaks = [] → s.settlementLayer = 0 → settlerAllowed s caller = true →
    1 ≤ k → s.totalBatchesVerified + k ≤ s.totalBatchesCommitted →
    (prove env s ⟨caller, s.totalBatchesVerified + 1, s.totalBatchesVerified + k,
        s.preimage s.totalBatchesVerified,
        (List.range k).map (fun j => s.preimage (s.totalBatchesVerified + 1 + j)),
        proof⟩).isSome =
      env.verify (((List.range k).map
        (fun j => s.preimage (s.totalBatchesVerified + 1 + j))).map (·.commitment)) proof

/-! ## Priority operations -/

/-- **PRIORITY OPERATIONS ARE CONSUMED IN ORDER, BY EXECUTED BATCHES, OR A MERKLE BREAK WAS
LOGGED.** In every reachable state:

* (no premise) the priority tree's `unprocessedIndex` is the total number of item hashes
  carried by the executed batches (`consumed`);
* (no premise) every executed batch carried as many item hashes as its `numberOfLayer1Txs`,
  and their rolling hash is its `priorityOperationsHash`;
* either some logged Merkle break is genuine (`processBatch` accepted a proof that opened a
  root the tree had held, that of a prefix of its leaves, for item hashes that are not the
  tree's current leaves at that index), or the item hashes consumed so far, in execution
  order, are exactly the first `unprocessedIndex` leaves pushed to the tree, in push order.

The statement does not say what producing a genuine Merkle break takes for the real tree;
`processBatch` leaves the validity of the item hashes to the validity proof (`PT:77-82`).
`MerkleBreakConsumesAnUnpushedOp` shows the break disjunct is needed. -/
def Properties.PriorityOpsConsumedInOrder : Prop :=
  ∀ (env : Env) (s : State), Reach env s →
    s.ptUnprocessedIndex = (consumed s).length ∧
    (∀ r ∈ s.executed, r.items.length = r.info.numberOfLayer1Txs ∧
      env.rollingHash r.items = r.info.priorityOperationsHash) ∧
    (MerkleBreakLogged env s ∨
      (s.ptUnprocessedIndex ≤ s.ptLeaves.length ∧
        consumed s = s.ptLeaves.take s.ptUnprocessedIndex))

/-- **ONLY `executeBatchesSharedBridge` CONSUMES PRIORITY OPERATIONS, AND NOTHING RETURNS
THEM.** For any state and any successful call: `unprocessedIndex` does not decrease (a revert
of batches never un-consumes a priority operation); if it changes, the call is an execute;
and an execute raises it by the sum of the executed batches' `numberOfLayer1Txs`. -/
def Properties.PriorityOpsConsumedOnlyByExecute : Prop :=
  ∀ (env : Env) (s s' : State) (c : Call), step env s c = some s' →
    s.ptUnprocessedIndex ≤ s'.ptUnprocessedIndex ∧
    (s'.ptUnprocessedIndex ≠ s.ptUnprocessedIndex → ∃ ec, c = .execute ec) ∧
    (∀ ec, c = .execute ec → s'.ptUnprocessedIndex =
      s.ptUnprocessedIndex + (ec.batches.map (·.info.numberOfLayer1Txs)).sum)

/-! ## The upgrade transaction -/

/-- **A PENDING UPGRADE TRANSACTION IS IN THE FIRST UNEXECUTED BATCH AND NO OTHER UNEXECUTED
ONE, OR A COLLISION WAS SUBMITTED.** In every reachable state: either the first hash break
logged since initialization is a concrete collision, or

* if `l2SystemContractsUpgradeBatchNumber ≠ 0` then the upgrade transaction hash is non-zero,
  that batch number is `executed + 1`, it is committed, and that batch was committed with
  exactly this hash as the upgrade transaction hash of its commitment
  (`_getBatchOutputHash`, `Co:306`);
* if an upgrade transaction is set and not yet in a batch
  (`l2SystemContractsUpgradeBatchNumber = 0`), no batch is committed beyond the executed
  ones, so the next commit carries it (`Co:105-108`);
* every other committed, unexecuted batch was committed with upgrade transaction hash `0`.

So a chain cannot commit past a pending upgrade transaction without including it, and among
the committed batches not yet executed only one carries it. This rests on the in-tree upgrade
engines' "all batches executed" guard (`Up:115-119`), which `setUpgradeTx` models; without it
the transaction lands in a later batch (`UpgradeWithoutExecutedCheckSkipsABatch`). -/
def Properties.UpgradeTxInFirstUnexecutedBatch : Prop :=
  ∀ (env : Env) (s : State), Reach env s → HashBreakLogged env s ∨
    ((s.l2SystemContractsUpgradeBatchNumber ≠ 0 →
        s.l2SystemContractsUpgradeTxHash ≠ 0 ∧
        s.l2SystemContractsUpgradeBatchNumber = s.totalBatchesExecuted + 1 ∧
        s.l2SystemContractsUpgradeBatchNumber ≤ s.totalBatchesCommitted ∧
        ∃ a, s.commitArgs s.l2SystemContractsUpgradeBatchNumber = some a ∧
          a.upgradeTxHash = s.l2SystemContractsUpgradeTxHash) ∧
      (s.l2SystemContractsUpgradeTxHash ≠ 0 → s.l2SystemContractsUpgradeBatchNumber = 0 →
        s.totalBatchesCommitted = s.totalBatchesExecuted) ∧
      (∀ n, s.totalBatchesExecuted < n → n ≤ s.totalBatchesCommitted →
        n ≠ s.l2SystemContractsUpgradeBatchNumber → ∀ a, s.commitArgs n = some a →
        a.upgradeTxHash = 0))

/-! ## The break logs -/

/-- **THE FIRST LOGGED HASH BREAK IS A REAL COLLISION.** In every reachable state, if the
hash-break log is non-empty then its first entry is a pair of different `StoredBatchInfo`
values with the same `hashStored`: the one a caller submitted and the one this chain had
hashed into that slot. (Later entries are not claimed: after a collision the slots no longer
track the ghost preimages.) -/
def Properties.LoggedHashBreaksAreCollisions : Prop :=
  ∀ (env : Env) (s : State), Reach env s →
    (∀ br, s.hashBreaks.head? = some br → br.Genuine env) ∧
    (s.hashBreaks ≠ [] → HashBreakLogged env s)

/-- **EVERY LOGGED MERKLE BREAK OPENED A ROOT THE TREE HAD HELD.** In every reachable state,
each entry of the Merkle-break log is a proof for which `Merkle.calculateRootPaths` returned
the root of a prefix of the tree's leaves, for item hashes that are not the tree's current
leaves at that index: an inclusion proof for operations that are not the pushed ones. What
such a proof takes for the real tree is not modelled (Specs header). -/
def Properties.LoggedMerkleBreaksAreForgeries : Prop :=
  ∀ (env : Env) (s : State), Reach env s →
    (∀ br ∈ s.merkleBreaks, br.Genuine env) ∧
    (s.merkleBreaks ≠ [] → MerkleBreakLogged env s)

end Contracts.ExecutorFacet
