import EraSpec.Contracts.ExecutorFacet.Specs.Pipeline

/-!
# Properties: the batch pipeline (commit, prove, execute, revert)

Statements about `EraSpec.Contracts.ExecutorFacet.Specs.Pipeline`. Proofs are in
`EraSpec.Contracts.ExecutorFacet.Proofs.Pipeline`.

Every run-level statement quantifies over `Reach env s`: any state an initialized chain can
get to by any interleaving of the model's eight calls (`commit`, `prove`, `execute`, `revert`,
`activatePriorityMode`, `deactivatePriorityMode`, `pushPriorityOp`, `setUpgradeTx`), for an
arbitrary `Env` (hash functions, Merkle functions and verifier). **No statement assumes a
hash is injective.** Where a guarantee rests on `keccak256(abi.encode(StoredBatchInfo))`
binding its preimage, it reads

  `HashBreakLogged env s ∨ …`

and `HashBreakLogged env s` says the run's first logged hash break is a concrete collision:
a `StoredBatchInfo` a caller submitted, different from the one this chain hashed into that
slot, with the same hash. The priority-tree statement uses `MerkleBreakLogged env s` the same
way. With an empty log the left disjunct is false, so the right one holds.

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`;
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

/-- **`_revertBatches(n)` MOVES ONLY COMMITTED AND VERIFIED, DOWN TO `n ≥ EXECUTED`.**
(`Base:317-337`.) If `_revertBatches(n)` succeeds from any state then
`totalBatchesExecuted ≤ n ≤ totalBatchesCommitted`; afterwards the committed count is `n`,
the verified count is `min n` of its old value, and the executed count, the executed log, the
stored batch hashes, the log roots, the interop fee units, the priority tree and the upgrade
transaction hash are unchanged. (The upgrade batch number may be reset; see
`Properties.RevertResetsUpgradeBatchNumber` in `Properties/Checks.lean`.) -/
def Properties.RevertBatchesEffect : Prop :=
  ∀ (s s' : State) (n : Nat), revertBatches s n = some s' →
    s.totalBatchesExecuted ≤ n ∧ n ≤ s.totalBatchesCommitted ∧
    s'.totalBatchesCommitted = n ∧
    s'.totalBatchesVerified = min n s.totalBatchesVerified ∧
    s'.totalBatchesExecuted = s.totalBatchesExecuted ∧
    s'.executed = s.executed ∧
    s'.storedBatchHashes = s.storedBatchHashes ∧
    s'.l2LogsRootHashes = s.l2LogsRootHashes ∧
    s'.interopFeeUnits = s.interopFeeUnits ∧
    s'.ptUnprocessedIndex = s.ptUnprocessedIndex ∧
    s'.ptLeaves = s.ptLeaves ∧
    s'.ptHistoricalRoots = s.ptHistoricalRoots ∧
    s'.l2SystemContractsUpgradeTxHash = s.l2SystemContractsUpgradeTxHash

/-- **WHO CAN REVERT, AND WHEN.** From any state:

* `revertBatchesSharedBridge(n)` succeeds only for a validator or the chain type manager,
  only outside priority mode, only on the settlement layer, and then acts as
  `_revertBatches(n)`;
* `activatePriorityMode` succeeds only outside priority mode and on the settlement layer,
  and then acts as `_revertBatches(totalBatchesExecuted)` with the mode switched on, so it
  leaves `committed = verified = executed`;
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

/-- **EXECUTION IS FINAL.** Across any run from a reachable state: the executed log only
grows at its end, the executed count does not decrease, and `l2LogsRootHashes[n]` is unchanged
for every batch `n` already executed (and for genesis, `n = 0`). No hash premise: this holds
even in a run that logs a hash collision. -/
def Properties.ExecutedIsFinal : Prop :=
  ∀ (env : Env) (s s' : State), Reach env s → Steps env s s' →
    s.executed <+: s'.executed ∧
    s.totalBatchesExecuted ≤ s'.totalBatchesExecuted ∧
    ∀ n ≤ s.totalBatchesExecuted, s'.l2LogsRootHashes n = s.l2LogsRootHashes n

/-- **THE STORED LOG ROOT OF AN EXECUTED BATCH IS THE ONE IT WAS EXECUTED WITH.** In every
reachable state, for every record of the executed log, `l2LogsRootHashes[batchNumber]` is the
record's `l2LogsTreeRoot` (`Ex:103`). No hash premise. Together with
`ExecutedBatchesWereCommittedAndProved` this is the root of the committed and proved batch. -/
def Properties.ExecutedLogRootsRecorded : Prop :=
  ∀ (env : Env) (s : State), Reach env s →
    ∀ r ∈ s.executed, s.l2LogsRootHashes r.info.batchNumber = r.info.l2LogsTreeRoot

/-- **THE STORED HASH OF AN EXECUTED BATCH NEVER CHANGES, OR A COLLISION WAS SUBMITTED.**
Across any run from a reachable state: either the run's first logged hash break is a concrete
collision, or `storedBatchHashes[n]` is unchanged for every batch `n` already executed at the
start (and for genesis). -/
def Properties.ExecutedStoredHashesFinal : Prop :=
  ∀ (env : Env) (s s' : State), Reach env s → Steps env s s' →
    HashBreakLogged env s' ∨
      ∀ n ≤ s.totalBatchesExecuted, s'.storedBatchHashes n = s.storedBatchHashes n

/-- **EVERY EXECUTED BATCH WAS COMMITTED AND COVERED BY AN ACCEPTED PROOF, OR A COLLISION WAS
SUBMITTED.** In every reachable state: either the run's first logged hash break is a concrete
collision, or for every record `r` of the executed log

* `r.info` is the `StoredBatchInfo` this chain built in `_commitOneBatch` for that batch
  number (`preimage`), and its hash is the one stored;
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
either the run's first logged hash break is a concrete collision, or

* for every `n ≤ totalBatchesCommitted`, `storedBatchHashes[n]` is the hash of `preimage n`,
  and `preimage n` carries batch number `n`;
* for every `1 ≤ n ≤ totalBatchesCommitted`, `preimage n` is the `StoredBatchInfo` that
  `_commitOneBatch` builds (`Co:244-259`) from a commit input and the `batchHash` of
  `preimage (n - 1)`: its `commitment` is `_getBatchCommitment` of the previous batch's
  state commitment, so each stored hash commits to its predecessor's state;
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

* (no hash premise) the verifier returned `true` for every logged
  `proveBatchesSharedBridge` call, on the commitments of exactly the batches the call listed;
* either the run's first logged hash break is a concrete collision, or for every batch number
  `n` with `executed < n ≤ verified`, some logged call had the *currently committed* batch
  `preimage n` at position `n`. A proof accepted for a batch that was later reverted and
  re-committed with different contents does not count for the re-committed batch. -/
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
item hashes as its `numberOfLayer1Txs`, with the rolling hash and the dependency-roots hash
recorded in the batch. No hash premise. -/
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
`verified + k ≤ committed`, the verifier accepted their commitments, and the verified count
becomes `verified + k` with the other two counters unchanged. Moreover either the first hash
break logged by then is a concrete collision, or the listed batches are exactly the committed
batches `verified + 1, …, verified + k` (`preimage`), and `_processBatchFrom`,
`_processBatchTo` are `verified + 1`, `verified + k`. -/
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
hash break logged by then is a concrete collision, or the submitted `lastCommittedBatchData`
is the last committed batch (`preimage committed`), the new batch is numbered
`committed + 1` (so are `_processFrom` and `_processTo`), and the slot written is
`storedBatchHashes[committed + 1]`, with the hash of the `StoredBatchInfo` built from the
input, the last committed batch's state commitment and the pending upgrade transaction
hash. -/
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

/-! ## Priority operations -/

/-- **PRIORITY OPERATIONS ARE CONSUMED IN ORDER, BY EXECUTED BATCHES, OR A MERKLE FORGERY WAS
SUBMITTED.** In every reachable state:

* (no premise) the priority tree's `unprocessedIndex` is the total number of item hashes
  carried by the executed batches (`consumed`);
* (no premise) every executed batch carried as many item hashes as its `numberOfLayer1Txs`,
  and their rolling hash is its `priorityOperationsHash`;
* either some logged Merkle break is a concrete forgery (a proof opening a root the tree
  really had to items it does not hold at that index), or the item hashes consumed so far,
  in execution order, are exactly the first `unprocessedIndex` leaves pushed to the tree, in
  push order. -/
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

/-- **A PENDING UPGRADE TRANSACTION IS IN THE FIRST UNEXECUTED BATCH AND NOWHERE ELSE, OR A
COLLISION WAS SUBMITTED.** In every reachable state: either the run's first logged hash break
is a concrete collision, or

* if `l2SystemContractsUpgradeBatchNumber ≠ 0` then the upgrade transaction hash is non-zero,
  that batch number is `executed + 1`, it is committed, and that batch was committed with
  exactly this upgrade transaction hash in its commitment;
* if an upgrade transaction is set and not yet in a batch
  (`l2SystemContractsUpgradeBatchNumber = 0`), no batch is committed beyond the executed
  ones: the next commit must carry it (`Co:105-108`);
* every other committed, unexecuted batch was committed with upgrade transaction hash `0`.

So a chain cannot commit past a pending upgrade transaction without including it, and
includes it in one batch only. This uses the in-tree upgrade engines' "all batches executed"
guard (`Up:115-119`), which `setUpgradeTx` models. -/
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
values with the same `hashStored`: the one a caller submitted and the one this chain hashed
into that slot. (Later entries are not claimed: after a collision the slots no longer track
the ghost preimages.) -/
def Properties.LoggedHashBreaksAreCollisions : Prop :=
  ∀ (env : Env) (s : State), Reach env s →
    (∀ br, s.hashBreaks.head? = some br → br.Genuine env) ∧
    (s.hashBreaks ≠ [] → HashBreakLogged env s)

/-- **EVERY LOGGED MERKLE BREAK IS A REAL FORGERY.** In every reachable state, each entry of
the Merkle-break log is a proof for which `Merkle.calculateRootPaths` returned the root of a
prefix of the tree's leaves, for item hashes that are not the tree's leaves at that index. -/
def Properties.LoggedMerkleBreaksAreForgeries : Prop :=
  ∀ (env : Env) (s : State), Reach env s →
    (∀ br ∈ s.merkleBreaks, br.Genuine env) ∧
    (s.merkleBreaks ≠ [] → MerkleBreakLogged env s)

end Contracts.ExecutorFacet
