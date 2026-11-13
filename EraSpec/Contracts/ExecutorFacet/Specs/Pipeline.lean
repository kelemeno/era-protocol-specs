import EraSpec.Core.Word

/-!
# Model: the batch pipeline of a ZK chain (commit, prove, execute, revert)

Source: era-contracts `draft/v0.35.0` at commit
`d9f678900e1bc8286412b78f56d4a9f443983c29`. Paths are relative to `l1-contracts/contracts/`;
every `file:line` below is at that commit. Abbreviations:

* `Ex` = `state-transition/chain-deps/facets/Executor.sol`
* `Co` = `state-transition/chain-deps/facets/Committer.sol`
* `Base` = `state-transition/chain-deps/facets/ZKChainBase.sol`
* `Hash` = `state-transition/chain-deps/StoredBatchHashing.sol`
* `Sto` = `state-transition/chain-deps/ZKChainStorage.sol`
* `PT` = `state-transition/libraries/PriorityTree.sol`
* `BD` = `state-transition/libraries/BatchDecoder.sol`
* `Adm` = `state-transition/chain-deps/facets/Admin.sol`
* `Up` = `upgrades/BaseZkSyncUpgrade.sol`

**This file is definitions only.** The guarantees are stated in
`EraSpec.Contracts.ExecutorFacet.Properties.Pipeline` and
`EraSpec.Contracts.ExecutorFacet.Properties.Checks`, and proved in the matching `Proofs`
modules. The concrete runs used by `Checks` are in `Specs/Witness.lean`.

## What is modelled

One chain's diamond storage, as far as the batch pipeline reads or writes it, and every
entry point that writes the pipeline's counters, its stored batch hashes, its upgrade
bookkeeping or its priority tree:

| step | source |
|---|---|
| `commit` | `commitBatchesSharedBridge` (`Co:72-111`), `_commitBatches` and `_commitOneBatch` (`Co:113-283`) |
| `prove` | `proveBatchesSharedBridge` (`Ex:215-251`) |
| `execute` | `executeBatchesSharedBridge` (`Ex:170-212`), `_executeOneBatch` (`Ex:86-114`), `_checkBatchData` (`Ex:59-79`) |
| `revert` | `revertBatchesSharedBridge` (`Ex:264-269`) and `_revertBatches` (`Base:317-337`) |
| `activatePriorityMode` | `Adm:523-552`, which calls `_revertBatches(totalBatchesExecuted)` |
| `deactivatePriorityMode` | `Adm:518-521` |
| `pushPriorityOp` | `PriorityTree.push` (`PT:52-56`), called from `Mailbox.sol:374` |
| `setUpgradeTx` | `_setL2SystemContractUpgrade` (`Up:162-202`) under `_setNewProtocolVersion`'s guard (`Up:259-268`) and the engines' `_requireAllBatchesExecuted` (`Up:115-119`; `DefaultUpgrade.sol:30`, `BootstrapUpgrade.sol:30`) |

A call that reverts is "no step" (`none`). Guards are listed in source order. Checks that
only reject and depend on data outside this state are **omitted**, which makes the model
accept more calls than the source: every safety result here covers a superset of the
source's behaviours. The omitted checks are listed at each step.

## Hashes, Merkle proofs and the verifier

`keccak256(abi.encode(StoredBatchInfo))` (`Hash:9-11`), the legacy hash (`Hash:14-28`),
`_getBatchCommitment ∘ _getBatchOutputHash` (`Co:291-328`), `_rollingHash` (`Ex:48-55`), the
priority tree's root and `Merkle.calculateRootPaths` (`PT:85-90`) and the verifier
(`Ex:253-258`) are fields of `Env`: arbitrary functions. **No injectivity is assumed
anywhere.** Instead the state carries two ghost logs:

* `hashBreaks`: every time a stored-batch-hash check (`Base:238-255`) passes for a
  submitted `StoredBatchInfo` other than the one this chain hashed into that slot, the pair
  is logged. Each logged pair is a keccak collision supplied by the caller (proved:
  `LoggedHashBreaksAreCollisions`).
* `merkleBreaks`: every time `PriorityTree.processBatch` accepts item hashes that are not
  the next segment of the tree's leaves, the submitted proof is logged. Each logged proof
  opens a root the tree really had to items it does not hold there (proved:
  `LoggedMerkleBreaksAreForgeries`).

Statements about the pipeline then read "… unless the run logged a concrete break". The
logs are ghost state: they never decide whether a step succeeds.

## Other ghost state

* `preimage n`: the `StoredBatchInfo` whose hash this chain wrote into
  `storedBatchHashes[n]` (written together with it).
* `commitArgs n`: the previous batch hash, the commit input and the upgrade transaction hash
  from which `preimage n` was built.
* `executed`: the `StoredBatchInfo` and priority-op item hashes of each executed batch, in
  execution order.
* `verified`: each accepted `proveBatchesSharedBridge` call: first batch number, the
  batches, the proof.

## Model boundaries

* Counters are natural numbers. Checked `+` in the source (`Co:110`, `Ex:201`) can only add
  reverts, so the model is a superset there. The one unchecked increment,
  `currentTotalBatchesVerified.uncheckedInc()` (`Ex:238`), is modelled without wrap-around;
  `Checks` proves this exact below `2^256` and exhibits the wrap case
  (`UncheckedIncExactBelowWrap`).
* The three parallel arrays of the execute data (`BD:186-220`, `Ex:183-188`) are one list of
  triples, so the two length checks cannot fail.
* External calls are not modelled: `protocolVersionIsActive` (`Co:85-87`), the DA validator
  (`Co:179-211`), the L2 messenger (`Co:261-270`), `MessageRoot.addChainBatchRootV32`
  (`Ex:192-194`), the dependency-root lookups (`Ex:117-158`; only their result
  `depRootsHash` is kept), and the interop-fee charge (`Ex:106-113`). Every entry point is
  `nonReentrant`; the model takes each call as atomic.
* The verifier is fixed for a run (`Env.verify`). Upgrades replace it only when every
  committed batch is executed (`Up:115-119`).
* `settlementLayer`, `chainTypeManager`, `permissionlessValidator` and `validators` are
  written by no step. Migration (`Migrator.sol:215-296`), which rewrites the counters, the
  stored hashes, the priority tree and the upgrade fields from a commitment, is not a step.
* `setUpgradeTx` models the in-tree upgrade engines. An upgrade is a governance-approved
  delegatecall and could run other code.
-/

namespace Contracts.ExecutorFacet

/-- A `bytes32` value. -/
abbrev Word := UInt256

/-- An address. -/
abbrev Addr := Nat

/-- `IExecutor.StoredBatchInfo` (`state-transition/chain-interfaces/IExecutor.sol:29-39`). -/
structure StoredBatchInfo where
  batchNumber : Nat
  batchHash : Word
  indexRepeatedStorageChanges : Nat
  numberOfLayer1Txs : Nat
  priorityOperationsHash : Word
  dependencyRootsRollingHash : Word
  l2LogsTreeRoot : Word
  timestamp : Nat
  commitment : Word
  deriving DecidableEq, Inhabited

/-- The fields of `CommitBatchInfoZKsyncOS` (`chain-interfaces/ICommitter.sol:30-49`) that the
pipeline reads. The rest feed only omitted reject-only checks or `Env.batchCommitment`. -/
structure CommitBatchInfo where
  batchNumber : Nat
  newStateCommitment : Word
  numberOfLayer1Txs : Nat
  numberOfLayer2Txs : Nat
  priorityOperationsHash : Word
  dependencyRootsRollingHash : Word
  l2LogsTreeRoot : Word
  interopFeeUnits : Nat
  deriving DecidableEq, Inhabited

/-- `PriorityOpsBatchInfo` (`PT:16-20`). -/
structure PriorityOpsBatchInfo where
  leftPath : List Word
  rightPath : List Word
  itemHashes : List Word
  deriving DecidableEq, Inhabited

/-- Pure functions and the verifier, fixed for a run. None is assumed injective. -/
structure Env where
  /-- `StoredBatchHashing.hashStoredBatchInfo` (`Hash:9-11`). -/
  hashStored : StoredBatchInfo → Word
  /-- `StoredBatchHashing.hashLegacyStoredBatchInfo` (`Hash:14-28`). -/
  hashLegacy : StoredBatchInfo → Word
  /-- `_getBatchCommitment(prev.batchHash, new.newStateCommitment, new.chainConfigHash,
  _getBatchOutputHash(new, upgradeTxHash))` (`Co:253-258`, `Co:291-328`). -/
  batchCommitment : Word → CommitBatchInfo → Word → Word
  /-- `s.verifier.verify(publicInput, proof)` (`Ex:253-258`). -/
  verify : List Word → List Nat → Bool
  /-- `_rollingHash` (`Ex:48-55`). -/
  rollingHash : List Word → Word
  /-- The root of the priority tree holding exactly these leaves (`DynamicIncrementalMerkle`). -/
  treeRoot : List Word → Word
  /-- `Merkle.calculateRootPaths(leftPath, rightPath, startIndex, itemHashes)` (`PT:85-90`). -/
  calculateRootPaths : List Word → List Word → Nat → List Word → Word

/-- Ghost: what a committed batch was built from. -/
structure CommitArgs where
  prevBatchHash : Word
  input : CommitBatchInfo
  upgradeTxHash : Word
  deriving DecidableEq, Inhabited

/-- Ghost: one executed batch. -/
structure ExecRecord where
  info : StoredBatchInfo
  items : List Word
  deriving DecidableEq, Inhabited

/-- Ghost: one accepted `proveBatchesSharedBridge` call. -/
structure VerifiedCall where
  first : Nat
  batches : List StoredBatchInfo
  proof : List Nat
  deriving DecidableEq, Inhabited

/-- Ghost: a stored-batch-hash check at slot `index` passed for `submitted`, while the chain
had hashed `stored` into that slot, and the two differ. -/
structure HashBreak where
  index : Nat
  submitted : StoredBatchInfo
  stored : StoredBatchInfo
  deriving DecidableEq, Inhabited

/-- Ghost: `processBatch` accepted `ops` at unprocessed index `index` against a tree with
`leaves`, and `ops.itemHashes` is not the segment of `leaves` starting at `index`. -/
structure MerkleBreak where
  index : Nat
  ops : PriorityOpsBatchInfo
  leaves : List Word
  deriving DecidableEq, Inhabited

/-- The diamond storage the pipeline touches (`Sto:75-305`), plus ghost fields. -/
structure State where
  /-- `s.validators` (`Sto:86`). -/
  validators : Addr → Bool
  /-- `s.chainTypeManager`. -/
  chainTypeManager : Addr
  /-- `s.settlementLayer` (`Sto:218`); zero means the chain settles here. -/
  settlementLayer : Addr
  /-- `s.priorityModeInfo.activated` (`Sto:61-66`). -/
  priorityModeActivated : Bool
  /-- `s.priorityModeInfo.permissionlessValidator`. -/
  permissionlessValidator : Addr
  /-- `s.totalBatchesExecuted` (`Sto:93`). -/
  totalBatchesExecuted : Nat
  /-- `s.totalBatchesVerified` (`Sto:96`). -/
  totalBatchesVerified : Nat
  /-- `s.totalBatchesCommitted` (`Sto:100`). -/
  totalBatchesCommitted : Nat
  /-- `s.storedBatchHashes` (`Sto:103`). -/
  storedBatchHashes : Nat → Word
  /-- `s.l2LogsRootHashes` (`Sto:106`). -/
  l2LogsRootHashes : Nat → Word
  /-- `s.interopFeeUnits` (`Sto:300`). -/
  interopFeeUnits : Nat → Nat
  /-- `s.l2SystemContractsUpgradeTxHash` (`Sto:159`). -/
  l2SystemContractsUpgradeTxHash : Word
  /-- `s.l2SystemContractsUpgradeBatchNumber` (`Sto:163`). -/
  l2SystemContractsUpgradeBatchNumber : Nat
  /-- `s.priorityTree.unprocessedIndex` (`PT:30`). -/
  ptUnprocessedIndex : Nat
  /-- The leaves of `s.priorityTree.tree`, in push order (abstracts the incremental tree). -/
  ptLeaves : List Word
  /-- `s.priorityTree.historicalRoots` (`PT:31`). -/
  ptHistoricalRoots : Word → Bool
  /-- Ghost: the preimage of `storedBatchHashes[n]` written by this chain. -/
  preimage : Nat → StoredBatchInfo
  /-- Ghost: what `preimage n` was committed from. -/
  commitArgs : Nat → Option CommitArgs
  /-- Ghost: executed batches, in order. -/
  executed : List ExecRecord
  /-- Ghost: accepted proofs. -/
  verified : List VerifiedCall
  /-- Ghost: stored-hash checks passed by a different `StoredBatchInfo`. -/
  hashBreaks : List HashBreak
  /-- Ghost: priority-op proofs accepted for a non-segment. -/
  merkleBreaks : List MerkleBreak

/-! ## Shared pieces -/

/-- `onlyValidatorOrPriorityMode` (`Base:75-83`). -/
def settlerAllowed (s : State) (caller : Addr) : Bool :=
  if s.priorityModeActivated then decide (caller = s.permissionlessValidator)
  else s.validators caller

/-- Ghost: log a hash break if `submitted` is not the slot's preimage. -/
def logHash (s : State) (n : Nat) (submitted : StoredBatchInfo) : List HashBreak :=
  if submitted = s.preimage n then [] else [⟨n, submitted, s.preimage n⟩]

/-- `items` is the segment of `leaves` starting at `idx`. -/
def SegmentOk (leaves : List Word) (idx : Nat) (items : List Word) : Prop :=
  idx + items.length ≤ leaves.length ∧ (leaves.drop idx).take items.length = items

instance (leaves : List Word) (idx : Nat) (items : List Word) :
    Decidable (SegmentOk leaves idx items) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The `StoredBatchInfo` that `_commitOneBatch` builds (`Co:244-259`). -/
def storedInfoOf (env : Env) (a : CommitArgs) : StoredBatchInfo where
  batchNumber := a.input.batchNumber
  batchHash := a.input.newStateCommitment
  indexRepeatedStorageChanges := 0
  numberOfLayer1Txs := a.input.numberOfLayer1Txs
  priorityOperationsHash := a.input.priorityOperationsHash
  dependencyRootsRollingHash := a.input.dependencyRootsRollingHash
  l2LogsTreeRoot := a.input.l2LogsTreeRoot
  timestamp := 0
  commitment := env.batchCommitment a.prevBatchHash a.input a.upgradeTxHash

/-- First and last batch numbers match `_processFrom`/`_processTo` (`BD:83-92`, `BD:151-160`,
`BD:208-217`); an empty list fails, as with `EmptyData`. -/
def boundsOk (nums : List Nat) (processFrom processTo : Nat) : Bool :=
  decide (nums.head? = some processFrom) && decide (nums.getLast? = some processTo)

/-! ## commit -/

/-- Arguments of `commitBatchesSharedBridge` after decoding. -/
structure CommitCall where
  caller : Addr
  processFrom : Nat
  processTo : Nat
  lastCommitted : StoredBatchInfo
  newBatches : List CommitBatchInfo

/-- `commitBatchesSharedBridge` (`Co:72-111`, `Co:113-157`, `Co:159-283`).

Omitted reject-only checks: `protocolVersionIsActive` (`Co:85-87`), the chain config hash
(`Co:169-172`), the DA validator (`Co:179-211`), the timestamps (`Co:218-226`), the chain id
(`Co:227-229`), the DA scheme (`Co:230-232`), the settlement-layer chain id (`Co:233-235`) and
the block range (`Co:272-274`). `UpgradeBatchNumberIsNotZero` (`Co:122-124`) cannot fail: it
re-tests a conjunct of `Co:106-107`. -/
def commit (env : Env) (s : State) (c : CommitCall) : Option State :=
  -- onlyValidatorOrPriorityMode (`Co:77`, `Base:75-83`)
  if settlerAllowed s c.caller = false then none else
  -- onlySettlementLayer (`Co:77`, `Base:141-146`)
  if s.settlementLayer ≠ 0 then none else
  -- decodeAndCheckCommitData: EmptyData and bounds (`BD:79-92`)
  if boundsOk (c.newBatches.map (·.batchNumber)) c.processFrom c.processTo = false then none else
  match c.newBatches with
  | [b] =>
    -- `_checkBatchHashMismatch(lastCommittedBatchData, s.totalBatchesCommitted, false)` (`Co:103`)
    if s.storedBatchHashes s.totalBatchesCommitted ≠ env.hashStored c.lastCommitted then none else
    -- processSystemUpgradeTx (`Co:105-107`)
    let processUpgrade : Bool :=
      decide (s.l2SystemContractsUpgradeTxHash ≠ 0 ∧ s.l2SystemContractsUpgradeBatchNumber = 0)
    let upgradeTx : Word := if processUpgrade then s.l2SystemContractsUpgradeTxHash else 0
    -- `_commitOneBatch`: only the next batch (`Co:165-167`)
    if b.batchNumber ≠ c.lastCommitted.batchNumber + 1 then none else
    -- priority mode: only priority transactions (`Co:214-216`)
    if s.priorityModeActivated = true ∧ (b.numberOfLayer2Txs ≠ 0 ∨ b.numberOfLayer1Txs = 0)
    then none else
    let args : CommitArgs := ⟨c.lastCommitted.batchHash, b, upgradeTx⟩
    let info := storedInfoOf env args
    some { s with
      -- `Co:127`
      l2SystemContractsUpgradeBatchNumber :=
        if processUpgrade then b.batchNumber else s.l2SystemContractsUpgradeBatchNumber
      -- `Co:136-138`
      storedBatchHashes := Function.update s.storedBatchHashes b.batchNumber (env.hashStored info)
      -- `Co:140`
      interopFeeUnits := Function.update s.interopFeeUnits b.batchNumber b.interopFeeUnits
      -- `Co:110`
      totalBatchesCommitted := s.totalBatchesCommitted + 1
      preimage := Function.update s.preimage b.batchNumber info
      commitArgs := Function.update s.commitArgs b.batchNumber (some args)
      hashBreaks := s.hashBreaks ++ logHash s s.totalBatchesCommitted c.lastCommitted }
  -- `CanOnlyProcessOneBatch` (`Co:99-101`)
  | _ => none

/-! ## prove -/

/-- Arguments of `proveBatchesSharedBridge` after decoding. -/
structure ProveCall where
  caller : Addr
  processFrom : Nat
  processTo : Nat
  prevBatch : StoredBatchInfo
  batches : List StoredBatchInfo
  proof : List Nat

/-- The loop's hash checks (`Ex:237-242`): starting after slot `n`, batch `i` must hash to
slot `n + i + 1`. -/
def proveChecks (env : Env) (s : State) : Nat → List StoredBatchInfo → Bool
  | _, [] => true
  | n, b :: bs =>
    decide (s.storedBatchHashes (n + 1) = env.hashStored b) && proveChecks env s (n + 1) bs

/-- Ghost: the hash breaks of the loop's checks. -/
def proveBreaks (s : State) : Nat → List StoredBatchInfo → List HashBreak
  | _, [] => []
  | n, b :: bs => logHash s (n + 1) b ++ proveBreaks s (n + 1) bs

/-- `proveBatchesSharedBridge` (`Ex:215-251`), with `ablateCommittedCheck = false`.
With `true` the `VerifiedBatchesExceedsCommittedBatches` check (`Ex:243-245`) is removed;
that variant exists only for the load-bearing countermodel. -/
def proveWith (ablateCommittedCheck : Bool) (env : Env) (s : State) (c : ProveCall) :
    Option State :=
  -- onlyValidatorOrPriorityMode, onlySettlementLayer (`Ex:220`)
  if settlerAllowed s c.caller = false then none else
  if s.settlementLayer ≠ 0 then none else
  -- decodeAndCheckProofData (`BD:147-160`)
  if boundsOk (c.batches.map (·.batchNumber)) c.processFrom c.processTo = false then none else
  -- `_checkBatchHashMismatch(prevBatch, currentTotalBatchesVerified, true)` (`Ex:235`, `Base:243-254`)
  if ¬ (s.storedBatchHashes s.totalBatchesVerified = env.hashStored c.prevBatch ∨
        s.storedBatchHashes s.totalBatchesVerified = env.hashLegacy c.prevBatch) then none else
  -- the loop (`Ex:237-242`)
  if proveChecks env s s.totalBatchesVerified c.batches = false then none else
  -- `VerifiedBatchesExceedsCommittedBatches` (`Ex:243-245`)
  if ablateCommittedCheck = false ∧
      s.totalBatchesVerified + c.batches.length > s.totalBatchesCommitted then none else
  -- `_verifyProof` (`Ex:247`, `Ex:253-258`)
  if env.verify (c.batches.map (·.commitment)) c.proof = false then none else
  some { s with
    -- `Ex:250`
    totalBatchesVerified := s.totalBatchesVerified + c.batches.length
    verified := s.verified ++ [⟨s.totalBatchesVerified + 1, c.batches, c.proof⟩]
    hashBreaks := s.hashBreaks ++ proveBreaks s s.totalBatchesVerified c.batches }

/-- `proveBatchesSharedBridge` as in the source. -/
def prove (env : Env) (s : State) (c : ProveCall) : Option State := proveWith false env s c

/-! ## execute -/

/-- One batch of the execute data: the batch, its priority-op proof, and the result of
`_verifyDependencyInteropRoots` on its dependency roots (`none`: that function reverts). -/
structure ExecBatch where
  info : StoredBatchInfo
  ops : PriorityOpsBatchInfo
  depRootsHash : Option Word

/-- Ghost: the record a successfully executed batch leaves in `State.executed`. -/
def ExecBatch.record (b : ExecBatch) : ExecRecord := ⟨b.info, b.ops.itemHashes⟩

/-- `PriorityTree.processBatch` (`PT:83-96`). -/
def processBatch (env : Env) (s : State) (ops : PriorityOpsBatchInfo) : Option State :=
  if ops.itemHashes.length > 0 then
    -- `NotHistoricalRoot` (`PT:85-93`)
    if s.ptHistoricalRoots (env.calculateRootPaths ops.leftPath ops.rightPath
        s.ptUnprocessedIndex ops.itemHashes) = false then none else
    some { s with
      -- `PT:94`
      ptUnprocessedIndex := s.ptUnprocessedIndex + ops.itemHashes.length
      merkleBreaks := s.merkleBreaks ++
        (if SegmentOk s.ptLeaves s.ptUnprocessedIndex ops.itemHashes then []
         else [⟨s.ptUnprocessedIndex, ops, s.ptLeaves⟩]) }
  else some s

/-- `_executeOneBatch(batch, …, i)` (`Ex:86-114`) with `_checkBatchData` (`Ex:59-79`).
The interop-fee charge (`Ex:106-113`) is an external call and is omitted. -/
def executeOne (env : Env) (s : State) (i : Nat) (b : ExecBatch) : Option State :=
  -- `MismatchNumberOfLayer1Txs` (`Ex:92-94`)
  if b.ops.itemHashes.length ≠ b.info.numberOfLayer1Txs then none else
  -- `_verifyDependencyInteropRoots` (`Ex:96`)
  match b.depRootsHash with
  | none => none
  | some depHash =>
  -- `_checkBatchData`: `NonSequentialBatch` (`Ex:66-68`)
  if b.info.batchNumber ≠ s.totalBatchesExecuted + i + 1 then none else
  -- `_checkBatchHashMismatch(_storedBatch, currentBatchNumber, false)` (`Ex:69`)
  if s.storedBatchHashes b.info.batchNumber ≠ env.hashStored b.info then none else
  -- `PriorityOperationsRollingHashMismatch` (`Ex:95`, `Ex:70-72`)
  if env.rollingHash b.ops.itemHashes ≠ b.info.priorityOperationsHash then none else
  -- `DependencyRootsRollingHashMismatch` (`Ex:73-78`)
  if depHash ≠ b.info.dependencyRootsRollingHash then none else
  -- `s.priorityTree.processBatch` (`Ex:98`)
  match processBatch env s b.ops with
  | none => none
  | some s1 =>
    some { s1 with
      -- `Ex:103`
      l2LogsRootHashes := Function.update s1.l2LogsRootHashes b.info.batchNumber
        b.info.l2LogsTreeRoot
      executed := s1.executed ++ [⟨b.info, b.ops.itemHashes⟩]
      hashBreaks := s1.hashBreaks ++ logHash s b.info.batchNumber b.info }

/-- The loop `Ex:196-199`. `s.totalBatchesExecuted` is not written inside it. -/
def executeLoop (env : Env) : State → Nat → List ExecBatch → Option State
  | s, _, [] => some s
  | s, i, b :: bs =>
    match executeOne env s i b with
    | none => none
    | some s1 => executeLoop env s1 (i + 1) bs

/-- Arguments of `executeBatchesSharedBridge` after decoding. -/
structure ExecuteCall where
  caller : Addr
  processFrom : Nat
  processTo : Nat
  batches : List ExecBatch

/-- `executeBatchesSharedBridge` (`Ex:170-212`), with `ablateProvenCheck = false`. With
`true` the `CantExecuteUnprovenBatches` check (`Ex:203-205`) is removed, for the countermodel
only. The `MessageRoot` appends (`Ex:192-194`) are external calls and are omitted. -/
def executeWith (ablateProvenCheck : Bool) (env : Env) (s : State) (c : ExecuteCall) :
    Option State :=
  -- onlyValidatorOrPriorityMode, onlySettlementLayer (`Ex:175`)
  if settlerAllowed s c.caller = false then none else
  if s.settlementLayer ≠ 0 then none else
  -- decodeAndCheckExecuteData (`BD:204-217`)
  if boundsOk (c.batches.map (·.info.batchNumber)) c.processFrom c.processTo = false
  then none else
  match executeLoop env s 0 c.batches with
  | none => none
  | some s1 =>
    -- `CantExecuteUnprovenBatches` (`Ex:201-205`)
    if ablateProvenCheck = false ∧
        s.totalBatchesExecuted + c.batches.length > s1.totalBatchesVerified then none else
    -- `Ex:202`, then the upgrade cleanup (`Ex:207-211`)
    if s1.l2SystemContractsUpgradeBatchNumber ≠ 0 ∧
        s1.l2SystemContractsUpgradeBatchNumber ≤ s.totalBatchesExecuted + c.batches.length then
      some { s1 with
        totalBatchesExecuted := s.totalBatchesExecuted + c.batches.length
        l2SystemContractsUpgradeTxHash := 0
        l2SystemContractsUpgradeBatchNumber := 0 }
    else some { s1 with totalBatchesExecuted := s.totalBatchesExecuted + c.batches.length }

/-- `executeBatchesSharedBridge` as in the source. -/
def execute (env : Env) (s : State) (c : ExecuteCall) : Option State :=
  executeWith false env s c

/-! ## revert, priority mode, the priority queue, the upgrade transaction -/

/-- `_revertBatches(_newLastBatch)` (`Base:317-337`), with `ablateExecutedCheck = false`.
With `true` the `CantRevertExecutedBatch` check (`Base:321-323`) is removed, for the
countermodel only. -/
def revertBatchesWith (ablateExecutedCheck : Bool) (s : State) (n : Nat) : Option State :=
  -- `RevertedBatchNotAfterNewLastBatch` (`Base:318-320`)
  if s.totalBatchesCommitted < n then none else
  -- `CantRevertExecutedBatch` (`Base:321-323`)
  if ablateExecutedCheck = false ∧ n < s.totalBatchesExecuted then none else
  some { s with
    -- `Base:325-327`
    totalBatchesVerified := if n < s.totalBatchesVerified then n else s.totalBatchesVerified
    -- `Base:328`
    totalBatchesCommitted := n
    -- `Base:332-334`
    l2SystemContractsUpgradeBatchNumber :=
      if s.l2SystemContractsUpgradeBatchNumber > n then 0
      else s.l2SystemContractsUpgradeBatchNumber }

/-- `_revertBatches` as in the source. -/
def revertBatches (s : State) (n : Nat) : Option State := revertBatchesWith false s n

/-- `revertBatchesSharedBridge` (`Ex:264-269`): `onlyValidatorOrChainTypeManager`
(`Base:134-139`), `notPriorityMode` (`Base:62-65`), `onlySettlementLayer`. -/
def revertBatchesSharedBridgeWith (ablate : Bool) (s : State) (caller : Addr) (n : Nat) :
    Option State :=
  if ¬ (s.validators caller = true ∨ caller = s.chainTypeManager) then none else
  if s.priorityModeActivated = true then none else
  if s.settlementLayer ≠ 0 then none else
  revertBatchesWith ablate s n

/-- `revertBatchesSharedBridge` as in the source. -/
def revertBatchesSharedBridge (s : State) (caller : Addr) (n : Nat) : Option State :=
  revertBatchesSharedBridgeWith false s caller n

/-- `activatePriorityMode` (`Adm:523-552`): `onlySettlementLayer`, `notPriorityMode`, then
`activated := true` and `_revertBatches(totalBatchesExecuted)`. Omitted reject-only checks:
`onlyL1`, `canBeActivated`, `isPermanentRollup`, and the expiry of the oldest unprocessed
priority operation (`Adm:524-546`). Any caller. -/
def activatePriorityMode (s : State) : Option State :=
  if s.settlementLayer ≠ 0 then none else
  if s.priorityModeActivated = true then none else
  revertBatches { s with priorityModeActivated := true } s.totalBatchesExecuted

/-- `deactivatePriorityMode` (`Adm:518-521`): `onlyPriorityMode`, `onlyChainTypeManager`,
`onlySettlementLayer` (`onlyL1` omitted). -/
def deactivatePriorityMode (s : State) (caller : Addr) : Option State :=
  if s.priorityModeActivated = false then none else
  if caller ≠ s.chainTypeManager then none else
  if s.settlementLayer ≠ 0 then none else
  some { s with priorityModeActivated := false }

/-- `PriorityTree.push` (`PT:52-56`) from `Mailbox.sol:374`. The Mailbox's own checks are
omitted; any caller. -/
def pushPriorityOp (env : Env) (s : State) (h : Word) : Option State :=
  some { s with
    ptLeaves := s.ptLeaves ++ [h]
    ptHistoricalRoots :=
      Function.update s.ptHistoricalRoots (env.treeRoot (s.ptLeaves ++ [h])) true }

/-- An upgrade that sets an L2 system upgrade transaction `h ≠ 0`: the engines'
`_requireAllBatchesExecuted` (`Up:115-119`), then, for a non-patch upgrade on the settlement
layer (the only kind that may set one, `Up:175-177`), `PreviousUpgradeNotFinalized` and
`PreviousUpgradeNotCleaned` (`Up:259-268`), then the write (`Up:199`). The genesis upgrade
(`L1GenesisUpgrade.sol:31-51`) runs at chain creation, where all of these hold. Every other
effect of an upgrade leaves this state alone. -/
def setUpgradeTx (s : State) (h : Word) : Option State :=
  if h = 0 then none else
  if s.settlementLayer ≠ 0 then none else
  if s.totalBatchesCommitted ≠ s.totalBatchesExecuted then none else
  if s.l2SystemContractsUpgradeTxHash ≠ 0 then none else
  if s.l2SystemContractsUpgradeBatchNumber ≠ 0 then none else
  some { s with l2SystemContractsUpgradeTxHash := h }

/-! ## Runs -/

/-- Every entry point of the model. -/
inductive Call where
  | commit (c : CommitCall)
  | prove (c : ProveCall)
  | execute (c : ExecuteCall)
  | revert (caller : Addr) (newLastBatch : Nat)
  | activatePriorityMode
  | deactivatePriorityMode (caller : Addr)
  | pushPriorityOp (h : Word)
  | setUpgradeTx (h : Word)

/-- Which checks are removed: all `false` is the source. -/
structure Ablation where
  committedCheck : Bool := false
  provenCheck : Bool := false
  executedCheck : Bool := false

/-- One call, under an ablation. -/
def stepWith (ab : Ablation) (env : Env) (s : State) : Call → Option State
  | .commit c => commit env s c
  | .prove c => proveWith ab.committedCheck env s c
  | .execute c => executeWith ab.provenCheck env s c
  | .revert caller n => revertBatchesSharedBridgeWith ab.executedCheck s caller n
  | .activatePriorityMode => activatePriorityMode s
  | .deactivatePriorityMode caller => deactivatePriorityMode s caller
  | .pushPriorityOp h => pushPriorityOp env s h
  | .setUpgradeTx h => setUpgradeTx s h

/-- One call of the source. -/
def step (env : Env) (s : State) (c : Call) : Option State := stepWith {} env s c

/-- One successful call. -/
def Step (env : Env) (s s' : State) : Prop := ∃ c, step env s c = some s'

/-- A freshly initialized chain (`DiamondInit.sol:110-140`): counters zero, the genesis batch
hash in slot `0` with a known preimage numbered `0`, no upgrade pending, an empty priority
tree whose only historical root is the empty tree's, and empty ghost logs. That the CTM's
`storedBatchZero` is the hash of a genesis `StoredBatchInfo` numbered `0` is a boundary
(`MODEL-EXEC-GENESIS`). -/
structure Init (env : Env) (s : State) : Prop where
  executed0 : s.totalBatchesExecuted = 0
  verified0 : s.totalBatchesVerified = 0
  committed0 : s.totalBatchesCommitted = 0
  genesisHash : s.storedBatchHashes 0 = env.hashStored (s.preimage 0)
  genesisNumber : (s.preimage 0).batchNumber = 0
  noUpgradeTx : s.l2SystemContractsUpgradeTxHash = 0
  noUpgradeBatch : s.l2SystemContractsUpgradeBatchNumber = 0
  unprocessed0 : s.ptUnprocessedIndex = 0
  leaves0 : s.ptLeaves = []
  roots0 : ∀ r, s.ptHistoricalRoots r = true → r = env.treeRoot []
  executedLog0 : s.executed = []
  verifiedLog0 : s.verified = []
  hashBreaks0 : s.hashBreaks = []
  merkleBreaks0 : s.merkleBreaks = []

/-- States reachable from an initialized chain by any interleaving of calls. -/
inductive Reach (env : Env) : State → Prop where
  | init {s : State} : Init env s → Reach env s
  | step {s s' : State} : Reach env s → Step env s s' → Reach env s'

/-- Zero or more successful calls. -/
def Steps (env : Env) : State → State → Prop := Relation.ReflTransGen (Step env)

/-- Run a list of calls; `none` as soon as one reverts. -/
def runCalls (env : Env) : State → List Call → Option State
  | s, [] => some s
  | s, c :: cs =>
    match step env s c with
    | none => none
    | some s' => runCalls env s' cs

/-! ## Derived notions used by the properties -/

/-- Batch `n` with info `b` was covered by an accepted proof: some logged
`proveBatchesSharedBridge` call, whose verifier call returned `true`, had `b` at the position
of batch `n`. -/
def ProvedAt (s : State) (n : Nat) (b : StoredBatchInfo) : Prop :=
  ∃ call ∈ s.verified, ∃ j, call.first + j = n ∧ call.batches[j]? = some b

/-- A logged hash break is a keccak collision supplied by the caller. -/
def HashBreak.Genuine (env : Env) (br : HashBreak) : Prop :=
  br.submitted ≠ br.stored ∧ env.hashStored br.submitted = env.hashStored br.stored

/-- A logged Merkle break opens a root the tree really had (that of its first `k` leaves) to
item hashes that are not the tree's segment at that index. -/
def MerkleBreak.Genuine (env : Env) (br : MerkleBreak) : Prop :=
  ¬ SegmentOk br.leaves br.index br.ops.itemHashes ∧
  ∃ k ≤ br.leaves.length,
    env.calculateRootPaths br.ops.leftPath br.ops.rightPath br.index br.ops.itemHashes =
      env.treeRoot (br.leaves.take k)

/-- The run's first logged hash break exists and is a genuine collision. This is the
"or break" disjunct of the pinned statements: to falsify their main disjunct a caller must
have submitted a concrete `StoredBatchInfo` colliding with the one the chain stored. -/
def HashBreakLogged (env : Env) (s : State) : Prop :=
  ∃ br, s.hashBreaks.head? = some br ∧ br.Genuine env

/-- Some logged Merkle break is a genuine forgery. -/
def MerkleBreakLogged (env : Env) (s : State) : Prop :=
  ∃ br ∈ s.merkleBreaks, br.Genuine env

/-- The priority operations consumed so far, in order. -/
def consumed (s : State) : List Word := s.executed.flatMap (·.items)

/-- `k` applications of `UncheckedMath.uncheckedInc`
(`common/libraries/UncheckedMath.sol:11-15`) as the EVM computes them: `+ 1` modulo `2^256`.
This is the counter the loop `Ex:237-242` really computes. -/
def uncheckedIncN (v : UInt256) : Nat → UInt256
  | 0 => v
  | k + 1 => uncheckedIncN v k + 1

end Contracts.ExecutorFacet
