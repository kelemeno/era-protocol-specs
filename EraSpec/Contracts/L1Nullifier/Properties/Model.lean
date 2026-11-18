import EraSpec.Contracts.L1Nullifier.Specs.Model

/-!
# Properties: the nullifier's deposit ledger

Statements about `EraSpec.Contracts.L1Nullifier.Specs.Model`. Proofs are in
`EraSpec.Contracts.L1Nullifier.Proofs.Model`. Every run-level statement quantifies over
`Reach`: any sequence of the fifteen entry points, in any interleaving, from any start storage
(the deployed proxy already holds records). Statements that count the log start from an empty
log (`s0.log = []`); the start storage stays arbitrary. No statement assumes anything about the
hash beyond what it names; there is no injectivity premise.

## The ledger

* `DepositRecordsClaimClears`: a bridgehub deposit records `txDataHash` of its own
  `(originalCaller, assetId, transferData)` at its key, and a claim empties its key.
* `ClearCountIdentity`: along every run, for every key `(c, h)`,
  `clears + occupied(end) = nonzero writes + zero-hash clears + occupied(start)`. Each clear
  consumes one nonzero record, unless the claimed triple hashes to `0`.
* `AtMostOneClearPerDeposit`: hence, when the run records the key at most once (the bridgehub's
  canonical transaction hashes are fresh, `PROTO-TXHASH-FRESH`) and no claim of it hashes to zero,
  the key is cleared at most once: a deposit is confirmed or refunded at most once.
* `ClearsAreBacked`: every clear is backed by what precedes it: its triple hashes to `0`, to the
  key's start value, or to a value an earlier write put at that key.
* `RecordsComeFromBridgehub`: while the nullifier's `l1AssetRouter` is unset or the router, every
  write in the log is a bridgehub deposit recording `txDataHash` of its own triple, or a
  counterpart registration recording `0`.
* `RefundGoesToDepositor`: together, with the start slot fresh and the claimed hash nonzero, every
  clear has an earlier bridgehub deposit at its key whose triple hashes the same: the refund's
  `(depositSender, assetId, assetData)` is the deposit's, or the two collide (collision form). With
  no collision among the run's deposit triples at that key it is exactly the deposit's triple.
* `ClearStatusIsTrue` and `NoFailureClearOfSucceededDeposit`: given a sound status prover
  (`PROTO-TX-STATUS`), every clear's status is the L2 transaction's real status; a deposit that
  succeeded on L2 is never cleared as failed, and no key is cleared with both statuses.
* `NoHandlerCallWithoutClear`: the router never calls an asset handler's
  `bridgeConfirmTransferResult` except through a nullifier clear (`onlyNullifier`).
* `RecordLeavesOnlyByPreimage`: a nonzero record changes only by a clear of its key whose triple
  hashes to the record. A record holding a hash in the removed legacy format therefore needs a
  new-format preimage of that value (a cross-format collision) to be cleared: legacy-format
  records are unclaimable at this pin.

## Configuration and legacy

* `DeprecatedSlotsFrozen`: no entry point changes any deprecated slot, in particular
  `__DEPRECATED_isWithdrawalFinalized`: the nullifier no longer records or checks withdrawal
  finalization. (At-most-once withdrawal finalization is the interop handler's `bundleStatus`, not
  modelled here.)
* `ConfigSetOnce`: `l1AssetRouter`, `l1NativeTokenVault`, `l1InteropHandler`, once nonzero, never
  change.
* `PausedStepKeepsRecords`: while paused nothing writes or clears a record, and only the owner
  unpauses. `PausedOwnerlessFreezesForever`: if the owner renounces while the contract is paused,
  the ledger is frozen for every later run; `PausedOwnerlessReachable` shows this state is reachable
  from fresh storage after a live deposit.

## Countermodels, witnesses and a NatSpec check

* `HashCheckLoadBearing`: without `DepositDoesNotExist` (`N:243-245`) one deposit is cleared twice.
* `ProofCheckLoadBearing`: without `InvalidProof` (`N:231`), with a sound prover, a deposit that
  succeeded on L2 is cleared as failed.
* `DepositExistsLoadBearing`: without `DepositExists` (`N:160`) a second deposit at the same key
  overwrites the first, and the ledger identity fails.
* `OnlyNullifierLoadBearing`: without `onlyNullifier` (`R:70-73`) an outside call reaches the asset
  handler's failure path with no clear.
* `LifecycleWitness`: from fresh storage, with a sound prover, a run initializes, configures the
  router, deposits and recovers the failed deposit: the premises of `RefundGoesToDepositor` and
  `ClearStatusIsTrue` hold together with a clear, so neither is vacuous.
* `RepeatedKeyAccepted`: `IL1Nullifier.sol:31` says `bridgehubConfirmL2TransactionForwarded`
  "Rejects duplicates". It rejects only an occupied slot: two successive records of the same
  `(chainId, txHash)` both succeed when the first records `0` (a counterpart registration).
-/

namespace Contracts.L1Nullifier

/-! ## The ledger -/

/-- Along every run from an empty log, for every key: clears plus the end occupancy equal
nonzero writes plus zero-hash clears plus the start occupancy. -/
def Properties.ClearCountIdentity : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] → Reach Checks.source env cfg s0 s →
    ∀ (c : ChainId) (h : Bytes32),
      s.log.countP (isClear c h) + occupied s.n c h =
        s.log.countP (isNzWrite c h) + s.log.countP (isZeroClear env c h) + occupied s0.n c h

/-- A key recorded at most once (counting a record already in the start storage) and never
claimed with a zero hash is cleared at most once along any run. -/
def Properties.AtMostOneClearPerDeposit : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys) (c : ChainId) (h : Bytes32),
    s0.log = [] → Reach Checks.source env cfg s0 s →
    s.log.countP (isNzWrite c h) + occupied s0.n c h ≤ 1 →
    s.log.countP (isZeroClear env c h) = 0 →
    s.log.countP (isClear c h) ≤ 1

/-- Every clear in the log is backed by the log before it (`Backed`). -/
def Properties.ClearsAreBacked : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] → Reach Checks.source env cfg s0 s →
    ∀ (pre post : List Event) (cl : Claim) (tgt : Address),
      s.log = pre ++ Event.clear cl tgt :: post → Backed env s0.n pre cl

/-- While the nullifier's `l1AssetRouter` is unset or the router, every write in the log came from
the bridgehub through the router: a deposit of its own triple's hash or a zero counterpart record. -/
def Properties.RecordsComeFromBridgehub : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] → Reach Checks.source env cfg s0 s →
    RouterConfigured cfg s →
    ∀ (o : Origin) (c : ChainId) (h v : Bytes32), Event.write o c h v ∈ s.log →
      (∃ t, o = .deposit t ∧ v = env.txDataHash t) ∨ (o = .counterpart ∧ v = 0)

/-- With the router configured, a fresh start slot and a nonzero claimed hash, every clear follows
a bridgehub deposit at its key whose triple has the same hash (collision form); with no collision
between the claimed triple and the run's deposit triples at that key, it follows a deposit of
exactly the claimed triple. -/
def Properties.RefundGoesToDepositor : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] → Reach Checks.source env cfg s0 s →
    RouterConfigured cfg s →
    ∀ (pre post : List Event) (cl : Claim) (tgt : Address),
      s.log = pre ++ Event.clear cl tgt :: post →
      s0.n.depositHappened cl.chainId cl.l2TxHash = 0 → env.txDataHash cl.triple ≠ 0 →
      (∃ t, Event.write (.deposit t) cl.chainId cl.l2TxHash (env.txDataHash t) ∈ pre ∧
        env.txDataHash t = env.txDataHash cl.triple) ∧
      ((∀ t, Event.write (.deposit t) cl.chainId cl.l2TxHash (env.txDataHash t) ∈ s.log →
          env.txDataHash t = env.txDataHash cl.triple → t = cl.triple) →
        Event.write (.deposit cl.triple) cl.chainId cl.l2TxHash (env.txDataHash cl.triple) ∈ pre)

/-- With a sound status prover (it accepts a query only for the L2 transaction's real status),
every clear's status is the real status of its transaction. -/
def Properties.ClearStatusIsTrue : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys) (truth : ChainId → Bytes32 → Option TxStatus),
    (∀ q, env.accepts q → truth q.chainId q.l2TxHash = some q.status) →
    s0.log = [] → Reach Checks.source env cfg s0 s →
    ∀ (cl : Claim) (tgt : Address), Event.clear cl tgt ∈ s.log →
      truth cl.chainId cl.l2TxHash = some cl.txStatus

/-- With a sound status prover, a deposit whose L2 transaction succeeded is never cleared as
failed, and no key is cleared once as failed and once as succeeded. -/
def Properties.NoFailureClearOfSucceededDeposit : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys) (truth : ChainId → Bytes32 → Option TxStatus),
    (∀ q, env.accepts q → truth q.chainId q.l2TxHash = some q.status) →
    s0.log = [] → Reach Checks.source env cfg s0 s →
    (∀ (cl : Claim) (tgt : Address), Event.clear cl tgt ∈ s.log →
      truth cl.chainId cl.l2TxHash = some .success → cl.txStatus = .success) ∧
    (∀ (cl cl' : Claim) (tgt tgt' : Address), Event.clear cl tgt ∈ s.log →
      Event.clear cl' tgt' ∈ s.log → cl.chainId = cl'.chainId → cl.l2TxHash = cl'.l2TxHash →
      cl.txStatus = cl'.txStatus)

/-- One step: a bridgehub deposit records `txDataHash(caller, assetId, transferData)` at its
`(chainId, txHash)`, and a claim (either entry point) leaves its slot empty. -/
def Properties.DepositRecordsClaimClears : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s s' : Sys) (l : Label), Step Checks.source env cfg s l s' →
    (∀ (caller : Address) (c : ChainId) (a : Bytes32) (d : Bytes) (h : Bytes32),
      l = .twoBridges caller c (.deposit a d) h →
      s'.n.depositHappened c h = env.txDataHash ⟨caller, a, d⟩) ∧
    (∀ (a : Address) (cl : Claim), (l = .confirm a cl ∨ l = .recover a cl) →
      s'.n.depositHappened cl.chainId cl.l2TxHash = 0)

/-- Along every run from an empty log, the router never calls an asset handler except through a
nullifier clear. -/
def Properties.NoHandlerCallWithoutClear : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] → Reach Checks.source env cfg s0 s →
    s.log.countP isHandler = 0

/-- A nonzero record that a run changes was cleared, during the run, by a claim of its key whose
triple hashes to the record. -/
def Properties.RecordLeavesOnlyByPreimage : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s s' : Sys) (c : ChainId) (h : Bytes32),
    Reach Checks.source env cfg s s' →
    s.n.depositHappened c h ≠ 0 → s'.n.depositHappened c h ≠ s.n.depositHappened c h →
    ∃ Δ, s'.log = s.log ++ Δ ∧ ∃ (cl : Claim) (tgt : Address), Event.clear cl tgt ∈ Δ ∧
      cl.chainId = c ∧ cl.l2TxHash = h ∧ env.txDataHash cl.triple = s.n.depositHappened c h

/-! ## Configuration and legacy -/

/-- No run changes any deprecated slot (whatever the checks). -/
def Properties.DeprecatedSlotsFrozen : Prop :=
  ∀ (chk : Checks) (env : Env) (cfg : Cfg) (s s' : Sys), Reach chk env cfg s s' →
    s'.n.deprecated = s.n.deprecated

/-- The three addresses are set once: once nonzero they never change along a run. -/
def Properties.ConfigSetOnce : Prop :=
  ∀ (chk : Checks) (env : Env) (cfg : Cfg) (s s' : Sys), Reach chk env cfg s s' →
    (s.n.l1AssetRouter ≠ 0 → s'.n.l1AssetRouter = s.n.l1AssetRouter) ∧
    (s.n.l1NativeTokenVault ≠ 0 → s'.n.l1NativeTokenVault = s.n.l1NativeTokenVault) ∧
    (s.n.l1InteropHandler ≠ 0 → s'.n.l1InteropHandler = s.n.l1InteropHandler)

/-- From a paused nullifier, no step changes `depositHappened`, and the only step that unpauses is
the owner's `unpause`. -/
def Properties.PausedStepKeepsRecords : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s s' : Sys) (l : Label), Step Checks.source env cfg s l s' →
    s.n.paused = true →
    s'.n.depositHappened = s.n.depositHappened ∧ (s'.n.paused = false → l = .unpause s.n.owner)

/-- An initialized nullifier that is paused, with owner and pending owner zero, keeps its paused
flag and its whole ledger along every later run. -/
def Properties.PausedOwnerlessFreezesForever : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s s' : Sys), Reach Checks.source env cfg s s' →
    s.n.initialized = true → s.n.paused = true → s.n.owner = 0 → s.n.pendingOwner = 0 →
    s'.n.paused = true ∧ s'.n.depositHappened = s.n.depositHappened

/-- From fresh storage, a run records a live deposit and then reaches a paused, ownerless state:
the frozen state of `PausedOwnerlessFreezesForever` is reachable with a deposit unclaimed. -/
def Properties.PausedOwnerlessReachable : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] ∧ s0.n.initialized = false ∧
    Reach Checks.source env cfg s0 s ∧
    s.n.initialized = true ∧ s.n.paused = true ∧ s.n.owner = 0 ∧ s.n.pendingOwner = 0 ∧
    ∃ c h, s.n.depositHappened c h ≠ 0

/-! ## Countermodels -/

/-- Without the data-hash check, a key recorded once and never claimed with a zero hash is
cleared twice. -/
def Properties.HashCheckLoadBearing : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (c : ChainId) (h : Bytes32),
    s0.log = [] ∧ Reach { Checks.source with dataHash := false } env cfg s0 s ∧
    s.log.countP (isNzWrite c h) + occupied s0.n c h ≤ 1 ∧
    s.log.countP (isZeroClear env c h) = 0 ∧
    ¬ s.log.countP (isClear c h) ≤ 1

/-- Without the proof check, with a sound prover, a deposit that succeeded on L2 is cleared as
failed. -/
def Properties.ProofCheckLoadBearing : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (truth : ChainId → Bytes32 → Option TxStatus),
    (∀ q, env.accepts q → truth q.chainId q.l2TxHash = some q.status) ∧
    s0.log = [] ∧ Reach { Checks.source with proof := false } env cfg s0 s ∧
    ∃ (cl : Claim) (tgt : Address), Event.clear cl tgt ∈ s.log ∧
      truth cl.chainId cl.l2TxHash = some .success ∧ cl.txStatus = .failure

/-- Without `DepositExists`, the ledger identity fails: a second deposit overwrites the first. -/
def Properties.DepositExistsLoadBearing : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (c : ChainId) (h : Bytes32),
    s0.log = [] ∧ Reach { Checks.source with depositExists := false } env cfg s0 s ∧
    s.log.countP (isClear c h) + occupied s.n c h ≠
      s.log.countP (isNzWrite c h) + s.log.countP (isZeroClear env c h) + occupied s0.n c h

/-- Without `onlyNullifier`, an outside call reaches the asset handler with no clear. -/
def Properties.OnlyNullifierLoadBearing : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] ∧
    Reach { Checks.source with onlyNullifier := false } env cfg s0 s ∧
    s.log.countP isHandler ≠ 0 ∧ ∀ c h, s.log.countP (isClear c h) = 0

/-! ## Witnesses and the NatSpec -/

/-- From fresh storage, with a sound prover, a run reaches a failure clear that targets the router
and follows a deposit of exactly the claimed triple, with the router configured and a nonzero hash:
the premises of `RefundGoesToDepositor` and `ClearStatusIsTrue` are jointly satisfiable. -/
def Properties.LifecycleWitness : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (truth : ChainId → Bytes32 → Option TxStatus),
    (∀ q, env.accepts q → truth q.chainId q.l2TxHash = some q.status) ∧
    s0.log = [] ∧ s0.n.initialized = false ∧ (∀ c h, s0.n.depositHappened c h = 0) ∧
    Reach Checks.source env cfg s0 s ∧ RouterConfigured cfg s ∧
    ∃ (cl : Claim) (tgt : Address), Event.clear cl tgt ∈ s.log ∧ cl.txStatus = .failure ∧
      tgt = cfg.router ∧ env.txDataHash cl.triple ≠ 0 ∧
      Event.write (.deposit cl.triple) cl.chainId cl.l2TxHash (env.txDataHash cl.triple) ∈ s.log

/-- `IL1Nullifier.sol:31` ("Rejects duplicates"), refuted as stated: two successive records of the
same key both succeed. -/
def Properties.RepeatedKeyAccepted : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s s1 s2 : Sys) (a a' : Address) (c : ChainId) (h : Bytes32)
    (r r' : SecondBridge),
    Step Checks.source env cfg s (.twoBridges a c r h) s1 ∧
    Step Checks.source env cfg s1 (.twoBridges a' c r' h) s2

end Contracts.L1Nullifier
