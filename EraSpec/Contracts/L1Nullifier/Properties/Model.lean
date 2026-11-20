import EraSpec.Contracts.L1Nullifier.Specs.Model
import EraSpec.Core.Headline

/-!
# Properties: the nullifier's deposit ledger

Statements about `EraSpec.Contracts.L1Nullifier.Specs.Model` (`draft/v0.35.0`, `b17415d20`). Proofs
are in `EraSpec.Contracts.L1Nullifier.Proofs.Model`. A run is `Reach`: any sequence of the fifteen
labelled calls, in any interleaving, from any start storage (a deployed proxy already holds
records). Statements that count or search the log start from an empty log (`s0.log = []`); the
start storage stays arbitrary. No statement assumes anything about the hash beyond what it names:
some assume a named hash value is nonzero, and the only no-collision premise is the second half of
`ClearCarriesDepositTriple`, on the run's own deposit triples at one key.

## (a) Each record is consumed at most once

* `DepositRecordsClaimClears` (one step): a bridgehub deposit records `txDataHash` of its own
  `(originalCaller, assetId, transferData)` at its key, and a claim empties its key.
* `ClearCountIdentity`: along every run, for every key `(c, h)`,
  `clears + occupied(end) = nonzero writes + zero-hash clears + occupied(start)`.
* `AtMostOneClearPerDeposit`: hence, if the run records the key at most once (counting a record
  in the start storage) and no claim of it hashes to zero, the key is cleared at most once. The
  count premise is `PROTO-TXHASH-FRESH`; `DepositExists` does not supply it
  (`TxHashFreshnessLoadBearing`, `RepeatedKeyAccepted`), and the zero-hash premise is needed too
  (`ZeroHashClaimClearsEmptySlot`).

## (b) A clear carries the triple of a bridgehub deposit

* `ClearsAreBacked`: every clear is backed by what precedes it: its triple hashes to `0`, to the
  key's start value, or to a value an earlier write put at that key.
* `RecordsComeFromBridgehub`: if the nullifier's `l1AssetRouter` is unset or the router at the end
  of the run, every write in the log is a bridgehub deposit recording `txDataHash` of its own
  triple, or a counterpart registration recording `0`.
* `ClearCarriesDepositTriple`: with the router configured, a fresh start slot and a nonzero
  claimed hash, every clear has an earlier bridgehub deposit at its key whose triple hashes the
  same. If no other deposit triple at that key in the run hashes the same, it is a deposit of
  exactly the claimed `(depositSender, assetId, assetData)`, the triple the nullifier passes on to
  `l1AssetRouter`. What the asset handler then pays, and to whom, is not modelled. `RouterConfiguredLoadBearing`
  and `ZeroHashClaimClearsEmptySlot` show two of the premises are needed.
* `NoHandlerCallWithoutClear`: no direct call reaches the router's `bridgeConfirmTransferResult`
  (`onlyNullifier`), so in the model the router calls an asset handler only inside a clear
  (`OnlyNullifierLoadBearing`).

## (c) A clear carries the transaction's real status

* `ClearStatusIsTrue`, `NoFailureClearOfSucceededDeposit`: given a sound status prover
  (`PROTO-TX-STATUS`, load-bearing by `SoundProverLoadBearing`), every clear's status is the L2
  transaction's real status. A deposit whose transaction succeeded is never cleared as failed, and
  no key is cleared once with each status.

## (d) Records persist and stay claimable

* `RecordLeavesOnlyByPreimage`: a nonzero record changes only by a clear of its key whose triple
  hashes to the record.
* `RecordStaysUntilCleared`: a nonzero value written at a key is still there at the end of the run
  if no later clear of that key happened.
* `UnclaimedDepositRecoverable`: so a bridgehub deposit with a nonzero hash and no later clear of
  its key can be recovered by any external caller while both contracts are unpaused, the
  nullifier's `l1AssetRouter` is the router and the prover accepts the failure query; the recovery
  clears the key and passes the deposit's own triple to the router. Downstream checks the model
  omits can still revert that call.

## (e) Configuration and pause

* `DeprecatedSlotsFrozen`: no run changes any deprecated slot.
* `ConfigSetOnce`: `l1AssetRouter`, `l1NativeTokenVault`, `l1InteropHandler`, once nonzero, never
  change.
* `OnlyOwnerPausesOrConfigures`: only the owner changes the pause flag or the three addresses; the
  owner changes only by `initialize`, `acceptOwnership` or `renounceOwnership`.
  `InitializeOnlyOnce`: `initialize` succeeds at most once along a run.
* `PausedStepKeepsRecords`: while paused no step changes `depositHappened`, and only the owner
  unpauses. `RouterPausedStepKeepsRecords`: while the router is paused and configured, no step
  changes `depositHappened` either. `PausedOwnerlessFreezesForever`: in this model, which has no proxy upgrade
  (`OPS-CONFIG`), a paused nullifier whose owner and pending owner are zero stays paused with an
  unchanged ledger for every later run. `PausedOwnerlessReachable`: that state is reachable from
  fresh storage with a record held.

## Countermodels

Each of `HashCheckLoadBearing`, `ProofCheckLoadBearing`, `DepositExistsLoadBearing` and
`OnlyNullifierLoadBearing` removes one source check and breaks the matching result.
`TxHashFreshnessLoadBearing`, `SoundProverLoadBearing`, `RouterConfiguredLoadBearing` and
`ZeroHashClaimClearsEmptySlot` keep every check and drop one premise. `RepeatedKeyAccepted`: two
successive records of one key both succeed when the first records zero.

## Witnesses

`LedgerRunWitness` is one run from fresh storage meeting the premises of the run-level results of
(a)-(c), with a recovery and a confirmation, a prover that accepts exactly the real statuses, and a
hash that separates the two deposits. `SameKeyClearedTwiceWitness` meets the premises of the
second half of `NoFailureClearOfSucceededDeposit` with two different clears of one key.
`RecordLeavesOnlyByPreimageWitness`, `UnclaimedDepositRecoverableWitness`, `LedgerStepWitness`
(the one-step results), `ConfigSetOnceWitness`, `InitializeOnlyOnceWitness` and
`RouterPausedStepWitness` cover the rest; `PausedOwnerlessReachable` covers
`PausedOwnerlessFreezesForever`.
-/

namespace Contracts.L1Nullifier

/-! ## (a) Each record is consumed at most once -/

/-- **A DEPOSIT RECORDS ITS OWN TRIPLE'S HASH; A CLAIM EMPTIES ITS KEY.** For one step of the
source: a bridgehub two-bridges deposit by `caller` of `(assetId, transferData)` leaves
`depositHappened[c][h] = txDataHash(caller, assetId, transferData)`; a claim through either entry
point leaves its own key `0`. -/
def Properties.DepositRecordsClaimClears : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s s' : Sys) (l : Label), Step Checks.source env cfg s l s' →
    (∀ (caller : Address) (c : ChainId) (a : Bytes32) (d : Bytes) (h : Bytes32),
      l = .twoBridges caller c (.deposit a d) h →
      s'.n.depositHappened c h = env.txDataHash ⟨caller, a, d⟩) ∧
    (∀ (a : Address) (cl : Claim), (l = .confirm a cl ∨ l = .recover a cl) →
      s'.n.depositHappened cl.chainId cl.l2TxHash = 0)

/-- **THE LEDGER COUNT IDENTITY.** Along every run of the source from an empty log, for every key
`(c, h)`: clears of the key plus its occupancy at the end equal nonzero writes at the key plus
clears of it whose triple hashes to zero plus its occupancy at the start. -/
def Properties.ClearCountIdentity : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] → Reach Checks.source env cfg s0 s →
    ∀ (c : ChainId) (h : Bytes32),
      s.log.countP (isClear c h) + occupied s.n c h =
        s.log.countP (isNzWrite c h) + s.log.countP (isZeroClear env c h) + occupied s0.n c h

/-- **HEADLINE (a): A KEY RECORDED ONCE IS CLEARED AT MOST ONCE.** Along every run of the source
from an empty log: if the key is recorded with a nonzero value at most once, counting a record
already in the start storage, and no clear of it carries a triple hashing to zero, then it is
cleared at most once. So a deposit is confirmed or recovered at most once, and not both. -/
@[headline] def Properties.AtMostOneClearPerDeposit : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys) (c : ChainId) (h : Bytes32),
    s0.log = [] → Reach Checks.source env cfg s0 s →
    s.log.countP (isNzWrite c h) + occupied s0.n c h ≤ 1 →
    s.log.countP (isZeroClear env c h) = 0 →
    s.log.countP (isClear c h) ≤ 1

/-! ## (b) A clear carries the triple of a bridgehub deposit -/

/-- **EVERY CLEAR IS BACKED.** Along every run of the source from an empty log, every clear is
`Backed` by the log before it: its triple hashes to `0`, or to its key's value in the start
storage, or to a value some earlier write put at its key. -/
def Properties.ClearsAreBacked : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] → Reach Checks.source env cfg s0 s →
    ∀ (pre post : List Event) (cl : Claim) (tgt : Address),
      s.log = pre ++ Event.clear cl tgt :: post → Backed env s0.n pre cl

/-- **RECORDS COME FROM THE BRIDGEHUB.** Along every run of the source from an empty log that ends
with the nullifier's `l1AssetRouter` unset or the router, every write in the log is a bridgehub
two-bridges deposit of some triple recording that triple's hash, or a counterpart registration
recording `0`. -/
def Properties.RecordsComeFromBridgehub : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] → Reach Checks.source env cfg s0 s →
    RouterConfigured cfg s →
    ∀ (o : Origin) (c : ChainId) (h v : Bytes32), Event.write o c h v ∈ s.log →
      (∃ t, o = .deposit t ∧ v = env.txDataHash t) ∨ (o = .counterpart ∧ v = 0)

/-- **HEADLINE (b): A CLEAR CARRIES THE TRIPLE OF AN EARLIER DEPOSIT.** Along every run of the source
from an empty log that ends with the router configured (`RouterConfigured`): for every clear of a
claim `cl` whose key was empty in the start storage and whose triple's hash is nonzero, (1) some
earlier bridgehub deposit at `cl`'s key has a triple with the same hash; (2) if no deposit triple
at that key in the run other than `cl`'s own hashes the same as `cl`'s, an earlier bridgehub deposit
at that key is of exactly `cl`'s `(depositSender, assetId, assetData)`. (2)'s premise is a
no-collision premise on the run's own deposits at one key, not global injectivity. -/
@[headline] def Properties.ClearCarriesDepositTriple : Prop :=
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

/-- **NO HANDLER CALL WITHOUT A CLEAR.** Along every run of the source from an empty log, no direct
call of the router's `bridgeConfirmTransferResult` succeeds (`onlyNullifier`): the log has no
`handler` event. In the model the router therefore calls an asset handler only inside a clear. -/
@[headline] def Properties.NoHandlerCallWithoutClear : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] → Reach Checks.source env cfg s0 s →
    s.log.countP isHandler = 0

/-! ## (c) A clear carries the transaction's real status -/

/-- **HEADLINE (c): A CLEAR'S STATUS IS THE REAL ONE.** If the status prover accepts a query only for
the L2 transaction's real status (`PROTO-TX-STATUS`), then along every run of the source from an
empty log every clear's status is the real status of its transaction. -/
@[headline] def Properties.ClearStatusIsTrue : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys) (truth : ChainId → Bytes32 → Option TxStatus),
    (∀ q, env.accepts q → truth q.chainId q.l2TxHash = some q.status) →
    s0.log = [] → Reach Checks.source env cfg s0 s →
    ∀ (cl : Claim) (tgt : Address), Event.clear cl tgt ∈ s.log →
      truth cl.chainId cl.l2TxHash = some cl.txStatus

/-- **A SUCCEEDED DEPOSIT IS NEVER CLEARED AS FAILED.** With a sound status prover, along every run
of the source from an empty log: a clear of a key whose transaction succeeded has status success,
and two clears of one key have the same status. -/
@[headline] def Properties.NoFailureClearOfSucceededDeposit : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys) (truth : ChainId → Bytes32 → Option TxStatus),
    (∀ q, env.accepts q → truth q.chainId q.l2TxHash = some q.status) →
    s0.log = [] → Reach Checks.source env cfg s0 s →
    (∀ (cl : Claim) (tgt : Address), Event.clear cl tgt ∈ s.log →
      truth cl.chainId cl.l2TxHash = some .success → cl.txStatus = .success) ∧
    (∀ (cl cl' : Claim) (tgt tgt' : Address), Event.clear cl tgt ∈ s.log →
      Event.clear cl' tgt' ∈ s.log → cl.chainId = cl'.chainId → cl.l2TxHash = cl'.l2TxHash →
      cl.txStatus = cl'.txStatus)

/-! ## (d) Records persist and stay claimable -/

/-- **A RECORD LEAVES ONLY BY A PREIMAGE.** Along any run of the source from any state: if a key's
value was nonzero at the start and differs at the end, then the run's new events include a clear
of that key whose claimed triple hashes to the start value. -/
def Properties.RecordLeavesOnlyByPreimage : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s s' : Sys) (c : ChainId) (h : Bytes32),
    Reach Checks.source env cfg s s' →
    s.n.depositHappened c h ≠ 0 → s'.n.depositHappened c h ≠ s.n.depositHappened c h →
    ∃ Δ, s'.log = s.log ++ Δ ∧ ∃ (cl : Claim) (tgt : Address), Event.clear cl tgt ∈ Δ ∧
      cl.chainId = c ∧ cl.l2TxHash = h ∧ env.txDataHash cl.triple = s.n.depositHappened c h

/-- **A RECORD STAYS UNTIL ITS KEY IS CLEARED.** Along every run of the source from an empty log: a
nonzero value written at a key, by any write in the log, is the key's value at the end of the run if
no clear of that key comes after the write. -/
def Properties.RecordStaysUntilCleared : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] → Reach Checks.source env cfg s0 s →
    ∀ (pre post : List Event) (o : Origin) (c : ChainId) (h v : Bytes32),
      s.log = pre ++ Event.write o c h v :: post → v ≠ 0 → post.countP (isClear c h) = 0 →
      s.n.depositHappened c h = v

/-- **HEADLINE (d): AN UNCLAIMED DEPOSIT CAN BE RECOVERED.** Along every run of the source from an
empty log, take a bridgehub deposit of triple `t` at key `(c, h)` with `txDataHash t ≠ 0` and no
later clear of that key. If at the end both contracts are unpaused and the nullifier's
`l1AssetRouter` is the router, then for any external caller `a` and any claim `cl` of that key and
triple whose failure query the prover accepts, `bridgeRecoverFailedTransfer` succeeds in the
model. It empties the key and its clear hands the router exactly `cl`'s fields with status
`Failure`. This is enabledness for the two modelled contracts only. The downstream checks the model
omits can still revert the call (`DEP-RESULTS`): `_checkAssetHandlerAllowed`, the asset handler's
own checks, and a reentrancy lock never initialized. -/
@[headline] def Properties.UnclaimedDepositRecoverable : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] → Reach Checks.source env cfg s0 s →
    ∀ (pre post : List Event) (t : Triple) (c : ChainId) (h : Bytes32),
      s.log = pre ++ Event.write (.deposit t) c h (env.txDataHash t) :: post →
      env.txDataHash t ≠ 0 → post.countP (isClear c h) = 0 →
      s.n.paused = false → s.n.l1AssetRouter = cfg.router → s.routerPaused = false →
      ∀ (a : Address) (cl : Claim), ExternalSender cfg a →
        cl.chainId = c → cl.l2TxHash = h → cl.triple = t → env.accepts cl.asFailure.query →
        Step Checks.source env cfg s (.recover a cl) (afterClaim s cl.asFailure) ∧
          (afterClaim s cl.asFailure).n.depositHappened c h = 0 ∧
          (afterClaim s cl.asFailure).log = s.log ++ [.clear cl.asFailure cfg.router]

/-! ## (e) Configuration and pause -/

/-- **DEPRECATED SLOTS ARE FROZEN.** Along any run, with any checks, no deprecated slot changes. -/
@[headline] def Properties.DeprecatedSlotsFrozen : Prop :=
  ∀ (chk : Checks) (env : Env) (cfg : Cfg) (s s' : Sys), Reach chk env cfg s s' →
    s'.n.deprecated = s.n.deprecated

/-- **THE THREE ADDRESSES ARE SET ONCE.** Along any run, with any checks, each of `l1AssetRouter`,
`l1NativeTokenVault` and `l1InteropHandler` that is nonzero at the start is unchanged at the end. -/
@[headline] def Properties.ConfigSetOnce : Prop :=
  ∀ (chk : Checks) (env : Env) (cfg : Cfg) (s s' : Sys), Reach chk env cfg s s' →
    (s.n.l1AssetRouter ≠ 0 → s'.n.l1AssetRouter = s.n.l1AssetRouter) ∧
    (s.n.l1NativeTokenVault ≠ 0 → s'.n.l1NativeTokenVault = s.n.l1NativeTokenVault) ∧
    (s.n.l1InteropHandler ≠ 0 → s'.n.l1InteropHandler = s.n.l1InteropHandler)

/-- **ONLY THE OWNER PAUSES OR CONFIGURES.** For one step, with any checks: if the step changes the
nullifier's pause flag or one of its three addresses, it is an `onlyOwner` call
(`Label.ownerCaller`) by the current owner, and that owner is nonzero. If the step changes the
owner, it is `initialize` on uninitialized storage, `acceptOwnership` by the pending owner, or
`renounceOwnership` by the owner. -/
def Properties.OnlyOwnerPausesOrConfigures : Prop :=
  ∀ (chk : Checks) (env : Env) (cfg : Cfg) (s s' : Sys) (l : Label), Step chk env cfg s l s' →
    ((s'.n.paused ≠ s.n.paused ∨ s'.n.l1AssetRouter ≠ s.n.l1AssetRouter ∨
        s'.n.l1NativeTokenVault ≠ s.n.l1NativeTokenVault ∨
        s'.n.l1InteropHandler ≠ s.n.l1InteropHandler) →
      l.ownerCaller = some s.n.owner ∧ s.n.owner ≠ 0) ∧
    (s'.n.owner ≠ s.n.owner →
      (∃ a o, l = .initialize a o ∧ s.n.initialized = false) ∨
        l = .acceptOwnership s.n.pendingOwner ∨ l = .renounceOwnership s.n.owner)

/-- **`initialize` SUCCEEDS AT MOST ONCE.** With any checks: after a successful `initialize`, no
state reached by a later run admits another `initialize` step, by any caller with any owner. -/
def Properties.InitializeOnlyOnce : Prop :=
  ∀ (chk : Checks) (env : Env) (cfg : Cfg) (s s' s'' t : Sys) (a o a' o' : Address),
    Step chk env cfg s (.initialize a o) s' → Reach chk env cfg s' s'' →
    ¬ Step chk env cfg s'' (.initialize a' o') t

/-- **THE ROUTER'S PAUSE ALSO KEEPS THE RECORDS.** For one step of the source while the router is
paused and is the nullifier's `l1AssetRouter`: `depositHappened` is unchanged. No bridgehub deposit
is recorded (`R:212`, `:248`), no claim succeeds (`R:312`), and no other address can record. -/
def Properties.RouterPausedStepKeepsRecords : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s s' : Sys) (l : Label), Step Checks.source env cfg s l s' →
    s.routerPaused = true → s.n.l1AssetRouter = cfg.router →
    s'.n.depositHappened = s.n.depositHappened

/-- **A PAUSED STEP KEEPS THE RECORDS.** For one step of the source from a paused nullifier:
`depositHappened` is unchanged, and if the step unpauses it is the owner's `unpause`. -/
def Properties.PausedStepKeepsRecords : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s s' : Sys) (l : Label), Step Checks.source env cfg s l s' →
    s.n.paused = true →
    s'.n.depositHappened = s.n.depositHappened ∧ (s'.n.paused = false → l = .unpause s.n.owner)

/-- **PAUSED AND OWNERLESS IS FINAL, IN THIS MODEL.** Along any run of the source from an
initialized, paused nullifier whose owner and pending owner are zero, the nullifier stays paused and
its whole ledger is unchanged. The model has no proxy upgrade (`OPS-CONFIG`). -/
def Properties.PausedOwnerlessFreezesForever : Prop :=
  ∀ (env : Env) (cfg : Cfg) (s s' : Sys), Reach Checks.source env cfg s s' →
    s.n.initialized = true → s.n.paused = true → s.n.owner = 0 → s.n.pendingOwner = 0 →
    s'.n.paused = true ∧ s'.n.depositHappened = s.n.depositHappened

/-- **THE PAUSED, OWNERLESS STATE IS REACHABLE WITH A RECORD HELD.** From uninitialized storage with
every record empty, a run of the source reaches an initialized, paused state with owner and
pending owner zero that holds a nonzero record: the premises of `PausedOwnerlessFreezesForever`. -/
@[witness] def Properties.PausedOwnerlessReachable : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] ∧ s0.n.initialized = false ∧
    (∀ c h, s0.n.depositHappened c h = 0) ∧ Reach Checks.source env cfg s0 s ∧
    s.n.initialized = true ∧ s.n.paused = true ∧ s.n.owner = 0 ∧ s.n.pendingOwner = 0 ∧
    ∃ c h, s.n.depositHappened c h ≠ 0

/-! ## Countermodels: one source check removed -/

/-- **WITHOUT THE DATA-HASH CHECK, ONE DEPOSIT IS CLEARED TWICE.** Without `DepositDoesNotExist`
(`N:243-245`), a run from an empty log records a key with a nonzero value at most once (counting
the start storage), never claims it with a zero hash, and clears it more than once. -/
@[countermodel] def Properties.HashCheckLoadBearing : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (c : ChainId) (h : Bytes32),
    s0.log = [] ∧ Reach { Checks.source with dataHash := false } env cfg s0 s ∧
    s.log.countP (isNzWrite c h) + occupied s0.n c h ≤ 1 ∧
    s.log.countP (isZeroClear env c h) = 0 ∧
    ¬ s.log.countP (isClear c h) ≤ 1

/-- **WITHOUT THE PROOF CHECK, A SUCCEEDED DEPOSIT IS CLEARED AS FAILED.** Without `InvalidProof`
(`N:231`), and with a sound prover, a run from an empty log clears a key with status failure
although its transaction succeeded. -/
@[countermodel] def Properties.ProofCheckLoadBearing : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (truth : ChainId → Bytes32 → Option TxStatus),
    (∀ q, env.accepts q → truth q.chainId q.l2TxHash = some q.status) ∧
    s0.log = [] ∧ Reach { Checks.source with proof := false } env cfg s0 s ∧
    ∃ (cl : Claim) (tgt : Address), Event.clear cl tgt ∈ s.log ∧
      truth cl.chainId cl.l2TxHash = some .success ∧ cl.txStatus = .failure

/-- **WITHOUT `DepositExists`, THE LEDGER IDENTITY FAILS.** Without `N:160`, a run from an empty log
breaks the identity of `ClearCountIdentity` at some key (in the proof, a second deposit overwrites
the first record). -/
@[countermodel] def Properties.DepositExistsLoadBearing : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (c : ChainId) (h : Bytes32),
    s0.log = [] ∧ Reach { Checks.source with depositExists := false } env cfg s0 s ∧
    s.log.countP (isClear c h) + occupied s.n c h ≠
      s.log.countP (isNzWrite c h) + s.log.countP (isZeroClear env c h) + occupied s0.n c h

/-- **WITHOUT `onlyNullifier`, AN OUTSIDE CALL REACHES THE HANDLER.** Without `R:70-73`, a run from
an empty log has a `handler` event and no clear at all. -/
@[countermodel] def Properties.OnlyNullifierLoadBearing : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] ∧
    Reach { Checks.source with onlyNullifier := false } env cfg s0 s ∧
    s.log.countP isHandler ≠ 0 ∧ ∀ c h, s.log.countP (isClear c h) = 0

/-! ## Countermodels: every check kept, one premise dropped -/

/-- **WITHOUT FRESH TRANSACTION HASHES, ONE KEY IS CLEARED TWICE.** With every source check, a run
from fresh storage whose log is a bridgehub deposit of `cl`'s triple at `cl`'s key, a clear of
`cl`, the same deposit again at the same key, and a second clear of `cl`; the hash is nonzero. So
the key has two nonzero writes, no zero-hash clear and two clears: `AtMostOneClearPerDeposit`
needs its count premise (`PROTO-TXHASH-FRESH`). `DepositExists` rejects only an occupied key, and
a clear empties it. -/
@[countermodel] def Properties.TxHashFreshnessLoadBearing : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (cl : Claim),
    s0.log = [] ∧ (∀ c' h', s0.n.depositHappened c' h' = 0) ∧ Reach Checks.source env cfg s0 s ∧
    s.log = [.write (.deposit cl.triple) cl.chainId cl.l2TxHash (env.txDataHash cl.triple),
      .clear cl cfg.router,
      .write (.deposit cl.triple) cl.chainId cl.l2TxHash (env.txDataHash cl.triple),
      .clear cl cfg.router] ∧
    env.txDataHash cl.triple ≠ 0 ∧
    s.log.countP (isNzWrite cl.chainId cl.l2TxHash) = 2 ∧
    s.log.countP (isZeroClear env cl.chainId cl.l2TxHash) = 0 ∧
    s.log.countP (isClear cl.chainId cl.l2TxHash) = 2

/-- **WITHOUT A SOUND PROVER, A SUCCEEDED DEPOSIT IS CLEARED AS FAILED.** With every source check, a
prover that accepts a failure query for a transaction whose real status is success lets a run from
an empty log clear that key as failed. `ClearStatusIsTrue` needs `PROTO-TX-STATUS`. -/
@[countermodel] def Properties.SoundProverLoadBearing : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (truth : ChainId → Bytes32 → Option TxStatus),
    s0.log = [] ∧ Reach Checks.source env cfg s0 s ∧
    ∃ (cl : Claim) (tgt : Address), Event.clear cl tgt ∈ s.log ∧
      truth cl.chainId cl.l2TxHash = some .success ∧ cl.txStatus = .failure ∧ env.accepts cl.query

/-- **WITH ANOTHER `l1AssetRouter`, A CLEAR NEEDS NO DEPOSIT.** With every source check, from fresh
storage, a run that ends with `l1AssetRouter` neither unset nor the router, whose log has a direct
write of a nonzero value by that address (`bridgehubConfirmL2TransactionForwarded` called by it,
`Origin.direct`) and a clear of a claim whose triple's hash is nonzero, and no bridgehub deposit.
So without `RouterConfigured` the conclusions of `RecordsComeFromBridgehub` and
`ClearCarriesDepositTriple` fail. -/
@[countermodel] def Properties.RouterConfiguredLoadBearing : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys), s0.log = [] ∧ (∀ c h, s0.n.depositHappened c h = 0) ∧
    Reach Checks.source env cfg s0 s ∧ ¬ RouterConfigured cfg s ∧
    (∀ (t : Triple) (c : ChainId) (h v : Bytes32), Event.write (.deposit t) c h v ∉ s.log) ∧
    (∃ (c : ChainId) (h v : Bytes32),
      Event.write (.direct s.n.l1AssetRouter) c h v ∈ s.log ∧ v ≠ 0) ∧
    ∃ (cl : Claim) (tgt : Address), Event.clear cl tgt ∈ s.log ∧ env.txDataHash cl.triple ≠ 0

/-- **A TRIPLE HASHING TO ZERO CLEARS AN EMPTY KEY, REPEATEDLY.** With every source check and the
router configured, from fresh storage: a run with no write at all clears one key twice, both times
with a claimed triple hashing to `0`, which passes the data-hash check against the empty key. So
`AtMostOneClearPerDeposit` needs its zero-hash premise and `ClearCarriesDepositTriple` its
nonzero-hash premise. For keccak such a triple is a preimage of zero. -/
@[countermodel] def Properties.ZeroHashClaimClearsEmptySlot : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (c : ChainId) (h : Bytes32),
    s0.log = [] ∧ (∀ c' h', s0.n.depositHappened c' h' = 0) ∧
    Reach Checks.source env cfg s0 s ∧ RouterConfigured cfg s ∧
    (∀ (o : Origin) (c' : ChainId) (h' v : Bytes32), Event.write o c' h' v ∉ s.log) ∧
    s.log.countP (isNzWrite c h) + occupied s0.n c h = 0 ∧ s.log.countP (isClear c h) = 2 ∧
    s.log.countP (isZeroClear env c h) = 2

/-- **A REPEATED KEY IS RECORDED AFTER A ZERO RECORD.** `DepositExists` (`N:160`) rejects only an
occupied key: two successive bridgehub requests at one key both succeed when the first is a
counterpart registration, which records `0`; the second, a deposit, then records its nonzero
hash there. -/
@[countermodel] def Properties.RepeatedKeyAccepted : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s s1 s2 : Sys) (a a' : Address) (c : ChainId) (h : Bytes32)
    (assetId : Bytes32) (data : Bytes),
    Step Checks.source env cfg s (.twoBridges a c .counterpart h) s1 ∧
    Step Checks.source env cfg s1 (.twoBridges a' c (.deposit assetId data) h) s2 ∧
    s1.n.depositHappened c h = 0 ∧
    s2.n.depositHappened c h = env.txDataHash ⟨a', assetId, data⟩ ∧
    env.txDataHash ⟨a', assetId, data⟩ ≠ 0

/-! ## Witnesses -/

/-- **ONE RUN MEETS THE RUN-LEVEL PREMISES OF (a)-(c).** From fresh, uninitialized storage, with every
source check, a prover that accepts exactly the queries naming a transaction's real status, and a
hash that is nonzero on both deposited triples and separates them: the run's log is exactly two
bridgehub deposits, by different senders at different keys, then a clear of the first with status
failure (its transaction failed) and a clear of the second with status success (its transaction
succeeded), both calling the router. In the proof the first is a recovery and the second a
confirmation. At the first key the count premises of `AtMostOneClearPerDeposit` hold with one
clear; each key's only deposit is of its claimed triple, so the no-collision premise of
`ClearCarriesDepositTriple` holds; the second clear is an instance of the first half of
`NoFailureClearOfSucceededDeposit`. -/
@[witness] def Properties.LedgerRunWitness : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (truth : ChainId → Bytes32 → Option TxStatus)
    (clF clS : Claim),
    (∀ q, env.accepts q ↔ truth q.chainId q.l2TxHash = some q.status) ∧
    s0.log = [] ∧ s0.n.initialized = false ∧ (∀ c h, s0.n.depositHappened c h = 0) ∧
    Reach Checks.source env cfg s0 s ∧ s.n.l1AssetRouter = cfg.router ∧
    s.log = [.write (.deposit clF.triple) clF.chainId clF.l2TxHash (env.txDataHash clF.triple),
      .write (.deposit clS.triple) clS.chainId clS.l2TxHash (env.txDataHash clS.triple),
      .clear clF cfg.router, .clear clS cfg.router] ∧
    clF.txStatus = .failure ∧ truth clF.chainId clF.l2TxHash = some .failure ∧
    clS.txStatus = .success ∧ truth clS.chainId clS.l2TxHash = some .success ∧
    clF.l2TxHash ≠ clS.l2TxHash ∧ clF.depositSender ≠ clS.depositSender ∧
    env.txDataHash clF.triple ≠ 0 ∧ env.txDataHash clS.triple ≠ 0 ∧
    env.txDataHash clF.triple ≠ env.txDataHash clS.triple

/-- **TWO DIFFERENT CLEARS OF ONE KEY, UNDER A SOUND PROVER.** From fresh storage, with every source
check and a prover that accepts exactly the real statuses, the run's log is a deposit, a clear of
it with status failure, the same deposit again at the same key, and a second clear with a different
claim, also with status failure: the premises of the second half of
`NoFailureClearOfSucceededDeposit` with `cl ≠ cl'`. -/
@[witness] def Properties.SameKeyClearedTwiceWitness : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (truth : ChainId → Bytes32 → Option TxStatus)
    (cl cl' : Claim),
    (∀ q, env.accepts q ↔ truth q.chainId q.l2TxHash = some q.status) ∧
    s0.log = [] ∧ (∀ c h, s0.n.depositHappened c h = 0) ∧ Reach Checks.source env cfg s0 s ∧
    s.log = [.write (.deposit cl.triple) cl.chainId cl.l2TxHash (env.txDataHash cl.triple),
      .clear cl cfg.router,
      .write (.deposit cl.triple) cl.chainId cl.l2TxHash (env.txDataHash cl.triple),
      .clear cl' cfg.router] ∧
    cl ≠ cl' ∧ cl.chainId = cl'.chainId ∧ cl.l2TxHash = cl'.l2TxHash ∧
    cl.txStatus = .failure ∧ cl'.txStatus = .failure ∧ env.txDataHash cl.triple ≠ 0

/-- **A RECORD THAT LEAVES.** A run of the source between two states: the key holds the claimed
triple's nonzero hash at the start, is `0` at the end, and the run's only event is a clear of that
claim: the premises of `RecordLeavesOnlyByPreimage`. -/
@[witness] def Properties.RecordLeavesOnlyByPreimageWitness : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s s' : Sys) (cl : Claim),
    Reach Checks.source env cfg s s' ∧
    s.n.depositHappened cl.chainId cl.l2TxHash = env.txDataHash cl.triple ∧
    env.txDataHash cl.triple ≠ 0 ∧ s'.n.depositHappened cl.chainId cl.l2TxHash = 0 ∧
    s'.log = s.log ++ [.clear cl cfg.router]

/-- **AN UNCLAIMED DEPOSIT, WITH OTHER ACTIVITY AFTER IT.** From fresh storage, a run of the source
meets every premise of `UnclaimedDepositRecoverable`. Two events follow the deposit (in the proof,
another depositor's deposit and its confirmation), and the recovery's caller is not the
depositor. -/
@[witness] def Properties.UnclaimedDepositRecoverableWitness : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s0 s : Sys) (pre post : List Event) (t : Triple) (c : ChainId)
    (h : Bytes32) (a : Address) (cl : Claim),
    s0.log = [] ∧ (∀ c' h', s0.n.depositHappened c' h' = 0) ∧ Reach Checks.source env cfg s0 s ∧
    s.log = pre ++ Event.write (.deposit t) c h (env.txDataHash t) :: post ∧
    env.txDataHash t ≠ 0 ∧ post.countP (isClear c h) = 0 ∧ post.length = 2 ∧
    s.n.paused = false ∧ s.n.l1AssetRouter = cfg.router ∧ s.routerPaused = false ∧
    ExternalSender cfg a ∧ a ≠ t.sender ∧
    cl.chainId = c ∧ cl.l2TxHash = h ∧ cl.triple = t ∧ env.accepts cl.asFailure.query

/-- **THE ONE-STEP PREMISES.** Five successive steps of the source: a bridgehub deposit with a
nonzero hash (`DepositRecordsClaimClears`), the owner's `pause` (a change of the pause flag:
`OnlyOwnerPausesOrConfigures`), the owner's `unpause` from the paused state with the record held
(`PausedStepKeepsRecords`), a recovery of that deposit (`DepositRecordsClaimClears`), and the owner's
`renounceOwnership`, a change of owner (`OnlyOwnerPausesOrConfigures`). -/
@[witness] def Properties.LedgerStepWitness : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s₁ s₂ s₃ s₄ s₅ s₆ : Sys) (caller o : Address) (c : ChainId)
    (a : Bytes32) (d : Bytes) (h : Bytes32) (cl : Claim),
    Step Checks.source env cfg s₁ (.twoBridges caller c (.deposit a d) h) s₂ ∧
    s₂.n.depositHappened c h ≠ 0 ∧
    Step Checks.source env cfg s₂ (.pause o) s₃ ∧ s₃.n.paused ≠ s₂.n.paused ∧
    Step Checks.source env cfg s₃ (.unpause o) s₄ ∧ s₃.n.paused = true ∧
    s₃.n.depositHappened c h ≠ 0 ∧ s₄.n.paused ≠ s₃.n.paused ∧
    Step Checks.source env cfg s₄ (.recover caller cl) s₅ ∧ cl.chainId = c ∧ cl.l2TxHash = h ∧
    Step Checks.source env cfg s₅ (.renounceOwnership o) s₆ ∧ s₆.n.owner ≠ s₅.n.owner

/-- **THE INITIALIZE-ONCE PREMISES.** From uninitialized storage, a successful `initialize` followed
by a run of the source that adds two events to the log (in the proof, a deposit and its
recovery). -/
@[witness] def Properties.InitializeOnlyOnceWitness : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s s' s'' : Sys) (a o : Address),
    s.n.initialized = false ∧ Step Checks.source env cfg s (.initialize a o) s' ∧
    Reach Checks.source env cfg s' s'' ∧ s''.log.length = s'.log.length + 2

/-- **THE ROUTER-PAUSED PREMISES.** A step of the source that changes the nullifier's pause flag, from
a state where the router is paused and is the nullifier's `l1AssetRouter` and a nonzero record is
held (in the proof, the nullifier owner's `pause`). -/
@[witness] def Properties.RouterPausedStepWitness : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s s' : Sys) (l : Label), Step Checks.source env cfg s l s' ∧
    s.routerPaused = true ∧ s.n.l1AssetRouter = cfg.router ∧
    (∃ c h, s.n.depositHappened c h ≠ 0) ∧ s'.n.paused ≠ s.n.paused

/-- **THE SET-ONCE PREMISES.** A run of the source that starts with all three addresses nonzero and
adds two events to the log (in the proof, a deposit and its recovery): the premises of
`ConfigSetOnce`. -/
@[witness] def Properties.ConfigSetOnceWitness : Prop :=
  ∃ (env : Env) (cfg : Cfg) (s s' : Sys), Reach Checks.source env cfg s s' ∧
    s.n.l1AssetRouter ≠ 0 ∧ s.n.l1NativeTokenVault ≠ 0 ∧ s.n.l1InteropHandler ≠ 0 ∧
    s'.log.length = s.log.length + 2

end Contracts.L1Nullifier
