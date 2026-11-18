import EraSpec.Contracts.MailboxFacet.Specs.PriorityTree

/-!
# Model: one chain's priority queue on L1 and on its gateway, out and back

Source: era-contracts `draft/v0.35.0` at `b17415d20`. Paths are relative to
`l1-contracts/contracts/`. The `PriorityTree` and `DynamicIncrementalMerkle` model this file
builds on (`EraSpec.Contracts.MailboxFacet.Specs.PriorityTree`) is copied, header aside, from
branch `origin/cov/mailbox` (commit `212f846`), which pinned `d9f678900`; both libraries are
byte-identical at `b17415d20`.

**This file is definitions only.** Statements are in
`EraSpec.Protocol.PriorityMirror.Properties.Mirror`, proofs in
`EraSpec.Protocol.PriorityMirror.Proofs.Mirror`.

At this commit `CHAIN_MIGRATIONS_ENABLED = false` (`common/Config.sol:320`) and
`ChainAssetHandlerBase.bridgeBurn`/`bridgeMint` carry `whenMigrationsEnabled`
(`core/chain-asset-handler/ChainAssetHandlerBase.sol:201`, `:365`), so no chain leaves L1. The
switch is the parameter `Params.migrationsEnabled`; the results about a migration are about the
kept machinery with the switch on.

## What is modelled

One chain `C` and the gateway `G` it may settle on. `C` has a diamond on L1 (`d1`) and, once
migrated, a second diamond on `G` (`d2`). Each copy has a priority tree (`PTree`), the
settlement-layer field (`settling` is `s.settlementLayer == address(0)`), the deposit-pause
timestamp, the diamond's `isFrozen` flag, and its batch counters and stored batch hashes.

* **L1 requests.** `MailboxFacet._requestL2Transaction` (`state-transition/chain-deps/facets/
  Mailbox.sol:232-285`) and `requestL2ServiceTransaction` (`:169-196`) both push the canonical
  hash into the L1 tree (`_writePriorityOp`, `:355-371`, which on L1 requires
  `!depositsPaused()`, `:362-365`) and, when `s.settlementLayer != address(0)`, call the
  gateway's L1 diamond (`:277-284`, `:188-195`). That call
  (`requestL2TransactionToGatewayMailbox`, `:110-130`) pushes a relay leaf into `G`'s L1 tree.
  The model keeps the relay leaves for `C` that `G` has not executed yet as the queue `relays`.
* **Relay execution on the gateway.** `G` executes its L1 tree in order. A relay leaf runs
  `InteropCenter.forwardTransactionOnGateway` (`interop/InteropCenter.sol:839-850`), which calls
  `bridgehubRequestL2TransactionOnGateway` on `C`'s gateway diamond (`Mailbox.sol:133-140`),
  pushing the hash into the gateway tree with no pause check. The call goes through the
  `DiamondProxy` fallback, which reverts on a frozen diamond for a freezable facet
  (`state-transition/chain-deps/DiamondProxy.sol:36`); the gateway `MailboxFacet` is freezable
  (`deploy-scripts/gateway/GatewayCTMDeployerHelper.sol:382`). A failed relay is consumed and
  not retried: the model drops it (`dropped`, a ghost).
* **Batch pipeline.** Commit, prove, execute and revert (`Committer.sol:72-77`,
  `Executor.sol:170-175`, `:215-220`, `:264-267`) all carry `onlySettlementLayer`
  (`ZKChainBase.sol:141-146`) and run through freezable facets. One step per copy covers them:
  it runs `PriorityTree.processBatch` (`Executor.sol:98`) and sets the batch counters and hashes
  to arbitrary values.
* **Migration out.** `Migrator.forwardedBridgeBurn` (`Migrator.sol:154-209`) on L1, with the
  chain asset handler's `_setMigrationInProgressOnL1` (`ChainAssetHandlerBase.sol:242`,
  `core/chain-asset-handler/L1ChainAssetHandler.sol:204-207`). On the gateway, the chain is
  deployed fresh: `ChainTypeManager.forwardedBridgeMint` (`state-transition/ChainTypeManager.sol:
  746-758`) runs `DiamondInit`, which calls `PriorityTree.setup` (`state-transition/chain-deps/
  DiamondInit.sol:137`), then `Migrator.forwardedBridgeMint` (`Migrator.sol:213-305`) runs
  `initFromCommitment` (`:290-291`). Back on L1, `L1ChainAssetHandler.bridgeConfirmTransferResult`
  (`L1ChainAssetHandler.sol:122-172`) clears `isMigrationInProgress` (`:163`), and the diamond's
  `forwardedBridgeConfirmTransferResult` (`Migrator.sol:309-333`) unpauses deposits
  unconditionally (`:316`) and on failure resets the settlement layer (`:332`).
* **Migration back.** `forwardedBridgeBurn` on the gateway copy, then `forwardedBridgeMint` on
  L1 with `_contractAlreadyDeployed = true`: the pause check (`:217-219`), the batch checks
  (`:247-266`), the historical-root check (`:270-276`), `NotMigrated` (`:280-282`) and
  `l1Reinit` (`:283`).
* **Pausing and freezing.** `pauseDepositsBeforeInitiatingMigration` and `unpauseDeposits`
  (`Migrator.sol:105-139`) on L1; `pauseDepositsOnGateway` (`:147-150`) on the gateway;
  `freezeDiamond`/`unfreezeDiamond` (`Admin.sol:616-639`, reached from
  `ChainTypeManager.freezeChain`/`unfreezeChain`, `ChainTypeManager.sol:577-586`) on either copy.
  Each acts on its own copy only. In the source the gateway pause runs when `G` executes the
  request an L1 pause sends while `C` is away (`Migrator.sol:122-127`,
  `L1ChainAssetHandler.sol:193-202`, `core/chain-asset-handler/L2ChainAssetHandler.sol:130-134`);
  the model makes it a free step with any timestamp.

## Ghost state

`log1` lists every leaf pushed into the L1 tree since `setup`, `leaves2` every leaf of the
gateway tree (the L1 leaves its commitment carried, then the relayed ones), `executed` every
leaf a `processBatch` of either copy advanced over, in order, and `dropped` the relays that
failed. The model's guards never read them.

## Modelling choices

* **Phases.** `phase` records where the migration stands and carries the in-flight data: the
  diamond as it was just before the L1 burn (`pre`) and the commitment each burn produced. It
  stands for `ChainAssetHandlerBase.migrationNumber` with the one round trip it allows
  (`ChainAssetHandlerBase.sol:274-279`, `common/Config.sol:329`) and for the transport of the
  two migration messages. A confirmation's status is the gateway transaction's actual outcome
  (the proof checked by `L1Nullifier.bridgeConfirmTransferResult` is modelled by its meaning).
* **Reject-only checks are omitted**: callers and admins, protocol versions, permanent rollup,
  priority mode, the settlement layer's CTM, the chain asset handler's own pauses and
  readiness, the gateway's whitelisting and caller checks on a relay
  (`Mailbox.sol:115-123`), fees, gas and the transaction filterer. Each only removes steps. In
  particular a relay that the gateway's L1 diamond refuses reverts the whole L1 request.
* **Relays come only from `C`'s L1 diamond.** `requestL2TransactionToGatewayMailbox` requires
  `getZKChain(_chainId) == msg.sender` (`Mailbox.sol:118-120`), and
  `forwardTransactionOnGateway` requires the virtual sender `SETTLEMENT_LAYER_RELAY_SENDER`
  (`InteropCenter.sol:130-133`, `common/Config.sol:219`), which only `_wrapRequest`
  (`Mailbox.sol:142-166`) produces. `C` is never a whitelisted settlement layer while away
  (`core/bridgehub/L1Bridgehub.sol:94-100`, `core/bridgehub/BridgehubBase.sol:416-418`), so its own
  `requestL2TransactionToGatewayMailbox` reverts (`Mailbox.sol:115-117`).
* **Who pushes into each tree.** `PriorityTree.push` has one caller, `_writePriorityOpHash`
  (`Mailbox.sol:373-378`). On the gateway copy only `bridgehubRequestL2TransactionOnGateway`
  reaches it: `requestL2ServiceTransaction` and `requestL2TransactionToGatewayMailbox` are
  `onlyL1` (`Mailbox.sol:69-74`), and `bridgehubRequestL2Transaction` is `onlyBridgehub`, which a
  diamond is sent only from `BridgehubBase._sendRequest`
  (`core/bridgehub/BridgehubBase.sol:366-381`), called only by `L1Bridgehub`
  (`core/bridgehub/L1Bridgehub.sol:172`, `:244`). On L1,
  `bridgehubRequestL2TransactionOnGateway` is `onlyInteropCenter`, `msg.sender ==
  L2_INTEROP_CENTER_ADDR` (`state-transition/chain-deps/facets/ZKChainBase.sol:99-104`); the model
  takes it that no L1 account has that address (no contract there and no key for it, an account
  premise also made by the topic `Protocol/PriorityRequests`), so every push into the L1 tree is a
  `request` step, relayed exactly when `C` is away.
* **Upgrades, diamond cuts and other chains are not steps.** Other chains' leaves in `G`'s L1
  tree do not touch `C`'s copies; the order of `G`'s other transactions relative to `C`'s relays
  is left free.
* **One clock.** `now` is the `block.timestamp` both layers read.
* **Freezable facets.** `MailboxFacet`, `ExecutorFacet` and `CommitterFacet` are freezable,
  `AdminFacet` and `MigratorFacet` are not, on L1
  (`deploy-scripts/ctm/DeployCTMUtils.s.sol:103-108`) and on the gateway
  (`deploy-scripts/gateway/GatewayCTMDeployerHelper.sol:358-411`). So a frozen
  copy refuses requests, relays and pipeline steps, and still runs the pause, burn, mint and
  confirmation steps.
* **Pipeline.** `processBatch` is the library's: with `calculateRootPaths` a parameter, nothing
  bounds the processed count by the pushed count. That bound is a run premise
  (`ConsistentProcessing`), as the library's own documentation relies on (`PriorityTree.sol:
  77-82`).
* **Storage before deployment.** The L1 diamond starts with the priority tree `DiamondInit`
  sets up (`DiamondInit.sol:137`) and zero batch storage. The gateway diamond's batch storage
  before the mint is zero too. `DiamondInit`'s genesis batch hash (`DiamondInit.sol:126`) is not
  modelled on either copy; batch storage enters the statements only through the burn and mint
  checks.
* **L2 execution is not modelled.** "Processed" means that a `processBatch` of a copy advanced
  that copy's `unprocessedIndex` over the leaf. Whether the chain's L2 can execute the operation
  at that position, and the binding of a batch's `itemHashes` to the tree, are outside the model.
-/

namespace Protocol.PriorityMirror

open Contracts.MailboxFacet

/-! ## Constants -/

/-- Deployment constants. -/
structure Params where
  /-- `Merkle.efficientHash`, `ZERO_LEAF_HASH` and `Merkle.calculateRootPaths`. -/
  tree : TreeParams
  /-- The `startIndex` of `C`'s L1 tree. `DiamondInit` sets it to the legacy queue's total
  (`DiamondInit.sol:137`), `0` on fresh storage; any value is allowed here. -/
  startIndex : ℕ
  /-- `PAUSE_DEPOSITS_TIME_WINDOW_START` (`common/Config.sol:271`, `:277`; `0` at this commit). -/
  pauseWindow : ℕ
  /-- `CHAIN_MIGRATION_TIME_WINDOW_START` (`common/Config.sol:275`, `:279`; `0` at this commit). -/
  migrationWindow : ℕ
  /-- `CHAIN_MIGRATIONS_ENABLED` (`common/Config.sol:320`; `false` at this commit). -/
  migrationsEnabled : Bool

/-! ## The incremental tree from its setup state -/

/-- The incremental tree as `setup` leaves fresh storage (`common/libraries/
DynamicIncrementalMerkle.sol:53-58`): no leaves, `_sides = [0]`, `_zeros = [ZERO_LEAF_HASH]`. -/
def setupTree (P : TreeParams) : PushTree :=
  { nextLeafIndex := 0, sides := [0], zeros := [P.zeroLeaf] }

/-- `DynamicIncrementalMerkle.push` of each leaf in order, from `t`; `none` if a push reverts. -/
def pushAll (h : NodeHash) : PushTree → List UInt256 → Option PushTree
  | t, [] => some t
  | t, x :: xs =>
      match t.push h x with
      | none => none
      | some (t', _) => pushAll h t' xs

/-- The root of the incremental tree whose leaves are `L`, pushed in order from the setup state. -/
def rootAfter (P : TreeParams) (L : List UInt256) : Option UInt256 :=
  (pushAll P.node (setupTree P) L).map PushTree.root

/-! ## One copy of the chain -/

/-- The batch counters and stored batch hashes (`totalBatchesCommitted`,
`totalBatchesVerified`, `totalBatchesExecuted`, `storedBatchHashes`). -/
structure Batches where
  committed : ℕ
  verified : ℕ
  executed : ℕ
  stored : ℕ → UInt256

/-- Zero batch storage. -/
def Batches.zero : Batches := ⟨0, 0, 0, fun _ => 0⟩

/-- The part of one diamond of `C` that the model reads and writes. -/
structure ChainDiamond where
  /-- `s.priorityTree`. -/
  tree : PTree
  /-- `s.settlementLayer == address(0)`: this copy is the one that settles. -/
  settling : Bool
  /-- `s.pausedDepositsTimestamp`. -/
  pausedTs : ℕ
  /-- `Diamond.DiamondStorage.isFrozen`. -/
  frozen : Bool
  /-- The batch counters and hashes. -/
  batches : Batches

/-- The modelled part of `ZKChainCommitment` (`common/Config.sol:234-261`): the three counters,
the batch hashes and the priority-tree commitment. -/
structure ChainCommitment where
  executed : ℕ
  verified : ℕ
  committed : ℕ
  batchHashes : List UInt256
  priorityTree : Commitment

/-- `prepareChainCommitment` (`Migrator.sol:339-375`): reverts unless
`executed ≤ verified ≤ committed`; the hashes are those of batches `executed .. committed`. -/
def prepare (d : ChainDiamond) : Option ChainCommitment :=
  if d.batches.executed ≤ d.batches.verified ∧ d.batches.verified ≤ d.batches.committed then
    some
      { executed := d.batches.executed
        verified := d.batches.verified
        committed := d.batches.committed
        batchHashes :=
          (List.range (d.batches.committed - d.batches.executed + 1)).map
            (fun i => d.batches.stored (d.batches.executed + i))
        priorityTree := d.tree.getCommitment }
  else none

/-- The batch part of `forwardedBridgeMint` (`Migrator.sol:230-266`): the counters are copied,
then checked (`:247-252`), the number of hashes must be `committed - executed + 1` (`:257-259`),
and the hashes are written from index `executed` on (`:263-266`). -/
def mintBatches (b : Batches) (c : ChainCommitment) : Option Batches :=
  if c.executed ≤ c.verified ∧ c.verified ≤ c.committed
      ∧ c.batchHashes.length = c.committed - c.executed + 1 then
    some
      { committed := c.committed
        verified := c.verified
        executed := c.executed
        stored := fun j =>
          if c.executed ≤ j ∧ j < c.executed + c.batchHashes.length then
            c.batchHashes.getD (j - c.executed) 0
          else b.stored j }
  else none

/-- `_commitment.priorityTree.sides[sides.length - 1]` (`Migrator.sol:272`). The model's guard
`sides ≠ []` stands for that index's revert on an empty array. -/
def lastSide (c : Commitment) : UInt256 := c.sides.getD (c.sides.length - 1) 0

/-- `_writePriorityOpHash` (`Mailbox.sol:373-378`): `PriorityTree.push`, then the checked
`getTotalPriorityTxs` (`PriorityTree.sol:42-44`). Its `- 1` cannot underflow after a push. The
request timestamp it records is not modelled. Both layers' writes are this function. -/
def mailboxWrite (P : TreeParams) (t : PTree) (h : UInt256) : Option PTree :=
  match t.push P h with
  | none => none
  | some t' =>
      match t'.getTotalPriorityTxs with
      | none => none
      | some _ => some t'

/-- `_isInDepositsPausedWindow` (`ZKChainBase.sol:229-232`): `timestamp != 0 &&
timestamp + window <= block.timestamp`. -/
def inPausedWindow (window ts now : ℕ) : Bool := decide (ts ≠ 0) && decide (ts + window ≤ now)

/-! ## The two layers -/

/-- Where the migration stands. -/
inductive Phase where
  /-- `C` settles on L1: initially, and after a failed move to the gateway. -/
  | onL1
  /-- The L1 burn has happened (`pre` is the L1 diamond just before it, `c` its commitment); the
  gateway transaction is in flight. -/
  | toGW (pre : ChainDiamond) (c : ChainCommitment)
  /-- The gateway transaction succeeded; L1 has not confirmed it. -/
  | gwMinted (pre : ChainDiamond)
  /-- The gateway transaction failed; L1 has not confirmed it. -/
  | gwFailed (pre : ChainDiamond)
  /-- Confirmed: `C` settles on the gateway. -/
  | onGW
  /-- The gateway burn has happened with commitment `c`; the message to L1 is in flight. -/
  | toL1 (c : ChainCommitment)
  /-- The L1 mint has happened: `C` settles on L1 again, for good. -/
  | back

/-- The diamond just before the L1 burn, while the move to the gateway awaits confirmation. -/
def Phase.preBurn : Phase → Option ChainDiamond
  | .toGW pre _ => some pre
  | .gwMinted pre => some pre
  | .gwFailed pre => some pre
  | _ => none

/-- Between an L1 burn and its confirmation. -/
def Phase.InFlight (p : Phase) : Prop := p.preBurn.isSome = true

/-- From the gateway copy's creation to `C`'s return to L1. -/
def Phase.Mirrored : Phase → Prop
  | .gwMinted _ => True
  | .onGW => True
  | .toL1 _ => True
  | _ => False

/-- The whole system. -/
structure St where
  /-- `C`'s L1 diamond. -/
  d1 : ChainDiamond
  /-- `C`'s gateway diamond, once deployed. -/
  d2 : Option ChainDiamond
  /-- `L1ChainAssetHandler.isMigrationInProgress[C]` (`L1ChainAssetHandler.sol:52`). -/
  inProgress : Bool
  /-- The relay leaves for `C` in `G`'s L1 tree that `G` has not executed, in order. -/
  relays : List UInt256
  /-- Where the migration stands. -/
  phase : Phase
  /-- `block.timestamp`. -/
  now : ℕ
  /-- Ghost: every leaf pushed into the L1 tree since `setup`, in order. -/
  log1 : List UInt256
  /-- Ghost: the gateway tree's leaves (those its initial commitment carried, then the relayed ones). -/
  leaves2 : List UInt256
  /-- Ghost: every leaf a `processBatch` of either copy advanced over, in order. -/
  executed : List UInt256
  /-- Ghost: the relays that failed on the gateway. -/
  dropped : List UInt256

/-- `depositsPaused()` on L1 (`Mailbox.sol:347-352`): the pause window has started, or the chain
asset handler has a migration of `C` in progress. -/
def depositsPausedL1 (P : Params) (s : St) : Bool :=
  inPausedWindow P.pauseWindow s.d1.pausedTs s.now || s.inProgress

/-- A fresh diamond as `DiamondInit` leaves it (`DiamondInit.sol:137`), with zero batch storage. -/
def freshDiamond (P : TreeParams) (startIndex : ℕ) : ChainDiamond :=
  { tree := emptyTree.setup P startIndex, settling := true, pausedTs := 0, frozen := false,
    batches := Batches.zero }

/-- The start: `C` freshly deployed on L1, nothing pushed, no gateway copy. -/
def initial (P : Params) : St :=
  { d1 := freshDiamond P.tree P.startIndex, d2 := none, inProgress := false, relays := [],
    phase := .onL1, now := 0, log1 := [], leaves2 := [], executed := [], dropped := [] }

/-! ## Steps -/

/-- One action. -/
inductive Op where
  /-- An L1 request to `C` with canonical hash `h`. -/
  | request (h : UInt256)
  /-- A batch-pipeline call on the L1 copy: `processBatch` with `info`, batch storage set to `b`. -/
  | l1Pipeline (info : BatchInfo) (b : Batches)
  /-- `pauseDepositsBeforeInitiatingMigration` (`Migrator.sol:105-129`). -/
  | pauseL1
  /-- `unpauseDeposits` (`Migrator.sol:132-139`). -/
  | unpauseL1
  /-- `freezeDiamond` on the L1 copy. -/
  | freezeL1
  /-- `unfreezeDiamond` on the L1 copy. -/
  | unfreezeL1
  /-- The L1 burn. -/
  | l1Burn
  /-- The gateway executes the migration transaction successfully. -/
  | gwMint
  /-- The gateway's migration transaction fails. -/
  | gwMintFails
  /-- `bridgeConfirmTransferResult` on L1 with the given status. -/
  | confirm (success : Bool)
  /-- The gateway executes the next relay leaf for `C`. -/
  | relay
  /-- A batch-pipeline call on the gateway copy. -/
  | gwPipeline (info : BatchInfo) (b : Batches)
  /-- `pauseDepositsOnGateway(ts)` (`Migrator.sol:147-150`). -/
  | gwPause (ts : ℕ)
  /-- `freezeDiamond` on the gateway copy. -/
  | freezeGW
  /-- `unfreezeDiamond` on the gateway copy. -/
  | unfreezeGW
  /-- The gateway burn. -/
  | gwBurn
  /-- The L1 mint. -/
  | l1Mint
  /-- Time passes. -/
  | tick (dt : ℕ)

/-- The `len` leaves of `L` from relative index `u`: what a `processBatch` of `len` items at
`unprocessedIndex = u` advances over. -/
def slice (L : List UInt256) (u len : ℕ) : List UInt256 := (L.drop u).take len

/-- An L1 request: the L1 copy's `MailboxFacet` is not frozen, deposits are not paused, the push
succeeds; while `C` is away the relay is queued in the same transaction. -/
def stepRequest (P : Params) (s : St) (h : UInt256) : Option St :=
  if s.d1.frozen = false ∧ depositsPausedL1 P s = false then
    match mailboxWrite P.tree s.d1.tree h with
    | none => none
    | some t =>
        some { s with
          d1 := { s.d1 with tree := t }
          log1 := s.log1 ++ [h]
          relays := if s.d1.settling then s.relays else s.relays ++ [h] }
  else none

/-- The L1 batch pipeline: only on the settling, unfrozen copy. -/
def stepL1Pipeline (P : Params) (s : St) (info : BatchInfo) (b : Batches) : Option St :=
  if s.d1.settling = true ∧ s.d1.frozen = false then
    match s.d1.tree.processBatch P.tree info with
    | none => none
    | some t =>
        some { s with
          d1 := { s.d1 with tree := t, batches := b }
          executed := s.executed ++ slice s.log1 s.d1.tree.unprocessedIndex info.itemHashes.length }
  else none

/-- `pauseDepositsBeforeInitiatingMigration` (`Migrator.sol:105-129`): requires no pause
(`:109`); the timestamp is `block.timestamp`, or `block.timestamp - PAUSE_DEPOSITS_TIME_WINDOW_START`
(checked) when nothing was ever pushed (`:113-120`); while `C` is away it requires a nonzero total
(`:122-123`). The request it then sends to the gateway is the free step `gwPause`. -/
def stepPauseL1 (P : Params) (s : St) : Option St :=
  if s.d1.pausedTs = 0 then
    match s.d1.tree.getTotalPriorityTxs with
    | none => none
    | some total =>
        if s.d1.settling = false ∧ total = 0 then none
        else if total = 0 then
          if P.pauseWindow ≤ s.now then
            some { s with d1 := { s.d1 with pausedTs := s.now - P.pauseWindow } }
          else none
        else some { s with d1 := { s.d1 with pausedTs := s.now } }
  else none

/-- `unpauseDeposits` (`Migrator.sol:132-139`): requires a pause and no migration in progress. -/
def stepUnpauseL1 (s : St) : Option St :=
  if s.d1.pausedTs ≠ 0 ∧ s.inProgress = false then
    some { s with d1 := { s.d1 with pausedTs := 0 } }
  else none

/-- `freezeDiamond` on L1 (`Admin.sol:616-626`). -/
def stepFreezeL1 (s : St) : Option St :=
  if s.d1.frozen = false then some { s with d1 := { s.d1 with frozen := true } } else none

/-- `unfreezeDiamond` on L1 (`Admin.sol:629-639`). -/
def stepUnfreezeL1 (s : St) : Option St :=
  if s.d1.frozen = true then some { s with d1 := { s.d1 with frozen := false } } else none

/-- The L1 burn (`Migrator.sol:154-209` under `ChainAssetHandlerBase.bridgeBurn`): migrations
enabled, `C` settles on L1 (`:162-164`), the tree is fully processed (`:170`), the migration
window is open (`:172-176`), every committed batch is executed (`:203-205`). It writes the
settlement layer (`:207`), builds the commitment (`:208`) and marks the migration in progress
(`L1ChainAssetHandler.sol:206`). -/
def stepL1Burn (P : Params) (s : St) : Option St :=
  match s.phase with
  | .onL1 =>
      if P.migrationsEnabled = true ∧ s.d1.settling = true ∧ s.d1.tree.getSize = some 0
          ∧ inPausedWindow P.migrationWindow s.d1.pausedTs s.now = true
          ∧ s.d1.batches.committed = s.d1.batches.executed then
        match prepare s.d1 with
        | none => none
        | some c =>
            some { s with
              d1 := { s.d1 with settling := false }
              inProgress := true
              phase := .toGW s.d1 c }
      else none
  | _ => none

/-- The gateway's migration transaction, successful: a fresh diamond (`DiamondInit`'s `setup`
with start index `0` on fresh storage), then `initFromCommitment` (`Migrator.sol:290-291`) and the
batch writes; settlement layer `0` (`:299`), deposits unpaused (`:302`). -/
def stepGwMint (P : Params) (s : St) : Option St :=
  match s.phase with
  | .toGW pre c =>
      if P.migrationsEnabled = true ∧ s.d2.isNone = true then
        match (emptyTree.setup P.tree 0).initFromCommitment P.tree c.priorityTree,
            mintBatches Batches.zero c with
        | some t, some b =>
            some { s with
              d2 := some { tree := t, settling := true, pausedTs := 0, frozen := false, batches := b }
              leaves2 := s.log1
              phase := .gwMinted pre }
        | _, _ => none
      else none
  | _ => none

/-- The gateway's migration transaction fails: nothing changes on the gateway. -/
def stepGwMintFails (s : St) : Option St :=
  match s.phase with
  | .toGW pre _ => some { s with phase := .gwFailed pre }
  | _ => none

/-- `bridgeConfirmTransferResult` on L1 (`L1ChainAssetHandler.sol:122-172`,
`Migrator.sol:309-333`): clears `isMigrationInProgress` (`:163`), unpauses deposits (`:316`); on
failure requires the chain to be away (`:324-326`) and resets the settlement layer (`:332`). -/
def stepConfirm (s : St) (success : Bool) : Option St :=
  match s.phase, success with
  | .gwMinted _, true =>
      some { s with inProgress := false, d1 := { s.d1 with pausedTs := 0 }, phase := .onGW }
  | .gwFailed _, false =>
      if s.d1.settling = false then
        some { s with
          inProgress := false
          d1 := { s.d1 with pausedTs := 0, settling := true }
          phase := .onL1 }
      else none
  | _, _ => none

/-- The gateway executes the next relay leaf (`InteropCenter.sol:839-850`, `Mailbox.sol:133-140`).
It pushes into the gateway tree unless the gateway diamond is absent (`InteropCenter.sol:845-847`),
frozen (`DiamondProxy.sol:36`) or the push reverts; then the relay is consumed and dropped. -/
def stepRelay (P : Params) (s : St) : Option St :=
  match s.relays with
  | [] => none
  | h :: rest =>
      match s.d2 with
      | none => some { s with relays := rest, dropped := s.dropped ++ [h] }
      | some d =>
          if d.frozen = true then some { s with relays := rest, dropped := s.dropped ++ [h] }
          else
            match mailboxWrite P.tree d.tree h with
            | none => some { s with relays := rest, dropped := s.dropped ++ [h] }
            | some t =>
                some { s with
                  relays := rest
                  d2 := some { d with tree := t }
                  leaves2 := s.leaves2 ++ [h] }

/-- The gateway batch pipeline: only on the settling, unfrozen gateway copy. -/
def stepGwPipeline (P : Params) (s : St) (info : BatchInfo) (b : Batches) : Option St :=
  match s.d2 with
  | none => none
  | some d =>
      if d.settling = true ∧ d.frozen = false then
        match d.tree.processBatch P.tree info with
        | none => none
        | some t =>
            some { s with
              d2 := some { d with tree := t, batches := b }
              executed := s.executed ++ slice s.leaves2 d.tree.unprocessedIndex info.itemHashes.length }
      else none

/-- `pauseDepositsOnGateway(ts)` (`Migrator.sol:147-150`). -/
def stepGwPause (s : St) (ts : ℕ) : Option St :=
  match s.d2 with
  | none => none
  | some d => some { s with d2 := some { d with pausedTs := ts } }

/-- `freezeDiamond` on the gateway copy. -/
def stepFreezeGW (s : St) : Option St :=
  match s.d2 with
  | none => none
  | some d => if d.frozen = false then some { s with d2 := some { d with frozen := true } } else none

/-- `unfreezeDiamond` on the gateway copy. -/
def stepUnfreezeGW (s : St) : Option St :=
  match s.d2 with
  | none => none
  | some d => if d.frozen = true then some { s with d2 := some { d with frozen := false } } else none

/-- The gateway burn: the checks of the L1 burn, on the gateway copy. -/
def stepGwBurn (P : Params) (s : St) : Option St :=
  match s.phase, s.d2 with
  | .onGW, some d =>
      if P.migrationsEnabled = true ∧ d.settling = true ∧ d.tree.getSize = some 0
          ∧ inPausedWindow P.migrationWindow d.pausedTs s.now = true
          ∧ d.batches.committed = d.batches.executed then
        match prepare d with
        | none => none
        | some c => some { s with d2 := some { d with settling := false }, phase := .toL1 c }
      else none
  | _, _ => none

/-- The L1 mint (`Migrator.sol:213-305`, `_contractAlreadyDeployed = true`): deposits paused
(`:217-219`), the batch checks and writes (`:230-266`), the commitment's root is historical in the
L1 tree (`:270-276`), the chain is away (`:280-282`) and `l1Reinit` passes (`:283`). Settlement
layer `0` (`:299`), deposits unpaused (`:302`). -/
def stepL1Mint (P : Params) (s : St) : Option St :=
  match s.phase with
  | .toL1 c =>
      if P.migrationsEnabled = true ∧ s.d1.pausedTs ≠ 0 ∧ c.priorityTree.sides ≠ []
          ∧ s.d1.tree.isHistoricalRoot (lastSide c.priorityTree) = true
          ∧ s.d1.settling = false then
        match mintBatches s.d1.batches c, s.d1.tree.l1Reinit c.priorityTree with
        | some b, some t =>
            some { s with
              d1 := { s.d1 with tree := t, batches := b, settling := true, pausedTs := 0 }
              phase := .back }
        | _, _ => none
      else none
  | _ => none

/-- One step; `none` is a revert. -/
def step (P : Params) (s : St) : Op → Option St
  | .request h => stepRequest P s h
  | .l1Pipeline info b => stepL1Pipeline P s info b
  | .pauseL1 => stepPauseL1 P s
  | .unpauseL1 => stepUnpauseL1 s
  | .freezeL1 => stepFreezeL1 s
  | .unfreezeL1 => stepUnfreezeL1 s
  | .l1Burn => stepL1Burn P s
  | .gwMint => stepGwMint P s
  | .gwMintFails => stepGwMintFails s
  | .confirm success => stepConfirm s success
  | .relay => stepRelay P s
  | .gwPipeline info b => stepGwPipeline P s info b
  | .gwPause ts => stepGwPause s ts
  | .freezeGW => stepFreezeGW s
  | .unfreezeGW => stepUnfreezeGW s
  | .gwBurn => stepGwBurn P s
  | .l1Mint => stepL1Mint P s
  | .tick dt => some { s with now := s.now + dt }

/-! ## Runs and their premises -/

/-- Successful steps from `s` to `t`, each allowed by `ok`. -/
inductive Steps (P : Params) (ok : St → Op → Prop) : St → St → Prop
  | refl (s : St) : Steps P ok s s
  | tail {s t u : St} (op : Op) : Steps P ok s t → ok t op → step P t op = some u → Steps P ok s u

/-- Reachable from `initial P` by steps allowed by `ok`. -/
def Reach (P : Params) (ok : St → Op → Prop) (s : St) : Prop := Steps P ok (initial P) s

/-- No premise on steps. -/
def Unrestricted : St → Op → Prop := fun _ _ => True

/-- A batch processes only leaves its copy holds: the library's `processBatch` checks a root
only, and `PriorityTree.sol:77-82` relies on the items being real priority transactions. -/
def ConsistentProcessing (s : St) : Op → Prop
  | .l1Pipeline info _ =>
      s.d1.tree.unprocessedIndex + info.itemHashes.length ≤ s.d1.tree.tree.nextLeafIndex
  | .gwPipeline info _ =>
      ∀ d, s.d2 = some d →
        d.tree.unprocessedIndex + info.itemHashes.length ≤ d.tree.tree.nextLeafIndex
  | _ => True

/-- FREEZE-ORDER: until the L1 mint, no relay for `C` executes on the gateway while the gateway
copy is frozen. After the L1 mint a relay may execute on a frozen gateway copy. -/
def FreezeOrder (s : St) : Op → Prop
  | .relay => s.phase = .back ∨ ∀ d, s.d2 = some d → d.frozen = false
  | _ => True

/-- Both premises. -/
def Honest (s : St) (op : Op) : Prop := ConsistentProcessing s op ∧ FreezeOrder s op

/-! ## Witness data

Inside this namespace `wNode` and `wParams` are the definitions below; the library model's own
witness data (`Contracts.MailboxFacet.wNode`, `Contracts.MailboxFacet.wParams`) is not used here. -/

/-- Witness node hash: `2a + 3b + 1` in `uint256`. -/
def wNode : NodeHash := fun a b => 2 * a + 3 * b + 1

/-- Witness tree parameters before `calculateRootPaths` is fixed: padding leaf `7`. -/
def wTreeBase : TreeParams := { node := wNode, zeroLeaf := 7, rootPaths := fun _ _ _ _ => none }

/-- Witness `calculateRootPaths`: `leftPath` carries all leaves before `startIndex`, and the result
is the root of the tree after those leaves and the items. It stands for a correct path
computation; nothing is assumed about the real function. -/
def wRootPaths : RootPaths := fun left _ start items =>
  if left.length = start then rootAfter wTreeBase (left ++ items) else none

/-- Witness tree parameters. -/
def wTree : TreeParams := { wTreeBase with rootPaths := wRootPaths }

/-- Witness constants: start index `5`, both windows `0` as at this commit, migrations enabled. -/
def wParams : Params :=
  { tree := wTree, startIndex := 5, pauseWindow := 0, migrationWindow := 0,
    migrationsEnabled := true }

/-- A degenerate node hash for the collision witness: every node hashes to `0`. -/
def cNode : NodeHash := fun _ _ => 0

/-- Collision-witness tree parameters. -/
def cTree : TreeParams :=
  { node := cNode, zeroLeaf := 7,
    rootPaths := fun left _ start items =>
      if left.length = start then
        rootAfter { node := cNode, zeroLeaf := 7, rootPaths := fun _ _ _ _ => none } (left ++ items)
      else none }

/-- Collision-witness constants. -/
def cParams : Params := { wParams with tree := cTree }

/-- Witness constants with migrations disabled, as at this commit. -/
def wParamsDisabled : Params := { wParams with migrationsEnabled := false }

/-- A batch whose items are `items`, with the earlier leaves `left` in the left path (the witness
`calculateRootPaths` reads them). -/
def wBatch (left items : List UInt256) : BatchInfo := { leftPath := left, rightPath := [], itemHashes := items }

/-- The first part of an honest round trip. Before migrating, op `11` is pushed and processed on
L1. The gateway copy is frozen while relay `1` is pending and unfrozen before it executes. Ops `1`,
`2` are relayed and processed on the gateway. L1 deposits are paused (in the source this queues the
gateway pause request in the gateway's L1 tree) and unpaused again; op `3` is requested, so relay
`3` is queued behind that request; the gateway pause executes, and the gateway burn goes through
with relay `3` still pending. -/
def honestRun : List Op :=
  [ .tick 1, .request 11, .l1Pipeline (wBatch [] [11]) Batches.zero, .pauseL1, .l1Burn,
    .gwMint, .confirm true,
    .freezeGW, .request 1, .unfreezeGW, .relay,
    .request 2, .relay, .gwPipeline (wBatch [11] [1, 2]) Batches.zero,
    .pauseL1, .unpauseL1, .request 3, .gwPause 1, .gwBurn ]

/-- The return, after `honestRun`. Relay `3` executes on the gateway copy, which no longer settles;
op `4` is requested and relayed while L1 deposits are open; deposits are paused and the L1 mint goes
through. L1 then processes ops `3` and `4`. The idle gateway copy is frozen, and relay `4` executes
on it and is dropped. -/
def honestReturn : List Op :=
  [ .relay, .request 4, .pauseL1, .l1Mint,
    .l1Pipeline (wBatch [11, 1, 2] [3, 4]) Batches.zero, .freezeGW, .relay ]

/-- A failed move to the gateway: op `11` is pushed and processed, the L1 burn happens, the
L1 copy is frozen during the window, the gateway transaction fails. -/
def failedRun : List Op :=
  [ .tick 1, .request 11, .l1Pipeline (wBatch [] [11]) Batches.zero, .pauseL1, .l1Burn,
    .freezeL1, .gwMintFails ]

/-- A run breaking FREEZE-ORDER in which nothing is lost. Op `1` is relayed and processed on the
gateway; the gateway copy is frozen, op `2` is requested and its relay is dropped; L1 deposits are
paused, the gateway pause executes and the frozen gateway copy burns. The L1 mint goes through, and
L1 processes op `2`. -/
def recoveredRun : List Op :=
  [ .tick 1, .request 11, .l1Pipeline (wBatch [] [11]) Batches.zero, .pauseL1, .l1Burn,
    .gwMint, .confirm true,
    .request 1, .relay, .gwPipeline (wBatch [11] [1]) Batches.zero,
    .freezeGW, .request 2, .relay, .pauseL1, .gwPause 1, .gwBurn,
    .l1Mint, .l1Pipeline (wBatch [11, 1] [2]) Batches.zero ]

/-- A run breaking FREEZE-ORDER once. The gateway copy is frozen while relay `2` is pending, relay
`2` executes and is dropped, the copy is unfrozen, and op `3` is relayed; the gateway processes ops
`1` and `3`, L1 deposits are paused, the gateway pause executes and the gateway burns. -/
def droppedRun : List Op :=
  [ .tick 1, .request 11, .l1Pipeline (wBatch [] [11]) Batches.zero, .pauseL1, .l1Burn,
    .gwMint, .confirm true,
    .request 1, .relay, .freezeGW, .request 2, .relay, .unfreezeGW, .request 3, .relay,
    .gwPipeline (wBatch [11] [1, 3]) Batches.zero, .pauseL1, .gwPause 1, .gwBurn ]

end Protocol.PriorityMirror
