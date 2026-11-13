import EraSpec.Core.Word

/-!
# Model: a chain migrating L1 → settlement layer → L1, end to end

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.ChainMigration.Properties.*`, proofs in
`EraSpec.Protocol.ChainMigration.Proofs.*`.

Source paths are relative to `l1-contracts/contracts/` in era-contracts `draft/v0.35.0` at
`d9f678900e1bc8286412b78f56d4a9f443983c29`.

## What one migration is, in the source

*L1 → settlement layer `x`.*  The chain admin calls
`L1Bridgehub.requestL2TransactionTwoBridges` towards chain `x`
(`core/bridgehub/L1Bridgehub.sol:200-265`) with the asset router as second bridge.
`AssetRouterBase._bridgehubDeposit` calls the asset's handler
(`bridge/asset-router/AssetRouterBase.sol:118-183`), which for a CTM asset is the chain
asset handler: `ChainAssetHandlerBase.bridgeBurn`
(`core/chain-asset-handler/ChainAssetHandlerBase.sol:188-254`).  It calls
`BridgehubBase.forwardedBridgeBurnSetSettlementLayer` (`core/bridgehub/BridgehubBase.sol:403-421`),
`ChainTypeManager.forwardedBridgeBurn` (`state-transition/ChainTypeManager.sol:721-741`) and
the chain's `Migrator.forwardedBridgeBurn`
(`state-transition/chain-deps/facets/Migrator.sol:154-209`), then
`L1ChainAssetHandler._recordMigrationToSL`
(`core/chain-asset-handler/L1ChainAssetHandler.sol:277-299`).  The bridgehub sends the
priority transaction to `x` and has the nullifier store the deposit's data hash under the
transaction hash (`L1Bridgehub.sol:260-264`, `bridge/L1Nullifier.sol:155-163`).

*On `x`.*  The priority transaction runs `L2AssetRouter.finalizeDeposit`, which calls
`ChainAssetHandlerBase.bridgeMint` (`ChainAssetHandlerBase.sol:361-420`):
`BridgehubBase.forwardedBridgeMint` (`BridgehubBase.sol:432-453`), then for a chain with no
diamond on `x` `ChainTypeManager.forwardedBridgeMint` (`ChainTypeManager.sol:746-758`), then
`Migrator.forwardedBridgeMint` (`Migrator.sol:213-305`).  The transaction succeeds or fails
as a whole; its status is an L2 → L1 log.

*Back on L1, for the L1 → `x` transaction.*  Anyone calls
`L1Nullifier.bridgeConfirmTransferResult` with a status and a proof of it
(`L1Nullifier.sol:166-248`).  It reaches `L1ChainAssetHandler.bridgeConfirmTransferResult`
(`L1ChainAssetHandler.sol:122-172`) through `L1AssetRouter.bridgeConfirmTransferResult`
(`bridge/asset-router/L1AssetRouter.sol:306-325`).  With status `Failure` this undoes the
migration: `BridgehubBase.forwardedBridgeConfirmTransferResult` (`BridgehubBase.sol:459-468`)
and `Migrator.forwardedBridgeConfirmTransferResult` (`Migrator.sol:309-333`).

*`x` → L1.*  `bridgeBurn` runs on `x` (same code, `block.chainid != L1` branches), and the
message is finalized on L1 by `bridgeMint` (same code, `block.chainid == L1` branches,
`L1ChainAssetHandler._recordMigrationFromSL`, `L1ChainAssetHandler.sol:304-320`).

## State

One `State` holds every layer.  Fields indexed `layer chain` are the storage of the layer's
`BridgehubBase`, `ChainAssetHandlerBase`, CTM and the chain's diamond on that layer; the index
`P.l1` is L1 itself and every other index is a ZK chain acting as a settlement layer.  The
remaining storage fields are L1-only contracts.  The last seven fields are transport: the
L1 → `x` priority transactions and their execution status, and the `x` → L1 messages.

## Model boundaries (see the README for the full list)

* `registered y c` stands for both `zkChainMap` containing `c` and `chainTypeManager[c] != 0`
  on layer `y`; the two are written together (`L1Bridgehub.sol:116-131`,
  `BridgehubBase.sol:446`, `ChainAssetHandlerBase.sol:405`).
* A CTM is identified by its asset id: `chainAsset y c` is `ctmAssetIdFromChainId(c)`
  (`BridgehubBase.sol:349-355`), and `ctmPV y a` is the `protocolVersion` of
  `ctmAssetIdToAddress[a]` on layer `y` (`none` when that address is zero).
* A diamond's `s.settlementLayer` address is modelled by the chain id it stands for:
  `none` is `address(0)`, `some x` is the diamond of chain `x` on L1
  (`ChainAssetHandlerBase.sol:268-270`, checked in `Migrator.sol:181-189`), and `some P.l1` is
  `L1_SETTLEMENT_LAYER_VIRTUAL_ADDRESS`.
* Transaction hashes and message ids are fresh counters.
* The proof checked by `MessageRootBase.proveL1ToL2TransactionStatusShared` is modelled by
  its meaning (`TxStatusProved`), and the L1 interop handler's check that a withdrawal bundle
  was sent and is executed once by `outbox` / `consumed`.
* Callers, pauses, deposit pausing and its time window, priority trees, batch counters and
  batch hashes, base-token origin data, and the message root are not modelled.  Each omitted
  check only removes steps.
-/

namespace Protocol.ChainMigration

/-- Chain ids (`uint256`). -/
abbrev Chain := UInt256

/-- Asset ids (`bytes32`): a CTM's asset id, or a token's. -/
abbrev Asset := UInt256

/-- The canonical hash of an L1 → settlement-layer priority transaction, as a fresh id. -/
abbrev TxId := ℕ

/-- A settlement-layer → L1 withdrawal message, as a fresh id. -/
abbrev MsgId := ℕ

/-- What `DataEncoding.encodeTxDataHash` hashes for a chain migration
(`common/libraries/DataEncoding.sol:159-170`): the original caller, the CTM asset id, and
the `BridgehubBurnCTMAssetData` (`core/bridgehub/IBridgehubBase.sol:51-55`), whose `ctmData`
is the new admin (`ChainTypeManager.sol:728`) and whose `chainData` is a protocol version
(`Migrator.sol:192`). -/
structure DepositRecord where
  sender : UInt256
  asset : Asset
  chain : Chain
  admin : UInt256
  version : UInt256

/-- The modelled part of `BridgehubMintCTMAssetData` (`IBridgehubBase.sol:42-49`) with its
asset id.  `layer` is transport data: the destination of an L1 → settlement-layer transaction,
or the chain that sent a settlement-layer → L1 message.  `version` is the protocol version in
`ctmData` (`ChainTypeManager.sol:740`).  The struct has no amount of any token. -/
structure MintMsg where
  layer : Chain
  asset : Asset
  chain : Chain
  base : Asset
  version : UInt256
  migNum : ℕ

/-- Deployment constants. -/
structure Params where
  /-- `L1_CHAIN_ID`. -/
  l1 : Chain
  /-- `_getChainMigrationsEnabled()` (`ChainAssetHandlerBase.sol:165-167`).  At the pin it is
  the constant `CHAIN_MIGRATIONS_ENABLED = false` (`common/Config.sol:320`). -/
  migrationsEnabled : Bool
  /-- `DataEncoding.encodeTxDataHash`. -/
  dataHash : DepositRecord → UInt256
  /-- `INTEROP_POOL_CHAIN_ID` (`common/Config.sol:37`). -/
  pool : Chain
  /-- `L1NativeTokenVault.chainBalanceBackfill` (`bridge/ntv/L1NativeTokenVault.sol:102`),
  held constant. -/
  backfill : Chain → Asset → ℕ
  /-- `L1NativeTokenVault.chainBalanceBackfillPending` (`L1NativeTokenVault.sol:108`), held
  constant. -/
  capExempt : Chain → Bool

/-- Point update of a one-argument map. -/
def set1 {α β : Type} [DecidableEq α] (f : α → β) (a : α) (v : β) : α → β :=
  fun a' => if a' = a then v else f a'

/-- Point update of a two-argument map. -/
def set2 {α β γ : Type} [DecidableEq α] [DecidableEq β] (f : α → β → γ) (a : α) (b : β)
    (v : γ) : α → β → γ :=
  fun a' b' => if a' = a ∧ b' = b then v else f a' b'

/-- The modelled storage of every layer, and the messages between them. -/
structure State where
  /-- `zkChainMap` contains the chain (`BridgehubBase.sol:344-347`). -/
  registered : Chain → Chain → Bool
  /-- `BridgehubBase.settlementLayer` (`BridgehubBase.sol:109`). -/
  bhSL : Chain → Chain → Chain
  /-- `ctmAssetIdFromChainId` (`BridgehubBase.sol:349-355`). -/
  chainAsset : Chain → Chain → Asset
  /-- `BridgehubBase.baseTokenAssetId` (`BridgehubBase.sol:96`). -/
  baseAsset : Chain → Chain → Asset
  /-- The protocol version of the CTM the layer maps the asset id to. -/
  ctmPV : Chain → Asset → Option UInt256
  /-- The chain's diamond on the layer: `s.settlementLayer`
  (`state-transition/chain-deps/ZKChainStorage.sol:218`). -/
  diamondSL : Chain → Chain → Option Chain
  /-- The chain's diamond on the layer: `s.protocolVersion`. -/
  diamondPV : Chain → Chain → UInt256
  /-- `ChainAssetHandlerBase.migrationNumber` (`ChainAssetHandlerBase.sol:110`). -/
  migNum : Chain → Chain → ℕ
  /-- L1: `whitelistedSettlementLayers` (`BridgehubBase.sol:115`). -/
  whitelisted : Chain → Bool
  /-- L1: `_migrationInterval[c][1].isActive` (`L1ChainAssetHandler.sol:291-298`). -/
  intervalActive : Chain → Bool
  /-- L1: `_migrationInterval[c][1].settlementLayerChainId`. -/
  intervalSL : Chain → Chain
  /-- L1: `L1Nullifier.depositHappened` (`L1Nullifier.sol:67-69`); `0` is "no deposit". -/
  depositHappened : Chain → TxId → UInt256
  /-- L1: `L1NativeTokenVault.chainTotalDeposited` (`L1NativeTokenVault.sol:96`). -/
  deposited : Chain → Asset → ℕ
  /-- L1: `L1NativeTokenVault.chainTotalWithdrawn` (`L1NativeTokenVault.sol:99`). -/
  withdrawn : Chain → Asset → ℕ
  /-- Transport: the next priority-transaction id. -/
  nextTx : TxId
  /-- Transport: the mint data an L1 → settlement-layer transaction carries. -/
  txPayload : TxId → Option MintMsg
  /-- Transport: the transaction's status once its destination executed it. -/
  txOutcome : TxId → Option Bool
  /-- Ghost: the record whose hash `depositHappened` holds for the transaction. -/
  txRecord : TxId → Option DepositRecord
  /-- Transport: the next message id. -/
  nextMsg : MsgId
  /-- Transport: the mint data of a settlement-layer → L1 message. -/
  outbox : MsgId → Option MintMsg
  /-- Transport: the message was executed on L1 (the L1 interop handler's bundle status). -/
  consumed : MsgId → Bool

/-- The state before any chain exists.  L1 is whitelisted as a settlement layer by
`BridgehubBase._initializeInner` (`BridgehubBase.sol:169-172`). -/
def init (P : Params) : State where
  registered := fun _ _ => false
  bhSL := fun _ _ => 0
  chainAsset := fun _ _ => 0
  baseAsset := fun _ _ => 0
  ctmPV := fun _ _ => none
  diamondSL := fun _ _ => none
  diamondPV := fun _ _ => 0
  migNum := fun _ _ => 0
  whitelisted := fun x => decide (x = P.l1)
  intervalActive := fun _ => false
  intervalSL := fun _ => 0
  depositHappened := fun _ _ => 0
  deposited := fun _ _ => 0
  withdrawn := fun _ _ => 0
  nextTx := 0
  txPayload := fun _ => none
  txOutcome := fun _ => none
  txRecord := fun _ => none
  nextMsg := 0
  outbox := fun _ => none
  consumed := fun _ => false

/-! ## Guards, in source order -/

/-- **`L1Bridgehub.createNewChain(c, ctm, base, admin)` SUCCEEDS** (`L1Bridgehub.sol:107-133`),
for the CTM with asset id `a`. -/
structure CreateChainOK (P : Params) (s : State) (c : Chain) (a : Asset) : Prop where
  /-- `ChainIdCantBeCurrentChain` (`BridgehubBase.sol:501-503`). -/
  notL1 : c ≠ P.l1
  /-- `CTMNotRegistered` (`BridgehubBase.sol:523-525`). -/
  ctmKnown : ∃ v, s.ctmPV P.l1 a = some v
  /-- `BridgeHubAlreadyRegistered` (`BridgehubBase.sol:534-536`). -/
  fresh : s.registered P.l1 c = false

/-- **`bridgeBurn` SUCCEEDS ON L1**, migrating chain `r.chain` to settlement layer `x`, and
the priority transaction is registered with the nullifier. -/
structure L1BurnOK (P : Params) (s : State) (x : Chain) (r : DepositRecord) : Prop where
  /-- `ChainMigrationsDisabled` (`ChainAssetHandlerBase.sol:151-156`, `:201`). -/
  enabled : P.migrationsEnabled = true
  /-- `ChainIdNotRegistered` (`BridgehubBase.sol:351-353`); `zkChainMap.get` (`:419`). -/
  registered : s.registered P.l1 r.chain = true
  /-- `IncorrectChainAssetId` (`ChainAssetHandlerBase.sol:207-210`). -/
  assetMatches : r.asset = s.chainAsset P.l1 r.chain
  /-- `SLNotWhitelisted` (`BridgehubBase.sol:407-409`). -/
  slWhitelisted : s.whitelisted x = true
  /-- `NotCurrentSettlementLayer` (`BridgehubBase.sol:411-413`). -/
  currentSL : s.bhSL P.l1 r.chain = P.l1
  /-- `SettlementLayersMustSettleOnL1` (`BridgehubBase.sol:416-418`). -/
  notASettlementLayer : s.whitelisted r.chain = false
  /-- `OutdatedProtocolVersion` (`ChainTypeManager.sol:735-738`): the chain is at its CTM's
  version. -/
  ctmVersion : s.ctmPV P.l1 r.asset = some (s.diamondPV P.l1 r.chain)
  /-- `SLHasDifferentCTM` (`ChainAssetHandlerBase.sol:232-237`). -/
  sameCtm : x = P.l1 ∨ s.chainAsset P.l1 x = r.asset
  /-- `AlreadyMigrated` (`Migrator.sol:162-164`). -/
  diamondHere : s.diamondSL P.l1 r.chain = none
  /-- `NotAZKChain` (`Migrator.sol:181-185`): the address passed at
  `ChainAssetHandlerBase.sol:268-270` is a registered chain's. -/
  slIsChain : x = P.l1 ∨ s.registered P.l1 x = true
  /-- `ProtocolVersionNotUpToDate` (`Migrator.sol:192-198`). -/
  chainVersion : r.version = s.diamondPV P.l1 r.chain
  /-- `IteratedMigrationsNotSupported` (`ChainAssetHandlerBase.sol:277`). -/
  migrationCount : s.migNum P.l1 r.chain < 2
  /-- `SettlementLayerMustNotBeL1` (`L1ChainAssetHandler.sol:283-285`). -/
  notToL1 : x ≠ P.l1
  /-- `MigrationNumberMismatch` (`L1ChainAssetHandler.sol:286-289`). -/
  firstMigration : s.migNum P.l1 r.chain + 1 = 1
  /-- `DepositExists` (`L1Nullifier.sol:160`). -/
  noDeposit : s.depositHappened x s.nextTx = 0

/-- **`bridgeMint` SUCCEEDS ON SETTLEMENT LAYER `x`** for the mint data `p`. -/
structure SLMintOK (P : Params) (s : State) (x : Chain) (p : MintMsg) : Prop where
  /-- `ChainMigrationsDisabled` (`ChainAssetHandlerBase.sol:365`). -/
  enabled : P.migrationsEnabled = true
  /-- `NoCTMForAssetId` (`BridgehubBase.sol:437-440`). -/
  ctmKnown : ∃ v, s.ctmPV x p.asset = some v
  /-- `AlreadyCurrentSL` (`BridgehubBase.sol:441-443`). -/
  notCurrent : s.bhSL x p.chain ≠ x
  /-- No diamond on `x` yet: `OutdatedProtocolVersion` in `ChainTypeManager.forwardedBridgeMint`
  (`ChainTypeManager.sol:754-756`).  The diamond it deploys starts at the CTM's version
  (`state-transition/chain-deps/DiamondInit.sol:58`, `:110`). -/
  freshVersion : s.registered x p.chain = false → s.ctmPV x p.asset = some p.version
  /-- A diamond on `x` already: `OutdatedProtocolVersion` in `Migrator.forwardedBridgeMint`
  (`Migrator.sol:225-229`).  `ChainTypeManager.forwardedBridgeMint` is not called
  (`ChainAssetHandlerBase.sol:397-415`). -/
  deployedVersion : s.registered x p.chain = true →
    s.ctmPV x p.asset = some (s.diamondPV x p.chain)
  /-- A diamond on `x` already: `NotMigrated` (`Migrator.sol:284-287`). -/
  deployedMigrated : s.registered x p.chain = true → s.diamondSL x p.chain ≠ none

/-- **THE STATUS PROOF, BY ITS MEANING.**  `proveL1ToL2TransactionStatusShared(x, h, .., ok)`
(`L1Nullifier.sol:222-231`) holds: settlement layer `x` executed priority transaction `h`
with status `ok`. -/
def TxStatusProved (s : State) (x : Chain) (h : TxId) (ok : Bool) : Prop :=
  ∃ p, s.txPayload h = some p ∧ p.layer = x ∧ s.txOutcome h = some ok

/-- **Everything `L1Nullifier.bridgeConfirmTransferResult` checks after the status proof**,
through to the chain's diamond, for the supplied record `r`. -/
structure ConfirmRestOK (P : Params) (s : State) (x : Chain) (h : TxId) (r : DepositRecord)
    (ok : Bool) : Prop where
  /-- `DepositDoesNotExist` (`L1Nullifier.sol:235-245`). -/
  hashMatches : P.dataHash r = s.depositHappened x h
  /-- `ZKChainNotRegistered`, `CTMNotRegistered` (`L1ChainAssetHandler.sol:140-141`). -/
  registered : s.registered P.l1 r.chain = true
  /-- `MigrationNumberMismatch` (`L1ChainAssetHandler.sol:151-156`). -/
  failedNumber : ok = false → s.migNum P.l1 r.chain = 1
  /-- `NotMigrated` (`Migrator.sol:324-326`). -/
  failedMigrated : ok = false → s.diamondSL P.l1 r.chain ≠ none
  /-- `OutdatedProtocolVersion` (`Migrator.sol:327-330`). -/
  failedVersion : ok = false → s.diamondPV P.l1 r.chain = r.version

/-- **`bridgeBurn` SUCCEEDS ON SETTLEMENT LAYER `x`**, sending chain `c` back to L1. -/
structure SLBurnOK (P : Params) (s : State) (x c : Chain) : Prop where
  /-- This is a settlement layer's handler, not L1's. -/
  notL1 : x ≠ P.l1
  /-- `ChainMigrationsDisabled` (`ChainAssetHandlerBase.sol:201`). -/
  enabled : P.migrationsEnabled = true
  /-- `ChainIdNotRegistered` (`BridgehubBase.sol:351-353`); `zkChainMap.get` (`:419`). -/
  registered : s.registered x c = true
  /-- `NotCurrentSettlementLayer` (`BridgehubBase.sol:411-413`).  The target is L1
  (`MigrationNotToL1`, `ChainAssetHandlerBase.sol:239-241`), which every bridgehub whitelists
  (`BridgehubBase.sol:171`). -/
  currentSL : s.bhSL x c = x
  /-- `SettlementLayersMustSettleOnL1` (`BridgehubBase.sol:416-418`): on a settlement layer
  only L1 is whitelisted. -/
  notL1Chain : c ≠ P.l1
  /-- `OutdatedProtocolVersion` (`ChainTypeManager.sol:735-738`). -/
  ctmVersion : s.ctmPV x (s.chainAsset x c) = some (s.diamondPV x c)
  /-- `AlreadyMigrated` (`Migrator.sol:162-164`). -/
  diamondHere : s.diamondSL x c = none
  /-- `IteratedMigrationsNotSupported` (`ChainAssetHandlerBase.sol:277`). -/
  migrationCount : s.migNum x c < 2

/-- **`bridgeMint` SUCCEEDS ON L1** for the mint data `p` of a returning chain. -/
structure L1MintOK (P : Params) (s : State) (p : MintMsg) : Prop where
  /-- `ChainMigrationsDisabled` (`ChainAssetHandlerBase.sol:365`). -/
  enabled : P.migrationsEnabled = true
  /-- `MigrationNumberMismatch` (`ChainAssetHandlerBase.sol:375-378`). -/
  leftWithOne : s.migNum P.l1 p.chain = 1
  /-- `MigrationNumberMismatch` (`ChainAssetHandlerBase.sol:379-382`). -/
  carriesTwo : p.migNum = 2
  /-- `MigrationIntervalNotSet` (`L1ChainAssetHandler.sol:314`). -/
  intervalSet : s.intervalActive p.chain = true
  /-- `NoCTMForAssetId` (`BridgehubBase.sol:437-440`). -/
  ctmKnown : ∃ v, s.ctmPV P.l1 p.asset = some v
  /-- `AlreadyCurrentSL` (`BridgehubBase.sol:441-443`). -/
  notCurrent : s.bhSL P.l1 p.chain ≠ P.l1
  /-- `ContractNotDeployed` (`Migrator.sol:277-279`): on L1 a chain is never deployed by a
  mint. -/
  deployed : s.registered P.l1 p.chain = true
  /-- `OutdatedProtocolVersion` (`Migrator.sol:225-229`).  The version in `p` is not
  compared with anything on this path (`ChainAssetHandlerBase.sol:397-415`). -/
  version : s.ctmPV P.l1 p.asset = some (s.diamondPV P.l1 p.chain)
  /-- `NotMigrated` (`Migrator.sol:280-282`). -/
  migrated : s.diamondSL P.l1 p.chain ≠ none

/-- **`_trackedBalance`'S POSSIBLE RESULTS** for chain `c`
(`L1NativeTokenVault.sol:468-477`): not tracked, the chain's own totals, or the interop
pool's. -/
def TrackedKey (P : Params) (c : Chain) (key : Option Chain) : Prop :=
  key = none ∨ key = some c ∨ key = some P.pool

/-- **`_handleBridgeToChain(c, a, amt)` SUCCEEDS** (`L1NativeTokenVault.sol:424-433`), the
tracked totals being those of `key`. -/
structure TokenDepositOK (P : Params) (s : State) (c : Chain) (a : Asset) (amt : ℕ)
    (key : Option Chain) : Prop where
  /-- `_trackedBalance` (`L1NativeTokenVault.sol:429`). -/
  tracked : TrackedKey P c key
  /-- Checked addition (`L1NativeTokenVault.sol:431`). -/
  noOverflow : ∀ k, key = some k → s.deposited k a + amt < UInt256.size

/-- **`_handleBridgeFromChain(c, a, amt)` SUCCEEDS** (`L1NativeTokenVault.sol:439-459`). -/
structure TokenWithdrawOK (P : Params) (s : State) (c : Chain) (a : Asset) (amt : ℕ)
    (key : Option Chain) : Prop where
  /-- `_trackedBalance` (`L1NativeTokenVault.sol:447`). -/
  tracked : TrackedKey P c key
  /-- Checked addition (`L1NativeTokenVault.sol:449`). -/
  noOverflow : ∀ k, key = some k → s.withdrawn k a + amt < UInt256.size
  /-- `ChainBalanceExceeded` (`L1NativeTokenVault.sol:450-456`). -/
  withinCap : ∀ k, key = some k → P.capExempt k = false →
    s.withdrawn k a + amt ≤ s.deposited k a + P.backfill k a

/-! ## Steps -/

/-- The modelled calls. -/
inductive Label
  /-- `L1Bridgehub.createNewChain` for chain `c`, CTM asset `a`, base-token asset `b`. -/
  | createChain (c : Chain) (a b : Asset)
  /-- `L1Bridgehub.setSettlementLayerStatus` (`L1Bridgehub.sol:94-100`). -/
  | setWhitelist (x : Chain) (b : Bool)
  /-- Any write of layer `y`'s CTM for asset `a`: registration, or a new protocol version. -/
  | ctmSetVersion (y : Chain) (a : Asset) (v : UInt256)
  /-- Any upgrade of chain `c`'s diamond on layer `y`. -/
  | diamondSetVersion (y c : Chain) (v : UInt256)
  /-- The migration request on L1: `bridgeBurn` towards `x` with burn data `r`. -/
  | l1Burn (x : Chain) (r : DepositRecord)
  /-- Settlement layer `x` executes priority transaction `h`, with status `ok`. -/
  | slExecute (x : Chain) (h : TxId) (ok : Bool)
  /-- `L1Nullifier.bridgeConfirmTransferResult` for transaction `h` on `x`, record `r`. -/
  | l1Confirm (x : Chain) (h : TxId) (r : DepositRecord) (ok : Bool)
  /-- `bridgeBurn` on settlement layer `x`, sending chain `c` back to L1. -/
  | slBurn (x c : Chain)
  /-- L1 finalizes return message `m`. -/
  | l1Mint (m : MsgId)
  /-- A token transfer from L1 towards chain `c`. -/
  | tokenDeposit (c : Chain) (a : Asset) (amt : ℕ) (key : Option Chain)
  /-- A token transfer from chain `c` to L1, or a claimed failed deposit. -/
  | tokenWithdraw (c : Chain) (a : Asset) (amt : ℕ) (key : Option Chain)

/-- What `bridgeMint` writes on layer `y` (`ChainAssetHandlerBase.sol:384`,
`BridgehubBase.sol:445-447`, `ChainAssetHandlerBase.sol:399-405`, `Migrator.sol:299`).  A
chain with no diamond on `y` gets one at the carried version, which `SLMintOK.freshVersion`
makes the CTM's. -/
def mintOn (s : State) (y : Chain) (p : MintMsg) : State :=
  { s with
    migNum := set2 s.migNum y p.chain p.migNum
    bhSL := set2 s.bhSL y p.chain y
    chainAsset := set2 s.chainAsset y p.chain p.asset
    baseAsset := set2 s.baseAsset y p.chain p.base
    registered := set2 s.registered y p.chain true
    diamondPV := set2 s.diamondPV y p.chain
      (if s.registered y p.chain = true then s.diamondPV y p.chain else p.version)
    diamondSL := set2 s.diamondSL y p.chain none }

/-- What a confirmation writes on L1: the deposit is cleared (`L1Nullifier.sol:247`), and for
status `Failure` the migration is undone (`BridgehubBase.sol:465-467`,
`L1ChainAssetHandler.sol:157-160`, `Migrator.sol:332`). -/
def confirmOn (P : Params) (s : State) (x : Chain) (h : TxId) (r : DepositRecord)
    (ok : Bool) : State :=
  if ok = true then
    { s with
      depositHappened := set2 s.depositHappened x h 0
      txRecord := set1 s.txRecord h none }
  else
    { s with
      depositHappened := set2 s.depositHappened x h 0
      txRecord := set1 s.txRecord h none
      bhSL := set2 s.bhSL P.l1 r.chain P.l1
      migNum := set2 s.migNum P.l1 r.chain 0
      intervalActive := set1 s.intervalActive r.chain false
      intervalSL := set1 s.intervalSL r.chain 0
      diamondSL := set2 s.diamondSL P.l1 r.chain none }

/-- The mint data a settlement layer sends with a returning chain
(`ChainAssetHandlerBase.sol:315-352`, `ChainTypeManager.sol:740`). -/
def returnMsg (s : State) (x c : Chain) : MintMsg :=
  ⟨x, s.chainAsset x c, c, s.baseAsset x c, s.diamondPV x c, s.migNum x c + 1⟩

/-- The mint data L1 sends with a departing chain.  Its version is the CTM's, which
`L1BurnOK.ctmVersion` makes the diamond's. -/
def departMsg (P : Params) (s : State) (x : Chain) (r : DepositRecord) : MintMsg :=
  ⟨x, r.asset, r.chain, s.baseAsset P.l1 r.chain, s.diamondPV P.l1 r.chain,
    s.migNum P.l1 r.chain + 1⟩

/-- The guard of each call. -/
def Guard (P : Params) (s : State) : Label → Prop
  | .createChain c a _ => CreateChainOK P s c a
  | .setWhitelist x _ => s.bhSL P.l1 x = P.l1
  | .ctmSetVersion _ _ _ => True
  | .diamondSetVersion y c _ => s.registered y c = true
  | .l1Burn x r => L1BurnOK P s x r
  | .slExecute x h ok =>
      x ≠ P.l1 ∧ ∃ p, s.txPayload h = some p ∧ p.layer = x ∧ s.txOutcome h = none ∧
        (ok = true → SLMintOK P s x p)
  | .l1Confirm x h r ok => TxStatusProved s x h ok ∧ ConfirmRestOK P s x h r ok
  | .slBurn x c => SLBurnOK P s x c
  | .l1Mint m => ∃ p, s.outbox m = some p ∧ s.consumed m = false ∧ L1MintOK P s p
  | .tokenDeposit c a amt key => TokenDepositOK P s c a amt key
  | .tokenWithdraw c a amt key => TokenWithdrawOK P s c a amt key

/-- The state after each call. -/
def next (P : Params) (s : State) : Label → State
  | .createChain c a b =>
      { s with
        registered := set2 s.registered P.l1 c true
        bhSL := set2 s.bhSL P.l1 c P.l1
        chainAsset := set2 s.chainAsset P.l1 c a
        baseAsset := set2 s.baseAsset P.l1 c b
        diamondSL := set2 s.diamondSL P.l1 c none
        diamondPV := set2 s.diamondPV P.l1 c ((s.ctmPV P.l1 a).getD 0) }
  | .setWhitelist x b => { s with whitelisted := set1 s.whitelisted x b }
  | .ctmSetVersion y a v => { s with ctmPV := set2 s.ctmPV y a (some v) }
  | .diamondSetVersion y c v => { s with diamondPV := set2 s.diamondPV y c v }
  | .l1Burn x r =>
      { s with
        bhSL := set2 s.bhSL P.l1 r.chain x
        diamondSL := set2 s.diamondSL P.l1 r.chain (some x)
        migNum := set2 s.migNum P.l1 r.chain (s.migNum P.l1 r.chain + 1)
        intervalActive := set1 s.intervalActive r.chain true
        intervalSL := set1 s.intervalSL r.chain x
        depositHappened := set2 s.depositHappened x s.nextTx (P.dataHash r)
        txPayload := set1 s.txPayload s.nextTx (some (departMsg P s x r))
        txRecord := set1 s.txRecord s.nextTx (some r)
        nextTx := s.nextTx + 1 }
  | .slExecute x h ok =>
      match s.txPayload h with
      | none => s
      | some p =>
          if ok = true then mintOn { s with txOutcome := set1 s.txOutcome h (some true) } x p
          else { s with txOutcome := set1 s.txOutcome h (some false) }
  | .l1Confirm x h r ok => confirmOn P s x h r ok
  | .slBurn x c =>
      { s with
        bhSL := set2 s.bhSL x c P.l1
        diamondSL := set2 s.diamondSL x c (some P.l1)
        migNum := set2 s.migNum x c (s.migNum x c + 1)
        outbox := set1 s.outbox s.nextMsg (some (returnMsg s x c))
        nextMsg := s.nextMsg + 1 }
  | .l1Mint m =>
      match s.outbox m with
      | none => s
      | some p =>
          { mintOn s P.l1 p with
            intervalActive := set1 s.intervalActive p.chain false
            consumed := set1 s.consumed m true }
  | .tokenDeposit _ a amt key =>
      match key with
      | none => s
      | some k => { s with deposited := set2 s.deposited k a (s.deposited k a + amt) }
  | .tokenWithdraw _ a amt key =>
      match key with
      | none => s
      | some k => { s with withdrawn := set2 s.withdrawn k a (s.withdrawn k a + amt) }

/-- **A RUN**: any sequence of the modelled calls, each accepted by its guard.  The log is
newest first. -/
inductive Run (P : Params) : State → List Label → State → Prop
  | nil (s : State) : Run P s [] s
  | step {s t : State} {ls : List Label} (l : Label) :
      Run P s ls t → Guard P t l → Run P s (l :: ls) (next P t l)

/-- The confirmation supplies the record the deposit was registered with.  The source
compares hashes only (`ConfirmRestOK.hashMatches`). -/
def NoClash (s : State) : Label → Prop
  | .l1Confirm _ h r _ => s.txRecord h = some r
  | _ => True

/-- **A RUN WITHOUT A HASH EVENT**: every confirmation supplies the registered record. -/
inductive CleanRun (P : Params) : State → List Label → State → Prop
  | nil (s : State) : CleanRun P s [] s
  | step {s t : State} {ls : List Label} (l : Label) :
      CleanRun P s ls t → Guard P t l → NoClash t l → CleanRun P s (l :: ls) (next P t l)

/-- Reachable from `init` by a run without a hash event. -/
def Reachable (P : Params) (s : State) : Prop := ∃ ls, CleanRun P (init P) ls s

/-- **A HASH EVENT**: two different records with the same `encodeTxDataHash`, or a record
whose hash is zero. -/
def HashEvent (P : Params) : Prop :=
  (∃ r r' : DepositRecord, r ≠ r' ∧ P.dataHash r = P.dataHash r') ∨
    ∃ r : DepositRecord, P.dataHash r = 0

/-! ## Where a chain is -/

/-- **LAYER `y` SETTLES CHAIN `c`**, by the layer's bridgehub: the chain is registered there
and `settlementLayer[c] == block.chainid`. -/
def OnLayer (s : State) (y c : Chain) : Prop :=
  s.registered y c = true ∧ s.bhSL y c = y

/-- The same by the chain's diamond on `y`: it exists and its `s.settlementLayer` is zero,
which is what `onlySettlementLayer` checks
(`state-transition/chain-deps/facets/ZKChainBase.sol:141-146`). -/
def DiamondOnLayer (s : State) (y c : Chain) : Prop :=
  s.registered y c = true ∧ s.diamondSL y c = none

/-- **CHAIN `c` IS IN FLIGHT IN TRANSACTION `h`**: the migration request is still registered
with the nullifier and its destination has not executed it successfully. -/
def InFlight (s : State) (h : TxId) (c : Chain) : Prop :=
  ∃ r, s.txRecord h = some r ∧ r.chain = c ∧ s.txOutcome h ≠ some true

/-- **CHAIN `c` IS RETURNING IN MESSAGE `m`**: sent and not yet executed on L1. -/
def Returning (s : State) (m : MsgId) (c : Chain) : Prop :=
  ∃ p, s.outbox m = some p ∧ p.chain = c ∧ s.consumed m = false

/-- The places a chain can be. -/
inductive Carrier
  /-- Settling on L1. -/
  | l1
  /-- Settling on settlement layer `x`. -/
  | sl (x : Chain)
  /-- In an L1 → settlement-layer transaction not executed successfully. -/
  | tx (h : TxId)
  /-- In a settlement-layer → L1 message not executed. -/
  | msg (m : MsgId)

/-- Chain `c` is at carrier `k`. -/
def Holds (P : Params) (s : State) (c : Chain) : Carrier → Prop
  | .l1 => OnLayer s P.l1 c
  | .sl x => x ≠ P.l1 ∧ OnLayer s x c
  | .tx h => InFlight s h c
  | .msg m => Returning s m c

/-- The layer a carrier belongs to: the layer itself, the transaction's destination, or the
message's source. -/
def carrierLayer (P : Params) (s : State) : Carrier → Option Chain
  | .l1 => some P.l1
  | .sl x => some x
  | .tx h => (s.txPayload h).map MintMsg.layer
  | .msg m => (s.outbox m).map MintMsg.layer

/-! ## Token totals along a run -/

/-- The label is a token transfer. -/
def Label.isToken : Label → Bool
  | .tokenDeposit _ _ _ _ => true
  | .tokenWithdraw _ _ _ _ => true
  | _ => false

/-- The amount a label adds to `chainTotalDeposited[k][a]`. -/
def Label.depositTo (k : Chain) (a : Asset) : Label → ℕ
  | .tokenDeposit _ a' amt (some k') => if k' = k ∧ a' = a then amt else 0
  | _ => 0

/-- The amount a label adds to `chainTotalWithdrawn[k][a]`. -/
def Label.withdrawFrom (k : Chain) (a : Asset) : Label → ℕ
  | .tokenWithdraw _ a' amt (some k') => if k' = k ∧ a' = a then amt else 0
  | _ => 0

/-- What a log adds to `chainTotalDeposited[k][a]`. -/
def depositedBy (ls : List Label) (k : Chain) (a : Asset) : ℕ :=
  (ls.map (Label.depositTo k a)).sum

/-- What a log adds to `chainTotalWithdrawn[k][a]`. -/
def withdrawnBy (ls : List Label) (k : Chain) (a : Asset) : ℕ :=
  (ls.map (Label.withdrawFrom k a)).sum

end Protocol.ChainMigration
