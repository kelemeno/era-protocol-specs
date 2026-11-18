import Mathlib.Tactic

/-!
# Model: chains migrating between settlement layers through the chain asset handler

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`. Paths are
relative to `l1-contracts/contracts/`; the two files modelled are cited as

* `CAH` — `core/chain-asset-handler/ChainAssetHandlerBase.sol`,
* `L1CAH` — `core/chain-asset-handler/L1ChainAssetHandler.sol`,

and the callees whose effects are part of a migration step as

* `BH` — `core/bridgehub/BridgehubBase.sol`, `L1BH` — `core/bridgehub/L1Bridgehub.sol`,
* `CTM` — `state-transition/ChainTypeManager.sol`,
* `MIG` — `state-transition/chain-deps/facets/Migrator.sol`, `ADM` — `.../facets/Admin.sol`,
* `L2CAH` — `core/chain-asset-handler/L2ChainAssetHandler.sol`, `CFG` — `common/Config.sol`.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.ChainAssetHandler.Properties.*`, proofs in
`EraSpec.Contracts.ChainAssetHandler.Proofs.*`.

## The system

A chain is an asset of its chain type manager (CTM). Migrating it is a bridge transfer of
that asset: `bridgeBurn` on the hub it settles on (`CAH:188-254`), a cross-chain message,
then `bridgeMint` on the destination (`CAH:361-420`). An L1 → settlement-layer deposit that
fails on the settlement layer is undone on L1 by `bridgeConfirmTransferResult`
(`L1CAH:122-172`). One chain asset handler runs on each *hub*: L1 and every settlement layer
(a "gateway"). The model is the joint state of all hubs, indexed by the hub's chain id, plus
the migration messages in flight.

Per hub `h` and chain `c` it keeps:

* the bridgehub's `settlementLayer[c]` (`sl h c`), whether `getZKChain(c) ≠ 0` (`reg h c`),
  and `chainTypeManager[c]` (`ctm h c`);
* the handler's `migrationNumber[c]` (`CAH:110`, `migNum h c`), `ecosystemMigrationPaused`
  (`CAH:84`), `ctmMigrationPaused[ctm]` (`CAH:118`), and `PausableUpgradeable.paused()`;
* on L1 only: `isMigrationInProgress[c]` (`L1CAH:52`) and the interval
  `_migrationInterval[c][1]` (`L1CAH:58`) as its `isActive` and `settlementLayerChainId`
  fields. Index 1 is the only index ever written: `_recordMigrationToSL` requires the new
  number to be `MIGRATION_NUMBER_L1_TO_SETTLEMENT_LAYER = 1` (`L1CAH:286-289`, `CFG:323`),
  `_recordMigrationFromSL` reads index 1 (`L1CAH:313`), and the failure path deletes index
  `failedMigrationNum = 1` (`L1CAH:153-160`). Batch-number fields are not modelled; on a
  settlement layer both recorders are no-ops (`L2CAH:136-152`);
* the CTM's `protocolVersion` (`ctmPV h x`), and the chain's diamond on that hub: its
  `s.protocolVersion` (`dpv h c`) and whether its `s.settlementLayer ≠ 0` (`away h c`).

## Messages

`bridgeBurn` returns the mint data; the asset router sends it to the destination. A message
records source, destination, chain, CTM asset id, the migration number it carries
(`BridgehubMintCTMAssetData.migrationNumber`, `CAH:349`) and the protocol version it carries
(the CTM data `abi.encode(admin, protocolVersion)`, `CTM:745`; the chain data's version,
which `MIG:192-198` makes equal to the diamond's). Its status is

* `pending` — sent, not yet executed;
* `executed` — the destination's `bridgeMint` ran;
* `failed` — an L1 → settlement-layer deposit whose L2 transaction failed;
* `done` — L1 consumed the deposit's status proof (`bridgeConfirmTransferResult`).

These statuses are the environment's guarantees (`PROTO-CAH-DELIVERY` in ASSUMPTIONS.md):
an L1 → L2 transaction executes once, with outcome success or failure, and its status proof
is truthful; `L1Nullifier._verifyAndClearTransfer` lets L1 consume each deposit's status
once; an L2 → L1 message is finalized at most once and its finalization does not fail
permanently (the source assumes "GW -> L1 transactions can never fail", `MIG:200-201`).

## Modelling choices

* **A revert is the absence of a step.** Each guard is listed in source order with its
  `file:line`. Values (`requireZeroValue`), events and the caller check `onlyAssetRouter`
  (the asset router is the only caller of the three handler entry points; a step *is* the
  router's call) are not modelled.
* **Identifiers are `ℕ`.** Chain ids, addresses and asset ids are compared for equality and
  against zero only. Migration numbers never exceed 2 on a reachable state
  (`Properties.L1MigrationBookkeeping`), so `uint256` wrap-around does not arise.
* **Reject-only checks omitted**: the diamond's priority-queue, priority-mode, deposit-pause
  window and batches-executed checks (`MIG:158-205`), the base-token origin checks of the
  mint data (`CAH:333-338`), message-root bookkeeping and batch numbers, the bridgehub's
  `_validateChainParams` details other than zero and own-chain checks. Omitting a
  reject-only check only adds runs, so every safety result covers the source.
* **Fixed configuration** (`World`): the whitelist, the CTM asset-id registry, CTM
  registration and ownership, handler owners, chain admins, and `isReadyForMigration`.
  The diamond's own `s.chainTypeManager` is identified with the bridgehub's
  `chainTypeManager[c]` on the same hub.
* **Versions are environment steps.** `ctmUpgrade` raises a CTM's version; `diamondUpgrade`
  raises a registered diamond's version. `ADM:559-590` (`upgradeChainFromVersion`) has no
  settlement-layer check, so an away diamond can be upgraded; both strictly increase
  (`ADM:585-587`; `VersionStrictlyIncreasesOnEdges` in the `ChainTypeManager` model).
* **`CHAIN_MIGRATIONS_ENABLED` is a parameter.** At this commit it is `false` (`CFG:320`), so
  in production `bridgeBurn` and `bridgeMint` always revert (`CAH:151-156`);
  `_getChainMigrationsEnabled` is virtual for test variants (`CAH:163-167`).
  `Properties.MigrationsDisabledFreezeSettlement` is the production statement; the other
  results hold for either value, and their witnesses use `true`.
* **Chain creation** is the L1 bridgehub's `createNewChain` / `registerAlreadyDeployedChain`
  (`L1BH:103-140`, `L1BH:290-315`): both set `settlementLayer[c] = block.chainid` and
  register the chain, which must not be registered yet (`ChainAlreadyLive`). Chains are
  created only on L1; a settlement layer registers a chain only in `bridgeMint`.
-/

namespace Contracts.ChainAssetHandler

/-- A chain id. `0` is no chain (`block.chainid ≠ 0`). -/
abbrev ChainId := ℕ
/-- An address; `0` is the zero address. Only equality and zero are used. -/
abbrev Address := ℕ
/-- A CTM asset id (`bytes32`). Only equality is used. -/
abbrev AssetId := ℕ

/-- Point update of a mapping. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-- Point update of a per-hub mapping: entry `b` on hub `a`. -/
def upd2 {α β γ : Type} [DecidableEq α] [DecidableEq β] (f : α → β → γ) (a : α) (b : β)
    (v : γ) : α → β → γ :=
  fun x y => if x = a ∧ y = b then v else f x y

/-- `MIGRATION_NUMBER_L1_TO_SETTLEMENT_LAYER` (`CFG:323`). -/
def numToSL : ℕ := 1
/-- `MIGRATION_NUMBER_SETTLEMENT_LAYER_TO_L1` (`CFG:326`). -/
def numToL1 : ℕ := 2
/-- `MAX_ALLOWED_NUMBER_OF_MIGRATIONS` (`CFG:329`). -/
def maxMigrations : ℕ := 2

/-- Fixed configuration of the ecosystem. -/
structure World where
  /-- `L1_CHAIN_ID` (`L1CAH:46`; on L2 `L2CAH:35`). -/
  l1 : ChainId
  /-- `_getChainMigrationsEnabled()`: `CHAIN_MIGRATIONS_ENABLED` (`CFG:320`, `false`). -/
  migrationsEnabled : Bool
  /-- `whitelistedSettlementLayers[t]` on the bridgehub of hub `h` (`wl h t`). -/
  wl : ChainId → ChainId → Bool
  /-- `ctmAssetIdToAddress[assetId]` (`BH:437`, `CAH:469`). -/
  ctmOfAsset : AssetId → Address
  /-- `ctmAssetIdFromAddress[ctm]` (`BH:354`). -/
  assetOfCTM : Address → AssetId
  /-- `chainTypeManagerIsRegistered(ctm)` on hub `h` (`CAH:139`). -/
  ctmRegistered : ChainId → Address → Bool
  /-- `IOwnable(ctm).owner()` (`CAH:142`). -/
  ctmOwner : Address → Address
  /-- The handler's `owner()` on hub `h` (`Ownable2StepUpgradeable`). -/
  owner : ChainId → Address
  /-- The chain's admin, `IZKChain(zkChain).getAdmin()` (`CAH:225`, `MIG:165`). -/
  admin : ChainId → Address
  /-- `isReadyForMigration(c)` on L1 (`L1CAH:175-190`): base token registered in the vault
  and supporting `totalSupply()`. -/
  ready : ChainId → Bool

/-- Status of a migration message (see the module docstring). -/
inductive MsgStatus
  | pending
  | executed
  | failed
  | done
  deriving DecidableEq

/-- A migration message: the mint data `bridgeBurn` returns, as the asset router carries it. -/
structure Msg where
  /-- The hub that burned (the source settlement layer). -/
  src : ChainId
  /-- `_settlementChainId`, the destination hub. -/
  dst : ChainId
  /-- The migrating chain, `bridgehubMintData.chainId`. -/
  chain : ChainId
  /-- The CTM asset id, `_assetId`. -/
  asset : AssetId
  /-- `bridgehubMintData.migrationNumber` (`CAH:349`). -/
  num : ℕ
  /-- The protocol version the CTM and chain data carry (`CTM:745`, `MIG:192-198`). -/
  pv : ℕ
  /-- Delivery status. -/
  status : MsgStatus

/-- The joint state of all hubs and the messages between them. -/
structure Sys where
  /-- Bridgehub of hub `h`: `settlementLayer[c]` (`sl h c`). -/
  sl : ChainId → ChainId → ChainId
  /-- Bridgehub of hub `h`: `getZKChain(c) ≠ address(0)`. -/
  reg : ChainId → ChainId → Bool
  /-- Bridgehub of hub `h`: `chainTypeManager[c]`. -/
  ctm : ChainId → ChainId → Address
  /-- Handler of hub `h`: `migrationNumber[c]` (`CAH:110`). -/
  migNum : ChainId → ChainId → ℕ
  /-- L1 handler: `isMigrationInProgress[c]` (`L1CAH:52`). -/
  inProgress : ChainId → Bool
  /-- L1 handler: `_migrationInterval[c][1].isActive` (`L1CAH:58`). -/
  ivActive : ChainId → Bool
  /-- L1 handler: `_migrationInterval[c][1].settlementLayerChainId`. -/
  ivSL : ChainId → ChainId
  /-- Handler of hub `h`: `ecosystemMigrationPaused` (`CAH:84`). -/
  ecoPaused : ChainId → Bool
  /-- Handler of hub `h`: `ctmMigrationPaused[ctm]` (`CAH:118`). -/
  ctmPaused : ChainId → Address → Bool
  /-- Handler of hub `h`: `PausableUpgradeable.paused()`. -/
  paused : ChainId → Bool
  /-- CTM `x` on hub `h`: `protocolVersion`. -/
  ctmPV : ChainId → Address → ℕ
  /-- Diamond of chain `c` on hub `h`: `s.protocolVersion`. -/
  dpv : ChainId → ChainId → ℕ
  /-- Diamond of chain `c` on hub `h`: `s.settlementLayer != address(0)`. -/
  away : ChainId → ChainId → Bool
  /-- Messages, by id. -/
  msgs : ℕ → Option Msg
  /-- The next message id. -/
  nMsgs : ℕ

/-- What happens. Every hub action names its hub `h`. -/
inductive Label
  /-- L1 `createNewChain` / `registerAlreadyDeployedChain` of chain `c` under CTM `x`. -/
  | register (c : ChainId) (x : Address)
  /-- Hub `h`'s `bridgeBurn(t, _, a, orig, data)` of chain `c` (`CAH:188-254`). -/
  | burn (h c t : ChainId) (a : AssetId) (orig : Address)
  /-- Hub `h`'s `bridgeMint(_, a, data)` executing message `i` for chain `c` (`CAH:361-420`). -/
  | mint (h : ChainId) (i : ℕ) (c : ChainId) (a : AssetId)
  /-- Environment: the L1 → settlement-layer transaction of message `i` fails. -/
  | failDeposit (i : ℕ)
  /-- L1 `bridgeConfirmTransferResult` for message `i` of chain `c`, `failure` or success
  (`L1CAH:122-172`). -/
  | confirm (i : ℕ) (c : ChainId) (failure : Bool)
  /-- `pauseMigration()` on hub `h` by `sender` (`CAH:437-440`). -/
  | pauseMigration (h : ChainId) (sender : Address)
  /-- `unpauseMigration()` (`CAH:443-446`). -/
  | unpauseMigration (h : ChainId) (sender : Address)
  /-- `pauseCTMMigration(x)` (`CAH:449-452`). -/
  | pauseCTM (h : ChainId) (x : Address) (sender : Address)
  /-- `unpauseCTMMigration(x)` (`CAH:455-458`). -/
  | unpauseCTM (h : ChainId) (x : Address) (sender : Address)
  /-- `pause()` (`CAH:476-478`). -/
  | pause (h : ChainId) (sender : Address)
  /-- `unpause()` (`CAH:481-483`). -/
  | unpause (h : ChainId) (sender : Address)
  /-- Environment: CTM `x` on hub `h` moves to version `v`. -/
  | ctmUpgrade (h : ChainId) (x : Address) (v : ℕ)
  /-- Environment: the diamond of chain `c` on hub `h` is upgraded to version `v`
  (`ADM:559-590`). -/
  | diamondUpgrade (h c : ChainId) (v : ℕ)

/-! ## Successor states -/

/-- The message `bridgeBurn` on hub `h` sends for chain `c` to `t`. -/
def burnMsg (s : Sys) (h c t : ChainId) (a : AssetId) : Msg :=
  { src := h, dst := t, chain := c, asset := a, num := s.migNum h c + 1, pv := s.dpv h c,
    status := .pending }

/-- After `bridgeBurn` on hub `h` of chain `c` to `t`:
the bridgehub records `t` (`BH:414`); on L1 the chain is marked in progress (`L1CAH:206`);
the diamond records that it left (`MIG:207`); the migration number is incremented
(`CAH:278-279`); on L1 interval 1 is opened (`L1CAH:291-298`); the message is sent. -/
def burnPost (W : World) (s : Sys) (h c t : ChainId) (a : AssetId) : Sys :=
  { s with
    sl := upd2 s.sl h c t
    inProgress := if h = W.l1 then upd s.inProgress c true else s.inProgress
    away := upd2 s.away h c true
    migNum := upd2 s.migNum h c (s.migNum h c + 1)
    ivActive := if h = W.l1 then upd s.ivActive c true else s.ivActive
    ivSL := if h = W.l1 then upd s.ivSL c t else s.ivSL
    msgs := upd s.msgs s.nMsgs (some (burnMsg s h c t a))
    nMsgs := s.nMsgs + 1 }

/-- After `bridgeMint` on hub `h` of message `i` (`m`) for chain `c` under CTM `x`:
the migration number is the carried one (`CAH:384`); on L1 interval 1 is closed
(`L1CAH:315-319`); the bridgehub records `h` and the CTM (`BH:445-446`); a chain not
registered here gets a fresh diamond at the CTM's version (`CTM:756-762`, registered at
`CAH:405`); the diamond is back (`MIG:299`); the message is executed. -/
def mintPost (W : World) (s : Sys) (h : ChainId) (i : ℕ) (m : Msg) (x : Address)
    (fresh : Bool) : Sys :=
  { s with
    migNum := upd2 s.migNum h m.chain m.num
    ivActive := if h = W.l1 then upd s.ivActive m.chain false else s.ivActive
    sl := upd2 s.sl h m.chain h
    ctm := upd2 s.ctm h m.chain x
    reg := upd2 s.reg h m.chain true
    dpv := if fresh then upd2 s.dpv h m.chain (s.ctmPV h x) else s.dpv
    away := upd2 s.away h m.chain false
    msgs := upd s.msgs i (some { m with status := .executed }) }

/-- After L1 `bridgeConfirmTransferResult` for message `i` (`m`): on failure the bridgehub
moves the chain back to L1 (`BH:465-467`), the migration number is decremented
(`L1CAH:157`), interval 1 is deleted (`L1CAH:160`) and the diamond is back (`MIG:332`); in
both cases the chain is no longer in progress (`L1CAH:163`) and the deposit is consumed. -/
def confirmPost (W : World) (s : Sys) (i : ℕ) (m : Msg) (failure : Bool) : Sys :=
  if failure then
    { s with
      sl := upd2 s.sl W.l1 m.chain W.l1
      migNum := upd2 s.migNum W.l1 m.chain (s.migNum W.l1 m.chain - 1)
      ivActive := upd s.ivActive m.chain false
      ivSL := upd s.ivSL m.chain 0
      inProgress := upd s.inProgress m.chain false
      away := upd2 s.away W.l1 m.chain false
      msgs := upd s.msgs i (some { m with status := .done }) }
  else
    { s with
      inProgress := upd s.inProgress m.chain false
      msgs := upd s.msgs i (some { m with status := .done }) }

/-- After chain registration on L1 (`L1BH:113-123`; the CTM deploys the diamond at its
current version). -/
def registerPost (W : World) (s : Sys) (c : ChainId) (x : Address) : Sys :=
  { s with
    ctm := upd2 s.ctm W.l1 c x
    sl := upd2 s.sl W.l1 c W.l1
    reg := upd2 s.reg W.l1 c true
    dpv := upd2 s.dpv W.l1 c (s.ctmPV W.l1 x)
    away := upd2 s.away W.l1 c false }

/-! ## Steps -/

/-- One successful call. A revert is the absence of a step. -/
inductive Step (W : World) : Sys → Label → Sys → Prop
  /-- Chain creation on L1. `_validateChainParams`: `c ≠ 0`, `c ≠ block.chainid`, `ctm ≠ 0`
  (`BH:497-524`); the CTM is registered; not yet live (`ChainAlreadyLive` in
  `_registerNewZKChain`). -/
  | register {s : Sys} {c : ChainId} {x : Address} :
      c ≠ 0 → c ≠ W.l1 → x ≠ 0 → W.ctmRegistered W.l1 x = true → s.reg W.l1 c = false →
      Step W s (.register c x) (registerPost W s c x)
  /-- `bridgeBurn` on hub `h` (`CAH:188-254`), guards in source order:
  `whenNotPaused` (`CAH:200`); `whenMigrationsEnabled` (`CAH:201`, `:151-156`);
  `_requireMigrationsNotPausedFor(a)` (`CAH:204`, `:468-473`, `:432-434`);
  `a == ctmAssetIdFromChainId(c)`, which reverts for an unregistered CTM (`CAH:207-210`,
  `BH:349-355`); in `forwardedBridgeBurnSetSettlementLayer`: `t` whitelisted (`BH:407-409`),
  `settlementLayer[c] == block.chainid` (`BH:411-413`), `c` not itself a whitelisted settlement
  layer (`BH:416-418`); `zkChain != 0` (`CAH:222-224`); `orig` is the chain admin
  (`CAH:225-227`); the CTM's `forwardedBridgeBurn` requires the diamond at the CTM's version
  (`CTM:739-743`); a non-L1 destination has the same CTM (`CAH:232-237`); off L1 the
  destination is L1 (`CAH:239-241`); on L1 the chain is ready (`L1CAH:205`); the diamond is not
  away (`MIG:162-164`); `migrationNumber < MAX_ALLOWED_NUMBER_OF_MIGRATIONS` (`CAH:277`); on L1,
  `_recordMigrationToSL` requires `t ≠ L1` (`L1CAH:283-285`) and the new number to be
  `MIGRATION_NUMBER_L1_TO_SETTLEMENT_LAYER` (`L1CAH:286-289`). `h ≠ 0` is `block.chainid ≠ 0`. -/
  | burn {s : Sys} {h c t : ChainId} {a : AssetId} {orig : Address} :
      h ≠ 0 →
      s.paused h = false →
      W.migrationsEnabled = true →
      s.ecoPaused h = false → s.ctmPaused h (W.ctmOfAsset a) = false →
      s.ctm h c ≠ 0 → a = W.assetOfCTM (s.ctm h c) →
      W.wl h t = true → s.sl h c = h → W.wl h c = false →
      s.reg h c = true →
      orig = W.admin c →
      s.dpv h c = s.ctmPV h (s.ctm h c) →
      (t ≠ W.l1 → s.ctm h t = s.ctm h c) →
      (h ≠ W.l1 → t = W.l1) →
      (h = W.l1 → W.ready c = true) →
      s.away h c = false →
      s.migNum h c < maxMigrations →
      (h = W.l1 → t ≠ W.l1 ∧ s.migNum h c + 1 = numToSL) →
      Step W s (.burn h c t a orig) (burnPost W s h c t a)
  /-- `bridgeMint` on hub `h` of a chain with no diamond here: the CTM deploys one
  (`CAH:398-409`). Guards: the message is pending for `h` (environment); `whenNotPaused`,
  `whenMigrationsEnabled` (`CAH:365`); `_requireMigrationsNotPausedFor(a)` (`CAH:366`); on L1
  the stored number is 1 and the carried one 2 (`CAH:374-383`); on L1 interval 1 is active
  (`L1CAH:309-314`); the asset id has a CTM (`BH:437-440`); `settlementLayer[c] !=
  block.chainid` (`BH:441-443`); the carried version is the CTM's (`CTM:756-761`); on L1 a
  fresh diamond is refused (`MIG:277-279`, `ContractNotDeployed`). -/
  | mintFresh {s : Sys} {h : ChainId} {i : ℕ} {m : Msg} :
      s.msgs i = some m → m.status = .pending → m.dst = h → h ≠ 0 →
      s.paused h = false →
      W.migrationsEnabled = true →
      s.ecoPaused h = false → s.ctmPaused h (W.ctmOfAsset m.asset) = false →
      (h = W.l1 → s.migNum h m.chain = numToSL ∧ m.num = numToL1) →
      (h = W.l1 → s.ivActive m.chain = true) →
      W.ctmOfAsset m.asset ≠ 0 →
      s.sl h m.chain ≠ h →
      s.reg h m.chain = false →
      m.pv = s.ctmPV h (W.ctmOfAsset m.asset) →
      h ≠ W.l1 →
      Step W s (.mint h i m.chain m.asset) (mintPost W s h i m (W.ctmOfAsset m.asset) true)
  /-- `bridgeMint` on hub `h` of a chain whose diamond is registered here: the diamond is
  reused (`CAH:397`, `:410-417`). Same guards up to the bridgehub; then the diamond's
  `forwardedBridgeMint` requires its version to be its CTM's (`MIG:223-229`) and the diamond
  to be away (`MIG:280-282` on L1, `:284-287` elsewhere). The carried version is not read. -/
  | mintReturn {s : Sys} {h : ChainId} {i : ℕ} {m : Msg} :
      s.msgs i = some m → m.status = .pending → m.dst = h → h ≠ 0 →
      s.paused h = false →
      W.migrationsEnabled = true →
      s.ecoPaused h = false → s.ctmPaused h (W.ctmOfAsset m.asset) = false →
      (h = W.l1 → s.migNum h m.chain = numToSL ∧ m.num = numToL1) →
      (h = W.l1 → s.ivActive m.chain = true) →
      W.ctmOfAsset m.asset ≠ 0 →
      s.sl h m.chain ≠ h →
      s.reg h m.chain = true →
      s.dpv h m.chain = s.ctmPV h (W.ctmOfAsset m.asset) →
      s.away h m.chain = true →
      Step W s (.mint h i m.chain m.asset) (mintPost W s h i m (W.ctmOfAsset m.asset) false)
  /-- Environment: a pending L1 → settlement-layer deposit fails on the settlement layer.
  The settlement layer's state is unchanged (its transaction reverted). -/
  | failDeposit {s : Sys} {i : ℕ} {m : Msg} :
      s.msgs i = some m → m.status = .pending → m.src = W.l1 →
      Step W s (.failDeposit i) { s with msgs := upd s.msgs i (some { m with status := .failed }) }
  /-- L1 `bridgeConfirmTransferResult` (`L1CAH:122-172`). Environment: the L1 nullifier proved
  the deposit's status and consumes it once. Guards: `zkChain != 0` (`L1CAH:140`), `ctm != 0`
  (`L1CAH:141`); on failure the stored number is 1 (`L1CAH:153-156`), the diamond is away
  (`MIG:324-326`) and at the version the data carries (`MIG:327-330`). No pause flag and no
  `whenMigrationsEnabled` (`L1CAH:119-120`, `:128`). -/
  | confirm {s : Sys} {i : ℕ} {m : Msg} {failure : Bool} :
      s.msgs i = some m → m.src = W.l1 →
      (failure = true → m.status = .failed) → (failure = false → m.status = .executed) →
      s.reg W.l1 m.chain = true → s.ctm W.l1 m.chain ≠ 0 →
      (failure = true → s.migNum W.l1 m.chain = numToSL) →
      (failure = true → s.away W.l1 m.chain = true) →
      (failure = true → s.dpv W.l1 m.chain = m.pv) →
      Step W s (.confirm i m.chain failure) (confirmPost W s i m failure)
  /-- `pauseMigration()`: `onlyOwner` (`CAH:437`). -/
  | pauseMigration {s : Sys} {h : ChainId} {sender : Address} :
      sender = W.owner h →
      Step W s (.pauseMigration h sender) { s with ecoPaused := upd s.ecoPaused h true }
  /-- `unpauseMigration()`: `onlyOwner` (`CAH:443`). -/
  | unpauseMigration {s : Sys} {h : ChainId} {sender : Address} :
      sender = W.owner h →
      Step W s (.unpauseMigration h sender) { s with ecoPaused := upd s.ecoPaused h false }
  /-- `pauseCTMMigration(x)`: `onlyRegisteredCTMOwner(x)` (`CAH:138-146`, `:449`). -/
  | pauseCTM {s : Sys} {h : ChainId} {x sender : Address} :
      W.ctmRegistered h x = true → sender = W.ctmOwner x →
      Step W s (.pauseCTM h x sender) { s with ctmPaused := upd2 s.ctmPaused h x true }
  /-- `unpauseCTMMigration(x)`: `onlyRegisteredCTMOwner(x)` (`CAH:455`). -/
  | unpauseCTM {s : Sys} {h : ChainId} {x sender : Address} :
      W.ctmRegistered h x = true → sender = W.ctmOwner x →
      Step W s (.unpauseCTM h x sender) { s with ctmPaused := upd2 s.ctmPaused h x false }
  /-- `pause()`: `onlyOwner`, then OpenZeppelin `_pause` is `whenNotPaused` (`CAH:476-478`). -/
  | pause {s : Sys} {h : ChainId} {sender : Address} :
      sender = W.owner h → s.paused h = false →
      Step W s (.pause h sender) { s with paused := upd s.paused h true }
  /-- `unpause()`: `onlyOwner`, then `_unpause` is `whenPaused` (`CAH:481-483`). -/
  | unpause {s : Sys} {h : ChainId} {sender : Address} :
      sender = W.owner h → s.paused h = true →
      Step W s (.unpause h sender) { s with paused := upd s.paused h false }
  /-- Environment: a CTM's version strictly increases. -/
  | ctmUpgrade {s : Sys} {h : ChainId} {x : Address} {v : ℕ} :
      s.ctmPV h x < v →
      Step W s (.ctmUpgrade h x v) { s with ctmPV := upd2 s.ctmPV h x v }
  /-- Environment: a registered diamond's version strictly increases (`ADM:559-590`; no
  settlement-layer check, so an away diamond can be upgraded). -/
  | diamondUpgrade {s : Sys} {h c : ChainId} {v : ℕ} :
      s.reg h c = true → s.dpv h c < v →
      Step W s (.diamondUpgrade h c v) { s with dpv := upd2 s.dpv h c v }

/-- A fresh deployment: no chain anywhere, no message. CTM versions and the pause flags are
arbitrary. -/
structure Init (s : Sys) : Prop where
  sl : ∀ h c, s.sl h c = 0
  reg : ∀ h c, s.reg h c = false
  migNum : ∀ h c, s.migNum h c = 0
  inProgress : ∀ c, s.inProgress c = false
  ivActive : ∀ c, s.ivActive c = false
  ivSL : ∀ c, s.ivSL c = 0
  away : ∀ h c, s.away h c = false
  msgs : ∀ i, s.msgs i = none
  nMsgs : s.nMsgs = 0

/-- States reachable from a fresh deployment by any interleaving of steps. -/
inductive Reach (W : World) : Sys → Prop
  | init {s : Sys} : Init s → Reach W s
  | step {s s' : Sys} {l : Label} : Reach W s → Step W s l s' → Reach W s'

/-- A sequence of steps. -/
inductive Run (W : World) : Sys → List Label → Sys → Prop
  | nil {s : Sys} : Run W s [] s
  | cons {s s' s'' : Sys} {l : Label} {ls : List Label} :
      Step W s l s' → Run W s' ls s'' → Run W s (l :: ls) s''

/-! ## Who holds a chain -/

/-- A message is live while it can still move the chain: pending, or failed and not yet
recovered. -/
def Msg.Live (m : Msg) : Prop := m.status = .pending ∨ m.status = .failed

/-- Where a chain can be: settling on a hub, or inside a live message. -/
inductive Holder
  | hub (h : ChainId)
  | msg (i : ℕ)
  deriving DecidableEq

/-- `Holds s c x`: hub `x` is the settlement layer of chain `c` by its own bridgehub
(`settlementLayer[c] == block.chainid`, the check of `BH:411`), or message `x` is a live
migration message for `c`. -/
def Holds (s : Sys) (c : ChainId) : Holder → Prop
  | .hub h => h ≠ 0 ∧ s.sl h c = h
  | .msg i => ∃ m, s.msgs i = some m ∧ m.chain = c ∧ m.Live

/-! ## Label classifiers -/

/-- A step that moves a chain under CTM `x` on hub `h` (a burn or mint whose asset id maps to
`x`). -/
def Label.movesUnder (W : World) (h : ChainId) (x : Address) : Label → Prop
  | .burn h' _ _ a _ => h' = h ∧ W.ctmOfAsset a = x
  | .mint h' _ _ a => h' = h ∧ W.ctmOfAsset a = x
  | _ => False

/-- A burn or a mint on hub `h`. -/
def Label.movesOn (h : ChainId) : Label → Prop
  | .burn h' _ _ _ _ => h' = h
  | .mint h' _ _ _ => h' = h
  | _ => False

/-- An `unpauseCTMMigration(x)` on hub `h`. -/
def Label.unpausesCTM (h : ChainId) (x : Address) : Label → Prop
  | .unpauseCTM h' x' _ => h' = h ∧ x' = x
  | _ => False

/-- An `unpauseMigration()` on hub `h`. -/
def Label.unpausesEcosystem (h : ChainId) : Label → Prop
  | .unpauseMigration h' _ => h' = h
  | _ => False

/-- An `unpause()` on hub `h`. -/
def Label.unpausesHub (h : ChainId) : Label → Prop
  | .unpause h' _ => h' = h
  | _ => False

/-- A `pauseCTMMigration(x)` or `unpauseCTMMigration(x)` on hub `h`, by `sender`. -/
def Label.togglesCTMPause (h : ChainId) (x : Address) (sender : Address) : Label → Prop
  | .pauseCTM h' x' snd => h' = h ∧ x' = x ∧ snd = sender
  | .unpauseCTM h' x' snd => h' = h ∧ x' = x ∧ snd = sender
  | _ => False

/-- A mint of chain `c` on L1 (the end of a round trip). -/
def Label.mintsOnL1 (W : World) (c : ChainId) : Label → Bool
  | .mint h _ c' _ => decide (h = W.l1) && decide (c' = c)
  | _ => false

/-- A burn of chain `c` on L1. -/
def Label.burnsOnL1 (W : World) (c : ChainId) : Label → Prop
  | .burn h c' _ _ _ => h = W.l1 ∧ c' = c
  | _ => False

/-- A burn or a mint of chain `c`, on any hub. -/
def Label.movesChain (c : ChainId) : Label → Prop
  | .burn _ c' _ _ _ => c' = c
  | .mint _ _ c' _ => c' = c
  | _ => False

/-- `pauseMigration()` or `unpauseMigration()` on hub `h`, by `sender`. -/
def Label.togglesEcosystemPause (h : ChainId) (sender : Address) : Label → Prop
  | .pauseMigration h' snd => h' = h ∧ snd = sender
  | .unpauseMigration h' snd => h' = h ∧ snd = sender
  | _ => False

/-- Every pause flag of every hub set: the ecosystem pause, every CTM pause, and `paused()`. -/
def pauseAll (s : Sys) : Sys :=
  { s with ecoPaused := fun _ => true, ctmPaused := fun _ _ => true, paused := fun _ => true }

/-- A diamond upgrade of chain `c` on hub `h`. -/
def Label.upgradesDiamond (h c : ChainId) : Label → Prop
  | .diamondUpgrade h' c' _ => h' = h ∧ c' = c
  | _ => False

/-- Number of round-trip ends of chain `c` (mints on L1) in a label list. -/
def countL1Mints (W : World) (c : ChainId) (ls : List Label) : ℕ :=
  (ls.filter (Label.mintsOnL1 W c)).length

end Contracts.ChainAssetHandler
