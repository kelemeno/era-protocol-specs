import Mathlib.Tactic

/-!
# Model: chains migrating between settlement layers through the chain asset handler

Source: era-contracts `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`; every
`file:line` below is at that commit. Paths are relative to `l1-contracts/contracts/`; the
files modelled are cited as

* `CAH` — `core/chain-asset-handler/ChainAssetHandlerBase.sol`,
* `L1CAH` — `core/chain-asset-handler/L1ChainAssetHandler.sol`,
* `L2CAH` — `core/chain-asset-handler/L2ChainAssetHandler.sol`,

and the callees whose effects or checks are part of a step as

* `BH` — `core/bridgehub/BridgehubBase.sol`, `L1BH` — `core/bridgehub/L1Bridgehub.sol`,
* `CTM` — `state-transition/ChainTypeManager.sol`,
  `DI` — `state-transition/chain-deps/DiamondInit.sol`,
* `MIG` — `state-transition/chain-deps/facets/Migrator.sol`, `ADM` — `.../facets/Admin.sol`,
* `CFG` — `common/Config.sol`.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.ChainAssetHandler.Properties.*`, proofs in
`EraSpec.Contracts.ChainAssetHandler.Proofs.*`.

## The system

A chain is an asset of its chain type manager (CTM). Migrating it is a bridge transfer of
that asset: `bridgeBurn` on the hub it settles on (`CAH:188-254`), a cross-chain message,
then `bridgeMint` on the destination (`CAH:361-420`). An L1 → settlement-layer deposit that
fails on the settlement layer is undone on L1 by `bridgeConfirmTransferResult`
(`L1CAH:122-172`). A chain asset handler runs on every chain: `L1ChainAssetHandler` on L1,
`L2ChainAssetHandler` on each L2. A *hub* is a chain id whose handler, bridgehub, CTMs and
diamonds the model tracks; a settlement layer ("gateway") is a hub. The model is the joint
state of all hubs, indexed by chain id, plus the migration messages in flight.

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
  `failedMigrationNum = 1` (`L1CAH:152-160`). Batch-number fields are not modelled; on L2
  both recorders are no-ops (`L2CAH:136-151`);
* the protocol version of CTM `x` on `h` (`ctmPV h x`), and chain `c`'s diamond on `h`: its
  `s.protocolVersion` (`dpv h c`), its own `s.chainTypeManager` (`dctm h c`, written only by
  `DI:91`), and whether its `s.settlementLayer ≠ 0` (`away h c`).

## Messages

`bridgeBurn` returns the mint data; the asset router sends it to the destination. A message
records source, destination, chain, CTM asset id, the migration number it carries
(`BridgehubMintCTMAssetData.migrationNumber`, `CAH:349`) and the protocol version it carries:
the CTM data is `abi.encode(admin, protocolVersion)` (`CTM:740`), the CTM's version, which
`CTM:735-738` makes equal to the diamond's; the burn's chain data carries the version
`MIG:192-198` makes equal to the diamond's, and the failure path re-reads it (`MIG:322-330`).
Its status is

* `pending` — sent, not yet executed;
* `executed` — the destination's `bridgeMint` ran;
* `failed` — an L1 → settlement-layer deposit whose L2 transaction failed;
* `done` — L1 consumed the deposit's status proof (`bridgeConfirmTransferResult`).

These statuses are the environment's guarantees (`PROTO-CAH-DELIVERY` in ASSUMPTIONS.md):
an L1 → L2 transaction executes once, with outcome success or failure, and its status proof
is truthful; `L1Nullifier._verifyAndClearTransfer` (`bridge/L1Nullifier.sol:218-248`) lets L1
consume each deposit's status once; an L2 → L1 message is finalized at most once and does
not fail permanently (the source assumes "GW -> L1 transactions can never fail",
`MIG:200-202`). A message from L2 waits, `pending`, until its mint on L1 succeeds.

## Modelling choices

* **A revert is the absence of a step.** Each kept guard is listed with its `file:line`.
  Values (`requireZeroValue`), events and the caller check `onlyAssetRouter` (the asset
  router is the only caller of the three handler entry points; a step *is* the router's
  call) are not modelled.
* **Identifiers are `ℕ`.** Chain ids, addresses and asset ids are compared for equality and
  against zero only. Counters are `ℕ`: checked-arithmetic overflow is not modelled, which
  only adds runs.
* **Reject-only checks omitted**, which only adds runs, so every safety result covers the
  source: the chain admin checks (`CAH:225-227`, `MIG:165-167`); `isReadyForMigration`
  (`L1CAH:205`, `:175-190`); the CTM's admin check (`CTM:728-731`); the diamond's priority-mode,
  priority-queue, deposit-pause window and batches-executed checks (`MIG:159-161`, `:170`,
  `:172-176`, `:203-205`); on a returning mint its deposit-pause, permanent-rollup, batch and
  priority-tree checks (`MIG:217-219`, `:234-259`, `:270-276`, `:288`); the base-token checks of
  the mint data (`CAH:337-338`); message-root bookkeeping and batch numbers; the bridgehub's
  `whenNotPaused` on chain creation (`L1BH:113`) and the `_validateChainParams` checks not kept
  in `CreateOk` and `RegisterDeployedOk` (`BH:497-499`, `:510-514`, `:519-521`, `:527-533`); the
  address, chain-id and bridgehub checks of `registerAlreadyDeployedZKChain` (`L1BH:286-288`,
  `:294-296`, `:304-306`); the upgrade engine's bound on an away diamond's new version by its
  settlement layer's diamond (`upgrades/BaseZkSyncUpgrade.sol:89-94`).
* **Fixed configuration** (`World`), per hub where the source stores it per hub: the
  settlement-layer whitelist, the CTM asset-id registry in both directions, CTM registration,
  CTM owners, and the handler's owner. Every result is about one `World`, so it covers runs in
  which these do not change (`OPS-CONFIG`).
* **Versions are environment steps.** `ctmUpgrade` is the CTM's `_commitVersionEdge`, which
  strictly raises its version (`CTM:523-537`); `diamondUpgrade` is the diamond's
  `upgradeChainFromVersion`, which strictly raises its version (`ADM:559-590`, `:587-589`).
  `upgradeChainFromVersion` does not require the diamond to be on its settlement layer, so an
  away diamond can be upgraded (the engine's bound above is omitted). A cut the CTM owner has
  the CTM execute (`executeUpgrade`, `CTM:626-628`, `ADM:593-595`) can rewrite any diamond
  field and is not a step; nor is a CTM or handler code swap.
* **`CHAIN_MIGRATIONS_ENABLED` is a parameter.** At this commit it is `false` (`CFG:320`), so
  in production `bridgeBurn` and `bridgeMint` always revert (`CAH:151-156`);
  `_getChainMigrationsEnabled` is virtual for test variants (`CAH:163-167`).
  `Properties.MigrationsDisabledFreezeSettlement` is the production statement; the other
  results hold for either value, and their witnesses use `true`.
* **Chain registration** is L1's `createNewChain` (`L1BH:108-139`), which has the CTM deploy a
  fresh diamond at its current version, and `registerAlreadyDeployedZKChain`
  (`L1BH:285-319`), which registers an existing diamond under that diamond's own CTM and writes
  nothing to it. Both set `settlementLayer[c] = block.chainid` and refuse a chain that has a
  CTM on L1's bridgehub (`BH:534-536`) or is registered there (`CTM:675-678`; `L1BH:290-293`).
  A settlement layer registers a chain only in `bridgeMint`.
* **A chain's own counter.** `L2ChainAssetHandler.setSettlementLayerChainId` (`L2CAH:116-127`),
  called by the system context at the start of each batch, increments
  `migrationNumber[block.chainid]` on the chain's own handler when the reported settlement
  layer changes. It is a step (`setSLChainId`) with free arguments.
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

/-- Fixed configuration of the ecosystem. Per-hub fields take the hub first. -/
structure World where
  /-- `L1_CHAIN_ID` (`L1CAH:46`; on L2 `L2CAH:35`). -/
  l1 : ChainId
  /-- `_getChainMigrationsEnabled()`: `CHAIN_MIGRATIONS_ENABLED` (`CFG:320`, `false`). -/
  migrationsEnabled : Bool
  /-- `whitelistedSettlementLayers[t]` on the bridgehub of hub `h` (`wl h t`). -/
  wl : ChainId → ChainId → Bool
  /-- `ctmAssetIdToAddress[assetId]` on hub `h` (`BH:437`, `CAH:469`). -/
  ctmOfAsset : ChainId → AssetId → Address
  /-- `ctmAssetIdFromAddress[ctm]` on hub `h` (`BH:354`). -/
  assetOfCTM : ChainId → Address → AssetId
  /-- `chainTypeManagerIsRegistered(ctm)` on hub `h` (`BH:523-525`, `CAH:139-141`). -/
  ctmRegistered : ChainId → Address → Bool
  /-- `IOwnable(ctm).owner()` of CTM `ctm` on hub `h` (`CAH:142-144`). -/
  ctmOwner : ChainId → Address → Address
  /-- The handler's `owner()` on hub `h` (`Ownable2StepUpgradeable`). -/
  owner : ChainId → Address

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
  /-- The protocol version the CTM and chain data carry (`CTM:740`, `MIG:192-198`). -/
  pv : ℕ
  /-- Delivery status. -/
  status : MsgStatus

/-- The joint state of all hubs and the messages between them. -/
structure Sys where
  /-- Bridgehub of hub `h`: `settlementLayer[c]` (`sl h c`). -/
  sl : ChainId → ChainId → ChainId
  /-- Bridgehub of hub `h`: `getZKChain(c) ≠ address(0)` (`BH:344-347`). -/
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
  /-- Diamond of chain `c` on hub `h`: `s.chainTypeManager` (`DI:91`). -/
  dctm : ChainId → ChainId → Address
  /-- Diamond of chain `c` on hub `h`: `s.settlementLayer != address(0)`. -/
  away : ChainId → ChainId → Bool
  /-- Messages, by id. -/
  msgs : ℕ → Option Msg
  /-- The next message id. -/
  nMsgs : ℕ

/-- What happens. Every hub action names its hub `h`. -/
inductive Label
  /-- L1 `createNewChain(c, x, …)` (`L1BH:108-139`). -/
  | createChain (c : ChainId) (x : Address)
  /-- L1 `registerAlreadyDeployedZKChain(c, diamond)` (`L1BH:285-319`). -/
  | registerDeployed (c : ChainId)
  /-- Hub `h`'s `bridgeBurn(t, _, a, _, data)` of chain `c` (`CAH:188-254`). -/
  | burn (h c t : ChainId) (a : AssetId)
  /-- Hub `h`'s `bridgeMint(_, a, data)` executing message `i` for chain `c` (`CAH:361-420`). -/
  | mint (h : ChainId) (i : ℕ) (c : ChainId) (a : AssetId)
  /-- Environment: the L1 → settlement-layer transaction of message `i` fails. -/
  | failDeposit (i : ℕ)
  /-- L1 `bridgeConfirmTransferResult` for message `i` of chain `c`, `failure` or success
  (`L1CAH:122-172`). -/
  | confirm (i : ℕ) (c : ChainId) (failure : Bool)
  /-- The system context's `setSettlementLayerChainId(prev, cur)` on L2 chain `h`
  (`L2CAH:116-127`). -/
  | setSLChainId (h prev cur : ChainId)
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
  /-- Environment: CTM `x` on hub `h` moves to version `v` (`CTM:523-537`). -/
  | ctmUpgrade (h : ChainId) (x : Address) (v : ℕ)
  /-- Environment: the diamond of chain `c` on hub `h` is upgraded to version `v`
  (`ADM:559-590`). -/
  | diamondUpgrade (h c : ChainId) (v : ℕ)

/-! ## Successor states -/

/-- After L1 `createNewChain(c, x, …)`: the bridgehub records `x` (`L1BH:116`) and L1 as the
settlement layer (`L1BH:119`), and registers the diamond `x` deploys (`L1BH:124-133`). The
fresh diamond is at `x`'s version (`DI:58`, `:110`; the genesis upgrade keeps it,
`upgrades/L1GenesisUpgrade.sol:32`, `:42-47`), names `x` as its CTM (`DI:91`), and is not away
(`DI` does not write `s.settlementLayer`). -/
def createPost (W : World) (s : Sys) (c : ChainId) (x : Address) : Sys :=
  { s with
    ctm := upd2 s.ctm W.l1 c x
    sl := upd2 s.sl W.l1 c W.l1
    reg := upd2 s.reg W.l1 c true
    dpv := upd2 s.dpv W.l1 c (s.ctmPV W.l1 x)
    dctm := upd2 s.dctm W.l1 c x
    away := upd2 s.away W.l1 c false }

/-- After L1 `registerAlreadyDeployedZKChain(c, diamond)`: the bridgehub records the
diamond's own CTM (`L1BH:298`, `:310`) and L1 as the settlement layer (`L1BH:313`), and
registers the diamond (`L1BH:315`). The diamond itself is not written. -/
def registerDeployedPost (W : World) (s : Sys) (c : ChainId) : Sys :=
  { s with
    ctm := upd2 s.ctm W.l1 c (s.dctm W.l1 c)
    sl := upd2 s.sl W.l1 c W.l1
    reg := upd2 s.reg W.l1 c true }

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

/-- After `bridgeMint` on hub `h` of message `i` (`m`) for chain `m.chain`, with `x` the CTM
`h`'s registry gives the asset id: the migration number is the carried one (`CAH:384`); on L1
interval 1 is closed (`L1CAH:319`); the bridgehub records `h` and `x` (`BH:445-446`); a chain
not registered here gets a fresh diamond, deployed by `x` (`CAH:399`, `CTM:757`) at `x`'s
version naming `x` (`DI:58`, `:91`, `:110`), registered at `CAH:405`; the diamond is back
(`MIG:299`); the message is executed. -/
def mintPost (W : World) (s : Sys) (h : ChainId) (i : ℕ) (m : Msg) (x : Address)
    (fresh : Bool) : Sys :=
  { s with
    migNum := upd2 s.migNum h m.chain m.num
    ivActive := if h = W.l1 then upd s.ivActive m.chain false else s.ivActive
    sl := upd2 s.sl h m.chain h
    ctm := upd2 s.ctm h m.chain x
    reg := upd2 s.reg h m.chain true
    dpv := if fresh then upd2 s.dpv h m.chain (s.ctmPV h x) else s.dpv
    dctm := if fresh then upd2 s.dctm h m.chain x else s.dctm
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

/-- After `setSettlementLayerChainId(prev, cur)` on L2 chain `h`: nothing for the initial
call on L1 (`L2CAH:120-123`) or an unchanged settlement layer; otherwise
`migrationNumber[block.chainid]` is incremented (`L2CAH:124-126`). -/
def slChainIdPost (W : World) (s : Sys) (h prev cur : ChainId) : Sys :=
  { s with
    migNum := if (prev = 0 ∧ cur = W.l1) ∨ prev = cur then s.migNum
      else upd2 s.migNum h h (s.migNum h h + 1) }

/-! ## Guards -/

/-- The kept guards of L1 `createNewChain(c, x, …)`. `_validateChainParams` (`L1BH:114`): -/
structure CreateOk (W : World) (s : Sys) (c : ChainId) (x : Address) : Prop where
  /-- `c ≠ 0` (`BH:492-494`). -/
  chainNonzero : c ≠ 0
  /-- `c ≠ block.chainid` (`BH:501-503`). -/
  notL1 : c ≠ W.l1
  /-- The CTM is not the zero address (`BH:516-518`). -/
  ctmNonzero : x ≠ 0
  /-- The CTM is registered (`BH:523-525`). -/
  ctmRegistered : W.ctmRegistered W.l1 x = true
  /-- `chainTypeManager[c] == 0` (`BH:534-536`). -/
  noCtm : s.ctm W.l1 c = 0
  /-- The CTM's `_deployNewChain`: `getZKChain(c) == 0` (`CTM:675-678`, via `CTM:704`). -/
  notRegistered : s.reg W.l1 c = false

/-- The kept guards of L1 `registerAlreadyDeployedZKChain(c, diamond)`, with the diamond's
own CTM `s.dctm W.l1 c` (`L1BH:298`). -/
structure RegisterDeployedOk (W : World) (s : Sys) (c : ChainId) : Prop where
  /-- The chain id is not registered (`L1BH:290-293`). -/
  notRegistered : s.reg W.l1 c = false
  /-- `_validateChainParams` (`L1BH:308`): `c ≠ 0` (`BH:492-494`). -/
  chainNonzero : c ≠ 0
  /-- `c ≠ block.chainid` (`BH:501-503`). -/
  notL1 : c ≠ W.l1
  /-- The diamond's CTM is not the zero address (`BH:516-518`). -/
  ctmNonzero : s.dctm W.l1 c ≠ 0
  /-- The diamond's CTM is registered (`BH:523-525`). -/
  ctmRegistered : W.ctmRegistered W.l1 (s.dctm W.l1 c) = true
  /-- `chainTypeManager[c] == 0` (`BH:534-536`). -/
  noCtm : s.ctm W.l1 c = 0

/-- The kept guards of a successful `bridgeBurn(t, _, a, _, data)` on hub `h` of chain `c`. -/
structure BurnOk (W : World) (s : Sys) (h c t : ChainId) (a : AssetId) : Prop where
  /-- `block.chainid ≠ 0`. -/
  hubNonzero : h ≠ 0
  /-- `whenNotPaused` (`CAH:200`). -/
  notPaused : s.paused h = false
  /-- `whenMigrationsEnabled` (`CAH:201`, `:151-156`). -/
  enabled : W.migrationsEnabled = true
  /-- `_requireMigrationsNotPausedFor(a)` (`CAH:204`, `:468-473`, `:432-434`): the ecosystem
  pause is off… -/
  ecoOff : s.ecoPaused h = false
  /-- …and so is the pause of the CTM `h`'s registry gives `a` (`CAH:469`). -/
  ctmOff : s.ctmPaused h (W.ctmOfAsset h a) = false
  /-- `ctmAssetIdFromChainId(c)` reverts for a chain with no CTM (`CAH:207-210`,
  `BH:351-353`)… -/
  ctmSet : s.ctm h c ≠ 0
  /-- …and `a` must be the asset id it returns (`CAH:207-210`, `BH:354`). -/
  asset : a = W.assetOfCTM h (s.ctm h c)
  /-- `forwardedBridgeBurnSetSettlementLayer` (`CAH:217-220`): `t` is whitelisted
  (`BH:407-409`)… -/
  dstListed : W.wl h t = true
  /-- …`settlementLayer[c] == block.chainid` (`BH:411-413`)… -/
  settlesHere : s.sl h c = h
  /-- …and `c` is not itself a whitelisted settlement layer (`BH:416-418`). -/
  notSL : W.wl h c = false
  /-- `zkChainMap.get(c)` reverts for an unregistered chain (`BH:419`; `CAH:222-224`). -/
  registered : s.reg h c = true
  /-- The CTM's `forwardedBridgeBurn` (`CAH:229`): the diamond is at the CTM's version
  (`CTM:735-738`). -/
  atCtmVersion : s.dpv h c = s.ctmPV h (s.ctm h c)
  /-- A destination other than L1 has the chain's CTM on `h`'s bridgehub (`CAH:232-237`). -/
  sameCtm : t ≠ W.l1 → s.ctm h t = s.ctm h c
  /-- Off L1 the destination is L1 (`CAH:239-241`). -/
  toL1 : h ≠ W.l1 → t = W.l1
  /-- The diamond's `forwardedBridgeBurn` (`CAH:267-273`): not already away (`MIG:162-164`). -/
  notAway : s.away h c = false
  /-- …for a destination other than L1, `getZKChain(t)` (`CAH:268-270`) is a diamond, called
  at `MIG:182` (the diamond registered for `t` reports chain id `t`: `DI` stores its
  `_chainId`, and `registerAlreadyDeployedZKChain` checks it, `L1BH:294-296`), under the
  migrating diamond's own CTM (`MIG:186-188`). -/
  dstDiamond : t ≠ W.l1 → s.reg h t = true ∧ s.dctm h c = s.ctm h t
  /-- `migrationNumber[c] < MAX_ALLOWED_NUMBER_OF_MIGRATIONS` (`CAH:277`). -/
  belowMax : s.migNum h c < maxMigrations
  /-- On L1, `_recordMigrationToSL` (`CAH:285-287`): `t ≠ L1` (`L1CAH:283-285`) and the new
  number is `MIGRATION_NUMBER_L1_TO_SETTLEMENT_LAYER` (`L1CAH:286-289`). -/
  l1Record : h = W.l1 → t ≠ W.l1 ∧ s.migNum h c + 1 = numToSL

/-- The kept guards shared by both `bridgeMint` branches on hub `h` executing message `i`. -/
structure MintOk (W : World) (s : Sys) (h : ChainId) (i : ℕ) (m : Msg) : Prop where
  /-- Environment (`PROTO-CAH-DELIVERY`): message `i` is `m`… -/
  msgAt : s.msgs i = some m
  /-- …pending… -/
  pending : m.status = .pending
  /-- …and for hub `h`. -/
  forHub : m.dst = h
  /-- `block.chainid ≠ 0`. -/
  hubNonzero : h ≠ 0
  /-- `whenNotPaused` (`CAH:365`). -/
  notPaused : s.paused h = false
  /-- `whenMigrationsEnabled` (`CAH:365`). -/
  enabled : W.migrationsEnabled = true
  /-- `_requireMigrationsNotPausedFor(a)` (`CAH:366`): the ecosystem pause is off… -/
  ecoOff : s.ecoPaused h = false
  /-- …and so is the pause of the CTM `h`'s registry gives the asset id (`CAH:469`). -/
  ctmOff : s.ctmPaused h (W.ctmOfAsset h m.asset) = false
  /-- On L1 the stored number is 1 and the carried one 2 (`CAH:374-383`). -/
  l1Numbers : h = W.l1 → s.migNum h m.chain = numToSL ∧ m.num = numToL1
  /-- On L1 `_recordMigrationFromSL` (`CAH:385-389`) needs interval 1 active (`L1CAH:314`). -/
  l1Interval : h = W.l1 → s.ivActive m.chain = true
  /-- `forwardedBridgeMint` (`CAH:391-395`): the asset id has a CTM (`BH:437-440`)… -/
  ctmKnown : W.ctmOfAsset h m.asset ≠ 0
  /-- …and `settlementLayer[c] != block.chainid` (`BH:441-443`). -/
  notHere : s.sl h m.chain ≠ h

/-- The kept guards of L1 `bridgeConfirmTransferResult` for message `i` (`m`). -/
structure ConfirmOk (W : World) (s : Sys) (i : ℕ) (m : Msg) (failure : Bool) : Prop where
  /-- Environment (`PROTO-CAH-DELIVERY`): the L1 nullifier proved the deposit's status and
  consumes it once. Message `i` is `m`… -/
  msgAt : s.msgs i = some m
  /-- …an L1 deposit… -/
  fromL1 : m.src = W.l1
  /-- …whose L2 transaction failed, for a failure… -/
  failed : failure = true → m.status = .failed
  /-- …or succeeded, for a success. -/
  executed : failure = false → m.status = .executed
  /-- `zkChain != 0` (`L1CAH:140`; `BH:463`). -/
  registered : s.reg W.l1 m.chain = true
  /-- `ctm != 0` (`L1CAH:141`; `BH:464`). -/
  ctmSet : s.ctm W.l1 m.chain ≠ 0
  /-- On failure the stored number is 1 (`L1CAH:152-156`)… -/
  failNum : failure = true → s.migNum W.l1 m.chain = numToSL
  /-- …the diamond is away (`MIG:324-326`)… -/
  failAway : failure = true → s.away W.l1 m.chain = true
  /-- …and at the version the data carries (`MIG:327-330`). -/
  failPv : failure = true → s.dpv W.l1 m.chain = m.pv

/-! ## Steps -/

/-- One successful call. A revert is the absence of a step. -/
inductive Step (W : World) : Sys → Label → Sys → Prop
  /-- L1 `createNewChain`. -/
  | createChain {s : Sys} {c : ChainId} {x : Address} :
      CreateOk W s c x → Step W s (.createChain c x) (createPost W s c x)
  /-- L1 `registerAlreadyDeployedZKChain`. -/
  | registerDeployed {s : Sys} {c : ChainId} :
      RegisterDeployedOk W s c → Step W s (.registerDeployed c) (registerDeployedPost W s c)
  /-- `bridgeBurn` on hub `h` (`CAH:188-254`). -/
  | burn {s : Sys} {h c t : ChainId} {a : AssetId} :
      BurnOk W s h c t a → Step W s (.burn h c t a) (burnPost W s h c t a)
  /-- `bridgeMint` on hub `h` of a chain with no diamond here: the CTM checks the carried
  version against its own (`CTM:754-756`) and deploys one (`CAH:398-409`, `CTM:757`); on L1 a
  fresh diamond is refused (`MIG:277-279`, `ContractNotDeployed`). The fresh diamond passes
  `MIG:225-229` (it is at its CTM's version). -/
  | mintFresh {s : Sys} {h : ChainId} {i : ℕ} {m : Msg} :
      MintOk W s h i m →
      s.reg h m.chain = false →
      m.pv = s.ctmPV h (W.ctmOfAsset h m.asset) →
      h ≠ W.l1 →
      Step W s (.mint h i m.chain m.asset) (mintPost W s h i m (W.ctmOfAsset h m.asset) true)
  /-- `bridgeMint` on hub `h` of a chain whose diamond is registered here: the diamond is
  reused (`CAH:397`, `:410-417`). Its `forwardedBridgeMint` requires its version to be its
  own CTM's (`MIG:223-229`) and the diamond to be away (`MIG:280-282` on L1, `:285-287`
  elsewhere). The carried version is not read. -/
  | mintReturn {s : Sys} {h : ChainId} {i : ℕ} {m : Msg} :
      MintOk W s h i m →
      s.reg h m.chain = true →
      s.dpv h m.chain = s.ctmPV h (s.dctm h m.chain) →
      s.away h m.chain = true →
      Step W s (.mint h i m.chain m.asset) (mintPost W s h i m (W.ctmOfAsset h m.asset) false)
  /-- Environment: a pending L1 → settlement-layer deposit fails on the settlement layer.
  The settlement layer's state is unchanged (its transaction reverted). -/
  | failDeposit {s : Sys} {i : ℕ} {m : Msg} :
      s.msgs i = some m → m.status = .pending → m.src = W.l1 →
      Step W s (.failDeposit i) { s with msgs := upd s.msgs i (some { m with status := .failed }) }
  /-- L1 `bridgeConfirmTransferResult` (`L1CAH:122-172`). The handler entry point has no pause
  flag and no `whenMigrationsEnabled` (`L1CAH:119-120`, `:128`). -/
  | confirm {s : Sys} {i : ℕ} {m : Msg} {failure : Bool} :
      ConfirmOk W s i m failure →
      Step W s (.confirm i m.chain failure) (confirmPost W s i m failure)
  /-- `setSettlementLayerChainId` on L2 chain `h` (`L2CAH:116-127`): `onlySystemContext`
  (`L2CAH:119`, `CAH:169-174`), whose arguments are the environment's. -/
  | setSLChainId {s : Sys} {h prev cur : ChainId} :
      h ≠ 0 → h ≠ W.l1 → Step W s (.setSLChainId h prev cur) (slChainIdPost W s h prev cur)
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
      W.ctmRegistered h x = true → sender = W.ctmOwner h x →
      Step W s (.pauseCTM h x sender) { s with ctmPaused := upd2 s.ctmPaused h x true }
  /-- `unpauseCTMMigration(x)`: `onlyRegisteredCTMOwner(x)` (`CAH:455`). -/
  | unpauseCTM {s : Sys} {h : ChainId} {x sender : Address} :
      W.ctmRegistered h x = true → sender = W.ctmOwner h x →
      Step W s (.unpauseCTM h x sender) { s with ctmPaused := upd2 s.ctmPaused h x false }
  /-- `pause()`: `onlyOwner`, then OpenZeppelin `_pause` is `whenNotPaused` (`CAH:476-478`). -/
  | pause {s : Sys} {h : ChainId} {sender : Address} :
      sender = W.owner h → s.paused h = false →
      Step W s (.pause h sender) { s with paused := upd s.paused h true }
  /-- `unpause()`: `onlyOwner`, then `_unpause` is `whenPaused` (`CAH:481-483`). -/
  | unpause {s : Sys} {h : ChainId} {sender : Address} :
      sender = W.owner h → s.paused h = true →
      Step W s (.unpause h sender) { s with paused := upd s.paused h false }
  /-- Environment: a CTM's version strictly increases (`CTM:532-535`). -/
  | ctmUpgrade {s : Sys} {h : ChainId} {x : Address} {v : ℕ} :
      s.ctmPV h x < v →
      Step W s (.ctmUpgrade h x v) { s with ctmPV := upd2 s.ctmPV h x v }
  /-- Environment: a diamond's version strictly increases (`ADM:587-589`). No guard reads
  whether the diamond is away (see the module docstring). -/
  | diamondUpgrade {s : Sys} {h c : ChainId} {v : ℕ} :
      s.dpv h c < v →
      Step W s (.diamondUpgrade h c v) { s with dpv := upd2 s.dpv h c v }

/-- A fresh deployment: no chain registered anywhere, no CTM recorded, no migration number,
interval or in-progress flag, no message, and no diamond away. A diamond's
`s.settlementLayer` is written only by the Migrator's three entry points (`MIG:207`, `:299`,
`:332`), all `onlyChainAssetHandler` of the diamond's own bridgehub
(`state-transition/chain-deps/facets/ZKChainBase.sol:113-118`), and that handler's
`bridgeBurn` needs the chain registered there (`BH:419`); `DiamondInit` does not write it, and
`registerAlreadyDeployedZKChain` registers only diamonds it set up (`OPS-CONFIG`). CTM
versions, diamond versions and CTMs, and the pause flags are arbitrary. -/
structure Init (s : Sys) : Prop where
  sl : ∀ h c, s.sl h c = 0
  reg : ∀ h c, s.reg h c = false
  ctm : ∀ h c, s.ctm h c = 0
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

/-- A step that moves a chain under CTM `x` on hub `h` (a burn or mint whose asset id `h`'s
registry maps to `x`). -/
def Label.movesUnder (W : World) (h : ChainId) (x : Address) : Label → Prop
  | .burn h' _ _ a => h' = h ∧ W.ctmOfAsset h a = x
  | .mint h' _ _ a => h' = h ∧ W.ctmOfAsset h a = x
  | _ => False

/-- A burn or a mint on hub `h`. -/
def Label.movesOn (h : ChainId) : Label → Prop
  | .burn h' _ _ _ => h' = h
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
  | .burn h c' _ _ => h = W.l1 ∧ c' = c
  | _ => False

/-- A burn or a mint of chain `c`, on any hub. -/
def Label.movesChain (c : ChainId) : Label → Prop
  | .burn _ c' _ _ => c' = c
  | .mint _ _ c' _ => c' = c
  | _ => False

/-- `pauseMigration()` or `unpauseMigration()` on hub `h`, by `sender`. -/
def Label.togglesEcosystemPause (h : ChainId) (sender : Address) : Label → Prop
  | .pauseMigration h' snd => h' = h ∧ snd = sender
  | .unpauseMigration h' snd => h' = h ∧ snd = sender
  | _ => False

/-- Every pause flag of every hub's handler set: the ecosystem pause, every CTM pause, and
`paused()`. -/
def pauseAll (s : Sys) : Sys :=
  { s with ecoPaused := fun _ => true, ctmPaused := fun _ _ => true, paused := fun _ => true }

/-- Every pause flag of every hub's handler other than `h` set; `h`'s flags kept. -/
def pauseAllBut (h : ChainId) (s : Sys) : Sys :=
  { s with
    ecoPaused := fun h' => if h' = h then s.ecoPaused h' else true
    ctmPaused := fun h' x => if h' = h then s.ctmPaused h' x else true
    paused := fun h' => if h' = h then s.paused h' else true }

/-- Number of round-trip ends of chain `c` (mints on L1) in a label list. -/
def countL1Mints (W : World) (c : ChainId) (ls : List Label) : ℕ :=
  (ls.filter (Label.mintsOnL1 W c)).length

/-! ## Witness data

L1 is chain `1`, the gateway chain `2`, the migrating chain `3`. One CTM, address `7` on
both hubs, with asset id `5` in both directions of both registries; it is registered on both
hubs, owned by `11`; both handlers are owned by `10`. Every bridgehub whitelists L1, as its
initializer does (`BH:169-172`), and L1's also whitelists the gateway. -/

/-- The witness ecosystem, with migrations enabled. -/
def cahWorld : World where
  l1 := 1
  migrationsEnabled := true
  wl := fun h t => decide (t = 1 ∨ (h = 1 ∧ t = 2))
  ctmOfAsset := fun _ a => if a = 5 then 7 else 0
  assetOfCTM := fun _ x => if x = 7 then 5 else 0
  ctmRegistered := fun _ x => decide (x = 7)
  ctmOwner := fun _ _ => 11
  owner := fun _ => 10

/-- The witness ecosystem with the production constant `CHAIN_MIGRATIONS_ENABLED = false`. -/
def cahWorldDisabled : World := { cahWorld with migrationsEnabled := false }

/-- The witness ecosystem with L1's `ctmAssetIdToAddress` mapping asset id `5` to CTM `8`,
while L1's `ctmAssetIdFromAddress` still gives CTM `7` asset id `5`. -/
def cahWorldMismatched : World :=
  { cahWorld with
    ctmOfAsset := fun h a => if h = 1 ∧ a = 5 then 8 else cahWorld.ctmOfAsset h a }

/-- The witness fresh deployment: every CTM at version `1`, no flag set. -/
def cahInit : Sys where
  sl := fun _ _ => 0
  reg := fun _ _ => false
  ctm := fun _ _ => 0
  migNum := fun _ _ => 0
  inProgress := fun _ => false
  ivActive := fun _ => false
  ivSL := fun _ => 0
  ecoPaused := fun _ => false
  ctmPaused := fun _ _ => false
  paused := fun _ => false
  ctmPV := fun _ _ => 1
  dpv := fun _ _ => 0
  dctm := fun _ _ => 0
  away := fun _ _ => false
  msgs := fun _ => none
  nMsgs := 0

/-- The gateway and chain `3` are created on L1 under CTM `7`. -/
def cahSetup : List Label := [.createChain 2 7, .createChain 3 7]

/-- Chain `3`'s complete round trip: L1 burns it to the gateway (message `0`), the gateway
mints it, L1 confirms the deposit's success, the gateway burns it back (message `1`), and L1
mints it. -/
def cahRoundTrip : List Label :=
  cahSetup ++ [.burn 1 3 2 5, .mint 2 0 3 5, .confirm 0 3 false, .burn 2 3 1 5, .mint 1 1 3 5]

/-- Chain `3`'s failed attempt: L1 burns it to the gateway, the deposit fails, and L1
recovers it. -/
def cahFailedAttempt : List Label :=
  cahSetup ++ [.burn 1 3 2 5, .failDeposit 0, .confirm 0 3 true]

end Contracts.ChainAssetHandler
