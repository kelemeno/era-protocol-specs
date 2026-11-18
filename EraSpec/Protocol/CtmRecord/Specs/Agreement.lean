import Mathlib.Tactic

/-!
# Model: the Bridgehub's CTM record and the CTM a chain's diamond obeys, on every layer

Source: era-contracts `draft/v0.35.0` at `b17415d20` (the v35 head). Paths are relative to
`l1-contracts/contracts/` and cited as

* `BB` — `core/bridgehub/BridgehubBase.sol`, `L1BH` — `core/bridgehub/L1Bridgehub.sol`,
  `L2BH` — `core/bridgehub/L2Bridgehub.sol`;
* `CAH` — `core/chain-asset-handler/ChainAssetHandlerBase.sol`,
  `L1CAH` — `core/chain-asset-handler/L1ChainAssetHandler.sol`;
* `CTM` — `state-transition/ChainTypeManager.sol`;
* `DI` — `state-transition/chain-deps/DiamondInit.sol`; `ZCB`, `ADM`, `MIG`, `GET` — the
  facets `ZKChainBase.sol`, `Admin.sol`, `Migrator.sol`, `Getters.sol` under
  `state-transition/chain-deps/facets/`;
* `TRK` — `core/ctm-deployment/CTMDeploymentTracker.sol`; `CFG` — `common/Config.sol`.

On `main` at `70096e2ea` the Bridgehub code modelled here is the same (`setCTMAssetAddress`
writes at `BB:291-292`, `forwardedBridgeMint` writes the record at `BB:447`, the L1 registrations
at `L1BH:123` and `:317`); there `DiamondInit` copies `s.chainTypeManager` from its init data
(`DI:82`), which the CTM fills with `address(this)` (`ChainTypeManagerBase.sol:631`), and the
chain asset handler has one ecosystem-wide migration pause and no per-CTM one.

**This file is definitions only.** Statements are in
`EraSpec.Protocol.CtmRecord.Properties.Agreement`, proofs in
`EraSpec.Protocol.CtmRecord.Proofs.Agreement`.

## The two fields

A chain `c` that lives on layer `h` (L1, or a ZK chain acting as settlement layer) has two
notions of "its CTM" there:

* the Bridgehub's record `chainTypeManager[c]` (`BB:75`), which the chain asset handler reads
  when `c` migrates: the CTM whose `forwardedBridgeBurn` and version check run
  (`CAH:217-229`, `BB:420`, `CTM:735-738`), and, through `ctmAssetIdFromChainId`
  (`BB:349-355`, `CAH:207-210`), the asset id whose CTM's migration pause gates the burn
  (`CAH:204`, `:468-473`);
* the diamond's own `s.chainTypeManager`, written once, by `DiamondInit` as `msg.sender`
  (`DI:91`: the CTM deploying the proxy, `CTM:688`). It is the only caller the diamond's
  `onlyChainTypeManager` admits (`ZCB:85-90`), so the only CTM that can `executeUpgrade`,
  `freezeDiamond` or `unfreezeDiamond` it (`ADM:593`, `:616`, `:629`, reached from
  `CTM:577-586`, `:626-628`), and the CTM whose cut `upgradeChainFromVersion` applies
  (`ADM:566`).

The record is written when a chain is registered (`L1BH:116`, `L1BH:310`) and on every
migration mint, from the asset id the migration message carries, with no comparison against
the diamond (`BB:437`, `:446`):

    ctm = ctmAssetIdToAddress[_assetId];                     // BB:437
    if (ctm == address(0)) { revert NoCTMForAssetId(_assetId); } // BB:438-440
    ...
    chainTypeManager[_chainId] = ctm;                         // BB:446

The two asset maps are written together, and only, by `setCTMAssetAddress` (`BB:268-293`),
which overwrites the two entries it names and clears neither the forward entry of the CTM's
previous asset id nor the reverse entry of the asset id's previous CTM:

    // BB:289
    bytes32 ctmAssetId = DataEncoding.encodeAssetId(_getL1ChainId(), _additionalData, sender);
    ctmAssetIdToAddress[ctmAssetId] = _assetAddress;          // BB:290
    ctmAssetIdFromAddress[_assetAddress] = ctmAssetId;        // BB:291

Its caller must be the `l1CtmDeployer`, unaliased off L1 (`BB:280-284`). That is the
`CTMDeploymentTracker`, which registers `(bytes32(x), x)` on L1 (`TRK:71-80`) and, on a
settlement layer, any owner-chosen pair `(bytes32(ctmL1), ctmL2)` through an L1 → L2
transaction (`TRK:106-126`, `:155-175`).

## State

Per layer `h`: the record `bhCtm h c`; the diamond `zkChainMap` holds for `c`
(`BB:88`, `getZKChain` `BB:344-347`), represented by its `s.chainTypeManager` (`none` when
the map has no entry); the two asset maps; `settlementLayer[c]` (`BB:109`). Plus the
migration messages sent so far (ghost).

## Operations (every writer of the modelled fields)

* `createNewChain` (`L1BH:108-139`) and `registerAlreadyDeployedZKChain` (`L1BH:285-319`), on
  L1 only (`L2BH` has neither);
* `setCTMAssetAddress` on any layer (`BB:268-293`);
* the chain asset handler's `bridgeBurn` (`CAH:188-254`) with
  `forwardedBridgeBurnSetSettlementLayer` (`BB:403-421`), its `bridgeMint` (`CAH:361-420`)
  with `forwardedBridgeMint` (`BB:432-453`), `CTM.forwardedBridgeMint` (`CTM:746-758`) and
  `registerNewZKChain` (`BB:483-489`), and L1's `bridgeConfirmTransferResult`
  (`L1CAH:122-172`) with `forwardedBridgeConfirmTransferResult` (`BB:459-468`).

Bridgehub storage is written only by `BB`, `L1BH` and `L2BH` code. There `chainTypeManager[..]`
is written at `L1BH:116`, `:310` and `BB:446` only, the two asset maps at `BB:290-291` only,
and `zkChainMap` at `BB:303` only (in `_registerNewZKChain`, called at `L1BH:133`, `:315` and
`BB:488`). Outside `dev-contracts/`, no code at `b17415d20` writes a diamond's
`s.chainTypeManager` other than `DI:91`.

## Modelling choices

* **A revert is the absence of a step.** Each kept guard cites its line. Reject-only checks
  are omitted, which only adds runs: callers (`onlyChainAssetHandler`, `onlyAssetRouter`,
  owners, admins), pauses and `whenMigrationsEnabled` (`CAH:198-201`, `:365`; `CFG:320` sets
  `CHAIN_MIGRATIONS_ENABLED = false`, so at `b17415d20` every `bridgeBurn` and `bridgeMint`
  reverts, while `bridgeConfirmTransferResult` is deliberately ungated, `L1CAH:119-120`),
  the settlement-layer whitelist (`BB:407-409`, `:416-418`), the new admin (`CTM:728-731`),
  protocol versions (`CTM:735-738`, `:754-756`, `MIG:192-198`, `:223-229`), migration numbers
  (`CAH:274-279`, `:372-384`, `L1CAH:286-289`, `:309-314`), the settlement layer's own
  identity (`MIG:182-185`), priority queues, deposit pauses, batches, base tokens, the
  message root, chain-count limits, `_validateChainParams`' asset-id and registration
  checks, and `isReadyForMigration`.
* **Messages persist.** A burn appends its message; a mint needs the message to be among
  those sent and does not consume it. Replays and the mint of a failed transfer are therefore
  steps, a superset of the source's runs.
* **Genuine code** (`OPS-CONFIG`): every CTM the Bridgehub calls runs `ChainTypeManager.sol`,
  whose `_deployNewChain` (`CTM:674-692`) creates a diamond whose `DiamondInit` writes
  `s.chainTypeManager = msg.sender`, the CTM (`DI:53`, `:91`; the proxy's constructor
  delegatecalls it, `DiamondProxy.sol:16-20`); the Bridgehub's `chainAssetHandler` is the
  chain asset handler; `registerAlreadyDeployedZKChain` reads the diamond's stored field
  through `getChainTypeManager()` (`L1BH:298`, `GET:59-61`). A cut by the diamond's CTM
  whose init writes `s.chainTypeManager` is outside the model.
* **Asset ids.** `enc h d` is the id `setCTMAssetAddress(d, _)` computes on layer `h`,
  `keccak256(abi.encode(L1_CHAIN_ID, l1CtmDeployer, d))` (`BB:289`,
  `DataEncoding.sol:125-127`). It is uninterpreted and may differ between layers. Only
  `PairDiscipline` constrains it, and only on the run's own registration words; `NoRebind`
  asks only that one registration's id be nonzero. In the source every layer uses one
  function (the same `L1_CHAIN_ID`, `L2BH:34`, `:78`, and the same tracker), and the witnesses
  use one.
* **A registered CTM is nonzero.** `setCTMAssetAddress` requires
  `chainTypeManagerIsRegistered[_assetAddress]` (`BB:285-287`), and `addChainTypeManager`
  refuses `address(0)` (`BB:228-230`); the model keeps only `ctm ≠ 0`.
* **Identifiers are `ℕ`**, compared for equality and against zero only.
-/

namespace Protocol.CtmRecord

/-- A chain id (`uint256`). A layer is named by its chain id. -/
abbrev ChainId := ℕ
/-- An address; `0` is `address(0)`. -/
abbrev Address := ℕ
/-- A CTM asset id (`bytes32`); `0` is the unset entry. -/
abbrev AssetId := ℕ
/-- `setCTMAssetAddress`'s `_additionalData` (`bytes32`). -/
abbrev Word := ℕ

/-- Point update of a per-layer mapping: entry `k` on layer `h` becomes `v`. -/
def upd2 {β γ : Type} [DecidableEq β] (f : ChainId → β → γ) (h : ChainId) (k : β) (v : γ) :
    ChainId → β → γ :=
  fun h' k' => if h' = h ∧ k' = k then v else f h' k'

/-- Deployment constants. -/
structure World where
  /-- `L1_CHAIN_ID`: `block.chainid` on L1 (`L1BH:56`), the stored value on a settlement
  layer (`L2BH:34`, written by `updateL2`, `:78`). -/
  l1 : ChainId
  /-- The asset id `setCTMAssetAddress(d, _)` computes on layer `h` (`BB:289`). -/
  enc : ChainId → Word → AssetId

/-- A migration message: the chain, the CTM asset id the asset router carries from the burn
to the mint (`CAH:191`, `:363`), the layer that burned and the destination layer
(`_settlementChainId`). -/
structure Msg where
  chain : ChainId
  asset : AssetId
  src : ChainId
  dst : ChainId
  deriving DecidableEq

/-- The modelled storage of every layer. -/
structure Sys where
  /-- `chainTypeManager[c]` on layer `h`'s Bridgehub (`BB:75`). -/
  bhCtm : ChainId → ChainId → Address
  /-- The diamond layer `h`'s `zkChainMap` holds for chain `c` (`BB:88`), as its
  `s.chainTypeManager` (`ZKChainStorage.sol:187`); `none` when the map has no entry. -/
  diamond : ChainId → ChainId → Option Address
  /-- `ctmAssetIdToAddress` (`BB:103`). -/
  assetCtm : ChainId → AssetId → Address
  /-- `ctmAssetIdFromAddress` (`BB:106`). -/
  ctmAsset : ChainId → Address → AssetId
  /-- `settlementLayer[c]` (`BB:109`). -/
  settlement : ChainId → ChainId → ChainId
  /-- The migration messages sent so far (ghost; nothing removes one). -/
  sent : List Msg

/-- Fresh storage on every layer: every mapping is zero, no diamond, no message. -/
def Sys.init : Sys where
  bhCtm := fun _ _ => 0
  diamond := fun _ _ => none
  assetCtm := fun _ _ => 0
  ctmAsset := fun _ _ => 0
  settlement := fun _ _ => 0
  sent := []

/-- The L1 writes of a chain registration with CTM `x`: the record (`L1BH:116`, `:310`), the
settlement layer (`L1BH:119`, `:313`) and the `zkChainMap` entry (`L1BH:133`, `:315`) for a
diamond whose `s.chainTypeManager` is `x`. -/
def Sys.addChain (W : World) (s : Sys) (c : ChainId) (x : Address) : Sys :=
  { s with
    bhCtm := upd2 s.bhCtm W.l1 c x
    settlement := upd2 s.settlement W.l1 c W.l1
    diamond := upd2 s.diamond W.l1 c (some x) }

/-- The calls that write the modelled fields. -/
inductive Op
  /-- `L1Bridgehub.createNewChain(c, ctm, _, _)`; the CTM deploys the diamond. -/
  | createNewChain (c : ChainId) (ctm : Address)
  /-- `L1Bridgehub.registerAlreadyDeployedZKChain(c, _)` of a diamond whose
  `getChainTypeManager()` is `ctm`. -/
  | registerAlreadyDeployed (c : ChainId) (ctm : Address)
  /-- `setCTMAssetAddress(d, ctm)` on layer `h`, by the `l1CtmDeployer`. -/
  | setCTMAssetAddress (h : ChainId) (d : Word) (ctm : Address)
  /-- The chain asset handler's `bridgeBurn` of chain `c` on layer `h` towards `dst`. -/
  | bridgeBurn (h c dst : ChainId)
  /-- The chain asset handler's `bridgeMint` of message `m` on `m.dst`. -/
  | bridgeMint (m : Msg)
  /-- L1's `bridgeConfirmTransferResult` with status `Failure` for chain `c`. -/
  | confirmFailure (c : ChainId)

/-- One successful call. -/
inductive Step (W : World) : Sys → Op → Sys → Prop
  /-- `createNewChain` (`L1BH:108-139`): `_validateChainParams` (`L1BH:114`, `BB:491-537`),
  then the CTM deploys (`L1BH:124-127`; `CTM:703-711`, `:674-692`). -/
  | createNewChain {s : Sys} {c : ChainId} {x : Address} :
      c ≠ 0 →                       -- ZeroChainId                 BB:492-494
      c ≠ W.l1 →                    -- ChainIdCantBeCurrentChain   BB:501-503
      x ≠ 0 →                       -- ZeroAddress                 BB:516-518
      s.bhCtm W.l1 c = 0 →          -- BridgeHubAlreadyRegistered  BB:534-536
      s.diamond W.l1 c = none →     -- ChainAlreadyLive            CTM:675-678
      Step W s (.createNewChain c x) (s.addChain W c x)
  /-- `registerAlreadyDeployedZKChain` (`L1BH:285-319`); `x` is the diamond's
  `getChainTypeManager()` (`L1BH:298`). -/
  | registerAlreadyDeployed {s : Sys} {c : ChainId} {x : Address} :
      s.diamond W.l1 c = none →     -- ChainIdAlreadyExists        L1BH:290-293
      c ≠ 0 →                       -- via L1BH:308                BB:492-494
      c ≠ W.l1 →                    --                             BB:501-503
      x ≠ 0 →                       --                             BB:516-518
      s.bhCtm W.l1 c = 0 →          --                             BB:534-536
      Step W s (.registerAlreadyDeployed c x) (s.addChain W c x)
  /-- `setCTMAssetAddress` (`BB:268-293`) on layer `h`. -/
  | setCTMAssetAddress {s : Sys} {h : ChainId} {d : Word} {y : Address} :
      y ≠ 0 →                       -- CTMNotRegistered            BB:285-287 (BB:228-230)
      Step W s (.setCTMAssetAddress h d y)
        { s with
          assetCtm := upd2 s.assetCtm h (W.enc h d) y          -- BB:290
          ctmAsset := upd2 s.ctmAsset h y (W.enc h d) }        -- BB:291
  /-- `bridgeBurn` (`CAH:188-254`) of chain `c` on layer `h`. The burned asset id is forced to
  `ctmAssetIdFromChainId(c)` (`CAH:207-210`). -/
  | bridgeBurn {s : Sys} {h c dst : ChainId} {D : Address} :
      s.bhCtm h c ≠ 0 →             -- ChainIdNotRegistered        BB:351-353 (CAH:208)
      s.settlement h c = h →        -- NotCurrentSettlementLayer   BB:411-413
      s.diamond h c = some D →      -- zkChainMap.get              BB:419; CAH:222-224
      (dst ≠ W.l1 → s.bhCtm h dst = s.bhCtm h c) →   -- SLHasDifferentCTM CAH:232-237
      (h ≠ W.l1 → dst = W.l1) →     -- MigrationNotToL1            CAH:239-241
      (h = W.l1 → dst ≠ W.l1) →     -- SettlementLayerMustNotBeL1  L1CAH:283-285
      (dst ≠ W.l1 → D = s.bhCtm h dst) →             -- SettlementLayerCTMMismatch MIG:181-189
      Step W s (.bridgeBurn h c dst)
        { s with
          settlement := upd2 s.settlement h c dst                                 -- BB:414
          sent := s.sent ++ [⟨c, s.ctmAsset h (s.bhCtm h c), h, dst⟩] }
  /-- `bridgeMint` (`CAH:361-420`) of message `m` on its destination: `forwardedBridgeMint`
  (`BB:432-453`), then, when the chain has no diamond there, `CTM.forwardedBridgeMint` of the
  CTM just written as the record deploys one (`CAH:398-405`, `CTM:746-758`, `DI:91`), and
  otherwise the existing diamond is kept (`CAH:410-415`). -/
  | bridgeMint {s : Sys} {m : Msg} :
      m ∈ s.sent →                  -- the message was sent (transport)
      s.assetCtm m.dst m.asset ≠ 0 →                 -- NoCTMForAssetId  BB:437-440
      s.settlement m.dst m.chain ≠ m.dst →           -- AlreadyCurrentSL BB:441-443
      (m.dst = W.l1 → s.diamond m.dst m.chain ≠ none) → -- ContractNotDeployed MIG:277-279
      Step W s (.bridgeMint m)
        { s with
          settlement := upd2 s.settlement m.dst m.chain m.dst                    -- BB:445
          bhCtm := upd2 s.bhCtm m.dst m.chain (s.assetCtm m.dst m.asset)          -- BB:446
          diamond := upd2 s.diamond m.dst m.chain
            (some ((s.diamond m.dst m.chain).getD (s.assetCtm m.dst m.asset))) }  -- CAH:398-405
  /-- `bridgeConfirmTransferResult` with `TxStatus.Failure` on L1 (`L1CAH:122-172`). -/
  | confirmFailure {s : Sys} {c : ChainId} {D : Address} :
      s.diamond W.l1 c = some D →   -- ZKChainNotRegistered        L1CAH:140 (BB:463)
      s.bhCtm W.l1 c ≠ 0 →          -- CTMNotRegistered            L1CAH:141 (BB:464)
      Step W s (.confirmFailure c)
        { s with settlement := upd2 s.settlement W.l1 c W.l1 }                   -- BB:465-467

/-! ## The asset-registration discipline -/

/-- One `setCTMAssetAddress(d, y)` on layer `h` keeps that layer's two asset maps a partial
bijection: its asset id is nonzero, and it neither rebinds an asset id already mapped to
another CTM nor moves a CTM already mapped to another asset id. An exact repeat passes. -/
def NoRebind (W : World) (s : Sys) (h : ChainId) (d : Word) (y : Address) : Prop :=
  W.enc h d ≠ 0 ∧
    (s.assetCtm h (W.enc h d) = 0 ∨ s.assetCtm h (W.enc h d) = y) ∧
    (s.ctmAsset h y = 0 ∨ s.ctmAsset h y = W.enc h d)

/-- The discipline, per call: registrations obey `NoRebind`; every other call is unrestricted. -/
def Disciplined (W : World) (s : Sys) : Op → Prop
  | .setCTMAssetAddress h d y => NoRebind W s h d y
  | _ => True

/-- A run: each call satisfies `ok` in the state it runs in, and succeeds. -/
inductive Run (W : World) (ok : Sys → Op → Prop) : Sys → List Op → Sys → Prop
  | nil (s : Sys) : Run W ok s [] s
  | cons {s s' s'' : Sys} {op : Op} {ops : List Op} :
      ok s op → Step W s op s' → Run W ok s' ops s'' → Run W ok s (op :: ops) s''

/-- No restriction on calls. -/
def AnyCall : Sys → Op → Prop := fun _ _ => True

/-- Reachable from fresh storage by a disciplined run. -/
def DReach (W : World) (s : Sys) : Prop :=
  ∃ ops, Run W (Disciplined W) Sys.init ops s

/-! ## Which CTM each migration check consults -/

/-- The asset id a `bridgeBurn` of chain `c` on layer `h` must carry:
`ctmAssetIdFromChainId(c) = ctmAssetIdFromAddress[chainTypeManager[c]]` (`BB:349-355`,
checked at `CAH:207-210`). -/
def burnAsset (s : Sys) (h c : ChainId) : AssetId := s.ctmAsset h (s.bhCtm h c)

/-- The CTM whose migration pause gates that burn: `_requireMigrationsNotPausedFor(_assetId)`
reads `ctmMigrationPaused[ctmAssetIdToAddress[_assetId]]` (`CAH:204`, `:468-473`). -/
def burnPauseCtm (s : Sys) (h c : ChainId) : Address := s.assetCtm h (burnAsset s h c)

/-- The CTM whose `forwardedBridgeBurn`, with its version check, the burn calls:
`chainTypeManager[c]` (`BB:420`, `CAH:217-229`, `CTM:735-738`). -/
def burnVersionCtm (s : Sys) (h c : ChainId) : Address := s.bhCtm h c

/-- The CTM whose migration pause gates a `bridgeMint` of `m` (`CAH:366`, `:468-473`), which
`forwardedBridgeMint` also writes as the chain's record (`BB:437`, `:446`). -/
def mintPauseCtm (s : Sys) (m : Msg) : Address := s.assetCtm m.dst m.asset

/-- The CTM whose protocol version that mint checks: the existing diamond's own
`s.chainTypeManager` (`MIG:223-229`), or, when the chain has no diamond on the layer, the
CTM whose `forwardedBridgeMint` deploys one (`CAH:399`, `CTM:754-756`). -/
def mintVersionCtm (s : Sys) (m : Msg) : Address :=
  (s.diamond m.dst m.chain).getD (s.assetCtm m.dst m.asset)

/-! ## The CTM a diamond admits, and the agreement -/

/-- The diamond's `onlyChainTypeManager` gate (`ZCB:85-90`) on layer `h`: a call from `X` into
chain `c`'s diamond passes it exactly when the layer's `zkChainMap` holds a diamond for `c`
whose `s.chainTypeManager` is `X`. The gate guards `executeUpgrade` (`ADM:593`),
`freezeDiamond` (`ADM:616`) and `unfreezeDiamond` (`ADM:629`), which a CTM reaches through
`CTM:626-628`, `:577-579` and `:584-586`, each finding the diamond through the Bridgehub's
`getZKChain` (`CTM:253-255`). -/
def diamondAdmits (s : Sys) (h c : ChainId) (X : Address) : Prop := s.diamond h c = some X

/-- On every layer, every chain the layer's `zkChainMap` holds has the Bridgehub's record
`chainTypeManager[c]` equal to its diamond's `s.chainTypeManager`. -/
def RecordAgrees (s : Sys) : Prop := ∀ h c D, s.diamond h c = some D → s.bhCtm h c = D

/-! ## The invariant -/

/-- On every layer, `ctmAssetIdToAddress[a] = y ≠ 0` exactly when
`ctmAssetIdFromAddress[y] = a ≠ 0`: the two asset maps are mutually inverse on their nonzero
entries. -/
def AssetBij (s : Sys) : Prop :=
  ∀ h a y, (s.assetCtm h a = y ∧ y ≠ 0) ↔ (s.ctmAsset h y = a ∧ a ≠ 0)

/-- What every disciplined run keeps.

* `bij`: `AssetBij`;
* `diaNz`, `agree`: every registered diamond's CTM is nonzero and is the Bridgehub's record;
* `home`: a chain's diamond on a settlement layer `h` belongs to the CTM registered on `h`
  under the asset id of the chain's L1 CTM;
* `sentOk`: every message carries `0` or the asset id of its chain's L1 CTM. -/
structure CtmInv (W : World) (s : Sys) : Prop where
  bij : AssetBij s
  diaNz : ∀ h c D, s.diamond h c = some D → D ≠ 0
  agree : ∀ h c D, s.diamond h c = some D → s.bhCtm h c = D
  home : ∀ h c D, h ≠ W.l1 → s.diamond h c = some D →
    ∃ X, s.diamond W.l1 c = some X ∧ s.ctmAsset W.l1 X ≠ 0 ∧
      s.ctmAsset h D = s.ctmAsset W.l1 X
  sentOk : ∀ m ∈ s.sent, ∃ X, s.diamond W.l1 m.chain = some X ∧
    (m.asset = 0 ∨ m.asset = s.ctmAsset W.l1 X)

/-! ## A repaired mint

A `bridgeMint` that also refused an existing diamond whose `getChainTypeManager()` differs
from the CTM `forwardedBridgeMint` returns (one comparison after `CAH:391-397`). This is not in
the source; it is stated to separate what the discipline buys from what a local check would. -/

/-- The repaired mint's extra check. Every other call is unrestricted. -/
def RepairGuard (s : Sys) : Op → Prop
  | .bridgeMint m => ∀ D, s.diamond m.dst m.chain = some D → D = s.assetCtm m.dst m.asset
  | _ => True

/-! ## The discipline at the tracker's level -/

/-- The registrations of a list of calls, as `(layer, additionalData, CTM)`. -/
def regsOf : List Op → List (ChainId × Word × Address)
  | [] => []
  | .setCTMAssetAddress h d y :: ops => (h, d, y) :: regsOf ops
  | _ :: ops => regsOf ops

/-- The registrations of a run, compared pairwise on each layer: `additionalData` and CTM
determine each other (on L1 the tracker passes `d = bytes32(x)` with `y = x`, `TRK:79`, so
this holds there by its code), and the asset ids of the logged words are nonzero and do not
collide. The hash conditions are on the run's own registration words only. -/
def PairDiscipline (W : World) (ops : List Op) : Prop :=
  ∀ h d y d' y', (h, d, y) ∈ regsOf ops → (h, d', y') ∈ regsOf ops →
    (d = d' ↔ y = y') ∧ (W.enc h d = W.enc h d' → d = d') ∧ W.enc h d ≠ 0

/-! ## Witness data

Layer `1` is L1 and layer `2` a settlement layer, which is also chain `2` on L1. L1 CTMs `10`
and `11`; settlement-layer CTMs `20` and `21`; the migrating chain is `3`. In
`CtmRecordDriftAdmitsForeignLayer` chain `4`, created on L1 under `11`, burns towards chain `3`
as its settlement layer. -/

/-- One asset-id function on both layers, as in the source. -/
def wWorld (e : Word → AssetId) : World := ⟨1, fun _ d => e d⟩

/-- Chains `2` and `3` under CTM `10` on L1; L1 registers `10` and `11`; the settlement layer
registers `10 ↦ 20`. -/
def wSetup : List Op :=
  [.createNewChain 2 10, .createNewChain 3 10, .setCTMAssetAddress 1 10 10,
    .setCTMAssetAddress 1 11 11, .setCTMAssetAddress 2 10 20]

/-- The disciplined continuation's registrations: `11 ↦ 21` on the settlement layer, then an
exact repeat of `10 ↦ 20`. -/
def wRegs : List Op := [.setCTMAssetAddress 2 11 21, .setCTMAssetAddress 2 10 20]

/-- Chain `3` goes to the settlement layer and burns back towards L1. -/
def wOut (e : Word → AssetId) : List Op :=
  [.bridgeBurn 1 3 2, .bridgeMint ⟨3, e 10, 1, 2⟩, .bridgeBurn 2 3 1]

/-- The message that brings chain `3` back to L1 in the disciplined run. -/
def wReturnMsg (e : Word → AssetId) : Msg := ⟨3, e 10, 2, 1⟩

/-- The undisciplined registration: `11 ↦ 20` on the settlement layer, a second asset id for
CTM `20`. -/
def cmRebind : Op := .setCTMAssetAddress 2 11 20

/-- The message that brings chain `3` back to L1 after `cmRebind`. -/
def cmReturnMsg (e : Word → AssetId) : Msg := ⟨3, e 11, 2, 1⟩

/-- Chain `3` reaches the settlement layer under CTM `20`. -/
def staleSetup (e : Word → AssetId) : List Op :=
  [.createNewChain 2 10, .createNewChain 3 10, .setCTMAssetAddress 1 10 10,
    .setCTMAssetAddress 2 10 20, .bridgeBurn 1 3 2, .bridgeMint ⟨3, e 10, 1, 2⟩]

/-- The undisciplined registration: the settlement layer re-points asset id `enc 10` at CTM
`21`, leaving `ctmAssetIdFromAddress[20]` in place. -/
def staleRebind : Op := .setCTMAssetAddress 2 10 21

end Protocol.CtmRecord
