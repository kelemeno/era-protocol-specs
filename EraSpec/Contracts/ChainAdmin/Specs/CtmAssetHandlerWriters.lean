import Mathlib.Tactic
import EraSpec.Contracts.AssetRouterBase.Specs.HandlerRegistration
import EraSpec.Contracts.ChainAdmin.Specs.PermanentRestrictionMigration

/-!
# Model: who writes the CTM asset's handler on L1

Source: branch `feat/upgrade-simplification` at commit `e561b9cc2`, as the topic
`PermanentRestrictionMigration`.  Paths are relative to `l1-contracts/contracts/`;
`CTMDT` is `core/ctm-deployment/CTMDeploymentTracker.sol`, `AR` is `bridge/asset-router/`,
`BH` is `core/bridgehub/`.  The pinned interop tree `c67894b9` has the same
`CTMDeploymentTracker` bodies at the same lines.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.ChainAdmin.Properties.CtmAssetHandlerWriters` and are proved in
`EraSpec.Contracts.ChainAdmin.Proofs.CtmAssetHandlerWriters`.

## Why this file exists

`PermanentRestriction` checks a migration only if
`L1AssetRouter.assetHandlerAddress(chainAssetId)` is the Bridgehub
(`governance/PermanentRestriction.sol:355-358`).  A CTM's asset id is
`encodeAssetId(L1, CTMDT, bytes32(ctm))` (`BH/BridgehubBase.sol:270, 289`;
`CTMDT:150-152`).  This file models every writer of that slot, and of the Bridgehub fields
the writers read, so that the deployed value can be derived instead of assumed.

## The two `CTMDeploymentTracker` writers

    // CTMDT:71-80, owner only
    function registerCTMAssetOnL1(address _ctmAddress) external onlyOwner {
        if (!BRIDGE_HUB.chainTypeManagerIsRegistered(_ctmAddress)) revert CTMNotRegistered();
        AssetRouterBase(address(L1_ASSET_ROUTER)).setAssetHandlerAddressThisChain(
            bytes32(uint256(uint160(_ctmAddress))), BRIDGE_HUB.chainAssetHandler());
        BRIDGE_HUB.setCTMAssetAddress(bytes32(uint256(uint160(_ctmAddress))), _ctmAddress);
    }
    // CTMDT:86-91, owner only
    function setCtmAssetHandlerAddressOnL1(address _ctmAddress) external onlyOwner {
        AssetRouterBase(address(L1_ASSET_ROUTER)).setAssetHandlerAddressThisChain(
            bytes32(uint256(uint160(_ctmAddress))), BRIDGE_HUB.chainAssetHandler());
    }

Both pass `BRIDGE_HUB.chainAssetHandler()`, the value the Bridgehub holds at that moment.
The router side is `_setAssetHandlerAddressThisChain` (`AR/AssetRouterBase.sol:65-77`), the
same body as at the pin, so it reuses `Contracts.AssetRouter.setHandler` and `SetGuard`
(`EraSpec/Contracts/AssetRouterBase/Specs/HandlerRegistration.lean`).  The CTMDT is not
the vault, so the id is hashed from the CTMDT itself, and the guard needs the CTMDT to be
the id's recorded tracker: the owner's `setAssetDeploymentTracker(bytes32(ctm), CTMDT)`
(`AR/L1AssetRouter.sol:134-141`) comes first.  The Bridgehub side is `setCTMAssetAddress`
(`BH/BridgehubBase.sol:268-293`): on L1 the sender must be `l1CtmDeployer` and the CTM
registered, and it writes `ctmAssetIdToAddress[encodeAssetId(L1, d, sender)]`.

## Every other writer of the L1 router's handler slot

A grep of `_setAssetHandler(` over the tree finds, on L1:

| `Op` | Source | Writes |
|---|---|---|
| `register` | `AR/L1AssetRouter.sol:144-149` → `AR/AssetRouterBase.sol:65-77`, any caller other than the CTMDT (the vault's `_unsafeRegisterNativeToken` among them, `bridge/ntv/NativeTokenVaultBase.sol:492-498`) | handler and tracker at the id hashed from the (normalised) caller |
| `finalize` | `_finalizeDeposit`'s fallback, `AR/AssetRouterBase.sol:273-282` | handler := vault, only where it is unset |
| `setNativeTokenVault` | `AR/L1AssetRouter.sol:115-120` (write :119) | handler := vault at `ETH_TOKEN_ASSET_ID = encodeNTVAssetId(L1, ETH_TOKEN_ADDRESS)` (:100) |

`setAssetDeploymentTracker` writes only the tracker.  `_burn`'s registration of an unknown
token (`AR/AssetRouterBase.sol:312-321`) is a vault `register`.  The CTMDT's code calls the
router only at `CTMDT:75-78, 87-90`, so a registration with `msg.sender = CTMDT` is one of
its two writers.

The Bridgehub's `chainAssetHandler` has one writer on L1, `setAddresses`
(`BH/L1Bridgehub.sol:268-280`, owner or upgrader), which also writes `assetRouter` and
`l1CtmDeployer`.  `chainTypeManagerIsRegistered` is written by `addChainTypeManager` and
`removeChainTypeManager` (`BH/BridgehubBase.sol:227-252`).

## Modelling choices

* **A revert is the absence of a step.**  Owner and upgrader checks only reject, so the
  model lets anyone call those functions; that only adds runs.
* **One-shot initializers are repeatable** (`setNativeTokenVault`), and the vault's
  `bridgeMint` is not modelled behind the fallback.  Both only add runs.
* **The vault address is fixed.**  Before `setNativeTokenVault` the L1 router is this model
  with `ntv = 0`.  `HandlerOffBridgehub` does not mention the vault, so a run across that
  switch is two runs under the two configurations, joined at a state.
* **`bytes32(uint256(uint160(ctm)))` is `ctm`**: addresses and asset data are both
  256-bit words here.
* **Hash collisions are logged, not excluded.**  A call writes the handler at the hash of
  one triple (`Op.handlerTriple`).  The results allow, as their only escape, a logged call
  whose triple is not the CTM's own `(L1, CTMDT, ctm)` but hashes to the CTM's id: a
  collision between two named inputs (`CollidesWithCtm`).
* **Not modelled:** router or Bridgehub implementation upgrades (`OPS-CONFIG`),
  `ctmAssetIdFromAddress`, events, the L2 side, and the `chainAssetHandler`'s own code.
-/

namespace Contracts.ChainAdmin.CtmAssetHandlerWriters

open Contracts.AssetRouter (AssetIdOf Router upd senderOf writtenId SetGuard setHandler)

/-- Chain ids, addresses, asset ids and asset data as 256-bit words. -/
abbrev Chain := UInt256
abbrev Address := UInt256
abbrev AssetId := UInt256
abbrev AssetData := UInt256

/-! ## Configuration and state -/

/-- The fixed deployment. -/
structure Cfg where
  /-- `DataEncoding.encodeAssetId(chainId, assetData, sender)` =
  `keccak256(abi.encode(chainId, sender, assetData))` (`common/libraries/DataEncoding.sol:125-127`). -/
  enc : AssetIdOf
  /-- `block.chainid` on L1, also the L1 Bridgehub's `_getL1ChainId()`. -/
  l1 : Chain
  /-- The L1 Bridgehub: `CTMDeploymentTracker.BRIDGE_HUB` (`CTMDT:32, 57`). -/
  bridgehub : Address
  /-- The L1 asset router: `CTMDeploymentTracker.L1_ASSET_ROUTER` (`CTMDT:35, 58`). -/
  router : Address
  /-- The `CTMDeploymentTracker` itself, the `msg.sender` of its calls. -/
  ctmdt : Address
  /-- `L1AssetRouter.nativeTokenVault` (`AR/L1AssetRouter.sol:58, 118`). -/
  ntv : Address
  /-- `L2_NATIVE_TOKEN_VAULT_ADDR` (`common/l2-helpers/L2ContractAddresses.sol:89`), the
  sender every vault id is hashed from. -/
  ntvAddr : Address
  /-- `ETH_TOKEN_ADDRESS` (`common/Config.sol:196`) as asset data. -/
  ethToken : AssetData
  /-- The CTMDT is not the vault (deployment fact: different contracts). -/
  ctmdtNotNtv : ctmdt ≠ ntv
  /-- The CTMDT is not `L2_NATIVE_TOKEN_VAULT_ADDR`, a system address in the kernel range. -/
  ctmdtNotNtvAddr : ctmdt ≠ ntvAddr

/-- A CTM's asset id: `encodeAssetId(L1, bytes32(ctm), CTMDT)`, as the router
(`AR/AssetRouterBase.sol:72`) and the Bridgehub (`BH/BridgehubBase.sol:289`) compute it
for the CTMDT's calls. -/
def ctmAssetId (K : Cfg) (ctm : Address) : AssetId := K.enc K.l1 K.ctmdt ctm

/-- The L1 router's two mappings and the Bridgehub fields the writers read or write. -/
structure St where
  /-- `L1AssetRouter.assetHandlerAddress` and `assetDeploymentTracker`. -/
  router : Router
  /-- `Bridgehub.assetRouter` (`BH/BridgehubBase.sol:66`). -/
  assetRouter : Address
  /-- `Bridgehub.l1CtmDeployer` (`BH/BridgehubBase.sol:100`). -/
  ctmDeployer : Address
  /-- `Bridgehub.chainAssetHandler` (`BH/BridgehubBase.sol:124`). -/
  chainAssetHandler : Address
  /-- `Bridgehub.chainTypeManagerIsRegistered` (`BH/BridgehubBase.sol:69`). -/
  ctmRegistered : Address → Bool
  /-- `Bridgehub.ctmAssetIdToAddress` (`BH/BridgehubBase.sol:103`). -/
  ctmAssetIdToAddress : AssetId → Address

/-! ## Operations -/

/-- One call that writes the modelled state. -/
inductive Op where
  /-- `CTMDeploymentTracker.registerCTMAssetOnL1(ctm)` (`CTMDT:71-80`). -/
  | registerCTMAssetOnL1 (ctm : Address)
  /-- `CTMDeploymentTracker.setCtmAssetHandlerAddressOnL1(ctm)` (`CTMDT:86-91`). -/
  | setCtmAssetHandlerAddressOnL1 (ctm : Address)
  /-- `L1AssetRouter.setAssetHandlerAddressThisChain(d, h)` by `caller`, not the CTMDT. -/
  | register (caller : Address) (d : AssetData) (h : Address)
  /-- `finalizeDeposit` for asset `a`, taking the unset-handler fallback. -/
  | finalize (a : AssetId)
  /-- `L1AssetRouter.setNativeTokenVault`. -/
  | setNativeTokenVault
  /-- `L1AssetRouter.setAssetDeploymentTracker(d, t)`. -/
  | setAssetDeploymentTracker (d : AssetData) (t : Address)
  /-- `L1Bridgehub.setAddresses(assetRouter, l1CtmDeployer, _, chainAssetHandler, _)`. -/
  | setAddresses (assetRouter ctmDeployer chainAssetHandler : Address)
  /-- `Bridgehub.setCTMAssetAddress(d, ctm)` by `sender`, not the CTMDT. -/
  | setCTMAssetAddress (sender : Address) (d : AssetData) (ctm : Address)
  /-- `Bridgehub.addChainTypeManager(ctm)`. -/
  | addChainTypeManager (ctm : Address)
  /-- `Bridgehub.removeChainTypeManager(ctm)`. -/
  | removeChainTypeManager (ctm : Address)

/-- One successful call.  A revert is the absence of a step. -/
inductive Step (K : Cfg) : St → Op → St → Prop
  /-- `CTMDT:71-80`: the CTM is registered (:72-74); the router's guard for the CTMDT and
  `bytes32(ctm)` (`AR/AssetRouterBase.sol:70-73`); then `setCTMAssetAddress` by the CTMDT,
  which must be the Bridgehub's `l1CtmDeployer` (`BH/BridgehubBase.sol:280-287`).  The
  handler written is the Bridgehub's current `chainAssetHandler`. -/
  | registerCTMAssetOnL1 {s : St} {ctm : Address} :
      s.ctmRegistered ctm = true →
      SetGuard K.enc K.l1 K.ntv K.ntvAddr s.router K.ctmdt ctm →
      K.ctmdt = s.ctmDeployer →
      Step K s (.registerCTMAssetOnL1 ctm)
        { s with
          router := setHandler K.enc K.l1 K.ntv K.ntvAddr s.router K.ctmdt ctm s.chainAssetHandler
          ctmAssetIdToAddress := upd s.ctmAssetIdToAddress (K.enc K.l1 K.ctmdt ctm) ctm }
  /-- `CTMDT:86-91`: the router's guard only; the handler written is the Bridgehub's current
  `chainAssetHandler`. -/
  | setCtmAssetHandlerAddressOnL1 {s : St} {ctm : Address} :
      SetGuard K.enc K.l1 K.ntv K.ntvAddr s.router K.ctmdt ctm →
      Step K s (.setCtmAssetHandlerAddressOnL1 ctm)
        { s with
          router := setHandler K.enc K.l1 K.ntv K.ntvAddr s.router K.ctmdt ctm s.chainAssetHandler }
  /-- Any other caller of `setAssetHandlerAddressThisChain` (`AR/L1AssetRouter.sol:144-149`),
  with the guard of `AR/AssetRouterBase.sol:70-73`. -/
  | register {s : St} {caller : Address} {d : AssetData} {h : Address} :
      caller ≠ K.ctmdt →
      SetGuard K.enc K.l1 K.ntv K.ntvAddr s.router caller d →
      Step K s (.register caller d h)
        { s with router := setHandler K.enc K.l1 K.ntv K.ntvAddr s.router caller d h }
  /-- `_finalizeDeposit`'s fallback (`AR/AssetRouterBase.sol:273-282`): only where the handler
  is unset. -/
  | finalize {s : St} {a : AssetId} :
      s.router.handler a = 0 →
      Step K s (.finalize a)
        { s with router := { s.router with handler := upd s.router.handler a K.ntv } }
  /-- `setNativeTokenVault`'s route for ETH (`AR/L1AssetRouter.sol:119`). -/
  | setNativeTokenVault {s : St} :
      Step K s .setNativeTokenVault
        { s with router := { s.router with
            handler := upd s.router.handler (K.enc K.l1 K.ntvAddr K.ethToken) K.ntv } }
  /-- `setAssetDeploymentTracker(d, t)` (`AR/L1AssetRouter.sol:134-141`): the tracker of the
  id hashed from `t` becomes `t`. -/
  | setAssetDeploymentTracker {s : St} {d : AssetData} {t : Address} :
      Step K s (.setAssetDeploymentTracker d t)
        { s with router := { s.router with tracker := upd s.router.tracker (K.enc K.l1 t d) t } }
  /-- `L1Bridgehub.setAddresses` (`BH/L1Bridgehub.sol:268-280`). -/
  | setAddresses {s : St} {ar dt cah : Address} :
      Step K s (.setAddresses ar dt cah)
        { s with assetRouter := ar, ctmDeployer := dt, chainAssetHandler := cah }
  /-- `setCTMAssetAddress` by another `l1CtmDeployer` (`BH/BridgehubBase.sol:268-293`). -/
  | setCTMAssetAddress {s : St} {sender : Address} {d : AssetData} {ctm : Address} :
      sender ≠ K.ctmdt → sender = s.ctmDeployer → s.ctmRegistered ctm = true →
      Step K s (.setCTMAssetAddress sender d ctm)
        { s with ctmAssetIdToAddress := upd s.ctmAssetIdToAddress (K.enc K.l1 sender d) ctm }
  /-- `addChainTypeManager` (`BH/BridgehubBase.sol:227-237`). -/
  | addChainTypeManager {s : St} {ctm : Address} :
      ctm ≠ 0 → s.ctmRegistered ctm = false →
      Step K s (.addChainTypeManager ctm)
        { s with ctmRegistered := fun x => if x = ctm then true else s.ctmRegistered x }
  /-- `removeChainTypeManager` (`BH/BridgehubBase.sol:242-252`). -/
  | removeChainTypeManager {s : St} {ctm : Address} :
      ctm ≠ 0 → s.ctmRegistered ctm = true →
      Step K s (.removeChainTypeManager ctm)
        { s with ctmRegistered := fun x => if x = ctm then false else s.ctmRegistered x }

/-- A sequence of successful calls, first call first. -/
inductive Run (K : Cfg) : St → List Op → St → Prop
  | nil {s : St} : Run K s [] s
  | cons {s s' s'' : St} {op : Op} {ops : List Op} :
      Step K s op s' → Run K s' ops s'' → Run K s (op :: ops) s''

/-! ## Classifying calls -/

/-- The call is one of the two CTMDT writers for `ctm`. -/
def Op.WritesCtmHandler (ctm : Address) (op : Op) : Prop :=
  op = .registerCTMAssetOnL1 ctm ∨ op = .setCtmAssetHandlerAddressOnL1 ctm

/-- The (chain, sender, data) triple whose hash is the id a call's handler write targets.
The fallback is given its id, and the other calls write no handler. -/
def Op.handlerTriple (K : Cfg) : Op → Option (Chain × Address × AssetData)
  | .registerCTMAssetOnL1 ctm => some (K.l1, K.ctmdt, ctm)
  | .setCtmAssetHandlerAddressOnL1 ctm => some (K.l1, K.ctmdt, ctm)
  | .register caller d _ => some (K.l1, senderOf K.ntv K.ntvAddr caller, d)
  | .setNativeTokenVault => some (K.l1, K.ntvAddr, K.ethToken)
  | _ => none

/-- **A logged collision with the CTM's id.**  Some call in `ops` writes a handler at the
hash of a triple that is not the CTM's own `(L1, CTMDT, ctm)`, and that hash is the CTM's
id.  Both colliding inputs are named by the run. -/
def CollidesWithCtm (K : Cfg) (ctm : Address) (ops : List Op) : Prop :=
  ∃ op ∈ ops, ∃ t : Chain × Address × AssetData, op.handlerTriple K = some t ∧
    t ≠ (K.l1, K.ctmdt, ctm) ∧ K.enc t.1 t.2.1 t.2.2 = ctmAssetId K ctm

/-- The Bridgehub's `chainAssetHandler` is a deployed contract other than the Bridgehub
(`OPS-CONFIG`). -/
def ChainAssetHandlerOk (K : Cfg) (s : St) : Prop :=
  s.chainAssetHandler ≠ 0 ∧ s.chainAssetHandler ≠ K.bridgehub

/-- The call keeps `ChainAssetHandlerOk`: if it is `setAddresses`, its new
`chainAssetHandler` is nonzero and not the Bridgehub. -/
def Op.KeepsChainAssetHandlerOk (K : Cfg) : Op → Prop
  | .setAddresses _ _ cah => cah ≠ 0 ∧ cah ≠ K.bridgehub
  | _ => True

/-- The call is `setAddresses`. -/
def Op.IsSetAddresses : Op → Prop
  | .setAddresses _ _ _ => True
  | _ => False

/-- The CTM's handler is set and is not the Bridgehub. -/
def HandlerOffBridgehub (K : Cfg) (ctm : Address) (s : St) : Prop :=
  s.router.handler (ctmAssetId K ctm) ≠ 0 ∧ s.router.handler (ctmAssetId K ctm) ≠ K.bridgehub

/-- What `PermanentRestriction` reads agrees with the state: the Bridgehub is the
deployment's, the Bridgehub's asset router is the modelled router, and the asset-handler,
CTM-asset and chain-asset-handler reads are the state's. -/
def EnvReads (K : Cfg) (s : St) (E : PermanentRestrictionMigration.Env) : Prop :=
  E.bridgehub = K.bridgehub ∧ s.assetRouter = K.router ∧ E.assetRouter = s.assetRouter ∧
    E.assetHandlerAddress = s.router.handler ∧ E.ctmAssetIdToAddress = s.ctmAssetIdToAddress ∧
    E.chainAssetHandler = s.chainAssetHandler

/-! ## Witness data

L1 `1`, Bridgehub `10`, router `12`, chain asset handler `13`, vault `14`,
`L2_NATIVE_TOKEN_VAULT_ADDR = 0x10004`, CTMDT `50`, CTM `30`.  The encoding
`c·10⁶ + s·10³ + d` is injective on the small values used. -/

/-- The witness deployment. -/
def cawCfg : Cfg where
  enc := fun c s d => c * 1000000 + s * 1000 + d
  l1 := 1
  bridgehub := 10
  router := 12
  ctmdt := 50
  ntv := 14
  ntvAddr := 0x10004
  ethToken := 1
  ctmdtNotNtv := by decide
  ctmdtNotNtvAddr := by decide

/-- Before the registration: an empty router, the CTM `30` registered with the Bridgehub,
the CTMDT as `l1CtmDeployer`, and the chain asset handler `13`. -/
def cawS0 : St where
  router := Contracts.AssetRouter.empty
  assetRouter := 12
  ctmDeployer := 50
  chainAssetHandler := 13
  ctmRegistered := fun x => decide (x = 30)
  ctmAssetIdToAddress := fun _ => 0

/-- The deployment sequence: the router owner records the CTMDT as the CTM id's tracker,
then the CTMDT registers the CTM. -/
def cawOps : List Op := [.setAssetDeploymentTracker 30 50, .registerCTMAssetOnL1 30]

/-- The state after the tracker write. -/
def cawS0' : St :=
  { cawS0 with router := { cawS0.router with
      tracker := upd cawS0.router.tracker (cawCfg.enc cawCfg.l1 50 30) 50 } }

/-- The state after `cawOps`. -/
def cawS1 : St :=
  { cawS0' with
    router := setHandler cawCfg.enc cawCfg.l1 cawCfg.ntv cawCfg.ntvAddr cawS0'.router cawCfg.ctmdt 30
      cawS0'.chainAssetHandler
    ctmAssetIdToAddress := upd cawS0'.ctmAssetIdToAddress (cawCfg.enc cawCfg.l1 cawCfg.ctmdt 30) 30 }

/-- The witness decoders: as `prmAbi`, but the second-bridge data names this deployment's
CTM id. -/
def cawAbi : PermanentRestrictionMigration.Abi :=
  { PermanentRestrictionMigration.prmAbi with
    decodeAssetData := fun b => if b = [2] then some (ctmAssetId cawCfg 30, [3]) else none }

/-- What `PermanentRestriction` reads after `cawOps`: `prmEnv`'s tables and code facts, with
the router and Bridgehub reads of `cawS1`. -/
def cawEnv : PermanentRestrictionMigration.Env :=
  { PermanentRestrictionMigration.prmEnv with
    assetHandlerAddress := cawS1.router.handler
    ctmAssetIdToAddress := cawS1.ctmAssetIdToAddress
    chainAssetHandler := cawS1.chainAssetHandler }

/-- A deployment that sets the Bridgehub as its own chain asset handler and then re-points
the CTM: the configuration in which `PermanentRestriction`'s check fires. -/
def cawOpsBridgehubAsHandler : List Op :=
  cawOps ++ [.setAddresses 12 50 10, .setCtmAssetHandlerAddressOnL1 30]

/-- The state after `setAddresses(12, 50, 10)` from `cawS1`. -/
def cawS2 : St := { cawS1 with assetRouter := 12, ctmDeployer := 50, chainAssetHandler := 10 }

/-- The state after `cawOpsBridgehubAsHandler`: the CTM re-pointed at the Bridgehub. -/
def cawS3 : St :=
  { cawS2 with
    router := setHandler cawCfg.enc cawCfg.l1 cawCfg.ntv cawCfg.ntvAddr cawS2.router cawCfg.ctmdt 30
      cawS2.chainAssetHandler }

/-- What `PermanentRestriction` reads after `cawOpsBridgehubAsHandler`. -/
def cawEnvBridgehubAsHandler : PermanentRestrictionMigration.Env :=
  { cawEnv with
    assetHandlerAddress := cawS3.router.handler
    chainAssetHandler := cawS3.chainAssetHandler }

/-- From `cawS3` (the Bridgehub as handler), an upgrade installs the chain asset handler
`13` (`setAddresses`) and the CTMDT re-points the CTM to it
(`setCtmAssetHandlerAddressOnL1`), as an ecosystem upgrade does (`CTMDT:82-85`). -/
def cawOpsRepoint : List Op := [.setAddresses 12 50 13, .setCtmAssetHandlerAddressOnL1 30]

/-- The state after `setAddresses(12, 50, 13)` from `cawS3`. -/
def cawS4 : St := { cawS3 with assetRouter := 12, ctmDeployer := 50, chainAssetHandler := 13 }

/-- The state after `cawOpsRepoint`. -/
def cawS5 : St :=
  { cawS4 with
    router := setHandler cawCfg.enc cawCfg.l1 cawCfg.ntv cawCfg.ntvAddr cawS4.router cawCfg.ctmdt 30
      cawS4.chainAssetHandler }

/-- What `PermanentRestriction` reads after `cawOpsRepoint`. -/
def cawEnvRepointed : PermanentRestrictionMigration.Env :=
  { cawEnv with
    assetHandlerAddress := cawS5.router.handler
    chainAssetHandler := cawS5.chainAssetHandler }

/-- A collision configuration: the encoding ignores the sender, so the vault's registration
of `bytes32(30)` hashes to the CTM's id. -/
def cawCollidingCfg : Cfg := { cawCfg with enc := fun _ _ d => d }

end Contracts.ChainAdmin.CtmAssetHandlerWriters
