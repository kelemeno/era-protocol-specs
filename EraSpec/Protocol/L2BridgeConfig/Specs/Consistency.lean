import Mathlib.Tactic
import EraSpec.Contracts.AssetRouterBase.Specs.HandlerRegistration

/-!
# Model: the L2 bridge configuration words across genesis and default upgrades

Source: era-contracts `draft/v0.35.0` head `b17415d20`, under `l1-contracts/contracts/`.
Abbreviations: `AR/` is `bridge/asset-router/`, `NTV/` is `bridge/ntv/`, `UP/` is
`l2-upgrades/`, and `Helper` is `UP/L2GenesisForceDeploymentsHelper.sol`.

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.L2BridgeConfig.Properties.Consistency`, proofs in
`EraSpec.Protocol.L2BridgeConfig.Proofs.Consistency`.

## The configuration words

Nine L2 built-ins each keep their own copy of the L1 chain id, and four keep their own
copy of the chain's base-token asset id.  Each contract makes decisions from its own copy.

| Contract | Words in the model | Writers at `b17415d20` |
|---|---|---|
| `L2MessageRoot` | `l1ChainId` | `updateL2`, `core/message-root/L2MessageRoot.sol:73-75`, also run by `initL2` (`:67-71`) |
| `L2Bridgehub` | `L1_CHAIN_ID`, `ETH_TOKEN_ASSET_ID` | `updateL2`, `core/bridgehub/L2Bridgehub.sol:77-92`, also run by `initL2` (`:60-68`) |
| `L2AssetRouter` | `L1_CHAIN_ID`, `L1_ASSET_ROUTER`, `BASE_TOKEN_ASSET_ID`, `assetHandlerAddress`, `assetDeploymentTracker` | `updateL2`, `AR/L2AssetRouter.sol:173-188`; `initL2` (`:154-163`) also points the base id at the vault (`:162`); the handler writers below |
| `L2NativeTokenVault` | `WETH_TOKEN`, `BASE_TOKEN_ASSET_ID`, `L1_CHAIN_ID`, `BASE_TOKEN_ORIGIN_TOKEN`, `bridgedTokenBeacon`, `tokenAddress`, `assetId`, `originChainId` | `updateL2`, `NTV/L2NativeTokenVault.sol:134-174`, also run by `initL2` (`:99-115`); `_setNewTokenStorage`, `NTV/NativeTokenVaultBase.sol:565-575` |
| `L2ChainAssetHandler` | `L1_CHAIN_ID`, `ETH_TOKEN_ASSET_ID` | `updateL2`, `core/chain-asset-handler/L2ChainAssetHandler.sol:100-109`, also run by `initL2` (`:89-92`) |
| `L2AssetTracker` | `L1_CHAIN_ID`, `BASE_TOKEN_ASSET_ID` | `initL2` only, `bridge/asset-tracker/L2AssetTracker.sol:96-99` |
| `InteropCenter` | `L1_CHAIN_ID` | `initL2` only, `interop/InteropCenter.sol:170-187` |
| `L2BaseToken` (ZKsync OS) | `L1_CHAIN_ID` | `initL2` only, `l2-system/zksync-os/L2BaseToken.sol:64-77` |
| `AtomicFlowManager` | `L1_CHAIN_ID` | `initL2` only, `atomic-interop/AtomicFlowManager.sol:76-85` |
| WETH (`L2WrappedBaseToken` proxy) | `baseTokenAssetId`, `l1Address` | `initializeV3`, `bridge/L2WrappedBaseToken.sol:55-78`, from the proxy's constructor in `_ensureWethToken` (`Helper:409-439`) |

A grep for assignments to `L1_CHAIN_ID`, `l1ChainId`, `BASE_TOKEN_ASSET_ID`,
`ETH_TOKEN_ASSET_ID`, `WETH_TOKEN`, `BASE_TOKEN_ORIGIN_TOKEN`, `baseTokenAssetId` and
`L1_ASSET_ROUTER` over `bridge/`, `core/`, `interop/`, `atomic-interop/`, `l2-system/`,
`l2-upgrades/` and `common/` finds exactly the L2 writers above (the other hits are L1
contracts).  The writers of the vault registry are `updateL2` and `_setNewTokenStorage`;
the latter is reached from `_unsafeRegisterNativeToken` (`NativeTokenVaultBase.sol:492-499`)
and from `_ensureAndSaveTokenDeployedInner` (`:550-563`).  The writers of the router's
`assetHandlerAddress` are `initL2` (`AR/L2AssetRouter.sol:162`), the counterpart's
`setAssetHandlerAddress` (`:198-204`), `_setAssetHandlerAddressThisChain`
(`AR/AssetRouterBase.sol:65-77`) and `_finalizeDeposit`'s unset-handler branch (`:273-278`).

## The two upgrade transactions

Both are delegatecalls of `L2ComplexUpgrader` (`UP/L2ComplexUpgrader.sol:35-69`,
`onlyForceDeployer`), so every call they make has `msg.sender = L2_COMPLEX_UPGRADER_ADDR`,
which is what every `onlyUpgrader` compares.  Both run
`performForceDeployedContractsInit` (`Helper:187-235`), atomically:

    genesisUpgrade (UP/L2GenesisUpgrade.sol:22-40)    defaultUpgrade (UP/L2DefaultUpgrade.sol:16-27)
      chainId != 0                                        -
      require governance != 0               (Helper:206)
      weth := _ensureWethToken(NTV.WETH_TOKEN(), …)      (Helper:210-217, 409-439)
      MessageRoot.initL2(l1)                (:253)        MessageRoot.updateL2(l1)          (:300)
      Bridgehub.initL2(l1, …)               (:255-259)    Bridgehub.updateL2(l1, …)         (:302-306)
      AssetRouter.initL2(l1, r, a, …)       (:262-267)    AssetRouter.updateL2(l1, r, a, …) (:309-314)
      NTV.initL2(l1, …, beacon, weth, bd, …)(:279-286)    NTV.updateL2(l1, …, weth, bd, …)  (:317-323)
      ChainAssetHandler.initL2(l1, …)       (:288-291)    ChainAssetHandler.updateL2(l1, …) (:325-328)
      Bridgehub.setAddresses(…)             (:337-343)    InteropHandler.updateL2()         (:330)
      AssetTracker.initL2(l1, a)            (:356-359)    Bridgehub.setAddresses(…)         (:337-343)
      InteropHandler.initL2()               (:361)
      InteropCenter.initL2(l1, …, zk)       (:363-367)
      NTV.registerBaseTokenIfNeeded()       (:369)
      L2BaseToken.initL2(l1)                (:371)
      InteropCommitmentTree.initL2()        (:373)
      AtomicFlowManager.initL2(l1)          (:374)

with `l1 = fixed.l1ChainId`, `r = fixed.l1AssetRouter`, `bd = additional.baseTokenBridgingData`
and `a = bd.assetId`.  The default upgrade does not touch the tracker, the interop center,
the base token or the flow manager: their words are written at genesis only.  Of the
`updateL2`s only the vault's checks anything against stored state: once its `WETH_TOKEN`
(`:145`), `L1_CHAIN_ID` (`:148`) or `BASE_TOKEN_ASSET_ID` (`:152-155`) is nonzero, it refuses a
different value.  It rewrites `BASE_TOKEN_ORIGIN_TOKEN` (`:160`) and `originChainId[a]`
(`:167`) with no check.

## One-shot guards

`reentrancyGuardInitializer` (`common/ReentrancyGuard.sol:43-63`) reverts unless the lock
slot is zero, and sets it to one; `nonReentrant` (`:72-98`) leaves it nonzero, so it never
returns to zero.  It guards `initL2` of the message root, bridgehub, router, vault, chain
asset handler, tracker and interop center (`locked` below).  `L2BaseToken.initL2` has its own
flag (`:65-68`), and `AtomicFlowManager.initL2` refuses unless its `L1_CHAIN_ID` is zero and
the new one is nonzero (`:77-83`).  WETH's `initializeV3` is `reinitializer(3)`: it runs in
the proxy's constructor, and afterwards OpenZeppelin's version check rejects it.

## Model boundary (`MODEL-L2-CONFIG`)

* **Delegate targets.**  The complex upgrader delegatecalls `L2GenesisUpgrade` or
  `L2DefaultUpgrade` (`UpgradeProgram`).  Other delegate targets are not modelled.  An
  `onlyUpgrader` function sees `msg.sender = L2_COMPLEX_UPGRADER_ADDR` only when code running
  at that address calls it: the helper, or another delegate target.  So in this model a
  *direct* `initL2`/`updateL2` call (`DirectCall`) by `L2_COMPLEX_UPGRADER_ADDR` stands for
  another delegate target; the run results exclude it (`ConfigCall.Admissible`), and
  `RouterUpdateOutsideHelperDivergesBase` shows why.
* **Code.**  The built-ins run the `b17415d20` implementations.  The force-deployment rows of
  `forceDeployAndUpgradeUniversal` (`UP/L2ComplexUpgrader.sol:41-47`), which deploy code and
  upgrade proxies, are not modelled, and neither is the `_delegateTo.code.length` check.
  Upgrading WETH's proxy (its admin is the aliased governance) is not modelled.
* **Abstract parts.**  ABI decoding, keccak (`ConfigEnv.enc`), CREATE2 addresses
  (`ConfigEnv.wethProxy`; a deployed bridged token's address is an argument of `vaultDeploy`),
  the beacon deployer's result and the address alias are functions of the environment.
  Nothing is assumed about them.
* **Over-approximated success.**  Steps that write none of the modelled words are omitted,
  and treated as succeeding: `_setupProxyAdmin`, `Bridgehub.setAddresses` and
  `_initializeInner`, `L2MessageRoot._initialize`, `InteropHandler.initL2/updateL2`,
  `registerBaseTokenIfNeeded`, the tree's `initL2`, `L2BaseToken`'s mint hook and value
  transfer, and the owner resets.  The owner resets cannot revert here: the helper checks
  `governance != 0` first (`Helper:206`), and only the vault's and the center's resets have a
  zero check.  `_disableInitializers` is not modelled.  Omitting a check only adds runs, so
  every statement "if the call succeeds then …" covers the source.  The countermodels use
  calls whose omitted parts check nothing the instance violates (see their statements).
* **Other writers, abstracted.**  `vaultRegister` is `_registerToken`
  (`NativeTokenVaultBase.sol:131-140`; reached from `registerToken`, `ensureTokenIsRegistered`
  and `tryRegisterTokenFromBurnData`) with its router callback; its `code.length` check
  (`:137`) is dropped, which only adds runs.  `vaultDeploy` is `_ensureAndSaveTokenDeployed`
  (`:515-563`) reached from `bridgeMint` or `bridgeRecoverFailedTransfer` on an asset with no
  token; the caller checks, the beacon-proxy code and the token's metadata are dropped, the
  origin chain is an argument, and the deployed address is any nonzero address other than
  `L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR`, where code already exists (`VM-DEPLOY`).
  `finalizeFallback` is `_finalizeDeposit`'s unset-handler branch behind
  `L2AssetRouter.finalizeDeposit`'s base-id check (`AR/L2AssetRouter.sol:258`), for any
  caller.  `routerRegister` is `setAssetHandlerAddressThisChain` called by an account other
  than the vault; the vault's own call is part of `vaultRegister`.
* **Not modelled:** events, `msg.value`, pause, the vault's metadata words
  (`BASE_TOKEN_NAME/SYMBOL/DECIMALS`), owners, the bridgehub's `MAX_NUMBER_OF_ZK_CHAINS`, and
  storage outside the table above.  A revert is `none`.  Transactions are atomic.
-/

namespace Contracts.L2BridgeConfig

open Contracts.AssetRouter (Chain AssetId Address AssetData AssetIdOf upd setHandler writtenId
  senderOf)

/-! ## Upgrade input -/

/-- `TokenBridgingData` of the base token (`common/Messaging.sol:376-381`), as the helper passes
it. -/
structure BaseTokenData where
  /-- `assetId`. -/
  assetId : AssetId
  /-- `originChainId`. -/
  originChainId : Chain
  /-- `originToken`. -/
  originToken : Address

/-- The fields of `FixedForceDeploymentsData` (`state-transition/l2-deps/IL2GenesisUpgrade.sol:20-43`)
and `ZKChainSpecificForceDeploymentsData` (`:6-16`) that reach a modelled word or check.  At
`b17415d20` L1 builds the chain-specific half from its own state
(`upgrades/ZKChainSpecificForceDeploymentsLib.sol:28-56`): the asset id from the Bridgehub,
the origin chain and origin token from the L1 vault. -/
structure UpgradeInput where
  /-- `fixed.l1ChainId`. -/
  l1ChainId : Chain
  /-- `fixed.l1AssetRouter`. -/
  l1AssetRouter : Address
  /-- `fixed.aliasedL1Governance`. -/
  governance : Address
  /-- `fixed.zkTokenAssetId`. -/
  zkTokenAssetId : AssetId
  /-- `fixed.dangerousTestOnlyForcedBeacon`. -/
  forcedBeacon : Address
  /-- `additional.baseTokenL1Address`. -/
  baseTokenL1Address : Address
  /-- `additional.baseTokenBridgingData`. -/
  base : BaseTokenData

/-! ## Environment -/

/-- Constants and abstract functions. -/
structure ConfigEnv where
  /-- `block.chainid` of this L2. -/
  thisChain : Chain
  /-- `L2_FORCE_DEPLOYER_ADDR` (`common/l2-helpers/L2ContractAddresses.sol:53`), checked by
  `onlyForceDeployer` (`UP/L2ComplexUpgrader.sol:22-27`). -/
  forceDeployer : Address
  /-- `L2_COMPLEX_UPGRADER_ADDR` (`L2ContractAddresses.sol:65`), the `msg.sender` every
  `onlyUpgrader` / `onlyComplexUpgrader` compares. -/
  upgrader : Address
  /-- `L2_NATIVE_TOKEN_VAULT_ADDR` (`L2ContractAddresses.sol:89`). -/
  ntvAddr : Address
  /-- `L2_ASSET_ROUTER_ADDR` (`L2ContractAddresses.sol:84`), the `l2Bridge` the helper hands
  to WETH's `initializeV3` (`Helper:394`). -/
  routerAddr : Address
  /-- `L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR` (`L2ContractAddresses.sol:59`). -/
  baseTokenAddr : Address
  /-- `ETH_TOKEN_ADDRESS = address(1)` (`common/Config.sol:203`). -/
  ethToken : Address
  /-- `DataEncoding.encodeAssetId(chainId, data, sender)` with arguments (chain, sender, data):
  `keccak256(abi.encode(chainId, sender, data))` (`common/libraries/DataEncoding.sol:125-136`). -/
  enc : AssetIdOf
  /-- The address of the WETH proxy `_ensureWethToken` creates (`Helper:431-436`, CREATE2 with
  salt zero; the init code includes the input's data). -/
  wethProxy : UpgradeInput → Address
  /-- What `UpgradeableBeaconDeployer.deployUpgradeableBeacon` returns (`Helper:271-273`). -/
  deployedBeacon : Address
  /-- `AddressAliasHelper.undoL1ToL2Alias`. -/
  undoAlias : Address → Address

/-- `DataEncoding.encodeNTVAssetId(chainId, token)` (`DataEncoding.sol:150-152`): the asset id
hashed with `L2_NATIVE_TOKEN_VAULT_ADDR` as sender. -/
def ConfigEnv.encNTV (E : ConfigEnv) (c : Chain) (t : Address) : AssetId := E.enc c E.ntvAddr t

/-- The beacon `_initContractsBeforeWiring` hands to the vault (`Helper:269-276`). -/
def ConfigEnv.beaconOf (E : ConfigEnv) (u : UpgradeInput) : Address :=
  if u.forcedBeacon = 0 then E.deployedBeacon else u.forcedBeacon

/-! ## State -/

/-- `L2MessageRoot`. -/
structure MessageRootCfg where
  /-- `l1ChainId` (read by `L1_CHAIN_ID()`, `L2MessageRoot.sol:51-53`). -/
  l1 : Chain
  /-- The reentrancy lock slot is nonzero. -/
  locked : Bool

/-- `L2Bridgehub`. -/
structure BridgehubCfg where
  /-- `L1_CHAIN_ID`. -/
  l1 : Chain
  /-- `ETH_TOKEN_ASSET_ID`. -/
  eth : AssetId
  /-- The reentrancy lock slot is nonzero. -/
  locked : Bool

/-- `L2AssetRouter`. -/
structure RouterCfg where
  /-- `L1_CHAIN_ID`. -/
  l1 : Chain
  /-- `L1_ASSET_ROUTER`, the counterpart `onlyAssetRouterCounterpart` compares
  (`AR/L2AssetRouter.sol:96-107`). -/
  l1AssetRouter : Address
  /-- `BASE_TOKEN_ASSET_ID`, the id `finalizeDeposit` rejects (`:258`). -/
  base : AssetId
  /-- `assetHandlerAddress` and `assetDeploymentTracker`. -/
  routes : Contracts.AssetRouter.Router
  /-- The reentrancy lock slot is nonzero. -/
  locked : Bool

/-- `L2NativeTokenVault`. -/
structure VaultCfg where
  /-- `WETH_TOKEN`. -/
  weth : Address
  /-- `BASE_TOKEN_ASSET_ID`, read by the base-token branch of `_getTokenAndBridgeToChain`
  (`NativeTokenVaultBase.sol:435`) and by `InteropCenter._ensureCorrectTotalValue`
  (`interop/InteropCenter.sol:426`). -/
  base : AssetId
  /-- `L1_CHAIN_ID`. -/
  l1 : Chain
  /-- `BASE_TOKEN_ORIGIN_TOKEN`. -/
  baseOriginToken : Address
  /-- `bridgedTokenBeacon`. -/
  beacon : Address
  /-- `tokenAddress[assetId]`. -/
  tokenAddress : AssetId → Address
  /-- `assetId[token]`. -/
  assetIdOf : Address → AssetId
  /-- `originChainId[assetId]`. -/
  originChainId : AssetId → Chain
  /-- The reentrancy lock slot is nonzero. -/
  locked : Bool

/-- `L2ChainAssetHandler`. -/
structure ChainAssetHandlerCfg where
  /-- `L1_CHAIN_ID`. -/
  l1 : Chain
  /-- `ETH_TOKEN_ASSET_ID`. -/
  eth : AssetId
  /-- The reentrancy lock slot is nonzero. -/
  locked : Bool

/-- `L2AssetTracker`. -/
structure TrackerCfg where
  /-- `L1_CHAIN_ID`. -/
  l1 : Chain
  /-- `BASE_TOKEN_ASSET_ID`, under which the tracker books base-token flows
  (`L2AssetTracker.sol:169-173, 176-190, 277-298`). -/
  base : AssetId
  /-- The reentrancy lock slot is nonzero. -/
  locked : Bool

/-- `InteropCenter`. -/
structure CenterCfg where
  /-- `L1_CHAIN_ID`. -/
  l1 : Chain
  /-- The reentrancy lock slot is nonzero. -/
  locked : Bool

/-- `L2BaseToken` (ZKsync OS). -/
structure BaseTokenCfg where
  /-- `L1_CHAIN_ID`. -/
  l1 : Chain
  /-- `baseTokenHolderBalanceInitialized`. -/
  initialized : Bool

/-- `AtomicFlowManager`.  Its `L1_CHAIN_ID` is also its initialization sentinel. -/
structure FlowManagerCfg where
  /-- `L1_CHAIN_ID`. -/
  l1 : Chain

/-- The WETH proxy the helper deploys. -/
structure WethCfg where
  /-- `baseTokenAssetId`. -/
  base : AssetId
  /-- `l1Address`. -/
  l1Address : Address
  /-- `initializeV3` has run (OpenZeppelin `_initialized = 3`). -/
  initialized : Bool

/-- Every modelled word of the ten contracts. -/
structure ConfigWorld where
  messageRoot : MessageRootCfg
  bridgehub : BridgehubCfg
  router : RouterCfg
  vault : VaultCfg
  chainAssetHandler : ChainAssetHandlerCfg
  tracker : TrackerCfg
  center : CenterCfg
  baseToken : BaseTokenCfg
  flowManager : FlowManagerCfg
  weth : WethCfg

/-- All-zero storage: the state before the genesis upgrade. -/
def ConfigWorld.fresh : ConfigWorld where
  messageRoot := ⟨0, false⟩
  bridgehub := ⟨0, 0, false⟩
  router := ⟨0, 0, 0, Contracts.AssetRouter.empty, false⟩
  vault := ⟨0, 0, 0, 0, 0, fun _ => 0, fun _ => 0, fun _ => 0, false⟩
  chainAssetHandler := ⟨0, 0, false⟩
  tracker := ⟨0, 0, false⟩
  center := ⟨0, false⟩
  baseToken := ⟨0, false⟩
  flowManager := ⟨0⟩
  weth := ⟨0, 0, false⟩

/-- `_setAssetHandler(id, h)` (`AR/AssetRouterBase.sol:289-291`): the handler moves, the tracker
does not. -/
def ConfigWorld.pointRoute (w : ConfigWorld) (id : AssetId) (h : Address) : ConfigWorld :=
  { w with router := { w.router with routes :=
      { w.router.routes with handler := upd w.router.routes.handler id h } } }

/-- Replace the router's two maps. -/
def ConfigWorld.setRoutes (w : ConfigWorld) (R : Contracts.AssetRouter.Router) : ConfigWorld :=
  { w with router := { w.router with routes := R } }

/-- `_setNewTokenStorage(id, token, origin)` (`NativeTokenVaultBase.sol:565-575`): the three
registry maps, written together.  The bridged-token list and the tracker hook write no
modelled word. -/
def ConfigWorld.setNewTokenStorage (w : ConfigWorld) (id : AssetId) (tok : Address)
    (origin : Chain) : ConfigWorld :=
  { w with vault := { w.vault with
      tokenAddress := upd w.vault.tokenAddress id tok
      assetIdOf := upd w.vault.assetIdOf tok id
      originChainId := upd w.vault.originChainId id origin } }

/-! ## The `initL2` / `updateL2` entry points

Each takes the caller `s`.  The `onlyUpgrader` check is `s = E.upgrader`.  Where
`reentrancyGuardInitializer` precedes it, the lock check comes first; both revert, so their
order does not show. -/

/-- `L2MessageRoot.updateL2` (`L2MessageRoot.sol:73-75`). -/
def messageRootUpdateL2 (E : ConfigEnv) (s : Address) (l1 : Chain) (w : ConfigWorld) :
    Option ConfigWorld :=
  if s = E.upgrader then some { w with messageRoot := { w.messageRoot with l1 := l1 } }
  else none

/-- `L2MessageRoot.initL2` (`:67-71`): the lock, then `updateL2`. -/
def messageRootInitL2 (E : ConfigEnv) (s : Address) (l1 : Chain) (w : ConfigWorld) :
    Option ConfigWorld :=
  if w.messageRoot.locked then none
  else messageRootUpdateL2 E s l1 { w with messageRoot := { w.messageRoot with locked := true } }

/-- `L2Bridgehub.updateL2` (`L2Bridgehub.sol:77-92`): `L1_CHAIN_ID`, then
`ETH_TOKEN_ASSET_ID = encodeNTVAssetId(L1_CHAIN_ID, ETH_TOKEN_ADDRESS)` (`:91`). -/
def bridgehubUpdateL2 (E : ConfigEnv) (s : Address) (l1 : Chain) (w : ConfigWorld) :
    Option ConfigWorld :=
  if s = E.upgrader then
    some { w with bridgehub := { w.bridgehub with l1 := l1, eth := E.encNTV l1 E.ethToken } }
  else none

/-- `L2Bridgehub.initL2` (`:60-68`): the lock, then `updateL2`. -/
def bridgehubInitL2 (E : ConfigEnv) (s : Address) (l1 : Chain) (w : ConfigWorld) :
    Option ConfigWorld :=
  if w.bridgehub.locked then none
  else bridgehubUpdateL2 E s l1 { w with bridgehub := { w.bridgehub with locked := true } }

/-- `L2AssetRouter.updateL2` (`AR/L2AssetRouter.sol:173-188`): a nonzero counterpart (`:179`),
then the three words, with no check against the stored ones. -/
def routerUpdateL2 (E : ConfigEnv) (s : Address) (l1 : Chain) (r : Address) (a : AssetId)
    (w : ConfigWorld) : Option ConfigWorld :=
  if s = E.upgrader ∧ r ≠ 0 then
    some { w with router := { w.router with l1 := l1, l1AssetRouter := r, base := a } }
  else none

/-- `L2AssetRouter.initL2` (`:154-163`): the lock, `updateL2`, then
`_setAssetHandler(_baseTokenAssetId, L2_NATIVE_TOKEN_VAULT_ADDR)` (`:162`). -/
def routerInitL2 (E : ConfigEnv) (s : Address) (l1 : Chain) (r : Address) (a : AssetId)
    (w : ConfigWorld) : Option ConfigWorld :=
  if w.router.locked then none
  else (routerUpdateL2 E s l1 r a { w with router := { w.router with locked := true } }).map
    fun w' => w'.pointRoute a E.ntvAddr

/-- Which of the vault's two id freezes are present.  The deployed vault has both
(`deployedFreezes`); the other values are variants used by the countermodels. -/
structure VaultFreezes where
  /-- `require(L1_CHAIN_ID == 0 || L1_CHAIN_ID == _l1ChainId)` (`NTV/L2NativeTokenVault.sol:148`). -/
  l1 : Bool
  /-- `require(BASE_TOKEN_ASSET_ID == 0 || BASE_TOKEN_ASSET_ID == _baseTokenBridgingData.assetId)`
  (`:152-155`). -/
  base : Bool

/-- The vault at `b17415d20`: both freezes. -/
def deployedFreezes : VaultFreezes := ⟨true, true⟩

/-- `L2NativeTokenVault.updateL2` (`NTV/L2NativeTokenVault.sol:134-174`), with the freezes `F`.
Checks in source order: upgrader, nonzero WETH (`:142`), WETH frozen once set (`:145`), then
the freezes in `F`.  Writes: the four words (`:157-160`) and the base token's registry entry
(`:165-167`), whatever its previous value. -/
def vaultUpdateL2With (F : VaultFreezes) (E : ConfigEnv) (s : Address) (l1 : Chain)
    (weth : Address) (b : BaseTokenData) (w : ConfigWorld) : Option ConfigWorld :=
  if s = E.upgrader ∧ weth ≠ 0 ∧ (w.vault.weth = 0 ∨ w.vault.weth = weth)
      ∧ (F.l1 = true → w.vault.l1 = 0 ∨ w.vault.l1 = l1)
      ∧ (F.base = true → w.vault.base = 0 ∨ w.vault.base = b.assetId) then
    some { w with vault := { w.vault with
      weth := weth, base := b.assetId, l1 := l1, baseOriginToken := b.originToken
      tokenAddress := upd w.vault.tokenAddress b.assetId E.baseTokenAddr
      assetIdOf := upd w.vault.assetIdOf E.baseTokenAddr b.assetId
      originChainId := upd w.vault.originChainId b.assetId b.originChainId } }
  else none

/-- The deployed `L2NativeTokenVault.updateL2`. -/
def vaultUpdateL2 : ConfigEnv → Address → Chain → Address → BaseTokenData → ConfigWorld →
    Option ConfigWorld :=
  vaultUpdateL2With deployedFreezes

/-- `L2NativeTokenVault.initL2` (`:99-115`): the lock, `updateL2`, then a nonzero beacon
(`:110-113`). -/
def vaultInitL2 (E : ConfigEnv) (s : Address) (l1 : Chain) (beacon weth : Address)
    (b : BaseTokenData) (w : ConfigWorld) : Option ConfigWorld :=
  if w.vault.locked then none
  else (vaultUpdateL2 E s l1 weth b { w with vault := { w.vault with locked := true } }).bind
    fun w' => if beacon ≠ 0 then some { w' with vault := { w'.vault with beacon := beacon } }
      else none

/-- `L2ChainAssetHandler.updateL2` (`L2ChainAssetHandler.sol:100-109`): `L1_CHAIN_ID` and
`ETH_TOKEN_ASSET_ID = encodeNTVAssetId(_l1ChainId, ETH_TOKEN_ADDRESS)` (`:105`). -/
def chainAssetHandlerUpdateL2 (E : ConfigEnv) (s : Address) (l1 : Chain) (w : ConfigWorld) :
    Option ConfigWorld :=
  if s = E.upgrader then
    some { w with chainAssetHandler :=
      { w.chainAssetHandler with l1 := l1, eth := E.encNTV l1 E.ethToken } }
  else none

/-- `L2ChainAssetHandler.initL2` (`:89-92`): the lock, then `updateL2`. -/
def chainAssetHandlerInitL2 (E : ConfigEnv) (s : Address) (l1 : Chain) (w : ConfigWorld) :
    Option ConfigWorld :=
  if w.chainAssetHandler.locked then none
  else chainAssetHandlerUpdateL2 E s l1
    { w with chainAssetHandler := { w.chainAssetHandler with locked := true } }

/-- `L2AssetTracker.initL2` (`L2AssetTracker.sol:96-99`): the lock, then both words.  The
tracker has no `updateL2`. -/
def trackerInitL2 (E : ConfigEnv) (s : Address) (l1 : Chain) (a : AssetId) (w : ConfigWorld) :
    Option ConfigWorld :=
  if w.tracker.locked then none
  else if s = E.upgrader then some { w with tracker := ⟨l1, a, true⟩ } else none

/-- `InteropCenter.initL2` (`interop/InteropCenter.sol:170-187`): the lock, a nonzero ZK token
id (`:178`), then `L1_CHAIN_ID` (`:181`). -/
def centerInitL2 (E : ConfigEnv) (s : Address) (l1 : Chain) (zk : AssetId) (w : ConfigWorld) :
    Option ConfigWorld :=
  if w.center.locked then none
  else if s = E.upgrader ∧ zk ≠ 0 then some { w with center := ⟨l1, true⟩ } else none

/-- `L2BaseToken.initL2` (`l2-system/zksync-os/L2BaseToken.sol:64-77`): its own one-shot flag
(`:65-68`), then `L1_CHAIN_ID` (`:69`). -/
def baseTokenInitL2 (E : ConfigEnv) (s : Address) (l1 : Chain) (w : ConfigWorld) :
    Option ConfigWorld :=
  if s = E.upgrader ∧ w.baseToken.initialized = false then
    some { w with baseToken := ⟨l1, true⟩ }
  else none

/-- `AtomicFlowManager.initL2` (`atomic-interop/AtomicFlowManager.sol:76-85`): refuses unless
`L1_CHAIN_ID` is zero (`:77-79`) and the new one is nonzero (`:81-83`). -/
def flowManagerInitL2 (E : ConfigEnv) (s : Address) (l1 : Chain) (w : ConfigWorld) :
    Option ConfigWorld :=
  if s = E.upgrader ∧ w.flowManager.l1 = 0 ∧ l1 ≠ 0 then some { w with flowManager := ⟨l1⟩ }
  else none

/-- `_ensureWethToken(NTV.WETH_TOKEN(), …)` (`Helper:210-217, 409-439`).  A nonzero stored WETH
is returned unchanged.  Otherwise a proxy is created whose constructor runs `initializeV3`
(`bridge/L2WrappedBaseToken.sol:55-78`), which requires a nonzero `l2Bridge`
(`L2_ASSET_ROUTER_ADDR`, `:62`), `l1Address` (`:64`) and base asset id (`:65`) and stores the
last two.  Returns the state and the WETH address. -/
def ensureWeth (E : ConfigEnv) (u : UpgradeInput) (w : ConfigWorld) :
    Option (ConfigWorld × Address) :=
  if w.vault.weth ≠ 0 then some (w, w.vault.weth)
  else if E.routerAddr ≠ 0 ∧ u.baseTokenL1Address ≠ 0 ∧ u.base.assetId ≠ 0 then
    some ({ w with weth := ⟨u.base.assetId, u.baseTokenL1Address, true⟩ }, E.wethProxy u)
  else none

/-! ## The two upgrade programs -/

/-- `L2GenesisUpgrade.genesisUpgrade(chainId, …)` (`UP/L2GenesisUpgrade.sol:22-40`) running
`performForceDeployedContractsInit(…, true)` (`Helper:187-235`), as listed in the header. -/
def genesisUpgrade (E : ConfigEnv) (chainId : Chain) (u : UpgradeInput) (w : ConfigWorld) :
    Option ConfigWorld :=
  if chainId = 0 ∨ u.governance = 0 then none
  else (ensureWeth E u w).bind fun p =>
    (messageRootInitL2 E E.upgrader u.l1ChainId p.1).bind fun w1 =>
    (bridgehubInitL2 E E.upgrader u.l1ChainId w1).bind fun w2 =>
    (routerInitL2 E E.upgrader u.l1ChainId u.l1AssetRouter u.base.assetId w2).bind fun w3 =>
    (vaultInitL2 E E.upgrader u.l1ChainId (E.beaconOf u) p.2 u.base w3).bind fun w4 =>
    (chainAssetHandlerInitL2 E E.upgrader u.l1ChainId w4).bind fun w5 =>
    (trackerInitL2 E E.upgrader u.l1ChainId u.base.assetId w5).bind fun w6 =>
    (centerInitL2 E E.upgrader u.l1ChainId u.zkTokenAssetId w6).bind fun w7 =>
    (baseTokenInitL2 E E.upgrader u.l1ChainId w7).bind fun w8 =>
    flowManagerInitL2 E E.upgrader u.l1ChainId w8

/-- `L2DefaultUpgrade.upgrade(…)` (`UP/L2DefaultUpgrade.sol:16-27`) running
`performForceDeployedContractsInit(…, false)`, with the vault's freezes `F`. -/
def defaultUpgradeWith (F : VaultFreezes) (E : ConfigEnv) (u : UpgradeInput) (w : ConfigWorld) :
    Option ConfigWorld :=
  if u.governance = 0 then none
  else (ensureWeth E u w).bind fun p =>
    (messageRootUpdateL2 E E.upgrader u.l1ChainId p.1).bind fun w1 =>
    (bridgehubUpdateL2 E E.upgrader u.l1ChainId w1).bind fun w2 =>
    (routerUpdateL2 E E.upgrader u.l1ChainId u.l1AssetRouter u.base.assetId w2).bind fun w3 =>
    (vaultUpdateL2With F E E.upgrader u.l1ChainId p.2 u.base w3).bind fun w4 =>
    chainAssetHandlerUpdateL2 E E.upgrader u.l1ChainId w4

/-- The deployed default upgrade. -/
def defaultUpgrade : ConfigEnv → UpgradeInput → ConfigWorld → Option ConfigWorld :=
  defaultUpgradeWith deployedFreezes

/-- What the complex upgrader delegatecalls (`MODEL-L2-CONFIG`). -/
inductive UpgradeProgram where
  /-- `L2GenesisUpgrade.genesisUpgrade(chainId, …)`. -/
  | genesis (chainId : Chain) (u : UpgradeInput)
  /-- `L2DefaultUpgrade.upgrade(…)`. -/
  | default (u : UpgradeInput)

/-- The delegatecalled program. -/
def runProgram (E : ConfigEnv) (w : ConfigWorld) : UpgradeProgram → Option ConfigWorld
  | .genesis c u => genesisUpgrade E c u w
  | .default u => defaultUpgrade E u w

/-! ## Every modelled entry point -/

/-- One direct call of an `initL2`/`updateL2`, outside the helper. -/
inductive DirectCall where
  | messageRootInit (l1 : Chain)
  | messageRootUpdate (l1 : Chain)
  | bridgehubInit (l1 : Chain)
  | bridgehubUpdate (l1 : Chain)
  | routerInit (l1 : Chain) (r : Address) (a : AssetId)
  | routerUpdate (l1 : Chain) (r : Address) (a : AssetId)
  | vaultInit (l1 : Chain) (beacon weth : Address) (b : BaseTokenData)
  | vaultUpdate (l1 : Chain) (weth : Address) (b : BaseTokenData)
  | chainAssetHandlerInit (l1 : Chain)
  | chainAssetHandlerUpdate (l1 : Chain)
  | trackerInit (l1 : Chain) (a : AssetId)
  | centerInit (l1 : Chain) (zk : AssetId)
  | baseTokenInit (l1 : Chain)
  | flowManagerInit (l1 : Chain)

/-- A direct call by `s`.  WETH's `initializeV3` is not listed: outside the proxy's
constructor it reverts (`reinitializer(3)`). -/
def directExec (E : ConfigEnv) (s : Address) (w : ConfigWorld) : DirectCall → Option ConfigWorld
  | .messageRootInit l1 => messageRootInitL2 E s l1 w
  | .messageRootUpdate l1 => messageRootUpdateL2 E s l1 w
  | .bridgehubInit l1 => bridgehubInitL2 E s l1 w
  | .bridgehubUpdate l1 => bridgehubUpdateL2 E s l1 w
  | .routerInit l1 r a => routerInitL2 E s l1 r a w
  | .routerUpdate l1 r a => routerUpdateL2 E s l1 r a w
  | .vaultInit l1 beacon weth b => vaultInitL2 E s l1 beacon weth b w
  | .vaultUpdate l1 weth b => vaultUpdateL2 E s l1 weth b w
  | .chainAssetHandlerInit l1 => chainAssetHandlerInitL2 E s l1 w
  | .chainAssetHandlerUpdate l1 => chainAssetHandlerUpdateL2 E s l1 w
  | .trackerInit l1 a => trackerInitL2 E s l1 a w
  | .centerInit l1 zk => centerInitL2 E s l1 zk w
  | .baseTokenInit l1 => baseTokenInitL2 E s l1 w
  | .flowManagerInit l1 => flowManagerInitL2 E s l1 w

/-- `_unsafeRegisterNativeToken(t)` (`NativeTokenVaultBase.sol:492-499`): the registry entry at
`encodeNTVAssetId(block.chainid, t)` with origin `block.chainid`, then the router's
`setAssetHandlerAddressThisChain(bytes32(t), address(this))` called by the vault
(`AR/AssetRouterBase.sol:65-77`), which passes the vault's check and records the vault as
handler and tracker of the same id. -/
def registerNative (E : ConfigEnv) (w : ConfigWorld) (t : Address) : ConfigWorld :=
  let w1 := w.setNewTokenStorage (E.encNTV E.thisChain t) t E.thisChain
  w1.setRoutes (setHandler E.enc E.thisChain E.ntvAddr E.ntvAddr w1.router.routes E.ntvAddr t E.ntvAddr)

/-- The modelled calls. -/
inductive ConfigOp where
  /-- `L2ComplexUpgrader.upgrade` or `forceDeployAndUpgradeUniversal` delegatecalling the
  program. -/
  | upgrade (p : UpgradeProgram)
  /-- One `initL2`/`updateL2`, called directly. -/
  | direct (c : DirectCall)
  /-- `L2AssetRouter.setAssetHandlerAddress(src, id, h)` (`AR/L2AssetRouter.sol:198-204`). -/
  | counterpartSet (src : Chain) (id : AssetId) (h : Address)
  /-- `setAssetHandlerAddressThisChain(d, h)` (`AR/L2AssetRouter.sol:209-214`) by an account
  other than the vault. -/
  | routerRegister (d : AssetData) (h : Address)
  /-- `_finalizeDeposit`'s unset-handler branch (`AR/AssetRouterBase.sol:273-278`) behind
  `L2AssetRouter.finalizeDeposit` (`AR/L2AssetRouter.sol:253-262`). -/
  | finalizeFallback (id : AssetId)
  /-- `_registerToken(t)` (`NativeTokenVaultBase.sol:131-140`) with its router callback. -/
  | vaultRegister (t : Address)
  /-- `_ensureAndSaveTokenDeployed` (`NativeTokenVaultBase.sol:515-563`) for asset `id`, with
  resolved origin chain `origin`, origin token `ot` and deployed token `tok`. -/
  | vaultDeploy (id : AssetId) (origin : Chain) (ot tok : Address)

/-- One call by `s`.  `none` is a revert. -/
def configExec (E : ConfigEnv) (s : Address) (w : ConfigWorld) : ConfigOp → Option ConfigWorld
  | .upgrade p => if s = E.forceDeployer then runProgram E w p else none
  | .direct c => directExec E s w c
  | .counterpartSet src id h =>
      -- `onlyAssetRouterCounterpart` (`AR/L2AssetRouter.sol:96-107`)
      if src = w.router.l1 ∧ E.undoAlias s = w.router.l1AssetRouter then
        some (w.pointRoute id h)
      else none
  | .routerRegister d h =>
      -- `require(senderIsNTV || msg.sender == assetDeploymentTracker[assetId])` (`:73`), for a
      -- caller other than the vault; `msg.sender` is never zero
      if s ≠ 0 ∧ s ≠ E.ntvAddr
          ∧ w.router.routes.tracker (writtenId E.enc E.thisChain E.ntvAddr E.ntvAddr s d) = s then
        some (w.setRoutes (setHandler E.enc E.thisChain E.ntvAddr E.ntvAddr w.router.routes s d h))
      else none
  | .finalizeFallback id =>
      -- `require(_assetId != BASE_TOKEN_ASSET_ID)` (`AR/L2AssetRouter.sol:258`), then the
      -- unset-handler branch (`AR/AssetRouterBase.sol:273-278`)
      if id ≠ w.router.base ∧ w.router.routes.handler id = 0 then
        some (w.pointRoute id E.ntvAddr)
      else none
  | .vaultRegister t =>
      -- the WETH rule (`NativeTokenVaultBase.sol:133-136`), unregistered (`:138`)
      if (t ≠ w.vault.weth ∨ E.thisChain = w.vault.l1) ∧ w.vault.assetIdOf t = 0 then
        some (registerNative E w t)
      else none
  | .vaultDeploy id origin ot tok =>
      -- a bridged asset with no token (`:225-235`, `:277-283`), `assetIdCheck` (`:557`), not
      -- native (`:603`), `bridgeInitialize`'s nonzero origin token
      -- (`bridge/BridgedStandardERC20.sol:83`), and a fresh nonzero CREATE2 address
      if w.vault.tokenAddress id = 0 ∧ w.vault.originChainId id ≠ E.thisChain
          ∧ id = E.encNTV origin ot ∧ origin ≠ E.thisChain ∧ ot ≠ 0
          ∧ tok ≠ 0 ∧ tok ≠ E.baseTokenAddr then
        some (w.setNewTokenStorage id tok origin)
      else none

/-- One logged call. -/
structure ConfigCall where
  sender : Address
  op : ConfigOp

/-- A run of successful calls, logged oldest first. -/
inductive ConfigRun (E : ConfigEnv) : ConfigWorld → List ConfigCall → ConfigWorld → Prop
  | nil {w : ConfigWorld} : ConfigRun E w [] w
  | snoc {w v v' : ConfigWorld} {cs : List ConfigCall} {c : ConfigCall} :
      ConfigRun E w cs v → configExec E c.sender v c.op = some v' →
      ConfigRun E w (cs ++ [c]) v'

/-! ## The invariant -/

/-- All copies agree.  Every L1 chain id word is `l1`; every base asset id copy is `a`; both
ETH asset ids are derived from `l1`; the vault's WETH is `weth`; the vault maps `a` to the
base-token system contract and back; every built-in is initialized; on the router every
recorded deployment tracker is zero or the vault.  Also the environment fact that
`L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR` is nonzero (it is `0x800a`). -/
structure ConfigConsistent (E : ConfigEnv) (l1 : Chain) (a : AssetId) (weth : Address)
    (w : ConfigWorld) : Prop where
  l1_ne : l1 ≠ 0
  base_ne : a ≠ 0
  weth_ne : weth ≠ 0
  baseTokenAddr_ne : E.baseTokenAddr ≠ 0
  messageRootL1 : w.messageRoot.l1 = l1
  bridgehubL1 : w.bridgehub.l1 = l1
  routerL1 : w.router.l1 = l1
  vaultL1 : w.vault.l1 = l1
  chainAssetHandlerL1 : w.chainAssetHandler.l1 = l1
  trackerL1 : w.tracker.l1 = l1
  centerL1 : w.center.l1 = l1
  baseTokenL1 : w.baseToken.l1 = l1
  flowManagerL1 : w.flowManager.l1 = l1
  routerBase : w.router.base = a
  vaultBase : w.vault.base = a
  trackerBase : w.tracker.base = a
  wethBase : w.weth.base = a
  bridgehubEth : w.bridgehub.eth = E.encNTV l1 E.ethToken
  chainAssetHandlerEth : w.chainAssetHandler.eth = E.encNTV l1 E.ethToken
  vaultWeth : w.vault.weth = weth
  baseTokenAddress : w.vault.tokenAddress a = E.baseTokenAddr
  baseAssetIdOf : w.vault.assetIdOf E.baseTokenAddr = a
  messageRootLocked : w.messageRoot.locked = true
  bridgehubLocked : w.bridgehub.locked = true
  routerLocked : w.router.locked = true
  vaultLocked : w.vault.locked = true
  chainAssetHandlerLocked : w.chainAssetHandler.locked = true
  trackerLocked : w.tracker.locked = true
  centerLocked : w.center.locked = true
  baseTokenInitialized : w.baseToken.initialized = true
  trackersVaultOnly : ∀ x, w.router.routes.tracker x = 0 ∨ w.router.routes.tracker x = E.ntvAddr

/-- The router points the base id at the vault. -/
def BaseRoutedToVault (E : ConfigEnv) (a : AssetId) (w : ConfigWorld) : Prop :=
  w.router.routes.handler a = E.ntvAddr

/-- The vault's origin data for the base id: `originChainId[a] = o` and
`BASE_TOKEN_ORIGIN_TOKEN = t`. -/
def BaseOriginIs (o : Chain) (t : Address) (a : AssetId) (w : ConfigWorld) : Prop :=
  w.vault.originChainId a = o ∧ w.vault.baseOriginToken = t

/-- The vault's and the tracker's test "the base token is native to this chain": the vault's
`originChainId[BASE_TOKEN_ASSET_ID] == block.chainid`.  The vault reads it for the base token
in `_bridgeBurnToken` (`_isBridgedToken`, `NativeTokenVaultBase.sol:369`), which picks the
branch at `:435-446` and, for a bridged token, resolves the origin token through
`BASE_TOKEN_ORIGIN_TOKEN` (`:389-393`, `NTV/L2NativeTokenVault.sol:307-312`); the tracker reads
the same word through `L2_NATIVE_TOKEN_VAULT.originChainId(BASE_TOKEN_ASSET_ID)`
(`L2AssetTracker.sol:171, 183`). -/
def BaseNativeHere (E : ConfigEnv) (w : ConfigWorld) : Prop :=
  w.vault.originChainId w.vault.base = E.thisChain

/-- The scalar configuration words: everything in the table except the three registry maps
and the router's two maps. -/
structure ScalarConfig where
  messageRootL1 : Chain
  bridgehubL1 : Chain
  bridgehubEth : AssetId
  routerL1 : Chain
  routerL1AssetRouter : Address
  routerBase : AssetId
  vaultL1 : Chain
  vaultBase : AssetId
  vaultWeth : Address
  vaultBaseOriginToken : Address
  chainAssetHandlerL1 : Chain
  chainAssetHandlerEth : AssetId
  trackerL1 : Chain
  trackerBase : AssetId
  centerL1 : Chain
  baseTokenL1 : Chain
  flowManagerL1 : Chain
  wethBase : AssetId

/-- Read the scalar words. -/
def ConfigWorld.scalars (w : ConfigWorld) : ScalarConfig where
  messageRootL1 := w.messageRoot.l1
  bridgehubL1 := w.bridgehub.l1
  bridgehubEth := w.bridgehub.eth
  routerL1 := w.router.l1
  routerL1AssetRouter := w.router.l1AssetRouter
  routerBase := w.router.base
  vaultL1 := w.vault.l1
  vaultBase := w.vault.base
  vaultWeth := w.vault.weth
  vaultBaseOriginToken := w.vault.baseOriginToken
  chainAssetHandlerL1 := w.chainAssetHandler.l1
  chainAssetHandlerEth := w.chainAssetHandler.eth
  trackerL1 := w.tracker.l1
  trackerBase := w.tracker.base
  centerL1 := w.center.l1
  baseTokenL1 := w.baseToken.l1
  flowManagerL1 := w.flowManager.l1
  wethBase := w.weth.base

/-- The registry and routing words at the base id `a`: `tokenAddress[a]`,
`assetId[L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR]`, `originChainId[a]` and the router's handler
of `a`. -/
def ConfigWorld.baseEntries (E : ConfigEnv) (a : AssetId) (w : ConfigWorld) :
    Address × AssetId × Chain × Address :=
  (w.vault.tokenAddress a, w.vault.assetIdOf E.baseTokenAddr, w.vault.originChainId a,
    w.router.routes.handler a)

/-! ## Run premises -/

/-- The call is the counterpart's write at the id `a`. -/
def ConfigOp.IsCounterpartAt (a : AssetId) : ConfigOp → Prop
  | .counterpartSet _ id _ => id = a
  | _ => False

/-- The two premises of the run results, for base id `a`:

* the upgrader makes no direct call: under `MODEL-L2-CONFIG` its calls are the helper's, which
  `upgrade` already contains;
* a logged vault registration does not register a token whose vault id on this chain is `a`.
  This is a premise on the logged call's own input. -/
structure ConfigCall.Admissible (E : ConfigEnv) (a : AssetId) (c : ConfigCall) : Prop where
  notUpgraderDirect : ∀ d, c.op = .direct d → c.sender ≠ E.upgrader
  registrationMissesBase : ∀ t, c.op = .vaultRegister t → E.encNTV E.thisChain t ≠ a

/-- Every logged default upgrade passes the origin data `o`, `t` for the base token. -/
def ConfigCall.KeepsBaseOrigin (o : Chain) (t : Address) (c : ConfigCall) : Prop :=
  ∀ u, c.op = .upgrade (.default u) → u.base.originChainId = o ∧ u.base.originToken = t

end Contracts.L2BridgeConfig
