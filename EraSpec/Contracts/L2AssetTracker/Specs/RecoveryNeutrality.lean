import EraSpec.Core.Word

/-!
# Model at v35: the source chain's bridge-out and atomic-recovery paths, on the `L2AssetTracker`

Source: era-contracts `draft/v0.35.0` head `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`.  Paths are
relative to `l1-contracts/contracts/` and cited as

* `TRK` = `bridge/asset-tracker/L2AssetTracker.sol`,
* `NTV` = `bridge/ntv/NativeTokenVaultBase.sol`, `L2NTV` = `bridge/ntv/L2NativeTokenVault.sol`,
* `BTH` = `l2-system/BaseTokenHolder.sol`,
* `L2AR` = `bridge/asset-router/L2AssetRouter.sol`, `ARB` = `bridge/asset-router/AssetRouterBase.sol`,
* `AFM` = `atomic-interop/AtomicFlowManager.sol`, `IC` = `interop/InteropCenter.sol`.

`main` at `70096e2ea6eeb5373992e178064c4b26dcf6436a` has the same code on every path modelled here.  The
files differ from the v35 head in comments, renamed internal getters (`_assetRouter` and the like), the
`ERA_CHAIN_ID` slot (deprecated at the v35 head), the bridged-token deployment mechanism (abstracted
here), and, outside the modelled paths, the interop center's pause modifiers and fee-unit counter and
the peer-allowlist checks of the interop center and the flow manager.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.L2AssetTracker.Properties.RecoveryNeutrality` and proved in
`EraSpec.Contracts.L2AssetTracker.Proofs.RecoveryNeutrality`.

## State

* The tracker's storage `Tracker` (`TRK:38-59`): `chainBalance`, `isAssetRegistered`, `interopInfo`
  and `totalPreV31TotalSupply`.  The deprecated slots (`TRK:43-44`, `:65`) are never read or written.
* The vault's registry entries the tracker reads: `originChainId` and `tokenAddress` (`NTV:76-79`),
  read through `L2_NATIVE_TOKEN_VAULT.originChainId(a)` (`TRK:171`, `:183`, `:235`) and
  `.tokenAddress(a)` (`TRK:318`), and passed by the vault's own hooks (`L2NTV:279-293`).
* The router's `assetHandlerAddress` (`ARB:41`), which `recoverAtomicCall` reads (`L2AR:299-301`).
* The base-token holder's native balance `holder` (`BTH`).  It is a natural number; a transfer out of a
  smaller balance reverts (`Address.sendValue`).
* `currentSettlementLayerChainId()` (`TRK:162`, `:225`), which changes when the chain migrates.
* A ghost log of successful bridge-outs and vault recoveries (`Event`).  It is not contract storage; it
  records each such call's arguments and the settlement layer it ran under, so that the meaning of
  `totalWithdrawalsToL1` can be stated.

## Fixed configuration (`OPS-CONFIG`)

`Config.l1` is `L1_CHAIN_ID` and `Config.base` is `BASE_TOKEN_ASSET_ID`.  Each is stored in several
contracts, and the model keeps one value for all copies.  The genesis upgrade passes the same
`_fixedForceDeploymentsData.l1ChainId` to the router (`L2AR:154-163`), the vault (`L2NTV:99-115`), the
tracker (`TRK:96-99`) and the flow manager, and the same `baseTokenBridgingData.assetId` to the router,
the vault and the tracker (`l2-upgrades/L2GenesisForceDeploymentsHelper.sol:262-286`, `:356-359`,
`:374`).  The tracker's `initL2` is `reentrancyGuardInitializer` and runs once; the vault freezes
`BASE_TOKEN_ASSET_ID` once set (`L2NTV:152-155`).  The router's `updateL2` rewrites its `L1_CHAIN_ID`
on every upgrade with the same value (`L2AR:173-188`).  The tracker's `initL2` is not a step of the
model; runs start after genesis.

## Operations (`Op`)

Each operation is one successful call by the caller the source permits; a revert is `none` and no step.
Every write to the modelled state at v35 is one of these:

| `Op` | Source | Tracker hook |
|---|---|---|
| `vaultRegister` | `_setNewTokenStorage` (`NTV:565-575`), reached from native registration (`NTV:492-499`) and bridged deployment (`NTV:550-563`) | `registerNewTokenIfNeeded` (`TRK:102-118`) |
| `vaultUpdateBase` | `updateL2`'s registry writes for the base token (`L2NTV:165-167`), upgrader only | none |
| `registerBaseIfNeeded` | `registerBaseTokenIfNeeded` (`L2NTV:118-123`), upgrader only | `registerNewTokenIfNeeded` |
| `registerLegacy` | anyone's `registerLegacyToken` (`TRK:121-130`) | itself |
| `setHandler` | any write of `assetHandlerAddress` | none |
| `setSettlementLayer` | a migration (not a contract call) | none |
| `holderVm` | the runtime moving the holder's balance (`BTH:65-66`; `protocol-docs/bridging.md` "Base-token handling") | none |
| `vaultBurn` | `bridgeBurn` (`NTV:294-318`) through `_bridgeBurnToken` (`:361-410`) and `_getTokenAndBridgeToChain` (`:425-457`) | `handleInitiateBridgingOnL2` (`TRK:137-166`) or, for a base token the vault does not record as native here, `burnAndStartBridging` (`BTH:93-96`) and `handleInitiateBaseTokenBridgingOnL2` (`TRK:169-173`) |
| `icBurnBase` | the interop center's same-base-token value burn (`IC:432-440`) | `burnAndStartBridging`, `handleInitiateBaseTokenBridgingOnL2` |
| `vaultMint` | `bridgeMint` (`NTV:180-189`, `:220-247`) | `handleFinalizeBridgingOnL2` (`TRK:193-229`) |
| `holderGive` | `give` (`BTH:67-76`), interop handler only | `handleFinalizeBaseTokenBridgingOnL2` (`TRK:277-298`) |
| `baseTokenFinalize` | the runtime's call as `L2BaseToken` (`TRK:88-93`; `protocol-docs/bridging.md` "L2 Asset Tracker") | `handleFinalizeBaseTokenBridgingOnL2` |
| `claimRefund` | `AtomicFlowManager.claimRefund` (`AFM:250-265`) running `_recoverBundle` (`AFM:292-325`) | through the router and the vault, below |

## Recovery (`recoverBundle`, `routerRecoverAtomicCall`, `routerRecoverBase`, `vaultRecover`, `holderRecover`)

`_recoverBundle` (`AFM:292-325`) requires `destChainId != L1_CHAIN_ID` (`:299`) and walks the calls:
a call with `from == L2_ASSET_ROUTER_ADDR` goes to `recoverAtomicCall(destChainId, c.data)`
(`:312-315`, result ignored); any other call with nonzero `value` goes to
`bridgehubRecoverBaseToken(destChainId, destinationBaseTokenAssetId, c.from, c.value)` (`:316-323`).
There is no `try/catch`: one revert reverts the whole `claimRefund`, including the leg's
`Revertable -> Reverted` flip (`AFM:258-262`), which the model does not represent.

* `recoverAtomicCall` (`L2AR:269-303`): requires `_destChainId != L1_CHAIN_ID` (`:275`); returns `false`
  with no effect unless the selector is `finalizeDeposit` (`:284-286`); decodes `(uint256, bytes32,
  bytes)` (`:290`, a revert on failure); requires a nonzero handler for the asset (`:299-300`) and calls
  its `bridgeRecoverFailedTransfer(_destChainId, assetId, mintData)` (`:301`).
* `bridgehubRecoverBaseToken` (`L2AR:314-328`): requires `_chainId != L1_CHAIN_ID` (`:320`), builds the
  mint data `(receiver, receiver, 0, amount, "")` (`:326`) and calls the vault (`:327`).
* The vault's `bridgeRecoverFailedTransfer` (`NTV:195-214`) decodes the mint data (`:201-202`), reads
  `isNative` (`:203`) and runs the L2 `_disburseFailedTransfer` (`L2NTV:204-227`):
  `assertRecoveryIsAccountingNeutral(_assetId, _chainId)` (`:213`, which is `TRK:176-185`: the
  destination is not L1, and the base token is not native here); for the base token,
  `BaseTokenHolder.recoverBaseToken` (`:214-217`); otherwise `NTV:264-286`: the tracker hook
  `handleFinalizeBridgingOnL2` (`:276`), then the release (`_withdrawFunds`, `:278`, or the bridged
  token's `bridgeMint`, `:279-285`, deploying the token first if the vault has no address for it).
* `recoverBaseToken` (`BTH:79-87`): nothing for a zero amount (`:80-82`);
  `assertBaseTokenRecoveryIsAccountingNeutral(_toChainId)` (`:84`, which is `TRK:188-190` and so
  `TRK:176-185` for the base token); then `Address.sendValue` (`:85`).

`Guards` switches each of these checks: the flow manager's (`AFM:299`), the router's (`L2AR:275` and
`L2AR:320`), the vault's call of the tracker check (`L2NTV:213`, L1 part `TRK:179` and base part
`TRK:182-184`), and the holder's call (`BTH:84`, the same two parts).  `Guards.v35` has all of them, as
the source does; the others exist only to state what each check contributes.

## Abstractions

* Token contracts are not modelled.  The tracker reads `totalSupply()` and `balanceOf(vault)` only at a
  token's first registration; `TokenReads` are those values at the moment of the call, any values.  A
  read through the zero address fails (`VM-CALL`, `SOL-ABI`).  The release of funds to a recipient (an
  ERC-20 transfer, a bridged token's `bridgeMint`, `sendValue`) is not modelled beyond the holder's
  balance; it happens after every tracker write of the call (`NTV:273-276`, `BTH:84-85`), and code it
  reaches can act on the modelled state only through the entry points above, which are further steps.
  In a `run` a claim is one step; `runNested` (and, for one asset, `runSchedule`) also lets further
  steps fall between the calls of a claim, as a release inside the claim can make them.
  In the model the release does not fail.  In the source it can (a recipient that rejects the base
  token, `protocol-docs/atomicity/security.md` "Known issues and accepted limitations" 3), which
  reverts the call; so statements that a call succeeds are about the modelled checks only.
* A handler other than the vault is arbitrary code.  Its `bridgeRecoverFailedTransfer` can neither call
  the tracker's hooks (`onlyL2NativeTokenVault`, `onlyBaseTokenHolder`) nor the holder's
  (`onlyNativeTokenVault`, `onlyBridgingCaller`); whatever it does through public entry points is a
  further step.  So in the model it changes nothing.
* Reject-only checks that do not touch the tracker or the holder are omitted: pause flags, reentrancy
  locks, WETH, the burn data's token/asset-id check (`NTV:337-354`), fee-on-transfer and metadata
  getters, and `msg.value` bookkeeping.  Omitting a check only adds runs.  The bridged-token deployment
  on a first `bridgeMint` is a separate `vaultRegister` step before the mint.
* Bridge-outs are taken at the vault: the router's choice of handler for a burn (`ARB:303-331`) is
  not modelled, so a burn by a handler other than the vault is not a step.
* `Config.deploy` is `_ensureAndSaveTokenDeployed` (`NTV:515-563`) on the recovery path: the origin
  chain decoded from the metadata and the deployed address, or `none` when decoding, `assetIdCheck`
  or deployment fails (`SOL-ABI`, `VM-DEPLOY`).
* Bundle call data is typed: `CallData.other` is a call `recoverAtomicCall` does not recognise,
  `badPayload` a `finalizeDeposit` whose `abi.decode` reverts, and in `finalizeDeposit a m` the mint
  data `m` is `none` when the vault's `decodeBridgeMintData` reverts.
* Leg states and sends are not modelled: `claimRefund` may name any bundle, any number of times.  In
  the source a claim needs its bundle's hash to have a `Revertable` leg (`AFM:251-257`); a leg is
  created only by the interop center's `append` (`AFM:104-108`, `:166`), which it calls only for a
  bundle toward a chain other than L1 (`IC:733-742`), and it refuses to send an atomic bundle toward
  L1 at all (`IC:552-553`).  So in this respect the model admits more runs than the source: a
  statement about every model run also covers the runs whose claims name appended bundles, and a
  model run with a claim toward L1 shows what the recovery-side checks do on their own, not a run of
  the source.
-/

namespace Contracts.L2AssetTracker.RecoveryNeutrality

/-- A 160-bit address. -/
abbrev Address := Fin (2 ^ 160)

/-- Asset ids are 256-bit words. -/
abbrev AssetId := UInt256

/-- Chain ids are 256-bit words. -/
abbrev ChainId := UInt256

/-! ## Checked uint256 arithmetic (`SOL-ARITH`) -/

/-- `MAX_TOKEN_BALANCE = type(uint256).max` (`common/Config.sol:79`). -/
def MAX_TOKEN_BALANCE : UInt256 := ⟨UInt256.size - 1, by unfold UInt256.size; omega⟩

/-- Solidity 0.8 checked `a + b` on `uint256`: `none` on overflow. -/
def checkedAdd (a b : UInt256) : Option UInt256 :=
  if h : a.val + b.val < UInt256.size then some ⟨a.val + b.val, h⟩ else none

/-- `if (a < b) revert …; a -= b;` (`TRK:306-311`): `none` exactly when `a < b`. -/
def checkedSub (a b : UInt256) : Option UInt256 :=
  if h : b.val ≤ a.val then some ⟨a.val - b.val, by have := a.isLt; omega⟩ else none

/-- `MAX_TOKEN_BALANCE - x` (`TRK:250`), which never underflows. -/
def maxMinus (x : UInt256) : UInt256 :=
  ⟨UInt256.size - 1 - x.val, by unfold UInt256.size; omega⟩

/-! ## Tracker storage -/

/-- `SavedTotalSupply` (`bridge/asset-tracker/IL2AssetTracker.sol:6-9`). -/
structure SavedTotalSupply where
  isSaved : Bool
  amount : UInt256
deriving DecidableEq

/-- `InteropL2Info` (`IL2AssetTracker.sol:17-25`). -/
structure InteropL2Info where
  /-- Amount withdrawn to L1 while the chain settled on L1. -/
  totalWithdrawalsToL1 : UInt256
  /-- Amount finalized from L1 while the chain settled on L1. -/
  totalSuccessfulDepositsFromL1 : UInt256
deriving DecidableEq

/-- The tracker's live storage at v35 (`TRK:38-59`). -/
structure Tracker where
  /-- `chainBalance[chainId][assetId]` (`TRK:38`). -/
  chainBalance : ChainId → AssetId → UInt256
  /-- `isAssetRegistered[assetId]` (`TRK:48`). -/
  isAssetRegistered : AssetId → Bool
  /-- `interopInfo[assetId]` (`TRK:55`). -/
  interopInfo : AssetId → InteropL2Info
  /-- `totalPreV31TotalSupply[assetId]` (`TRK:59`). -/
  totalPreV31TotalSupply : AssetId → SavedTotalSupply

/-- `chainBalance[c][a] = v`. -/
def Tracker.setChainBalance (t : Tracker) (c : ChainId) (a : AssetId) (v : UInt256) : Tracker :=
  { t with chainBalance := Function.update t.chainBalance c (Function.update (t.chainBalance c) a v) }

/-- `isAssetRegistered[a] = true` and `totalPreV31TotalSupply[a] = snap`. -/
def Tracker.markRegistered (t : Tracker) (a : AssetId) (snap : SavedTotalSupply) : Tracker :=
  { t with
    isAssetRegistered := Function.update t.isAssetRegistered a true
    totalPreV31TotalSupply := Function.update t.totalPreV31TotalSupply a snap }

/-- `interopInfo[a] = info`. -/
def Tracker.setInterop (t : Tracker) (a : AssetId) (info : InteropL2Info) : Tracker :=
  { t with interopInfo := Function.update t.interopInfo a info }

/-! ## Configuration, call data and the system state -/

/-- Decoded bridge-mint data `(originalCaller, remoteReceiver, originToken, amount, erc20Metadata)`
(`common/libraries/DataEncoding.sol`, `decodeBridgeMintData`). -/
structure MintData where
  originalCaller : Address
  remoteReceiver : Address
  originToken : Address
  amount : UInt256
  erc20Data : List UInt8

/-- The source chain's fixed configuration. -/
structure Config where
  /-- `block.chainid`. -/
  thisChain : ChainId
  /-- `L1_CHAIN_ID` of the tracker, the router and the flow manager (one value, `OPS-CONFIG`). -/
  l1 : ChainId
  /-- `BASE_TOKEN_ASSET_ID` of the tracker, the vault and the router (one value, `OPS-CONFIG`). -/
  base : AssetId
  /-- `L2_NATIVE_TOKEN_VAULT_ADDR`, as a value of `assetHandlerAddress`. -/
  ntv : Address
  /-- `L2_ASSET_ROUTER_ADDR`, as the `from` of a router-produced bundle call (`IC:820`). -/
  router : Address
  /-- `L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR`: the base token's `tokenAddress` (`L2NTV:165`) and the token
  the base-token hook passes (`TRK:296`). -/
  baseTokenAddr : Address
  /-- `_ensureAndSaveTokenDeployed(a, originToken, erc20Data)` on the recovery path (`NTV:279-283`):
  the decoded origin chain and the deployed token, or `none` if it reverts. -/
  deploy : AssetId → MintData → Option (ChainId × Address)

/-- What a token returns to the tracker's first-touch registration (`TRK:249`, `:258`). -/
structure TokenReads where
  /-- `IERC20(token).totalSupply()`. -/
  totalSupply : UInt256
  /-- `IERC20(token).balanceOf(L2_NATIVE_TOKEN_VAULT_ADDR)`. -/
  ntvBalance : UInt256

/-- A bundle call's data, as `recoverAtomicCall` parses it (`L2AR:284-290`). -/
inductive CallData where
  /-- `finalizeDeposit(sourceChainId, assetId, mintData)`; the mint data is `none` when the vault's
  `decodeBridgeMintData` reverts. -/
  | finalizeDeposit (a : AssetId) (mint : Option MintData)
  /-- The `finalizeDeposit` selector with a payload that `abi.decode` rejects. -/
  | badPayload
  /-- Fewer than four bytes or another selector: `recoverAtomicCall` returns `false`. -/
  | other

/-- One `InteropCall` of a bundle, as `_recoverBundle` reads it (`AFM:303-323`). -/
structure Call where
  /-- `InteropCall.from`. -/
  sender : Address
  data : CallData
  /-- `InteropCall.value`. -/
  value : UInt256

/-- The decoded bundle `claimRefund` recovers. -/
structure Bundle where
  /-- `destinationChainId`. -/
  dest : ChainId
  /-- `destinationBaseTokenAssetId`, fixed at send time (`IC:629-636`). -/
  destBase : AssetId
  calls : List Call

/-- Ghost record of one successful call (not contract storage). -/
inductive Event where
  /-- A bridge-out of `amount` of `asset` toward `dest`, made while the chain settled on `settlement`. -/
  | burned (asset : AssetId) (dest : ChainId) (amount : UInt256) (settlement : ChainId)
  /-- A vault recovery of `amount` of `asset` whose original destination was `dest`. -/
  | recovered (asset : AssetId) (dest : ChainId) (amount : UInt256)
deriving DecidableEq

/-- The source chain's state. -/
structure Sys where
  trk : Tracker
  /-- The vault's `originChainId` (`NTV:76`). -/
  origin : AssetId → ChainId
  /-- The vault's `tokenAddress` (`NTV:79`). -/
  token : AssetId → Address
  /-- The router's `assetHandlerAddress` (`ARB:41`). -/
  handler : AssetId → Address
  /-- The base-token holder's balance. -/
  holder : ℕ
  /-- `currentSettlementLayerChainId()`. -/
  sl : ChainId
  /-- Ghost log, oldest first. -/
  log : List Event

/-- Append a ghost event. -/
def Sys.record (sys : Sys) (e : Event) : Sys := { sys with log := sys.log ++ [e] }

/-- Which recovery checks are present.  The source has all of them (`Guards.v35`). -/
structure Guards where
  /-- `AFM:299`. -/
  managerL1 : Bool
  /-- `L2AR:275` and `L2AR:320`. -/
  routerL1 : Bool
  /-- `TRK:179`, as the vault calls it (`L2NTV:213`). -/
  vaultL1 : Bool
  /-- `TRK:182-184`, as the vault calls it (`L2NTV:213`). -/
  vaultBase : Bool
  /-- `TRK:179`, as the holder calls it (`BTH:84`, `TRK:188-190`). -/
  holderL1 : Bool
  /-- `TRK:182-184`, as the holder calls it (`BTH:84`, `TRK:188-190`). -/
  holderBase : Bool

/-- The source at v35: every check present. -/
def Guards.v35 : Guards := ⟨true, true, true, true, true, true⟩

/-! ## Tracker internals -/

/-- `_registerLegacyToken(a, tok)` (`TRK:233-262`): the vault must record an origin chain (`:235-236`).
A token native here must have a zero chain balance (`:237-244`) and gets `MAX - balanceOf(vault)` as
chain balance and snapshot (`:249-253`); any other gets its `totalSupply()` as snapshot (`:258-259`).
Both branches read the token, so a zero token address fails. -/
def registerLegacyInner (cfg : Config) (sys : Sys) (reads : TokenReads) (t : Tracker) (a : AssetId)
    (tok : Address) : Option Tracker :=
  if sys.origin a = 0 then none
  else if tok = 0 then none
  else if sys.origin a = cfg.thisChain then
    if t.chainBalance cfg.thisChain a ≠ 0 then none
    else some ((t.setChainBalance cfg.thisChain a (maxMinus reads.ntvBalance)).markRegistered a
      ⟨true, maxMinus reads.ntvBalance⟩)
  else some (t.markRegistered a ⟨true, reads.totalSupply⟩)

/-- `_registerLegacyTokenIfNeeded(a, tok)` (`TRK:264-274`): the first-touch registration. -/
def registerIfNeeded (cfg : Config) (sys : Sys) (reads : TokenReads) (t : Tracker) (a : AssetId)
    (tok : Address) : Option Tracker :=
  if t.isAssetRegistered a = true then some t else registerLegacyInner cfg sys reads t a tok

/-- `_decreaseChainBalance(c, a, x)` (`TRK:306-311`). -/
def decreaseChainBalance (t : Tracker) (c : ChainId) (a : AssetId) (x : UInt256) : Option Tracker :=
  (checkedSub (t.chainBalance c a) x).map (t.setChainBalance c a)

/-- `chainBalance[block.chainid][a] += x` (`TRK:220`), checked. -/
def increaseChainBalance (t : Tracker) (c : ChainId) (a : AssetId) (x : UInt256) : Option Tracker :=
  (checkedAdd (t.chainBalance c a) x).map (t.setChainBalance c a)

/-- `interopInfo[a].totalWithdrawalsToL1 += x` (`TRK:164`), checked. -/
def addWithdrawalToL1 (t : Tracker) (a : AssetId) (x : UInt256) : Option Tracker :=
  (checkedAdd (t.interopInfo a).totalWithdrawalsToL1 x).map fun w =>
    t.setInterop a { t.interopInfo a with totalWithdrawalsToL1 := w }

/-- `interopInfo[a].totalSuccessfulDepositsFromL1 += x` (`TRK:227`), checked. -/
def addDepositFromL1 (t : Tracker) (a : AssetId) (x : UInt256) : Option Tracker :=
  (checkedAdd (t.interopInfo a).totalSuccessfulDepositsFromL1 x).map fun w =>
    t.setInterop a { t.interopInfo a with totalSuccessfulDepositsFromL1 := w }

/-- `_handleInitiateBridgingOnL2Inner(d, a, x, tokOrigin)` (`TRK:146-166`): `_tryGetTokenAddress`
(`:152`, `:317-320`), first-touch registration (`:153`), the decrease for a token native here
(`:155-158`), and the withdrawal counter when the destination and the current settlement layer are
both L1 (`:160-165`). -/
def initiateInner (cfg : Config) (sys : Sys) (reads : TokenReads) (d : ChainId) (a : AssetId)
    (x : UInt256) (tokOrigin : ChainId) : Option Tracker :=
  if sys.token a = 0 then none
  else
    (registerIfNeeded cfg sys reads sys.trk a (sys.token a)).bind fun t₁ =>
      (if tokOrigin = cfg.thisChain then decreaseChainBalance t₁ cfg.thisChain a x
        else some t₁).bind fun t₂ =>
        if d = cfg.l1 ∧ sys.sl = cfg.l1 then addWithdrawalToL1 t₂ a x else some t₂

/-- `_handleFinalizeBridgingOnL2Inner(c, a, x, isNative, tok)` (`TRK:209-229`): first-touch
registration with the passed token (`:216`), the checked increase for a token native here
(`:219-221`), and the deposit counter when the source and the current settlement layer are both L1
(`:223-228`). -/
def finalizeInner (cfg : Config) (sys : Sys) (reads : TokenReads) (c : ChainId) (a : AssetId)
    (x : UInt256) (isNative : Bool) (tok : Address) : Option Tracker :=
  (registerIfNeeded cfg sys reads sys.trk a tok).bind fun t₁ =>
    (if isNative = true then increaseChainBalance t₁ cfg.thisChain a x else some t₁).bind fun t₂ =>
      if c = cfg.l1 ∧ sys.sl = cfg.l1 then addDepositFromL1 t₂ a x else some t₂

/-! ## Tracker entry points -/

/-- `registerNewTokenIfNeeded(a, o)` (`TRK:102-118`), called by the vault: nothing if registered; a
token native here gets chain balance and snapshot `MAX_TOKEN_BALANCE`, any other a zero snapshot. -/
def registerNewToken (cfg : Config) (t : Tracker) (a : AssetId) (o : ChainId) : Tracker :=
  if t.isAssetRegistered a = true then t
  else if o = cfg.thisChain then
    (t.setChainBalance o a MAX_TOKEN_BALANCE).markRegistered a ⟨true, MAX_TOKEN_BALANCE⟩
  else t.markRegistered a ⟨true, 0⟩

/-- The vault's `handleInitiateBridgingOnL2(d, a, x, originChainId[a])` (`L2NTV:279-283`,
`TRK:137-144`). -/
def trackerInitiate (cfg : Config) (sys : Sys) (reads : TokenReads) (d : ChainId) (a : AssetId)
    (x : UInt256) : Option Tracker :=
  initiateInner cfg sys reads d a x (sys.origin a)

/-- The holder's `handleInitiateBaseTokenBridgingOnL2(d, x)` (`TRK:169-173`): the base asset, with
the vault's origin chain for it. -/
def trackerInitiateBase (cfg : Config) (sys : Sys) (reads : TokenReads) (d : ChainId)
    (x : UInt256) : Option Tracker :=
  initiateInner cfg sys reads d cfg.base x (sys.origin cfg.base)

/-- The vault's `handleFinalizeBridgingOnL2(c, a, x, originChainId[a], tokenAddress[a])`
(`L2NTV:285-293`, `TRK:193-207`). -/
def trackerFinalize (cfg : Config) (sys : Sys) (reads : TokenReads) (c : ChainId) (a : AssetId)
    (x : UInt256) : Option Tracker :=
  finalizeInner cfg sys reads c a x (decide (sys.origin a = cfg.thisChain)) (sys.token a)

/-- `handleFinalizeBaseTokenBridgingOnL2(c, x)` (`TRK:277-298`): nothing for a zero amount, a revert
for a zero base asset id, and otherwise the finalize path with `_isNativeToThisChain: false`
hard-coded (`:295`). -/
def trackerFinalizeBase (cfg : Config) (sys : Sys) (reads : TokenReads) (c : ChainId)
    (x : UInt256) : Option Tracker :=
  if x = 0 then some sys.trk
  else if cfg.base = 0 then none
  else finalizeInner cfg sys reads c cfg.base x false cfg.baseTokenAddr

/-! ## The base-token holder -/

/-- `burnAndStartBridging{value: v}(d)` (`BTH:93-96`): the value arrives, then the tracker hook. -/
def holderBurn (cfg : Config) (sys : Sys) (reads : TokenReads) (d : ChainId) (v : UInt256) :
    Option Sys :=
  (trackerInitiateBase cfg sys reads d v).map fun t =>
    { sys with trk := t, holder := sys.holder + v.val }

/-- `recoverBaseToken(to, x, d)` (`BTH:79-87`): nothing for a zero amount; the tracker check
(`:84`, switched by `g.holderL1` and `g.holderBase`); then `sendValue`, which needs the balance. -/
def holderRecover (cfg : Config) (g : Guards) (sys : Sys) (x : UInt256) (d : ChainId) :
    Option Sys :=
  if x = 0 then some sys
  else if g.holderL1 = true ∧ d = cfg.l1 then none
  else if g.holderBase = true ∧ sys.origin cfg.base = cfg.thisChain then none
  else if sys.holder < x.val then none
  else some { sys with holder := sys.holder - x.val }

/-- `give(to, x, c)` (`BTH:67-76`): nothing for a zero amount; the tracker hook, then `sendValue`. -/
def holderGive (cfg : Config) (sys : Sys) (reads : TokenReads) (c : ChainId) (x : UInt256) :
    Option Sys :=
  if x = 0 then some sys
  else (trackerFinalizeBase cfg sys reads c x).bind fun t =>
    if sys.holder < x.val then none else some { sys with trk := t, holder := sys.holder - x.val }

/-! ## The vault -/

/-- `_setNewTokenStorage(a, tok, o)` (`NTV:565-575`): the registry entries, then the tracker's
`registerNewTokenIfNeeded(a, o)` (`L2NTV:177-179`). -/
def vaultSetNewTokenStorage (cfg : Config) (sys : Sys) (a : AssetId) (o : ChainId)
    (tok : Address) : Sys :=
  { sys with
    origin := Function.update sys.origin a o
    token := Function.update sys.token a tok
    trk := registerNewToken cfg sys.trk a o }

/-- `bridgeBurn(d, ·, a, ·, ·)` on its tracker and holder effects (`NTV:294-318`, `:361-410`,
`:425-457`): a nonzero amount (`:370`); for the base asset, the holder's `burnAndStartBridging` when
the vault does not record it as native here (`:437-441`) and the tracker hook otherwise (`:442-445`);
for any other asset, the tracker hook (`:446-447`). -/
def vaultBurn (cfg : Config) (sys : Sys) (reads : TokenReads) (d : ChainId) (a : AssetId)
    (x : UInt256) : Option Sys :=
  if x = 0 then none
  else if a = cfg.base ∧ sys.origin a ≠ cfg.thisChain then holderBurn cfg sys reads d x
  else (trackerInitiate cfg sys reads d a x).map fun t => { sys with trk := t }

/-- `bridgeMint(c, a, data)` on its tracker effect (`NTV:220-247`).  The router never delivers the
base asset here (`L2AR:258`). -/
def vaultMint (cfg : Config) (sys : Sys) (reads : TokenReads) (c : ChainId) (a : AssetId)
    (x : UInt256) : Option Sys :=
  if a = cfg.base then none
  else (trackerFinalize cfg sys reads c a x).map fun t => { sys with trk := t }

/-- `bridgeRecoverFailedTransfer(d, a, data)` (`NTV:195-214`) with the L2 `_disburseFailedTransfer`
(`L2NTV:204-227`, `NTV:264-286`).  The mint data must decode.  The tracker check (`L2NTV:213`) is
switched by `g.vaultL1` and `g.vaultBase`.  The base asset goes to the holder; any other asset gets the
tracker hook, then the release, with the bridged token deployed first if the vault records `a` as not
native here and has no address for it (`NTV:280-283`; the deployment reverts for an origin equal to
this chain, `NTV:603`).  A successful recovery appends a ghost `recovered` event. -/
def vaultRecover (cfg : Config) (g : Guards) (sys : Sys) (reads : AssetId → TokenReads)
    (d : ChainId) (a : AssetId) : Option MintData → Option Sys
  | none => none
  | some md =>
    if g.vaultL1 = true ∧ d = cfg.l1 then none
    else if g.vaultBase = true ∧ a = cfg.base ∧ sys.origin a = cfg.thisChain then none
    else if a = cfg.base then
      (holderRecover cfg g sys md.amount d).map fun s => s.record (.recovered a d md.amount)
    else
      (trackerFinalize cfg sys (reads a) d a md.amount).bind fun t =>
        if sys.origin a = cfg.thisChain ∨ sys.token a ≠ 0 then
          some ({ sys with trk := t }.record (.recovered a d md.amount))
        else
          (cfg.deploy a md).bind fun p =>
            if p.1 = cfg.thisChain then none
            else some ((vaultSetNewTokenStorage cfg { sys with trk := t } a p.1 p.2).record
              (.recovered a d md.amount))

/-! ## The router and the flow manager -/

/-- `recoverAtomicCall(d, data)` (`L2AR:269-303`).  A handler other than the vault is arbitrary code
that changes nothing modelled (see the header). -/
def routerRecoverAtomicCall (cfg : Config) (g : Guards) (sys : Sys) (reads : AssetId → TokenReads)
    (d : ChainId) : CallData → Option Sys
  | .other => if g.routerL1 = true ∧ d = cfg.l1 then none else some sys
  | .badPayload => none
  | .finalizeDeposit a m =>
    if g.routerL1 = true ∧ d = cfg.l1 then none
    else if sys.handler a = 0 then none
    else if sys.handler a = cfg.ntv then vaultRecover cfg g sys reads d a m
    else some sys

/-- `bridgehubRecoverBaseToken(d, a, receiver, x)` (`L2AR:314-328`). -/
def routerRecoverBase (cfg : Config) (g : Guards) (sys : Sys) (reads : AssetId → TokenReads)
    (d : ChainId) (a : AssetId) (receiver : Address) (x : UInt256) : Option Sys :=
  if g.routerL1 = true ∧ d = cfg.l1 then none
  else vaultRecover cfg g sys reads d a (some ⟨receiver, receiver, 0, x, []⟩)

/-- One iteration of `_recoverBundle`'s loop (`AFM:303-323`). -/
def recoverCall (cfg : Config) (g : Guards) (reads : AssetId → TokenReads) (d : ChainId)
    (destBase : AssetId) (sys : Sys) (c : Call) : Option Sys :=
  (if c.sender = cfg.router then routerRecoverAtomicCall cfg g sys reads d c.data
    else some sys).bind fun s =>
    if c.sender ≠ cfg.router ∧ c.value ≠ 0 then
      routerRecoverBase cfg g s reads d destBase c.sender c.value
    else some s

/-- The calls of a bundle in order, all or nothing. -/
def recoverCalls (cfg : Config) (g : Guards) (reads : AssetId → TokenReads) (d : ChainId)
    (destBase : AssetId) : Sys → List Call → Option Sys
  | sys, [] => some sys
  | sys, c :: cs =>
    (recoverCall cfg g reads d destBase sys c).bind fun s => recoverCalls cfg g reads d destBase s cs

/-- `_recoverBundle(bundle)` (`AFM:292-325`): the L1 check (`:299`), then every call. -/
def recoverBundle (cfg : Config) (g : Guards) (sys : Sys) (reads : AssetId → TokenReads)
    (b : Bundle) : Option Sys :=
  if g.managerL1 = true ∧ b.dest = cfg.l1 then none
  else recoverCalls cfg g reads b.dest b.destBase sys b.calls

/-- Vault recoveries of asset `a` toward `d`, one per mint data and in order, all or nothing: what one
bundle's recovery does to `a` when every call that reaches the vault names `a` (the bundle's value
calls with `destBase = a`, or its router calls for `a` with the vault as handler). -/
def vaultRecoverAll (cfg : Config) (g : Guards) (sys : Sys) (reads : AssetId → TokenReads)
    (d : ChainId) (a : AssetId) : List MintData → Option Sys
  | [] => some sys
  | md :: mds =>
    (vaultRecover cfg g sys reads d a (some md)).bind fun s => vaultRecoverAll cfg g s reads d a mds

/-! ## Runs -/

/-- One successful call (or a migration), with the caller the source permits. -/
inductive Op where
  /-- The vault's `_setNewTokenStorage(a, token, origin)` and the tracker registration it makes. -/
  | vaultRegister (a : AssetId) (origin : ChainId) (token : Address)
  /-- The upgrader's `updateL2`, writing the base token's registry entries. -/
  | vaultUpdateBase (origin : ChainId)
  /-- The upgrader's `registerBaseTokenIfNeeded`. -/
  | registerBaseIfNeeded
  /-- Anyone's `registerLegacyToken(a)`, with the token's reads at that moment. -/
  | registerLegacy (reads : TokenReads) (a : AssetId)
  /-- Any write of `assetHandlerAddress[a]`. -/
  | setHandler (a : AssetId) (handler : Address)
  /-- The chain's settlement layer becomes `c`. -/
  | setSettlementLayer (c : ChainId)
  /-- The runtime sets the holder's balance. -/
  | holderVm (balance : ℕ)
  /-- The router's `bridgeBurn` of `x` of `a` toward `d`. -/
  | vaultBurn (reads : TokenReads) (d : ChainId) (a : AssetId) (x : UInt256)
  /-- The interop center's same-base-token value burn of `v` toward `d` (`IC:436-440`). -/
  | icBurnBase (reads : TokenReads) (d : ChainId) (v : UInt256)
  /-- The router's `bridgeMint` of `x` of `a` from `c`. -/
  | vaultMint (reads : TokenReads) (c : ChainId) (a : AssetId) (x : UInt256)
  /-- The interop handler's `give` of `x` from `c`. -/
  | holderGive (reads : TokenReads) (c : ChainId) (x : UInt256)
  /-- The runtime's `handleFinalizeBaseTokenBridgingOnL2(c, x)` as `L2BaseToken`. -/
  | baseTokenFinalize (reads : TokenReads) (c : ChainId) (x : UInt256)
  /-- `claimRefund` of bundle `b`; the leg-state check is not modelled (see the header), so any
  bundle may be claimed. -/
  | claimRefund (reads : AssetId → TokenReads) (b : Bundle)

/-- The successor of one operation, or `none` if it reverts. -/
def exec (cfg : Config) (g : Guards) (sys : Sys) : Op → Option Sys
  | .vaultRegister a o tok => some (vaultSetNewTokenStorage cfg sys a o tok)
  | .vaultUpdateBase o =>
    some { sys with
      origin := Function.update sys.origin cfg.base o
      token := Function.update sys.token cfg.base cfg.baseTokenAddr }
  | .registerBaseIfNeeded =>
    some { sys with trk := registerNewToken cfg sys.trk cfg.base (sys.origin cfg.base) }
  | .registerLegacy reads a =>
    if sys.trk.isAssetRegistered a = true then some sys
    else if sys.token a = 0 then none
    else (registerLegacyInner cfg sys reads sys.trk a (sys.token a)).map fun t => { sys with trk := t }
  | .setHandler a h => some { sys with handler := Function.update sys.handler a h }
  | .setSettlementLayer c => some { sys with sl := c }
  | .holderVm h => some { sys with holder := h }
  | .vaultBurn reads d a x =>
    (vaultBurn cfg sys reads d a x).map fun s => s.record (.burned a d x sys.sl)
  | .icBurnBase reads d v =>
    if v = 0 then none
    else (holderBurn cfg sys reads d v).map fun s => s.record (.burned cfg.base d v sys.sl)
  | .vaultMint reads c a x => vaultMint cfg sys reads c a x
  | .holderGive reads c x => holderGive cfg sys reads c x
  | .baseTokenFinalize reads c x =>
    (trackerFinalizeBase cfg sys reads c x).map fun t => { sys with trk := t }
  | .claimRefund reads b => recoverBundle cfg g sys reads b

/-- A sequence of operations, all successful. -/
def run (cfg : Config) (g : Guards) : Sys → List Op → Option Sys
  | sys, [] => some sys
  | sys, op :: ops => (exec cfg g sys op).bind fun s => run cfg g s ops

/-- One item of a recovery schedule: a vault recovery of the scheduled asset, or any other
operation. -/
inductive SchedItem where
  | recover (md : MintData)
  | other (op : Op)

/-- Vault recoveries of asset `a` toward `d` interleaved with other operations, all successful.  The
calls of one claim are recovered in order, and a refund's release can run code between them
(the header's abstractions); a schedule also covers recoveries spread over several claims. -/
def runSchedule (cfg : Config) (g : Guards) (reads : AssetId → TokenReads) (d : ChainId)
    (a : AssetId) : Sys → List SchedItem → Option Sys
  | sys, [] => some sys
  | sys, .recover md :: items =>
    (vaultRecover cfg g sys reads d a (some md)).bind fun s => runSchedule cfg g reads d a s items
  | sys, .other op :: items =>
    (exec cfg g sys op).bind fun s => runSchedule cfg g reads d a s items

/-- The mint data of a schedule's recoveries, in order. -/
def scheduleRecoveries : List SchedItem → List MintData
  | [] => []
  | .recover md :: items => md :: scheduleRecoveries items
  | .other _ :: items => scheduleRecoveries items

/-- One item of a run in which other steps can fall between the calls of a claim, as the code that a
refund's release reaches can make them (the header's abstractions): an operation, or one call of a
claimed bundle's loop (`AFM:303-323`), after the flow manager's check of that bundle (`AFM:299`). -/
inductive NestedItem where
  | op (op : Op)
  | call (reads : AssetId → TokenReads) (b : Bundle) (c : Call)

/-- The successor of one item, or `none` if it reverts. -/
def execNested (cfg : Config) (g : Guards) (sys : Sys) : NestedItem → Option Sys
  | .op op => exec cfg g sys op
  | .call reads b c =>
    if g.managerL1 = true ∧ b.dest = cfg.l1 then none
    else recoverCall cfg g reads b.dest b.destBase sys c

/-- A sequence of items, all successful.  The calls of different claims may interleave in any order,
which covers a claim made by code that another claim's release reaches. -/
def runNested (cfg : Config) (g : Guards) : Sys → List NestedItem → Option Sys
  | sys, [] => some sys
  | sys, it :: its => (execNested cfg g sys it).bind fun s => runNested cfg g s its

/-- An operation as items: a claim becomes one item per call of its bundle, in order. -/
def NestedItem.ofOp : Op → List NestedItem
  | .claimRefund reads b => b.calls.map (NestedItem.call reads b)
  | o => [.op o]

/-! ## Vocabulary for the statements -/

/-- Two trackers agree on every entry indexed by asset `a`. -/
def Tracker.AgreeAt (t t' : Tracker) (a : AssetId) : Prop :=
  (∀ c, t.chainBalance c a = t'.chainBalance c a) ∧
    t.isAssetRegistered a = t'.isAssetRegistered a ∧ t.interopInfo a = t'.interopInfo a ∧
    t.totalPreV31TotalSupply a = t'.totalPreV31TotalSupply a

/-- Two states agree on everything about asset `a`: its tracker entries, its registry entries, its
handler, and, for the base asset, the holder's balance. -/
def Sys.AgreeAt (cfg : Config) (s s' : Sys) (a : AssetId) : Prop :=
  s.trk.AgreeAt s'.trk a ∧ s.origin a = s'.origin a ∧ s.token a = s'.token a ∧
    s.handler a = s'.handler a ∧ (a = cfg.base → s.holder = s'.holder)

/-- The asset a bundle call's data names, if any. -/
def CallData.asset? : CallData → Option AssetId
  | .finalizeDeposit a _ => some a
  | _ => none

/-- A bundle recovery can reach asset `a`: a router call naming `a`, or a valued call when the bundle's
destination base token is `a`. -/
def Bundle.Touches (cfg : Config) (b : Bundle) (a : AssetId) : Prop :=
  ∃ c ∈ b.calls, (c.sender = cfg.router ∧ c.data.asset? = some a) ∨
    (c.sender ≠ cfg.router ∧ c.value ≠ 0 ∧ b.destBase = a)

/-- The operation is a step on asset `a`: its asset argument is `a`, or `a` is the base asset and the
operation acts on the base asset or the holder. -/
def Op.Touches (cfg : Config) : Op → AssetId → Prop
  | .vaultRegister a' _ _, a => a' = a
  | .vaultUpdateBase _, a => a = cfg.base
  | .registerBaseIfNeeded, a => a = cfg.base
  | .registerLegacy _ a', a => a' = a
  | .setHandler a' _, a => a' = a
  | .setSettlementLayer _, _ => False
  | .holderVm _, a => a = cfg.base
  | .vaultBurn _ _ a' _, a => a' = a
  | .icBurnBase _ _ _, a => a = cfg.base
  | .vaultMint _ _ a' _, a => a' = a
  | .holderGive _ _ _, a => a = cfg.base
  | .baseTokenFinalize _ _ _, a => a = cfg.base
  | .claimRefund _ b, a => b.Touches cfg a

/-- The nested item is a step on asset `a`: an operation that is (`Op.Touches`), or a call of a claim
that reaches the vault for `a` (a router call naming `a`, or a valued call of a bundle whose
destination base token is `a`). -/
def NestedItem.Touches (cfg : Config) : NestedItem → AssetId → Prop
  | .op o, a => o.Touches cfg a
  | .call _ b c, a => (c.sender = cfg.router ∧ c.data.asset? = some a) ∨
      (c.sender ≠ cfg.router ∧ c.value ≠ 0 ∧ b.destBase = a)

/-- The nested item is a bridge-out of `a` toward a chain other than L1 (the vault's, or for the base
asset the interop center's value burn), or a call of a claim. -/
def NestedItem.IsFlowOf (cfg : Config) (a : AssetId) : NestedItem → Prop
  | .op (.vaultBurn _ d a' _) => a' = a ∧ d ≠ cfg.l1
  | .op (.icBurnBase _ d _) => a = cfg.base ∧ d ≠ cfg.l1
  | .call _ _ _ => True
  | .op _ => False

/-- The nested item is a router call naming `a`. -/
def NestedItem.IsRouterCallOn (cfg : Config) (a : AssetId) : NestedItem → Prop
  | .call _ _ c => c.sender = cfg.router ∧ c.data.asset? = some a
  | .op _ => False

/-- The amount of `a` a nested item bridges out. -/
def NestedItem.burnedOf (cfg : Config) (a : AssetId) : NestedItem → ℕ
  | .op (.vaultBurn _ _ a' x) => if a' = a then x.val else 0
  | .op (.icBurnBase _ _ v) => if a = cfg.base then v.val else 0
  | _ => 0

/-- The amount of `a` a call of a claim asks the vault to recover: the mint data's amount of a router
call `finalizeDeposit(a, md)`, or the value of a valued call of a bundle whose destination base token
is `a` (`L2AR:326`). -/
def NestedItem.recoveredOf (cfg : Config) (a : AssetId) : NestedItem → ℕ
  | .call _ b c =>
    if c.sender = cfg.router then
      match c.data with
      | .finalizeDeposit a' (some md) => if a' = a then md.amount.val else 0
      | _ => 0
    else if c.value ≠ 0 ∧ b.destBase = a then c.value.val else 0
  | .op _ => 0

/-- The total of the logged bridge-outs of `a` toward L1 made while the chain settled on L1. -/
def l1BurnTotal (cfg : Config) (a : AssetId) : List Event → ℕ
  | [] => 0
  | .burned a' d x s :: es =>
    (if a' = a ∧ d = cfg.l1 ∧ s = cfg.l1 then x.val else 0) + l1BurnTotal cfg a es
  | .recovered _ _ _ :: es => l1BurnTotal cfg a es

/-- Every recovery check removed; the countermodels switch single checks back on from here. -/
def Guards.none : Guards := ⟨false, false, false, false, false, false⟩

end Contracts.L2AssetTracker.RecoveryNeutrality
