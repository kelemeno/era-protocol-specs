import EraSpec.Contracts.BridgedStandardERC20.Specs.Model

/-!
# Model: `L2AssetTracker` — chain balances, registration and the two flow hooks

Source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`, cited as `TRK` for
`l1-contracts/contracts/bridge/asset-tracker/L2AssetTracker.sol`, `ITRK` for
`bridge/asset-tracker/IL2AssetTracker.sol`, `L2NTV` for `bridge/ntv/L2NativeTokenVault.sol`
and `BTH` for `l2-system/BaseTokenHolder.sol`.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.L2AssetTracker.Properties.Accounting` and proved in
`EraSpec.Contracts.L2AssetTracker.Proofs.Accounting`.

## What the tracker stores (`TRK:44-80`)

* `chainBalance[chainId][assetId]` (`TRK:44`), written only at `block.chainid`;
* `isAssetRegistered[assetId]` (`TRK:56`);
* `L1_CHAIN_ID`, `BASE_TOKEN_ASSET_ID` (`TRK:58-60`), set once by `initL2` (`TRK:146-154`);
* `interopInfo[assetId] = (totalWithdrawalsToL1, totalSuccessfulDepositsFromL1)` (`TRK:63`,
  `ITRK:16-24`);
* `totalPreV31TotalSupply[assetId] = (isSaved, amount)` (`TRK:74`, `ITRK:10-13`);
* `needBaseTokenTotalSupplyBackfill` (`TRK:80`);
* the `ReentrancyGuard` lock slot, which `reentrancyGuardInitializer` requires to be zero and
  sets (`common/ReentrancyGuard.sol:43-63`), so `initL2` runs at most once.  The inherited
  `Ownable2Step`/`Pausable` slots are unused on L2 (`TRK:32-35`) and not modelled.

## What the tracker reads from elsewhere (`Config`, `TokenReads`, the settlement layer)

* `block.chainid`, and the native token vault's `originChainId(assetId)` and
  `tokenAddress(assetId)` (`TRK:311`, `:399`).  They are fixed for a run (`Config`): the vault
  writes each asset's entries once, when it registers the asset, and the tracker cannot act on
  an asset before that (`_tryGetTokenAddress` and `_registerLegacyToken` revert on a zero
  entry).  `L2NativeTokenVault.updateL2` can rewrite the base token's entries
  (`L2NTV:170-172`); that upgrade path is outside the model (`OPS-CONFIG`).
* `L2_SYSTEM_CONTEXT_SYSTEM_CONTRACT.currentSettlementLayerChainId()` (`TRK:246`, `:301`): it
  changes when the chain migrates, so it is an argument of every flow, and a run can change it.
* `IERC20(token).balanceOf(L2_NATIVE_TOKEN_VAULT_ADDR)` and `IERC20(token).totalSupply()`
  (`TRK:327`, `:336`), read only by the first-touch legacy registration: `TokenReads`, the
  token's state at the moment of the call.  A read through the zero address fails (it has no
  code, and the returned `uint256` cannot be decoded; `VM-CALL`/`SOL-ABI`).

## Checked arithmetic (`SOL-ARITH`)

Solidity 0.8 reverts on uint256 overflow and underflow.  `chainBalance += amount` (`TRK:296`)
and the two counter increments (`TRK:248`, `:303`) are `checkedAdd`; `_decreaseChainBalance`
(`TRK:388-393`) checks and then subtracts, which is `checkedSub`.  Every stored value is a
`UInt256`, so nothing here wraps.

## The flows

`handleInitiateBridgingOnL2` (`TRK:221-250`) and `handleFinalizeBridgingOnL2` (`TRK:269-305`)
are called only by the vault (`onlyL2NativeTokenVault`, `TRK:89-94`), from its two hooks:
`_handleBridgeToChain(_chainid, _assetId, _amount)` passes `originChainId[_assetId]`
(`L2NTV:296-302`); `_handleBridgeFromChain` passes `originChainId[_assetId]` and
`tokenAddress[_assetId]` (`L2NTV:304-315`).  The base-token entry points are called by the
`BaseTokenHolder` (`BTH:99-118`) and by `L2BaseToken` (`l2-system/era/L2BaseTokenEra.sol:92`):
`handleInitiateBaseTokenBridgingOnL2` reads the vault's origin chain for the base token
(`TRK:256-260`), while `handleFinalizeBaseTokenBridgingOnL2` passes `_isNativeToThisChain: false`
whatever it is (`TRK:359-380`).

## Runs

`Step` is one successful call of any entry point by its permitted caller, or a change of the
settlement layer.  The vault's calls pass the vault's own stored entries (the two call sites
above); the upgrader's `initL2` passes `Config.initL1ChainId` and `Config.initBaseAssetId`
(`l2-upgrades/L2GenesisForceDeploymentsHelper.sol:418-423`).  Each step also writes a ghost
`Audit`: the amounts of all successful flows, per asset.  The audit is not tracker storage; it
exists so that the meaning of `chainBalance` can be stated.
-/

namespace Contracts.L2AssetTracker

/-- A 160-bit address, as in the token model. -/
abbrev Address := Contracts.BridgedStandardERC20.Address

/-- Asset ids and chain ids are 256-bit words. -/
abbrev AssetId := UInt256
abbrev ChainId := UInt256

/-! ## Checked uint256 arithmetic -/

/-- `MAX_TOKEN_BALANCE = type(uint256).max` (`ITRK:8`). -/
def MAX_TOKEN_BALANCE : UInt256 := ⟨UInt256.size - 1, by unfold UInt256.size; omega⟩

/-- Solidity 0.8 checked `a + b` on `uint256`: reverts on overflow. -/
def checkedAdd (a b : UInt256) : Option UInt256 :=
  if h : a.val + b.val < UInt256.size then some ⟨a.val + b.val, h⟩ else none

/-- `if (a < b) revert …; a -= b;` (`TRK:388-393`): reverts exactly when `a < b`. -/
def checkedSub (a b : UInt256) : Option UInt256 :=
  if h : b.val ≤ a.val then some ⟨a.val - b.val, by have := a.isLt; omega⟩ else none

/-- `MAX_TOKEN_BALANCE - x` (`TRK:328`), which never underflows. -/
def maxMinus (x : UInt256) : UInt256 := ⟨UInt256.size - 1 - x.val, by unfold UInt256.size; omega⟩

/-! ## Storage -/

/-- `SavedTotalSupply` (`ITRK:10-13`). -/
structure SavedTotalSupply where
  isSaved : Bool
  amount : UInt256
deriving DecidableEq

/-- `InteropL2Info` (`ITRK:16-24`). -/
structure InteropL2Info where
  /-- Amount withdrawn to L1 while the chain settled on L1. -/
  totalWithdrawalsToL1 : UInt256
  /-- Amount finalized from L1 while the chain settled on L1. -/
  totalSuccessfulDepositsFromL1 : UInt256
deriving DecidableEq

/-- The tracker's storage (`TRK:44-80`, plus the reentrancy-guard slot). -/
structure Storage where
  /-- `chainBalance[chainId][assetId]` (`TRK:44`). -/
  chainBalance : ChainId → AssetId → UInt256
  /-- `isAssetRegistered[assetId]` (`TRK:56`). -/
  isAssetRegistered : AssetId → Bool
  /-- `L1_CHAIN_ID` (`TRK:58`). -/
  l1ChainId : ChainId
  /-- `BASE_TOKEN_ASSET_ID` (`TRK:60`). -/
  baseTokenAssetId : AssetId
  /-- `interopInfo[assetId]` (`TRK:63`). -/
  interopInfo : AssetId → InteropL2Info
  /-- `totalPreV31TotalSupply[assetId]` (`TRK:74`). -/
  totalPreV31TotalSupply : AssetId → SavedTotalSupply
  /-- `needBaseTokenTotalSupplyBackfill` (`TRK:80`). -/
  needBaseTokenTotalSupplyBackfill : Bool
  /-- The reentrancy-guard lock slot is nonzero: `initL2` has run
  (`common/ReentrancyGuard.sol:43-63`). -/
  guardInitialized : Bool

/-- Freshly deployed storage: every slot zero. -/
def Storage.fresh : Storage :=
  ⟨fun _ _ => 0, fun _ => false, 0, 0, fun _ => ⟨0, 0⟩, fun _ => ⟨false, 0⟩, false, false⟩

/-- The fixed environment of a run: system addresses, this chain, the vault's two maps, and the
values the upgrader passes to `initL2`. -/
structure Config where
  /-- `L2_NATIVE_TOKEN_VAULT_ADDR`. -/
  ntv : Address
  /-- `L2_BASE_TOKEN_HOLDER_ADDR`. -/
  baseTokenHolder : Address
  /-- `address(L2_BASE_TOKEN_SYSTEM_CONTRACT)`. -/
  l2BaseToken : Address
  /-- `L2_COMPLEX_UPGRADER_ADDR`. -/
  upgrader : Address
  /-- `block.chainid`. -/
  thisChain : ChainId
  /-- `L2_NATIVE_TOKEN_VAULT.originChainId(assetId)`. -/
  ntvOriginChainId : AssetId → ChainId
  /-- `L2_NATIVE_TOKEN_VAULT.tokenAddress(assetId)`. -/
  ntvTokenAddress : AssetId → Address
  /-- The `_l1ChainId` the upgrader passes to `initL2`. -/
  initL1ChainId : ChainId
  /-- The `_baseTokenAssetId` the upgrader passes to `initL2`. -/
  initBaseAssetId : AssetId

/-- What the first-touch registration reads from the token (`TRK:327`, `:336`), at the moment
of the call. -/
structure TokenReads where
  /-- `IERC20(token).totalSupply()`. -/
  totalSupply : UInt256
  /-- `IERC20(token).balanceOf(L2_NATIVE_TOKEN_VAULT_ADDR)`. -/
  ntvBalance : UInt256

/-- The reads of a token in the token model's state: its supply and the vault's balance.  Exact
for a token whose supply is below `2^256` (`BridgedStandardERC20.WellFormed`). -/
def tokenReads (cfg : Config) (tok : Contracts.BridgedStandardERC20.State) : TokenReads :=
  ⟨(tok.totalSupply : UInt256), (tok.balances cfg.ntv : UInt256)⟩

/-- An asset is native here when the vault's origin chain for it is `block.chainid`. -/
def Native (cfg : Config) (a : AssetId) : Prop := cfg.ntvOriginChainId a = cfg.thisChain

instance (cfg : Config) (a : AssetId) : Decidable (Native cfg a) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Storage writes -/

/-- `chainBalance[c][a] = v`. -/
def setChainBalance (st : Storage) (c : ChainId) (a : AssetId) (v : UInt256) : Storage :=
  { st with chainBalance := Function.update st.chainBalance c (Function.update (st.chainBalance c) a v) }

/-- `isAssetRegistered[a] = true` and `totalPreV31TotalSupply[a] = snap`. -/
def markRegistered (st : Storage) (a : AssetId) (snap : SavedTotalSupply) : Storage :=
  { st with
    isAssetRegistered := Function.update st.isAssetRegistered a true
    totalPreV31TotalSupply := Function.update st.totalPreV31TotalSupply a snap }

/-- `interopInfo[a] = info`. -/
def setInterop (st : Storage) (a : AssetId) (info : InteropL2Info) : Storage :=
  { st with interopInfo := Function.update st.interopInfo a info }

/-! ## Internal functions -/

/-- `_registerLegacyToken(_assetId, _tokenAddress)` (`TRK:309-340`).  The origin chain must be
set in the vault (`:311-312`).  A native asset must have a zero chain balance (`:316-320`) and
gets `MAX_TOKEN_BALANCE - balanceOf(vault)` as chain balance and snapshot (`:327-331`); any other
asset gets its `totalSupply()` as snapshot (`:336-337`).  Both read the token, so a zero token
address fails. -/
def registerLegacyTokenInner (cfg : Config) (st : Storage) (reads : TokenReads) (a : AssetId)
    (token : Address) : Option Storage :=
  if cfg.ntvOriginChainId a = 0 then none
  else if token = 0 then none
  else if Native cfg a then
    if st.chainBalance cfg.thisChain a ≠ 0 then none
    else some (markRegistered (setChainBalance st cfg.thisChain a (maxMinus reads.ntvBalance)) a
      ⟨true, maxMinus reads.ntvBalance⟩)
  else some (markRegistered st a ⟨true, reads.totalSupply⟩)

/-- `_registerLegacyTokenIfNeeded` (`TRK:342-353`): nothing if the asset is registered. -/
def registerLegacyTokenIfNeeded (cfg : Config) (st : Storage) (reads : TokenReads) (a : AssetId)
    (token : Address) : Option Storage :=
  if st.isAssetRegistered a then some st else registerLegacyTokenInner cfg st reads a token

/-- `_decreaseChainBalance(c, a, amount)` (`TRK:388-393`). -/
def decreaseChainBalance (st : Storage) (c : ChainId) (a : AssetId) (amount : UInt256) :
    Option Storage :=
  (checkedSub (st.chainBalance c a) amount).map (setChainBalance st c a)

/-- `chainBalance[c][a] += amount` (`TRK:296`). -/
def increaseChainBalance (st : Storage) (c : ChainId) (a : AssetId) (amount : UInt256) :
    Option Storage :=
  (checkedAdd (st.chainBalance c a) amount).map (setChainBalance st c a)

/-- `interopInfo[a].totalWithdrawalsToL1 += amount` (`TRK:248`). -/
def addWithdrawalToL1 (st : Storage) (a : AssetId) (amount : UInt256) : Option Storage :=
  (checkedAdd (st.interopInfo a).totalWithdrawalsToL1 amount).map fun w =>
    setInterop st a { st.interopInfo a with totalWithdrawalsToL1 := w }

/-- `interopInfo[a].totalSuccessfulDepositsFromL1 += amount` (`TRK:303`). -/
def addDepositFromL1 (st : Storage) (a : AssetId) (amount : UInt256) : Option Storage :=
  (checkedAdd (st.interopInfo a).totalSuccessfulDepositsFromL1 amount).map fun d =>
    setInterop st a { st.interopInfo a with totalSuccessfulDepositsFromL1 := d }

/-- `_handleInitiateBridgingOnL2Inner(_toChainId, _assetId, _amount, _tokenOriginChainId)`
(`TRK:230-250`), in source order: `_tryGetTokenAddress` (`:236`, `:398-401`), first-touch
registration (`:237`), the native decrease (`:239-242`), and the withdrawal counter when the
destination and the current settlement layer are both L1 (`:244-249`). -/
def initiateInner (cfg : Config) (st : Storage) (sl : ChainId) (reads : TokenReads)
    (toChain : ChainId) (a : AssetId) (amount : UInt256) (tokenOrigin : ChainId) :
    Option Storage :=
  if cfg.ntvTokenAddress a = 0 then none
  else
    match registerLegacyTokenIfNeeded cfg st reads a (cfg.ntvTokenAddress a) with
    | none => none
    | some st₁ =>
      match (if tokenOrigin = cfg.thisChain then decreaseChainBalance st₁ cfg.thisChain a amount
          else some st₁) with
      | none => none
      | some st₂ =>
        if toChain = st.l1ChainId ∧ sl = st.l1ChainId then addWithdrawalToL1 st₂ a amount
        else some st₂

/-- `_handleFinalizeBridgingOnL2Inner(_fromChainId, _assetId, _amount, _isNativeToThisChain,
_tokenAddress)` (`TRK:285-305`): first-touch registration with the PASSED token address
(`:292`; no `_tryGetTokenAddress`), the native increase (`:295-297`), and the deposit counter
when the source and the current settlement layer are both L1 (`:299-304`). -/
def finalizeInner (cfg : Config) (st : Storage) (sl : ChainId) (reads : TokenReads)
    (fromChain : ChainId) (a : AssetId) (amount : UInt256) (isNative : Bool) (token : Address) :
    Option Storage :=
  match registerLegacyTokenIfNeeded cfg st reads a token with
  | none => none
  | some st₁ =>
    match (if isNative then increaseChainBalance st₁ cfg.thisChain a amount else some st₁) with
    | none => none
    | some st₂ =>
      if fromChain = st.l1ChainId ∧ sl = st.l1ChainId then addDepositFromL1 st₂ a amount
      else some st₂

/-! ## Entry points -/

/-- `registerNewTokenIfNeeded(_assetId, _originChainId)` (`TRK:157-175`), `onlyL2NativeTokenVault`.
Called from the vault's `_setNewTokenStorage` (`L2NTV:186-188`) and `registerBaseTokenIfNeeded`
(`L2NTV:127-133`).  Note that it uses its ARGUMENT, not the vault's stored origin chain.  The
native branch writes `chainBalance[_originChainId]` with `_originChainId == block.chainid`. -/
def registerNewTokenIfNeeded (cfg : Config) (st : Storage) (caller : Address) (a : AssetId)
    (origin : ChainId) : Option Storage :=
  if caller ≠ cfg.ntv then none
  else if st.isAssetRegistered a then some st
  else if origin = cfg.thisChain then
    some (markRegistered (setChainBalance st cfg.thisChain a MAX_TOKEN_BALANCE) a
      ⟨true, MAX_TOKEN_BALANCE⟩)
  else some (markRegistered st a ⟨true, 0⟩)

/-- `registerBaseTokenDuringUpgrade()` (`TRK:187-194`), `onlyUpgrader`: reverts if the base token
is registered; registers it with snapshot `0` and no chain balance. -/
def registerBaseTokenDuringUpgrade (cfg : Config) (st : Storage) (caller : Address) :
    Option Storage :=
  if caller ≠ cfg.upgrader then none
  else if st.isAssetRegistered st.baseTokenAssetId then none
  else some (markRegistered st st.baseTokenAssetId ⟨true, 0⟩)

/-- `registerLegacyToken(_assetId)` (`TRK:198-210`): anyone; nothing if registered. -/
def registerLegacyToken (cfg : Config) (st : Storage) (reads : TokenReads) (a : AssetId) :
    Option Storage :=
  if st.isAssetRegistered a then some st
  else if cfg.ntvTokenAddress a = 0 then none
  else registerLegacyTokenInner cfg st reads a (cfg.ntvTokenAddress a)

/-- `handleInitiateBridgingOnL2(_toChainId, _assetId, _amount, _tokenOriginChainId)`
(`TRK:221-228`), `onlyL2NativeTokenVault`. -/
def handleInitiateBridgingOnL2 (cfg : Config) (st : Storage) (sl : ChainId) (reads : TokenReads)
    (caller : Address) (toChain : ChainId) (a : AssetId) (amount : UInt256)
    (tokenOrigin : ChainId) : Option Storage :=
  if caller ≠ cfg.ntv then none else initiateInner cfg st sl reads toChain a amount tokenOrigin

/-- `handleInitiateBaseTokenBridgingOnL2(_toChainId, _amount)` (`TRK:256-260`),
`onlyBaseTokenHolder`: the base asset, with the vault's stored origin chain for it. -/
def handleInitiateBaseTokenBridgingOnL2 (cfg : Config) (st : Storage) (sl : ChainId)
    (reads : TokenReads) (caller : Address) (toChain : ChainId) (amount : UInt256) :
    Option Storage :=
  if caller ≠ cfg.baseTokenHolder then none
  else initiateInner cfg st sl reads toChain st.baseTokenAssetId amount
    (cfg.ntvOriginChainId st.baseTokenAssetId)

/-- `handleFinalizeBridgingOnL2(_fromChainId, _assetId, _amount, _tokenOriginChainId,
_tokenAddress)` (`TRK:269-283`), `onlyL2NativeTokenVault`. -/
def handleFinalizeBridgingOnL2 (cfg : Config) (st : Storage) (sl : ChainId) (reads : TokenReads)
    (caller : Address) (fromChain : ChainId) (a : AssetId) (amount : UInt256)
    (tokenOrigin : ChainId) (token : Address) : Option Storage :=
  if caller ≠ cfg.ntv then none
  else finalizeInner cfg st sl reads fromChain a amount (decide (tokenOrigin = cfg.thisChain)) token

/-- `handleFinalizeBaseTokenBridgingOnL2(_fromChainId, _amount)` (`TRK:359-380`),
`onlyBaseTokenHolderOrL2BaseToken`: nothing for a zero amount, a revert before `initL2`, and
otherwise the finalize path with `_isNativeToThisChain: false` HARD-CODED (`:377`). -/
def handleFinalizeBaseTokenBridgingOnL2 (cfg : Config) (st : Storage) (sl : ChainId)
    (reads : TokenReads) (caller : Address) (fromChain : ChainId) (amount : UInt256) :
    Option Storage :=
  if caller ≠ cfg.baseTokenHolder ∧ caller ≠ cfg.l2BaseToken then none
  else if amount = 0 then some st
  else if st.baseTokenAssetId = 0 then none
  else finalizeInner cfg st sl reads fromChain st.baseTokenAssetId amount false cfg.l2BaseToken

/-- `backFillZKSyncOSBaseTokenV31MigrationData(_amount)` (`TRK:120-140`), `onlyL2BaseToken`:
requires the flag, a registered base token with a saved zero snapshot; writes the snapshot's
amount and clears the flag. -/
def backFillZKSyncOSBaseTokenV31MigrationData (cfg : Config) (st : Storage) (caller : Address)
    (amount : UInt256) : Option Storage :=
  if caller ≠ cfg.l2BaseToken then none
  else if st.needBaseTokenTotalSupplyBackfill = false then none
  else if st.isAssetRegistered st.baseTokenAssetId = false then none
  else if (st.totalPreV31TotalSupply st.baseTokenAssetId).isSaved = false then none
  else if (st.totalPreV31TotalSupply st.baseTokenAssetId).amount ≠ 0 then none
  else some { st with
    totalPreV31TotalSupply := Function.update st.totalPreV31TotalSupply st.baseTokenAssetId
      ⟨true, amount⟩
    needBaseTokenTotalSupplyBackfill := false }

/-- `initL2(_l1ChainId, _baseTokenAssetId, _needBaseTokenTotalSupplyBackfill)` (`TRK:146-154`),
`reentrancyGuardInitializer onlyUpgrader`: at most once. -/
def initL2 (cfg : Config) (st : Storage) (caller : Address) (l1 : ChainId) (base : AssetId)
    (need : Bool) : Option Storage :=
  if st.guardInitialized then none
  else if caller ≠ cfg.upgrader then none
  else some { st with
    l1ChainId := l1, baseTokenAssetId := base, needBaseTokenTotalSupplyBackfill := need,
    guardInitialized := true }

/-! ## Runs -/

/-- The amounts of all successful flows, per asset.  Ghost state, not storage. -/
structure Audit where
  /-- Bridged out through `handleInitiateBridgingOnL2` or `handleInitiateBaseTokenBridgingOnL2`. -/
  outflow : AssetId → ℕ
  /-- Bridged in through `handleFinalizeBridgingOnL2` or `handleFinalizeBaseTokenBridgingOnL2`. -/
  inflow : AssetId → ℕ

/-- The empty audit. -/
def Audit.zero : Audit := ⟨fun _ => 0, fun _ => 0⟩

/-- `audit.outflow[a] += amount`. -/
def Audit.addOut (au : Audit) (a : AssetId) (amount : UInt256) : Audit :=
  { au with outflow := Function.update au.outflow a (au.outflow a + amount.val) }

/-- `audit.inflow[a] += amount`. -/
def Audit.addIn (au : Audit) (a : AssetId) (amount : UInt256) : Audit :=
  { au with inflow := Function.update au.inflow a (au.inflow a + amount.val) }

/-- The tracker in its environment: storage, the current settlement layer, and the audit. -/
structure Sys where
  st : Storage
  /-- `currentSettlementLayerChainId()`. -/
  sl : ChainId
  audit : Audit

/-- One call, with its caller and arguments as the source's callers supply them. -/
inductive Op where
  /-- The vault's `registerNewTokenIfNeeded(a, originChainId[a])` (`L2NTV:132`, `:187`). -/
  | registerNewToken (a : AssetId)
  /-- The upgrader's `registerBaseTokenDuringUpgrade()`. -/
  | registerBaseDuringUpgrade
  /-- Anyone's `registerLegacyToken(a)`, with the token's reads at that moment. -/
  | registerLegacy (reads : TokenReads) (a : AssetId)
  /-- The vault's `handleInitiateBridgingOnL2(toChain, a, amount, originChainId[a])`. -/
  | initiate (reads : TokenReads) (toChain : ChainId) (a : AssetId) (amount : UInt256)
  /-- The holder's `handleInitiateBaseTokenBridgingOnL2(toChain, amount)`. -/
  | initiateBase (reads : TokenReads) (toChain : ChainId) (amount : UInt256)
  /-- The vault's `handleFinalizeBridgingOnL2(fromChain, a, amount, originChainId[a],
  tokenAddress[a])`. -/
  | finalize (reads : TokenReads) (fromChain : ChainId) (a : AssetId) (amount : UInt256)
  /-- `handleFinalizeBaseTokenBridgingOnL2(fromChain, amount)` by the holder or the base token. -/
  | finalizeBase (reads : TokenReads) (caller : Address) (fromChain : ChainId) (amount : UInt256)
  /-- The base token's `backFillZKSyncOSBaseTokenV31MigrationData(amount)`. -/
  | backfill (amount : UInt256)
  /-- The upgrader's `initL2(initL1ChainId, initBaseAssetId, need)`. -/
  | initL2 (need : Bool)
  /-- The chain's settlement layer becomes `c` (migration; not a tracker call). -/
  | setSettlementLayer (c : ChainId)

/-- The successor of one operation, or `none` if the call reverts. -/
def exec (cfg : Config) (sys : Sys) : Op → Option Sys
  | .registerNewToken a =>
      (registerNewTokenIfNeeded cfg sys.st cfg.ntv a (cfg.ntvOriginChainId a)).map fun st =>
        { sys with st := st }
  | .registerBaseDuringUpgrade =>
      (registerBaseTokenDuringUpgrade cfg sys.st cfg.upgrader).map fun st => { sys with st := st }
  | .registerLegacy reads a =>
      (registerLegacyToken cfg sys.st reads a).map fun st => { sys with st := st }
  | .initiate reads toChain a amount =>
      (handleInitiateBridgingOnL2 cfg sys.st sys.sl reads cfg.ntv toChain a amount
          (cfg.ntvOriginChainId a)).map fun st =>
        { sys with st := st, audit := sys.audit.addOut a amount }
  | .initiateBase reads toChain amount =>
      (handleInitiateBaseTokenBridgingOnL2 cfg sys.st sys.sl reads cfg.baseTokenHolder toChain
          amount).map fun st =>
        { sys with st := st, audit := sys.audit.addOut sys.st.baseTokenAssetId amount }
  | .finalize reads fromChain a amount =>
      (handleFinalizeBridgingOnL2 cfg sys.st sys.sl reads cfg.ntv fromChain a amount
          (cfg.ntvOriginChainId a) (cfg.ntvTokenAddress a)).map fun st =>
        { sys with st := st, audit := sys.audit.addIn a amount }
  | .finalizeBase reads caller fromChain amount =>
      (handleFinalizeBaseTokenBridgingOnL2 cfg sys.st sys.sl reads caller fromChain amount).map
        fun st => { sys with st := st, audit := sys.audit.addIn sys.st.baseTokenAssetId amount }
  | .backfill amount =>
      (backFillZKSyncOSBaseTokenV31MigrationData cfg sys.st cfg.l2BaseToken amount).map fun st =>
        { sys with st := st }
  | .initL2 need =>
      (initL2 cfg sys.st cfg.upgrader cfg.initL1ChainId cfg.initBaseAssetId need).map fun st =>
        { sys with st := st }
  | .setSettlementLayer c => some { sys with sl := c }

/-- One successful operation. -/
def Step (cfg : Config) (sys sys' : Sys) : Prop := ∃ op, exec cfg sys op = some sys'

/-- Any number of successful operations. -/
abbrev Reach (cfg : Config) : Sys → Sys → Prop := Relation.ReflTransGen (Step cfg)

/-- A freshly deployed tracker, with an empty audit, on settlement layer `sl`. -/
def Sys.fresh (sl : ChainId) : Sys := ⟨Storage.fresh, sl, Audit.zero⟩

/-! ## The invariant of the chain balance -/

/-- **WHAT `chainBalance` MEANS.**  For every registered native asset, the chain balance plus
everything bridged out equals the registration snapshot plus everything bridged in:
`chainBalance = totalPreV31TotalSupply.amount - (Σout - Σin)`.  The snapshot is
`MAX_TOKEN_BALANCE` for an asset registered as new (`TRK:164-167`) and
`MAX_TOKEN_BALANCE - balanceOf(vault)` for a legacy one (`TRK:327-331`), so
`chainBalance = MAX - (E + Σout - Σin)` with `E` the vault's balance at registration. -/
def ChainBalanceSentinel (cfg : Config) (sys : Sys) (a : AssetId) : Prop :=
  (sys.st.chainBalance cfg.thisChain a).val + sys.audit.outflow a =
    (sys.st.totalPreV31TotalSupply a).amount.val + sys.audit.inflow a

/-- The configuration premise that the base token is not native to this chain: true of the
base asset the upgrader installs and of the one installed now.  UPG makes it a check for
recovery (`BaseTokenNativeToThisChain`, `UPG/bridge/asset-tracker/L2AssetTracker.sol:182-184`). -/
def BaseNotSelfNative (cfg : Config) (sys : Sys) : Prop :=
  ¬ Native cfg cfg.initBaseAssetId ∧ ¬ Native cfg sys.st.baseTokenAssetId

/-- The inductive invariant of a run.
* An unregistered asset has no recorded flows and a zero chain balance here.
* A registered native asset satisfies `ChainBalanceSentinel`, and its snapshot is saved.
* `initL2` has not run only while the backfill flag is clear (fresh storage).
* The base token is not native here. -/
structure Inv (cfg : Config) (sys : Sys) : Prop where
  unregisteredQuiet : ∀ a, sys.st.isAssetRegistered a = false →
    sys.audit.outflow a = 0 ∧ sys.audit.inflow a = 0 ∧ sys.st.chainBalance cfg.thisChain a = 0
  sentinel : ∀ a, sys.st.isAssetRegistered a = true → Native cfg a →
    ChainBalanceSentinel cfg sys a ∧ (sys.st.totalPreV31TotalSupply a).isSaved = true
  backfillNeedsInit : sys.st.guardInitialized = false →
    sys.st.needBaseTokenTotalSupplyBackfill = false
  baseNotNative : BaseNotSelfNative cfg sys

end Contracts.L2AssetTracker
