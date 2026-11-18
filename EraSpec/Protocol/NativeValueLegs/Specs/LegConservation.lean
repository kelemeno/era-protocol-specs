import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model at head: a native-value atomic leg, collected at send and refunded on timeout

Source: era-contracts `draft/v0.35.0` at `b17415d20` ("EVM-1830 feat(v35): CTMUpgrade_v35 splits a
shared CTM-domain ProxyAdmin (#2673)"); paths are relative to `l1-contracts/contracts/`.  The
functions modelled here have the same logic at `main` `70096e2ea`, up to line numbers, comments and
renames of internal getters (`_getNativeTokenVaultAddr` → `_nativeTokenVaultAddr` and the like).
`main` also puts `whenNotPaused` on the center's two send entry points and has neither the
fee-units counter nor the peer-allowed checks; the model reads none of these.

**This file is definitions only.**  The statements are in
`EraSpec.Protocol.NativeValueLegs.Properties.LegConservation` and are proved in
`EraSpec.Protocol.NativeValueLegs.Proofs.LegConservation`.

## What changed at head

At the round-5 pin `c67894b9`, `InteropCenter._validateAtomicBundle` rejected every atomic call that
carried native `value`, so an atomic leg burned no base token (`Contracts.InteropCenter`
`AtomicDispatchBurnsNothing`, a pin result).  At head that check is gone: every L2→L2 send is
atomic (`InteropCenter.sol:552-556`) and a *direct* call may carry `interopCallValue`.  Its value is
collected from the sender at send time and returned by the timeout refund.  This file models that
round trip on the source chain.

## Send: the bundle's calls (`InteropCenter.sol:621-687, :776-832`)

    // _buildInteropBundle, per call starter (:645-686)
    if (indirectCall) {
        require(to == L2_ASSET_ROUTER_ADDR, IndirectCallOnlyToAssetRouter(to));          // :665-668
        require(interopCallValue == 0, IndirectCallCannotCarryValue(interopCallValue)); // :674-677
    }
    InteropCall memory interopCall = _processCallStarter(_callStarters[i], d);           // :679
    totalBurnedCallsValue += interopCallValue;                                          // :681

    // _processCallStarter (:776-832)
    indirect: IL2CrossChainSender(to).initiateIndirectCall{value: ...}(d, msg.sender, value, data)
              -> InteropCall({to: returned recipient, data: returned data,
                              value: interopCallValue, from: to})                         // :814-821
    direct:   InteropCall({to: to, data: data, value: interopCallValue, from: msg.sender}) // :823-830

An indirect starter's target is the router (the first check), and the router's
`initiateIndirectCall` (`bridge/asset-router/L2AssetRouter.sol:331-361`) returns the
`finalizeDeposit(block.chainid, assetId, bridgeMintData)` calldata of `getDepositCalldata`
(`AssetRouterBase.sol:365-371`), after `_bridgehubDepositNonBaseTokenAsset` rejected
`assetId == baseTokenAssetId(d)` (`AssetRouterBase.sol:150`).  `baseTokenAssetId(d)` is the
`L2_BRIDGEHUB` entry the center read earlier in the same transaction for the bundle's
`destinationBaseTokenAssetId` (`InteropCenter.sol:629-631, :696-704`); the model takes the two reads
to agree (nothing on the send path writes that entry).  `FormsCall` records exactly this; the
bridge-mint bytes and the returned recipient stay free.

## Send: the collection (`InteropCenter.sol:418-460`)

    bytes32 thisChainBaseTokenAssetId = IL2NativeTokenVault(L2_NATIVE_TOKEN_VAULT).BASE_TOKEN_ASSET_ID(); // :426
    if (_destinationBaseTokenAssetId == thisChainBaseTokenAssetId) {
        require(msg.value == totalBurned + totalIndirect + protocolFee);                  // :433-434
        if (totalBurned > 0) L2_BASE_TOKEN_HOLDER.burnAndStartBridging{value: totalBurned}(d); // :436-440
    } else {
        require(msg.value == totalIndirect + protocolFee);                                // :442-443
        if (totalBurned > 0)
            IAssetRouterShared(L2_ASSET_ROUTER_ADDR).bridgehubDepositBaseToken(d, A, msg.sender, totalBurned); // :445-452
    }

The same-base branch sends `totalBurned` of the sender's `msg.value` on to `BaseTokenHolder`
(`l2-system/BaseTokenHolder.sol:93-96`), which notifies the tracker
(`bridge/asset-tracker/L2AssetTracker.sol:169-173`).  The different-base branch asks the router,
which burns through the handler registered for `A` (`AssetRouterBase.sol:97-116`):

    address assetHandler = assetHandlerAddress[_assetId];                                // :103
    require(assetHandler != address(0), AssetHandlerDoesNotExist(_assetId));            // :104
    IAssetHandler(assetHandler).bridgeBurn{value: msg.value}(_chainId, 0, _assetId,
        _originalCaller, DataEncoding.encodeBridgeBurnData(_amount, address(0), address(0))); // :107-113

For the vault this is `NativeTokenVaultBase.bridgeBurn` (`bridge/ntv/NativeTokenVaultBase.sol:294-318`):
resolve the token from `tokenAddress[A]` and check the reverse map (`:337-354`), then
`_bridgeBurnToken` (`:361-410`) and `_getTokenAndBridgeToChain` (`:425-457`): the tracker's
`handleInitiateBridgingOnL2` (`L2NativeTokenVault.sol:279-283`), then a burn from the sender
(`BridgedStandardERC20.bridgeBurn`, `bridge/BridgedStandardERC20.sol:164-167`) for a bridged token
or `_depositFunds` into the vault's escrow (`:468-475`) for a token native to this chain.

## Refund (`atomic-interop/AtomicFlowManager.sol:250-265, :292-325`)

    require(destChainId != L1_CHAIN_ID, RecoverToL1NotSupported());                        // :299
    for (uint256 i = 0; i < callsLen; ++i) {
        InteropCall memory c = _bundle.calls[i];
        if (c.from == L2_ASSET_ROUTER_ADDR) IAtomicRecoverable(c.from).recoverAtomicCall(destChainId, c.data); // :312-315
        if (c.from != L2_ASSET_ROUTER_ADDR && c.value != 0)
            IAssetRouterShared(L2_ASSET_ROUTER_ADDR).bridgehubRecoverBaseToken(
                destChainId, destBaseTokenAssetId, c.from, c.value);                       // :316-323
    }

`bridgehubRecoverBaseToken` (`L2AssetRouter.sol:314-328`) rejects an L1 destination (`:320`), builds
`encodeBridgeMintData(_receiver, _receiver, address(0), _amount, "")` (`:326`) and calls the vault's
`bridgeRecoverFailedTransfer` (`:327`; `NativeTokenVaultBase.sol:195-214`), which runs the L2
override of `_disburseFailedTransfer` (`L2NativeTokenVault.sol:204-227`): the tracker's view check
`assertRecoveryIsAccountingNeutral` (`L2AssetTracker.sol:176-185`); for the base token,
`BaseTokenHolder.recoverBaseToken` (`BaseTokenHolder.sol:79-87`), which checks the tracker again and
sends native value with `Address.sendValue`; otherwise the base body
(`NativeTokenVaultBase.sol:264-286`): the tracker's `handleFinalizeBridgingOnL2`
(`L2NativeTokenVault.sol:285-293`, `L2AssetTracker.sol:193-229`), then `_withdrawFunds` from the
escrow (`L2NativeTokenVault.sol:196-199`) for a native token, or `bridgeMint` on the registered
token (`BridgedStandardERC20.sol:158-161`).  `vaultRefund` below models these branches, each with
its source line.

## What is modelled

* **One source chain.**  `Config` fixes `block.chainid`, the L1 chain id, the system addresses, the
  vault's `BASE_TOKEN_ASSET_ID` and its registry (`tokenAddress`, `assetId`, `originChainId`).
  The registry is configuration: apart from the upgrader's `updateL2`, which rewrites the base
  token's entries (`L2NativeTokenVault.sol:165-167`, `OPS-CONFIG`), an entry is written only by
  `_setNewTokenStorage` (`NativeTokenVaultBase.sol:565-575`), reached behind `assetId[token] == 0`
  or `tokenAddress[a] == 0`, so a registered asset's entry does not change (up to a keccak collision
  on asset ids); `BASE_TOKEN_ASSET_ID` is frozen once set (`L2NativeTokenVault.sol:150-155`).  The
  center, manager, router, vault and tracker each keep their own `L1_CHAIN_ID`, and the vault and
  tracker their own `BASE_TOKEN_ASSET_ID`; the model has one of each (`OPS-CONFIG`: all are set by
  the upgrader).
* **The world** `World` holds what the round trip reads or writes: native balances, the token
  ledger and supply of each asset (keyed by asset id: one local token per registered asset), the
  router's `assetHandlerAddress`, the vault's pause flag, and the tracker's `isAssetRegistered`,
  `chainBalance[block.chainid][·]`, `totalWithdrawalsToL1` and `totalSuccessfulDepositsFromL1`.
* **Amounts are naturals** (`SOL-ARITH`): the source sums `uint256` with checked arithmetic, so a
  successful send's total is a natural.  The checked overflows of `+=` are omitted (they only
  reject); underflows that the source checks are modelled as reverts.  A revert is `none`.
* **The collection is one component of the send.**  `collect` is the value movement of
  `_ensureCorrectTotalValue` only.  In the same-base branch the sender's `msg.value` enters the
  center at call entry and its `totalBurned` part leaves to the holder in the same transaction,
  so the component is a transfer from the sender to the holder.  The fee and the indirect calls'
  values are other components (fees are `N-6`).
* **Router-produced calls are recovered by abstract code** `Params.routerRecover`: the router's
  `recoverAtomicCall` (`L2AssetRouter.sol:269-303`) and whatever handler `assetHandlerAddress`
  names at claim time.  Results that need it to leave the leg's asset alone say so
  (`RecoveryFramesOthers`).  A handler other than the vault burns with arbitrary code
  `Params.customBurn`.
* **Omitted reject-only checks**: the router's `whenNotPaused` on indirect deposits
  (`AssetRouterBase.sol:124`), attribute parsing and the destination's registration and peer checks
  (`InteropCenter.sol:696-704`), the indirect `IndirectCallValueMismatch` and recipient checks, the
  vault's origin-token
  and metadata reads in `_bridgeBurnToken`, ERC20 allowances and zero-address checks, the
  `nonReentrant` guards.  Omitting a check that only rejects adds runs.  (At `b17415d20` the center's
  send entry points have no pause gate; the vault's, which is modelled, is the only pause on this
  path.)
* **Reentrancy.**  `Address.sendValue` runs the recipient's code.  The holder, vault and router
  write no state after that call (they emit events), and the router's `nonReentrant` lock is held,
  so a nested claim that reaches the router reverts.  A nested call that succeeds (a send, or a claim
  of a bundle with nothing to recover) is outside this model; its effects are those of a separate
  transaction.  Tokens are standard ERC20s with no callbacks (`MODEL-ESCROW`).
-/

namespace Contracts.NativeValueLegs

/-- Chain ids. -/
abbrev Chain := UInt256
/-- Asset ids (`bytes32`). -/
abbrev AssetId := UInt256
/-- Addresses, as 256-bit words. -/
abbrev Address := UInt256
/-- Other words: flow ids, bundle hashes, salts. -/
abbrev Word := UInt256
/-- Opaque bytes. -/
abbrev Bytes := List UInt8

/-- `MAX_TOKEN_BALANCE = type(uint256).max` (`common/Config.sol:79`). -/
def maxTokenBalance : ℕ := UInt256.size - 1

/-! ## Configuration of the source chain -/

/-- What is fixed on the source chain for the duration of the model. -/
structure Config where
  /-- `block.chainid`. -/
  thisChain : Chain
  /-- `L1_CHAIN_ID` of the center, manager, router, vault and tracker (`OPS-CONFIG`: one value). -/
  l1Chain : Chain
  /-- `L2_SYSTEM_CONTEXT_SYSTEM_CONTRACT.currentSettlementLayerChainId() == L1_CHAIN_ID`, read by the
  tracker's L1 counters (`L2AssetTracker.sol:160-165, :223-228`). -/
  slIsL1 : Bool
  /-- `L2_ASSET_ROUTER_ADDR`. -/
  router : Address
  /-- `L2_NATIVE_TOKEN_VAULT_ADDR`. -/
  ntv : Address
  /-- `L2_BASE_TOKEN_HOLDER_ADDR`. -/
  holder : Address
  /-- `BASE_TOKEN_ASSET_ID` of the vault and the tracker (`OPS-CONFIG`: one value). -/
  baseAsset : AssetId
  /-- The vault's `tokenAddress[assetId]`; `0` for an asset it never registered. -/
  tokenOf : AssetId → Address
  /-- The vault's `assetId[token]`. -/
  assetOf : Address → AssetId
  /-- The vault's `originChainId[assetId]`; `0` for an asset it never registered. -/
  originOf : AssetId → Chain
  /-- The vault's `WETH_TOKEN`. -/
  weth : Address
  /-- The account's code reverts when sent native value with no calldata, so `Address.sendValue`
  to it reverts. -/
  rejectsValue : Address → Bool

/-! ## Bundle calls and call starters -/

/-- The `data` of a bundle call, as far as recovery distinguishes it. -/
inductive CallData where
  /-- `finalizeDeposit(sourceChain, assetId, mint)`: what the router returns for an indirect call. -/
  | finalizeDeposit (sourceChain : Chain) (assetId : AssetId) (mint : Bytes)
  /-- Any other bytes. -/
  | other (raw : Bytes)
deriving DecidableEq

/-- `InteropCall` (`common/Messaging.sol:240-247`) without the constant `version` and the reserved
`shadowAccount`. -/
structure Call where
  /-- `to`. -/
  target : Address
  /-- `from`: the router for an indirect call, the sender for a direct call. -/
  fromAddr : Address
  /-- `value`: base token the destination releases with the call. -/
  value : ℕ
  /-- `data`. -/
  data : CallData
deriving DecidableEq

/-- `InteropBundle` (`common/Messaging.sol:268-276`) without the constant `version`. -/
structure Bundle where
  /-- `sourceChainId`. -/
  sourceChain : Chain
  /-- `destinationChainId`. -/
  destChain : Chain
  /-- `destinationBaseTokenAssetId`: the asset the value legs are collected and refunded in. -/
  destBaseAsset : AssetId
  /-- `interopBundleSalt`. -/
  salt : Word
  /-- `calls`, in order. -/
  calls : List Call
  /-- `bundleAttributes`, opaque. -/
  attributes : Bytes
deriving DecidableEq

/-- `InteropCallStarterInternal` (`common/Messaging.sol:199-203`) with its parsed `CallAttributes`
(`:210-214`). -/
structure Starter where
  /-- `to`: the recipient, or for an indirect call the contract asked for the actual call. -/
  target : Address
  /-- `data`. -/
  data : CallData
  /-- `interopCallValue`. -/
  interopCallValue : ℕ
  /-- `indirectCallMessageValue`. -/
  indirectCallMessageValue : ℕ
  /-- `indirectCall`. -/
  indirectCall : Bool
deriving DecidableEq

/-- The two send-time checks on indirect starters, as switches.  The deployed code has both. -/
structure Checks where
  /-- `IndirectCallOnlyToAssetRouter` (`InteropCenter.sol:665-668`). -/
  indirectOnlyToRouter : Bool
  /-- `IndirectCallCannotCarryValue` (`InteropCenter.sol:674-677`). -/
  indirectNoValue : Bool

/-- The deployed code. -/
def deployed : Checks := ⟨true, true⟩

/-- The deployed code without `IndirectCallCannotCarryValue`. -/
def withoutIndirectValueBan : Checks := ⟨true, false⟩

/-- Starter `s` passes the enabled indirect-starter checks (`InteropCenter.sol:659-678`). -/
def StarterPasses (K : Checks) (cfg : Config) (s : Starter) : Prop :=
  s.indirectCall = true →
    (K.indirectOnlyToRouter = true → s.target = cfg.router) ∧
    (K.indirectNoValue = true → s.interopCallValue = 0)

/-- `_processCallStarter(s, d)` by sender `u` may return `c`, in a bundle whose
`destinationBaseTokenAssetId` is `A` (`InteropCenter.sol:776-832`). -/
structure FormsCall (cfg : Config) (A : AssetId) (u : Address) (s : Starter) (c : Call) : Prop where
  /-- Both branches: `value: _callStarter.callAttributes.interopCallValue` (`:819, :828`). -/
  value : c.value = s.interopCallValue
  /-- Direct: the starter's recipient and data, `from: msg.sender` (`:823-830`). -/
  direct : s.indirectCall = false → c.target = s.target ∧ c.data = s.data ∧ c.fromAddr = u
  /-- Indirect: `from: recipientAddress`, the starter's target (`:820`). -/
  indirect : s.indirectCall = true → c.fromAddr = s.target
  /-- Indirect through the router: the data is `finalizeDeposit(block.chainid, assetId, ·)` for an
  asset other than `A` (`L2AssetRouter.sol:331-361`, `AssetRouterBase.sol:140-183, :365-371`). -/
  routerData : s.indirectCall = true → s.target = cfg.router →
    ∃ a m, c.data = .finalizeDeposit cfg.thisChain a m ∧ a ≠ A

/-- `totalBurnedCallsValue` (`InteropCenter.sol:681`): what the send collects for the bundle. -/
def collected (starters : List Starter) : ℕ :=
  (starters.map Starter.interopCallValue).sum

/-- The base-token refunds `_recoverBundle` requests, in order: `(c.from, c.value)` for every call
with `c.from != L2_ASSET_ROUTER_ADDR && c.value != 0` (`AtomicFlowManager.sol:316-323`). -/
def valueRefunds (cfg : Config) (calls : List Call) : List (Address × ℕ) :=
  (calls.filter fun c => decide (c.fromAddr ≠ cfg.router ∧ c.value ≠ 0)).map
    fun c => (c.fromAddr, c.value)

/-! ## The world -/

/-- What the round trip reads or writes on the source chain. -/
structure World where
  /-- Native base-token balances (account balances). -/
  native : Address → ℕ
  /-- `balanceOf` of the local token of each asset. -/
  bal : AssetId → Address → ℕ
  /-- `totalSupply` of the local token of each asset. -/
  supply : AssetId → ℕ
  /-- The router's `assetHandlerAddress` (`AssetRouterBase.sol:41`). -/
  handler : AssetId → Address
  /-- The vault's `paused()`. -/
  ntvPaused : Bool
  /-- The tracker's `isAssetRegistered` (`L2AssetTracker.sol:48`). -/
  registered : AssetId → Bool
  /-- The tracker's `chainBalance[block.chainid][·]` (`L2AssetTracker.sol:38`); the only key the L2
  tracker writes. -/
  chainBalance : AssetId → ℕ
  /-- The tracker's `interopInfo[·].totalWithdrawalsToL1` (`L2AssetTracker.sol:164`). -/
  toL1 : AssetId → ℕ
  /-- The tracker's `interopInfo[·].totalSuccessfulDepositsFromL1` (`L2AssetTracker.sol:227`). -/
  fromL1 : AssetId → ℕ

/-- Move `v` native value from `src` to `dst`: debit, then credit the debited map. -/
def moveNative (w : World) (src dst : Address) (v : ℕ) : World :=
  let n₁ := Function.update w.native src (w.native src - v)
  { w with native := Function.update n₁ dst (n₁ dst + v) }

/-- Move `v` of asset `a`'s token from `src` to `dst`: debit, then credit the debited map. -/
def moveToken (w : World) (a : AssetId) (src dst : Address) (v : ℕ) : World :=
  let b₁ := Function.update (w.bal a) src (w.bal a src - v)
  { w with bal := Function.update w.bal a (Function.update b₁ dst (b₁ dst + v)) }

/-- Burn `v` of asset `a`'s token from `src`. -/
def burnToken (w : World) (a : AssetId) (src : Address) (v : ℕ) : World :=
  { w with
    bal := Function.update w.bal a (Function.update (w.bal a) src (w.bal a src - v))
    supply := Function.update w.supply a (w.supply a - v) }

/-- Mint `v` of asset `a`'s token to `dst`. -/
def mintToken (w : World) (a : AssetId) (dst : Address) (v : ℕ) : World :=
  { w with
    bal := Function.update w.bal a (Function.update (w.bal a) dst (w.bal a dst + v))
    supply := Function.update w.supply a (w.supply a + v) }

/-! ## The tracker (`bridge/asset-tracker/L2AssetTracker.sol`) -/

/-- `IERC20(tokenAddress[a]).balanceOf(L2_NATIVE_TOKEN_VAULT_ADDR)`: native value for the base
token (its token is the base-token system contract), the token ledger otherwise. -/
def ntvHolding (cfg : Config) (w : World) (a : AssetId) : ℕ :=
  if a = cfg.baseAsset then w.native cfg.ntv else w.bal a cfg.ntv

/-- `_registerLegacyTokenIfNeeded(a, tokenAddress[a])` (`:264-274`, `_registerLegacyToken`
`:233-262`).  A native token's `chainBalance` starts at `MAX_TOKEN_BALANCE` minus the vault's
holding; a bridged token's supply snapshot (`:258-259`) is not modelled. -/
def registerIfNeeded (cfg : Config) (w : World) (a : AssetId) : Option World :=
  if w.registered a = true then some w
  -- `require(originChainId != 0, AssetIdNotRegistered(_assetId))` (:235-236)
  else if cfg.originOf a = 0 then none
  -- both branches call the token at `tokenAddress[a]` (`balanceOf` :249, `totalSupply` :258)
  else if cfg.tokenOf a = 0 then none
  else if cfg.originOf a = cfg.thisChain then
    -- `ChainBalanceMustBeZeroBeforeMigration` (:240-244)
    if w.chainBalance a ≠ 0 then none
    -- checked `MAX_TOKEN_BALANCE - ntvBalance` (:250)
    else if maxTokenBalance < ntvHolding cfg w a then none
    else some { w with
      registered := Function.update w.registered a true
      chainBalance := Function.update w.chainBalance a (maxTokenBalance - ntvHolding cfg w a) }
  else some { w with registered := Function.update w.registered a true }

/-- `_handleInitiateBridgingOnL2Inner(toChain, a, amount, originChainId[a])` (`:146-166`), reached
through `handleInitiateBridgingOnL2` (`:137-144`) or `handleInitiateBaseTokenBridgingOnL2`
(`:169-173`). -/
def trackerInitiate (cfg : Config) (w : World) (toChain : Chain) (a : AssetId) (amount : ℕ) :
    Option World :=
  -- `_tryGetTokenAddress` (:152, :317-320)
  if cfg.tokenOf a = 0 then none else
  (registerIfNeeded cfg w a).bind fun w₁ =>
  -- `_decreaseChainBalance(block.chainid, a, amount)` for a native token (:155-158, :306-311)
  (if cfg.originOf a = cfg.thisChain then
      (if w₁.chainBalance a < amount then none
       else some { w₁ with chainBalance := Function.update w₁.chainBalance a (w₁.chainBalance a - amount) })
    else some w₁).map fun w₂ =>
  -- `totalWithdrawalsToL1 += amount` (:160-165)
  if toChain = cfg.l1Chain ∧ cfg.slIsL1 = true then
    { w₂ with toL1 := Function.update w₂.toL1 a (w₂.toL1 a + amount) }
  else w₂

/-- `handleFinalizeBridgingOnL2(fromChain, a, amount, originChainId[a], tokenAddress[a])`
(`:193-229`). -/
def trackerFinalize (cfg : Config) (w : World) (fromChain : Chain) (a : AssetId) (amount : ℕ) :
    Option World :=
  (registerIfNeeded cfg w a).map fun w₁ =>
  -- `chainBalance[block.chainid][a] += amount` for a native token (:218-221)
  let w₂ := if cfg.originOf a = cfg.thisChain then
      { w₁ with chainBalance := Function.update w₁.chainBalance a (w₁.chainBalance a + amount) }
    else w₁
  -- `totalSuccessfulDepositsFromL1 += amount` (:223-228)
  if fromChain = cfg.l1Chain ∧ cfg.slIsL1 = true then
    { w₂ with fromL1 := Function.update w₂.fromL1 a (w₂.fromL1 a + amount) }
  else w₂

/-- `assertRecoveryIsAccountingNeutral(a, toChain)` does not revert (`:176-185`): the destination
is not L1, and the base token does not originate here. -/
def RecoveryNeutral (cfg : Config) (a : AssetId) (toChain : Chain) : Prop :=
  toChain ≠ cfg.l1Chain ∧ (a = cfg.baseAsset → cfg.originOf a ≠ cfg.thisChain)

instance (cfg : Config) (a : AssetId) (toChain : Chain) : Decidable (RecoveryNeutral cfg a toChain) := by
  unfold RecoveryNeutral; infer_instance

/-! ## The holder (`l2-system/BaseTokenHolder.sol`) -/

/-- `Address.sendValue(payable(dst), v)` from `src`: reverts on a short balance or a rejecting
recipient. -/
def sendValue (cfg : Config) (w : World) (src dst : Address) (v : ℕ) : Option World :=
  if w.native src < v then none
  else if cfg.rejectsValue dst = true then none
  else some (moveNative w src dst v)

/-- `recoverBaseToken(dst, v, toChain)` called by the vault (`:79-87`). -/
def holderRecover (cfg : Config) (w : World) (dst : Address) (v : ℕ) (toChain : Chain) :
    Option World :=
  if v = 0 then some w
  -- `assertBaseTokenRecoveryIsAccountingNeutral(toChain)` (:84; `L2AssetTracker.sol:188-190`)
  else if ¬ RecoveryNeutral cfg cfg.baseAsset toChain then none
  else sendValue cfg w cfg.holder dst v

/-- `burnAndStartBridging{value: v}(toChain)` called by the center with `v` of sender `u`'s
`msg.value` (`:93-96`): the value moves from `u` to the holder, then the tracker's
`handleInitiateBaseTokenBridgingOnL2(toChain, v)` (`L2AssetTracker.sol:169-173`). -/
def holderBurn (cfg : Config) (w : World) (u : Address) (toChain : Chain) (v : ℕ) : Option World :=
  if w.native u < v then none
  else trackerInitiate cfg (moveNative w u cfg.holder v) toChain cfg.baseAsset v

/-! ## The vault (`bridge/ntv/NativeTokenVaultBase.sol`, `bridge/ntv/L2NativeTokenVault.sol`) -/

/-- `bridgeRecoverFailedTransfer(d, a, encodeBridgeMintData(u, u, address(0), v, ""))` called by
the router with no value (`NativeTokenVaultBase.sol:195-214`), with the L2 override of
`_disburseFailedTransfer` (`L2NativeTokenVault.sol:204-227`) and its base body (`:264-286`). -/
def vaultRefund (cfg : Config) (w : World) (d : Chain) (a : AssetId) (u : Address) (v : ℕ) :
    Option World :=
  -- `whenNotPaused` (:199)
  if w.ntvPaused = true then none
  -- `L2_ASSET_TRACKER.assertRecoveryIsAccountingNeutral(a, d)` (L2NativeTokenVault.sol:213)
  else if ¬ RecoveryNeutral cfg a d then none
  -- the base token: `L2_BASE_TOKEN_HOLDER.recoverBaseToken(u, v, d)` (L2NativeTokenVault.sol:214-216)
  else if a = cfg.baseAsset then holderRecover cfg w u v d
  -- `_handleBridgeFromChain(d, a, v)` (:276; L2NativeTokenVault.sol:285-293)
  else (trackerFinalize cfg w d a v).bind fun w₁ =>
    -- native: `_withdrawFunds(a, u, tokenAddress[a], v)` (:277-278; L2NativeTokenVault.sol:196-199),
    -- `IERC20(token).safeTransfer(u, v)`: with no token address the call has no code to run and
    -- OpenZeppelin v4.9.5 `SafeERC20` reverts (`Address.verifyCallResultFromTarget`)
    if cfg.originOf a = cfg.thisChain then
      (if cfg.tokenOf a = 0 then none
       else if w₁.bal a cfg.ntv < v then none else some (moveToken w₁ a cfg.ntv u v))
    -- bridged, no registered token: `_ensureAndSaveTokenDeployed` (:281-282) reverts
    else if cfg.tokenOf a = 0 then none
    -- bridged: `IBridgedStandardToken(token).bridgeMint(u, v)` (:284)
    else some (mintToken w₁ a u v)

/-- `bridgeBurn(d, 0, a, u, encodeBridgeBurnData(v, address(0), address(0)))` called by the router
with no value (`NativeTokenVaultBase.sol:294-318`). -/
def vaultBurn (cfg : Config) (w : World) (d : Chain) (a : AssetId) (u : Address) (v : ℕ) :
    Option World :=
  -- `whenNotPaused` (:306)
  if w.ntvPaused = true then none
  -- the token resolves to `tokenAddress[a]` and must be set (:343-350)
  else if cfg.tokenOf a = 0 then none
  -- `assetId[token] == a` (:352-353)
  else if cfg.assetOf (cfg.tokenOf a) ≠ a then none
  -- `AmountMustBeGreaterThanZero` (:370)
  else if v = 0 then none
  -- `BurningNativeWETHNotSupported` (:372-376)
  else if cfg.originOf a = cfg.thisChain ∧ cfg.tokenOf a = cfg.weth then none
  -- the base token needs `v == msg.value`, and `msg.value` is zero (:435-436)
  else if a = cfg.baseAsset then none
  -- `_handleBridgeToChain(d, a, v)` before any balance change (:447; L2NativeTokenVault.sol:279-283)
  else (trackerInitiate cfg w d a v).bind fun w₁ =>
    -- bridged: `IBridgedStandardToken(token).bridgeBurn(u, v)` (:449-450)
    if cfg.originOf a ≠ cfg.thisChain then
      (if w₁.bal a u < v then none else some (burnToken w₁ a u v))
    -- native: `_depositFunds(u, token, v)` must report `v` (:451-454, :468-475); from the vault
    -- itself it reports `0`
    else if u = cfg.ntv then none
    else if w₁.bal a u < v then none
    else some (moveToken w₁ a u cfg.ntv v)

/-! ## Abstract code and the router -/

/-- What the model leaves to other code. -/
structure Params where
  /-- The source chain's configuration. -/
  cfg : Config
  /-- `IAtomicRecoverable(L2_ASSET_ROUTER_ADDR).recoverAtomicCall(d, data)` called by the manager:
  the router's code (`L2AssetRouter.sol:269-303`) and the handler it reaches.  `none` reverts. -/
  routerRecover : World → Chain → CallData → Option World
  /-- `IAssetHandler(h).bridgeBurn{value: 0}(d, 0, a, u, encodeBridgeBurnData(v, 0, 0))` for a
  handler `h` other than the vault: arbitrary code.  `none` reverts. -/
  customBurn : Address → World → Chain → AssetId → Address → ℕ → Option World

/-- `L2AssetRouter.bridgehubRecoverBaseToken(d, a, receiver, v)` called by the manager
(`L2AssetRouter.sol:314-328`): no L1 destination (`:320`), then the vault's
`bridgeRecoverFailedTransfer` (`:327`). -/
def routerRecoverBase (cfg : Config) (w : World) (d : Chain) (a : AssetId) (receiver : Address)
    (v : ℕ) : Option World :=
  if d = cfg.l1Chain then none else vaultRefund cfg w d a receiver v

/-- `AssetRouterBase._bridgehubDepositBaseToken(d, a, u, v)` called through `bridgehubDepositBaseToken`
by the center with no value (`AssetRouterBase.sol:97-116`; `L2AssetRouter.sol:237-244`): the
handler registered for `a` burns. -/
def routerDepositBase (P : Params) (w : World) (d : Chain) (a : AssetId) (u : Address) (v : ℕ) :
    Option World :=
  if w.handler a = 0 then none
  else if w.handler a = P.cfg.ntv then vaultBurn P.cfg w d a u v
  else P.customBurn (w.handler a) w d a u v

/-! ## The collection and the refund -/

/-- The value movement of `_ensureCorrectTotalValue` (`InteropCenter.sol:432-453`) for sender `u`,
destination `d`, destination base-token asset `a` and `totalBurnedCallsValue = v`. -/
def collect (P : Params) (w : World) (u : Address) (d : Chain) (a : AssetId) (v : ℕ) :
    Option World :=
  if a = P.cfg.baseAsset then (if v = 0 then some w else holderBurn P.cfg w u d v)
  else if v = 0 then some w
  else routerDepositBase P w d a u v

/-- One iteration of `_recoverBundle`'s loop (`AtomicFlowManager.sol:302-324`).  The source's two
`if`s are exclusive. -/
def recoverCall (P : Params) (d : Chain) (a : AssetId) (w : World) (c : Call) : Option World :=
  if c.fromAddr = P.cfg.router then P.routerRecover w d c.data
  else if c.value ≠ 0 then routerRecoverBase P.cfg w d a c.fromAddr c.value
  else some w

/-- `_recoverBundle`'s loop: the calls in order, no `try`/`catch`. -/
def recoverBundle (P : Params) (d : Chain) (a : AssetId) : World → List Call → Option World
  | w, [] => some w
  | w, c :: cs => (recoverCall P d a w c).bind fun w' => recoverBundle P d a w' cs

/-- The world effect of `claimRefund` for decoded bundle `B` (`AtomicFlowManager.sol:250-265`):
`_recoverBundle` with its L1 check (`:299`).  The leg-state check and write are the caller's
(`LegConservationRuns`). -/
def claimRefund (P : Params) (w : World) (B : Bundle) : Option World :=
  if B.destChain = P.cfg.l1Chain then none
  else recoverBundle P B.destChain B.destBaseAsset w B.calls

/-! ## The leg's footprint -/

/-- The ledger a leg's value lives in: native balances for the source chain's base token, the
token ledger otherwise. -/
def ledger (cfg : Config) (A : AssetId) (w : World) : Address → ℕ :=
  if A = cfg.baseAsset then w.native else w.bal A

/-- Where collected value sits while the leg is in flight: the holder for the base token, the
vault's escrow for a token native to this chain, nowhere for a bridged token (it is burned). -/
def sink (cfg : Config) (A : AssetId) : Option Address :=
  if A = cfg.baseAsset then some cfg.holder
  else if cfg.originOf A = cfg.thisChain then some cfg.ntv
  else none

/-- The direction of a leg's refund for payer `u`: `+1` at `u`, `-1` at the sink. -/
def dir (cfg : Config) (A : AssetId) (u x : Address) : ℤ :=
  (if x = u then 1 else 0) - (if sink cfg A = some x then 1 else 0)

/-- The asset's token is burned on collection: not the base token, and not native here. -/
def BurnsSupply (cfg : Config) (A : AssetId) : Prop :=
  A ≠ cfg.baseAsset ∧ cfg.originOf A ≠ cfg.thisChain

instance (cfg : Config) (A : AssetId) : Decidable (BurnsSupply cfg A) := by
  unfold BurnsSupply; infer_instance

/-- The asset originates on this chain, so the tracker keeps its `chainBalance`. -/
def NativeHere (cfg : Config) (A : AssetId) : Prop := cfg.originOf A = cfg.thisChain

instance (cfg : Config) (A : AssetId) : Decidable (NativeHere cfg A) := by
  unfold NativeHere; infer_instance

/-- **`w'` IS `w` WITH `c` OF ASSET `A` MOVED TO PAYER `u`.**  Every account of the leg's ledger
changes by `c * dir`: `u` gains `c` and the sink loses `c`.  The token's supply grows by `c` if the
asset is burned on collection, the tracker's `chainBalance` grows by `c` if the asset is native here,
and the two L1 counters do not move.  `c` may be negative. -/
structure Shifted (cfg : Config) (A : AssetId) (u : Address) (c : ℤ) (w w' : World) : Prop where
  ledger : ∀ x, (ledger cfg A w' x : ℤ) = ledger cfg A w x + c * dir cfg A u x
  supply : (w'.supply A : ℤ) = w.supply A + c * (if BurnsSupply cfg A then 1 else 0)
  chainBalance :
    (w'.chainBalance A : ℤ) = w.chainBalance A + c * (if NativeHere cfg A then 1 else 0)
  toL1 : w'.toL1 A = w.toL1 A
  fromL1 : w'.fromL1 A = w.fromL1 A

/-- No account holds more of asset `A`'s token than its total supply: the ERC20 ledger invariant
(the sum of balances is `totalSupply`), which `burnToken` relies on (OpenZeppelin v4 `_burn`
decrements `_totalSupply` unchecked after checking only the balance).  The model keeps supply and
balances as separate fields, so results that burn state it. -/
def SupplyCovers (w : World) (A : AssetId) : Prop := ∀ x, w.bal A x ≤ w.supply A

/-- `w'` leaves asset `A`'s footprint and its tracker registration as they were in `w`. -/
def Frames (cfg : Config) (A : AssetId) (w w' : World) : Prop :=
  ledger cfg A w' = ledger cfg A w ∧ w'.supply A = w.supply A ∧
    w'.chainBalance A = w.chainBalance A ∧ w'.toL1 A = w.toL1 A ∧ w'.fromL1 A = w.fromL1 A ∧
    w'.registered A = w.registered A

/-- **THE FRAME PREMISE ON ROUTER-CALL RECOVERY.**  Recovering a router-produced call whose data
does not name asset `A` leaves `A`'s footprint and tracker registration alone.  For the vault this
is its refund of another asset, which writes that asset's ledger, supply and tracker entries, and
the native ledger only when that asset is the base token.  A custom handler's code is not
constrained by the source. -/
def RecoveryFramesOthers (P : Params) (A : AssetId) : Prop :=
  ∀ w d cd w', (∀ src a m, cd = .finalizeDeposit src a m → a ≠ A) →
    P.routerRecover w d cd = some w' → Frames P.cfg A w w'

/-- The change of `A`'s footprint from `w₀` to `w₁` is the negation of its change from `w₂` to
`w₃`, account by account, for the supply and for the three tracker counters. -/
def DeltasCancel (cfg : Config) (A : AssetId) (w₀ w₁ w₂ w₃ : World) : Prop :=
  (∀ x, (ledger cfg A w₃ x : ℤ) - ledger cfg A w₂ x = -((ledger cfg A w₁ x : ℤ) - ledger cfg A w₀ x)) ∧
    ((w₃.supply A : ℤ) - w₂.supply A = -((w₁.supply A : ℤ) - w₀.supply A)) ∧
    ((w₃.chainBalance A : ℤ) - w₂.chainBalance A = -((w₁.chainBalance A : ℤ) - w₀.chainBalance A)) ∧
    ((w₃.toL1 A : ℤ) - w₂.toL1 A = -((w₁.toL1 A : ℤ) - w₀.toL1 A)) ∧
    ((w₃.fromL1 A : ℤ) - w₂.fromL1 A = -((w₁.fromL1 A : ℤ) - w₀.fromL1 A))

/-! ## Witness data

One source chain, `10`, with L1 `1`: router `3`, vault `4`, holder `17`, WETH `66`.  Asset `100` is
the base token (from L1, local token `9`), asset `200` a token native to this chain (token `50`), and
asset `300` a token bridged from L1 (token `60`).  The sender is `5` and the destination chain
`20`. -/

/-- The witness chain. -/
def wCfg : Config where
  thisChain := 10
  l1Chain := 1
  slIsL1 := true
  router := 3
  ntv := 4
  holder := 17
  baseAsset := 100
  tokenOf := fun a => if a = 100 then 9 else if a = 200 then 50 else if a = 300 then 60 else 0
  assetOf := fun t => if t = 9 then 100 else if t = 50 then 200 else if t = 60 then 300 else 0
  originOf := fun a => if a = 100 then 1 else if a = 200 then 10 else if a = 300 then 1 else 0
  weth := 66
  rejectsValue := fun _ => false

/-- Router-call recovery that mints one unit of the asset its data names to account `8`, a
stand-in for the vault refunding another asset; other data is declined. -/
def wRecover : World → Chain → CallData → Option World
  | w, _, .finalizeDeposit _ a _ => some (mintToken w a 8 1)
  | w, _, .other _ => some w

/-- A handler other than the vault that burns from the payer's ledger. -/
def wCustomBurn (_h : Address) (w : World) (_d : Chain) (a : AssetId) (u : Address) (v : ℕ) :
    Option World :=
  if w.bal a u < v then none else some (burnToken w a u v)

/-- The witness parameters. -/
def wParams : Params := ⟨wCfg, wRecover, wCustomBurn⟩

/-- The witness world: the holder holds `1000` native, the sender and the router `100` each; the
sender holds `50` of asset `200` (the vault `30`) and `20` of asset `300`.  Assets `100`, `200`,
`300` are routed to the vault and registered in the tracker. -/
def wWorld : World where
  native := fun x => if x = 17 then 1000 else if x = 5 ∨ x = 3 then 100 else 0
  bal := fun a x =>
    if a = 200 ∧ x = 5 then 50 else if a = 200 ∧ x = 4 then 30
    else if a = 300 ∧ x = 5 then 20 else 0
  supply := fun a => if a = 200 then 80 else if a = 300 then 20 else 0
  handler := fun a => if a = 100 ∨ a = 200 ∨ a = 300 then 4 else 0
  ntvPaused := false
  registered := fun a => decide (a = 100 ∨ a = 200 ∨ a = 300)
  chainBalance := fun a => if a = 200 then 500 else 0
  toL1 := fun _ => 0
  fromL1 := fun _ => 0

/-- `wWorld` with asset `300` not yet registered in the tracker. -/
def wWorldUnregistered : World := { wWorld with registered := fun a => decide (a = 100 ∨ a = 200) }

/-- `wWorld` with asset `200` (native to the source chain) not yet registered in the tracker, and
every `chainBalance` zero, as `_registerLegacyToken` requires of a native token
(`L2AssetTracker.sol:240-244`). -/
def wWorldNativeUnregistered : World :=
  { wWorld with registered := fun a => decide (a = 100 ∨ a = 300), chainBalance := fun _ => 0 }

/-- A direct starter to `77` carrying value `v`. -/
def wDirect (v : ℕ) : Starter := ⟨77, .other [], v, 0, false⟩

/-- An indirect starter through the router carrying value `v`. -/
def wIndirect (v : ℕ) : Starter := ⟨3, .other [], v, 0, true⟩

/-- The call a direct starter to `77` forms for sender `u`. -/
def wDirectCall (u : Address) (v : ℕ) : Call := ⟨77, u, v, .other []⟩

/-- A router-produced call on asset `a`. -/
def wRouterCall (a : AssetId) (v : ℕ) : Call := ⟨3, 3, v, .finalizeDeposit 10 a []⟩

/-- A bundle from chain `10` to chain `20` with destination base-token asset `A`. -/
def wBundle (A : AssetId) (calls : List Call) : Bundle := ⟨10, 20, A, 0, calls, []⟩

end Contracts.NativeValueLegs
