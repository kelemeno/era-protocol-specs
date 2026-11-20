import Mathlib.Tactic
import EraSpec.Contracts.InteropCenter.Specs.Common

/-!
# Model: `InteropCenter` fee state at draft/v0.35.0 — balances, fee ledgers, claims, fee
parameters and the fee-unit counter

Source: era-contracts draft/v0.35.0 head **`b17415d20`**, `l1-contracts/contracts/interop/InteropCenter.sol`
(a bare `:N` is a line of that file), with `common/ReentrancyGuard.sol`, `common/Config.sol`,
`atomic-interop/AtomicFlowManager.sol`, `atomic-interop/L2InteropCommitmentTree.sol`,
`l2-system/BaseTokenHolder.sol`, `bridge/asset-router/L2AssetRouter.sol` and
`bridge/ntv/L2NativeTokenVault.sol` from the same commit. The pin model of the send path is `Specs/Dispatch.lean` (`c67894b9`), which omits every
field below; this file reuses its `CallStarter` and `totalBurnedCallsValue`
(`InteropCallStarterInternal` and `CallAttributes` are unchanged at `b17415d20`,
`common/Messaging.sol:199-214`).

**This file is definitions only.** The results are in
`EraSpec.Contracts.InteropCenter.Properties.FeeState` and are proved in
`EraSpec.Contracts.InteropCenter.Proofs.FeeState`. The nested-call refinement used for the
reentrancy question is `Specs/FeeReentry.lean`.

## The code

    uint256 public interopProtocolFee;                                          // :105
    uint256 public ZK_INTEROP_FEE;                                              // :111
    bytes32 public ZK_TOKEN_ASSET_ID;                                           // :114
    IERC20 public zkToken;                                                      // :117
    mapping(address coinbase => uint256 amount) public accumulatedProtocolFees; // :120
    mapping(address coinbase => uint256 amount) public accumulatedZKFees;       // :123

    // _sendBundle (:533-613), after the salt check (:562-566):
    (bundle, totalBurnedCallsValue, totalIndirectCallsValue) = _buildInteropBundle(...);   // :570-574
    if (_bundleAttributes.useFixedFee && _destinationChainId != L1_CHAIN_ID) {             // :579
        uint256 totalZKFee = ZK_INTEROP_FEE * callStartersLength;                          // :580
        _getZKToken().safeTransferFrom(msg.sender, address(this), totalZKFee);             // :581
        accumulatedZKFees[block.coinbase] += totalZKFee;                                   // :582
    }
    _ensureCorrectTotalValue(...);                                                          // :587-594
    (bundleHash, msgHash) = _dispatchBundle(bundle, _atomicSend);                           // :602

    // _ensureCorrectTotalValue (:418-460)
    uint256 protocolFee = (_useFixedFee || _destinationChainId == L1_CHAIN_ID) ? 0
        : interopProtocolFee * _callCount;                                                 // :428-430
    if (_destinationBaseTokenAssetId == thisChainBaseTokenAssetId) {                        // :432
        require(msg.value == _totalBurnedCallsValue + _totalIndirectCallsValue + protocolFee); // :433-434
        if (_totalBurnedCallsValue > 0)
            L2_BASE_TOKEN_HOLDER.burnAndStartBridging{value: _totalBurnedCallsValue}(_destinationChainId); // :436-440
    } else {
        require(msg.value == _totalIndirectCallsValue + protocolFee);                       // :442-443
        if (_totalBurnedCallsValue > 0)
            IAssetRouterShared(L2_ASSET_ROUTER_ADDR).bridgehubDepositBaseToken(
                _destinationChainId, _destinationBaseTokenAssetId, msg.sender, _totalBurnedCallsValue); // :445-452
    }
    if (protocolFee > 0) accumulatedProtocolFees[block.coinbase] += protocolFee;           // :456-459

    // _processCallStarter, indirect branch (:782-821), run inside _buildInteropBundle (:679)
    IL2CrossChainSender(recipientAddress).initiateIndirectCall{
        value: _callStarter.callAttributes.indirectCallMessageValue }(...);                 // :788-790

    // _dispatchBundle (:727-750)
    if (_bundle.destinationChainId == L1_CHAIN_ID) {
        msgHash = L2_TO_L1_MESSENGER_SYSTEM_CONTRACT.sendToL1(...); return ...;             // :733-737
    }
    IAtomicFlowManager(L2_ATOMIC_FLOW_MANAGER_ADDR).append(...);                           // :742-746
    StorageSlot.getUint256Slot(INTEROP_FEE_UNITS_SLOT).value += _bundle.calls.length;       // :749

    function setInteropFee(uint256 _fee) external onlyCallFromBootloader { interopProtocolFee = _fee; } // :889-893
    function claimProtocolFees(address _receiver) external nonReentrant {                  // :896
        uint256 amount = accumulatedProtocolFees[msg.sender]; if (amount == 0) return;      // :897-900
        accumulatedProtocolFees[msg.sender] = 0;                                            // :902
        (bool success, ) = _receiver.call{value: amount}(""); require(success);             // :905-906
    }
    function claimZKFees(address _receiver) external nonReentrant {                        // :912
        uint256 amount = accumulatedZKFees[msg.sender]; if (amount == 0) return;            // :913-916
        accumulatedZKFees[msg.sender] = 0;                                                  // :918
        _getZKToken().safeTransfer(_receiver, amount);                                      // :919
    }

`_getZKToken` (:159-167) returns `zkToken` if it is set, else
`IL2NativeTokenVault(L2_NATIVE_TOKEN_VAULT).tokenAddress(ZK_TOKEN_ASSET_ID)` (:148-153), requires it
nonzero (`ZKTokenNotAvailable`) and caches it in `zkToken` if unset. `initL2` (:170-187) is
`reentrancyGuardInitializer onlyUpgrader`; it requires `_zkTokenAssetId != 0` and writes
`ZK_TOKEN_ASSET_ID`, `L1_CHAIN_ID`, `ZK_INTEROP_FEE = DEFAULT_ZK_INTEROP_FEE = 10e18` (:79) and,
if it differs, the owner.

## The inventory the model rests on (checked against `b17415d20`)

* Writers. `interopProtocolFee`: only :891. `ZK_INTEROP_FEE`, `ZK_TOKEN_ASSET_ID`, `L1_CHAIN_ID`:
  only :179-182 in `initL2`. `zkToken`: only :164. `accumulatedProtocolFees`: :457 and :902.
  `accumulatedZKFees`: :582 and :918. `INTEROP_FEE_UNITS_SLOT` (`Config.sol:143-147`): only :749
  (`interopFeeUnits()` :884-886 reads it). The salt mapping and `__DEPRECATED_interopBundleNonce`
  (:102, never written) are not fee state.
* The center has **no** `onlyOwner` function, no `whenNotPaused`, no call to `_pause`/`_unpause`,
  and no `receive`/`fallback`. The only owner-gated functions are the inherited OpenZeppelin v4
  `Ownable2StepUpgradeable.transferOwnership`/`acceptOwnership`/`renounceOwnership`, which write
  only `_owner`/`_pendingOwner`. (main `70096e2ea` differs: it has `pause()`/`unpause()`
  `onlyOwner` and `whenNotPaused` on both sends, and no fee-unit counter.)
* The center sends native value only at :439 (holder), :788-790 (indirect sender, which
  `IndirectCallOnlyToAssetRouter`, :665-668, pins to `L2_ASSET_ROUTER_ADDR`) and :905 (claim
  receiver). `bridgehubDepositBaseToken` (:446) is called with no value. Its only payable entry
  points are the two sends; the previews (:284-304, :307-335) are not payable and always revert
  (:353).
* `nonReentrant` (`ReentrancyGuard.sol:72-98`) reverts unless the lock slot
  (`keccak256("ReentrancyGuard") - 1`, :31) holds `1`, holds `2` during the call and `1` after.
  `reentrancyGuardInitializer` (:43-63) writes `1` and reverts unless the slot held `0`. So before
  `initL2` no send or claim succeeds, and `initL2` succeeds at most once.
* `AtomicFlowManager.append` is `onlyInteropCenter` (AtomicFlowManager.sol:88-93, :108) and is
  called only at :742; the commitment tree's `insert` accepts only the manager
  (L2InteropCommitmentTree.sol:51-53), which calls it only in `append` (:170). So every IMT leaf is
  an `append` made by `_dispatchBundle` for an L2 destination, immediately followed by :749.

## Modelling choices

* **One chain, one center.** `Params` fixes the system addresses, this chain's base-token asset id
  and what the token contract at each address does on `transferFrom`/`transfer` (`TokenCode`).
* **Value.** `bal` is the center's native balance; `tokBal t` its ERC-20 balance in the token
  contract `t`. Native value enters only as `msg.value` of a send or as a forced inflow
  (`nativeInflow`, e.g. a `SELFDESTRUCT` beneficiary); tokens enter by `transferFrom` on the
  fixed-fee path or by anyone's `transfer` to the center (`tokenInflow`). The asset router's
  `initiateIndirectCall` and `bridgehubDepositBaseToken`, the holder's `burnAndStartBridging` and
  the claim receiver send nothing back to the center that the model does not show as an inflow.
* **A revert is the absence of a step** (`VM-REVERT`): `exec` returns `none`. A preview always
  reverts, so it never commits. A claim of a zero ledger returns early and succeeds with no effect.
* **A transaction is one step.** In the deployed code the shared lock stops a send or claim from
  starting inside a send or claim (`FeeReentry.HeldLockBlocksSendsAndClaims`); calls made from
  inside one (by `initiateIndirectCall`, a deposit's token hooks, a claim receiver) to the other
  entry points are taken here as separate transactions. `Specs/FeeReentry.lean` models the nested
  calls themselves, and shows a transaction here is exactly such a call with none
  (`FlatIsNestedWithoutCalls`).
* **Reject-only checks that read nothing the fee state depends on are omitted**: the ERC-7930
  parsing and nonzero-recipient checks, attribute parsing, the destination registration and
  `isPeerAllowed` checks (:696-704), the salt check (modelled in `Dispatch`), the atomicity flag
  check (:552-556; the destination alone decides the branch), `IndirectCallValueMismatch`
  (:796-802), every check inside `append`, the token side of `bridgehubDepositBaseToken` and the
  sender's ZK allowance, and the overflow checks of the fee products and ledgers (amounts are
  `ℕ`). Omitting a rejecting check only adds runs.
* **Kept checks**: the lock, the L1/self destination rules (:260-264, :401, :404), the L1 and
  indirect starter restrictions (:646-678), that every value call can be paid, the two `msg.value`
  equalities (a switch, `Checks.valueCheck`), the ZK token's availability and code, the checked
  `+=` at :749, and `onlyInteropCenter` (a switch).
* **Ghosts**: `forcedIn` (the native value forced in), `leaves` (the call count of each appended
  bundle, one entry per IMT leaf), `log` (every successful send, with its payments) and `claims`.
* **Of `AtomicFlowManager`'s entry points only `append` is modelled**, as a foreign attempt
  (`Tx.foreignAppend`). The others (`initL2`, `requireFlowFinalized`, `authorizeRefund`,
  `claimRefund`) are not the center's code and append no leaf, so they write none of the center's
  storage, its counter slot or the leaves; a call they make into the center is one of the
  center's own transactions, which the model admits from any caller.
* **Layout.** The counter is its own field. In storage it is the slot `INTEROP_FEE_UNITS_SLOT`; that
  it is distinct from the lock slot, the EIP-1967 slots and every slot below `2^64` (where the
  sequentially allocated variables live) is `FeeUnitsSlotSeparate`; that no mapping slot
  `keccak256(key . p)` equals it is a keccak premise the model does not state (ASSUMPTIONS.md
  `MODEL-FEE-STATE`). Upgrades that rewrite storage are `OPS-CONFIG`.
-/

namespace Contracts.InteropCenter.FeeState

open Contracts.InteropCenter (Word Address CallStarter CallAttributes totalBurnedCallsValue)

/-! ## Constants -/

/-- `DEFAULT_ZK_INTEROP_FEE = 10e18` (:79), the value `initL2` writes to `ZK_INTEROP_FEE` (:182). -/
def defaultZkInteropFee : ℕ := 10 * 10 ^ 18

/-- `INTEROP_FEE_UNITS_SLOT` (`Config.sol:147`). -/
def feeUnitsSlot : ℕ := 0xcb06feb7f26e08c2ab18254891cfbe115998e9ed512f0732aa6fc7f097a78265

/-- The reentrancy lock slot `LOCK_FLAG_ADDRESS` (`ReentrancyGuard.sol:31`). -/
def lockSlot : ℕ := 0x8e94fed44239eb2314ab7a406345e6c5a8f0ccedf3b600de3d004e672c33abf4

/-- The EIP-1967 implementation slot, `keccak256("eip1967.proxy.implementation") - 1`. -/
def eip1967ImplSlot : ℕ := 0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc

/-- The EIP-1967 admin slot, `keccak256("eip1967.proxy.admin") - 1`. -/
def eip1967AdminSlot : ℕ := 0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103

/-! ## Tokens and parameters -/

/-- What the contract at an address does when the center calls `transferFrom(sender, center, x)`
(`SafeERC20.safeTransferFrom`, :581) or `transfer(receiver, x)` (`safeTransfer`, :919) on it. -/
inductive TokenCode where
  /-- A standard ERC-20: `transferFrom(sender, center, x)` with `sender ≠ center` adds exactly `x`
  to the center's balance; `transfer(receiver, x)` needs `x` at most the center's balance and
  removes `x` from it unless `receiver` is the center itself. -/
  | standard
  /-- No `transferFrom`, no `transfer`, no fallback: both calls revert. -/
  | noTransfer
  /-- `transferFrom(sender, center, x)` succeeds and adds `credit x` to the center's balance;
  `transfer` is standard. Used only to show that the standard-token premise is load-bearing. -/
  | nonStandard (credit : ℕ → ℕ)

/-- Whether `transferFrom` and `transfer` exist and can succeed. -/
def TokenCode.hasTransfer : TokenCode → Bool
  | .noTransfer => false
  | _ => true

/-- What a successful `transferFrom(sender, center, x)` adds to the center's balance. -/
def TokenCode.credited : TokenCode → ℕ → ℕ
  | .standard, x => x
  | .noTransfer, _ => 0
  | .nonStandard f, x => f x

/-- One chain's constants and the environment the fee path reads. -/
structure Params where
  /-- `block.chainid`. -/
  chainId : Word
  /-- `L2_INTEROP_CENTER_ADDR` (`0x1000d`). -/
  center : Address
  /-- `L2_BOOTLOADER_ADDRESS` (`0x8001`), the only caller of `setInteropFee` (:142-145). -/
  bootloader : Address
  /-- `L2_COMPLEX_UPGRADER_ADDR` (`0x800f`), the only caller of `initL2` (:136-139). -/
  upgrader : Address
  /-- `SETTLEMENT_LAYER_RELAY_SENDER` (`Config.sol:219`), the only caller of
  `forwardTransactionOnGateway` (:130-133). -/
  relaySender : Address
  /-- `L2_ASSET_ROUTER_ADDR` (`0x10003`), the only indirect sender (:665-668). -/
  router : Address
  /-- `L2_BASE_TOKEN_HOLDER` (`0x10011`). -/
  holder : Address
  /-- `IL2NativeTokenVault(L2_NATIVE_TOKEN_VAULT).BASE_TOKEN_ASSET_ID()` (:426), frozen once set
  (`L2NativeTokenVault.sol:150-155`). -/
  baseAssetId : Word
  /-- The code at each address, as far as `transferFrom`/`transfer` go. -/
  tokenCode : Address → TokenCode

/-- **STANDARD-TOKEN PREMISE.** No token contract on the chain credits the center anything other
than the amount transferred: each is `standard` or has no transfer functions at all. -/
def StandardTokens (P : Params) : Prop := ∀ (t : Address) (f : ℕ → ℕ), P.tokenCode t ≠ .nonStandard f

/-! ## Sends -/

/-- A value transfer or value-free bridging call the center makes during a send, in code order. -/
inductive Payment where
  /-- `IL2CrossChainSender(sender).initiateIndirectCall{value: value}(...)` (:788-790). -/
  | forward (sender : Address) (value : ℕ)
  /-- `L2_BASE_TOKEN_HOLDER.burnAndStartBridging{value: value}(toChain)` (:439). -/
  | burn (toChain : Word) (value : ℕ)
  /-- `IAssetRouterShared(L2_ASSET_ROUTER_ADDR).bridgehubDepositBaseToken(toChain, assetId,
  originalCaller, amount)` (:446-451), called with no value. -/
  | deposit (toChain : Word) (assetId : Word) (originalCaller : Address) (amount : ℕ)
deriving DecidableEq

/-- The native value a payment takes from the center. -/
def Payment.nativeValue : Payment → ℕ
  | .forward _ v => v
  | .burn _ v => v
  | .deposit .. => 0

/-- The total native value a list of payments takes from the center. -/
def nativeOut (ps : List Payment) : ℕ := (ps.map Payment.nativeValue).sum

/-- One `sendBundle` (:248-281) or `sendMessage` (:197-245) transaction that reaches `_sendBundle`,
after parsing, with the answers of the contracts it reads. -/
structure SendInput where
  /-- `msg.sender`. -/
  sender : Address
  /-- `block.coinbase`. -/
  coinbase : Address
  /-- `msg.value`. -/
  msgValue : ℕ
  /-- The destination chain id. -/
  dest : Word
  /-- The bundle's `destinationBaseTokenAssetId` (:629-631). -/
  destBase : Word
  /-- The parsed call starters. -/
  starters : List CallStarter
  /-- The `useFixedFee` bundle attribute. -/
  useFixedFee : Bool
  /-- `IL2NativeTokenVault.tokenAddress(ZK_TOKEN_ASSET_ID)` (:152), read only while `zkToken` is
  unset. -/
  zkResolved : Address

/-- The call count of the bundle (`callStartersLength`, `_bundle.calls.length`). -/
def SendInput.calls (inp : SendInput) : ℕ := inp.starters.length

/-- `totalIndirectCallsValue` (:683-685): the `indirectCallMessageValue`s of the indirect
starters. -/
def indirectTotal (starters : List CallStarter) : ℕ :=
  ((starters.filter fun cs => cs.callAttributes.indirectCall).map
    fun cs => cs.callAttributes.indirectCallMessageValue).sum

/-- The value call of one indirect starter (:788-790). -/
def forwardOf (cs : CallStarter) : Payment := .forward cs.target cs.callAttributes.indirectCallMessageValue

/-- The forwards `_buildInteropBundle` makes, one per indirect starter, in order. -/
def forwardPayments (starters : List CallStarter) : List Payment :=
  (starters.filter fun cs => cs.callAttributes.indirectCall).map forwardOf

/-- The destination base token is this chain's (:432). -/
def sameBase (P : Params) (inp : SendInput) : Bool := decide (inp.destBase = P.baseAssetId)

/-- The burn (same base token) or deposit (different base token) of the calls' total value, if it
is nonzero (:436-440, :445-452). -/
def valuePayment (P : Params) (inp : SendInput) : List Payment :=
  if totalBurnedCallsValue inp.starters = 0 then []
  else if sameBase P inp then [.burn inp.dest (totalBurnedCallsValue inp.starters)]
  else [.deposit inp.dest inp.destBase inp.sender (totalBurnedCallsValue inp.starters)]

/-- Every payment of a send, in code order. -/
def sendPayments (P : Params) (inp : SendInput) : List Payment :=
  forwardPayments inp.starters ++ valuePayment P inp


/-- One successful send, as the ghost log records it. -/
structure SendRecord where
  /-- The transaction. -/
  input : SendInput
  /-- `_dispatchBundle` took the L1 branch (:733): the bundle was published, not appended. -/
  toL1 : Bool
  /-- The base-token protocol fee charged (:428-430). -/
  protocolFee : ℕ
  /-- The ZK fee charged (:580), `0` off the fixed-fee path. -/
  zkFee : ℕ
  /-- The ZK token the fixed-fee path pulled from, `0` off that path. -/
  zkTokenUsed : Address
  /-- Every payment the center made, in code order. -/
  payments : List Payment

/-- One claim that paid a nonzero amount. -/
structure ClaimRecord where
  /-- `claimZKFees` (else `claimProtocolFees`). -/
  zk : Bool
  /-- `msg.sender`, whose ledger entry was paid. -/
  claimant : Address
  /-- `_receiver`. -/
  receiver : Address
  /-- The amount paid. -/
  amount : ℕ

/-- The fee-state fields of one chain's center, with ghosts. -/
structure State where
  /-- The center's native balance. -/
  bal : ℕ
  /-- The center's balance in each token contract (`balanceOf(center)`). -/
  tokBal : Address → ℕ
  /-- `accumulatedProtocolFees` (:120). -/
  protocolFees : Address → ℕ
  /-- `accumulatedZKFees` (:123). -/
  zkFees : Address → ℕ
  /-- `interopProtocolFee` (:105). -/
  interopProtocolFee : ℕ
  /-- `ZK_INTEROP_FEE` (:111). -/
  zkInteropFee : ℕ
  /-- `ZK_TOKEN_ASSET_ID` (:114). -/
  zkTokenAssetId : Word
  /-- `L1_CHAIN_ID` (:98). -/
  l1ChainId : Word
  /-- `zkToken` (:117); `0` is unset. -/
  zkToken : Address
  /-- The reentrancy lock slot: `0` before `initL2`, `1` between calls. -/
  lock : ℕ
  /-- `PausableUpgradeable._paused`. -/
  paused : Bool
  /-- `OwnableUpgradeable._owner`. -/
  owner : Address
  /-- `Ownable2StepUpgradeable._pendingOwner`. -/
  pendingOwner : Address
  /-- The word at `INTEROP_FEE_UNITS_SLOT`. -/
  feeUnits : ℕ
  /-- Ghost: the native value forced into the center. -/
  forcedIn : ℕ
  /-- Ghost: one entry per IMT leaf (`AtomicFlowManager.append`), the appended bundle's call
  count, oldest first. -/
  leaves : List ℕ
  /-- Ghost: every successful send, oldest first. -/
  log : List SendRecord
  /-- Ghost: every claim that paid a nonzero amount, oldest first. -/
  claims : List ClaimRecord

/-- Fresh storage, with no balance. -/
def init : State where
  bal := 0
  tokBal := fun _ => 0
  protocolFees := fun _ => 0
  zkFees := fun _ => 0
  interopProtocolFee := 0
  zkInteropFee := 0
  zkTokenAssetId := 0
  l1ChainId := 0
  zkToken := 0
  lock := 0
  paused := false
  owner := 0
  pendingOwner := 0
  feeUnits := 0
  forcedIn := 0
  leaves := []
  log := []
  claims := []

/-- The center's balance in its cached ZK token, `0` while `zkToken` is unset. -/
def zkBalance (S : State) : ℕ := if S.zkToken = 0 then 0 else S.tokBal S.zkToken

/-! ## The fee arithmetic of one send -/

/-- `protocolFee` (:428-430). -/
def protocolFeeOf (S : State) (inp : SendInput) : ℕ :=
  if inp.useFixedFee = true ∨ inp.dest = S.l1ChainId then 0 else S.interopProtocolFee * inp.calls

/-- The fixed-ZK-fee branch is taken (:579). -/
def fixedFeePath (S : State) (inp : SendInput) : Bool :=
  inp.useFixedFee && !decide (inp.dest = S.l1ChainId)

/-- `totalZKFee` (:580), `0` off the fixed-fee path. -/
def zkFeeOf (S : State) (inp : SendInput) : ℕ :=
  if fixedFeePath S inp = true then S.zkInteropFee * inp.calls else 0

/-- `getZKTokenAddress()` (:148-153), with the vault's answer `resolved`. -/
def zkTokenFor (S : State) (resolved : Address) : Address :=
  if S.zkToken = 0 then resolved else S.zkToken

/-- `expectedValue` (:433 same base token, :442 different base token). -/
def expectedValue (P : Params) (S : State) (inp : SendInput) : ℕ :=
  if sameBase P inp = true then
    totalBurnedCallsValue inp.starters + indirectTotal inp.starters + protocolFeeOf S inp
  else indirectTotal inp.starters + protocolFeeOf S inp

/-- The restrictions on a starter of an L2→L1 bundle (:646-658): indirect, through the asset
router, with no `interopCallValue`. -/
def ToL1Starter (P : Params) (cs : CallStarter) : Prop :=
  cs.callAttributes.indirectCall = true ∧ cs.target = P.router ∧
    cs.callAttributes.interopCallValue = 0

instance (P : Params) (cs : CallStarter) : Decidable (ToL1Starter P cs) := by
  unfold ToL1Starter; infer_instance

/-- Which of two checks the code performs. The deployed code performs both. -/
structure Checks where
  /-- The `msg.value` equalities of `_ensureCorrectTotalValue` (:433-434, :442-443). -/
  valueCheck : Bool
  /-- `onlyInteropCenter` on `AtomicFlowManager.append` (AtomicFlowManager.sol:88-93, :108). -/
  onlyInteropCenter : Bool

/-- The deployed code. -/
def deployed : Checks := ⟨true, true⟩

/-- The deployed code without the `msg.value` equalities. -/
def withoutValueCheck : Checks := ⟨false, true⟩

/-- The deployed code without `onlyInteropCenter` on `append`. -/
def withoutOnlyInteropCenter : Checks := ⟨true, false⟩

/-- A send of `inp` from `S` succeeds: the checks the model keeps. -/
def SendOk (K : Checks) (P : Params) (S : State) (inp : SendInput) : Prop :=
  -- `nonReentrant` (:201, :252; `ReentrancyGuard.sol:78-84`).
  S.lock = 1 ∧
  -- `CannotInitiateInteropOnL1` (:260) / `_ensureL2ToL2` (:401).
  S.l1ChainId ≠ P.chainId ∧
  -- `InteropToSelfNotSupported` (:261, :404).
  inp.dest ≠ P.chainId ∧
  -- An L2→L1 bundle is one indirect zero-value call through the asset router (:262-264,
  -- :646-658).
  (inp.dest = S.l1ChainId → inp.calls = 1 ∧ ∀ cs ∈ inp.starters, ToL1Starter P cs) ∧
  -- `IndirectCallOnlyToAssetRouter` and `IndirectCallCannotCarryValue` (:659-678).
  (∀ cs ∈ inp.starters, cs.callAttributes.indirectCall = true →
    cs.target = P.router ∧ cs.callAttributes.interopCallValue = 0) ∧
  -- Every value call (:788-790, :439) can be paid from the balance plus `msg.value`.
  nativeOut (sendPayments P inp) ≤ S.bal + inp.msgValue ∧
  -- `MsgValueMismatch` (:433-434, :442-443).
  (K.valueCheck = true → inp.msgValue = expectedValue P S inp) ∧
  -- The fixed-fee path (:579-582): the ZK token is available (`ZKTokenNotAvailable`, :161) and
  -- has `transferFrom`; the sender is never the center, which never calls its own sends.
  (fixedFeePath S inp = true →
    zkTokenFor S inp.zkResolved ≠ 0 ∧ (P.tokenCode (zkTokenFor S inp.zkResolved)).hasTransfer = true ∧
      inp.sender ≠ P.center) ∧
  -- The checked `+=` of :749.
  (inp.dest ≠ S.l1ChainId → S.feeUnits + inp.calls < UInt256.size)

instance (K : Checks) (P : Params) (S : State) (inp : SendInput) : Decidable (SendOk K P S inp) := by
  unfold SendOk; infer_instance

/-- The record a successful send of `inp` from `S` logs. -/
def sendRecord (P : Params) (S : State) (inp : SendInput) : SendRecord where
  input := inp
  toL1 := decide (inp.dest = S.l1ChainId)
  protocolFee := protocolFeeOf S inp
  zkFee := zkFeeOf S inp
  zkTokenUsed := if fixedFeePath S inp = true then zkTokenFor S inp.zkResolved else 0
  payments := sendPayments P inp

/-- The state after a successful send of `inp` from `S`. -/
def afterSend (P : Params) (S : State) (inp : SendInput) : State :=
  { S with
    bal := S.bal + inp.msgValue - nativeOut (sendPayments P inp)
    protocolFees := Function.update S.protocolFees inp.coinbase
      (S.protocolFees inp.coinbase + protocolFeeOf S inp)
    zkToken := if fixedFeePath S inp = true then zkTokenFor S inp.zkResolved else S.zkToken
    tokBal := if fixedFeePath S inp = true then
        Function.update S.tokBal (zkTokenFor S inp.zkResolved)
          (S.tokBal (zkTokenFor S inp.zkResolved) +
            (P.tokenCode (zkTokenFor S inp.zkResolved)).credited (zkFeeOf S inp))
      else S.tokBal
    zkFees := if fixedFeePath S inp = true then
        Function.update S.zkFees inp.coinbase (S.zkFees inp.coinbase + zkFeeOf S inp)
      else S.zkFees
    feeUnits := if inp.dest = S.l1ChainId then S.feeUnits else S.feeUnits + inp.calls
    leaves := if inp.dest = S.l1ChainId then S.leaves else S.leaves ++ [inp.calls]
    log := S.log ++ [sendRecord P S inp] }

/-! ## The other entry points -/

/-- `claimProtocolFees(_receiver)` (:896-909) by `c`. -/
def claimProtocolFeesStep (P : Params) (S : State) (c r : Address) : Option State :=
  if S.lock = 1 then
    if S.protocolFees c = 0 then some S
    else if S.protocolFees c ≤ S.bal ∧ r ≠ P.center then
      some { S with
        protocolFees := Function.update S.protocolFees c 0
        bal := S.bal - S.protocolFees c
        claims := S.claims ++ [⟨false, c, r, S.protocolFees c⟩] }
    else none
  else none

/-- The body of `claimZKFees(_receiver)` (:913-921) by `c`, after `nonReentrant`'s check, with
the vault's answer `z` for `_getZKToken`. The standard token's `transfer` calls no other code. -/
def claimZKFeesBody (P : Params) (S : State) (c r z : Address) : Option State :=
  if S.zkFees c = 0 then some S
  else if zkTokenFor S z ≠ 0 ∧ (P.tokenCode (zkTokenFor S z)).hasTransfer = true ∧
      S.zkFees c ≤ S.tokBal (zkTokenFor S z) then
    some { S with
      zkFees := Function.update S.zkFees c 0
      zkToken := zkTokenFor S z
      tokBal := if r = P.center then S.tokBal
        else Function.update S.tokBal (zkTokenFor S z) (S.tokBal (zkTokenFor S z) - S.zkFees c)
      claims := S.claims ++ [⟨true, c, r, S.zkFees c⟩] }
  else none

/-- `claimZKFees(_receiver)` (:912-922) by `c`, with the vault's answer `z` for `_getZKToken`. -/
def claimZKFeesStep (P : Params) (S : State) (c r z : Address) : Option State :=
  if S.lock = 1 then claimZKFeesBody P S c r z else none

/-- `initL2(_l1ChainId, _owner, _zkTokenAssetId)` (:170-187) by `c`. -/
def initL2Step (P : Params) (S : State) (c : Address) (l1 : Word) (o : Address) (z : Word) :
    Option State :=
  if c = P.upgrader ∧ S.lock = 0 ∧ z ≠ 0 ∧ (S.owner ≠ o → o ≠ 0) then
    some { S with
      lock := 1
      zkTokenAssetId := z
      l1ChainId := l1
      zkInteropFee := defaultZkInteropFee
      owner := o
      pendingOwner := if S.owner = o then S.pendingOwner else 0 }
  else none

/-- One transaction. -/
inductive Tx where
  /-- `sendBundle` / `sendMessage`. -/
  | send (inp : SendInput)
  /-- `previewBundleHash` / `previewMessageHash` (:284-335). -/
  | preview (caller : Address)
  /-- `claimProtocolFees(receiver)` by `caller`. -/
  | claimProtocolFees (caller receiver : Address)
  /-- `claimZKFees(receiver)` by `caller`; `zkResolved` is the vault's answer for `_getZKToken`. -/
  | claimZKFees (caller receiver zkResolved : Address)
  /-- `setInteropFee(fee)` by `caller` (:889-893). -/
  | setInteropFee (caller : Address) (fee : ℕ)
  /-- `initL2(l1ChainId, newOwner, zkTokenAssetId)` by `caller`. -/
  | initL2 (caller : Address) (l1ChainId : Word) (newOwner : Address) (zkTokenAssetId : Word)
  /-- `forwardTransactionOnGateway` by `caller` (:839-850): an external call to a chain's diamond. -/
  | forwardTransactionOnGateway (caller : Address)
  /-- `Ownable2StepUpgradeable.transferOwnership(newOwner)` by `caller`. -/
  | transferOwnership (caller newOwner : Address)
  /-- `Ownable2StepUpgradeable.acceptOwnership()` by `caller`. -/
  | acceptOwnership (caller : Address)
  /-- `OwnableUpgradeable.renounceOwnership()` by `caller`. -/
  | renounceOwnership (caller : Address)
  /-- A call of `AtomicFlowManager.append` by `caller`, not from the center's code, for a bundle
  with `calls` calls. -/
  | foreignAppend (caller : Address) (calls : ℕ)
  /-- Native value forced into the center (no call of its code). -/
  | nativeInflow (amount : ℕ)
  /-- `token.transfer(center, amount)` by anyone. -/
  | tokenInflow (token : Address) (amount : ℕ)

/-- The successor state of a transaction, `none` if it reverts. -/
def exec (K : Checks) (P : Params) : Tx → State → Option State
  | .send inp, S => if SendOk K P S inp then some (afterSend P S inp) else none
  | .preview _, _ => none
  | .claimProtocolFees c r, S => claimProtocolFeesStep P S c r
  | .claimZKFees c r z, S => claimZKFeesStep P S c r z
  | .setInteropFee c f, S => if c = P.bootloader then some { S with interopProtocolFee := f } else none
  | .initL2 c l o z, S => initL2Step P S c l o z
  | .forwardTransactionOnGateway c, S => if c = P.relaySender then some S else none
  | .transferOwnership c o, S => if c = S.owner then some { S with pendingOwner := o } else none
  | .acceptOwnership c, S =>
      if c = S.pendingOwner then some { S with owner := c, pendingOwner := 0 } else none
  | .renounceOwnership c, S =>
      if c = S.owner then some { S with owner := 0, pendingOwner := 0 } else none
  | .foreignAppend c m, S =>
      if c ≠ P.center ∧ K.onlyInteropCenter = false then some { S with leaves := S.leaves ++ [m] }
      else none
  | .nativeInflow x, S => some { S with bal := S.bal + x, forcedIn := S.forcedIn + x }
  | .tokenInflow t x, S => some { S with tokBal := Function.update S.tokBal t (S.tokBal t + x) }

/-- A sequence of transactions, all of which succeed. -/
def run (K : Checks) (P : Params) : List Tx → State → Option State
  | [], S => some S
  | tx :: txs, S =>
    match exec K P tx S with
    | some S' => run K P txs S'
    | none => none

/-- `S'` is reachable from `S`. -/
def Reach (K : Checks) (P : Params) (S S' : State) : Prop := ∃ txs, run K P txs S = some S'

/-- One of the three inherited ownership entry points. -/
def Tx.isOwnership : Tx → Bool
  | .transferOwnership .. | .acceptOwnership .. | .renounceOwnership .. => true
  | _ => false

/-- `initL2`. -/
def Tx.isInitL2 : Tx → Bool
  | .initL2 .. => true
  | _ => false

/-- A send or a claim: the entry points with `nonReentrant` (:201, :252, :896, :912). -/
def Tx.isSendOrClaim : Tx → Bool
  | .send _ | .claimProtocolFees .. | .claimZKFees .. => true
  | _ => false

/-- A claim (:896, :912). -/
def Tx.isClaim : Tx → Bool
  | .claimProtocolFees .. | .claimZKFees .. => true
  | _ => false

/-- `S` with the given owner and pending owner. -/
def State.withOwners (S : State) (o p : Address) : State := { S with owner := o, pendingOwner := p }

/-- The sum of the call counts of the L2→L2 sends among `rs`. -/
def l2Calls (rs : List SendRecord) : ℕ :=
  ((rs.filter fun r => !r.toL1).map fun r => r.input.calls).sum

/-- What `_dispatchBundle` adds to the counter (:749) when `tx` runs from `S`: an L2→L2 send's
call count, `0` for every other transaction. -/
def Tx.unitsFrom (S : State) : Tx → ℕ
  | .send inp => if inp.dest = S.l1ChainId then 0 else inp.calls
  | _ => 0

/-! ## Witness data

Chain `271` settling on L1 `1`, with the system addresses of `L2ContractAddresses.sol`. In `wP`
every address is a standard token. -/

/-- This chain's base-token asset id in the witnesses. -/
def wBase : Word := 0xba5e

/-- A different base-token asset id. -/
def wOtherBase : Word := 0x07e5

/-- The witness ZK token contract. -/
def wZk : Address := 0x2000

/-- The witness chain. -/
def wP : Params where
  chainId := 271
  center := 0x1000d
  bootloader := 0x8001
  upgrader := 0x800f
  relaySender := 0x1111111111111111111111111111111111111111
  router := 0x10003
  holder := 0x10011
  baseAssetId := wBase
  tokenCode := fun _ => .standard

/-- As `wP`, but the token at `wZk` reports success on `transferFrom` and credits nothing. -/
def wPBadZk : Params :=
  { wP with tokenCode := fun t => (if t = wZk then .nonStandard (fun _ => 0) else wP.tokenCode t) }

/-- A direct starter to `0x60` with destination value `v`. -/
def wDirect (v : ℕ) : CallStarter := ⟨0x60, [], ⟨v, 0, false⟩⟩

/-- An indirect starter through the asset router, passing `m` of source-side value. -/
def wIndirect (m : ℕ) : CallStarter := ⟨0x10003, [], ⟨0, m, true⟩⟩

/-- `initL2` by the upgrader: L1 is chain `1`, owner `0x99`, ZK asset id `0x2a`. -/
def wInit : Tx := .initL2 0x800f 1 0x99 0x2a

/-- The bootloader sets the protocol fee to `3` per call. -/
def wSetFee : Tx := .setInteropFee 0x8001 3

/-- An L2→L2 send to chain `272` with the same base token: one direct call carrying `4`, one
indirect call passing `5`, base-token fee `3 * 2`, so `msg.value = 4 + 5 + 6`. -/
def wSendA : SendInput := ⟨0x50, 0x77, 15, 272, wBase, [wDirect 4, wIndirect 5], false, 0⟩

/-- A fixed-fee L2→L2 send to chain `272` with a different base token: one direct call carrying
`7` (deposited through the router), no base-token fee, so `msg.value = 0`; the vault resolves the
ZK token to `wZk`. -/
def wSendB : SendInput := ⟨0x51, 0x77, 0, 272, wOtherBase, [wDirect 7], true, wZk⟩

/-- An L2→L1 withdrawal: one indirect zero-value call through the router passing `8`; L2→L1 is
free, so `msg.value = 8`. -/
def wSendC : SendInput := ⟨0x52, 0x77, 8, 1, wBase, [wIndirect 8], false, 0⟩

/-- The witness run: initialise, set the fee, the three sends, then `2` forced in. -/
def wTxs : List Tx :=
  [wInit, wSetFee, .send wSendA, .send wSendB, .send wSendC, .nativeInflow 2]

/-- The underpaid withdrawal of the value-check countermodel: as `wSendC` passing `6`, with no
`msg.value`. -/
def wSendUnderpaid : SendInput := ⟨0x52, 0x77, 0, 1, wBase, [wIndirect 6], false, 0⟩

/-- A zero-call L2→L2 send. -/
def wSendEmpty : SendInput := ⟨0x53, 0x77, 0, 272, wBase, [], false, 0⟩

end Contracts.InteropCenter.FeeState
