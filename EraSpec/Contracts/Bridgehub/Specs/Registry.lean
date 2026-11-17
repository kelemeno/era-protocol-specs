import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `L1Bridgehub` — the chain registry, settlement-layer bookkeeping, and requests

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`,
files `l1-contracts/contracts/core/bridgehub/BridgehubBase.sol` (written `BB:` below) and
`l1-contracts/contracts/core/bridgehub/L1Bridgehub.sol` (written `L1:` below).

**This file is definitions only.** The guarantees are stated in
`EraSpec.Contracts.Bridgehub.Properties.Registry` and proved in
`EraSpec.Contracts.Bridgehub.Proofs.Registry`.

## What is modelled

All of the Bridgehub's storage that a non-view entry point writes (`BB:66-130`), and every
non-view external entry point of `L1Bridgehub` as one `Action`, executed by `exec`:

* administration: `setPendingAdmin`/`acceptAdmin` (`BB:179-204`), OpenZeppelin
  `Ownable2Step` (`transferOwnership`, `acceptOwnership`, `renounceOwnership`),
  `setAddresses` (`L1:268-280`), `setAddressesV31` (`BB:219-221`), `pause`/`unpause`
  (`BB:544-551`, OpenZeppelin `Pausable`: `whenNotPaused` / `whenPaused`);
* the registries: `addChainTypeManager`, `removeChainTypeManager`, `addTokenAssetId`,
  `setCTMAssetAddress` (`BB:227-293`);
* chain registration: `createNewChain` (`L1:108-139`), `registerAlreadyDeployedZKChain`
  (`L1:285-319`), both through `_validateChainParams` (`BB:491-537`) and
  `_registerNewZKChain` (`BB:301-307`); and the chain asset handler's
  `registerNewZKChain` (`BB:483-489`);
* settlement-layer bookkeeping: `setSettlementLayerStatus` (`L1:94-100`) and the three
  migration hooks `forwardedBridgeBurnSetSettlementLayer`, `forwardedBridgeMint`,
  `forwardedBridgeConfirmTransferResult` (`BB:403-468`);
* the two request entry points `requestL2TransactionDirect` (`L1:146-187`) and
  `requestL2TransactionTwoBridges` (`L1:200-265`), through `_sendRequest`
  (`BB:366-381`). They write no Bridgehub storage; what they forward is the `Outcome`.

A revert is the absence of a step (`exec` returns `none`). Guards are written in source
order. Modifiers are checked before the body, in the order they are listed.

## Modelling choices

* Addresses, chain ids, asset ids and values are 256-bit words (`UInt256`).
* `zkChainMap` (an OpenZeppelin v4.9 `EnumerableMap.UintToAddressMap`) is a key set
  `zkKeys` plus a value function `zkAddr`. `set` (`BB:303`) inserts the key and overwrites
  the value; `get` (`BB:378`, `BB:419`) reverts unless the value is nonzero or the key is
  present (`EnumerableMap.sol:137-141`); `tryGet` (`BB:346`, `L1:290`) returns `0` for an
  absent key; `length` is the key count.
* External calls are inputs. The CTM's `createNewChain` return value (`L1:124`), the
  deployed diamond's getters (`L1:294-302`), the second bridge's reply (`L1:232`), and
  `actualRefundRecipient` when no recipient is given (`AddressAliasHelper.sol:56-80`,
  it reads `tx.origin` and code size) are supplied by the caller of `exec`. A call that
  reverts makes the whole entry point revert, which is the absence of a step. Calls to the
  message root (`L1:134-135`, `L1:316`), the asset router (`L1:164`, `L1:223`), the
  Mailbox (`BB:380`) and the second bridge's confirmation (`L1:260`) are assumed to write
  no Bridgehub storage and are otherwise not modelled.
* The calls are atomic. `createNewChain` calls the CTM after writing the chain's CTM, base
  token and settlement layer (`L1:116-127`); a re-entrant call from the CTM into a
  Bridgehub function without `nonReentrant` is not modelled (ASSUMPTIONS `MODEL-BRIDGEHUB`).
* `setCTMAssetAddress` runs on L1, where `_getL1ChainId() == block.chainid`, so the sender
  is `msg.sender` without unaliasing (`BB:280`).
* `DataEncoding.encodeAssetId` (`keccak256(abi.encode(chainId, sender, data))`) is an
  uninterpreted function `Config.encodeAssetId`. No injectivity is assumed anywhere.

## What is not modelled

Events; view functions other than `getZKChain`; `initialize`'s reentrancy-guard
initializer (the starting state is `init`); the `nonReentrant` lock itself; the
`L2Bridgehub` variant; storage gaps and deprecated slots (never written).
-/

namespace Contracts.Bridgehub

open Clear

abbrev Address := UInt256
abbrev ChainId := UInt256
abbrev AssetId := UInt256

/-- Deployment constants. -/
structure Config where
  /-- `block.chainid`, which on L1 is also `L1_CHAIN_ID` (`L1:56`). -/
  thisChain : ChainId
  /-- `address(this)`. -/
  self : Address
  /-- `ETH_TOKEN_ASSET_ID` (`L1:63`). -/
  ethAssetId : AssetId
  /-- `MAX_NUMBER_OF_ZK_CHAINS` (`L1:58`). -/
  maxChains : ℕ
  /-- `L2_COMPLEX_UPGRADER_ADDR`, the other caller `onlyOwnerOrUpgrader` admits (`BB:146-151`). -/
  upgrader : Address
  /-- `TWO_BRIDGES_MAGIC_VALUE` (`Config.sol:206`). -/
  twoBridgesMagic : UInt256
  /-- `DataEncoding.encodeAssetId(chainId, data, sender)` (`DataEncoding.sol:125-127`),
  a keccak; uninterpreted. Arguments: chain id, asset data, sender. -/
  encodeAssetId : ChainId → UInt256 → Address → AssetId

/-- `HARD_CODED_CHAIN_ID` (`Config.sol:33`). -/
def hardCodedChainId : ChainId := 270
/-- `MAINNET_CHAIN_ID` (`Config.sol:86`). -/
def mainnetChainId : ChainId := 1
/-- `SEPOLIA_CHAIN_ID` (`Config.sol:89`). -/
def sepoliaChainId : ChainId := 11155111
/-- `BRIDGEHUB_MIN_SECOND_BRIDGE_ADDRESS = address(uint160(type(uint16).max))` (`Config.sol:209`). -/
def minSecondBridgeAddress : Address := 65535

/-- The Bridgehub's storage (`BB:66-130` plus the OpenZeppelin `Ownable2Step` and
`Pausable` slots). Mappings to `bool` are `Bool`-valued functions; unset entries are `0` /
`false`. -/
structure State where
  /-- `Ownable.owner()`. -/
  owner : Address
  /-- `Ownable2Step.pendingOwner()`. -/
  pendingOwner : Address
  /-- `admin` (`BB:82`). -/
  admin : Address
  /-- `pendingAdmin` (`BB:85`). -/
  pendingAdmin : Address
  /-- `Pausable.paused()`. -/
  paused : Bool
  /-- `assetRouter` (`BB:66`). -/
  assetRouter : Address
  /-- `l1CtmDeployer` (`BB:100`). -/
  l1CtmDeployer : Address
  /-- `messageRoot` (`BB:93`). -/
  messageRoot : Address
  /-- `chainAssetHandler` (`BB:124`). -/
  chainAssetHandler : Address
  /-- `chainRegistrationSender` (`BB:130`). -/
  chainRegistrationSender : Address
  /-- `chainTypeManagerIsRegistered` (`BB:69`). -/
  ctmRegistered : Address → Bool
  /-- `chainTypeManager[chainId]` (`BB:75`). -/
  chainTypeManager : ChainId → Address
  /-- The key set of `zkChainMap` (`BB:88`). -/
  zkKeys : Finset ChainId
  /-- The values of `zkChainMap`. -/
  zkAddr : ChainId → Address
  /-- `baseTokenAssetId[chainId]` (`BB:96`). -/
  baseTokenAssetId : ChainId → AssetId
  /-- `ctmAssetIdToAddress` (`BB:103`). -/
  ctmAssetIdToAddress : AssetId → Address
  /-- `ctmAssetIdFromAddress` (`BB:106`). -/
  ctmAssetIdFromAddress : Address → AssetId
  /-- `settlementLayer[chainId]` (`BB:109`). -/
  settlementLayer : ChainId → ChainId
  /-- `whitelistedSettlementLayers` (`BB:115`). -/
  whitelistedSL : ChainId → Bool
  /-- `assetIdIsRegistered` (`BB:118`). -/
  assetIdRegistered : AssetId → Bool

/-- The state after the proxy's `initialize(owner)` (`L1:71-74`): the owner is set,
`_initializeInner` registers the ETH asset id and whitelists L1 (`BB:169-172`), and every
other slot is zero. `setAddresses` comes later (`BB:206-207`). -/
def init (cfg : Config) (owner : Address) : State where
  owner := owner
  pendingOwner := 0
  admin := 0
  pendingAdmin := 0
  paused := false
  assetRouter := 0
  l1CtmDeployer := 0
  messageRoot := 0
  chainAssetHandler := 0
  chainRegistrationSender := 0
  ctmRegistered := fun _ => false
  chainTypeManager := fun _ => 0
  zkKeys := ∅
  zkAddr := fun _ => 0
  baseTokenAssetId := fun _ => 0
  ctmAssetIdToAddress := fun _ => 0
  ctmAssetIdFromAddress := fun _ => 0
  settlementLayer := fun _ => 0
  whitelistedSL := fun c => decide (c = cfg.thisChain)
  assetIdRegistered := fun a => decide (a = cfg.ethAssetId)

/-! ## `zkChainMap` -/

/-- `zkChainMap.tryGet(c)` / `getZKChain(c)` (`BB:344-347`): the stored address, or `0`
for an absent key. -/
def getZKChain (s : State) (c : ChainId) : Address :=
  if c ∈ s.zkKeys then s.zkAddr c else 0

/-- `zkChainMap.get(c)` does not revert (`EnumerableMap.sol:139`). -/
def ZkGetOk (s : State) (c : ChainId) : Prop := s.zkAddr c ≠ 0 ∨ c ∈ s.zkKeys

instance (s : State) (c : ChainId) : Decidable (ZkGetOk s c) := by
  unfold ZkGetOk; infer_instance

/-- `_registerNewZKChain(c, z, check)` (`BB:301-307`): `zkChainMap.set(c, z)`, then the
chain-count limit if `check`. -/
def registerNew (cfg : Config) (s : State) (c : ChainId) (z : Address) (check : Bool) :
    Option State :=
  if check = true ∧ (insert c s.zkKeys).card > cfg.maxChains then none   -- ZKChainLimitReached
  else some { s with zkKeys := insert c s.zkKeys, zkAddr := Function.update s.zkAddr c z }

/-! ## `_validateChainParams` -/

/-- `_validateChainParams(c, a, ctm)` (`BB:491-537`) passes. The conjuncts are in source
order. -/
def ValidChainParams (cfg : Config) (s : State) (c : ChainId) (a : AssetId) (ctm : Address) :
    Prop :=
  c ≠ 0 ∧                                                       -- ZeroChainId          :492
  c.val < 2 ^ 48 ∧                                              -- ChainIdTooBig        :497
  c ≠ cfg.thisChain ∧                                           -- ChainIdCantBeCurrent :501
  ¬ (c = hardCodedChainId ∧
      (cfg.thisChain = mainnetChainId ∨ cfg.thisChain = sepoliaChainId)) ∧ -- Hardcoded :510
  ctm ≠ 0 ∧                                                     -- ZeroAddress          :516
  a ≠ 0 ∧                                                       -- EmptyAssetId         :519
  s.ctmRegistered ctm = true ∧                                  -- CTMNotRegistered     :523
  s.assetIdRegistered a = true ∧                                -- AssetIdNotSupported  :527
  s.assetRouter ≠ 0 ∧                                           -- SharedBridgeNotSet   :531
  s.chainTypeManager c = 0                                      -- BridgeHubAlreadyRegistered :534

instance (cfg : Config) (s : State) (c : ChainId) (a : AssetId) (ctm : Address) :
    Decidable (ValidChainParams cfg s c a ctm) := by
  unfold ValidChainParams; infer_instance

/-- The chain-specific writes shared by `createNewChain` (`L1:116-119`) and
`registerAlreadyDeployedZKChain` (`L1:310-313`). -/
def writeChain (cfg : Config) (s : State) (c : ChainId) (ctm : Address) (a : AssetId) : State :=
  { s with
    chainTypeManager := Function.update s.chainTypeManager c ctm
    baseTokenAssetId := Function.update s.baseTokenAssetId c a
    settlementLayer := Function.update s.settlementLayer c cfg.thisChain }

/-! ## Requests -/

/-- The fields of `L2TransactionRequestDirect` (`IBridgehubBase.sol:10-20`) that the
Bridgehub reads; calldata, gas fields and factory deps are passed through unchanged. -/
structure DirectRequest where
  chainId : ChainId
  mintValue : UInt256
  l2Contract : Address
  l2Value : UInt256
  refundRecipient : Address

/-- The fields of `L2TransactionRequestTwoBridgesOuter` (`IBridgehubBase.sol:22-32`) that
the Bridgehub reads. -/
structure TwoBridgesRequest where
  chainId : ChainId
  mintValue : UInt256
  l2Value : UInt256
  refundRecipient : Address
  secondBridgeAddress : Address
  secondBridgeValue : UInt256

/-- The second bridge's reply (`L2TransactionRequestTwoBridgesInner`,
`IBridgehubBase.sol:34-40`), as far as the Bridgehub reads it. -/
structure SecondBridgeReply where
  magicValue : UInt256
  l2Contract : Address

/-- The call's environment: `msg.value`, and what `actualRefundRecipient(0, msg.sender)`
returns (the caller, or its alias; `AddressAliasHelper.sol:60-80`). -/
structure CallEnv where
  msgValue : UInt256
  defaultRefund : Address

/-- What a successful request forwards. -/
structure Outcome where
  /-- `bridgehubDepositBaseToken(chainId, assetId, sender, amount)` arguments. -/
  depositChainId : ChainId
  depositAssetId : AssetId
  depositSender : Address
  depositAmount : UInt256
  /-- ETH attached to `bridgehubDepositBaseToken`. -/
  ethToAssetRouter : ℕ
  /-- ETH attached to the second bridge's `bridgehubDeposit` (zero for the direct path). -/
  ethToSecondBridge : ℕ
  /-- The diamond whose `bridgehubRequestL2Transaction` is called. -/
  target : Address
  /-- The `BridgehubL2TransactionRequest` fields the Bridgehub sets. -/
  l2Sender : Address
  l2Contract : Address
  mintValue : UInt256
  l2Value : UInt256
  refundRecipient : Address

/-- `actualRefundRecipient(r, msg.sender).recipient` (`AddressAliasHelper.sol:56-59`). -/
def refundOf (env : CallEnv) (r : Address) : Address :=
  if r ≠ 0 then r else env.defaultRefund

/-- `requestL2TransactionDirect` (`L1:146-187`). -/
def requestDirect (cfg : Config) (s : State) (caller : Address) (env : CallEnv)
    (req : DirectRequest) : Option Outcome :=
  if s.paused = true then none                                             -- whenNotPaused :148
  else if s.baseTokenAssetId req.chainId = cfg.ethAssetId ∧ env.msgValue ≠ req.mintValue
    then none                                                              -- MsgValueMismatch :154
  else if s.baseTokenAssetId req.chainId ≠ cfg.ethAssetId ∧ env.msgValue ≠ 0
    then none                                                              -- MsgValueMismatch :158
  else if ¬ ZkGetOk s req.chainId then none                                -- zkChainMap.get BB:378
  else some
    { depositChainId := req.chainId
      depositAssetId := s.baseTokenAssetId req.chainId                     -- :152, :164-169
      depositSender := caller
      depositAmount := req.mintValue
      ethToAssetRouter := env.msgValue.val                                 -- :164
      ethToSecondBridge := 0
      target := s.zkAddr req.chainId                                       -- BB:378-380
      l2Sender := caller                                                   -- :176
      l2Contract := req.l2Contract
      mintValue := req.mintValue                                           -- :178
      l2Value := req.l2Value
      refundRecipient := refundOf env req.refundRecipient }                -- BB:376-377

/-- `requestL2TransactionTwoBridges` (`L1:200-265`). `mintValue + secondBridgeValue` is
checked arithmetic (Solidity 0.8): an overflow reverts. -/
def requestTwoBridges (cfg : Config) (s : State) (caller : Address) (env : CallEnv)
    (req : TwoBridgesRequest) (reply : SecondBridgeReply) : Option Outcome :=
  if s.paused = true then none                                             -- whenNotPaused :202
  else if req.secondBridgeAddress ≤ minSecondBridgeAddress then none      -- SecondBridgeAddressTooLow :203
  else if s.baseTokenAssetId req.chainId = cfg.ethAssetId ∧
      req.mintValue.val + req.secondBridgeValue.val ≥ UInt256.size then none -- checked add :211
  else if s.baseTokenAssetId req.chainId = cfg.ethAssetId ∧
      env.msgValue.val ≠ req.mintValue.val + req.secondBridgeValue.val
    then none                                                              -- MsgValueMismatch :211
  else if s.baseTokenAssetId req.chainId ≠ cfg.ethAssetId ∧
      env.msgValue ≠ req.secondBridgeValue then none                       -- MsgValueMismatch :216
  else if reply.magicValue ≠ cfg.twoBridgesMagic then none                 -- WrongMagicValue :240
  else if ¬ ZkGetOk s req.chainId then none                                -- zkChainMap.get BB:378
  else some
    { depositChainId := req.chainId
      depositAssetId := s.baseTokenAssetId req.chainId                     -- :208, :223-228
      depositSender := caller
      depositAmount := req.mintValue
      ethToAssetRouter :=                                                  -- :214, :219
        if s.baseTokenAssetId req.chainId = cfg.ethAssetId then req.mintValue.val else 0
      ethToSecondBridge := req.secondBridgeValue.val                       -- :233
      target := s.zkAddr req.chainId                                       -- BB:378-380
      l2Sender := req.secondBridgeAddress                                  -- :248
      l2Contract := reply.l2Contract                                       -- :249
      mintValue := req.mintValue                                           -- :250
      l2Value := req.l2Value
      refundRecipient := refundOf env req.refundRecipient }                -- BB:376-377

/-! ## Entry points -/

/-- What `registerAlreadyDeployedZKChain` reads from the diamond (`L1:294-302`). -/
structure DeployedChainInfo where
  chainId : ChainId
  ctm : Address
  baseTokenAssetId : AssetId
  bridgehub : Address

/-- Every non-view external entry point of `L1Bridgehub`. Inputs that come back from
external calls are arguments (see the header). -/
inductive Action
  | setPendingAdmin (newPending : Address)
  | acceptAdmin
  | transferOwnership (newOwner : Address)
  | acceptOwnership
  | renounceOwnership
  | setAddresses (assetRouter deployer messageRoot handler sender : Address)
  | setAddressesV31 (sender : Address)
  | addChainTypeManager (ctm : Address)
  | removeChainTypeManager (ctm : Address)
  | addTokenAssetId (a : AssetId)
  | setCTMAssetAddress (data : UInt256) (assetAddress : Address)
  | registerNewZKChain (c : ChainId) (z : Address) (check : Bool)
  | burnSetSettlementLayer (c newSL : ChainId)
  | forwardedBridgeMint (assetId : AssetId) (c : ChainId) (baseAsset : AssetId)
  | confirmTransferResult (c : ChainId) (failure : Bool)
  /-- `deployed` is the CTM's `createNewChain` return value (`L1:124`). -/
  | createNewChain (c : ChainId) (ctm : Address) (baseAsset : AssetId) (chainAdmin : Address)
      (deployed : Address)
  | registerAlreadyDeployed (c : ChainId) (z : Address) (info : DeployedChainInfo)
  | setSettlementLayerStatus (sl : ChainId) (whitelisted : Bool)
  | pause
  | unpause
  | requestDirect (env : CallEnv) (req : DirectRequest)
  | requestTwoBridges (env : CallEnv) (req : TwoBridgesRequest) (reply : SecondBridgeReply)

/-- One call, by `caller`. `none` is a revert. -/
def exec (cfg : Config) (caller : Address) : Action → State → Option State
  | .setPendingAdmin p, s =>                                               -- BB:179-188
      if caller ≠ s.admin ∧ caller ≠ s.owner then none                     -- onlyOwnerOrAdmin
      else if p = 0 then none                                              -- ZeroAddress
      else some { s with pendingAdmin := p }
  | .acceptAdmin, s =>                                                     -- BB:191-204
      if caller ≠ s.pendingAdmin then none
      else some { s with admin := s.pendingAdmin, pendingAdmin := 0 }
  | .transferOwnership o, s =>                                             -- Ownable2Step
      if caller ≠ s.owner then none else some { s with pendingOwner := o }
  | .acceptOwnership, s =>                                                 -- Ownable2Step
      if caller ≠ s.pendingOwner then none
      else some { s with owner := caller, pendingOwner := 0 }
  | .renounceOwnership, s =>                                               -- Ownable(2Step)
      if caller ≠ s.owner then none else some { s with owner := 0, pendingOwner := 0 }
  | .setAddresses ar dep mr h snd, s =>                                    -- L1:268-280
      if caller ≠ s.owner ∧ caller ≠ cfg.upgrader then none               -- onlyOwnerOrUpgrader
      else some { s with assetRouter := ar, l1CtmDeployer := dep, messageRoot := mr,
                         chainAssetHandler := h, chainRegistrationSender := snd }
  | .setAddressesV31 snd, s =>                                             -- BB:219-221
      if caller ≠ s.owner ∧ caller ≠ cfg.upgrader then none
      else some { s with chainRegistrationSender := snd }
  | .addChainTypeManager m, s =>                                           -- BB:227-237
      if caller ≠ s.owner then none                                        -- onlyOwner
      else if m = 0 then none                                              -- ZeroAddress
      else if s.ctmRegistered m = true then none                           -- CTMAlreadyRegistered
      else some { s with ctmRegistered := Function.update s.ctmRegistered m true }
  | .removeChainTypeManager m, s =>                                        -- BB:242-252
      if caller ≠ s.owner then none
      else if m = 0 then none
      else if s.ctmRegistered m = false then none                          -- CTMNotRegistered
      else some { s with ctmRegistered := Function.update s.ctmRegistered m false }
  | .addTokenAssetId a, s =>                                               -- BB:256-263
      if caller ≠ s.admin ∧ caller ≠ s.owner then none                     -- onlyOwnerOrAdmin
      else if s.assetIdRegistered a = true then none                       -- AssetIdAlreadyRegistered
      else some { s with assetIdRegistered := Function.update s.assetIdRegistered a true }
  | .setCTMAssetAddress d m, s =>                                          -- BB:268-293
      if caller ≠ s.l1CtmDeployer then none                                -- Unauthorized :282
      else if s.ctmRegistered m = false then none                          -- CTMNotRegistered :285
      else
        some { s with                                                      -- :289-291
          ctmAssetIdToAddress :=
            Function.update s.ctmAssetIdToAddress (cfg.encodeAssetId cfg.thisChain d caller) m
          ctmAssetIdFromAddress :=
            Function.update s.ctmAssetIdFromAddress m (cfg.encodeAssetId cfg.thisChain d caller) }
  | .registerNewZKChain c z chk, s =>                                      -- BB:483-489
      if caller ≠ s.chainAssetHandler then none                            -- onlyChainAssetHandler
      else registerNew cfg s c z chk
  | .burnSetSettlementLayer c sl, s =>                                     -- BB:403-421
      if caller ≠ s.chainAssetHandler then none
      else if s.whitelistedSL sl = false then none                         -- SLNotWhitelisted :407
      else if s.settlementLayer c ≠ cfg.thisChain then none                -- NotCurrentSettlementLayer :411
      else if s.whitelistedSL c = true then none                           -- SettlementLayersMustSettleOnL1 :416
      else if ¬ ZkGetOk s c then none                                      -- zkChainMap.get :419
      else some { s with settlementLayer := Function.update s.settlementLayer c sl }
  | .forwardedBridgeMint aid c base, s =>                                  -- BB:432-453
      if caller ≠ s.chainAssetHandler then none
      else if s.ctmAssetIdToAddress aid = 0 then none                      -- NoCTMForAssetId :438
      else if s.settlementLayer c = cfg.thisChain then none                -- AlreadyCurrentSL :441
      else some { s with
        settlementLayer := Function.update s.settlementLayer c cfg.thisChain
        chainTypeManager := Function.update s.chainTypeManager c (s.ctmAssetIdToAddress aid)
        baseTokenAssetId := Function.update s.baseTokenAssetId c base
        assetIdRegistered := Function.update s.assetIdRegistered base true }
  | .confirmTransferResult c failure, s =>                                 -- BB:459-468
      if caller ≠ s.chainAssetHandler then none
      else if failure = true then
        some { s with settlementLayer := Function.update s.settlementLayer c cfg.thisChain }
      else some s
  | .createNewChain c m a _adm dep, s =>                                   -- L1:108-139
      if caller ≠ s.admin ∧ caller ≠ s.owner then none                     -- onlyOwnerOrAdmin
      else if s.paused = true then none                                    -- whenNotPaused
      else if ¬ ValidChainParams cfg s c a m then none                     -- :114
      else if dep = 0 then none                                            -- ZeroAddress :129
      else registerNew cfg (writeChain cfg s c m a) c dep true             -- :116-119, :133
  | .registerAlreadyDeployed c z info, s =>                                -- L1:285-319
      if caller ≠ s.owner then none                                        -- onlyOwner
      else if z = 0 then none                                              -- ZeroAddress :286
      else if c ∈ s.zkKeys then none                                       -- ChainIdAlreadyExists :291
      else if info.chainId ≠ c then none                                   -- ChainIdMismatch :294
      else if info.bridgehub ≠ cfg.self then none                          -- IncorrectBridgeHubAddress :304
      else if ¬ ValidChainParams cfg s c info.baseTokenAssetId info.ctm then none -- :308
      else registerNew cfg (writeChain cfg s c info.ctm info.baseTokenAssetId) c z true -- :310-315
  | .setSettlementLayerStatus sl b, s =>                                   -- L1:94-100
      if caller ≠ s.owner then none
      else if s.settlementLayer sl ≠ cfg.thisChain then none               -- SettlementLayersMustSettleOnL1
      else some { s with whitelistedSL := Function.update s.whitelistedSL sl b }
  | .pause, s =>                                                           -- BB:544-546
      if caller ≠ s.owner then none else if s.paused = true then none
      else some { s with paused := true }
  | .unpause, s =>                                                         -- BB:549-551
      if caller ≠ s.owner then none else if s.paused = false then none
      else some { s with paused := false }
  | .requestDirect env req, s =>                                           -- L1:146-187
      (requestDirect cfg s caller env req).map fun _ => s
  | .requestTwoBridges env req reply, s =>                                 -- L1:200-265
      (requestTwoBridges cfg s caller env req reply).map fun _ => s

/-! ## Runs -/

/-- A call: the caller and the entry point with its arguments. -/
abbrev Call := Address × Action

/-- `Run cfg s l t`: the calls `l`, in order, all succeed from `s` and end in `t`. Reverted
calls are not part of a run; any interleaving of callers and entry points is. -/
inductive Run (cfg : Config) : State → List Call → State → Prop
  | nil (s : State) : Run cfg s [] s
  | snoc {s t u : State} {l : List Call} (k : Call) :
      Run cfg s l t → exec cfg k.1 k.2 t = some u → Run cfg s (l ++ [k]) u

/-- A state some run reaches from an initialized Bridgehub. -/
def Reachable (cfg : Config) (s : State) : Prop :=
  ∃ owner l, Run cfg (init cfg owner) l s

/-! ## Labels on calls -/

/-- The call registers chain `c` through `createNewChain` or
`registerAlreadyDeployedZKChain`. -/
def Action.registers (c : ChainId) : Action → Bool
  | .createNewChain c' .. => decide (c' = c)
  | .registerAlreadyDeployed c' .. => decide (c' = c)
  | _ => false

/-- The call is `forwardedBridgeMint` for chain `c`. -/
def Action.bridgeMintFor (c : ChainId) : Action → Bool
  | .forwardedBridgeMint _ c' _ => decide (c' = c)
  | _ => false

/-- The call is `forwardedBridgeBurnSetSettlementLayer` for chain `c` (the only entry point
that moves a chain's settlement layer away from this chain). -/
def Action.burnFor (c : ChainId) : Action → Bool
  | .burnSetSettlementLayer c' _ => decide (c' = c)
  | _ => false

/-- The call is one of the chain asset handler's two writers of `zkChainMap` /
`chainTypeManager` (`registerNewZKChain`, `forwardedBridgeMint`). -/
def Action.handlerRegistryWrite : Action → Bool
  | .registerNewZKChain .. => true
  | .forwardedBridgeMint .. => true
  | _ => false

/-- The call is `registerNewZKChain` for chain `c` (the only entry point that can replace
the stored diamond of a chain that already has a CTM). -/
def Action.handlerRegistersFor (c : ChainId) : Action → Bool
  | .registerNewZKChain c' _ _ => decide (c' = c)
  | _ => false

/-- The call is `registerNewZKChain(_, _, false)`, which skips the chain-count limit. -/
def Action.uncheckedRegistration : Action → Bool
  | .registerNewZKChain _ _ chk => !chk
  | _ => false

/-- The call is not a `setCTMAssetAddress(data, m)` with `data ≠ m`. `CTMDeploymentTracker`,
the intended `l1CtmDeployer`, always passes `data = bytes32(uint256(uint160(m)))`
(`CTMDeploymentTracker.sol:79`), i.e. `data = m` as words. -/
def Action.ctmAssetDisciplined : Action → Bool
  | .setCTMAssetAddress d m => decide (d = m)
  | _ => true

/-! ## Variants with one source check removed

Used only by the countermodels in `Properties.Registry`, to show that check is
load-bearing. Each is the corresponding entry point with exactly one guard deleted. -/

/-- `createNewChain` without the `BridgeHubAlreadyRegistered` check (`BB:534-536`). -/
def createNewChainNoDupCheck (cfg : Config) (caller : Address) (s : State) (c : ChainId)
    (m : Address) (a : AssetId) (dep : Address) : Option State :=
  if caller ≠ s.admin ∧ caller ≠ s.owner then none
  else if s.paused = true then none
  else if ¬ (c ≠ 0 ∧ c.val < 2 ^ 48 ∧ c ≠ cfg.thisChain ∧
      ¬ (c = hardCodedChainId ∧
        (cfg.thisChain = mainnetChainId ∨ cfg.thisChain = sepoliaChainId)) ∧
      m ≠ 0 ∧ a ≠ 0 ∧ s.ctmRegistered m = true ∧ s.assetIdRegistered a = true ∧
      s.assetRouter ≠ 0) then none
  else if dep = 0 then none
  else registerNew cfg (writeChain cfg s c m a) c dep true

/-- `forwardedBridgeBurnSetSettlementLayer` without the `SettlementLayersMustSettleOnL1`
check (`BB:416-418`). -/
def burnNoSettlementLayerCheck (cfg : Config) (caller : Address) (s : State)
    (c sl : ChainId) : Option State :=
  if caller ≠ s.chainAssetHandler then none
  else if s.whitelistedSL sl = false then none
  else if s.settlementLayer c ≠ cfg.thisChain then none
  else if ¬ ZkGetOk s c then none
  else some { s with settlementLayer := Function.update s.settlementLayer c sl }

/-- `forwardedBridgeMint` without the `AlreadyCurrentSL` check (`BB:441-443`); otherwise
identical to the `forwardedBridgeMint` case of `exec`. -/
def forwardedBridgeMintNoCurrentSLCheck (cfg : Config) (caller : Address) (s : State)
    (aid : AssetId) (c : ChainId) (base : AssetId) : Option State :=
  if caller ≠ s.chainAssetHandler then none
  else if s.ctmAssetIdToAddress aid = 0 then none
  else some { s with
    settlementLayer := Function.update s.settlementLayer c cfg.thisChain
    chainTypeManager := Function.update s.chainTypeManager c (s.ctmAssetIdToAddress aid)
    baseTokenAssetId := Function.update s.baseTokenAssetId c base
    assetIdRegistered := Function.update s.assetIdRegistered base true }

/-- `requestL2TransactionTwoBridges` without the `SecondBridgeAddressTooLow` check
(`L1:203-205`); otherwise identical to `requestTwoBridges`. -/
def requestTwoBridgesNoMinAddress (cfg : Config) (s : State) (caller : Address) (env : CallEnv)
    (req : TwoBridgesRequest) (reply : SecondBridgeReply) : Option Outcome :=
  if s.paused = true then none
  else if s.baseTokenAssetId req.chainId = cfg.ethAssetId ∧
      req.mintValue.val + req.secondBridgeValue.val ≥ UInt256.size then none
  else if s.baseTokenAssetId req.chainId = cfg.ethAssetId ∧
      env.msgValue.val ≠ req.mintValue.val + req.secondBridgeValue.val then none
  else if s.baseTokenAssetId req.chainId ≠ cfg.ethAssetId ∧
      env.msgValue ≠ req.secondBridgeValue then none
  else if reply.magicValue ≠ cfg.twoBridgesMagic then none
  else if ¬ ZkGetOk s req.chainId then none
  else some
    { depositChainId := req.chainId
      depositAssetId := s.baseTokenAssetId req.chainId
      depositSender := caller
      depositAmount := req.mintValue
      ethToAssetRouter :=
        if s.baseTokenAssetId req.chainId = cfg.ethAssetId then req.mintValue.val else 0
      ethToSecondBridge := req.secondBridgeValue.val
      target := s.zkAddr req.chainId
      l2Sender := req.secondBridgeAddress
      l2Contract := reply.l2Contract
      mintValue := req.mintValue
      l2Value := req.l2Value
      refundRecipient := refundOf env req.refundRecipient }

end Contracts.Bridgehub
