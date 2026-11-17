import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: the Mailbox request paths of one diamond

Source: era-contracts `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5` (label
`head-v35-b17415d`). Paths are relative to `l1-contracts/contracts/`. A bare `:N` is a line of
`state-transition/chain-deps/facets/Mailbox.sol`. Other files are cited as

* `ZB` — `state-transition/chain-deps/facets/ZKChainBase.sol`,
* `PT` — `state-transition/libraries/PriorityTree.sol`,
* `DIM` — `common/libraries/DynamicIncrementalMerkle.sol`,
* `TV` — `state-transition/libraries/TransactionValidator.sol`,
* `AAH` — `vendor/AddressAliasHelper.sol`,
* `CFG` — `common/Config.sol`, `MSG` — `common/Messaging.sol`,
* `L2A` — `common/l2-helpers/L2ContractAddresses.sol`.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.MailboxFacet.Properties.RequestPaths`, proofs in
`EraSpec.Contracts.MailboxFacet.Proofs.RequestPaths`. The composition of several diamonds (the
relay into a settlement layer's tree, and who may call which entry on L1) is the topic
`EraSpec.Protocol.PriorityRequests` (`PrivilegedSenders`).

## The code

Four entry points of `MailboxFacet` append to the diamond's priority tree:

    bridgehubRequestL2Transaction(req)        onlyBridgehub (:92-96)
      → _requestL2TransactionSender (:198-230, nonReentrant)
          filterer (:202-215); require gasPerPubdata == 800 (:222-224)
      → _requestL2Transaction (:232-285)
          txId = total (:235); price = _deriveL2GasPrice(tx.gasprice, 800) (:238)
          require mintValue >= price * gasLimit (:239-244)
          refund recipient (:246-266); sender aliasing unless tx.origin or 7702 (:270-272)
          (tx, hash) = _validateTx (:274); _writePriorityOp (:276)
          if s.settlementLayer != 0: settlementLayer.requestL2TransactionToGatewayMailbox(...) (:277-284)
    requestL2ServiceTransaction(to, data)     onlyServiceTransaction onlyL1 (:169-196)
      → _requestL2TransactionFree(sender = SERVICE_TRANSACTION_SENDER, ...) (:173-186)
          if s.settlementLayer != 0: relay as above (:188-195)
    requestL2TransactionToGatewayMailbox(c, h, e)   onlyL1 (:110-130)
          whitelisted settlement layer (:115-117); getZKChain(c) == msg.sender (:118-120); e == 0
          → _requestL2TransactionFree(_wrapRequest(c, h, e)) (:124-129, :142-166)
    bridgehubRequestL2TransactionOnGateway(h, _)   onlyInteropCenter (:133-140)
          → _writePriorityOpHash(h) (:137)

    _requestL2TransactionFree (:291-303, nonReentrant): txId = total, l2GasPrice = 0,
        _validateTx, _writePriorityOp
    _serializeL2Transaction (:305-331): factoryDeps must be empty (:309-311); nonce = txId (:322)
    _validateTx (:333-344): serialize, TransactionValidator, hash = keccak256(abi.encode(tx))
    _writePriorityOp (:355-371): _writePriorityOpHash; on L1 require !depositsPaused() (:363-365)
    _writePriorityOpHash (:373-378): priorityTree.push(h);
        priorityOpsRequestTimestamp[total - 1] = block.timestamp

## Modelling choices (`MODEL-MAILBOX-REQUESTS` in `ASSUMPTIONS.md`)

* **One diamond.** `Diamond` holds the fields of `ZKChainStorage` the four paths read or write.
  The priority tree is its counters (`PT:28-33`): `startIndex`, `unprocessedIndex` and
  `nextLeafIndex` (`DIM`'s `_nextLeafIndex`). `getTotalPriorityTxs` is `startIndex +
  nextLeafIndex` (`PT:42-44`). The tree's frontier and `historicalRoots` are not modelled (the
  topic `PriorityTree` on branch `cov/mailbox` models them); instead the ghost map `leafAt`
  records the leaf pushed at each global index. That `DIM.push` stores the pushed leaf at index
  `_nextLeafIndex` and increments the counter by one (`DIM:92-137`) is what the ghost encodes.
* **Words are natural numbers with explicit reverts.** A checked `uint256` operation whose exact
  value does not fit reverts (`checkedWord`); a division by zero reverts. A revert is `none`.
  `getMinimalPriorityTransactionGasLimit` (`TV:107-130`) is computed in `ℕ`: its products overflow
  only for calldata longer than `2^256 / 40` bytes, which no call can carry.
* **External view calls are values of the environment** (`Env`): the filterer's
  `isTransactionAllowed`, the `EIP7702Checker`, `isMigrationInProgress` of the chain asset handler,
  and `code.length`. The first two interfaces declare their functions `view`
  (`state-transition/chain-interfaces/ITransactionFilterer.sol:17-24`, `IEIP7702Checker.sol:14`),
  and the third is read inside the `view` function `depositsPaused()` (:347-352), so the calls are
  static and cannot write state (`VM-CALL`).
* **Hashing and encoding are parameters.** `Params.txHash` is `keccak256(abi.encode(tx))`
  (:337, :343) and `Params.encForward` is `abi.encodeCall(IInteropCenter.forwardTransactionOnGateway,
  ...)` (:148-151). Nothing is assumed about either; no result here needs a hash premise.
* **The relay call is not part of this file.** `_requestL2Transaction` and
  `requestL2ServiceTransaction` call another diamond after their own push; the functions here stop
  at the push and the system model performs the call (`Contracts.PriorityRequests.userCall`).
* **Caller checks and events.** The modifiers `onlyBridgehub`, `onlyServiceTransaction`,
  `onlyInteropCenter`, `onlyL1` and the `getZKChain` / whitelist checks of
  `requestL2TransactionToGatewayMailbox` read other contracts; the system model applies them.
  `nonReentrant` is the system model's too. Events are not modelled.
* **`PAUSE_DEPOSITS_TIME_WINDOW_START` is `0`** on mainnet and testnet (`CFG:271`, `CFG:277`), so
  `depositsPaused()` (:347-352) is `pausedDepositsTimestamp != 0 && pausedDepositsTimestamp <=
  block.timestamp`, or a migration in progress on L1.

## Differences at `main` (`70096e2ea6eeb5373992e178064c4b26dcf6436a`), not modelled

This file does not model `main`. There `_serializeL2Transaction` hashes the factory dependencies
instead of rejecting them, `_requestL2Transaction` bounds their number by `MAX_NEW_FACTORY_DEPS`,
the two free paths use `l2GasLimit: 72_000_000`, `TransactionValidator` takes the encoding and
`s.zksyncOS`, and `bridgehubRequestL2TransactionOnGateway` is `onlyBridgehubOrInteropCenter`. The
lines for the index and nonce, the push and its timestamp, the fee floor and the aliasing read the
same at both commits (`git diff` of `Mailbox.sol` touches only the lines listed here), so the
statements about them would carry over; the statements about `factoryDeps` and the free paths'
gas limit would not.
-/

namespace Contracts.MailboxFacet.RequestPaths

/-! ## Words, addresses and constants -/

/-- An `address`: a 160-bit word. `uint160` arithmetic wraps (`AAH:30-32` is `unchecked`). -/
abbrev Address := Fin (2 ^ 160)

/-- A `bytes32` word: transaction hashes. -/
abbrev Word := UInt256

/-- `bytes`. -/
abbrev Bytes := List UInt8

/-- `2^256`: one past the largest `uint256`. -/
def requestWordLimit : ℕ := 2 ^ 256

/-- A checked `uint256` result: a revert (`none`) when the exact value does not fit. -/
def checkedWord (n : ℕ) : Option ℕ := if n < requestWordLimit then some n else none

/-- `REQUIRED_L2_GAS_PRICE_PER_PUBDATA = 800` (`CFG:157`). -/
def requiredGasPerPubdata : ℕ := 800

/-- `PRIORITY_TX_MAX_GAS_LIMIT = 1 << 24` (`CFG:197`): the `l2GasLimit` of the two free paths
(:159, :179). -/
def freePathGasLimit : ℕ := 2 ^ 24

/-- `ZKSYNC_OS_PRIORITY_OPERATION_L2_TX_TYPE = 127` (`CFG:64`), returned by `_getPriorityTxType`
(`ZB:196-198`). -/
def priorityOpTxType : ℕ := 127

/-- `SETTLEMENT_LAYER_RELAY_SENDER` (`CFG:219`). -/
def relaySender : Address := ⟨0x1111111111111111111111111111111111111111, by decide⟩

/-- `SERVICE_TRANSACTION_SENDER` (`CFG:264`). -/
def serviceSender : Address := ⟨0xFFfFfFffFFfffFFfFFfFFFFFffFFFffffFfFFFfF, by decide⟩

/-- `L2_INTEROP_CENTER_ADDR = 0x1000d` (`L2A:118`). -/
def l2InteropCenterAddr : Address := ⟨0x1000d, by decide⟩

/-- `L2_BRIDGEHUB_ADDR = 0x10002` (`L2A:81`). -/
def l2BridgehubAddr : Address := ⟨0x10002, by decide⟩

/-- `L2_CHAIN_ASSET_HANDLER_ADDR = 0x1000a` (`L2A:107`). -/
def l2ChainAssetHandlerAddr : Address := ⟨0x1000a, by decide⟩

/-- `AddressAliasHelper.offset` (`AAH:23`). -/
def aliasOffset : Address := ⟨0x1111000000000000000000000000000000001111, by decide⟩

/-- `applyL1ToL2Alias` (`AAH:29-33`): `uint160` addition of the offset, wrapping. -/
def applyL1ToL2Alias (a : Address) : Address := a + aliasOffset

/-- `undoL1ToL2Alias` (`AAH:39-43`): `uint160` subtraction of the offset, wrapping. -/
def undoL1ToL2Alias (a : Address) : Address := a - aliasOffset

/-! ## Calldata structures -/

/-- `BridgehubL2TransactionRequest` (`MSG:126-136`). -/
structure Request where
  sender : Address
  contractL2 : Address
  mintValue : ℕ
  l2Value : ℕ
  l2Calldata : Bytes
  l2GasLimit : ℕ
  l2GasPerPubdataByteLimit : ℕ
  factoryDeps : List Bytes
  refundRecipient : Address
deriving DecidableEq

/-- `L2CanonicalTransaction` (`MSG:87-114`). `from`, `to` and `reserved[1]` are `uint256` widenings
of addresses (:314-315, :324); the model keeps the address. `reserved` is split into its four
words. -/
structure L2Tx where
  txType : ℕ
  fromAddr : Address
  toAddr : Address
  gasLimit : ℕ
  gasPerPubdataByteLimit : ℕ
  maxFeePerGas : ℕ
  maxPriorityFeePerGas : ℕ
  paymaster : ℕ
  nonce : ℕ
  value : ℕ
  /-- `reserved[0]`: the `mintValue` (:324). -/
  reserved0 : ℕ
  /-- `reserved[1]`: the refund recipient (:324). -/
  reserved1 : Address
  reserved2 : ℕ
  reserved3 : ℕ
  data : Bytes
  signature : Bytes
  factoryDeps : List ℕ
  paymasterInput : Bytes
  reservedDynamic : Bytes
deriving DecidableEq

/-- `PubdataPricingMode` (`state-transition/chain-deps/ZKChainStorage.sol`). -/
inductive PubdataPricingMode where
  | rollup
  | validium
deriving DecidableEq

/-- `FeeParams` (`ZKChainStorage.sol:46-53`). -/
structure FeeParams where
  pubdataPricingMode : PubdataPricingMode
  batchOverheadL1Gas : ℕ
  maxPubdataPerBatch : ℕ
  maxL2GasPerBatch : ℕ
  priorityTxMaxPubdata : ℕ
  minimalL2GasPrice : ℕ
deriving DecidableEq

/-! ## The diamond, its deployment and the environment -/

/-- The fields of one diamond's `ZKChainStorage` that the request paths read or write. -/
structure Diamond where
  /-- `s.chainId`. -/
  chainId : ℕ
  /-- `s.settlementLayer`: `0` while the chain settles on this layer, otherwise the settlement
  layer's diamond on this layer. -/
  settlementLayer : Address
  /-- `s.transactionFilterer`. -/
  transactionFilterer : Address
  /-- `s.baseTokenGasPriceMultiplierNominator`. -/
  priceNominator : ℕ
  /-- `s.baseTokenGasPriceMultiplierDenominator`. -/
  priceDenominator : ℕ
  /-- `s.feeParams`. -/
  feeParams : FeeParams
  /-- `s.priorityTxMaxGasLimit`. -/
  priorityTxMaxGasLimit : ℕ
  /-- `s.pausedDepositsTimestamp`. -/
  pausedDepositsTimestamp : ℕ
  /-- `s.priorityTree.startIndex`. -/
  startIndex : ℕ
  /-- `s.priorityTree.unprocessedIndex`, relative to `startIndex`. -/
  unprocessedIndex : ℕ
  /-- `s.priorityTree.tree._nextLeafIndex`. -/
  nextLeafIndex : ℕ
  /-- Ghost: the leaf pushed at each global index. Not storage (`DIM` keeps only a frontier). -/
  leafAt : ℕ → Word
  /-- `s.priorityOpsRequestTimestamp`. -/
  requestTimestamp : ℕ → ℕ

/-- `getTotalPriorityTxs` (`PT:42-44`), before its overflow check. -/
def Diamond.total (d : Diamond) : ℕ := d.startIndex + d.nextLeafIndex

/-- `getFirstUnprocessedPriorityTx` (`PT:37-39`), before its overflow check. -/
def Diamond.firstUnprocessed (d : Diamond) : ℕ := d.startIndex + d.unprocessedIndex

/-- The facet's immutables and the two abstract functions it composes. -/
structure Params where
  /-- `L1_CHAIN_ID` (:62). -/
  l1ChainId : ℕ
  /-- `keccak256(abi.encode(transaction))` (:337, :343). -/
  txHash : L2Tx → Word
  /-- `abi.encodeCall(IInteropCenter.forwardTransactionOnGateway, (c, h, e))` (:148-151). -/
  encForward : ℕ → Word → ℕ → Bytes

/-- The transaction context of one call. -/
structure Env where
  /-- `block.chainid`. -/
  chainId : ℕ
  /-- `block.timestamp`. -/
  timestamp : ℕ
  /-- `tx.origin`. -/
  origin : Address
  /-- `tx.gasprice`. -/
  gasPrice : ℕ
  /-- `a.code.length != 0`. -/
  hasCode : Address → Bool
  /-- `EIP_7702_CHECKER.isEIP7702Account(a)` (a view call, `IEIP7702Checker.sol:14`). -/
  is7702 : Address → Bool
  /-- `ITransactionFilterer(f).isTransactionAllowed(...)` on the request's fields (a view call). -/
  filterAllows : Address → Request → Bool
  /-- `IL1ChainAssetHandler(CHAIN_ASSET_HANDLER).isMigrationInProgress(chainId)` (a view call). -/
  migrationInProgress : ℕ → Bool

/-- The call runs on L1: `block.chainid == L1_CHAIN_ID`. -/
def Env.onL1 (P : Params) (env : Env) : Prop := env.chainId = P.l1ChainId

instance (P : Params) (env : Env) : Decidable (env.onL1 P) := by
  unfold Env.onL1; infer_instance

/-! ## Gas price and validation -/

/-- `_deriveL2GasPrice(_l1GasPrice, _gasPerPubdata)` (`ZB:261-300`): it reverts on a zero
denominator (`ZB:262-264`), on an overflowing checked operation, on a division by zero, and on the
`- 1` underflow; `L1_GAS_PER_PUBDATA_BYTE = 17` (`CFG:151`). -/
def deriveL2GasPrice (d : Diamond) (l1GasPrice gasPerPubdata : ℕ) : Option ℕ :=
  if d.priceDenominator = 0 then none else
  match checkedWord (l1GasPrice * d.priceNominator) with
  | none => none
  | some prod =>
    let converted := prod / d.priceDenominator
    let pubdataPrice : Option ℕ :=
      match d.feeParams.pubdataPricingMode with
      | .rollup => checkedWord (17 * converted)
      | .validium => some 0
    match pubdataPrice with
    | none => none
    | some pubdataPrice =>
    match checkedWord (d.feeParams.batchOverheadL1Gas * converted) with
    | none => none
    | some batchOverhead =>
    if d.feeParams.maxPubdataPerBatch = 0 then none else
    match checkedWord (pubdataPrice + batchOverhead / d.feeParams.maxPubdataPerBatch) with
    | none => none
    | some fullPubdataPrice =>
    if d.feeParams.maxL2GasPerBatch = 0 then none else
    match checkedWord (d.feeParams.minimalL2GasPrice + batchOverhead / d.feeParams.maxL2GasPerBatch) with
    | none => none
    | some l2GasPrice =>
    match checkedWord (fullPubdataPrice + gasPerPubdata) with
    | none => none
    | some sum =>
    if sum = 0 then none else
    if gasPerPubdata = 0 then none else
    some (max l2GasPrice ((sum - 1) / gasPerPubdata))

/-- `getMinimalPriorityTransactionGasLimit(len, gasPerPubdata)` (`TV:107-130`) with
`L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS = 21000`, `L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS = 40`,
`L1_TX_INTRINSIC_PUBDATA_ZKSYNC_OS = 351`, and `Math.ceilDiv(1 << 35, 100_000_000) = 344`
(`CFG:168-182`). -/
def minimalPriorityTxGasLimit (calldataLength gasPerPubdata : ℕ) : ℕ :=
  max (21000 + 40 * calldataLength) (351 * gasPerPubdata + 344)

/-- `TransactionValidator.validateL1ToL2Transaction(tx, priorityTxMaxGasLimit, priorityTxMaxPubdata)`
(`TV:31-55`) does not revert. The division by `gasPerPubdataByteLimit` panics on zero. -/
def ValidL1ToL2 (tx : L2Tx) (maxGasLimit maxPubdata : ℕ) : Prop :=
  tx.gasLimit ≤ maxGasLimit ∧ tx.gasPerPubdataByteLimit ≠ 0 ∧
    tx.gasLimit / tx.gasPerPubdataByteLimit ≤ maxPubdata ∧
    minimalPriorityTxGasLimit tx.data.length tx.gasPerPubdataByteLimit ≤ tx.gasLimit

instance (tx : L2Tx) (a b : ℕ) : Decidable (ValidL1ToL2 tx a b) := by
  unfold ValidL1ToL2; infer_instance

/-! ## Serialization and the push -/

/-- `_serializeL2Transaction` (:305-331), given the request, `txId` and `l2GasPrice`: a revert on
nonempty `factoryDeps` (:309-311). -/
def serializeL2Transaction (req : Request) (txId l2GasPrice : ℕ) : Option L2Tx :=
  if req.factoryDeps ≠ [] then none else
  some
    { txType := priorityOpTxType
      fromAddr := req.sender
      toAddr := req.contractL2
      gasLimit := req.l2GasLimit
      gasPerPubdataByteLimit := req.l2GasPerPubdataByteLimit
      maxFeePerGas := l2GasPrice
      maxPriorityFeePerGas := 0
      paymaster := 0
      nonce := txId
      value := req.l2Value
      reserved0 := req.mintValue
      reserved1 := req.refundRecipient
      reserved2 := 0
      reserved3 := 0
      data := req.l2Calldata
      signature := []
      factoryDeps := []
      paymasterInput := []
      reservedDynamic := [] }

/-- `_validateTx` (:333-344): serialize, validate against the diamond's limits, hash. -/
def validateTx (P : Params) (d : Diamond) (req : Request) (txId l2GasPrice : ℕ) :
    Option (L2Tx × Word) :=
  match serializeL2Transaction req txId l2GasPrice with
  | none => none
  | some tx =>
    if ValidL1ToL2 tx d.priorityTxMaxGasLimit d.feeParams.priorityTxMaxPubdata then
      some (tx, P.txHash tx)
    else none

/-- The diamond after `_writePriorityOpHash(h)` at time `t` (:373-378): one more leaf, the leaf
and the request timestamp recorded at the old total. -/
def Diamond.pushLeaf (d : Diamond) (h : Word) (t : ℕ) : Diamond :=
  { d with
    nextLeafIndex := d.nextLeafIndex + 1
    leafAt := Function.update d.leafAt d.total h
    requestTimestamp := Function.update d.requestTimestamp d.total t }

/-- `_writePriorityOpHash(h)` (:373-378). `push` reverts only when `_nextLeafIndex++` overflows
(`DIM:99`) on a tree set up by `DiamondInit` (`state-transition/chain-deps/DiamondInit.sol:137`);
the following `getTotalPriorityTxs` reverts when the new total overflows (`PT:42-44`). Both are the
one guard below. -/
def writePriorityOpHash (d : Diamond) (t : ℕ) (h : Word) : Option Diamond :=
  if requestWordLimit ≤ d.total + 1 then none else some (d.pushLeaf h t)

/-- `_isInDepositsPausedWindow(PAUSE_DEPOSITS_TIME_WINDOW_START)` (`ZB:229-232`) with window start
`0`. -/
def inPausedWindow (d : Diamond) (t : ℕ) : Bool :=
  d.pausedDepositsTimestamp ≠ 0 && decide (d.pausedDepositsTimestamp ≤ t)

/-- `depositsPaused()` (:347-352). -/
def depositsPaused (P : Params) (d : Diamond) (env : Env) : Bool :=
  inPausedWindow d env.timestamp || (decide (env.onL1 P) && env.migrationInProgress d.chainId)

/-- `_writePriorityOp(tx, factoryDeps, h)` (:355-371): the push, then on L1 the deposit pause check
(:363-365), which reads fields the push leaves unchanged. -/
def writePriorityOp (P : Params) (d : Diamond) (env : Env) (h : Word) : Option Diamond :=
  match writePriorityOpHash d env.timestamp h with
  | none => none
  | some d' => if env.onL1 P ∧ depositsPaused P d' env = true then none else some d'

/-! ## The user path -/

/-- `AddressAliasHelper.actualRefundRecipient(rr, caller)` (`AAH:52-80`): the recipient and whether
its aliasing is final. -/
def actualRefundRecipient (env : Env) (rr caller : Address) : Address × Bool :=
  if rr ≠ 0 then (rr, false)
  else if caller = env.origin then (caller, true)
  else if env.hasCode caller then (caller, false)
  else (applyL1ToL2Alias caller, true)

/-- `AddressAliasHelper.applyRefundRecipientAlias(rr, is7702)` (`AAH:87-96`). -/
def applyRefundRecipientAlias (env : Env) (rr : Address) (is7702 : Bool) : Address :=
  if env.hasCode rr = false ∨ is7702 = true then rr else applyL1ToL2Alias rr

/-- `isEIP7702Account(request.sender)`, asked only on L1 (:254-255). -/
def senderIs7702 (P : Params) (env : Env) (sender : Address) : Bool :=
  decide (env.onL1 P) && env.is7702 sender

/-- The sender `_requestL2Transaction` writes into the request (:270-272): unchanged when it is
`tx.origin` or (on L1) an EIP-7702 account, otherwise aliased. -/
def l2Sender (P : Params) (env : Env) (sender : Address) : Address :=
  if sender ≠ env.origin ∧ senderIs7702 P env sender = false then applyL1ToL2Alias sender
  else sender

/-- The request after `_requestL2Transaction` rewrote its refund recipient (:246-266) and its
sender (:270-272). The source writes both through the memory reference `request`, which is
`_params.request`, so `_validateTx(_params)` (:274) serializes the rewritten request. -/
def rewriteRequest (P : Params) (env : Env) (req : Request) : Request :=
  let rr := actualRefundRecipient env req.refundRecipient req.sender
  let is7702Sender := senderIs7702 P env req.sender
  let is7702Refund : Bool :=
    if env.onL1 P ∧ rr.2 = false then
      (if rr.1 = req.sender then is7702Sender else env.is7702 rr.1)
    else false
  { req with
    refundRecipient := if rr.2 then rr.1 else applyRefundRecipientAlias env rr.1 is7702Refund
    sender := l2Sender P env req.sender }

/-- The diamond's own effect of `bridgehubRequestL2Transaction(req)` (:92-96): `_requestL2TransactionSender`
(:198-230) and `_requestL2Transaction` (:232-285) up to and including `_writePriorityOp` (:276).
It returns the new diamond, the serialized transaction and its hash. The relay call (:277-284)
is made by the caller of this function, `Contracts.PriorityRequests.userCall`. -/
def requestL2TransactionSender (P : Params) (d : Diamond) (env : Env) (req : Request) :
    Option (Diamond × L2Tx × Word) :=
  if d.transactionFilterer ≠ 0 ∧ env.filterAllows d.transactionFilterer req = false then none else
  if req.l2GasPerPubdataByteLimit ≠ requiredGasPerPubdata then none else
  match checkedWord d.total with
  | none => none
  | some txId =>
  match deriveL2GasPrice d env.gasPrice req.l2GasPerPubdataByteLimit with
  | none => none
  | some price =>
  match checkedWord (price * req.l2GasLimit) with
  | none => none
  | some baseCost =>
  if req.mintValue < baseCost then none else
  match validateTx P d (rewriteRequest P env req) txId price with
  | none => none
  | some (tx, h) =>
  match writePriorityOp P d env h with
  | none => none
  | some d' => some (d', tx, h)

/-! ## The free paths -/

/-- `_requestL2TransactionFree(req)` (:291-303): `txId = total`, `l2GasPrice = 0`, no fee check,
no aliasing. -/
def requestL2TransactionFree (P : Params) (d : Diamond) (env : Env) (req : Request) :
    Option (Diamond × L2Tx × Word) :=
  match checkedWord d.total with
  | none => none
  | some txId =>
  match validateTx P d req txId 0 with
  | none => none
  | some (tx, h) =>
  match writePriorityOp P d env h with
  | none => none
  | some d' => some (d', tx, h)

/-- The request `requestL2ServiceTransaction(_contractL2, _l2Calldata)` builds (:173-186). -/
def serviceRequest (target : Address) (data : Bytes) : Request where
  sender := serviceSender
  contractL2 := target
  mintValue := 0
  l2Value := 0
  l2Calldata := data
  l2GasLimit := freePathGasLimit
  l2GasPerPubdataByteLimit := requiredGasPerPubdata
  factoryDeps := []
  refundRecipient := 0

/-- `_wrapRequest(c, h, e)` (:142-166). -/
def wrapRequest (P : Params) (c : ℕ) (h : Word) (e : ℕ) : Request where
  sender := relaySender
  contractL2 := l2InteropCenterAddr
  mintValue := 0
  l2Value := 0
  l2Calldata := P.encForward c h e
  l2GasLimit := freePathGasLimit
  l2GasPerPubdataByteLimit := requiredGasPerPubdata
  factoryDeps := []
  refundRecipient := 0

/-- `bridgehubRequestL2TransactionOnGateway(h, _)` after its modifier (:133-140): the hash is
pushed as given, with no transaction and no deposit pause check. -/
def requestOnGateway (d : Diamond) (env : Env) (h : Word) : Option Diamond :=
  writePriorityOpHash d env.timestamp h

/-! ## Who can be the sender of a user request

The user path keeps the sender when it is `tx.origin` or (on L1) an EIP-7702 account, and aliases
it otherwise (:270-272). Which addresses can reach the Bridgehub as a request's sender is a fact
about L1 accounts, stated here as a premise. -/

/-- Which L1 addresses can act. `keyed a`: someone holds a private key for `a`, so `a` can be
`tx.origin` and can carry an EIP-7702 delegation. `contract a`: contract code other than a 7702
delegation runs at `a` (a deployed contract or one under construction). -/
structure Accounts where
  keyed : Address → Prop
  contract : Address → Prop

/-- The environment agrees with the accounts: `tx.origin` is keyed, and the 7702 checker reports a
delegation only at a keyed address (a delegation is installed by a signed authorization). -/
def EnvAgrees (A : Accounts) (env : Env) : Prop :=
  A.keyed env.origin ∧ ∀ a, env.is7702 a = true → A.keyed a

/-- `s` can be the `sender` of a user request. The Bridgehub sets it to its own `msg.sender`
(`core/bridgehub/L1Bridgehub.sol:176`) or to a second bridge that answered a call
(`L1Bridgehub.sol:232-238`, `:248`). Either code ran at `s`, or `s` is `tx.origin`. -/
def CanSend (A : Accounts) (env : Env) (s : Address) : Prop :=
  s = env.origin ∨ env.is7702 s = true ∨ A.contract s

/-- No account can act as `C` unaliased, and no contract runs at the address that aliases to `C`. -/
def Unreachable (A : Accounts) (C : Address) : Prop :=
  ¬ A.keyed C ∧ ¬ A.contract (undoL1ToL2Alias C)

/-! ## Other writers of the tree on L1

On L1 the priority tree has four writers (`grep -rn 'priorityTree\.' contracts/`): `setup` in
`DiamondInit` (`DiamondInit.sol:137`, once, when the diamond is created), `push` in
`_writePriorityOpHash` (:374), `processBatch` in the Executor (`Executor.sol:98`), and `l1Reinit` in
`Migrator.forwardedBridgeMint` on L1 (`Migrator.sol:283`). `initFromCommitment` and
`checkGWReinit` run only off L1 (`Migrator.sol:286-291`). `priorityOpsRequestTimestamp` has one
writer, :377. -/

/-- One call that changes an L1 diamond's priority tree or request timestamps. `EnvOk` is a
condition on the environment of every request of the run (the results take
`fun env => 0 < env.timestamp`). -/
inductive TreeStepL1 (P : Params) (EnvOk : Env → Prop) : Diamond → Diamond → Prop
  /-- A successful user-path request on L1. -/
  | userRequest {d d' : Diamond} (env : Env) (req : Request) (tx : L2Tx) (h : Word) :
      env.onL1 P → EnvOk env → requestL2TransactionSender P d env req = some (d', tx, h) →
      TreeStepL1 P EnvOk d d'
  /-- A successful free-path request on L1 (service transaction or relay). -/
  | freeRequest {d d' : Diamond} (env : Env) (req : Request) (tx : L2Tx) (h : Word) :
      env.onL1 P → EnvOk env → requestL2TransactionFree P d env req = some (d', tx, h) →
      TreeStepL1 P EnvOk d d'
  /-- A successful `bridgehubRequestL2TransactionOnGateway`. On L1 its caller check cannot pass
  (`L2_INTEROP_CENTER_ADDR` is not an L1 account); the step is kept so that the result does not
  depend on that. -/
  | onGatewayRequest {d d' : Diamond} (env : Env) (h : Word) :
      EnvOk env → requestOnGateway d env h = some d' → TreeStepL1 P EnvOk d d'
  /-- `processBatch` (`PT:83-96`): `unprocessedIndex` grows by the number of items; the root check
  only rejects and is omitted. -/
  | processBatch {d : Diamond} (n : ℕ) :
      TreeStepL1 P EnvOk d { d with unprocessedIndex := d.unprocessedIndex + n }
  /-- `l1Reinit` (`PT:135-147`): same `startIndex`, `unprocessedIndex` does not decrease, the
  commitment's `nextLeafIndex` is not beyond the tree's; only `unprocessedIndex` is written. -/
  | l1Reinit {d : Diamond} (startIndex unprocessedIndex nextLeafIndex : ℕ) :
      d.startIndex = startIndex → d.unprocessedIndex ≤ unprocessedIndex →
      nextLeafIndex ≤ d.nextLeafIndex →
      TreeStepL1 P EnvOk d { d with unprocessedIndex := unprocessedIndex }
  /-- Any write by another facet that leaves the tree counters and the request timestamps alone. -/
  | other {d d' : Diamond} :
      d'.startIndex = d.startIndex → d'.nextLeafIndex = d.nextLeafIndex →
      d'.requestTimestamp = d.requestTimestamp → TreeStepL1 P EnvOk d d'

/-- A run of an L1 diamond. -/
inductive TreeRunL1 (P : Params) (EnvOk : Env → Prop) : Diamond → Diamond → Prop
  | refl {d : Diamond} : TreeRunL1 P EnvOk d d
  | tail {d e f : Diamond} : TreeRunL1 P EnvOk d e → TreeStepL1 P EnvOk e f → TreeRunL1 P EnvOk d f

/-! ## Witness data

A chain with id `324` on L1 `1`, with five operations before its tree started and two in the tree,
so the next request gets index `7`. The toy hash adds `1000` to the nonce; the toy encoder writes
three bytes. No result depends on either. -/

/-- Witness deployment: L1 is chain `1`. -/
def wParams : Params where
  l1ChainId := 1
  txHash := fun tx => (tx.nonce : Word) + 1000
  encForward := fun _ _ _ => [1, 2, 3]

/-- Witness fee parameters: rollup pricing, every divisor nonzero. -/
def wFeeParams : FeeParams where
  pubdataPricingMode := .rollup
  batchOverheadL1Gas := 1000
  maxPubdataPerBatch := 100
  maxL2GasPerBatch := 1000
  priorityTxMaxPubdata := 100000
  minimalL2GasPrice := 2

/-- Witness diamond: chain `324` settling on L1, no filterer, multiplier `1/1`, `startIndex = 5`,
two leaves in the tree, one processed. -/
def wDiamond : Diamond where
  chainId := 324
  settlementLayer := 0
  transactionFilterer := 0
  priceNominator := 1
  priceDenominator := 1
  feeParams := wFeeParams
  priorityTxMaxGasLimit := freePathGasLimit
  pausedDepositsTimestamp := 0
  startIndex := 5
  unprocessedIndex := 1
  nextLeafIndex := 2
  leafAt := fun _ => 0
  requestTimestamp := fun _ => 0

/-- The witness EOA, `tx.origin`. -/
def wOrigin : Address := ⟨0xA11CE, by decide⟩

/-- A witness contract that calls the Bridgehub. -/
def wContract : Address := ⟨0xC0FFEE0000000000000000000000000000C0FFEE, by decide⟩

/-- The witness environment on L1 at time `1000` with gas price `3`: only `wContract` has code,
there is no 7702 account, every filter passes, no migration is in progress. -/
def wEnv : Env where
  chainId := 1
  timestamp := 1000
  origin := wOrigin
  gasPrice := 3
  hasCode := fun a => decide (a = wContract)
  is7702 := fun _ => false
  filterAllows := fun _ _ => true
  migrationInProgress := fun _ => false

/-- A witness user request with sender `s`: mint `2_000_000`, L2 value `7`, gas limit `300_000`. -/
def wRequest (s : Address) : Request where
  sender := s
  contractL2 := ⟨0x1234, by decide⟩
  mintValue := 2000000
  l2Value := 7
  l2Calldata := [0xAB]
  l2GasLimit := 300000
  l2GasPerPubdataByteLimit := requiredGasPerPubdata
  factoryDeps := []
  refundRecipient := 0

/-- The witness accounts: only `wOrigin` is keyed, only `wContract` is a contract. -/
def wAccounts : Accounts where
  keyed := fun a => a = wOrigin
  contract := fun a => a = wContract

/-- A witness EIP-7702 account (keyed, with a delegation, so it has code). -/
def w7702 : Address := ⟨0x7702000000000000000000000000000000007702, by decide⟩

/-- `wEnv`, with `w7702` an EIP-7702 account that has code. -/
def wEnv7702 : Env :=
  { wEnv with
    hasCode := fun a => decide (a = wContract ∨ a = w7702)
    is7702 := fun a => decide (a = w7702) }

/-- The address whose alias is `SERVICE_TRANSACTION_SENDER`:
`0xEEEEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEEEE`. -/
def wServicePreimage : Address := undoL1ToL2Alias serviceSender

/-- `wEnv`, except that contract code also runs at `wServicePreimage`. -/
def wEnvPreimage : Env := { wEnv with hasCode := fun a => decide (a = wContract ∨ a = wServicePreimage) }

/-- `wAccounts`, except that `wServicePreimage` is also a contract: the account premise fails. -/
def wAccountsPreimage : Accounts where
  keyed := fun a => a = wOrigin
  contract := fun a => a = wContract ∨ a = wServicePreimage

end Contracts.MailboxFacet.RequestPaths
