import EraSpec.Contracts.MailboxFacet.Specs.RequestPaths

/-!
# Properties: what one request does to one diamond

Statements about `EraSpec.Contracts.MailboxFacet.Specs.RequestPaths` (pin `b17415d20`). Proofs are
in `EraSpec.Contracts.MailboxFacet.Proofs.RequestPaths`. No statement takes a hash or encoding
premise: `txHash` and `encForward` are arbitrary.

## (a) One leaf, at the old total

`Diamond.pushLeaf h t` adds one to the total, records `h` and `t` at the old total, changes no other
index's leaf or timestamp, and keeps the start index, the processed count, the chain id, the
settlement layer and the pause timestamp (`PushLeafFrame`); by its definition it changes no other
field. A successful request of each path returns exactly `pushLeaf` of the old diamond, with the
transaction's hash as the leaf and the old total as the nonce: the user path
(`UserRequestExact`), the free path (`FreeRequestExact`, with the fixed fields of the service and
relay requests in `ServiceRequestShape` and `RelayRequestShape`), and the gateway path, which pushes
the given hash (`OnGatewayRequestExact`). The user and free transactions have empty `factoryDeps`
and type `127`; the user, service and relay transactions have `gasPerPubdataByteLimit = 800`.

## (b) The user path: fee floor and sender

A successful user request paid at least the derived price times its gas limit, and that price is
the transaction's `maxFeePerGas` (`UserRequestFeeFloor`). Its `from` is the request's sender when
the sender is `tx.origin` or, on L1, an address the 7702 checker reports, and the sender's alias
otherwise (`UserRequestSender`). Under the account premise `Unreachable`, no user request on L1 has
a given `from` (`UserRequestNeverReachesUnreachableSender`); `SETTLEMENT_LAYER_RELAY_SENDER` and
`SERVICE_TRANSACTION_SENDER` are the intended instances (`RelayAndServiceUnreachableIff` says what
the premise asks of them). The premise is needed: with a contract at the address whose alias is
`SERVICE_TRANSACTION_SENDER`, a user request from it has that `from`
(`AliasPreimageYieldsServiceSender`).

## (c) Request timestamps on an L1 diamond

Along a run of an L1 diamond whose requests are made at positive timestamps, every index from the
run's initial total up to the current total has a nonzero request timestamp, the start index is
unchanged and the total only grows (`L1RequestTimestampsNonzero`). So the first unprocessed
operation, if it is one of them, has the timestamp `activatePriorityMode` and
`permanentlyAllowPriorityMode` require (`state-transition/chain-deps/facets/Admin.sol:501`, `:532`)
(`FirstUnprocessedTimestampNonzero`).

## Non-vacuity

`UserRequestWitness` meets every premise of (a), (b) and the unreachable-sender result with an
aliased contract sender, a nonzero index and a nonzero fee; `UserRequestOriginWitness` and
`UserRequest7702Witness` reach the other two branches of `UserRequestSender`.
`FreeRequestWitness` runs both free paths, `OnGatewayRequestWitness` the gateway path, and
`L1TimestampWitness` is a run with two requests and a processed batch whose first unprocessed index
lies in the covered range.
-/

namespace Contracts.MailboxFacet.RequestPaths

/-! ## (a) One leaf, at the old total -/

/-- **WHAT A PUSH CHANGES.** `pushLeaf h t` raises the total by one, keeps `startIndex` and
`unprocessedIndex`, stores `h` and `t` at the old total, keeps every other index's leaf and
timestamp, and keeps the chain id, the settlement layer and the pause timestamp. -/
def Properties.PushLeafFrame : Prop :=
  ∀ (d : Diamond) (h : Word) (t : ℕ),
    (d.pushLeaf h t).total = d.total + 1 ∧
    (d.pushLeaf h t).startIndex = d.startIndex ∧
    (d.pushLeaf h t).unprocessedIndex = d.unprocessedIndex ∧
    (d.pushLeaf h t).leafAt d.total = h ∧
    (d.pushLeaf h t).requestTimestamp d.total = t ∧
    (∀ i, i ≠ d.total →
      (d.pushLeaf h t).leafAt i = d.leafAt i ∧
      (d.pushLeaf h t).requestTimestamp i = d.requestTimestamp i) ∧
    (d.pushLeaf h t).chainId = d.chainId ∧
    (d.pushLeaf h t).settlementLayer = d.settlementLayer ∧
    (d.pushLeaf h t).pausedDepositsTimestamp = d.pausedDepositsTimestamp

/-- **HEADLINE (a), USER PATH.** A successful `bridgehubRequestL2Transaction(req)` at time `t` on a
diamond with total `k` is exactly one push: leaf `keccak256(abi.encode(tx))` at index `k`,
timestamp `t` at `k` and nowhere else. The transaction has nonce `k`, `gasPerPubdataByteLimit =
800`, empty `factoryDeps`, type `127`, and the request's target, calldata, L2 value, gas limit
and mint value; the request's own `factoryDeps` were empty. -/
def Properties.UserRequestExact : Prop :=
  ∀ (P : Params) (d : Diamond) (env : Env) (req : Request) (d' : Diamond) (tx : L2Tx) (h : Word),
    requestL2TransactionSender P d env req = some (d', tx, h) →
      d' = d.pushLeaf h env.timestamp ∧ h = P.txHash tx ∧ tx.nonce = d.total ∧
      tx.gasPerPubdataByteLimit = requiredGasPerPubdata ∧ tx.factoryDeps = [] ∧
      tx.txType = priorityOpTxType ∧ tx.toAddr = req.contractL2 ∧ tx.data = req.l2Calldata ∧
      tx.value = req.l2Value ∧ tx.gasLimit = req.l2GasLimit ∧ tx.reserved0 = req.mintValue ∧
      req.factoryDeps = []

/-- **HEADLINE (a), FREE PATHS.** A successful `_requestL2TransactionFree(req)` at time `t` on a
diamond with total `k` is exactly one push of `keccak256(abi.encode(tx))` at index `k` with
timestamp `t`. The transaction has nonce `k`, `maxFeePerGas = 0`, empty `factoryDeps`, type `127`,
and copies the request's sender, target, calldata, values, gas fields and refund recipient. -/
def Properties.FreeRequestExact : Prop :=
  ∀ (P : Params) (d : Diamond) (env : Env) (req : Request) (d' : Diamond) (tx : L2Tx) (h : Word),
    requestL2TransactionFree P d env req = some (d', tx, h) →
      d' = d.pushLeaf h env.timestamp ∧ h = P.txHash tx ∧ tx.nonce = d.total ∧
      tx.maxFeePerGas = 0 ∧ tx.factoryDeps = [] ∧ tx.txType = priorityOpTxType ∧
      tx.fromAddr = req.sender ∧ tx.toAddr = req.contractL2 ∧ tx.data = req.l2Calldata ∧
      tx.value = req.l2Value ∧ tx.reserved0 = req.mintValue ∧ tx.gasLimit = req.l2GasLimit ∧
      tx.gasPerPubdataByteLimit = req.l2GasPerPubdataByteLimit ∧
      tx.reserved1 = req.refundRecipient

/-- **THE SERVICE TRANSACTION.** A successful free path on the request that
`requestL2ServiceTransaction(target, data)` builds (its own push, before any relay) is one push at
index `k` of a transaction from `SERVICE_TRANSACTION_SENDER` to `target` with calldata `data`, mint
value `0`, L2 value `0`, `maxFeePerGas = 0`, refund recipient `0`, gas limit `2^24` and
`gasPerPubdataByteLimit = 800`, at nonce `k`. -/
def Properties.ServiceRequestShape : Prop :=
  ∀ (P : Params) (d : Diamond) (env : Env) (target : Address) (data : Bytes) (d' : Diamond)
    (tx : L2Tx) (h : Word),
    requestL2TransactionFree P d env (serviceRequest target data) = some (d', tx, h) →
      d' = d.pushLeaf h env.timestamp ∧ h = P.txHash tx ∧ tx.nonce = d.total ∧
      tx.fromAddr = serviceSender ∧ tx.toAddr = target ∧ tx.data = data ∧
      tx.reserved0 = 0 ∧ tx.value = 0 ∧ tx.maxFeePerGas = 0 ∧ tx.reserved1 = 0 ∧
      tx.gasLimit = freePathGasLimit ∧ tx.gasPerPubdataByteLimit = requiredGasPerPubdata

/-- **THE RELAY TRANSACTION.** A successful free path on `_wrapRequest(c, h₀, e)` (the push of
`requestL2TransactionToGatewayMailbox(c, h₀, e)` once its checks passed) is one push at index `k`
of a transaction from `SETTLEMENT_LAYER_RELAY_SENDER` to `L2_INTEROP_CENTER_ADDR` with calldata
`forwardTransactionOnGateway(c, h₀, e)`, mint value `0`, L2 value `0`, `maxFeePerGas = 0`, refund
recipient `0`, gas limit `2^24` and `gasPerPubdataByteLimit = 800`, at nonce `k`. -/
def Properties.RelayRequestShape : Prop :=
  ∀ (P : Params) (d : Diamond) (env : Env) (c : ℕ) (h₀ : Word) (e : ℕ) (d' : Diamond)
    (tx : L2Tx) (h : Word),
    requestL2TransactionFree P d env (wrapRequest P c h₀ e) = some (d', tx, h) →
      d' = d.pushLeaf h env.timestamp ∧ h = P.txHash tx ∧ tx.nonce = d.total ∧
      tx.fromAddr = relaySender ∧ tx.toAddr = l2InteropCenterAddr ∧ tx.data = P.encForward c h₀ e ∧
      tx.reserved0 = 0 ∧ tx.value = 0 ∧ tx.maxFeePerGas = 0 ∧ tx.reserved1 = 0 ∧
      tx.gasLimit = freePathGasLimit ∧ tx.gasPerPubdataByteLimit = requiredGasPerPubdata

/-- **THE GATEWAY PATH.** A successful `bridgehubRequestL2TransactionOnGateway(h, _)` at time `t`
pushes `h` at the old total with timestamp `t`. -/
def Properties.OnGatewayRequestExact : Prop :=
  ∀ (d : Diamond) (env : Env) (h : Word) (d' : Diamond),
    requestOnGateway d env h = some d' → d' = d.pushLeaf h env.timestamp

/-! ## (b) The user path: fee floor and sender -/

/-- **HEADLINE (b), FEE FLOOR.** A successful user request derived a price `p =
_deriveL2GasPrice(tx.gasprice, 800)`, its transaction's `maxFeePerGas` is `p`, and the mint value
covers `p` times the gas limit. -/
def Properties.UserRequestFeeFloor : Prop :=
  ∀ (P : Params) (d : Diamond) (env : Env) (req : Request) (d' : Diamond) (tx : L2Tx) (h : Word),
    requestL2TransactionSender P d env req = some (d', tx, h) →
      ∃ p, deriveL2GasPrice d env.gasPrice requiredGasPerPubdata = some p ∧
        tx.maxFeePerGas = p ∧ p * tx.gasLimit ≤ tx.reserved0

/-- **HEADLINE (b), SENDER.** A successful user request's `from` is the request's sender when the
sender is `tx.origin` or, on L1, an address the 7702 checker reports, and the sender's L1-to-L2
alias otherwise. -/
def Properties.UserRequestSender : Prop :=
  ∀ (P : Params) (d : Diamond) (env : Env) (req : Request) (d' : Diamond) (tx : L2Tx) (h : Word),
    requestL2TransactionSender P d env req = some (d', tx, h) →
      tx.fromAddr =
        if req.sender = env.origin ∨ (env.onL1 P ∧ env.is7702 req.sender = true) then req.sender
        else applyL1ToL2Alias req.sender

/-- **NO USER REQUEST HAS AN UNREACHABLE SENDER.** On L1, if the environment agrees with the
accounts, the request's sender is one that can reach the Bridgehub (`CanSend`), and `C` is
`Unreachable` (no key for `C`, no contract at `undoL1ToL2Alias C`), then a successful user request's
`from` is not `C`. -/
def Properties.UserRequestNeverReachesUnreachableSender : Prop :=
  ∀ (P : Params) (A : Accounts) (d : Diamond) (env : Env) (req : Request) (d' : Diamond)
    (tx : L2Tx) (h : Word) (C : Address),
    env.onL1 P → EnvAgrees A env → CanSend A env req.sender → Unreachable A C →
    requestL2TransactionSender P d env req = some (d', tx, h) → tx.fromAddr ≠ C

/-- **WHAT `Unreachable` ASKS OF THE TWO CONSTANTS.** For the relay sender it asks that no key is
known for `0x1111…1111` and no contract runs at `0x0000111111111111111111111111111111110000`; for
the service sender, no key for `0xFFFF…FFFF` and no contract at
`0xEEEEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEEEE`. -/
def Properties.RelayAndServiceUnreachableIff : Prop :=
  ∀ (A : Accounts),
    (Unreachable A relaySender ↔
      ¬ A.keyed relaySender ∧ ¬ A.contract ⟨0x0000111111111111111111111111111111110000, by decide⟩) ∧
    (Unreachable A serviceSender ↔
      ¬ A.keyed serviceSender ∧ ¬ A.contract ⟨0xEEEEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEEEE, by decide⟩)

/-- **THE ACCOUNT PREMISE IS NEEDED.** If contract code runs at `0xEEEEFFFF…FFFFEEEE`, the address
whose alias is `SERVICE_TRANSACTION_SENDER`, a user request from that contract succeeds on the
witness diamond, every other premise of `UserRequestNeverReachesUnreachableSender` holds, and the
transaction's `from` is `SERVICE_TRANSACTION_SENDER`. -/
def Properties.AliasPreimageYieldsServiceSender : Prop :=
  ∃ (d' : Diamond) (tx : L2Tx) (h : Word),
    requestL2TransactionSender wParams wDiamond wEnvPreimage (wRequest wServicePreimage) =
      some (d', tx, h) ∧
    tx.fromAddr = serviceSender ∧ wEnvPreimage.onL1 wParams ∧
    EnvAgrees wAccountsPreimage wEnvPreimage ∧
    CanSend wAccountsPreimage wEnvPreimage wServicePreimage ∧
    ¬ wAccountsPreimage.keyed serviceSender ∧
    wAccountsPreimage.contract (undoL1ToL2Alias serviceSender)

/-! ## (c) Request timestamps on an L1 diamond -/

/-- **HEADLINE (c).** Along a run of an L1 diamond in which every request is made at a positive
`block.timestamp`, the start index is unchanged, the total does not decrease, and every index from
the run's initial total up to its current total has a nonzero request timestamp. -/
def Properties.L1RequestTimestampsNonzero : Prop :=
  ∀ (P : Params) (d d' : Diamond),
    TreeRunL1 P (fun env => 0 < env.timestamp) d d' →
      d'.startIndex = d.startIndex ∧ d.total ≤ d'.total ∧
      ∀ i, d.total ≤ i → i < d'.total → d'.requestTimestamp i ≠ 0

/-- **THE PRIORITY-MODE TIMESTAMP IS PRESENT.** On such a run, if the first unprocessed operation is
at or after the run's initial total and before the current total, its request timestamp is
nonzero. -/
def Properties.FirstUnprocessedTimestampNonzero : Prop :=
  ∀ (P : Params) (d d' : Diamond),
    TreeRunL1 P (fun env => 0 < env.timestamp) d d' →
      d.total ≤ d'.firstUnprocessed → d'.firstUnprocessed < d'.total →
        d'.requestTimestamp d'.firstUnprocessed ≠ 0

/-! ## Non-vacuity -/

/-- **WITNESS: AN ALIASED CONTRACT SENDER.** On the witness L1 diamond (total `7`), a request from
the contract `wContract` at time `1000` succeeds. Its index is `7`, its fee is `5` per gas (so
`1_500_000` for the gas limit, below the mint value `2_000_000`), its `from` is the contract's alias,
and every premise of `UserRequestNeverReachesUnreachableSender` holds for both constants. -/
def Properties.UserRequestWitness : Prop :=
  ∃ (d' : Diamond) (tx : L2Tx) (h : Word),
    requestL2TransactionSender wParams wDiamond wEnv (wRequest wContract) = some (d', tx, h) ∧
    wDiamond.total = 7 ∧ tx.nonce = 7 ∧ wEnv.timestamp = 1000 ∧
    deriveL2GasPrice wDiamond wEnv.gasPrice requiredGasPerPubdata = some 5 ∧
    tx.maxFeePerGas = 5 ∧ 5 * tx.gasLimit = 1500000 ∧ tx.reserved0 = 2000000 ∧
    tx.fromAddr = applyL1ToL2Alias wContract ∧ tx.fromAddr ≠ wContract ∧
    wEnv.onL1 wParams ∧ EnvAgrees wAccounts wEnv ∧ CanSend wAccounts wEnv wContract ∧
    Unreachable wAccounts relaySender ∧ Unreachable wAccounts serviceSender

/-- **WITNESS: THE SENDER IS `tx.origin`.** The same request from `wOrigin` succeeds and keeps its
sender. -/
def Properties.UserRequestOriginWitness : Prop :=
  ∃ (d' : Diamond) (tx : L2Tx) (h : Word),
    requestL2TransactionSender wParams wDiamond wEnv (wRequest wOrigin) = some (d', tx, h) ∧
    tx.fromAddr = wOrigin ∧ CanSend wAccounts wEnv wOrigin

/-- **WITNESS: AN EIP-7702 SENDER.** On L1, a request whose sender `w7702` is not `tx.origin` but is
reported by the 7702 checker succeeds and keeps its sender. -/
def Properties.UserRequest7702Witness : Prop :=
  ∃ (d' : Diamond) (tx : L2Tx) (h : Word),
    requestL2TransactionSender wParams wDiamond wEnv7702 (wRequest w7702) = some (d', tx, h) ∧
    tx.fromAddr = w7702 ∧ w7702 ≠ wEnv7702.origin ∧ wEnv7702.is7702 w7702 = true ∧
    wEnv7702.onL1 wParams

/-- **WITNESS: THE GATEWAY PATH.** `bridgehubRequestL2TransactionOnGateway(77, _)` on the witness diamond
at time `1000` succeeds. -/
def Properties.OnGatewayRequestWitness : Prop :=
  ∃ d', requestOnGateway wDiamond wEnv 77 = some d' ∧ d'.total = 8 ∧ wEnv.timestamp = 1000

/-- **WITNESS: BOTH FREE PATHS.** On the witness diamond a service request to the L2 Bridgehub and a
relay request for chain `325` succeed. -/
def Properties.FreeRequestWitness : Prop :=
  (∃ (d' : Diamond) (tx : L2Tx) (h : Word),
    requestL2TransactionFree wParams wDiamond wEnv (serviceRequest l2BridgehubAddr [0xCD]) =
      some (d', tx, h) ∧ tx.nonce = 7) ∧
  (∃ (d' : Diamond) (tx : L2Tx) (h : Word),
    requestL2TransactionFree wParams wDiamond wEnv (wrapRequest wParams 325 77 0) =
      some (d', tx, h) ∧ tx.nonce = 7)

/-- **WITNESS: A RUN WITH TWO REQUESTS.** From the witness diamond (total `7`, first unprocessed
index `6`), a user request and a service request at positive times and a processed batch of two
operations give a diamond with total `9` whose first unprocessed index is `8`, inside the range
`[7, 9)` that `L1RequestTimestampsNonzero` covers. -/
def Properties.L1TimestampWitness : Prop :=
  ∃ d', TreeRunL1 wParams (fun env => 0 < env.timestamp) wDiamond d' ∧
    d'.total = 9 ∧ d'.firstUnprocessed = 8 ∧ wDiamond.total ≤ d'.firstUnprocessed

end Contracts.MailboxFacet.RequestPaths
