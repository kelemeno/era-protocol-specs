# MailboxFacet

The four request paths of the `MailboxFacet` that append to a diamond's priority tree, at
era-contracts `draft/v0.35.0` `b17415d20`.

## Headline guarantees

The folder's real guarantees about `b17415d20`, each with every premise. They are meant to carry
`@[headline]` (the lists after the table: `@[witness]`, `@[countermodel]`) once the tag attributes
of `EraSpec.Core.Headline` are on this branch; they are not tagged yet. They
are about one diamond; the external view calls (transaction filterer, 7702 checker,
`isMigrationInProgress`, code size) are environment values, and the hash
`keccak256(abi.encode(tx))` is an arbitrary function (no hash premise). Caller checks, the
reentrancy lock and the relay into the settlement layer are applied by
`../../Protocol/PriorityRequests/` (`MODEL-MAILBOX-REQUESTS`).

| Guarantee | Premises | Statement |
|---|---|---|
| A user request is exactly one push: leaf `keccak256(abi.encode(tx))` at the old total `k`, timestamp `block.timestamp` at `k` only; `tx` has nonce `k`, `gasPerPubdataByteLimit = 800`, empty `factoryDeps`, type `127` and the request's fields | The request succeeded | `UserRequestExact` |
| The free path behind service and relay requests is exactly one push of its transaction (nonce `k`, `maxFeePerGas = 0`, empty `factoryDeps`, type `127`, the request's fields) | The request succeeded | `FreeRequestExact` |
| The gateway path pushes the given hash at the old total, with the current timestamp | The request succeeded | `OnGatewayRequestExact` |
| A user request's `maxFeePerGas` is the derived L2 gas price, and the mint value covers that price times the gas limit | The request succeeded | `UserRequestFeeFloor` |
| A user request's `from` is the sender when it is `tx.origin` or (on L1) an EIP-7702 account, and its alias otherwise | The request succeeded | `UserRequestSender` |
| No user request on L1 has `from = C` | `C` is unreachable: no key is known for `C` and no contract runs at `C`'s alias preimage; the sender can reach the Bridgehub; the environment's account reports agree with the accounts | `UserRequestNeverReachesUnreachableSender` |
| Every index from the run's initial total to the current total has a nonzero request timestamp; the start index is unchanged and the total never decreases | A run of an L1 diamond (requests, `processBatch`, `l1Reinit`, writes that leave the tree counters and timestamps alone) whose requests are all at a positive `block.timestamp` | `L1RequestTimestampsNonzero` |
| The first unprocessed operation carries the nonzero timestamp `activatePriorityMode` and `permanentlyAllowPriorityMode` require | Such a run; the first unprocessed index lies between the run's initial total and the current total | `FirstUnprocessedTimestampNonzero` |

Witnesses: `UserRequestWitness`, `UserRequestOriginWitness`,
`UserRequest7702Witness`, `FreeRequestWitness`, `OnGatewayRequestWitness`, `L1TimestampWitness`.
Countermodel: `AliasPreimageYieldsServiceSender`. The other statements are
supporting lemmas.

## Source

`l1-contracts/contracts/state-transition/chain-deps/facets/Mailbox.sol` on era-contracts
branch `draft/v0.35.0` at **`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`**, with the parts of
`ZKChainBase.sol`, `libraries/PriorityTree.sol`, `libraries/TransactionValidator.sol`,
`vendor/AddressAliasHelper.sol` and `common/Config.sol` the request paths use. Every `file:line`
in the specs is at that commit.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those
exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| RequestPaths | [Specs/RequestPaths.lean](Specs/RequestPaths.lean) | [Properties/RequestPaths.lean](Properties/RequestPaths.lean) | [Proofs/RequestPaths.lean](Proofs/RequestPaths.lean) |

The model of the `PriorityTree` library itself is in `../PriorityTree/` (`Specs/Library.lean` and
topic `SegmentBinding`); it used to sit here as `Specs/PriorityTree.lean`.

Namespace `Contracts.MailboxFacet.RequestPaths`. Statements are
`Contracts.MailboxFacet.RequestPaths.Properties.*`; each certificate has the same name without the
`Properties` segment.

- **One request, one leaf, at the old total.** A successful request of each of the four entry
  points returns exactly `pushLeaf` of the diamond: one more leaf, stored at the old total `k`,
  with request timestamp `block.timestamp` at `k` and at no other index (`PushLeafFrame`). The
  user path (`UserRequestExact`) and the free path behind service and relay requests
  (`FreeRequestExact`, `ServiceRequestShape`, `RelayRequestShape`) push
  `keccak256(abi.encode(tx))` of a transaction with nonce `k`, empty `factoryDeps` and type `127`;
  the gateway path pushes the given hash (`OnGatewayRequestExact`). No hash premise.
- **Fee floor and sender of the user path.** The mint value covers the derived L2 gas price times
  the gas limit, and that price is the transaction's `maxFeePerGas` (`UserRequestFeeFloor`). The
  `from` is the sender when it is `tx.origin` or an L1 EIP-7702 account, and its alias otherwise
  (`UserRequestSender`). Under the account premise `Unreachable` no user request on L1 has a given
  `from` (`UserRequestNeverReachesUnreachableSender`); what the premise asks of the two privileged
  constants is `RelayAndServiceUnreachableIff`, and it is needed: a contract at the alias preimage
  of `SERVICE_TRANSACTION_SENDER` gets that `from` (`AliasPreimageYieldsServiceSender`).
- **Request timestamps on an L1 diamond.** Along a run of an L1 diamond (requests, `processBatch`,
  `l1Reinit`, and writes that leave the tree counters and timestamps alone) whose requests are
  made at positive timestamps, every index from the run's initial total to the current total has a
  nonzero request timestamp (`L1RequestTimestampsNonzero`). If the run starts at the upgrade that
  introduced the mapping, the first unprocessed operation, when it is in that range, carries the
  timestamp `activatePriorityMode` and `permanentlyAllowPriorityMode` require
  (`Admin.sol:501`, `:532`; `FirstUnprocessedTimestampNonzero`).

Witnesses: `UserRequestWitness` (aliased contract sender, index `7`, fee `5` per gas, every premise
of the unreachable-sender result), `UserRequestOriginWitness`, `UserRequest7702Witness`,
`FreeRequestWitness`, `OnGatewayRequestWitness`, `L1TimestampWitness`.

Model boundaries (`MODEL-MAILBOX-REQUESTS`): one diamond. The priority tree is its counters and a ghost map of pushed leaves;
`DynamicIncrementalMerkle`'s frontier and `historicalRoots` are not modelled here
(`../PriorityTree/Specs/Library.lean` models them; the two are not composed). Hashing (`keccak256(abi.encode(tx))`) and the
`forwardTransactionOnGateway` encoder are arbitrary functions. The external view calls (filterer,
7702 checker, `isMigrationInProgress`, code size) are environment values. Caller checks, the
reentrancy lock and the relay into the settlement layer are applied by the system model,
`../../Protocol/PriorityRequests/` (topic `PrivilegedSenders`). The timestamp result assumes no
other code (for example an upgrade initializer) writes the tree counters or
`priorityOpsRequestTimestamp` during the run. Events are not modelled. `main`
(`70096e2ea`) differs in the factory-dependency handling and the free paths' gas limit; see the
header of `Specs/RequestPaths.lean`.
