# MailboxFacet

Source: `l1-contracts/contracts/state-transition/chain-deps/facets/Mailbox.sol` on era-contracts
branch `draft/v0.35.0` at **`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`**, with the parts of
`ZKChainBase.sol`, `libraries/PriorityTree.sol`, `libraries/TransactionValidator.sol`,
`vendor/AddressAliasHelper.sol` and `common/Config.sol` the request paths use. This is not the
pinned `c67894b9` tree; the specs quote `file:line` at `b17415d20`.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those
exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| RequestPaths | [Specs/RequestPaths.lean](Specs/RequestPaths.lean) | [Properties/RequestPaths.lean](Properties/RequestPaths.lean) | [Proofs/RequestPaths.lean](Proofs/RequestPaths.lean) |
| PriorityTree | [Specs/PriorityTree.lean](Specs/PriorityTree.lean) | none | none |

`Specs/PriorityTree.lean` is a definitions-only model of the `PriorityTree` library and the
`DynamicIncrementalMerkle` functions it calls (namespace `Contracts.MailboxFacet`), pinned at
`d9f678900` and byte-identical at `b17415d20`. It has no Properties or Proofs modules of its own;
it is used by `../../Protocol/PriorityMirror/` (topic `Mirror`).

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
`DynamicIncrementalMerkle`'s frontier and `historicalRoots` are not modelled (branch `cov/mailbox`,
topic `PriorityTree`, models them). Hashing (`keccak256(abi.encode(tx))`) and the
`forwardTransactionOnGateway` encoder are arbitrary functions. The external view calls (filterer,
7702 checker, `isMigrationInProgress`, code size) are environment values. Caller checks, the
reentrancy lock and the relay into the settlement layer are applied by the system model,
`../../Protocol/PriorityRequests/` (topic `PrivilegedSenders`). The timestamp result assumes no
other code (for example an upgrade initializer) writes the tree counters or
`priorityOpsRequestTimestamp` during the run. Events are not modelled. `main`
(`70096e2ea`) differs in the factory-dependency handling and the free paths' gas limit; see the
header of `Specs/RequestPaths.lean`.
