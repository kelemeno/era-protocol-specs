# PriorityRequests

Who appends priority operations on L1, and who can send the two privileged L2 senders
`SETTLEMENT_LAYER_RELAY_SENDER` and `SERVICE_TRANSACTION_SENDER`. Source: era-contracts branch
`draft/v0.35.0` at **`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`**: the Mailbox facet, the
`L1Bridgehub` request entries, `ChainRegistrationSender`, `L1ChainAssetHandler`
(`requestPauseDepositsForChainOnGateway`) and `Migrator.pauseDepositsBeforeInitiatingMigration`.
One diamond's request functions are `../../Contracts/MailboxFacet/` (topic `RequestPaths`).

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| PrivilegedSenders | [Specs/PrivilegedSenders.lean](Specs/PrivilegedSenders.lean) | [Properties/PrivilegedSenders.lean](Properties/PrivilegedSenders.lean) | [Proofs/PrivilegedSenders.lean](Proofs/PrivilegedSenders.lean) |

Namespace `Contracts.PriorityRequests`. Statements are `Contracts.PriorityRequests.Properties.*`;
each certificate has the same name without the `Properties` segment.

The model is one L1 with any number of diamonds, the Bridgehub's registry and roles, and the
registration sender's flags. A step is one successful L1 transaction: a Bridgehub request
(direct, two bridges with an arbitrary second bridge, or with the registration sender as second
bridge), the registration sender's `allowInteropPeer` and `deregisterInteropPairs`, a diamond's
`pauseDepositsBeforeInitiatingMigration`, a direct call by any other account (`Actor`) to any of
the four Mailbox entries or to the chain asset handler, a configuration change, and (only when
allowed) a write of the two Bridgehub roles. A ghost log records every push with its transaction.

- **Relay (A).** A user request on a diamond settling here appends one push; on a diamond
  settling elsewhere it appends that push and one relay push into the settlement layer's diamond
  (a different diamond, whose total grows by one) calling `forwardTransactionOnGateway(c, h, 0)`
  for the pushed leaf `h`; no other diamond changes (`UserCallRelaysIffSettled`). Service requests
  do the same, except that the settlement layer may be the requesting diamond and the statement
  does not state how its total grows (`ServiceCallRelaysIffSettled`).
- **Privileged senders (B).** From an `Init` state (genuine roles), without role writes, and under
  the account premises (no key for either constant, no contract at their alias preimages, no
  account at `L2_INTEROP_CENTER_ADDR` on L1, the registration sender is a contract whose alias has
  no key), along every run:
  relay leaves call `forwardTransactionOnGateway(c, h, 0)` on the L2 interop center for the push
  made just before them in the same transaction by a diamond of chain `c` with leaf `h`
  (`RelayLeavesForwardTheirHash`), into a whitelisted settlement layer's tree, after a push by
  `c`'s registered diamond (`RelayLeafStepFacts`); service leaves carry one of
  `allowInteropPeer(p, a ≠ 0)`, `deregisterChainForInterop(p)` to the L2 Bridgehub or
  `requestPauseDepositsForChainOnGateway(c)` to the L2 chain asset handler
  (`ServiceLeavesHaveFixedPurpose`), with the Bridgehub's base token asset id and the pair allowed,
  the pair disallowed, or `c`'s diamond paused in the same transaction and the leaf in the tree of
  `c`'s settlement layer (`ServiceLeafStepFacts`); leaves from the aliased registration sender
  register an allowed peer (`AliasedRegistrationLeavesRegister`, `RegistrationLeafStepFacts`);
  no user request yields either constant (`UserLeavesNeverPrivileged`); every leaf is the hash of a
  serialized transaction with the leaf's index as nonce, so no hash-only push happens on L1
  (`EveryLeafIsASerializedTransaction`). The roles and `SysWF` are kept (`RolesStayGenuine`).
  Both L2 receivers accept any service sender (`core/bridgehub/L2Bridgehub.sol:45-53`,
  `core/chain-asset-handler/L2ChainAssetHandler.sol:80-85`); along these runs the L2 Bridgehub is
  sent only the two registration calls and the L2 chain asset handler only the pause call. No hash
  premise.
- **Countermodel.** With role writes, the Bridgehub owner points `chainRegistrationSender` at an
  ordinary contract, which then appends a service leaf of any shape
  (`RedirectedRoleBreaksServicePurpose`).

Witnesses: `PrivilegedSendersWitness` (a five-step run with a gateway, a chain settling on it, a
deposit, a registration, its re-submission, a deregistration and a deposit pause; relay, service
and aliased-registration leaves are all present), `StepFactsWitness`, `RelayWitness`.

Model boundaries (`MODEL-PRIORITY-SENDERS`): no upgrades of diamonds or of the three system contracts during the run
(`OPS-CONFIG`); registered chain ids map to modelled diamonds (`SysWF`, kept by configuration
steps). A callee's nested calls inside a request are separate `Actor` steps. Reject-only checks
that read nothing modelled are omitted (listed in the Specs header). L2 execution of the leaves is
not modelled: on L2 the bootloader executes a transaction whose hash is the leaf, so these
statements about the serialized transaction transfer to L2 only up to a keccak collision on two
transaction encodings. Chain migrations are disabled at the pin (`CHAIN_MIGRATIONS_ENABLED = false`,
`common/Config.sol:317-320`; per `core/chain-asset-handler/IChainAssetHandler.sol:81-83` the
release requires every chain to settle on L1), so the relay half is latent; the model allows chains
that settle elsewhere.

## Headline guarantees

These are the area's `@[headline]` statements (see [CONSOLIDATION.md](../../../CONSOLIDATION.md)),
about `b17415d20`. The run-level ones (B1 to B4) carry the same premises: the run starts from an
`Init` state (no push logged, the Bridgehub's registration-sender and chain-asset-handler roles are
the genuine contracts, the state well formed), has no role write, every step is an L1 transaction
agreeing with the accounts, and the account premises hold (nobody acts as
`SETTLEMENT_LAYER_RELAY_SENDER` or `SERVICE_TRANSACTION_SENDER`, no account acts at
`L2_INTEROP_CENTER_ADDR` on L1, and nobody holds a key for the registration sender's alias).

| Guarantee | Premises | Statement |
|---|---|---|
| A user request on a diamond pushes one leaf there, plus one relay leaf into its settlement layer's diamond when it settles elsewhere; nothing else changes | The call succeeds | `UserCallRelaysIffSettled` |
| The same for a service request | The call succeeds | `ServiceCallRelaysIffSettled` |
| A leaf from `SETTLEMENT_LAYER_RELAY_SENDER` forwards the hash pushed just before it, by a diamond of the named chain, in the same L1 transaction | The run-level premises | `RelayLeavesForwardTheirHash` |
| A leaf from `SERVICE_TRANSACTION_SENDER` allows a peer, deregisters a chain, or requests a gateway deposit pause | The run-level premises | `ServiceLeavesHaveFixedPurpose` |
| A leaf from the registration sender's alias registers a peer | The run-level premises | `AliasedRegistrationLeavesRegister` |
| No user request has a privileged sender | The run-level premises | `UserLeavesNeverPrivileged` |

Witnesses (`@[witness]`): `RelayWitness` (both request paths, settled here and on a gateway) and
`PrivilegedSendersWitness` (a run with every kind of privileged leaf). Countermodel
(`@[countermodel]`): `RedirectedRoleBreaksServicePurpose` (with role writes, a service leaf loses
its shape).

