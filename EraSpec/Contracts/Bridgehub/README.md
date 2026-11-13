# Bridgehub

Source: era-contracts `draft/v0.35.0` at commit
**`d9f678900e1bc8286412b78f56d4a9f443983c29`**, files

- `l1-contracts/contracts/core/bridgehub/BridgehubBase.sol`
- `l1-contracts/contracts/core/bridgehub/L1Bridgehub.sol`

Every `file:line` in the specs is at that commit (`BB:` is `BridgehubBase.sol`, `L1:` is
`L1Bridgehub.sol`).

Review `Specs/` for state, operations and assumptions, then `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those
exact named propositions, plus auxiliary lemmas. Reviewers do not need to read `Proofs/`.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Registry | [Specs/Registry.lean](Specs/Registry.lean) | [Properties/Registry.lean](Properties/Registry.lean) | [Proofs/Registry.lean](Proofs/Registry.lean) |

Namespace: `Contracts.Bridgehub`. Statements are `Contracts.Bridgehub.Properties.*`;
each certificate has the same name without the `Properties` segment.

## What is modelled

The `L1Bridgehub` storage that any non-view entry point writes, and every non-view
external entry point (22 of them) as one `Action` executed by `exec`: administration
(admin two-step, `Ownable2Step`, `setAddresses`, `setAddressesV31`, pause), the CTM and
asset registries, `setCTMAssetAddress`, chain registration (`createNewChain`,
`registerAlreadyDeployedZKChain`, the handler's `registerNewZKChain`), settlement-layer
bookkeeping (`setSettlementLayerStatus` and the three `forwardedBridge*` migration
hooks), and the two request paths (`requestL2TransactionDirect`,
`requestL2TransactionTwoBridges`), which write no storage and return an `Outcome` (what
is forwarded to the asset router, the second bridge and the Mailbox).

`Run cfg s l t` is any sequence of successful calls, by any callers, in any order; a
revert is the absence of a step. `Reachable` starts from the state after `initialize`.

## What to check

**Chain registration**

- A chain id is registered at most once in any run, and never if it already has a CTM
  (`ChainIdRegisteredOnce`), because no entry point clears a chain's CTM
  (`CtmNeverCleared`).
- Every chain's base token is a registered asset (`ChainBaseTokenRegistered`); every
  chain's CTM was added by `addChainTypeManager` earlier in the run
  (`ChainCtmWasApproved`).
- Outside `forwardedBridgeMint`, a registered chain's CTM and base token never change
  (`CtmAndBaseTokenFixedOutsideBridgeMint`). `forwardedBridgeMint` (chain asset handler
  only) rewrites them without comparing (`BridgeMintRewritesBaseToken`).
- Without the handler's two registry writers, `zkChainMap` and `chainTypeManager` list
  the same chains with nonzero diamonds (`RegistryConsistentWithoutHandler`). Without
  `registerNewZKChain(_, _, false)` the chain count stays within `MAX_NUMBER_OF_ZK_CHAINS`
  (`ChainCountBounded`). With them, the
  Bridgehub's own checks let `createNewChain` overwrite a handler-written map entry
  (`HandlerEntryOverwrittenByCreate`); in the deployed system the message root's
  `ChainExists` check stops that.
- `ctmAssetIdFromAddress` then `ctmAssetIdToAddress` returns the CTM unless the asset-id
  hash collides at two CTM addresses (pinned collision, no injectivity premise), provided
  every `setCTMAssetAddress` passes the CTM address as data, as `CTMDeploymentTracker`
  does (`CtmAssetIdRoundTrip`). The Bridgehub does not enforce this
  (`CtmAssetIdRoundTripNeedsDiscipline`, with an injective hash).

**Settlement layers**

- Every whitelisted settlement layer other than this chain settles on this chain
  (`WhitelistedSettlementLayersSettleHere`); the `SettlementLayersMustSettleOnL1` check in
  the burn hook is load-bearing (`WithoutCheckWhitelistedLayerLeaves`).
- A chain's settlement layer leaves this chain only through the handler's burn hook, to a
  whitelisted layer, from a chain settled here (`MigrationOutOnlyToWhitelisted`).

**Requests**

- Both paths forward all of `msg.value` and keep none; the asset router gets exactly
  `mintValue` in ETH for an ETH-based chain and nothing otherwise; the deposit and the
  Mailbox request carry the same `mintValue`, for the same chain, in that chain's base
  token; the two-bridges L2 sender is the second bridge, above the reserved range
  (`DirectRequestAccounting`, `TwoBridgesRequestAccounting`). The reserved-range check is
  load-bearing (`WithoutMinAddressCheckLowSender`).
- Without the handler's registry writers, every request goes to the registered nonzero
  diamond of a chain with a CTM and is charged in a registered asset
  (`RequestsReachRegisteredChains`). After `createNewChain(c, _, a, _, d)` and no later
  `forwardedBridgeMint` for `c`, requests for `c` are charged in `a`, and go to `d` if no
  handler registry write follows (`RequestChargesCreationBaseToken`).

**Authority and pause**

- Only the owner changes the CTM registry or the settlement-layer whitelist; only the
  owner, admin or chain asset handler changes a chain's CTM, settlement layer or the asset
  registry (`RegistryWritesAuthorized`). A paused Bridgehub creates no chain and serves no
  request (`PauseBlocksCreationAndRequests`).

**Non-vacuity**

`RegistrationWitness` (two chains, one a whitelisted settlement layer, the other migrated
onto it) and `RequestWitness` (both request kinds served for an ETH-based chain) are
explicit runs from `init`.

## Scope of a source comment (internal; ask Kalman before reporting)

`removeChainTypeManager`'s NatSpec (`BB:240`) says removal "stops new Chains from using
the CTM". `forwardedBridgeMint` does not check CTM registration, so the Bridgehub alone
lets a removed CTM be assigned to a chain id it has never seen
(`RemovedCtmStillAssignedByBridgeMint`). On L1 the chain asset handler only lets a chain
that left L1 come back, so the theorem's run uses a handler call the deployed L1 handler
does not make. `L2Bridgehub` (a settlement layer receiving chains for the first time)
shares `forwardedBridgeMint` and is outside this model; that is where the comment would
matter. Low severity: the handler is trusted.

A minor inaccuracy, not stated as a theorem: the comment at `L1:149-150` says a request
for a chain that does not exist reverts "on `bridgehubRequestL2Transaction` as call to
zero address"; it reverts earlier, in `zkChainMap.get` (`EnumerableMap: nonexistent key`).

## What is not modelled

- External calls are inputs (CTM's `createNewChain` result, the diamond's getters, the
  second bridge's reply, `actualRefundRecipient`'s default) or are assumed not to write
  Bridgehub storage (message root, asset router deposit, Mailbox, second-bridge
  confirmation). Reverts inside them are not modelled; omitting a revert only adds steps,
  so the safety results are conservative, but the witnesses and countermodels assume those
  calls succeed. `HandlerEntryOverwrittenByCreate` is one the message root would block.
- Re-entrancy: calls are atomic; the CTM call inside `createNewChain` cannot re-enter
  (`ASSUMPTIONS.md` `MODEL-BRIDGEHUB`).
- `L2Bridgehub`, events, view functions other than `getZKChain`, the `nonReentrant` lock,
  deprecated slots, and the aliasing branch of `setCTMAssetAddress` (L1 only).
- The asset router, the Mailbox and the chain asset handler themselves: the request
  results say what the Bridgehub forwards, not what those contracts do with it.

## Open

- The handler's writes (`registerNewZKChain`, `forwardedBridgeMint`) are trusted. The
  registry-consistency and chain-limit results exclude them; a composed proof with the
  chain asset handler model (to show the deployed handler keeps them) is not done.
- No refinement from this model to compiled code.
