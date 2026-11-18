# Bridgehub

Source: era-contracts `draft/v0.35.0` at commit
**`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`**, files

- `l1-contracts/contracts/core/bridgehub/BridgehubBase.sol`
- `l1-contracts/contracts/core/bridgehub/L1Bridgehub.sol`

The model was first written at `d9f678900e1bc8286412b78f56d4a9f443983c29`. Both files, and
every other file the specs cite, are byte-identical at the two commits, so every
`file:line` in the specs holds at both (`BB:` is `BridgehubBase.sol`, `L1:` is
`L1Bridgehub.sol`). OpenZeppelin is v4.9.6 at the submodule commits `b17415d2` pins.

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

`zkChainMap` is a key set and a value function, read as OpenZeppelin's `EnumerableMap` reads
it: `get` and `tryGet`'s `exists` flag accept a nonzero stored value or a key, and
`getZKChain` is the stored value.

`Run cfg s l t` is any sequence of successful calls, by any callers, in any order; a
revert is the absence of a step. `Reachable` starts from the state after `initialize` on a
fresh proxy at this version; `initialize` cannot be called again.

## What to check

**Chain registration**

- A chain id is registered at most once in any run, and never if it already has a CTM
  (`ChainIdRegisteredOnce`), because no entry point clears a chain's CTM
  (`CtmNeverCleared`).
- Every chain with a CTM has a registered base token (`ChainBaseTokenRegistered`); every
  chain's CTM was added by `addChainTypeManager` earlier in the run
  (`ChainCtmWasApproved`). It need not still be registered: `forwardedBridgeMint` assigns a
  CTM without reading the CTM registry (`RemovedCtmStillAssignedByBridgeMint`).
- A successful `createNewChain` or `registerAlreadyDeployedZKChain` had a registered CTM
  and a registered base token at that moment, writes that chain's CTM, base token,
  settlement layer (this chain) and diamond, and leaves every other chain alone
  (`CreateNewChainPostcondition`, `RegisterDeployedPostcondition`). No entry point
  unregisters an asset id, and ETH's is always registered (`AssetIdNeverUnregistered`).
- While a chain settles here its CTM and base token do not change, whatever is called:
  they can change only in a run that contains a `forwardedBridgeBurnSetSettlementLayer`
  for that chain (`CtmAndBaseTokenFixedWhileSettlingHere`). The `AlreadyCurrentSL` check in
  `forwardedBridgeMint` and the `BridgeHubAlreadyRegistered` check are load-bearing
  (`WithoutCurrentSLCheckBaseTokenRewritten`,
  `WithoutAlreadyRegisteredCheckChainReRegistered`).
- Outside `forwardedBridgeMint`, a registered chain's CTM and base token never change
  (`CtmAndBaseTokenFixedOutsideBridgeMint`). `forwardedBridgeMint` (chain asset handler
  only), for a chain that has left, rewrites them without comparing
  (`BridgeMintRewritesBaseToken`).
- In a run from `init` without the handler's two registry writers, `zkChainMap` and
  `chainTypeManager` list the same chains with nonzero diamonds
  (`RegistryConsistentWithoutHandler`). Without `registerNewZKChain(_, _, false)` the chain
  count stays within `MAX_NUMBER_OF_ZK_CHAINS` (`ChainCountBounded`). With them, the
  Bridgehub's own checks let `createNewChain` overwrite a handler-written map entry
  (`HandlerEntryOverwrittenByCreate`). In the deployed system the message root's
  `ChainExists` check, a revert this model leaves out, stops that (argued from source:
  `ChainAssetHandlerBase.sol:405-409`, `MessageRootBase.sol:146-148`).
- `ctmAssetIdFromAddress` then `ctmAssetIdToAddress` returns the CTM unless two
  `setCTMAssetAddress` calls of the run, for different CTMs, hash to the same asset id (a
  logged collision; no injectivity premise), provided every `setCTMAssetAddress` passes the
  CTM address as data, as `CTMDeploymentTracker` does (`CtmAssetIdRoundTrip`). The
  Bridgehub does not enforce this (`CtmAssetIdRoundTripNeedsDiscipline`, with a hash
  injective in the data and no logged collision). The collision disjunct is needed: it fires
  on a run whose hash, in the data, collides only on the two CTMs' addresses
  (`CtmAssetIdCollisionFires`).

**The chain map**

- `zkChainMap` only grows, and in every reachable state `get` succeeds exactly for its keys
  (`ChainMapOnlyGrows`). A chain's diamond changes only through the handler's
  `registerNewZKChain` for it or through its own registration while it has no CTM
  (`DiamondChangesOnlyByRegistration`), so a registered chain's diamond is fixed in any run
  without a `registerNewZKChain` for it (`DiamondFixedAfterRegistration`). That handler call
  replaces it (`HandlerRegisterReplacesDiamond`).

**Settlement layers**

- Every whitelisted settlement layer other than this chain settles on this chain
  (`WhitelistedSettlementLayersSettleHere`); the `SettlementLayersMustSettleOnL1` check in
  the burn hook is load-bearing (`WithoutCheckWhitelistedLayerLeaves`).
- A chain's settlement layer leaves this chain only through the handler's burn hook, to a
  whitelisted layer, from a chain settled here (`MigrationOutOnlyToWhitelisted`). Over a
  whole run from `init`: a recorded layer other than `0` and this chain was written by a
  burn for that chain and is never the chain itself (`RemoteSettlementLayerCameFromBurn`);
  in a reachable state the target is this chain or settles here right after the move
  (`MigrationTargetSettlesHere`).
- These hold for a layer only while it is whitelisted: a chain can be recorded on a layer
  that is no longer whitelisted and itself settles elsewhere
  (`SettlementLayerOfAChainNeedNotSettleHere`). The run uses handler calls whose
  preconditions in the chain asset handler, CTM and diamond are not modelled.

**Requests**

- Both paths forward all of `msg.value` and keep none; the asset router gets exactly
  `mintValue` in ETH for an ETH-based chain and nothing otherwise; the deposit and the
  Mailbox request carry the same `mintValue`, for the same chain, in that chain's base
  token; the two-bridges L2 sender is the second bridge, above the reserved range
  (`DirectRequestAccounting`, `TwoBridgesRequestAccounting`). The reserved-range check is
  load-bearing (`WithoutMinAddressCheckLowSender`).
- In a run from `init` without the handler's registry writers, every request goes to the
  registered nonzero diamond of a chain with a CTM and is charged in a registered asset
  (`RequestsReachRegisteredChains`). With them, a request still needs a `zkChainMap` key and
  goes to its stored diamond (`RequestNeedsMapEntry`). After `createNewChain(c, _, a, _, d)`
  and no later `forwardedBridgeMint` for `c`, requests for `c` are charged in `a`, and go
  to `d` if no `registerNewZKChain` for `c` follows (`RequestChargesCreationBaseToken`).

**Authority and pause**

- Every write to the Bridgehub's storage is by a caller the source's modifiers admit:
  owner only for the CTM registry, the whitelist and pausing; owner, admin or chain asset
  handler for a chain's CTM, base token, settlement layer and diamond and for the asset
  registry; the CTM deployer for the CTM asset maps; owner or upgrader for the ecosystem
  addresses; the two-step handovers for owner and admin (`RegistryWritesAuthorized`). A
  paused Bridgehub creates no chain and serves no request
  (`PauseBlocksCreationAndRequests`).

**Non-vacuity**

Every property with premises is instantiated on explicit runs from `init` in the Specs
file's deployment `wRegistryCfg`: `wRegistryRun` (two CTMs, a second base token, chains
`10` and `11` created, chain `12` registered as deployed, `10` whitelisted and `11` migrated
onto it) and the handler's run `wRegistryHandlerRun` after it (a burn, a
`forwardedBridgeMint` that changes a chain's CTM and base token, and two
`registerNewZKChain` calls). `RegistryRunWitness`, `HandlerRunWitness`,
`RegistryStepWitness` and `RequestWitness` list which premises each instantiates; in
`HandlerRunWitness` the calls a premise excludes occur in the run for other chains. The
collision disjunct of `CtmAssetIdRoundTrip` is false on `wRegistryRun`
(`RegistryRunWitness`) and true on the run of `CtmAssetIdCollisionFires`.

## What is not modelled

- External calls are inputs (CTM's `createNewChain` result, the diamond's getters, the
  second bridge's reply, `actualRefundRecipient`'s default) or are assumed not to revert
  and not to write Bridgehub storage (message root, asset router deposit, the second
  bridge's `bridgehubDeposit` and confirmation, Mailbox). Omitting a revert only adds steps,
  so the safety results are conservative, but the witnesses and countermodels assume those
  calls succeed. `HandlerEntryOverwrittenByCreate` is one the message root would block; a
  request to a key whose stored diamond is `0` is another (the call to a codeless address).
- Re-entrancy: calls are atomic; no external call re-enters the Bridgehub
  (`ASSUMPTIONS.md` `MODEL-BRIDGEHUB`).
- `L2Bridgehub`, events, view functions other than `getZKChain`, the `nonReentrant` lock,
  deprecated slots, and the aliasing branch of `setCTMAssetAddress` (L1 only).
- The asset router, the Mailbox and the chain asset handler themselves: the request
  results say what the Bridgehub forwards, not what those contracts do with it.

## Open

- The handler's writes (`registerNewZKChain`, `forwardedBridgeMint`) are trusted.
  `RegistryConsistentWithoutHandler` and `RequestsReachRegisteredChains` exclude both;
  `ChainCountBounded` excludes `registerNewZKChain(_, _, false)`, the form the deployed
  handler uses (`ChainAssetHandlerBase.sol:405`). A composed proof with a chain asset handler
  model is not done.
- `Reachable` starts at a fresh proxy at this version. That the deployed proxy's storage,
  written partly by earlier implementations, satisfies the reachable-state results is not
  shown.
- `main` at `70096e2` is not covered. From a diff of the two files only: it renames the
  internal getters, and its `createNewChain` takes three more arguments (`_salt`, unused;
  `_initData` and `_factoryDeps`, forwarded to the CTM with the base-token asset id). The
  model was not re-read against it.
- No refinement from this model to compiled code.
