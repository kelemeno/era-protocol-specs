# AssetRouterBase

Source: `contracts/bridge/asset-router/AssetRouterBase.sol` and the two routers
(`L1AssetRouter.sol`, `L2AssetRouter.sol`) in the pinned era-contracts tree
(`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`).

`HandlerRegistration` models one writer, `_setAssetHandlerAddressThisChain`;
`L1AssetRouter` and `L2AssetRouter` reach it through
`setAssetHandlerAddressThisChain`, and the model starts at the internal function.
The model's header quotes the function body, and that quotation matches the pinned
source. Its `RunValid` ("a live route has an accountable tracker") is exactly a
statement about the registration-only fragment of `AllWriters`
(`AllWriters.SingleWriterIsRegisterOnlyFragment`).

`AllWriters` models every write to `assetHandlerAddress` and
`assetDeploymentTracker` at the pin, per router: the `_finalizeDeposit` fallback,
the initializers (`setNativeTokenVault`, `initL2`), the L2 counterpart's
`setAssetHandlerAddress`, and the L1 owner's `setAssetDeploymentTracker`.
`AtomicRecovery` models `L2AssetRouter.recoverAtomicCall` and the refund loop that
calls it. `AtomicRecoveryFaithful` repairs one place where that model differs from
the source: the target of a router-produced call to L1.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| HandlerRegistration | [Specs/HandlerRegistration.lean](Specs/HandlerRegistration.lean) | [Properties/HandlerRegistration.lean](Properties/HandlerRegistration.lean) | [Proofs/HandlerRegistration.lean](Proofs/HandlerRegistration.lean) |
| HandlerRegistrationRuns | [Specs/HandlerRegistrationRuns.lean](Specs/HandlerRegistrationRuns.lean) | [Properties/HandlerRegistrationRuns.lean](Properties/HandlerRegistrationRuns.lean) | [Proofs/HandlerRegistrationRuns.lean](Proofs/HandlerRegistrationRuns.lean) |
| AllWriters | [Specs/AllWriters.lean](Specs/AllWriters.lean) | [Properties/AllWriters.lean](Properties/AllWriters.lean) | [Proofs/AllWriters.lean](Proofs/AllWriters.lean) |
| AllWritersStrong | [Specs/AllWritersStrong.lean](Specs/AllWritersStrong.lean) | [Properties/AllWritersStrong.lean](Properties/AllWritersStrong.lean) | [Proofs/AllWritersStrong.lean](Proofs/AllWritersStrong.lean) |
| VaultMintGate | [Specs/VaultMintGate.lean](Specs/VaultMintGate.lean) | [Properties/VaultMintGate.lean](Properties/VaultMintGate.lean) | [Proofs/VaultMintGate.lean](Proofs/VaultMintGate.lean) |
| CounterpartGate | [Specs/CounterpartGate.lean](Specs/CounterpartGate.lean) | [Properties/CounterpartGate.lean](Properties/CounterpartGate.lean) | [Proofs/CounterpartGate.lean](Proofs/CounterpartGate.lean) |
| AtomicRecovery | [Specs/AtomicRecovery.lean](Specs/AtomicRecovery.lean) | [Properties/AtomicRecovery.lean](Properties/AtomicRecovery.lean) | [Proofs/AtomicRecovery.lean](Proofs/AtomicRecovery.lean) |
| AtomicRecoveryFaithful | [Specs/AtomicRecoveryFaithful.lean](Specs/AtomicRecoveryFaithful.lean) | [Properties/AtomicRecoveryFaithful.lean](Properties/AtomicRecoveryFaithful.lean) | [Proofs/AtomicRecoveryFaithful.lean](Proofs/AtomicRecoveryFaithful.lean) |

Namespaces: `Contracts.AssetRouter` (HandlerRegistration, HandlerRegistrationRuns),
`Contracts.AssetRouter.AllWriters` (AllWriters, AllWritersStrong, VaultMintGate,
CounterpartGate),
`Contracts.AssetRouter.AtomicRecovery` and
`Contracts.AssetRouter.AtomicRecoveryFaithful`. Statements are `<namespace>.Properties.*`;
each certificate has the same name without the `Properties` segment.

## Run-level registration (`HandlerRegistrationRuns`)

Runs of the single writer, from an arbitrary start router, logged one call at a
time (`ReachLog`; logging loses no run, `ReachIffReachLog`). The hash premise is
`IdInjOn` on the triples the run's calls hashed (one per call,
`LoggedTriplesCardLe`) plus the watched triple. Under it:

- the route and tracker at every id are what the last call hashing that id's triple
  set, or the start router's (`LoggedRouteIsLastOwnWrite`; without the guard,
  `RouteIsLastOwnWriteWithoutGuard`; unhashed triples, `LoggedRunLeavesUnhashedRoutes`);
- no step moves another sender's route (`LoggedRunNoHijack`,
  `LoggedRunNtvTouchesOnlyItsOwnIds`), and a custom route answers only to its
  registrant (`LoggedRunCustomRouteAnswersToRegistrant`);
- a vault-installed route survives every later call except a vault re-registration
  of the same data (`LoggedRunKeepsVaultRoutes`, with `IdInjOn` on the log alone).

With no hash premise: a vault route survives every non-vault call
(`NtvRouteSurvivesNonVaultCalls`, `VaultTrackerIsPermanent`,
`NonVaultRunKeepsVaultRoutes`), and, since the deployed vault always names itself as
handler, vault-held routes keep pointing at the vault (`VaultHeldRoutesPointAtVault`).
From fresh storage only the vault passes the guard (`OnlyVaultActsFromEmpty`); on L2,
whose other writers write handlers only, that stays so (`OnlyVaultActsAmidOtherWriters`).
A custom tracker exists only after L1's owner-only `setAssetDeploymentTracker`, which
is why these runs start from an arbitrary router.

Countermodels: one logged collision lets a vault call take over a live custom route
(`LoggedCollisionTakesOverLiveRoute`); a colliding vault call moves a vault route
(`CollidingVaultCallMovesVaultRoute`); without the `require`, the hash alone does not
protect vault routes (`HashAloneDoesNotProtectVaultRoutes`).

## Every writer (`AllWriters`, `VaultMintGate`, `CounterpartGate`)

- **`RunValid` is false on the deployed routers.** One fallback deposit breaks it, on
  every deployment (`FinalizeFallbackBreaksValid`, `RunValidFailsAfterOneDeposit`,
  `AllWritersRunValidFalse`); the seed and the counterpart do too
  (`SeedAndCounterpartBreakValid`).
- **`WeakValid` holds instead:** every live route has a nonzero tracker or is a vault
  route. With no hash premise along runs without counterpart or zero-tracker writes
  (`RunWeakValid`, `L2RunWeakValid`); along every L1 run under `IdInjOn` on the run's
  logged triples (`L1RunWeakValidOn`, `RunWeakValidOn`). Each premise is needed
  (`CounterpartBreaksWeakValid`, `ZeroTrackerBreaksWeakValidUnderCollision`,
  `NonVaultMintBreaksWeakValid`, `NonVaultSeedBreaksWeakValid`).
- **No hijack, except through the counterpart** (`NoHijackOnExceptCounterpart`, premise
  on the two compared triples). On L2 only the vault ever registers
  (`L2OnlyVaultRegisters`, no hash premise), and every non-counterpart call changes
  handlers only at vault ids (`L2OnlyCounterpartTouchesNonVaultIds`).
- **The counterpart is the explicit trusted exception** (`CounterpartRepointsAnyRoute`,
  `CounterpartRepointsVaultRoute`). `CounterpartGate` models the L1 router's tracker
  check and narrows it: a vault triple's id on L2 is only ever unset, tracked, or
  pointed at the L2 vault (`CounterpartCannotMisrouteVaultTriple`,
  `L1CounterpartAtVaultIdOn`, `L1CounterpartAtVaultIdOrLoggedClash`). The exception
  remains for custom assets (`CustomTrackerNamesAnyHandler`).
- **Each tracker was recorded by a logged call, at that call's own id**
  (`AllWritersStrong`: `RunTrackerRecorded`, no hash premise). `RunTrackerHashed` alone
  is weak: its data word is existential, so an encoding that reaches every id satisfies
  it in every state (`TrackerHashedAdmitsUnreachableRouter`). The owner cannot hand a
  tracker an id hashed from someone else when no logged triple clashes with that id
  (`RunTrackerNotHandedToOtherSenderOn`); with a clash it can
  (`TrackerHandedToOtherSenderUnderCollision`).
- `VaultMintGate` proves the fallback's vault premise `MintsOnlyNtvIds` from the
  vault's own registry model, with no hash premise (`VaultRunIdShape`,
  `VaultModelDischargesMintPremise`, `RunWeakValidWithVaultModel`).

`IsNtvId` is existential (some preimage with the vault as sender). For a keccak-like
encoding almost every id has one, so the id conjunct of a vault route is weak; the
handler conjunct is the informative part. The pinned forms are registration triples,
`CounterpartGate`'s named triple, and the vault's own record (`VaultRunIdShape`).

Source documentation (both verifiers classify it as a documentation error; reported
to the maintainer of this repo, not yet confirmed upstream): `AssetRouterBase.sol:61-64`
("custom tokens may have their own specific asset deployment trackers") holds on L1
only. On L2 every tracker is zero or the vault (`L2OnlyVaultRegisters`,
`OnlyVaultActsAmidOtherWriters`). The docstring of `Properties/HandlerRegistration.lean`
says a custom tracker is bootstrapped "through the native token vault or the L1-to-L2
counterpart path"; neither records a custom tracker, and the only bootstrap is L1's
owner-only `setAssetDeploymentTracker` (`OnlyVaultActsFromEmpty`).

## Atomic recovery (`AtomicRecovery`)

What is modelled: `recoverAtomicCall` (`L2AssetRouter.sol:281-296`); the vault's
`bridgeRecoverFailedTransfer` guard chain as far as `assetIdCheck`
(`NativeTokenVaultBase.sol:213-306, 573-586`), over the registry model's vault;
`_burn`'s handler choice (`AssetRouterBase.sol:322-336`); `_validateAtomicBundle`
(`InteropCenter.sol:670-677`); and the manager's `_recoverBundle`/`claimRefund` loop on
threaded state (`AtomicFlowManager.sol:165-180, 219-230`).

| Result | Statement |
|---|---|
| `RecoveryCallsTheVault`, `RecoveryIgnoresHandler`, `BurnUsesRegisteredHandler` | The refund always calls the vault and never reads the routing table; the source burn uses the registered handler. No premises. |
| `VaultRejectsUnknownAsset`, `UnknownAssetRecoveryReverts` | An asset the vault does not know, whose id is not the NTV id of the decoded pair, makes the refund revert rather than return `false`. No hash premise. |
| `CustomIdFailsAssetIdCheckOn`, `CustomIdUnknownAlongLoggedRunsOn`, `CustomAssetRecoveryRevertsOrCollision` | A custom-handler id fails that check and is never registered by the vault along any logged registry run, under `IdInjOn` on the custom triple paired with one NTV triple (or a pinned collision). |
| `CustomHandlerDepositRefundReverts` | Headline (a): the refund of a custom-handler deposit reverts. |
| `CustomHandlerBundleNeverRefunded` | Headline (b): one such call blocks every claim of its bundle, vault-asset calls included, in every registry state the model reaches. Also `UnknownAssetOutcomeBlocksClaim`, `ClaimRevertsWithUnknownAssetCall`, `LegNeverRefunded`; concrete: `CustomHandlerBundleIsStranded`. |
| `ClaimSucceedsIffAccepted` | The stateful loop succeeds iff the outcome list satisfies `RecoveryLimits.ClaimAccepted`. |
| `PreparedBurnRefundsDepositor` | Headline (c): router-produced calls on assets the vault knows refund the burn's original caller the burned amount (`KnownBridgedAssetRefundsOriginalCaller`, `NativeAssetRefundsOriginalCaller`, `RefundIgnoresRemoteReceiver`). |
| `RefundIgnoresCallSender`, `DirectCallIsRefunded`, `DirectCallMintsUnbacked` | Countermodel: the refund cannot see a call's sender, so a direct call with self-written mint data is refunded although nothing was burned. |
| `RecoveryOnlyByManager`, `VaultRefundOnlyByRouter` | Only the manager invokes recovery; only the router invokes the vault's refund. |

Possible findings (both verifiers classify them as real bugs; reported to the
maintainer of this repo, not yet confirmed upstream):

- Custom-handler assets: `recoverAtomicCall` reverts instead of returning `false`
  (`IAtomicRecoverable.sol:13-15`), `_recoverBundle` has no try/catch, so the whole
  bundle's refund reverts and its leg stays `Revertable` (headlines (a), (b)). The
  guidance to make fund-moving legs asset-router calls (`AtomicFlowManager.sol:215-217`)
  does not cover custom-handler assets.
- Direct calls: a direct atomic call to the router with arbitrary `finalizeDeposit`
  data is refunded with no source burn (`DirectCallIsRefunded`). The step that brings
  such a leg to `Revertable` (`authorizeRefund` on a phantom leg) is argued from
  source, not modelled.
- A `finalizeDeposit`-selector call whose outer arguments fail to decode also reverts
  (`CallData.malformedFinalizeDeposit`); it blocks only the sender's own bundle.

## Atomic recovery by destination (`AtomicRecoveryFaithful`)

`AtomicRecovery.routerCall` always targets `L2_ASSET_ROUTER_ADDR`. The router chooses
the target by destination: `_chainId == L1_CHAIN_ID ? address(L1_ASSET_ROUTER) :
request.l2Contract` (`L2AssetRouter.sol:336`). `routerCallTo` models that choice, and
`CenterEnv`/`PinSendChecks`/`pinSend` model the checks of `InteropCenter.sendBundle`
that restrict an L1 destination, plus `_validateAtomicBundle` and `_dispatchBundle`'s
branch. The other send checks read no atomic flag and are omitted (listed in the
Specs header); the admission results do not say every send succeeds.

| Result | Statement |
|---|---|
| `RouterCallToL2IsModelled`, `RouterCallToL1RetargetsModelled` | Off L1 the real call is `routerCall`, so every `AtomicRecovery` result on `routerCall` holds for it; to L1 only the target differs. No premises. |
| `L1LegRefundBypassesRouter`, `L1LegClaimOnlyByForeignCode` | With `L1_ASSET_ROUTER ≠ L2_ASSET_ROUTER_ADDR`, the refund of an L2→L1 call is whatever the code at the L1 router's address on L2 does, and a one-call claim succeeds exactly when that code returns `true`. Concrete: `L1LegForeignTrueClosesWithoutRefund` (a foreign `true` closes the leg, nothing refunded). |
| `L1LegRefundReverts`, `L1LegNeverRefunded` | Adding `CodelessAt` (no code at that address, `VM-CALL`), the refund reverts and every claim of every bundle containing the call reverts, in every leg state and world. |
| `PreparedBurnRefundsDepositorToL2`, `PreparedBurnRefundByDestination` | Headline (c) on the real call: holds off L1 (witness `PreparedBurnRefundToL2Satisfiable`); for every destination, an exact case split. |
| `PreparedBurnRefundFailsToL1` | Countermodel: one burn to L1 meets every premise of `AtomicRecovery.PreparedBurnRefundsDepositor`; the modelled call is refunded, the real one reverts. |
| `PinAdmitsAtomicL1Leg`, `PinAtomicityIrrelevantToL1`, `UpgradeGuardRejectsAtomicL1` | At the pin, atomicity never changes whether an L1 send passes the modelled checks; it only turns publication into `append`. The upgrade's guard (`e561b9cc2`, `InteropCenter.sol:550-554`) rejects the atomic L1 send. |
| `AtomicL1LegIsStranded` | Headline (d), concrete: a prepared burn to L1 debits the depositor, the pin appends its atomic bundle instead of publishing it, and no claim of that bundle ever succeeds. |
| `CustomHandlerBundleIsStrandedToL2` | `AtomicRecovery.CustomHandlerBundleIsStranded` on the real calls of a two-call bundle to another L2 that passes `PinSendChecks`. |

Environment premises: `L1_ASSET_ROUTER ≠ L2_ASSET_ROUTER_ADDR` (`OPS-CONFIG`) and
`CodelessAt other L1_ASSET_ROUTER` (`VM-CALL`, one address). No hash premise. That L1
never executes an unpublished atomic bundle rests on message-inclusion soundness
(`PROTO-EVIDENCE`) and is argued from source, not modelled; so are `append`'s own
checks and the step that moves such a leg to `Revertable`.

Possible finding (one agent's analysis, not independently verified; not reported
upstream): at the pin an atomic bundle to L1 is admitted and appended, never
published, and its refund cannot reach the router, so the burned amount is neither
minted on L1 nor refunded (`AtomicL1LegIsStranded`). The upgrade tree `e561b9cc2`
rejects it at send time and in `_recoverBundle`.

## Assumptions to review

`NoHijack` and `NtvTouchesOnlyItsOwnIds` take `IdAssumptions enc` as a premise.
Its `inj` field states that `encodeAssetId` is injective on all
(chain, sender, data) triples of 256-bit words. No function into 256-bit words
can satisfy that, so as stated those two properties hold vacuously. See
`CRYPTO-ID` in the [assumption register](../../../ASSUMPTIONS.md). The other six
original `HandlerRegistration` properties do not use the premise. Bounded forms
exist: per call `NoHijackOn`, `NtvTouchesOnlyItsOwnIdsOn` (and the `…OrCollision`
forms); per logged run the `HandlerRegistrationRuns` results above;
`AllWriters.NoHijackOnExceptCounterpart` (pair) and `AllWriters.L1RunWeakValidOn`
(logged triples). No reduction-style (collision-finding) form is stated.

`AllWriters` premises: `MintsOnlyNtvIds`, discharged by `VaultMintGate`; the L2
seeded `_baseTokenAssetId` is a vault id (`OPS-CONFIG`, load-bearing:
`NonVaultSeedBreaksWeakValid`); `CounterpartGate.VaultApprovals` (no code at
`0x10004` on L1); per-message L1 provenance of counterpart writes
(`PROTO-EVIDENCE`). Initializers are over-approximated as repeatable.

`AtomicRecovery` premises: call and mint data are typed (`SOL-ABI`); the vault's
tracker, transfer, deploy and mint effects are hooks on an abstract rest of the
world that cannot write the registry, the router maps or the pause flag
(`DEP-FRAME`); other bundle targets are arbitrary, under the explicit premise
`OthersLeaveAlone`. Vault registry writes that are not registry-model steps (the
base-token write in `updateL2`, recovery and mint deploys) are covered only through
`LegNeverRefunded`.

Everything here is abstract. Events, `msg.value`, pause, `nonReentrant`, router
upgrades, `_setAssetHandler`'s other effects, the L1 failed-deposit path
(`bridgeConfirmTransferResult`, which does use the handler), and ABI encoding of the
id preimage are not modelled. Router storage and call correspondence are open.
