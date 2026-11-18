# AssetRouterBase

Source: `contracts/bridge/asset-router/AssetRouterBase.sol` and the two routers
(`L1AssetRouter.sol`, `L2AssetRouter.sol`) in the pinned era-contracts tree
(`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`). `HandlerGateAtV35` and `AtomicRecoveryAtHead`
are pinned at `draft/v0.35.0` (`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`); see their sections
below.

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
calls it. `AtomicRecoveryFaithful` models one place where that model differs from
the source, the target of a router-produced call to L1, and restates the results
that depend on it. `AtomicRecovery.routerCall` itself is unchanged.
`AtomicRecoveryAtHead` models the refund at `draft/v0.35.0` (`b17415d20`), where the
manager dispatches on the call's sender and the router refunds through the asset's
registered handler.

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
| PausedRecovery | [Specs/PausedRecovery.lean](Specs/PausedRecovery.lean) | [Properties/PausedRecovery.lean](Properties/PausedRecovery.lean) | [Proofs/PausedRecovery.lean](Proofs/PausedRecovery.lean) |
| AtomicRecoveryAtHead | [Specs/AtomicRecoveryAtHead.lean](Specs/AtomicRecoveryAtHead.lean) | [Properties/AtomicRecoveryAtHead.lean](Properties/AtomicRecoveryAtHead.lean) | [Proofs/AtomicRecoveryAtHead.lean](Proofs/AtomicRecoveryAtHead.lean) |
| HandlerGateAtV35 | [Specs/HandlerGateAtV35.lean](Specs/HandlerGateAtV35.lean) | [Properties/HandlerGateAtV35.lean](Properties/HandlerGateAtV35.lean) | [Proofs/HandlerGateAtV35.lean](Proofs/HandlerGateAtV35.lean) |

Namespaces: `Contracts.AssetRouter` (HandlerRegistration, HandlerRegistrationRuns),
`Contracts.AssetRouter.AllWriters` (AllWriters, AllWritersStrong, VaultMintGate,
CounterpartGate),
`Contracts.AssetRouter.AtomicRecovery`,
`Contracts.AssetRouter.AtomicRecoveryFaithful`,
`Contracts.AssetRouter.AtomicRecoveryAtHead` and
`Contracts.AssetRouter.HandlerGateAtV35`. Statements are `<namespace>.Properties.*`;
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
| `PreparedBurnRefundsDepositor` | Headline (c): router-produced calls on assets the vault knows refund the burn's original caller the burned amount (`KnownBridgedAssetRefundsOriginalCaller`, `NativeAssetRefundsOriginalCaller`, `RefundIgnoresRemoteReceiver`). This is about `routerCall`, which is the router-produced call only for a destination other than L1. For an L1 destination the call targets `L1_ASSET_ROUTER` and the result does not apply: see `AtomicRecoveryFaithful` below. |
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
`formedCall` the call the center forms from a starter routed through the router
(`InteropCenter.sol:709-740`). `CenterEnv`/`PinSendChecks`/`pinSend` model the checks of
`InteropCenter.sendBundle` that restrict an L1 destination, plus `_validateAtomicBundle`
and `_dispatchBundle`'s branch. The other send steps are omitted and listed in the Specs
header. Two of them depend on atomicity: the decoding of the `atomicBundle` attribute,
and the manager's `append`, which runs only for an atomic send. That the omitted steps
otherwise treat an atomic send to L1 like the L2→L1 withdrawal is argued from source.
The admission results are about the modelled checks only; they do not say every send
succeeds.

`routerCall`, `PausedRecovery` and `AssetBridgePreparation`'s `FullRecovery` are
unchanged. Their statements are about calls that target the router, which a
router-produced call to L1 does not, unless `L1_ASSET_ROUTER` equals
`L2_ASSET_ROUTER_ADDR`.

| Result | Statement |
|---|---|
| `RouterCallToL2IsModelled`, `RouterCallToL1RetargetsModelled` | Off L1 the real call is `routerCall`, so every `AtomicRecovery` result on `routerCall` holds for it; to L1 only the target differs. No premises. |
| `RouterStarterFormsRouterCall` | The call the center forms from the router's starter is `routerCallTo` if and only if the center's `L2_ASSET_ROUTER_ADDR` is the router's address. |
| `L1LegRefundBypassesRouter`, `L1LegClaimOnlyByForeignCode` | With `L1_ASSET_ROUTER ≠ L2_ASSET_ROUTER_ADDR`, the refund of an L2→L1 call is whatever the code at the L1 router's address on L2 does, and a one-call claim succeeds exactly when that code returns `true`. Witness: `L1LegForeignTrueClosesWithoutRefund` (a foreign `true` that changes nothing closes the leg, nothing refunded). |
| `L1LegRefundReverts`, `L1LegNeverRefunded` | Adding `CodelessAt` (no code at that address, `VM-CALL`), the refund reverts and every claim of every bundle containing the call reverts, in every leg state and world. |
| `PreparedBurnRefundsDepositorToL2`, `PreparedBurnRefundByDestination` | Headline (c) on the real call: holds off L1 (witness `PreparedBurnRefundToL2Satisfiable`); for every destination, an exact case split. |
| `PreparedBurnRefundFailsToL1` | Countermodel: one burn to L1 meets every premise of `AtomicRecovery.PreparedBurnRefundsDepositor`; the modelled call is refunded, the real one reverts, under the two environment premises. |
| `PinAdmitsAtomicL1Leg`, `PinAtomicityIrrelevantToL1`, `PinL1SendIsRouterStarter` | At the pin, atomicity never changes whether an L1 send passes the modelled checks; it only turns publication into `append`. The only starter list those checks admit for L1 is the router's one starter. |
| `UpgradeGuardRejectsAtomicL1` | The guard of the other tree, `e561b9cc2` (`InteropCenter.sol:550-554`), rejects the atomic L1 send. That tree is not a successor of the pin. |
| `AdmittedAtomicL1LegNeverRefunded` | Headline (d). Premises: the center is on an L2, the center and the router agree on `L1_CHAIN_ID` and `L2_ASSET_ROUTER_ADDR`, and the two environment premises. Then the atomic one-starter send to L1 passes the modelled checks and is appended instead of published, the call the center forms from the starter is the router-produced call to L1, and no claim of that bundle ever succeeds, in any world and leg state. |
| `AtomicL1LegIsStranded` | Headline (d), one instance: a burn prepared by the configuration's own vault, on its chain, called by its router, debits the depositor, and the bundle formed with its mint data is stranded. |
| `CustomHandlerBundleIsStrandedToL2` | `AtomicRecovery.CustomHandlerBundleIsStranded` on the real calls of a two-call bundle to another L2 that passes `PinSendChecks`. The bundle the center forms from the two starters is the bundle of the two router-produced calls. |

Environment premises: `L1_ASSET_ROUTER ≠ L2_ASSET_ROUTER_ADDR` (`OPS-CONFIG`) and
`CodelessAt other L1_ASSET_ROUTER` (`VM-CALL`, one address). No hash premise. The three
instances with a prepared burn (`PreparedBurnRefundFailsToL1`,
`PreparedBurnRefundToL2Satisfiable`, `AtomicL1LegIsStranded`) tie the burning vault to
the refund configuration: same chain, the vault's own address, its router, and the
burn's caller; the burn goes to another chain. The two with a refund world also have its registry agree with the vault
on the asset's local token and origin chain.

That L1 never executes an unpublished atomic bundle is argued from source, not
modelled here. This chain's half of it, that the bytes of an atomic dispatch are never
the bytes of a bundle published to L1, is `Contracts.InteropCenter.AtomicBytesNeverPublished`
(under `EncInjOn`, except a pinned cross-sender salt clash). The L1 side rests on
message-inclusion soundness (`PROTO-EVIDENCE`). That `append` accepts such a leg, and
the step that moves it to `Revertable`, are argued from source too.

Possible finding (one agent's analysis; one independent review of this model, on
2026-11-14, re-traced the send, execution and refund paths in the pinned source and
agreed; no severity assessed; not reported upstream and not confirmed there). At the
pin, an atomic one-call bundle to L1 passes the destination and atomicity checks and is
dispatched to the manager's `append`, never published. If `L1_ASSET_ROUTER` is not
`L2_ASSET_ROUTER_ADDR` and has no code on the L2, the refund of that bundle cannot reach
the router, so the burned amount is neither minted on L1 nor refunded
(`AdmittedAtomicL1LegNeverRefunded`, instance `AtomicL1LegIsStranded`). Without the
no-code premise the refund is whatever the code at that address does
(`L1LegClaimOnlyByForeignCode`). The other tree, `e561b9cc2`, rejects the send
(`InteropCenter.sol:550-554`) and the recovery of an L1-destined bundle
(`AtomicFlowManager.sol:295`).

## Atomic recovery while the vault is paused (`PausedRecovery`)

Namespace `Contracts.AssetRouter.PausedRecovery`, in `AtomicRecovery`'s refund model, whose
world already carries the vault's `paused()` flag and whose vault refund begins with
`whenNotPaused` (`NativeTokenVaultBase.sol:217`). It adds the owner's `pause()`/`unpause()`
(`pauseVault`, `unpauseVault`: OpenZeppelin's guards, writing only the flag) and two frame
premises on the bundle's other targets: `OthersLeavePause` (they do not write the vault's
flag) and `OthersIgnorePause` (they neither read nor write it). No hash premise.

| Result | Statement |
|---|---|
| `PausedVaultRevertsRouterDeposit`, `PausedRouterDepositBlocksClaim`, `RouterRefundLeavesPause` | While the vault is paused, `recoverAtomicCall` on any `finalizeDeposit` call reverts (outcome `reverts`, not `declined`), so no outcome list containing it is accepted. A returning router refund leaves the flag alone. |
| `PausedVaultBlocksClaim` | Paused vault, `OthersLeavePause`, and a call in the bundle that targets the router with `finalizeDeposit` data (`HasRouterDeposit`): `claimRefund` reverts, for any leg state, on the state the earlier calls leave. The leg keeps its state. |
| `PauseIrrelevantWithoutRouterDeposit` | With `OthersIgnorePause` and no router deposit, the claim's result does not depend on the flag. |
| `PauseUnpauseRoundTrip`, `PausedClaimRetriedAfterUnpause` | A claim that succeeds on an unpaused world reverts once the vault is paused; pause then unpause returns exactly the original world, where the claim gives the same result. |
| `PausedPreparedBurnRefundDelayed` | In `PreparedBurnRefundsDepositor`'s setting (a burn the vault prepared from a `WellFormed` state, an asset the refund world knows as bridged, a returning tracker hook): the router call carrying the burn's data reverts while paused, and unpaused it re-mints the burned amount to the depositor. Stated on `routerCall`, the router-produced call only for a destination other than L1. |

Witness: `PausedRecoveryWitness`, on `AtomicRecovery`'s concrete world: a one-call bundle
with a vault-asset router deposit is claimed unpaused and reverts paused, and a bundle with
no router deposit is claimed both paused and unpaused. A router-produced call to L1 targets
`L1_ASSET_ROUTER` and is a router deposit here only if that address is
`L2_ASSET_ROUTER_ADDR` (`OPS-CONFIG`). The protocol-level pause model is
`Protocol/InteropAtomicity` `Pause`, whose refund gate reads the vault flag exactly for
bundles with a router call, which `PauseIrrelevantWithoutRouterDeposit` justifies for this
model.

## Atomic recovery at head (`AtomicRecoveryAtHead`)

Source: `draft/v0.35.0` at `b17415d20`; the modelled functions are the same at `main`
`70096e2ea`. Two upstream changes replaced the pin's refund. The manager dispatches on
`InteropCall.from` (`AtomicFlowManager.sol:312-323`), ignores the router's answer, and no
longer rejects a claim that recovers nothing. `recoverAtomicCall` calls the handler that
`assetHandlerAddress` names at claim time (`L2AssetRouter.sol:299-302`). A direct call's
value is refunded through `bridgehubRecoverBaseToken` (`:314-328`). On L2 the vault's
refund gained a base-token branch (`L2NativeTokenVault.sol:204-227`); off this chain's
base token it is the pin model's `ntvRecover`. The pin model is unchanged.

| Result | Statement |
|---|---|
| `DirectCallSkipsRouterRecovery`, `DirectCallDataIgnoredAtHead`, `CallTargetIgnoredAtHead`, `DirectValueLegRefundsItsSenderAtHead`, `CrossBaseValueLegRefundAtHead`, `SameBaseValueLegRefundAtHead` | A call not from the router never reaches `recoverAtomicCall`: its iteration is the vault's refund of the call's own value to its own sender, or nothing when the value is zero. No call's target is read. |
| `DirectBundleClaimIsNoOpAtHead` | Headline (a): a bundle of zero-value direct calls is claimed as a no-op, whatever data the calls carry. For a sender other than the router only indirect starters yield calls from the router (`RouterSenderIffIndirectAtHead`, `SentDirectCallNeverRecoveredAtHead`). The pin's forged-refund instance is rejected (`PinUnbackedMintRejectedAtHead`), and `DirectCallIsRefunded` is false of the head (`DirectCallIsRefundedFailsAtHead`). |
| `VaultRecoverAtHeadIsPinRefundOffBaseToken`, `VaultRecoverAtHeadOnBaseToken`, `VaultRouterCallIsPinIterationAtHead` | Off this chain's base token and off L1 the vault's head refund is the pin model's `ntvRecover`; on the base token it is the base-token holder's `recoverBaseToken`. While the vault handles an asset, a router call's head iteration equals the pin model's iteration on the pin's router call, so the pin's results about it apply. |
| `RecoveryReadsClaimTimeHandler`, `BurnLeavesBurnHandler`, `NoRotationKeepsHandler`, `NoRotationKeepsHandlerLoggedOn`, `HandlerMovesOnlyByRotation` | The refund uses the handler registered at claim time. The burn leaves its own handler registered, and a run of the router-map writers (`AllWriters`) that rotates nothing leaves it there: no hash premise, or in the logged form `IdInjOn` on the asset's triple paired with each triple the run hashes. |
| `RouterLegReachesBurnHandler`, `RouterLegReachesBurnHandlerLoggedOn` | Headline (b): without a rotation, a router leg's refund is the burn handler's own refund on the burn's bytes. Also `CustomHandlerRecoveredByItsHandler` (no hash premise), `PreparedBurnRefundsDepositorAtHead`, `PinStrandedBundleRefundedAtHead`; `RecoveryCallsTheVaultFailsAtHead`, `RecoveryIgnoresHandlerFailsAtHead`. |
| `VaultBurnRefundsDepositorAfterRunAtHead` | Headline (b) for a vault burn: after any run of the writers that does not rotate the asset away from the vault, the router leg's refund re-mints the prepared burn's amount to its depositor (with the vault-side premises of `PreparedBurnRefundsDepositorAtHead`). |
| `RotationToNoOpHandlerStrandsBurn`, `RotationToRevertingHandlerBlocksClaim`, `ZeroedHandlerRecoveryReverts`, `L2RotationOnlyByCounterpartSeedOrVault` | Headline (c), upstream known issue 5 (`protocol-docs/atomicity/security.md:149-156`), as concrete instances: one counterpart call between burn and claim that re-points the asset at a no-op handler lets the claim consume the leg with nothing refunded, and one that re-points it at a reverting handler blocks the claim until a second call points it back. An unset handler makes the refund revert. On L2, along runs from fresh storage, only the counterpart, the initializer and the vault's own registration rotate a live route. |
| `ClaimSucceedsIffLoopCompletesAtHead`, `RevertingCallBlocksClaimAtHead`, `UnrecoverableHandlerBlocksBundleAtHead`, `HandlerWithoutRecoveryStrandsBundleAtHead` | Headline (d): a claim succeeds exactly when no attempted recovery reverts, so one call that reverts in every reachable world blocks its whole bundle. |
| `NothingRecoveredStillConsumesLegAtHead`, `UnrecognisedRouterCallConsumedAtHead`, `PinRejectsNothingRecoverableHeadAccepts` | A claim that recovers nothing consumes the leg (upstream known issue 1). |
| `L1DestinationClaimRevertsAtHead` | (e) A claim with an L1 destination reverts in every leg state. An atomic bundle to L1 is rejected at send (`InteropCenter.sol:552-553`), which is not modelled. |

Model boundaries (Specs header; `MODEL-ATOMIC-RECOVERY-HEAD`): the code at every handler
other than the vault is arbitrary (`HandlerCode`); the vault's hooks and the base-token
holder's `recoverBase` write only the rest of the world (`DEP-FRAME`); call and mint data
are typed (`SOL-ABI`); router-map writes between burn and claim are `AllWriters` steps;
the `L1_CHAIN_ID` slots of router, manager and tracker are one value, and the
`BASE_TOKEN_ASSET_ID` slots of vault and tracker another (`OPS-CONFIG`); the send side is
`_processCallStarter` alone, with the premise that the router never sends a bundle
itself; `nonReentrant`, events and `claimRefund`'s bundle decoding are omitted. The only
hash premises are in the two `…LoggedOn` forms. Every property with premises has a
witness (the `…Satisfiable` statements and `ZeroedHandlerReachableByCounterpart`).

## The v35 handler gate (`HandlerGateAtV35`)

Pinned at `draft/v0.35.0` (`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`). The router, message-root
and Bridgehub files it cites are unchanged from the earlier head `d9f6789`. v35 adds a check
to the L1 router, `_checkAssetHandlerAllowed` (`L1AssetRouter.sol:276-288`). It runs first in
`bridgehubDepositBaseToken`, `bridgehubDeposit` (new encoding), `finalizeDeposit` and
`bridgeConfirmTransferResult`, and lets the call through when the asset's handler is unset, the
router's vault or `BRIDGE_HUB.chainAssetHandler()`, or when the chain is interop-enabled in the
current message root. The model is `AllWriters`' L1 step relation, plus the four entry points as
events that move an asset through its handler, plus `L1MessageRoot.enableInterop` and
`L1Bridgehub.setAddresses` as the events that change what the gate reads. The handlers' own calls
are taken to succeed and the entry points' other checks are not modelled, so "has a step" means
that the gate and the handler-set check let the call through.

| Result | Statement |
|---|---|
| `MovementEnabledIff` | A gated entry point at `(c, a)` has a step exactly when `a`'s handler is set and `(c, a)` is not stranded (custom handler, `c` without interop), and it changes nothing. The gate never stops the fallback. No premises. |
| `MovementsUseExemptHandlerOrEnabledChain` | In every run, each event moving an asset at chain `c` moved it through the router's vault or the chain asset handler of the state it ran in, or `c` was interop-enabled in that state. Witness `CustomMovementAtEnabledChainWitness`. |
| `MovementsAtDisabledChainUseExemptHandler` | Along a run without `setAddresses`, every asset moved at a chain still without interop at the end moved through the vault or the chain asset handler. Witness `MovementsAtDisabledChainWitness`. |
| `RunProjectsToAllWriters`, `GatedRunWeakValidOn` | The router maps of every v35 run follow the `AllWriters` L1 run of its router-writing calls, so the gate adds no writer and `AllWriters`' L1 results carry over, for instance `WeakValid` under the run-local `IdInjOn`. Witnesses `RunProjectsToAllWritersWitness`, `GatedRunWeakValidOnWitness`. |
| `InteropFlagsOneWayWithoutSetAddresses` | Without `setAddresses`, the chain asset handler stays, enabled chains stay enabled, and only `enableInterop(c)` changes `c`'s flag. Witness `InteropFlagsOneWayWitness`. |
| `StrandedUntilListedCall`, `UnstrandingCallIsListed` | A stranded `(c, a)` stays stranded, and no event moves `a` at `c`, until `enableInterop(c)`, `setAddresses`, `setNativeTokenVault` seeding `a`, or a registration of `a` (by the vault or `a`'s recorded tracker). Witnesses `StrandedUntilListedCallWitness`, `UnstrandingCallIsListedWitness`. |
| `OpenGateStaysOpen` | Once a gated entry point at `(c, a)` has a step, every gated entry point at `(c, a)` keeps one, through the same handler, along every run without `setAddresses` and without a call that can rewrite `a`'s handler. Witness `OpenGateStaysOpenWitness`. |
| `SetAddressesClosesOpenGate`, `RepointingClosesOpenGate` | Both exclusions are needed: a `setAddresses` installing a message root that does not enable `c` closes an open gate, and a tracker's re-registration of an asset routed to the chain asset handler can leave it with a custom handler and close the gate at a chain without interop. |

No hash premise, except `GatedRunWeakValidOn`'s, which is `AllWriters`'. Not modelled: the
handlers' internal state (for instance the vault's per-chain balance cap, which the upstream
documentation gives as the reason for the gate), callers of the configuration events, and router,
Bridgehub and message-root upgrades (`OPS-CONFIG`).

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
`HandlerGateAtV35` models only the v35 gate on that failed-deposit path, with the handler's
own call taken to succeed (`MODEL-ROUTER-GATE-V35`).
