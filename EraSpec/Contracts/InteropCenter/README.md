# InteropCenter

Source: `contracts/interop/InteropCenter.sol` in the pinned era-contracts tree, with
`contracts/atomic-interop/AtomicFlowManager.sol` for the leg state that `append` writes.
Only the send path is modelled: the salt mapping `isInteropBundleSaltUsed`, bundle
formation in `_sendBundle`, `_validateAtomicBundle`, and `_dispatchBundle` →
`AtomicFlowManager.append`. Topic `AtomicRouting` adds the send entry points' handling of
the `atomicBundle` attribute, the refund loop and the destination handlers' bundle status.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Dispatch | [Specs/Dispatch.lean](Specs/Dispatch.lean) | [Properties/Dispatch.lean](Properties/Dispatch.lean) | [Proofs/Dispatch.lean](Proofs/Dispatch.lean) |
| AtomicRouting | [Specs/AtomicRouting.lean](Specs/AtomicRouting.lean) | [Properties/AtomicRouting.lean](Properties/AtomicRouting.lean) | [Proofs/AtomicRouting.lean](Proofs/AtomicRouting.lean) |

Namespace `Contracts.InteropCenter`. Statements are `Contracts.InteropCenter.Properties.*`;
each certificate has the same name without the `Properties` segment.

- **Salts do not replay.** Along any run of the deployed code from fresh storage, the
  `(sender, salt)` keys of all dispatches are pairwise distinct (`EachSaltDispatchesOnce`;
  no hash premise). The flag records exactly the dispatched keys and is never cleared
  (`SaltFlagRecordsDispatches`, `SaltFlagsNeverCleared`). Without the check the same
  bundle, and so the same bundle hash, is dispatched twice with no hash collision
  (`WithoutSaltCheckABundleRepeats`).
- **Committed legs carry no native value.** Every manager leg that is not `Unset` was
  committed by a logged atomic dispatch of this chain with that flow id and bundle hash,
  whose bundle passed `_validateAtomicBundle` (`CommittedLegsAreValidatedDispatches`; per
  step `OnlyADispatchCommitsALeg`; no hash premise). The model includes a foreign
  direct-`append` step, so the result depends on `onlyInteropCenter` rather than assuming
  it. Both checks are load-bearing (`WithoutValueCheckValueLegCommits`,
  `WithoutOnlyInteropCenterUnbackedLegCommits`). An atomic dispatch burns no base token
  (`AtomicDispatchBurnsNothing`), and each leg is appended at most once
  (`EachLegAppendedOnce`).
  - `AtomicFlowManager`'s `validation_unbypassable` takes the funnel `sole_path` as a
    premise. `SolePath` proves it for the center's appended bundles, and
    `ValidationUnbypassableDischarged` instantiates the statement; both are close to the
    send step's guard, and the content is in `CommittedLegsAreValidatedDispatches`.
  - Following `claimRefund`'s own hash of the bytes it is given, the bundle it decodes
    and recovers carries no value, or keccak collides on two named preimages
    (`ClaimedBundleValidatedOrCollision`, under the decoder round trip on the run's
    bundles; `PresentedBundleValidatedOrClash` is the coarser form).
- **Distinct dispatches, distinct bundles.** Two dispatches carry different bundles unless
  two different senders used the same salt and keccak collides on their packed preimages
  (`DistinctDispatchesDistinctBundles`; no hash premise). With an encoder that separates
  the run's bundles (`EncInjOn`), their bundle-hash preimages differ
  (`DistinctDispatchesDistinctPreimages`), and their hashes differ or keccak collides on
  those preimages (`DistinctDispatchesDistinctBundleHashes`). Under keccak injectivity on
  the run's own preimages, every bundle hash of a run is unique
  (`LoggedRunBundleHashesUnique`). An atomic dispatch's bytes are never a public
  dispatch's bytes on this chain, except under the same salt clash
  (`AtomicBytesNeverPublished`).

Witnesses: `DispatchWitness`, `StepWitness`, `ClaimWitness`, `EncInjOnSatisfiable`,
`KeccakInjOnSatisfiable`. The clash disjuncts fire in
`SaltClashLetsTwoSendersShareABundle` (indirect calls) and
`CollisionLetsAValueBundleMatchACommittedLeg`.

Model boundaries: one chain, with a ghost log of dispatches. `abi.encode(InteropBundle)`
and keccak are abstract; encoder, decoder and keccak premises are run-local, never global.
A revert is the absence of a step, and a send is one step (`nonReentrant`). The indirect
sender's returned recipient and calldata are free. Reject-only checks are omitted (pause,
destinations, fees and `msg.value`, attribute parsing, the tree insert inside `append`,
the proof checks of `authorizeRefund`/`claimRefund`); omitting them only adds runs. The
three checks the results depend on are switches (`Checks`). Not modelled: fee balances
and claims, asset-router/NTV preparation behind indirect calls, other chains, upgrades
(`OPS-CONFIG`), events. The tree side of `append` is `../../Protocol/InteropAtomicity/`
topic `OncePerLeg`.

Source findings, reported to the maintainer of this repo, not yet confirmed upstream:
- `sendMessage` parses its attributes with `CallAndBundleAttributes` (:222-225), under
  which `parseAttributes` accepts `atomicBundle` (:843-854), and then hard-codes
  `isAtomic: false` (:246-252). Such a bundle is published to L1 (:657) and never
  appended to the `AtomicFlowManager`. If it is listed as a leg of a flow, the flow can
  never finalize and the other legs become refundable, while this leg stays executable
  through the ordinary path. Both verifiers classified it as a bug, low severity.
- The same behaviour contradicts `interop/IERC7786Attributes.sol:26-30` (the attribute
  appends the bundle to the IMT instead of publishing it). Both verifiers classified it as
  wrong documentation, low severity.

Neither is formalized at the attribute-parsing level in `Dispatch`; in that model such a
bundle is a public dispatch. Topic `AtomicRouting` models the attribute: see below.

## AtomicRouting

Namespace `Contracts.InteropCenter.AtomicRouting` (`c67894b9`). It composes this chain's
center and manager (`Dispatch`'s state), a ghost log of each send's entry point and
`atomicBundle` attribute, the source chain's code map and world for the refund loop
(`AtomicFlowManager` topic `RecoveryTargets`), and every destination's `bundleStatus`.
`pin` is the pinned code; `upgradeTree` adds the two checks of `e561b9cc2` (also at the
current heads) that decide where the attribute goes: `sendMessage` passes the attribute on,
and an atomic send must not go to L1.

- **Routing.** A logged send is atomic exactly when it carried the attribute and came
  through `sendBundle`, or through `sendMessage` where `sendMessage` honours it
  (`AttributeRoutingByEntryPoint`; no hash premise). The `sendMessage` finding above is
  `SendMessageAtomicMisrouted`: a pinned run in which a `sendMessage` carrying a flow's
  attribute is executed at its destination through `executeBundle` while the flow's other
  leg is refunded on the source.
- **An atomic leg to L1 at the pin** (the case recorded in `../AssetRouterBase/README.md`).
  Its one call targets the router's `L1_ASSET_ROUTER` (`AtomicL1BundleCarriesL1RouterTarget`).
  L1's `bundleStatus` of the leg stays `Unreceived` (`AtomicToL1NeverExecuted`), every claim
  of its bytes reverts when no recoverer is deployed at that address on the L2
  (`AtomicToL1ClaimReverts`), and together the leg is neither received on L1 nor `Reverted`
  in any reachable state (`AtomicToL1Stranded`), each up to a pinned keccak collision on
  logged preimages or `CrossSenderSaltClash`. Premises: `VmCall`, no recoverer at the L1
  router's address on the L2, the publication premise `CenterPublishesOnlyPublicDispatches`
  (`PROTO-EVIDENCE`) and the run-local decoding premise `DecodesRunBundles` (`SOL-ABI`).
  Both environment premises are needed: with an inclusion verdict that accepts the leg's
  bytes L1 executes it (`AtomicToL1StrandedNeedsPublicationPremise`), and with code at the
  L1 router's address that returns `true` the leg is claimed and `Reverted`
  (`AtomicToL1StrandedNeedsNoRecoverer`), with no collision in either run.
- **Targets on the source chain.** A router call in a send to an L2 targets
  `L2_ASSET_ROUTER_ADDR`, the source chain's own router (`IndirectL2RouterLegsReachSourceRouter`).
  An atomic leg with a call whose target has no recoverer on the source chain is not
  `Reverted`, up to a pinned collision with a logged claim (`NonRecovererLegNeverRefunded`).
- **The other tree's checks.** Under `upgradeTree` every send is atomic exactly when it
  carried the attribute, and no atomic send goes to L1 (`AttributeHonouredOrRejected`,
  `GuardKeepsAtomicLegsOffL1`); at the pin both fail (`PinBreaksAttributeHonoured`).

Witnesses: `AtomicToL1StrandedWitness` (every premise of the L1 results, the leg
`Revertable`, a public withdrawal executed on L1, every collision disjunct false),
`NonRecovererLegNeverRefundedWitness`, `IndirectL2RouterLegsReachSourceRouterWitness`,
`AttributeRoutingByEntryPointWitness`, `AttributeHonouredOrRejectedWitness` (whose run also
meets the premises of `GuardKeepsAtomicLegsOffL1`). Model boundaries: `MODEL-ATOMIC-ROUTING`
in `../../../ASSUMPTIONS.md`. In particular one `L1_CHAIN_ID` serves the center and the
router, `authorize` abstracts the absence proof and is read only by the witnesses, token
balances are not modelled, and that L1 credits a withdrawal only by executing or unbundling
its bundle is argued from source in the Specs header.
