# InteropCenter

Source: `contracts/interop/InteropCenter.sol` in the pinned era-contracts tree, with
`contracts/atomic-interop/AtomicFlowManager.sol` for the leg state that `append` writes.
Only the send path is modelled: the salt mapping `isInteropBundleSaltUsed`, bundle
formation in `_sendBundle`, `_validateAtomicBundle`, and `_dispatchBundle` →
`AtomicFlowManager.append`.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Dispatch | [Specs/Dispatch.lean](Specs/Dispatch.lean) | [Properties/Dispatch.lean](Properties/Dispatch.lean) | [Proofs/Dispatch.lean](Proofs/Dispatch.lean) |

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

Neither is formalized at the attribute-parsing level; in the model such a bundle is a
public dispatch.
