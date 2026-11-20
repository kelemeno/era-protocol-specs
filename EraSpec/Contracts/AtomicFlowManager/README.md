# AtomicFlowManager

## Headline guarantees

All about `l1-contracts/contracts/atomic-interop/AtomicFlowManager.sol` at era-contracts
`draft/v0.35.0` head `b17415d20`. No statement assumes anything about a hash: the flow id
`keccak256(abi.encode(preimage))` is any function, and a collision is always named on two
preimages. The timeout refund (`authorizeRefund`, `claimRefund`) is modelled; the expiry refund of
era-contracts PR 2642 is not in `b17415d20` and is not modelled.

"A run" (`FlowCanonicalAtV35`) is any sequence of successful calls of `append`,
`requireFlowFinalized`, `authorizeRefund` and `claimRefund` from any `_state`, with the flow-id and
leg checks and the `_state` writes transcribed; the left-out checks (caller, settlement layer,
deadline gate, registration, proofs, receive filter) only revert, so every successful deployed run
is a run here, and a call that re-enters the manager is its own later call (`MODEL-AFM-V35`).

- `Contracts.FlowCanonicalAtV35.Properties.ValidateV35SomeIff`: `_validateAndComputeFlowId`
  returns `id` exactly when the version byte is `0x01`, there are at most eight legs, the bundle
  hashes strictly ascend, there are as many source chains as legs, and the hash is `id`. Premises:
  none.
- `Contracts.FlowCanonicalAtV35.Properties.TooManyLegsRevertsEveryEntryPointV35`: on a preimage
  with more than eight legs, `append`, `requireFlowFinalized` and `authorizeRefund` revert, for
  every hash, state and other argument. Premises: more than eight legs; the transcription
  boundary above.
- `Contracts.FlowCanonicalAtV35.Properties.RunV35ClaimsEachLegAtMostOnce`: in every run, each leg
  has at most one `claimRefund`, and none if it starts `Reverted`. Premises: the run boundary above.
- `Contracts.FlowCanonicalAtV35.Properties.RunV35AppendsEachLegAtMostOnce`: in every run, each leg
  has at most one `append` under its flow id, and none if it does not start `Unset`. Premises: the
  run boundary above.
- `Contracts.FlowCanonicalAtV35.Properties.WrittenLegAppendedUnderAcceptedPreimageV35`: a leg
  first written in a run was appended by a call of the run under an accepted preimage that hashes
  to its flow id and declares the leg on this chain. Premises: the run boundary above.
- `Contracts.FlowCanonicalAtV35.Properties.OversizedFlowCommitsNoLegOrLoggedClashV35`: a preimage
  with more than eight legs gets no leg committed under its flow id, unless the run appended under
  an accepted preimage that collides with it. Premises: more than eight legs; the run boundary.
- `Contracts.FlowCanonicalAtV35.Properties.RefundedLegSameFlowOrLoggedClashV35`: a leg refunded in
  a run was appended and authorized by calls of the run, under the same preimage or two colliding
  ones. Premises: the leg starts `Unset`; the run boundary above.
- `Contracts.AtomicFlowManager.ModelStrong.Properties.writeFirst_payout_at_most_once`: however
  deeply `claimRefund`'s recovery calls re-enter the manager, each leg pays out at most once.
  Premises: the deployed order (write at `:260` before `_recoverBundle` at `:262`); model boundary
  `MODEL-AFM-NESTED` (each call is its `_state` guard and write; `append` and `authorizeRefund`
  make no re-entering write; a callback is any nested sequence of successful manager calls).
- `Contracts.AtomicFlowManager.RefundClosesAppend.Properties.AuthorizedPreimageNeverAppendedAgain`:
  after a successful `authorizeRefund` of preimage `p`, every later `append` of `p` reverts.
  Premises: at the start of the run every stored root timestamp is at most its chain's tracked
  latest timestamp (`LatestBoundsStored`, true of fresh storage and kept by every run); model
  boundary `MODEL-REFUND-CLOSES-APPEND` (one chain's manager, `L1_CHAIN_ID`, root storage and an
  abstract tree; hash, proof authentication and tree checks are free parameters).
- `Contracts.AtomicFlowManager.RefundClosesAppend.Properties.AuthorizedPreimageAppendHitsDeadlineGate`:
  the same, and the interop center's `append` of `p` reverts with `ManagerFlowDeadlinePassed`.
  Premises: as above, and `L1_CHAIN_ID` set at the authorization.
- `Contracts.AtomicFlowManager.RefundClosesAppend.Properties.LaterAppendsHaveLaterDeadlines`: after
  the authorization, every successful `append` of any flow is on the same settlement layer with a
  strictly later deadline. Premises: as above, and `L1_CHAIN_ID` set at the authorization.
- `Contracts.AtomicFlowManager.RefundClosesAppend.Properties.RefundedFlowHasNoCommittedLegOrLoggedClash`:
  from a fresh manager, no leg of the refunded flow is `Committed` afterwards except through a
  flow-id collision between two preimages of the run. Premises: fresh manager; `LatestBoundsStored`;
  the model boundary.
- `Contracts.AtomicFlowManager.RefundClosesAppend.Properties.CommittedLegsBecomeClaimableOnce`: the
  legs committed at a successful `authorizeRefund` become `Revertable`, are claimed at most once
  afterwards, and stay claimable until then. Premises: the model boundary; "claimable" assumes the
  recovery loop does not revert.
- `Contracts.AtomicFlowManager.RefundClosesAppend.Properties.RevertedLegClosesFlowOrLoggedClash`:
  the source comment's form: once a leg of a flow is reverted (`Revertable` or `Reverted`), no
  later `append` of that flow id succeeds except under a different, colliding preimage. Premises:
  fresh manager; `LatestBoundsStored`; the model boundary.
- `Contracts.AtomicFlowManager.RecoveryLimitsFaithful.Properties.V35ClaimRejectsL1Destination`:
  `claimRefund` of a bundle destined to `L1_CHAIN_ID` reverts. Premises: model boundary
  `MODEL-AFM-CALL` (the claim is stated for the bundle presented).
- `Contracts.AtomicFlowManager.RecoveryLimitsFaithful.Properties.V35ClaimSucceedsWithConformingRouter`:
  `claimRefund` of a `Revertable` leg succeeds, whatever the calls and whatever runs off the
  router; no recovery is required. Premises: an L2 destination; the router always answers a
  well-formed `bool`; the base-token refund never reverts (it is abstract, `MODEL-AFM-CALL`).
- `Contracts.AtomicFlowManager.RecoveryLimitsFaithful.Properties.V35ClaimReadsOnlyRouterCode`: the
  claim's result depends on the source chain's code only at the router. Premises: the two source
  chains agree at the router; the base-token refund step is held fixed (`MODEL-AFM-CALL`).

Witnesses: `AcceptanceWitnessV35`, `TooManyLegsWitnessV35`, `LegWritesWitnessV35`,
`SecondClaimOrAppendRevertsWitnessV35`, `OversizedFlowWitnessV35`,
`RefundUnderOtherPreimageWitnessV35`, `nestedRun_witness`, `RefundClosesAppendWitness`,
`V35ClaimWitness`, `V35ClaimSucceedsOnMixedBundle`, and the History witness
`DirectTargetCodeDecidesOnlyThePinnedClaim`. Countermodels: `Valid` without the version byte or the
cap is not sufficient (`ValidNotSufficientVersionV35`, `ValidNotSufficientLegCapV35`); the reversed
write order pays one leg any number of times (`writeAfter_unbounded_payouts`,
`claim_order_decides_double_payout`); the expired-flow gate, the maximum in the root storage, the
proof's settlement-layer check, the strict root-timestamp check and `LatestBoundsStored` are each
needed (`WithoutDeadlineGateLegCommittedAfterRefund`, `LastValueLatestReadmitsAppend`,
`UnboundProofSettlementLayerReadmitsAppend`, `NonStrictRootTimestampReadmitsAppend`,
`WithoutLatestBoundAppendAfterRefund`).

## Topics

`Specs/` holds the models, `Properties/` the statements, `Proofs/` the proofs. Every topic outside
`History/` is about `b17415d20`, except the two pin records listed below.

| Topic | What it is |
|---|---|
| [FlowCanonicalAtV35](Specs/FlowCanonicalAtV35.lean) | **Canonical model.** `_validateAndComputeFlowId`, `_checkFlowId` and the four entry points that take a preimage or write `_state`, over runs. Every run is a `Reach` run of `Model` (`RunV35IsPinLegRun`). |
| [Model](Specs/Model.lean) | The leg machine: `Unset → Committed → Revertable → Reverted`, each step guarded on its exact predecessor. The other models write the same `Manager`. |
| [ModelStrong](Specs/ModelStrong.lean) | `Model` with labelled runs, and with reentrant claims whose write order is a parameter. |
| [RefundClosesAppend](Specs/RefundClosesAppend.lean) | One chain's manager, `L1_CHAIN_ID` and root storage under every writing entry point: an authorized refund closes `append` for its flow. Its leg map is a `Reach` run of `Model` (`ChainRunLegsReach`). |
| [RecoveryLimitsFaithful](Specs/RecoveryLimitsFaithful.lean) | The refund loop's external call and its `bool` decoding, and `claimRefund`'s loop at `b17415d20`. |
| [FlowCanonical](Specs/FlowCanonical.lean) | The neighbour sort check and the length check (`:370-377`): what they give over all pairs. Two of the four checks of `_validateAndComputeFlowId`. |
| [FlowCanonicalAtHead](Specs/FlowCanonicalAtHead.lean) | A second transcription of `_validateAndComputeFlowId`, first written at `main` `3605e82`, the same text. Kept because `Protocol/InteropAtomicity` `FlowBindingAtHead` builds on its types; refinement lemmas make it the canonical model (`ToV35Bijective`, `ValidateAgreesWithV35`, `CheckFlowIdAgreesWithV35`, `AcceptedIffAcceptedV35`). |

**Pin records kept in place.** [RecoveryLimits](Specs/RecoveryLimits.lean) and
[RecoveryTargets](Specs/RecoveryTargets.lean) describe the refund loop at the older pin `c67894b9`
(a call to every call's `to`, at least one recovery required). They are not claims about
`b17415d20`, are untagged, and stay outside `History/` only because other folders' pinned models
(InteropCenter, AssetRouterBase, Protocol/AssetBridgePreparation) use their names.

**History.** `History/` is the record of the older pin `c67894b9`, not a claim about `b17415d20`:
[RecoveryLimitsStrong](History/Specs/RecoveryLimitsStrong.lean) (the pinned loop's limits on the
manager's runs and across retries) and the pinned half of
[RecoveryLimitsFaithful](History/Specs/RecoveryLimitsFaithful.lean) (the loop over each call's `to`).

Model boundaries: `MODEL-AFM-V35`, `MODEL-AFM-NESTED`, `MODEL-AFM-CALL`, `MODEL-REFUND-CLOSES-APPEND`,
`MODEL-FLOW-HEAD` in `../../../ASSUMPTIONS.md`. The multi-chain composition is in
`../../Protocol/InteropAtomicity/`. This folder does not certify the compiled contract
(`../../Refinement.lean`).
