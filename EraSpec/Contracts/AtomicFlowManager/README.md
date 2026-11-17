# AtomicFlowManager

Source: `contracts/atomic-interop/AtomicFlowManager.sol` in the pinned era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| FlowCanonical | [Specs/FlowCanonical.lean](Specs/FlowCanonical.lean) | [Properties/FlowCanonical.lean](Properties/FlowCanonical.lean) | [Proofs/FlowCanonical.lean](Proofs/FlowCanonical.lean) |
| RecoveryLimits | [Specs/RecoveryLimits.lean](Specs/RecoveryLimits.lean) | [Properties/RecoveryLimits.lean](Properties/RecoveryLimits.lean) | [Proofs/RecoveryLimits.lean](Proofs/RecoveryLimits.lean) |
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| ModelStrong | [Specs/ModelStrong.lean](Specs/ModelStrong.lean) | [Properties/ModelStrong.lean](Properties/ModelStrong.lean) | [Proofs/ModelStrong.lean](Proofs/ModelStrong.lean) |
| RecoveryLimitsStrong | [Specs/RecoveryLimitsStrong.lean](Specs/RecoveryLimitsStrong.lean) | [Properties/RecoveryLimitsStrong.lean](Properties/RecoveryLimitsStrong.lean) | [Proofs/RecoveryLimitsStrong.lean](Proofs/RecoveryLimitsStrong.lean) |
| RefundClosesAppend | [Specs/RefundClosesAppend.lean](Specs/RefundClosesAppend.lean) | [Properties/RefundClosesAppend.lean](Properties/RefundClosesAppend.lean) | [Proofs/RefundClosesAppend.lean](Proofs/RefundClosesAppend.lean) |

Several `Model` and `RecoveryLimits` properties are one-state facts whose docstrings
used to make run-level claims; the docstrings now say so, and the run-level claims
are stated in the two `…Strong` topics:

- **ModelStrong.** Labelled runs (`LegRun`, equivalent to `Reach`). Every claim of a
  leg that starts below `Revertable` is preceded by an `authorize` of it in the same
  run; from `Committed` (resp. `Unset`) the only steps on a leg that ends claimable
  are `authorize` (resp. `append`, `authorize`); a run changes a leg exactly
  rank-gain times, so at most three. A reentrant model (`NestedRun`) with the order
  of `claimRefund`'s write as a parameter: under the deployed write-first order each
  leg pays out at most once however deep the callbacks nest; under the reversed
  order one `Revertable` leg pays out any number of times
  (`claim_order_decides_double_payout`).
- **RecoveryLimitsStrong.** Ties `RecoveryLimits` to the loop of
  `AssetRouterBase/Specs/AtomicRecovery.lean` and to the manager's state. Limit 1:
  a claim that the real loop accepts with fewer recoveries than calls, after which
  no run of the manager lets that leg be claimed again
  (`partial_stranding_is_terminal`). Limit 2: if some call reverts in every world
  satisfying an invariant that the bundle and the environment preserve, every retry
  reverts and the leg stays `Revertable` (`blocked_retry_reverts`,
  `blocked_leg_stays_revertable`). Without that invariant the retry can succeed
  (`retry_succeeds_once_blocker_clears`).

Model boundary for both topics: `MODEL-AFM-NESTED` in `../../../ASSUMPTIONS.md`
(no reentrant writes from `append`/`authorizeRefund`; the at-least-one-recovery
check is over-approximated; retry results need a caller-supplied invariant).

**RefundClosesAppend** (pin `draft/v0.35.0` `b17415d20`; namespace
`Contracts.AtomicFlowManager.RefundClosesAppend`). One chain's manager `_state` and
`L1_CHAIN_ID`, its `L2InteropRootStorage`, and an abstract commitment tree, under every
writing entry point in any interleaving. The source comment at `AtomicFlowManager.sol:116-119`
says that once a leg of a flow was reverted on a chain, no new leg of it can be committed
there. With no hash premise, from root storage satisfying `LatestBoundsStored` (fresh storage
and the v31 layout do, and every run keeps it: `LatestBoundsStoredInvariant`), after a
successful `authorizeRefund` of preimage `p`:
- every later `append` of `p` reverts (`AuthorizedPreimageNeverAppendedAgain`), with
  `ManagerFlowDeadlinePassed` for the interop center once `L1_CHAIN_ID` is set
  (`AuthorizedPreimageAppendHitsDeadlineGate`); keyed on the flow id, a later `append`
  reverts or its preimage collides with `p` (`AuthorizedFlowIdAppendRevertsOrLoggedClash`);
- every later successful `append`, of any flow, has a later deadline
  (`LaterAppendsHaveLaterDeadlines`);
- from a fresh manager, no leg of the flow is `Committed` afterwards except through a
  `flowHash` collision between two preimages of the run
  (`RefundedFlowHasNoCommittedLegOrLoggedClash`), and the comment's own form holds
  (`RevertedLegClosesFlowOrLoggedClash`);
- legs committed at the authorization become claimable and are claimed at most once
  (`CommittedLegsBecomeClaimableOnce`).

The leg map of every run is a `Reach` run of the `Model` machine (`ChainRunLegsReach`).

Countermodels: the expired-flow gate, the maximum in the root storage, the proof's
settlement-layer check, the strict root-timestamp check and `LatestBoundsStored` are each
needed (`WithoutDeadlineGateLegCommittedAfterRefund`, `LastValueLatestReadmitsAppend`,
`UnboundProofSettlementLayerReadmitsAppend`, `NonStrictRootTimestampReadmitsAppend`,
`WithoutLatestBoundAppendAfterRefund`). Without the gate, a leg appended after the refund
is `Committed`, and repeating the same `authorizeRefund` call then marks it `Revertable`.
Witness: `RefundClosesAppendWitness`. Model boundary: `MODEL-REFUND-CLOSES-APPEND`.

The full flow gate spans `AtomicInteropProof`, the commitment tree, and the
handler. Its multi-chain composition lives in `../../Protocol/`. Implementation
refinement and the known generator mismatch are recorded in
`../../Refinement.lean`; this folder does not certify the compiled contract.
