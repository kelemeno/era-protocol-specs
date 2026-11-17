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
| FlowCanonicalAtV35 | [Specs/FlowCanonicalAtV35.lean](Specs/FlowCanonicalAtV35.lean) | [Properties/FlowCanonicalAtV35.lean](Properties/FlowCanonicalAtV35.lean) | [Proofs/FlowCanonicalAtV35.lean](Proofs/FlowCanonicalAtV35.lean) |

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

**FlowCanonicalAtV35** models `draft/v0.35.0` at `b17415d20`; the pin topics above are
unchanged. There `_validateAndComputeFlowId` adds a version byte and an eight-leg cap to
the pin's two checks, hashes the whole preimage, and also runs in `append`. Proved:
the exact acceptance condition (`AcceptedV35Iff`), with the pin's `Valid` necessary but
not sufficient; an oversized preimage reverts the transcribed `append`,
`requireFlowFinalized` and `authorizeRefund` (`TooManyLegsRevertsEveryEntryPointV35`).
Over runs of the transcribed `_state` writes (`MODEL-AFM-V35`): `append` succeeds exactly
for an accepted preimage that declares the leg on this chain, with the leg `Unset`
(`AppendV35SomeIff`); every run is a run of the pin's leg machine (`RunV35IsPinLegRun`), so
the `Model` topic's `Reach` results apply; a run claims each leg at most once and appends it
at most once; a leg first written in a run was appended under an accepted preimage that
hashes to its flow id and declares it on this chain; a run writes no `Unset` leg under the
flow id of a rejected (for instance oversized) preimage unless it appended under an accepted
preimage that clashes with it; and a refunded leg was marked by an `authorizeRefund`
presenting the preimage it was committed under, or one that clashes with it. No hash
premise; each clash disjunct is reached by a witness.

The full flow gate spans `AtomicInteropProof`, the commitment tree, and the
handler. Its multi-chain composition lives in `../../Protocol/`. Implementation
refinement and the known generator mismatch are recorded in
`../../Refinement.lean`; this folder does not certify the compiled contract.
