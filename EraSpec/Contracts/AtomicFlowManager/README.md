# AtomicFlowManager

Source: `contracts/atomic-interop/AtomicFlowManager.sol` in the pinned era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| FlowCanonical | [Specs/FlowCanonical.lean](Specs/FlowCanonical.lean) | [Properties/FlowCanonical.lean](Properties/FlowCanonical.lean) | [Proofs/FlowCanonical.lean](Proofs/FlowCanonical.lean) |
| FlowCanonicalAtHead (`3605e82`) | [Specs/FlowCanonicalAtHead.lean](Specs/FlowCanonicalAtHead.lean) | [Properties/FlowCanonicalAtHead.lean](Properties/FlowCanonicalAtHead.lean) | [Proofs/FlowCanonicalAtHead.lean](Proofs/FlowCanonicalAtHead.lean) |
| RecoveryLimits | [Specs/RecoveryLimits.lean](Specs/RecoveryLimits.lean) | [Properties/RecoveryLimits.lean](Properties/RecoveryLimits.lean) | [Proofs/RecoveryLimits.lean](Proofs/RecoveryLimits.lean) |
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| ModelStrong | [Specs/ModelStrong.lean](Specs/ModelStrong.lean) | [Properties/ModelStrong.lean](Properties/ModelStrong.lean) | [Proofs/ModelStrong.lean](Proofs/ModelStrong.lean) |
| RecoveryLimitsStrong | [Specs/RecoveryLimitsStrong.lean](Specs/RecoveryLimitsStrong.lean) | [Properties/RecoveryLimitsStrong.lean](Properties/RecoveryLimitsStrong.lean) | [Proofs/RecoveryLimitsStrong.lean](Proofs/RecoveryLimitsStrong.lean) |

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

`FlowCanonicalAtHead` (namespace `Contracts.FlowCanonicalAtHead`) models
`_validateAndComputeFlowId` and `_checkFlowId` at era-contracts `main` `3605e82`, next to
the pin's `FlowCanonical`, which is unchanged. At that commit the preimage is one struct
with a version byte, two checks are new (version `0x01`, at most eight legs), and one
function serves `append`, `requireFlowFinalized` and `authorizeRefund`. `main` at
`70096e2` changes no contract since `3605e82`. At `draft/v0.35.0` (`d9f6789`, and the head
`b17415d20`) the two functions and their three call sites are the same text at other line
numbers, listed in the spec's "Other heads" section.

- The pin's `Valid` is still necessary and no longer sufficient
  (`AcceptedPreimageIsValid`, `ValidNoLongerSufficient`); acceptance is exactly `Valid`
  plus the version plus the cap (`AcceptedIffValidVersionCap`, `ValidateIsSomeIffAccepted`).
- An accepted preimage is canonical and gives each leg one declared source chain
  (`AcceptedPreimageIsCanonical`, `DeclaredSourceChainUnique`, `ListedLegIsDeclared`).
- A preimage the new checks reject is rejected on all three paths
  (`NewChecksRejectOnEveryPath`); an accepted preimage has at most eight legs, and some
  has exactly eight (`AcceptedHasAtMostMaxLegs`, `AcceptedCapIsReached`).
- Recorded, but unfoldings with no content of their own: `SharedValidationNoDrift` (the
  model has one function because the source has one), `CheckedFlowsAgreeOrClash` and
  `DifferentVersionsShareAnIdOnlyByClash` (two different preimages with one id are a
  `PreimageClash` by definition). `Protocol/InteropAtomicity` `FlowBindingAtHead` makes
  the same case split on two preimages from one run's log, where it has content.
- `keccak256(abi.encode(preimage))` is the free parameter `enc`; no property of it is
  assumed. `PreimageHashInjOnSatisfiable` and `HonestPreimageHashNoClash` show the bounded
  premise and the clash disjunct are not empty; `FlowCanonicalAtHeadWitness` is the
  satisfiability witness.

The full flow gate spans `AtomicInteropProof`, the commitment tree, and the
handler. Its multi-chain composition lives in `../../Protocol/`. Implementation
refinement and the known generator mismatch are recorded in
`../../Refinement.lean`; this folder does not certify the compiled contract.
