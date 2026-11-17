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
| RecoveryTargets | [Specs/RecoveryTargets.lean](Specs/RecoveryTargets.lean) | [Properties/RecoveryTargets.lean](Properties/RecoveryTargets.lean) | [Proofs/RecoveryTargets.lean](Proofs/RecoveryTargets.lean) |

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

**RecoveryTargets** (`c67894b9`) models `claimRefund`'s loop over a code map: what is
deployed at each call's `to` on the chain running the refund (the leg's source chain) is
nothing, a recoverer, or code without `recoverAtomicCall`. Under the call-semantics
premise `VmCall`:

- a claim of a `Revertable` leg succeeds exactly when every target is a recoverer that
  returns and one of them returns `true` (`ClaimSucceedsIff`);
- a target with no recoverer makes every claim revert, in every world and leg state
  (`NonRecovererTargetBlocksClaim`). On the router model, a bundle of a router call and a
  direct call to an address with nothing deployed on the refunding chain is not claimable,
  while the router call alone is (`CodelessCallTargetBlocksBundleClaim`);
- a returned `true` is counted whatever the code did: targets that return `true` and change
  nothing close the leg with the world unchanged (`ForeignTrueCountsAsRecovered`);
- the manager reads only `to` and `data` (`RecoveryReadsOnlyTargetAndData`, by definition).

`AssetRouterBase`'s `AtomicRecovery` loop is the case with a recoverer at every address
(`RouterModelIsACodeMap`). A router call to another L2 targets `L2_ASSET_ROUTER_ADDR`, the
source chain's own router; with the router's `recoverAtomicCall` deployed there, the
manager's call of a prepared burn's router call is the vault's mint of the burned amount to
the depositor (`SourceRouterTargetRefundsDepositor`). Witnesses:
`VmCallHolds`, `ClaimSucceedsIffWitness`, `NonRecovererTargetBlocksClaimWitness`,
`ForeignTrueCountsAsRecoveredWitness`, `RecoveryReadsOnlyTargetAndDataWitness`,
`SourceRouterTargetRefundsDepositorWitness`; `VmCall` is load-bearing
(`NonRecovererTargetBlocksClaimNeedsVmCall`). No hash premise. The code map is fixed (a
later deployment at an address is outside the model), and `_recoverBundle` at `e561b9cc2`
and the current heads, which calls `c.from`, is not modelled. Model boundary:
`MODEL-RECOVERY-TARGETS`. The run-level use, with the center and the destinations, is
`../InteropCenter/` topic `AtomicRouting`.

The full flow gate spans `AtomicInteropProof`, the commitment tree, and the
handler. Its multi-chain composition lives in `../../Protocol/`. Implementation
refinement and the known generator mismatch are recorded in
`../../Refinement.lean`; this folder does not certify the compiled contract.
