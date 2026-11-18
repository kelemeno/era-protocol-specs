# AtomicFlowManager

Source: `contracts/atomic-interop/AtomicFlowManager.sol` in the pinned era-contracts tree.
Topics named `…AtHead` or `…AtV35` are pinned to a later era-contracts commit instead, as
their sections say.

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
| RecoveryLimitsFaithful | [Specs/RecoveryLimitsFaithful.lean](Specs/RecoveryLimitsFaithful.lean) | [Properties/RecoveryLimitsFaithful.lean](Properties/RecoveryLimitsFaithful.lean) | [Proofs/RecoveryLimitsFaithful.lean](Proofs/RecoveryLimitsFaithful.lean) |
| RefundClosesAppend | [Specs/RefundClosesAppend.lean](Specs/RefundClosesAppend.lean) | [Properties/RefundClosesAppend.lean](Properties/RefundClosesAppend.lean) | [Proofs/RefundClosesAppend.lean](Proofs/RefundClosesAppend.lean) |
| FlowCanonicalAtV35 | [Specs/FlowCanonicalAtV35.lean](Specs/FlowCanonicalAtV35.lean) | [Properties/FlowCanonicalAtV35.lean](Properties/FlowCanonicalAtV35.lean) | [Proofs/FlowCanonicalAtV35.lean](Proofs/FlowCanonicalAtV35.lean) |
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

**RecoveryLimitsFaithful** models the refund loop's external call: whether code runs
at the call's target on the source chain, what that code returns, and Solidity
0.8.28's decoding of the `bool` answer (`MODEL-AFM-CALL`). The loop runs over the
bundles of `InteropCenter`'s model. At the pin the loop calls each call's `to`. A
call reverts exactly when its target runs no code or returns nothing that decodes as
a `bool` (`PinnedCallRevertsIff`), and a claim succeeds exactly when the outcome list
satisfies `RecoveryLimits`' `ClaimAccepted` (`PinnedClaimSucceedsIffAccepted`). A
target that never runs code, or never answers, makes every claim of its bundle
revert (`CodelessTargetBlocksEveryClaim`, `NonAnsweringTargetBlocksEveryClaim`). In
a bundle the center formed, a direct call's target is its starter's recipient
(`DirectCallWithoutSourceCodeBlocksClaim`). Conforming code at every target, one of
which recovers, suffices (`ConformingTargetsRefund`). The loop at `draft/v0.35.0`
(`b17415d`; the same lines at `main` `70096e2`) calls only the router, reads no
other code of the source-chain parameter, needs no recovery, and rejects an L1
destination (`V35ClaimReadsOnlyRouterCode`, `V35ClaimSucceedsWithConformingRouter`,
`V35ClaimRejectsL1Destination`). The base-token refund step is a fixed parameter
`baseRecover` there, so the contracts it calls (the base token, the asset tracker)
are outside these statements, and the independence from code off the router holds
by how the v35 loop step is built. The witnesses use a two-call leg that the
deployed center and manager bring to `Revertable`, on source chains that differ only
in the code at the direct call's target. Open: `AssetRouterBase`'s
`AtomicRecovery` (`MODEL-ATOMIC-RECOVERY`) models the same pinned loop over its own
typed calls, and no refinement theorem relates that loop to this one over
`InteropCenter`'s calls.

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
