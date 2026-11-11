# InteropHandlerBase

Source: `contracts/interop/interop-handler/InteropHandlerBase.sol` and its L1/L2
variants in the pinned era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| BundleStatusMachine | [Specs/BundleStatusMachine.lean](Specs/BundleStatusMachine.lean) | [Properties/BundleStatusMachine.lean](Properties/BundleStatusMachine.lean) | [Proofs/BundleStatusMachine.lean](Proofs/BundleStatusMachine.lean) |
| SelfCallAuthority | [Specs/SelfCallAuthority.lean](Specs/SelfCallAuthority.lean) | [Properties/SelfCallAuthority.lean](Properties/SelfCallAuthority.lean) | [Proofs/SelfCallAuthority.lean](Proofs/SelfCallAuthority.lean) |
| Reentrancy | [Specs/Reentrancy.lean](Specs/Reentrancy.lean) | [Properties/Reentrancy.lean](Properties/Reentrancy.lean) | [Proofs/Reentrancy.lean](Proofs/Reentrancy.lean) |
| BundleStatusMachineStrong | [Specs/BundleStatusMachineStrong.lean](Specs/BundleStatusMachineStrong.lean) | [Properties/BundleStatusMachineStrong.lean](Properties/BundleStatusMachineStrong.lean) | [Proofs/BundleStatusMachineStrong.lean](Proofs/BundleStatusMachineStrong.lean) |
| SelfCallAuthorityStrong | [Specs/SelfCallAuthorityStrong.lean](Specs/SelfCallAuthorityStrong.lean) | [Properties/SelfCallAuthorityStrong.lean](Properties/SelfCallAuthorityStrong.lean) | [Proofs/SelfCallAuthorityStrong.lean](Proofs/SelfCallAuthorityStrong.lean) |
| ReentrancyStrong | [Specs/ReentrancyStrong.lean](Specs/ReentrancyStrong.lean) | [Properties/ReentrancyStrong.lean](Properties/ReentrancyStrong.lean) | [Proofs/ReentrancyStrong.lean](Proofs/ReentrancyStrong.lean) |

`Reentrancy` (namespace `Contracts.InteropHandler`) covers what happens inside a
transaction. The target of every delivered call is an arbitrary finite tree of re-entrant
calls to `executeBundle`/`executeAtomicBundle`/`verifyBundle`/`unbundleBundle`, each
failure caught or propagated; rollback is `Option`. In the deployed write order, with no
hash premise:
- no call is delivered twice and no bundle completes twice, across routes and
  transactions (`NoEffectCommittedTwice`); a whole-bundle execution commits exactly its
  calls in order and `BundleExecuted` (`WholeBundleExecutionRunsEachCallOnce`), and the
  status mappings record exactly the committed effects
  (`StatusRecordsExactlyTheCommittedEffects`, `CommittedEffectsWereOpen`);
- nested frames follow `BundleStatusMachine` (`NestedExecutionFollowsTheStatusMachine`),
  and re-entry for an executing bundle reverts (`ReentryForAnExecutingBundleReverts`,
  the NatSpec at `L2InteropHandler.sol:45-46`);
- a target that reverts immediately reverts the whole execution, and the bundle can be
  retried
  (`RevertingCallRevertsTheExecution`, `FailedAttemptCanBeRetried`);
- moving either replay write after `_executeCalls` admits double execution
  (`StatusWriteAfterCallsRunsAnyBundleTwice`, `CallWriteAfterCallsRunsAnyCallTwice`).

Witnesses: `ReentrantExecutionWitness`, `FailedAttemptRetryWitness`,
`CaughtReentrantRevertWitness`. The model assumes re-entry only at the target's
`receiveMessage` (`InteropHandlerBase.sol:282-286`): that `_proveInclusion` and
`requireFlowFinalized` are static calls and that `_handleCallValue` reaches no entry point
are argued in the Specs header, not proved. Reject-only checks are omitted.

`BundleStatusMachine`'s atomic sub-machine relies on atomic bundles never being published
to L1. This chain's half of that fact is `Contracts.InteropCenter.AtomicBytesNeverPublished`
(under `EncInjOn`, except a pinned cross-sender salt clash).

Three topics restate statements of the original topics that, as written, are facts about
abstract relations or repackage their premise (their docstrings now say so):
- `BundleStatusMachineStrong` (namespace `Contracts.InteropHandler`, over the `Reentrancy`
  model). The whole-bundle write ignores the call statuses it overwrites
  (`WholeBundleWriteIgnoresCallStatus`), so only the bundle status stops a second payment
  (`CallStatusDoesNotStopWholeBundleRedelivery`). The deployed guards never reach a state where
  that matters (`AdmittedBundleHasOnlyUnprocessedCalls`). A `Verified` hash is never executed
  atomically, while `executeBundle` stays open (`VerifiedBundleNeverExecutesAtomically`). The atomic
  sub-machine is derived from the guards under a named no-proof premise
  (`NoProofKeepsBundleInAtomicMachine`). That premise is load-bearing
  (`ProofForAtomicHashOpensUnbundledRoute`) and is discharged from the source chain's center,
  up to a cross-sender salt clash or a keccak collision on named preimages
  (`AtomicLegStaysAtomicAtDestinationOrClash`, witnessed with both clashes false).
- `SelfCallAuthorityStrong` (namespace `AttackVectors.SelfCallAuthority`). It models
  `receiveMessage`'s dispatch table. For every table, every admitted call is authorised for its
  principal (for a relayed call, the original sender `(sourceChainId, from)`) if and only if
  every gated branch checks first, given the ERC-7930 round trip on the relayed pair
  (`SelfCallRelaySoundIffEveryGatedBranchChecked`). The deployed table is such a table
  (`DeployedSelfCallRelaysOriginalSenderAuthority`). The countermodels are an unchecked
  `executeAtomicBundle` branch and a parser that breaks the ERC-7930 round trip.
- `ReentrancyStrong`. A target that reverts from every state
  (`AlwaysRevertingTargetRevertsTheExecution`), or reverts where the loop reaches it
  (`TargetRevertingWhereReachedRevertsTheExecution`), reverts the execution, and the attempt can be
  retried (`FailedAttemptWithAlwaysRevertingTargetCanBeRetried`). This covers more than the leaf
  `Callee.reverts`: for example, targets that revert after nested work.

The atomic path's source identity is reviewed separately under
`../L2InteropHandler/`. Destination-wide composition is
`../../Protocol/DestinationCapstone.lean`. Whole-program call-site enumeration, the
static-call and no-callback facts above, and binding the actual executed bytes to
authenticated bundle bytes are separate implementation obligations, not discharged by
these abstract state machines.
