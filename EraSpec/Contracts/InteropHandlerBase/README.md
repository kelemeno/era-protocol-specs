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

The atomic path's source identity is reviewed separately under
`../L2InteropHandler/`. Destination-wide composition is
`../../Protocol/DestinationCapstone.lean`. Whole-program call-site enumeration, the
static-call and no-callback facts above, and binding the actual executed bytes to
authenticated bundle bytes are separate implementation obligations, not discharged by
these abstract state machines.
