# InteropHandlerBase

Source: `contracts/interop/interop-handler/InteropHandlerBase.sol` and its L1/L2
variants in the pinned era-contracts tree.
Topics named `…AtHead` or `…AtV35` are pinned to a later era-contracts commit instead, as
their sections say.

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
| BundleStatusMachineFaithful | [Specs/BundleStatusMachineFaithful.lean](Specs/BundleStatusMachineFaithful.lean) | [Properties/BundleStatusMachineFaithful.lean](Properties/BundleStatusMachineFaithful.lean) | [Proofs/BundleStatusMachineFaithful.lean](Proofs/BundleStatusMachineFaithful.lean) |
| SelfCallAuthorityFaithful | [Specs/SelfCallAuthorityFaithful.lean](Specs/SelfCallAuthorityFaithful.lean) | [Properties/SelfCallAuthorityFaithful.lean](Properties/SelfCallAuthorityFaithful.lean) | [Proofs/SelfCallAuthorityFaithful.lean](Proofs/SelfCallAuthorityFaithful.lean) |
| ValueLedgerFaithful | [Specs/ValueLedgerFaithful.lean](Specs/ValueLedgerFaithful.lean) | [Properties/ValueLedgerFaithful.lean](Properties/ValueLedgerFaithful.lean) | [Proofs/ValueLedgerFaithful.lean](Proofs/ValueLedgerFaithful.lean) |
| ReentrancyAtV35 | [Specs/ReentrancyAtV35.lean](Specs/ReentrancyAtV35.lean) | [Properties/ReentrancyAtV35.lean](Properties/ReentrancyAtV35.lean) | [Proofs/ReentrancyAtV35.lean](Proofs/ReentrancyAtV35.lean) |

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

### Faithfulness repairs

Three of the original abstract models say less than their docstrings claim. The `…Faithful`
modules restate them against the source at `c67894b9`, in the re-entrant model where a run is
involved, and link back to the original statements. The originals are kept unchanged, with a
correction note in their docstrings.

- **`BundleStatusMachineFaithful`.** The original's prose says that publishing atomic bundles to L1
  would "brick" them. In the source it is the other way round: a `Verified` bundle is delivered by
  `executeBundle` or `unbundleBundle` consulting no check, and neither consults the flow gate. The
  labelled machine `LStep` names the entry point and check of each edge, and is exactly `Step` with
  labels (`lstep_refines_step`). Every route from `Unreceived` consults an inclusion proof or the
  flow gate (`route_consults_inclusion_or_flowGate`); removing the inclusion-proof edges leaves
  `AtomicReach` (`no_inclusion_paths_are_atomic`). Operationally, with every target behaviour at
  every depth: a hash with no accepted inclusion proof and no passing flow gate is never delivered
  (`DeliveryNeedsInclusionOrFlowGate`), and under the never-published premise alone, delivery needs
  the flow gate (`NeverPublishedBundleNeedsTheFlowGate`, headline). Without the premise the gate is
  bypassed (`ProvableBytesBypassTheFlowGate`, `VerifiedBundleRunsWithoutAnyGate`). Witness:
  `FlowGateRoutesWitness`.
- **`SelfCallAuthorityFaithful`.** The original `selfCall_relays_authority` is a tautology
  (`selfCall_relays_authority_conclusion_always_holds`). The repair quantifies over every call that
  reaches a permission gate (`Reaches`): for any dispatch table, delegation is sound iff every arm
  checks the attribute its target's gate reads (`DelegationSoundIffMatched`). The pin's table is
  sound (`PinnedDelegationSound`), and so are both `e561b9cc2` tables, whose L2 execute arm
  self-calls `executeAtomicBundle` (`DelegationSoundAtV35`,
  `AtomicSelfDisjunctLiveAndCheckedAtV35`; at the pin that disjunct is dead,
  `AtomicSelfDisjunctDeadAtPin`). The original hypothesis `checked` is established at every pinned
  self-call (`RelayEstablishesTheOriginalHypothesis`). Countermodels:
  `UncheckedAtomicArmWidensAuthority`, `MiswiredCheckWidensAuthority`.
- **`ValueLedgerFaithful`.** The original "no inflation" results are about an arbitrary list. The
  repair derives the ledger from the handler's state and measures release at `_handleCallValue`.
  From fresh storage, under the run-local binding premise `NamesOnly b` (every entry-point call
  naming `b.hash` names `b`): released equals `releasedSum` of the handler's ledger, and its
  `collectedSum` is what the source collected for `b` (`collectedFor`, the sum of its call values,
  which is the send's `totalBurnedCallsValue`) (`ReleaseIsTheHandlerLedger`);
  so release is at most collection (`HandlerReleasesAtMostCollected`), with equality once the bundle
  executes whole (`ExecutedBundleReleasesAllCollected`). Every release is for a call of `b`
  (`ReleasesAreTheBundlesCalls`, from any state). The premise is satisfiable (`LedgerWitness`, with
  a strict inequality) and load-bearing (`SharedHashBreaksTheLedger`).

Boundary: each model enumerates the source sites it relies on (the self-call sites and dispatch
arms, the call sites of `requireFlowFinalized`, `_verifyBundle` and `_proveInclusion`, and the
base-token release sites). `scripts/check-interop-handler-inventory.sh [ERA_CONTRACTS_ROOT]` checks
that inventory against a tree and passes only on the layout of `c67894b9` (it fails at `e561b9cc2`, whose
upgrade tables are transcribed by hand in `SelfCallAuthorityFaithful`). Open items: the
never-published premise for bundles published by other chains is outside both this model and
`InteropCenter`'s; the bytes-to-hash binding behind `NamesOnly` and the value function is
`InteropDataEncoding`'s obligation; values are naturals (the source's checked `uint256` sum reverts
on overflow).

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

### At draft/v0.35.0 (`ReentrancyAtV35`)

`ReentrancyAtV35` (namespace `Contracts.InteropHandlerAtV35`) models both handlers at
`draft/v0.35.0` `b17415d20` (first written against `d9f6789`; every cited file is identical at
both). Public L2→L2 interop is gone: L2 has `executeAtomicBundle` and `verifyAtomicBundle`, L1 has
`executeBundle` and `verifyBundle`, and `unbundleBundle` is shared. `verifyAtomicBundle` is new, so
an atomic bundle can be verified, then unbundled; and `executeAtomicBundle` now admits a `Verified`
bundle and skips the flow gate for it. The entry points of one layer form one type,
`EntryAtV35 ℓ`, so a call tree holds one layer's entry points only.
- **The translation.** A v35 frame runs as its translation in the pin model `exec`, in the deployed
  order and `callWriteAfterCalls` on both layers and in every order on L1 (`ExecMatchesPinAtV35`,
  `SubmitAllMatchesPinAtV35`).
  Both layers' `execute` maps to the pin's `executeBundle`; on L2 the pin's extra `Verified` write is
  overwritten by `FullyExecuted` before any call runs. On L2 in the order `statusWriteAfterCalls`
  the two differ (`LateStatusWriteSeparatesL2FromPinAtV35`).
- **Nothing runs twice**, on both layers, proved through the translation:
  `NoEffectCommittedTwiceAtV35` (headline), `CommittedEffectsWereOpenAtV35`,
  `WholeBundleExecutionRunsEachCallOnceAtV35`, `StatusRecordsExactlyTheCommittedEffectsAtV35`,
  `NestedExecutionFollowsTheStatusMachineAtV35`, and `ReentryForAnExecutingBundleRevertsAtV35`
  (the NatSpec at `L2InteropHandler.sol:55-58`).
- **Rollback**, in every order, for targets that revert from every state or where the loop reaches
  them: `AlwaysRevertingTargetRevertsTheExecutionAtV35`,
  `TargetRevertingWhereReachedRevertsTheExecutionAtV35`, `FailedAttemptCanBeRetriedAtV35`.
- **The gate.** A `Verified` bundle executes with a failing verdict
  (`VerifiedBundleExecutesWithoutTheGateAtV35`). A hash none of whose entry-point calls, at any
  depth, carries a passing verdict stays `Unreceived` with no committed effect
  (`DeliveryNeedsTheGateAtV35`). On L2 the verdict is the flow gate's, and the statement needs no
  never-published premise: L2 has no entry point that consults an inclusion proof at v35. The
  receive filter (`L2Bridgehub.isPeerAllowed`) is read at the gate only: a bundle verified before
  its source peer is removed still executes (`ReceiveFilterIsReadAtTheGateAtV35`, as
  `protocol-docs/interop-gating.md:195-197` documents).
- Witnesses: `PinMatchWitnessAtV35`, `ReentrantExecutionWitnessAtV35`, `RevertingTargetWitnessAtV35`,
  `CaughtReentrantRevertWitnessAtV35`, `GateRoutesWitnessAtV35` (the three L2 routes, and a bundle
  left partly executed by unbundling), `ReceiveFilterWitnessAtV35`. Countermodels:
  `LateStatusWriteSeparatesL2FromPinAtV35`, `StatusWriteAfterCallsRunsTwiceAtV35`,
  `CallWriteAfterCallsRunsTwiceAtV35`, `StatusWriteAfterCallsRunsAnyBundleTwiceAtV35`,
  `CallWriteAfterCallsRunsAnyCallTwiceAtV35`.

The model boundary is `MODEL-HANDLER-REENTRY-V35`. The handlers at main `70096e2` differ from
`b17415d20` only by three internal getters' names (two also `view` instead of `pure`) and
`L2InteropHandler.updateL2`, so `execAtV35` models them too; main has no receive filter. The pin topics above are unchanged and still describe `c67894b9`.

The atomic path's source identity is reviewed separately under
`../L2InteropHandler/`. Destination-wide composition is
`../../Protocol/DestinationCapstone.lean`. Whole-program call-site enumeration, the
static-call and no-callback facts above, and binding the actual executed bytes to
authenticated bundle bytes are separate implementation obligations, not discharged by
these abstract state machines.
