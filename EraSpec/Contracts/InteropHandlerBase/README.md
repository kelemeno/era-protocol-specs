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
| BundleStatusMachineFaithful | [Specs/BundleStatusMachineFaithful.lean](Specs/BundleStatusMachineFaithful.lean) | [Properties/BundleStatusMachineFaithful.lean](Properties/BundleStatusMachineFaithful.lean) | [Proofs/BundleStatusMachineFaithful.lean](Proofs/BundleStatusMachineFaithful.lean) |
| SelfCallAuthorityFaithful | [Specs/SelfCallAuthorityFaithful.lean](Specs/SelfCallAuthorityFaithful.lean) | [Properties/SelfCallAuthorityFaithful.lean](Properties/SelfCallAuthorityFaithful.lean) | [Proofs/SelfCallAuthorityFaithful.lean](Proofs/SelfCallAuthorityFaithful.lean) |
| ValueLedgerFaithful | [Specs/ValueLedgerFaithful.lean](Specs/ValueLedgerFaithful.lean) | [Properties/ValueLedgerFaithful.lean](Properties/ValueLedgerFaithful.lean) | [Proofs/ValueLedgerFaithful.lean](Proofs/ValueLedgerFaithful.lean) |

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
  self-calls `executeAtomicBundle` (`UpgradeDelegationSound`,
  `AtomicSelfDisjunctLiveAndCheckedAtUpgrade`; at the pin that disjunct is dead,
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

The atomic path's source identity is reviewed separately under
`../L2InteropHandler/`. Destination-wide composition is
`../../Protocol/DestinationCapstone.lean`. Whole-program call-site enumeration, the
static-call and no-callback facts above, and binding the actual executed bytes to
authenticated bundle bytes are separate implementation obligations, not discharged by
these abstract state machines.
