# InteropHandlerBase

## Headline guarantees

About `interop/interop-handler/InteropHandlerBase.sol` and its two handlers `L2InteropHandler.sol`
(`executeAtomicBundle`, `verifyAtomicBundle`) and `L1InteropHandler.sol` (`executeBundle`,
`verifyBundle`), with the shared `unbundleBundle` and `receiveMessage`, at era-contracts
`draft/v0.35.0` head `b17415d20`. "Every run" means every sequence of transactions, on one layer,
with every behaviour of every delivered call's target at every depth (re-entrant calls to any of the
layer's entry points, caught or not), every budget and every proof verdict, in the deployed write
order. No headline takes a hash premise: the handler keys its state by the bundle hash, and so do the
statements.

The re-entrancy headlines share the model premises `MODEL-HANDLER-REENTRY-V35`: execution re-enters
the handler only through a delivered call's target; `requireFlowFinalized`, `_proveInclusion` and
`BASE_TOKEN_ASSET_ID()` are static calls and `_handleCallValue` reaches no entry point (argued in
the Specs header, not proved); each entry-point call carries its proof verdict as an input; a bundle
is its hash and its call count; a reverted frame's writes and logs are undone (`VM-REVERT`). The
dispatch headlines share the premise that the calls reaching a permission gate are a direct call by
an account other than the handler, or the self-call of one `receiveMessage` arm (the self-call
inventory, checked by hand at `b17415d20`).

| Guarantee | Premises | Lean name |
|---|---|---|
| No call is delivered twice and no bundle completes twice, across whole-bundle execution and unbundling, in one transaction or several | every run, any start state; model premises | `Contracts.InteropHandlerAtV35.Properties.NoEffectCommittedTwiceAtV35` |
| Every committed effect was open when the run started and is spent at its end | every run, any start state; model premises | `…Properties.CommittedEffectsWereOpenAtV35` |
| A successful `execute` commits exactly its own bundle's calls `0..n-1` in order, then `BundleExecuted`, and leaves it `FullyExecuted` | any state, targets and verdict; model premises | `…Properties.WholeBundleExecutionRunsEachCallOnceAtV35` |
| `callStatus` is `Executed` exactly for delivered calls, `bundleStatus` is `FullyExecuted` exactly for executed bundles | the run starts from fresh storage; model premises | `…Properties.StatusRecordsExactlyTheCommittedEffectsAtV35` |
| Nested execution moves every bundle and call status along `BundleStatusMachine`'s edges | the start state has processed calls only for closed bundles (fresh storage does); model premises | `…Properties.NestedExecutionFollowsTheStatusMachineAtV35` |
| A re-entrant call for an executing bundle reverts (the CEI claim at `L2InteropHandler.sol:55-58`) | model premises | `…Properties.ReentryForAnExecutingBundleRevertsAtV35` |
| A target that reverts from every state reverts the whole `execute` | that target is one of the bundle's first `calls` targets; any write order; model premises | `…Properties.AlwaysRevertingTargetRevertsTheExecutionAtV35` |
| A target that reverts from the state the call loop reaches it in reverts the whole `execute` | the loop over the earlier calls commits to that state; any write order; model premises | `…Properties.TargetRevertingWhereReachedRevertsTheExecutionAtV35` |
| A failed attempt leaves the state as it was, and a retry whose targets return executes the bundle | the bundle is `Unreceived`; one target always reverts; both attempts carry a passing verdict; on L1 a one-call bundle to `L1_ASSET_ROUTER` (omitted reject-only checks); model premises | `…Properties.FailedAttemptCanBeRetriedAtV35` |
| A bundle hash none of whose entry-point calls (any depth) carries a passing verdict stays `Unreceived` with no committed effect; on L2 the verdict is the flow gate's | the hash is `Unreceived` at the start; model premises | `…Properties.DeliveryNeedsTheGateAtV35` |
| Every call passing a permission gate carries a principal the bundle's attribute admits, under both `b17415d20` dispatch tables | the self-call inventory | `AttackVectors.SelfCallAuthority.Faithful.Properties.DelegationSoundAtV35` |
| An admitted relayed call on L1 acts for the original sender `(sourceChainId, from)`, whom the attribute must name | ERC-7930 round trip on the relayed pair; the self-call inventory | `AttackVectors.SelfCallAuthority.Properties.DeployedSelfCallRelaysOriginalSenderAuthority` |
| The same on L2, whose execute arm self-calls `executeAtomicBundle` | ERC-7930 round trip on the relayed pair; the self-call inventory | `AttackVectors.SelfCallAuthority.Properties.DeployedL2SelfCallRelaysOriginalSenderAuthority` |

Witnesses (`@[witness]`): `ReentrantExecutionWitnessAtV35`, `RevertingTargetWitnessAtV35`,
`CaughtReentrantRevertWitnessAtV35`, `GateRoutesWitnessAtV35`, `AtomicSelfDisjunctLiveAndCheckedAtV35`,
`SelfCallRelayWitness`, `DeployedL2SelfCallRelayWitness`.
Countermodels (`@[countermodel]`): `VerifiedBundleExecutesWithoutTheGateAtV35` (a `Verified` bundle
executes with a failing verdict), `ReceiveFilterIsReadAtTheGateAtV35` (the receive filter is read at
the gate only), the four write-order countermodels `StatusWriteAfterCalls…AtV35` /
`CallWriteAfterCalls…AtV35` (the deployed order is necessary), `UncheckedAtomicArmWidensAuthority`,
`MiswiredCheckWidensAuthority`, `UncheckedAtomicBranchWidensAuthority`,
`MisparsedSenderBreaksTheRelay` (the round trip is necessary).

## The model: one stack

Every non-History file cites `b17415d20`. `History/` is the record of the interop pin `c67894b9`, not
a claim about `b17415d20`.

| Layer | Files | Namespace |
|---|---|---|
| Status vocabulary and guard machine (abstract) | `BundleStatusMachine` | `AttackVectors.BundleStatusMachine` |
| Re-entrant execution engine: four entry points, every target tree, every depth | `Reentrancy`, `ReentrancyStrong`, `BundleStatusMachineFaithful` (gate predicates), `ValueLedgerFaithful` (base-token ledger) | `Contracts.InteropHandler` |
| The `b17415d20` layer: each handler's entry points (`EntryAtV35 ℓ`), linked to the engine by `ExecMatchesPinAtV35`/`SubmitAllMatchesPinAtV35` | `ReentrancyAtV35` (part of topic `Reentrancy`) | `Contracts.InteropHandlerAtV35` |
| The `receiveMessage` dispatch and its self-call relay | `SelfCallAuthority`, `SelfCallAuthorityFaithful` (tables), `SelfCallAuthorityStrong` (relay) | `AttackVectors.SelfCallAuthority` |

The engine's `executeBundle`, `verifyBundle` and `unbundleBundle` are `b17415d20`'s L1 entry points;
the translation sends L2's `executeAtomicBundle`/`verifyAtomicBundle` to them with the flow gate's
verdict. The engine's fourth entry `executeAtomicBundle` is the pin's L2 entry (admits `Unreceived`
only); the translation never produces it, so it only adds runs. The engine statements are
untagged supporting lemmas: the headlines are the `b17415d20` layer's, proved through the
translation. `ReentrancyAtV35` is kept as its own file because its proofs use the engine's
`ReentrancyStrong` and gate lemmas, which come after `Proofs/Reentrancy.lean`.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| BundleStatusMachine | [Specs](Specs/BundleStatusMachine.lean) | [Properties](Properties/BundleStatusMachine.lean) | [Proofs](Proofs/BundleStatusMachine.lean) |
| Reentrancy (engine) | [Specs](Specs/Reentrancy.lean) | [Properties](Properties/Reentrancy.lean) | [Proofs](Proofs/Reentrancy.lean) |
| Reentrancy (`b17415d20` layer) | [Specs](Specs/ReentrancyAtV35.lean) | [Properties](Properties/ReentrancyAtV35.lean) | [Proofs](Proofs/ReentrancyAtV35.lean) |
| ReentrancyStrong | [Specs](Specs/ReentrancyStrong.lean) | [Properties](Properties/ReentrancyStrong.lean) | [Proofs](Proofs/ReentrancyStrong.lean) |
| BundleStatusMachineFaithful | [Specs](Specs/BundleStatusMachineFaithful.lean) | [Properties](Properties/BundleStatusMachineFaithful.lean) | [Proofs](Proofs/BundleStatusMachineFaithful.lean) |
| ValueLedgerFaithful | [Specs](Specs/ValueLedgerFaithful.lean) | [Properties](Properties/ValueLedgerFaithful.lean) | [Proofs](Proofs/ValueLedgerFaithful.lean) |
| SelfCallAuthority | [Specs](Specs/SelfCallAuthority.lean) | [Properties](Properties/SelfCallAuthority.lean) | [Proofs](Proofs/SelfCallAuthority.lean) |
| SelfCallAuthorityFaithful | [Specs](Specs/SelfCallAuthorityFaithful.lean) | [Properties](Properties/SelfCallAuthorityFaithful.lean) | [Proofs](Proofs/SelfCallAuthorityFaithful.lean) |
| SelfCallAuthorityStrong | [Specs](Specs/SelfCallAuthorityStrong.lean) | [Properties](Properties/SelfCallAuthorityStrong.lean) | [Proofs](Proofs/SelfCallAuthorityStrong.lean) |

Notes on the supporting topics:
- `BundleStatusMachine`'s statements are about the abstract edge relation; its "no inflation" results
  are list identities, tied to the handler by `ValueLedgerFaithful` (`ReleaseIsTheHandlerLedger`,
  `HandlerReleasesAtMostCollected`, under the run-local binding premise `NamesOnly`, which is
  satisfiable (`LedgerWitness`) and load-bearing (`SharedHashBreaksTheLedger`)). Restating the
  ledger on the `b17415d20` layer is a follow-up.
- `SelfCallAuthority.selfCall_relays_authority` is a tautology
  (`selfCall_relays_authority_conclusion_always_holds`); `SelfCallAuthorityFaithful` and
  `SelfCallAuthorityStrong` state the claim. `pinnedTable` (the pin's dispatch) is, as a list, the
  `b17415d20` L1 table, so its statements also hold for the `b17415d20` L1 handler.
- Open items: the self-call inventory and the static-call facts are argued, not derived;
  `scripts/check-interop-handler-inventory.sh` checks the pin's layout only; the bytes-to-hash
  binding behind `NamesOnly` is `InteropDataEncoding`'s obligation; values are naturals.

## History (`c67894b9`)

- `History/*/BundleStatusMachine.lean` (`AttackVectors.BundleStatusMachine.History`): the atomic
  sub-machine `AtomicStep`/`AtomicReach`, which assumed an atomic bundle never reaches `Verified`.
  At `b17415d20` `verifyAtomicBundle` (`L2InteropHandler.sol:83-92`) verifies it.
- `History/*/BundleStatusMachineFaithful.lean`: the labelled machine of the pin's edges, the
  never-published statements (`NeverPublishedBundleNeedsTheFlowGate`) and their countermodels.
- `History/*/BundleStatusMachineStrong.lean` (`Contracts.InteropHandler.History`): the atomic
  sub-machine derived from the pin's guards and the pin's `InteropCenter`/bundle-hash models.

Destination-wide composition is `../../Protocol/DestinationCapstone.lean`; the atomic path's source
identity is under `../L2InteropHandler/`.
