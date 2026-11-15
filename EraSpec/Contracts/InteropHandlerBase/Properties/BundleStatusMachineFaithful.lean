import EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachineFaithful

/-!
# Properties: the never-published premise is what keeps the atomicity gate unbypassable

Statements about `EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachineFaithful`. Proofs
are in `EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachineFaithful`.

## (a) The labelled machine

* `lstep_refines_step`: labelling loses no edge and adds none.
* `atomic_entry_needs_unreceived`: the atomic entry point's only edge leaves `Unreceived`. This is
  all `BundleStatusMachine.verified_blocks_atomic_execution` can mean.
* `verified_runs_unchecked`: but `Verified` is no dead end. `executeBundle` takes it to
  `FullyExecuted` and `unbundleBundle` to `Unbundled`, each with no inclusion proof and no flow gate.
* `route_consults_inclusion_or_flowGate` (the conditional, corrected): every path from `Unreceived`
  to `FullyExecuted` or `Unbundled` consults an inclusion proof or the flow gate; and
  `no_inclusion_paths_are_atomic`: one that consults no inclusion proof stays inside
  `BundleStatusMachine.AtomicReach`, so `AtomicStep` is exactly the machine with every
  inclusion-proof edge removed (`executeFresh` as well as `verify`).
* `inclusion_routes_skip_flowGate`: and an inclusion proof alone suffices, by three routes.

## (b) The same, operationally (`Contracts.InteropHandler.exec`, re-entrant)

* `DeliveryNeedsInclusionOrFlowGate`: along any sequence of transactions, with every target
  behaviour at every depth, a bundle hash none of whose entry-point calls presents an accepted
  inclusion proof or passes the flow gate stays `Unreceived` and has no committed effect.
* `NeverPublishedBundleNeedsTheFlowGate` (the headline): under the never-published premise alone,
  the bundle's status stays inside `AtomicReach`, and if anything of it is committed then some
  entry-point call of the sequence passed the flow gate for it.
* `ProvableBytesBypassTheFlowGate` (countermodel, premise dropped): for every bundle, wherever it is
  `Unreceived`, the flow gate refusing it does not stop `executeBundle` with an accepted inclusion
  proof from running every call and completing it, in a transaction that passes no flow gate.
* `VerifiedBundleRunsWithoutAnyGate` (countermodel to "bricked"): for every `Verified` bundle, the
  atomic entry point refuses it, and `executeBundle` with no accepted proof runs every call.
* `FlowGateRoutesWitness`: on a one-call bundle from fresh storage, the gated route and the three
  gate-free routes (fresh, verified, unbundled), each with its committed log.
-/

namespace AttackVectors.BundleStatusMachine.Faithful

/-! ## (a) The labelled machine -/

/-- **THE LABELS ADD ONLY NAMES.** An unlabelled edge is a labelled one with its labels forgotten,
and every labelled edge is an unlabelled one. -/
def Properties.lstep_refines_step : Prop :=
  ∀ s t : Status, Step s t ↔ ∃ (e : EntryPoint) (c : Check), LStep s e c t

/-- **THE ATOMIC ENTRY POINT NEEDS `Unreceived`.** Every edge `executeAtomicBundle` takes starts at
`Unreceived` (`L2InteropHandler.sol:79`); in particular none starts at `Verified`. -/
def Properties.atomic_entry_needs_unreceived : Prop :=
  ∀ (s t : Status) (c : Check), LStep s .executeAtomicBundle c t → s = .Unreceived

/-- **BUT `Verified` IS NOT A DEAD END.** From `Verified`, `executeBundle` reaches `FullyExecuted` and
`unbundleBundle` reaches `Unbundled`, each consulting no check: a bundle that reached `Verified` is
deliverable without the atomicity gate, not undeliverable. -/
def Properties.verified_runs_unchecked : Prop :=
  LStep .Verified .executeBundle .noCheck .FullyExecuted ∧
    LStep .Verified .unbundleBundle .noCheck .Unbundled

/-- **EVERY ROUTE CONSULTS AN INCLUSION PROOF OR THE FLOW GATE.** Along every labelled path from
`Unreceived` to `FullyExecuted` or `Unbundled`, an inclusion proof or the flow gate was consulted.
Where no inclusion proof can succeed, as for a bundle whose bytes are never published, the flow gate
was. -/
def Properties.route_consults_inclusion_or_flowGate : Prop :=
  ∀ (cs : List Check) (t : Status), LReach .Unreceived cs t →
    (t = .FullyExecuted ∨ t = .Unbundled) → Check.inclusionProof ∈ cs ∨ Check.flowGate ∈ cs

/-- **WITHOUT INCLUSION PROOFS THE MACHINE IS `AtomicStep`.** Every labelled path from `Unreceived`
that consults no inclusion proof ends in a state `AtomicReach` reaches: `executeFresh` is closed by
the never-published premise exactly as `verify` is. -/
def Properties.no_inclusion_paths_are_atomic : Prop :=
  ∀ (cs : List Check) (t : Status), LReach .Unreceived cs t → Check.inclusionProof ∉ cs →
    AtomicReach .Unreceived t

/-- **AN INCLUSION PROOF ALONE SUFFICES.** Three routes deliver from `Unreceived` without the flow
gate: `executeBundle` fresh; `verifyBundle` then `executeBundle`; `verifyBundle` then
`unbundleBundle`. -/
def Properties.inclusion_routes_skip_flowGate : Prop :=
  LReach .Unreceived [.inclusionProof] .FullyExecuted ∧
    LReach .Unreceived [.inclusionProof, .noCheck] .FullyExecuted ∧
    LReach .Unreceived [.inclusionProof, .noCheck] .Unbundled

end AttackVectors.BundleStatusMachine.Faithful

namespace Contracts.InteropHandler.Faithful

open AttackVectors.BundleStatusMachine (Status AtomicReach)

/-! ## (b) Operationally -/

/-- **NO ACCEPTED INCLUSION PROOF AND NO PASSING FLOW GATE, NO DELIVERY.** From every state in which
bundle hash `h` is `Unreceived`, along every sequence of transactions none of whose entry-point
calls (at any depth, in any target) presents an inclusion proof accepted for `h` or passes the flow
gate for `h`: `h` ends `Unreceived`, and no committed effect belongs to `h`. None of its calls is
delivered and it never completes. -/
def Properties.DeliveryNeedsInclusionOrFlowGate : Prop :=
  ∀ (s : State) (h : BundleHash) (txs : List Tx), s.bundle h = .Unreceived →
    (∀ t ∈ txs, TxAll (fun e => ¬ ProvesInclusion h e ∧ ¬ PassesFlowGate h e) t) →
      (submitAll .deployed s txs).1.bundle h = .Unreceived ∧
        ∀ e ∈ (submitAll .deployed s txs).2, e.bundleHash ≠ h

/-- **UNDER THE NEVER-PUBLISHED PREMISE, THE ATOMICITY GATE CANNOT BE BYPASSED.** From every state in
which `h` is `Unreceived`, along every sequence of transactions none of whose entry-point calls
presents an inclusion proof accepted for `h` (no L1 publication of its bytes exists to prove):
`h`'s status stays inside `AtomicReach` (`Unreceived` or `FullyExecuted`, never `Verified` or
`Unbundled`), and if any effect of `h` is committed, some entry-point call of the sequence passed
the flow gate for `h`. -/
def Properties.NeverPublishedBundleNeedsTheFlowGate : Prop :=
  ∀ (s : State) (h : BundleHash) (txs : List Tx), s.bundle h = .Unreceived →
    (∀ t ∈ txs, TxAll (fun e => ¬ ProvesInclusion h e) t) →
      AtomicReach .Unreceived ((submitAll .deployed s txs).1.bundle h) ∧
        ((∃ e ∈ (submitAll .deployed s txs).2, e.bundleHash = h) →
          ¬ ∀ t ∈ txs, TxAll (fun e => ¬ PassesFlowGate h e) t)

/-- **IF A BUNDLE'S BYTES WERE PROVABLE, THE FLOW GATE WOULD BE BYPASSED.** For every bundle `b` and
every state in which it is `Unreceived`: `executeAtomicBundle(b)` with the flow gate refusing commits
nothing, whatever its fuel and targets; yet `executeBundle(b)` with an accepted inclusion proof, in a
transaction none of whose entry-point calls passes the flow gate for `b`, delivers each of `b`'s
calls once, in order, and completes `b`. So the never-published premise is a safety premise for
atomic bundles: without it the atomicity gate is bypassable. -/
def Properties.ProvableBytesBypassTheFlowGate : Prop :=
  ∀ (s : State) (b : Bundle), s.bundle b.hash = .Unreceived →
    (∀ (fuel : ℕ) (cs : List Callee),
        submit .deployed s ⟨fuel, .executeAtomicBundle b false, cs⟩ = (s, [])) ∧
      TxAll (fun e => ¬ PassesFlowGate b.hash e) (freshPublicRun b) ∧
      (submit .deployed s (freshPublicRun b)).2 =
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash]

/-- **A `Verified` BUNDLE IS NOT BRICKED: IT RUNS WITH NO INCLUSION PROOF AND NO FLOW GATE.** ("No
gate" in the name means neither of these two; the source still runs the pause, destination-context
and execution-address checks on `executeBundle`, which `executeAtomicBundle` runs too and the model
omits as reject-only.) For every bundle `b` and
every state in which it is `Verified`: `executeAtomicBundle(b)` commits nothing, whatever its gate
verdict, fuel and targets (`L2InteropHandler.sol:79`); but `executeBundle(b)` with no accepted proof,
in a transaction none of whose entry-point calls presents an accepted proof or passes the flow gate
for `b`, delivers each of `b`'s calls once, in order, and completes `b` (`Verified` skips `:123`). -/
def Properties.VerifiedBundleRunsWithoutAnyGate : Prop :=
  ∀ (s : State) (b : Bundle), s.bundle b.hash = .Verified →
    (∀ (fuel : ℕ) (gate : Bool) (cs : List Callee),
        submit .deployed s ⟨fuel, .executeAtomicBundle b gate, cs⟩ = (s, [])) ∧
      TxAll (fun e => ¬ ProvesInclusion b.hash e ∧ ¬ PassesFlowGate b.hash e)
        (provelessPublicRun b) ∧
      (submit .deployed s (provelessPublicRun b)).2 =
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash]

/-- **ALL FOUR ROUTES, ON A WITNESS.** From fresh storage, for bundle `wC` (hash `3`, one call): the
gated route (`executeAtomicBundle`, gate passing) delivers it, in a run that satisfies the
never-published headline's premise for hash `3` (no entry-point call presents an accepted inclusion
proof), so that premise and the headline's antecedent hold together; and with no flow gate anywhere, `executeBundle` with a proof delivers it,
`verifyBundle` then `executeBundle` without a proof delivers it, and `verifyBundle` then
`unbundleBundle` delivers its call and leaves it `Unbundled`. -/
def Properties.FlowGateRoutesWitness : Prop :=
  (submitAll .deployed init [wAtomicC]).2 = [.delivered 3 0, .executed 3] ∧
    (submitAll .deployed init [wFreshC]).2 = [.delivered 3 0, .executed 3] ∧
    (submitAll .deployed init [wVerifyC, wProvelessC]).2 = [.delivered 3 0, .executed 3] ∧
    (submitAll .deployed init [wVerifyC, wUnbundleC]).2 = [.delivered 3 0] ∧
    (submitAll .deployed init [wVerifyC, wUnbundleC]).1.bundle 3 = .Unbundled ∧
    (∀ t ∈ [wFreshC, wVerifyC, wProvelessC, wUnbundleC], TxAll (fun e => ¬ PassesFlowGate 3 e) t) ∧
    (∀ t ∈ [wAtomicC], TxAll (fun e => ¬ ProvesInclusion 3 e) t)

end Contracts.InteropHandler.Faithful
