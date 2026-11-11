import EraSpec.Contracts.InteropHandlerBase.Specs.ReentrancyAtHead

/-!
# Properties: the pinned re-entrancy results, re-checked at head

Statements about `EraSpec.Contracts.InteropHandlerBase.Specs.ReentrancyAtHead`, the L2 handler at
main `3605e82` (and, with the same logic, `e561b9cc2` and v0.35 `d9f6789`). Proofs are in
`EraSpec.Contracts.InteropHandlerBase.Proofs.ReentrancyAtHead`.

Each statement below is the head counterpart of a pinned one in
`Properties/Reentrancy.lean`, re-checked against a model that has `verifyAtomicBundle` and an
`executeAtomicBundle` that admits a `Verified` bundle without consulting the flow gate. As there,
every result quantifies over every target behaviour (`Callee` trees, so re-entrant calls to any entry
point at any depth, caught or not) and every budget, and none takes a hash premise. The log carries
flow-gate events as well; `effects` removes them, giving the pinned log.

All of them still hold:

* **No effect is committed twice** (`NoEffectCommittedTwiceAtHead`). Each logged effect was open
  where the sequence started and is spent where it ends (`CommittedEffectsWereOpenAtHead`).
* **A successful `executeAtomicBundle` runs each of its calls once** and leaves the bundle
  `FullyExecuted`, whether it started `Unreceived` or `Verified`
  (`WholeAtomicExecutionRunsEachCallOnceAtHead`).
* **The replay state is the committed history** (`StatusRecordsExactlyTheCommittedEffectsAtHead`),
  and nested execution follows `BundleStatusMachine`'s `Reach` and `CallReach`
  (`NestedExecutionFollowsTheStatusMachineAtHead`). The new edges are existing `Step`s:
  `verifyAtomicBundle` is `Step.verify`, and `executeAtomicBundle` of a `Verified` bundle is
  `Step.executeVerified`. They are not `BundleStatusMachine.AtomicStep`s: that sub-machine describes
  the pin only (see `AtomicUnbundlingAtHead`).
* **Re-entry for an executing bundle reverts** (`ReentryForAnExecutingBundleRevertsAtHead`, the NatSpec
  at `L2InteropHandler.sol:45-48`), for all three entry points.
* **A reverting target reverts `executeAtomicBundle`** (`RevertingCallRevertsAtomicExecutionAtHead`),
  from either admitted status, **and a failed attempt can be retried**
  (`FailedAtomicAttemptCanBeRetriedAtHead`).

What these do **not** say at head: that an atomic bundle runs all of its calls or none. They are
about one `executeAtomicBundle` call. After `verifyAtomicBundle`, the same bundle can instead be
unbundled, running some calls and cancelling the others for good; that is
`AtomicUnbundlingAtHead`, which also states the guarantee that replaces it.

Witnesses: `ReentrantExecutionWitnessAtHead` (the pinned nesting witness at head) and
`NestedVerifyAndUnbundleWitnessAtHead` (a target that verifies and unbundles another bundle
re-entrantly).
-/

namespace Contracts.InteropHandlerAtHead

open AttackVectors.BundleStatusMachine (Status CallStatus Reach CallReach)
open Contracts.InteropHandler (BundleHash Bundle State Effect Spent CallsClosed init wA wB)

/-! ## Nothing runs twice -/

/-- **NO EFFECT IS COMMITTED TWICE, AT HEAD.** For every state and every sequence of transactions,
with every behaviour of every target at every depth, the committed effects have no repeated entry:
no call `i` of a bundle hash `h` is delivered twice, by the whole-bundle route, the unbundled route
or both, and no bundle hash completes `executeAtomicBundle` twice. -/
def Properties.NoEffectCommittedTwiceAtHead : Prop :=
  ∀ (s : State) (txs : List Tx), (effects (submitAll s txs).2).Nodup

/-- **EACH COMMITTED EFFECT WAS OPEN, AND IS CLOSED, AT HEAD.** Every effect committed by a sequence
of transactions was not spent in the state the sequence started from, and is spent in the state it
ends in. -/
def Properties.CommittedEffectsWereOpenAtHead : Prop :=
  ∀ (s : State) (txs : List Tx) (e : Effect), e ∈ effects (submitAll s txs).2 →
    ¬ Spent s e ∧ Spent (submitAll s txs).1 e

/-- **A SUCCESSFUL `executeAtomicBundle` RUNS EACH OF ITS CALLS ONCE.** If `executeAtomicBundle` of
bundle `b` succeeds, from any state (so from `Unreceived` or from `Verified`) and with any targets,
then the effects of `b.hash` it commits are exactly the deliveries of calls `0, …, n-1`, in order,
then `BundleExecuted`; and `b.hash` ends `FullyExecuted`. -/
def Properties.WholeAtomicExecutionRunsEachCallOnceAtHead : Prop :=
  ∀ (n : ℕ) (b : Bundle) (ok : Bool) (cs : List Callee) (s s' : State) (l : List Event),
    exec n (.entry (.executeAtomicBundle b ok) cs) s = some (s', l) →
    (effects l).filter (fun e => e.bundleHash = b.hash) =
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash] ∧
      s'.bundle b.hash = .FullyExecuted

/-- **THE REPLAY STATE IS THE COMMITTED HISTORY, AT HEAD.** After any sequence of transactions from
fresh storage, call `i` of bundle hash `h` is recorded `Executed` if and only if a delivery of it was
committed, and `h` is `FullyExecuted` if and only if its `BundleExecuted` was. -/
def Properties.StatusRecordsExactlyTheCommittedEffectsAtHead : Prop :=
  ∀ (txs : List Tx) (h : BundleHash) (i : ℕ),
    ((submitAll init txs).1.call h i = .Executed ↔
        Effect.delivered h i ∈ effects (submitAll init txs).2) ∧
    ((submitAll init txs).1.bundle h = .FullyExecuted ↔
        Effect.executed h ∈ effects (submitAll init txs).2)

/-- **NESTED EXECUTION FOLLOWS THE STATUS MACHINE, AT HEAD.** From any state in which only bundles
that left both entry states have processed calls (`CallsClosed`; fresh storage is one), along any
sequence of transactions: that still holds at the end, every bundle status moved along
`BundleStatusMachine.Reach`, and every call status along `BundleStatusMachine.CallReach`. -/
def Properties.NestedExecutionFollowsTheStatusMachineAtHead : Prop :=
  CallsClosed init ∧
  ∀ (s : State) (txs : List Tx), CallsClosed s →
    CallsClosed (submitAll s txs).1 ∧
    (∀ h, Reach (s.bundle h) ((submitAll s txs).1.bundle h)) ∧
    ∀ h i, CallReach (s.call h i) ((submitAll s txs).1.call h i)

/-- **A RE-ENTRANT CALL FOR AN EXECUTING BUNDLE HITS THE STATUS CHECK, AT HEAD**
(`L2InteropHandler.sol:45-48`). The calls of an `executeAtomicBundle` of `b` run from a state in
which `b.hash` is `FullyExecuted`; everything committed from such a state keeps it so; and from such
a state every entry point called on a bundle with that hash reverts, whichever of the three it
is. -/
def Properties.ReentryForAnExecutingBundleRevertsAtHead : Prop :=
  (∀ (b : Bundle) (s : State), (markFullyExecuted b s).bundle b.hash = .FullyExecuted) ∧
  (∀ (n : ℕ) (f : Frame) (h : BundleHash) (s s' : State) (l : List Event),
    s.bundle h = .FullyExecuted → exec n f s = some (s', l) →
    s'.bundle h = .FullyExecuted) ∧
  ∀ (n : ℕ) (e : Entry) (cs : List Callee) (s : State),
    s.bundle e.bundle.hash = .FullyExecuted → exec n (.entry e cs) s = none

/-- **THE RESULTS ABOVE ARE ABOUT REAL NESTING.** From fresh storage, in `wNested`, call 0 of `wA`
reaches a target that executes `wB` re-entrantly, then tries `wA` again and catches the refusal: the
transaction commits both bundles, each call once, with `wB`'s effects nested inside `wA`'s first
delivery and each flow gate logged before its bundle's effects. -/
def Properties.ReentrantExecutionWitnessAtHead : Prop :=
  (submit init wNested).2 =
      [.gated 1, .effect (.delivered 1 0), .gated 2, .effect (.delivered 2 0),
        .effect (.executed 2), .effect (.delivered 1 1), .effect (.executed 1)] ∧
    (submit init wNested).1.bundle 1 = .FullyExecuted ∧
    (submit init wNested).1.bundle 2 = .FullyExecuted

/-- **THE NEW ENTRY POINT NESTS TOO.** From fresh storage, in `wNestedUnbundle`, call 0 of `wA`
reaches a target that verifies `wB` and unbundles it, executing its only call, then tries to verify
`wA` and catches the refusal. The transaction commits `wA` whole and `wB`'s call through the unbundled
route, and leaves `wB` `Unbundled`. -/
def Properties.NestedVerifyAndUnbundleWitnessAtHead : Prop :=
  (submit init wNestedUnbundle).2 =
      [.gated 1, .effect (.delivered 1 0), .verified 2, .effect (.delivered 2 0),
        .effect (.delivered 1 1), .effect (.executed 1)] ∧
    (submit init wNestedUnbundle).1.bundle 1 = .FullyExecuted ∧
    (submit init wNestedUnbundle).1.bundle 2 = .Unbundled ∧
    (submit init wNestedUnbundle).1.call 2 0 = .Executed

/-! ## A failing call rolls the execution back -/

/-- **A REVERTING TARGET REVERTS `executeAtomicBundle`, AT HEAD.** If the target of one of bundle
`b`'s calls reverts, then `executeAtomicBundle` of `b` reverts, from every state and with every gate
verdict, whatever the targets before it did in their own frames. This is a statement about the
execute route only: after `verifyAtomicBundle`, the unbundled route can skip or cancel that call
(`AtomicUnbundlingAtHead`). -/
def Properties.RevertingCallRevertsAtomicExecutionAtHead : Prop :=
  ∀ (n : ℕ) (b : Bundle) (ok : Bool) (cs : List Callee) (s : State),
    Callee.reverts ∈ cs.take b.calls →
    exec n (.entry (.executeAtomicBundle b ok) cs) s = none

/-- **SO A FAILED ATTEMPT CAN BE RETRIED, AT HEAD.** If bundle `b` is `Unreceived` or `Verified` and
one of its calls' targets reverts, the transaction `executeAtomicBundle(b)` leaves the state exactly
as it was and commits nothing. From that same state, a retry with a passing gate whose targets
return logs the gate unless the bundle was `Verified`, delivers each of `b`'s calls once, in order,
and executes `b`. -/
def Properties.FailedAtomicAttemptCanBeRetriedAtHead : Prop :=
  ∀ (s : State) (b : Bundle) (fuel : ℕ) (ok : Bool) (cs : List Callee),
    (s.bundle b.hash = .Unreceived ∨ s.bundle b.hash = .Verified) →
    Callee.reverts ∈ cs.take b.calls →
    submit s ⟨fuel, .executeAtomicBundle b ok, cs⟩ = (s, []) ∧
    submit s ⟨b.calls + 2, .executeAtomicBundle b true, List.replicate b.calls .returns⟩ =
      (markFullyExecuted b s,
        gateLog s b.hash ++
          ((List.range b.calls).map fun i => Event.effect (.delivered b.hash i)) ++
          [.effect (.executed b.hash)])

end Contracts.InteropHandlerAtHead
