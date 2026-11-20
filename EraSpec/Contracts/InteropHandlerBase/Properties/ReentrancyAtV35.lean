import EraSpec.Contracts.InteropHandlerBase.Specs.ReentrancyAtV35

/-!
# Properties: re-entrant execution in the v35 handlers

Statements about `EraSpec.Contracts.InteropHandlerBase.Specs.ReentrancyAtV35` (era-contracts
`draft/v0.35.0` at `b17415d20`). Proofs are in
`EraSpec.Contracts.InteropHandlerBase.Proofs.ReentrancyAtV35`.

The general statements quantify over every target behaviour (`CalleeAtV35` trees: re-entrant calls
to any of the layer's entry points, at any depth, caught or not) and every budget; the witnesses and
the concrete countermodels are evaluated runs. None takes a hash premise: the handler keys its state
by the bundle hash, and so do the statements. Where a result says "both layers", it holds for
`L2InteropHandler` (`execute` = `executeAtomicBundle`, `verify` = `verifyAtomicBundle`) and for
`L1InteropHandler` (`executeBundle`, `verifyBundle`).

## (a) The v35 handlers are the engine, translated

* `ExecMatchesPinAtV35`: in the deployed order on both layers, in the order `callWriteAfterCalls`
  on both layers, and in every order on L1, a v35 frame runs exactly as its translation does in the
  engine `Contracts.InteropHandler.exec`: same state, same committed log, same revert.
  `SubmitAllMatchesPinAtV35` lifts this to sequences of transactions.
* `LateStatusWriteSeparatesL2FromPinAtV35`: the excluded case is a real difference.
* `PinMatchWitnessAtV35`: both cases of the premise, on runs that commit nested work.

## (b) Nothing runs twice, on both layers, in the deployed order

The engine's results, restated over `submitAllAtV35`/`execAtV35` and proved through (a):
`NoEffectCommittedTwiceAtV35` (headline), `CommittedEffectsWereOpenAtV35`,
`WholeBundleExecutionRunsEachCallOnceAtV35`, `StatusRecordsExactlyTheCommittedEffectsAtV35`,
`NestedExecutionFollowsTheStatusMachineAtV35`, and `ReentryForAnExecutingBundleRevertsAtV35`, the
claim of the NatSpec at `L2InteropHandler.sol:55-58`. Witness: `ReentrantExecutionWitnessAtV35`.

## (c) A failing call rolls the execution back

For a target that reverts from every state (`AlwaysRevertsAtV35`), or where the loop reaches it,
not only the leaf `reverts`: `AlwaysRevertingTargetRevertsTheExecutionAtV35`,
`TargetRevertingWhereReachedRevertsTheExecutionAtV35` (every order, both layers), and
`FailedAttemptCanBeRetriedAtV35`, the claim at `InteropHandlerBase.sol:322-324`. Witnesses:
`RevertingTargetWitnessAtV35`, and `CaughtReentrantRevertWitnessAtV35` (a caught re-entrant
revert is undone alone).

## (d) What changed at v35: the gate

* `VerifiedBundleExecutesWithoutTheGateAtV35`: a `Verified` bundle cannot be verified again, and
  executes with a failing verdict.
* `DeliveryNeedsTheGateAtV35` (headline for the gate): a bundle hash none of whose entry-point
  calls carries a passing verdict stays `Unreceived` and has no committed effect. On L2 the only
  verdict is `requireFlowFinalized`'s, so no premise about inclusion proofs is needed, unlike the
  History record `NeverPublishedBundleNeedsTheFlowGate` (pin `c67894b9`).
* `GateRoutesWitnessAtV35`: the three L2 routes, the partial execution after unbundling, and the
  gate premise on a run that commits.
* `ReceiveFilterIsReadAtTheGateAtV35` and `ReceiveFilterWitnessAtV35`: the receive filter decides
  at the gate only, as `protocol-docs/interop-gating.md:195-197` documents.

## (e) The order of the writes is load-bearing (countermodels)

`StatusWriteAfterCallsRunsTwiceAtV35`, `CallWriteAfterCallsRunsTwiceAtV35` (concrete runs),
`StatusWriteAfterCallsRunsAnyBundleTwiceAtV35` and `CallWriteAfterCallsRunsAnyCallTwiceAtV35`
(every bundle with a call and every admitting state, both layers).
-/

namespace Contracts.InteropHandlerAtV35

open AttackVectors.BundleStatusMachine (Status CallStatus Reach CallReach)
open Contracts.InteropHandler (BundleHash Bundle State init Effect Variant beforeCalls Spent
  Recorded CallsClosed exec submit submitAll wA wB wC requestFirst)

/-! ## (a) The translation -/

/-- **A V35 HANDLER RUNS AS ITS TRANSLATION IN THE PIN MODEL.** For layer `ℓ` and write order `v`
with `ℓ = l1` or `v ≠ statusWriteAfterCalls` (so: the deployed order on both layers, the order
`callWriteAfterCalls` on both layers, every order on L1), from every state and at every budget,
running a v35 frame gives exactly what running its translation `FrameAtV35.toPin` gives in the pin
model: the same final state and committed log, or a revert on both sides. The translation sends
`execute` to the engine's `executeBundle`, `verify` to `verifyBundle` and `unbundleBundle` to itself,
recursively through every target. On L1 `execute` is the engine's `executeBundle` step for step; on
L2 it skips the engine `executeBundle`'s `Verified` write, which `beforeCalls` overwrites with `FullyExecuted` in both
of these orders before any call runs. -/
def Properties.ExecMatchesPinAtV35 : Prop :=
  ∀ (ℓ : LayerAtV35) (v : Variant), (ℓ = .l1 ∨ v ≠ .statusWriteAfterCalls) →
    ∀ (n : ℕ) (f : FrameAtV35 ℓ) (s : State), execAtV35 ℓ v n f s = exec v n f.toPin s

/-- **AND SO DOES EVERY SEQUENCE OF TRANSACTIONS.** Under the same condition on `ℓ` and `v`, from
every state, a sequence of v35 transactions leaves the state and committed log that the sequence
of their translations leaves in the engine. -/
def Properties.SubmitAllMatchesPinAtV35 : Prop :=
  ∀ (ℓ : LayerAtV35) (v : Variant), (ℓ = .l1 ∨ v ≠ .statusWriteAfterCalls) →
    ∀ (s : State) (txs : List (TxAtV35 ℓ)),
      submitAllAtV35 ℓ v s txs = submitAll v s (txs.map TxAtV35.toPin)

/-- **THE EXCLUDED CASE DIFFERS.** On L2 in the order `statusWriteAfterCalls`, from fresh storage:
`executeAtomicBundle(wC)` with a passing gate whose target re-enters it with a failing gate commits
nothing (the bundle is still `Unreceived` when the re-entry is checked, so the gate is consulted
and refuses), while its translation commits `wC`'s call twice and completes `wC` twice (the pin's
`executeBundle` wrote `Verified` first, so the re-entry is admitted without a proof). -/
def Properties.LateStatusWriteSeparatesL2FromPinAtV35 : Prop :=
  (submitAtV35 .l2 .statusWriteAfterCalls init (wReenterAtomicAtV35 false false)).2 = [] ∧
    (submit .statusWriteAfterCalls init (wReenterAtomicAtV35 false false).toPin).2 =
      [.delivered 3 0, .delivered 3 0, .executed 3, .executed 3]

/-- **BOTH CASES OF THE CONDITION, ON RUNS THAT COMMIT NESTED WORK.** From fresh storage: on L2 in
the deployed order, `wNestedAtV35` (an atomic execution of `wA` whose first target executes `wB`
re-entrantly) gives the same result as its translation, and commits five effects; on L1 in the
order `statusWriteAfterCalls`, `wReenterL1AtV35` gives the same result as its translation, and
commits `wC`'s call twice. -/
def Properties.PinMatchWitnessAtV35 : Prop :=
  submitAtV35 .l2 .deployed init wNestedAtV35 = submit .deployed init wNestedAtV35.toPin ∧
    (submitAtV35 .l2 .deployed init wNestedAtV35).2 =
      [.delivered 1 0, .delivered 2 0, .executed 2, .delivered 1 1, .executed 1] ∧
    submitAtV35 .l1 .statusWriteAfterCalls init wReenterL1AtV35 =
      submit .statusWriteAfterCalls init wReenterL1AtV35.toPin ∧
    (submitAtV35 .l1 .statusWriteAfterCalls init wReenterL1AtV35).2 =
      [.delivered 3 0, .delivered 3 0, .executed 3, .executed 3]

/-! ## (b) Nothing runs twice -/

/-- **NO EFFECT IS COMMITTED TWICE, AT V35.** On both layers, for every state and every sequence of
transactions, with every behaviour of every target at every depth, in the deployed order: the
committed log has no repeated entry. No call `i` of a bundle hash `h` is delivered twice, whether by
whole-bundle execution, unbundling or both, in one transaction or several; and no bundle hash
completes a whole-bundle execution twice. -/
def Properties.NoEffectCommittedTwiceAtV35 : Prop :=
  ∀ (ℓ : LayerAtV35) (s : State) (txs : List (TxAtV35 ℓ)),
    (submitAllAtV35 ℓ .deployed s txs).2.Nodup

/-- **EACH COMMITTED EFFECT WAS OPEN, AND IS CLOSED, AT V35.** On both layers, in the deployed
order: every effect in the committed log of a sequence of transactions was not `Spent` in the state
the sequence started from, and is `Spent` in the state it ends in. -/
def Properties.CommittedEffectsWereOpenAtV35 : Prop :=
  ∀ (ℓ : LayerAtV35) (s : State) (txs : List (TxAtV35 ℓ)) (e : Effect),
    e ∈ (submitAllAtV35 ℓ .deployed s txs).2 →
      ¬ Spent s e ∧ Spent (submitAllAtV35 ℓ .deployed s txs).1 e

/-- **A WHOLE-BUNDLE EXECUTION RUNS EACH OF ITS CALLS ONCE, AT V35.** On both layers, in the
deployed order, from any state and with any targets: if `execute` of bundle `b` succeeds
(`executeAtomicBundle` on L2, `executeBundle` on L1, whatever its verdict `ok`), the effects of
`b.hash` in its committed log are exactly the deliveries of calls `0, …, n-1`, in order, then
`BundleExecuted`; and `b.hash` ends `FullyExecuted`. -/
def Properties.WholeBundleExecutionRunsEachCallOnceAtV35 : Prop :=
  ∀ (ℓ : LayerAtV35) (n : ℕ) (b : Bundle) (ok : Bool) (cs : List (CalleeAtV35 ℓ))
    (s s' : State) (l : List Effect),
    execAtV35 ℓ .deployed n (.entry (.execute b ok) cs) s = some (s', l) →
    l.filter (fun e => e.bundleHash = b.hash) =
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash] ∧
      s'.bundle b.hash = .FullyExecuted

/-- **THE REPLAY STATE IS THE COMMITTED HISTORY, AT V35.** On both layers, in the deployed order,
after any sequence of transactions from fresh storage: call `i` of bundle hash `h` is recorded
`Executed` if and only if the committed log delivered it, and `h` is `FullyExecuted` if and only if
the log executed it. -/
def Properties.StatusRecordsExactlyTheCommittedEffectsAtV35 : Prop :=
  ∀ (ℓ : LayerAtV35) (txs : List (TxAtV35 ℓ)) (h : BundleHash) (i : ℕ),
    ((submitAllAtV35 ℓ .deployed init txs).1.call h i = .Executed ↔
        Effect.delivered h i ∈ (submitAllAtV35 ℓ .deployed init txs).2) ∧
    ((submitAllAtV35 ℓ .deployed init txs).1.bundle h = .FullyExecuted ↔
        Effect.executed h ∈ (submitAllAtV35 ℓ .deployed init txs).2)

/-- **NESTED EXECUTION FOLLOWS THE STATUS MACHINE, AT V35.** Fresh storage satisfies `CallsClosed`.
On both layers, in the deployed order, from any state satisfying it, along any sequence of
transactions: it holds at the end, every bundle status moved along `BundleStatusMachine.Reach`,
and every call status along `BundleStatusMachine.CallReach`. -/
def Properties.NestedExecutionFollowsTheStatusMachineAtV35 : Prop :=
  CallsClosed init ∧
  ∀ (ℓ : LayerAtV35) (s : State) (txs : List (TxAtV35 ℓ)), CallsClosed s →
    CallsClosed (submitAllAtV35 ℓ .deployed s txs).1 ∧
    (∀ h, Reach (s.bundle h) ((submitAllAtV35 ℓ .deployed s txs).1.bundle h)) ∧
    ∀ h i, CallReach (s.call h i) ((submitAllAtV35 ℓ .deployed s txs).1.call h i)

/-- **A RE-ENTRANT CALL FOR AN EXECUTING BUNDLE HITS THE STATUS CHECK, AT V35** (the NatSpec at
`L2InteropHandler.sol:55-58`: no `nonReentrant` guard, because replay safety is by CEI, so "a
reentrant call for this bundle hits the status check"). On both layers, in the deployed order: the
calls of `execute` of `b` run from a state in which `b.hash` is `FullyExecuted` (`beforeCalls`
after the layer's proof write); every frame committed from a state where a hash is
`FullyExecuted` leaves it so; and from such a state every entry point called on a bundle with that
hash reverts, whichever of the three it is. -/
def Properties.ReentryForAnExecutingBundleRevertsAtV35 : Prop :=
  (∀ (ℓ : LayerAtV35) (b : Bundle) (s : State),
      (beforeCalls .deployed b (proofWriteAtV35 ℓ b.hash s)).bundle b.hash = .FullyExecuted) ∧
  (∀ (ℓ : LayerAtV35) (n : ℕ) (f : FrameAtV35 ℓ) (h : BundleHash) (s s' : State)
      (l : List Effect),
    s.bundle h = .FullyExecuted → execAtV35 ℓ .deployed n f s = some (s', l) →
    s'.bundle h = .FullyExecuted) ∧
  ∀ (ℓ : LayerAtV35) (n : ℕ) (e : EntryAtV35 ℓ) (cs : List (CalleeAtV35 ℓ)) (s : State),
    s.bundle e.bundle.hash = .FullyExecuted → execAtV35 ℓ .deployed n (.entry e cs) s = none

/-- **THE RESULTS ABOVE ARE ABOUT REAL NESTING.** On L2 from fresh storage, in `wNestedAtV35`,
call 0 of `wA` reaches a target that executes `wB` re-entrantly, then calls
`executeAtomicBundle(wA)` and catches the refusal: the transaction commits both bundles, each call
once, with `wB`'s effects nested inside `wA`'s first delivery. The refusal is the third part of
`ReentryForAnExecutingBundleRevertsAtV35`; the witness also shows its premise and conclusion at the
state `wA`'s writes leave: `wA` is `FullyExecuted` there, and `executeAtomicBundle(wA)` reverts
there. In `wNestedUncaughtAtV35` the target does not catch the refusal, and the whole transaction,
`wB`'s nested execution included, reverts. -/
def Properties.ReentrantExecutionWitnessAtV35 : Prop :=
  (submitAtV35 .l2 .deployed init wNestedAtV35).2 =
      [.delivered 1 0, .delivered 2 0, .executed 2, .delivered 1 1, .executed 1] ∧
    (submitAtV35 .l2 .deployed init wNestedAtV35).1.bundle 1 = .FullyExecuted ∧
    (submitAtV35 .l2 .deployed init wNestedAtV35).1.bundle 2 = .FullyExecuted ∧
    (beforeCalls .deployed wA (proofWriteAtV35 .l2 wA.hash init)).bundle wA.hash =
      .FullyExecuted ∧
    execAtV35 .l2 .deployed 5 (.entry (executeAtomicBundleAtV35 wA true) [])
      (beforeCalls .deployed wA (proofWriteAtV35 .l2 wA.hash init)) = none ∧
    (submitAtV35 .l2 .deployed init wNestedUncaughtAtV35).2 = [] ∧
    (submitAtV35 .l2 .deployed init wNestedUncaughtAtV35).1.bundle 1 = .Unreceived ∧
    (submitAtV35 .l2 .deployed init wNestedUncaughtAtV35).1.bundle 2 = .Unreceived

/-! ## (c) A failing call rolls the execution back -/

/-- **A TARGET THAT REVERTS FROM EVERY STATE REVERTS THE WHOLE EXECUTION, AT V35.** On both layers,
in every write order, at every budget and from every state: if the target of one of bundle `b`'s
first `b.calls` calls is `AlwaysRevertsAtV35`, then `execute` of `b` reverts, whatever the targets
before it did and committed in their own frames. -/
def Properties.AlwaysRevertingTargetRevertsTheExecutionAtV35 : Prop :=
  ∀ (ℓ : LayerAtV35) (v : Variant) (n : ℕ) (b : Bundle) (ok : Bool) (cs : List (CalleeAtV35 ℓ))
    (s : State),
    (∃ c ∈ cs.take b.calls, AlwaysRevertsAtV35 ℓ v c) →
    execAtV35 ℓ v n (.entry (.execute b ok) cs) s = none

/-- **A TARGET THAT REVERTS WHERE THE LOOP REACHES IT REVERTS THE WHOLE EXECUTION, AT V35.** On both
layers, in every write order: let `k < b.calls` be a call whose target `cs[k]` is given. If the call
loop over the first `k` calls, run from the state `execute`'s writes leave (`beforeCalls` after the
layer's proof write), commits to `t`, and `cs[k]` reverts from `t` at the budget the loop gives it,
then `execute` of `b` reverts. Nothing is assumed about how `cs[k]` behaves from any other
state. -/
def Properties.TargetRevertingWhereReachedRevertsTheExecutionAtV35 : Prop :=
  ∀ (ℓ : LayerAtV35) (v : Variant) (m : ℕ) (b : Bundle) (ok : Bool) (cs : List (CalleeAtV35 ℓ))
    (s : State) (k : ℕ) (hk : k < cs.length) (t : State) (l : List Effect), k < b.calls →
    execAtV35 ℓ v (m + 1 + k) (.calls b.hash (List.range k) (cs.take k))
        (beforeCalls v b (proofWriteAtV35 ℓ b.hash s)) = some (t, l) →
    execAtV35 ℓ v m (.target cs[k]) t = none →
    execAtV35 ℓ v (m + 2 + k) (.entry (.execute b ok) cs) s = none

/-- **SO A FAILED ATTEMPT CAN BE RETRIED, AT V35** (the claim at `InteropHandlerBase.sol:322-324`:
"any failing call reverts the whole flow, leaving no state changes"). On both layers, in the
deployed order: if bundle `b` is `Unreceived` and one of its first `b.calls` targets is
`AlwaysRevertsAtV35`, the transaction `execute(b)` with a passing verdict leaves the state exactly
as it was and commits nothing, including whatever that target and the targets before it committed
in their own frames. From that same state, a retry with a passing verdict whose targets return
delivers each of `b`'s calls once, in order, executes `b`, and leaves it `FullyExecuted` with its
calls `Executed`. On L1 the run exists only for a single-call bundle whose target is `L1_ASSET_ROUTER`: the model
omits `executeBundle`'s `calls.length == 1` check (`L1InteropHandler.sol:85`) and
`_interopCallTarget`'s target check (`L1InteropHandler.sol:189-192`), and on both layers the
permission and destination-context checks (`MODEL-HANDLER-REENTRY-V35`), all of which only
reject. -/
def Properties.FailedAttemptCanBeRetriedAtV35 : Prop :=
  ∀ (ℓ : LayerAtV35) (s : State) (b : Bundle) (fuel : ℕ) (cs : List (CalleeAtV35 ℓ)),
    s.bundle b.hash = .Unreceived → (∃ c ∈ cs.take b.calls, AlwaysRevertsAtV35 ℓ .deployed c) →
    submitAtV35 ℓ .deployed s ⟨fuel, .execute b true, cs⟩ = (s, []) ∧
    submitAtV35 ℓ .deployed s ⟨b.calls + 2, .execute b true, List.replicate b.calls .returns⟩ =
      ((s.setBundle b.hash .FullyExecuted).executeAll b.hash b.calls,
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash])

/-- **THE PREMISES FIRE ON TARGETS THAT ARE NOT THE LEAF `reverts`.** On L2, in the deployed
order:
* `wRevertsAfterWorkAtV35` (execute `wB` re-entrantly, then revert) is `AlwaysRevertsAtV35` in
  every order. It is call 0's target of `wAttemptAfterWorkAtV35`; from fresh storage, its
  re-entrant `executeAtomicBundle(wB)` commits on its own from the state where the target runs
  (with the budget the run gives it), yet the attempt commits nothing and leaves `wA` and `wB`
  `Unreceived`. The retry `wRetryAtV35` then executes `wA`, each call once.
* In `wLateReentryAtV35`, with `k = 1` and `m = 5`: the loop over call 0 (whose target executes
  `wB` re-entrantly) commits to some state `t` in which `wA` is `FullyExecuted`, and call 1's
  target, which calls `executeAtomicBundle(wA)` without catching a failure, reverts from `t`,
  although from fresh storage it commits. The transaction commits nothing, and `wB` stays
  `Unreceived`. -/
def Properties.RevertingTargetWitnessAtV35 : Prop :=
  (∀ v : Variant, AlwaysRevertsAtV35 .l2 v wRevertsAfterWorkAtV35) ∧
    (execAtV35 .l2 .deployed 5 (.entry (executeAtomicBundleAtV35 wB true) [])
      (beforeCalls .deployed wA (proofWriteAtV35 .l2 wA.hash init))).isSome = true ∧
    (submitAtV35 .l2 .deployed init wAttemptAfterWorkAtV35).2 = [] ∧
    (submitAtV35 .l2 .deployed init wAttemptAfterWorkAtV35).1.bundle 1 = .Unreceived ∧
    (submitAtV35 .l2 .deployed init wAttemptAfterWorkAtV35).1.bundle 2 = .Unreceived ∧
    (submitAllAtV35 .l2 .deployed init [wAttemptAfterWorkAtV35, wRetryAtV35]).2 =
      [.delivered 1 0, .delivered 1 1, .executed 1] ∧
    (∃ (t : State) (l : List Effect),
      execAtV35 .l2 .deployed (5 + 1 + 1)
          (.calls wA.hash (List.range 1) (wLateReentryAtV35.callees.take 1))
          (beforeCalls .deployed wA (proofWriteAtV35 .l2 wA.hash init)) = some (t, l) ∧
        t.bundle wA.hash = .FullyExecuted ∧
        execAtV35 .l2 .deployed 5 (.target (reenterAtV35 (executeAtomicBundleAtV35 wA true) false))
          t = none) ∧
    (execAtV35 .l2 .deployed 5 (.target (reenterAtV35 (executeAtomicBundleAtV35 wA true) false))
      init).isSome = true ∧
    (submitAtV35 .l2 .deployed init wLateReentryAtV35).2 = [] ∧
    (submitAtV35 .l2 .deployed init wLateReentryAtV35).1.bundle 2 = .Unreceived

/-- **A CAUGHT RE-ENTRANT REVERT IS UNDONE ALONE.** On L2, in the deployed order, from fresh
storage: in `wCaughtAtV35` the target of `wA`'s first call executes `wB` re-entrantly, `wB`'s only
call reverts, and the target catches the failure. `wA` commits, `wB`'s status write is undone, and
`wB` is executed later by `wRunBAtV35`. -/
def Properties.CaughtReentrantRevertWitnessAtV35 : Prop :=
  (submitAllAtV35 .l2 .deployed init [wCaughtAtV35]).2 =
      [.delivered 1 0, .delivered 1 1, .executed 1] ∧
    (submitAllAtV35 .l2 .deployed init [wCaughtAtV35]).1.bundle 1 = .FullyExecuted ∧
    (submitAllAtV35 .l2 .deployed init [wCaughtAtV35]).1.bundle 2 = .Unreceived ∧
    (submitAllAtV35 .l2 .deployed init [wCaughtAtV35, wRunBAtV35]).2 =
      [.delivered 1 0, .delivered 1 1, .executed 1, .delivered 2 0, .executed 2]

/-! ## (d) What changed at v35: the gate -/

/-- **A `Verified` BUNDLE EXECUTES WITHOUT ITS PROOF CHECK.** On both layers, in the deployed order,
for every bundle `b` and every state in which it is `Verified`: `verify` of `b` commits nothing,
whatever its verdict, fuel and targets (`IHB:313`); and `execute` of `b` with a failing verdict,
whose targets return, delivers each of `b`'s calls once, in order, and completes `b`. On L2 that is
`executeAtomicBundle` skipping `requireFlowFinalized` (`L2InteropHandler.sol:73-75`), new at v35:
at the pin `executeAtomicBundle` refused a `Verified` bundle. On L1 the run exists only for a single-call bundle whose target is `L1_ASSET_ROUTER`: the model
omits `executeBundle`'s `calls.length == 1` check (`L1InteropHandler.sol:85`) and
`_interopCallTarget`'s target check (`L1InteropHandler.sol:189-192`), and on both layers the
permission and destination-context checks (`MODEL-HANDLER-REENTRY-V35`), all of which only
reject. -/
def Properties.VerifiedBundleExecutesWithoutTheGateAtV35 : Prop :=
  ∀ (ℓ : LayerAtV35) (s : State) (b : Bundle), s.bundle b.hash = .Verified →
    (∀ (fuel : ℕ) (ok : Bool) (cs : List (CalleeAtV35 ℓ)),
        submitAtV35 ℓ .deployed s ⟨fuel, .verify b ok, cs⟩ = (s, [])) ∧
    submitAtV35 ℓ .deployed s ⟨b.calls + 2, .execute b false, List.replicate b.calls .returns⟩ =
      ((s.setBundle b.hash .FullyExecuted).executeAll b.hash b.calls,
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash])

/-- **NO PASSING VERDICT, NO DELIVERY.** On both layers, in the deployed order, from every state in
which bundle hash `h` is `Unreceived` (fresh storage among them), along every sequence of
transactions none of whose entry-point calls (its own or any a target makes, at any depth) names
`h` with a passing verdict: `h` ends `Unreceived`, and no committed effect belongs to `h`. None of
its calls is delivered and it never completes.

On L2 the verdict is `requireFlowFinalized`'s, consulted by `verifyAtomicBundle` and by
`executeAtomicBundle` of an `Unreceived` bundle. So every route that delivers a call of an L2
bundle from such a state (atomic execution; verification then execution; verification then
unbundling) has the flow gate accept a proof for it in some entry-point call of the run, possibly
one in a frame that later reverted. Unlike the History record `NeverPublishedBundleNeedsTheFlowGate` (pin `c67894b9`), this
needs no premise about inclusion proofs: L2 has no entry point that consults one at v35. -/
def Properties.DeliveryNeedsTheGateAtV35 : Prop :=
  ∀ (ℓ : LayerAtV35) (s : State) (h : BundleHash) (txs : List (TxAtV35 ℓ)),
    s.bundle h = .Unreceived →
    (∀ t ∈ txs, TxAllAtV35 (fun e => ¬ PassesGateAtV35 h e) t) →
      (submitAllAtV35 ℓ .deployed s txs).1.bundle h = .Unreceived ∧
        ∀ e ∈ (submitAllAtV35 ℓ .deployed s txs).2, e.bundleHash ≠ h

/-- **THE L2 ROUTES, ON A WITNESS.** On L2, in the deployed order, from fresh storage, for bundle
`wA` (hash 1, two calls):
* `executeAtomicBundle` with a passing gate delivers both calls and completes `wA`;
* `verifyAtomicBundle` with a passing gate, then `executeAtomicBundle` with a failing gate, does
  the same: the gate is skipped for a `Verified` bundle;
* `verifyAtomicBundle`, then `unbundleBundle` executing call 0 and cancelling call 1, delivers
  call 0 only and leaves `wA` `Unbundled`, call 0 `Executed` and call 1 `Cancelled`; after that,
  `executeAtomicBundle` commits nothing, with a failing gate or a passing one. So an atomic bundle
  can end partly executed (`protocol-docs/interop.md:256`).
* The premise of `DeliveryNeedsTheGateAtV35` holds for hash 1 on `[wExecANoGateAtV35, wRunBAtV35]`:
  the attempt on `wA` carries a failing gate, and the run commits `wB`'s execution. -/
def Properties.GateRoutesWitnessAtV35 : Prop :=
  (submitAllAtV35 .l2 .deployed init [wRetryAtV35]).2 =
      [.delivered 1 0, .delivered 1 1, .executed 1] ∧
    (submitAllAtV35 .l2 .deployed init [wVerifyAAtV35, wExecANoGateAtV35]).2 =
      [.delivered 1 0, .delivered 1 1, .executed 1] ∧
    (submitAllAtV35 .l2 .deployed init [wVerifyAAtV35, wUnbundleExecCancelAtV35]).2 =
      [.delivered 1 0] ∧
    (submitAllAtV35 .l2 .deployed init [wVerifyAAtV35, wUnbundleExecCancelAtV35]).1.bundle 1 =
      .Unbundled ∧
    (submitAllAtV35 .l2 .deployed init [wVerifyAAtV35, wUnbundleExecCancelAtV35]).1.call 1 0 =
      .Executed ∧
    (submitAllAtV35 .l2 .deployed init [wVerifyAAtV35, wUnbundleExecCancelAtV35]).1.call 1 1 =
      .Cancelled ∧
    (submitAllAtV35 .l2 .deployed init
        [wVerifyAAtV35, wUnbundleExecCancelAtV35, wExecANoGateAtV35, wRetryAtV35]).2 =
      [.delivered 1 0] ∧
    (∀ t ∈ [wExecANoGateAtV35, wRunBAtV35], TxAllAtV35 (fun e => ¬ PassesGateAtV35 1 e) t) ∧
    (submitAllAtV35 .l2 .deployed init [wExecANoGateAtV35, wRunBAtV35]).2 =
      [.delivered 2 0, .executed 2]

/-- **THE RECEIVE FILTER DECIDES AT THE GATE ONLY** (`protocol-docs/interop-gating.md:195-197`).
For chain `self`, a whitelist `p` and the source chains `legs` of a flow's legs, all allowed under
`p` (`_checkLegSourceAllowed` passes for each), and a peer `c` among them other than `self`:
* after `deregisterChainForInterop(c)`, `requireFlowFinalized`'s verdict is `false`, whatever the
  other checks say; after allowing `c` again it is `true` when the other checks pass;
* on L2, in the deployed order, from every state in which bundle `b` is `Unreceived`: while `c` is
  removed, `executeAtomicBundle(b)` and `verifyAtomicBundle(b)` commit nothing, whatever the fuel
  and targets; once `c` is allowed again, `executeAtomicBundle(b)` whose targets return delivers
  each call and completes `b`; and if `b` was verified while `c` was allowed, it executes after the
  removal, every target returning, delivering each call and completing `b`.
Here the verdict is `gateVerdictAtV35`, the model's reading of `requireFlowFinalized`
(`AtomicFlowManager.sol:176-213`), with the other checks a single input bit. This is a model-level
illustration: that the filter is read only at the gate (`unbundleBundle` and the `Verified` path
never call `requireFlowFinalized`) is established by the call-site inventory in the Specs header,
not by this statement. -/
def Properties.ReceiveFilterIsReadAtTheGateAtV35 : Prop :=
  ∀ (self : ℕ) (p : ℕ → Bool) (legs : List ℕ) (c : ℕ),
    legs.all (legSourceAllowedAtV35 self p) = true → c ∈ legs → c ≠ self →
    (∀ proofsOk : Bool, gateVerdictAtV35 self (deregisterAtV35 p c) legs proofsOk = false) ∧
    gateVerdictAtV35 self (allowAtV35 (deregisterAtV35 p c) c) legs true = true ∧
    ∀ (s : State) (b : Bundle), s.bundle b.hash = .Unreceived →
      (∀ (fuel : ℕ) (proofsOk : Bool) (cs : List (CalleeAtV35 .l2)),
        submitAtV35 .l2 .deployed s ⟨fuel, executeAtomicBundleAtV35 b
            (gateVerdictAtV35 self (deregisterAtV35 p c) legs proofsOk), cs⟩ = (s, []) ∧
        submitAtV35 .l2 .deployed s ⟨fuel, verifyAtomicBundleAtV35 b
            (gateVerdictAtV35 self (deregisterAtV35 p c) legs proofsOk), cs⟩ = (s, [])) ∧
      (submitAtV35 .l2 .deployed s (runAtomicAtV35 b
          (gateVerdictAtV35 self (allowAtV35 (deregisterAtV35 p c) c) legs true))).2 =
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash] ∧
      (submitAllAtV35 .l2 .deployed s
          [verifyAtomicTxAtV35 b (gateVerdictAtV35 self p legs true),
            runAtomicAtV35 b (gateVerdictAtV35 self (deregisterAtV35 p c) legs true)]).2 =
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash]

/-- **THE FILTER'S PREMISES, ON A WITNESS.** Chain `10` receives a flow with legs from itself and
from peer `20`, which its whitelist allows: every premise of `ReceiveFilterIsReadAtTheGateAtV35`
holds with `c = 20`. From fresh storage on L2, `wA` verified before `20` is removed then executes
after it, committing both calls and `wA`'s completion; `wA` not verified first commits nothing
after the removal. -/
def Properties.ReceiveFilterWitnessAtV35 : Prop :=
  wFilterLegsAtV35.all (legSourceAllowedAtV35 wFilterSelfAtV35 wFilterPeersAtV35) = true ∧
    20 ∈ wFilterLegsAtV35 ∧ (20 : ℕ) ≠ wFilterSelfAtV35 ∧
    (submitAllAtV35 .l2 .deployed init
        [verifyAtomicTxAtV35 wA
            (gateVerdictAtV35 wFilterSelfAtV35 wFilterPeersAtV35 wFilterLegsAtV35 true),
          runAtomicAtV35 wA (gateVerdictAtV35 wFilterSelfAtV35
            (deregisterAtV35 wFilterPeersAtV35 20) wFilterLegsAtV35 true)]).2 =
      [.delivered 1 0, .delivered 1 1, .executed 1] ∧
    (submitAtV35 .l2 .deployed init (runAtomicAtV35 wA (gateVerdictAtV35 wFilterSelfAtV35
        (deregisterAtV35 wFilterPeersAtV35 20) wFilterLegsAtV35 true))).2 = []

/-! ## (e) The order of the writes is load-bearing -/

/-- **WITH THE STATUS WRITE AFTER THE CALLS, RE-ENTRY RUNS A BUNDLE TWICE, AT V35.** From fresh
storage, in the order `statusWriteAfterCalls`:
* on L2, `executeAtomicBundle(wC)` with a passing gate whose target re-enters it with a passing
  gate commits `wC`'s call twice and completes `wC` twice; with a failing gate on the re-entry it
  commits nothing (the bundle is still `Unreceived`, so the gate is consulted);
* on L2, after `verifyAtomicBundle(wC)`, `executeAtomicBundle(wC)` with a failing gate whose target
  re-enters it with a failing gate commits `wC` twice (the bundle is still `Verified`, so neither
  call consults the gate);
* on L1, `executeBundle(wC)` with a valid proof whose target re-enters it with no valid proof
  commits `wC` twice (`_verifyBundle` already wrote `Verified`).
In the deployed order the three runs that commit twice above commit nothing, and with the failure
caught the first one commits one execution. -/
def Properties.StatusWriteAfterCallsRunsTwiceAtV35 : Prop :=
  (submitAtV35 .l2 .statusWriteAfterCalls init (wReenterAtomicAtV35 true false)).2 =
      [.delivered 3 0, .delivered 3 0, .executed 3, .executed 3] ∧
    (submitAtV35 .l2 .statusWriteAfterCalls init (wReenterAtomicAtV35 false false)).2 = [] ∧
    (submitAllAtV35 .l2 .statusWriteAfterCalls init [wVerifyCAtV35, wReenterVerifiedAtV35]).2 =
      [.delivered 3 0, .delivered 3 0, .executed 3, .executed 3] ∧
    (submitAtV35 .l1 .statusWriteAfterCalls init wReenterL1AtV35).2 =
      [.delivered 3 0, .delivered 3 0, .executed 3, .executed 3] ∧
    (submitAtV35 .l2 .deployed init (wReenterAtomicAtV35 true false)).2 = [] ∧
    (submitAllAtV35 .l2 .deployed init [wVerifyCAtV35, wReenterVerifiedAtV35]).2 = [] ∧
    (submitAtV35 .l1 .deployed init wReenterL1AtV35).2 = [] ∧
    (submitAtV35 .l2 .deployed init (wReenterAtomicAtV35 true true)).2 =
      [.delivered 3 0, .executed 3]

/-- **WITH THE CALL WRITE AFTER THE CALLS, RE-ENTRY RUNS AN UNBUNDLED CALL TWICE, AT V35.** On L2
from fresh storage, after `verifyAtomicBundle(wC)`, in the order `callWriteAfterCalls`:
`unbundleBundle` of `wC` requesting its call, whose target makes the same request again, delivers
the call twice in one committed transaction. In the deployed order that transaction commits
nothing, and with the failure caught it commits the call once. -/
def Properties.CallWriteAfterCallsRunsTwiceAtV35 : Prop :=
  (submitAllAtV35 .l2 .callWriteAfterCalls init [wVerifyCAtV35, wReenterUnbundleAtV35 false]).2 =
      [.delivered 3 0, .delivered 3 0] ∧
    (submitAllAtV35 .l2 .deployed init [wVerifyCAtV35, wReenterUnbundleAtV35 false]).2 = [] ∧
    (submitAllAtV35 .l2 .deployed init [wVerifyCAtV35, wReenterUnbundleAtV35 true]).2 =
      [.delivered 3 0]

/-- **IN THAT ORDER, EVERY BUNDLE CAN BE RUN TWICE, AT V35.** On both layers, for every bundle `b`
with at least one call and every state where `execute(b)` with a passing verdict is admitted (`b`
is `Unreceived` or `Verified`): in the order `statusWriteAfterCalls`, `execute(b)` with a passing
verdict whose first call's target re-enters `execute(b)` with a passing verdict, not catching a
failure, commits a log with a repeated effect. On L2, when `b` was `Unreceived`, the re-entry's
verdict is consulted; the statement takes it passing, as the same check on the same proof would
be. In the deployed order the same transaction commits nothing. -/
def Properties.StatusWriteAfterCallsRunsAnyBundleTwiceAtV35 : Prop :=
  ∀ (ℓ : LayerAtV35) (s : State) (b : Bundle), 0 < b.calls →
    (s.bundle b.hash = .Unreceived ∨ s.bundle b.hash = .Verified) →
    ¬ (submitAtV35 ℓ .statusWriteAfterCalls s ⟨b.calls + 5, .execute b true,
        [reenterAtV35 (.execute b true) false]⟩).2.Nodup ∧
    submitAtV35 ℓ .deployed s ⟨b.calls + 5, .execute b true,
        [reenterAtV35 (.execute b true) false]⟩ = (s, [])

/-- **IN THAT ORDER, EVERY UNBUNDLED CALL CAN BE RUN TWICE, AT V35.** On both layers, for every
bundle `b` with at least one call and every state where `unbundleBundle(b)` is admitted (`b` is
`Verified` or `Unbundled`) and call 0 is `Unprocessed`, in the order `callWriteAfterCalls`:
`unbundleBundle(b)` requesting call 0 only, whose target makes the same request again, commits call
0's delivery twice. In the deployed order the same transaction commits nothing. -/
def Properties.CallWriteAfterCallsRunsAnyCallTwiceAtV35 : Prop :=
  ∀ (ℓ : LayerAtV35) (s : State) (b : Bundle), 0 < b.calls →
    (s.bundle b.hash = .Verified ∨ s.bundle b.hash = .Unbundled) →
    s.call b.hash 0 = .Unprocessed →
    (submitAtV35 ℓ .callWriteAfterCalls s ⟨6, .unbundleBundle b (requestFirst b.calls),
        [reenterAtV35 (.unbundleBundle b (requestFirst b.calls)) false]⟩).2 =
      [.delivered b.hash 0, .delivered b.hash 0] ∧
    submitAtV35 ℓ .deployed s ⟨6, .unbundleBundle b (requestFirst b.calls),
        [reenterAtV35 (.unbundleBundle b (requestFirst b.calls)) false]⟩ = (s, [])

end Contracts.InteropHandlerAtV35
