import EraSpec.Contracts.InteropHandlerBase.Specs.Reentrancy

/-!
# Properties: re-entrant execution cannot run a bundle or a call twice

Statements about `EraSpec.Contracts.InteropHandlerBase.Specs.Reentrancy`. Proofs are in
`EraSpec.Contracts.InteropHandlerBase.Proofs.Reentrancy`.

Every result below quantifies over every target behaviour (`Callee` trees, so re-entrant
calls to any entry point at any depth, caught or not) and every budget. None takes a hash
premise: the handler keys its state by the bundle hash, and so do the statements.

## (a) Nothing runs twice, in the deployed order

* **No effect is committed twice** (`NoEffectCommittedTwice`, the headline). In the
  committed log of any sequence of transactions, from any state, no call is delivered twice
  and no bundle hash completes a whole-bundle execution twice. Each logged effect was not yet
  spent when the sequence started, and is spent at its end (`CommittedEffectsWereOpen`).
* **A whole-bundle execution runs each of its calls once.** Of the effects a successful
  `executeAtomicBundle` or `executeBundle` commits, those of its own bundle are exactly its
  calls `0, …, n-1`, in order, then its `BundleExecuted`. Whatever its targets did
  re-entrantly concerns other bundles only (`WholeBundleExecutionRunsEachCallOnce`).
* **The replay state is the committed history.** From fresh storage, a call is recorded
  `Executed` exactly when the log delivered it, and a bundle is `FullyExecuted` exactly when
  the log executed it (`StatusRecordsExactlyTheCommittedEffects`).
* **Nested execution follows `BundleStatusMachine`.** Every bundle status moves along
  `Reach`, and from a state where only closed bundles have processed calls (fresh storage is
  one), every call status moves along `CallReach` (`NestedExecutionFollowsTheStatusMachine`).
  So `routes_exclusive` and the terminality results of that file apply across re-entrant
  frames too.
* **The source's own argument** (`ReentryForAnExecutingBundleReverts`, for
  `L2InteropHandler.sol:45-46`): a whole-bundle execution's calls run with its bundle
  `FullyExecuted`, nothing committed undoes that, and every entry point refuses such a
  bundle.
* `ReentrantExecutionWitness`: a target that executes another bundle re-entrantly commits
  it, and its attempt to re-execute the outer bundle is refused.

## (b) A failing call rolls the execution back

* **A reverting target reverts the whole execution** (`RevertingCallRevertsTheExecution`):
  for every order, whatever the earlier targets committed — for a target that is the leaf
  `Callee.reverts`. The premise is syntactic: a target that reverts after nested work, or whose
  uncaught re-entrant call fails, is not covered here. Topic `ReentrancyStrong` covers them
  (`AlwaysRevertingTargetRevertsTheExecution`, `TargetRevertingWhereReachedRevertsTheExecution`).
* **So a failed attempt can be retried** (`FailedAttemptCanBeRetried`): it leaves the state
  exactly as it was, so the bundle is still `Unreceived`, and a retry whose targets return
  delivers each call once and executes the bundle. This is `VM-REVERT` as modelled
  (`Specs`, "A revert is `none`"). Same leaf premise; the semantic form is
  `ReentrancyStrong.FailedAttemptWithAlwaysRevertingTargetCanBeRetried`.
* `FailedAttemptRetryWitness`: the failed attempt had executed another bundle re-entrantly;
  that is undone too. `CaughtReentrantRevertWitness`: a re-entrant execution that reverts
  inside a committed transaction is undone alone, and its bundle stays executable.

## (c) The order of the writes is what does it (countermodels)

* **Status write after the calls** (`StatusWriteAfterCallsRunsTwice`): with
  `bundleStatus = FullyExecuted` moved after `_executeCalls`, a target that re-enters the
  same bundle runs its call twice and completes it twice, on both the atomic and the public
  route; the public re-entry needs no inclusion proof, because the outer call's
  `_verifyBundle` already wrote `Verified`. The deployed order reverts the same transaction,
  or commits one execution when the target catches the failure.
* **Call write after the calls** (`CallWriteAfterCallsRunsTwice`): with `unbundleBundle`'s
  `callStatus = Executed` moved after `_executeCalls`, a target that re-enters with the same
  request runs the call twice. The unbundled route admits re-entry by design (`Unbundled →
  Unbundled`), so there the per-call write is the only guard.
* Both hold in general, not only on the witness bundle: for every bundle with a call and
  every state in which the entry point admits it (`StatusWriteAfterCallsRunsAnyBundleTwice`,
  `CallWriteAfterCallsRunsAnyCallTwice`), and the deployed order commits nothing on the same
  transactions.
-/

namespace Contracts.InteropHandler

open AttackVectors.BundleStatusMachine (Status CallStatus Reach CallReach)

/-! ## (a) Nothing runs twice -/

/-- **NO EFFECT IS COMMITTED TWICE.** For every state and every sequence of transactions, with
every behaviour of every target at every depth: the committed log has no repeated entry. No
call `i` of a bundle hash `h` is delivered twice, whether by the whole-bundle routes, the
unbundled route or both, in one transaction or several; and no bundle hash completes
`executeBundle` or `executeAtomicBundle` twice. -/
def Properties.NoEffectCommittedTwice : Prop :=
  ∀ (s : State) (txs : List Tx), (submitAll .deployed s txs).2.Nodup

/-- **EACH COMMITTED EFFECT WAS OPEN, AND IS CLOSED.** Every effect in the committed log of a
sequence of transactions was not spent in the state the sequence started from, and is spent in
the state it ends in. -/
def Properties.CommittedEffectsWereOpen : Prop :=
  ∀ (s : State) (txs : List Tx) (e : Effect), e ∈ (submitAll .deployed s txs).2 →
    ¬ Spent s e ∧ Spent (submitAll .deployed s txs).1 e

/-- **A WHOLE-BUNDLE EXECUTION RUNS EACH OF ITS CALLS ONCE.** If `executeAtomicBundle` or
`executeBundle` of bundle `b` succeeds, from any state and with any targets, then the
effects of `b.hash` in its committed log are exactly the deliveries of calls `0, …, n-1`, in
order, then `BundleExecuted`; and `b.hash` ends `FullyExecuted`. Everything the targets did
re-entrantly, including any further attempt on `b`, contributes no effect of `b.hash`. -/
def Properties.WholeBundleExecutionRunsEachCallOnce : Prop :=
  ∀ (n : ℕ) (b : Bundle) (ok : Bool) (cs : List Callee) (s s' : State) (l : List Effect),
    (exec .deployed n (.entry (.executeAtomicBundle b ok) cs) s = some (s', l) ∨
      exec .deployed n (.entry (.executeBundle b ok) cs) s = some (s', l)) →
    l.filter (fun e => e.bundleHash = b.hash) =
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash] ∧
      s'.bundle b.hash = .FullyExecuted

/-- **THE REPLAY STATE IS THE COMMITTED HISTORY.** After any sequence of transactions from
fresh storage, call `i` of bundle hash `h` is recorded `Executed` if and only if the committed
log delivered it, and `h` is `FullyExecuted` if and only if the log executed it. -/
def Properties.StatusRecordsExactlyTheCommittedEffects : Prop :=
  ∀ (txs : List Tx) (h : BundleHash) (i : ℕ),
    ((submitAll .deployed init txs).1.call h i = .Executed ↔
        Effect.delivered h i ∈ (submitAll .deployed init txs).2) ∧
    ((submitAll .deployed init txs).1.bundle h = .FullyExecuted ↔
        Effect.executed h ∈ (submitAll .deployed init txs).2)

/-- **NESTED EXECUTION FOLLOWS THE STATUS MACHINE.** Fresh storage satisfies `CallsClosed`
(only bundles that left both entry states have processed calls). From any state satisfying
it, along any sequence of transactions: it holds at the end, every bundle status moved along
`BundleStatusMachine.Reach`, and every call status along `BundleStatusMachine.CallReach`. -/
def Properties.NestedExecutionFollowsTheStatusMachine : Prop :=
  CallsClosed init ∧
  ∀ (s : State) (txs : List Tx), CallsClosed s →
    CallsClosed (submitAll .deployed s txs).1 ∧
    (∀ h, Reach (s.bundle h) ((submitAll .deployed s txs).1.bundle h)) ∧
    ∀ h i, CallReach (s.call h i) ((submitAll .deployed s txs).1.call h i)

/-- **A RE-ENTRANT CALL FOR AN EXECUTING BUNDLE HITS THE STATUS CHECK** (the claim at
`L2InteropHandler.sol:45-46`). In the deployed order: the calls of a whole-bundle execution of
`b` run from a state in which `b.hash` is `FullyExecuted`; everything committed from such a
state keeps it so; and from such a state every entry point called on a bundle with that hash
reverts, whichever of the four it is. -/
def Properties.ReentryForAnExecutingBundleReverts : Prop :=
  (∀ (b : Bundle) (s : State), (beforeCalls .deployed b s).bundle b.hash = .FullyExecuted) ∧
  (∀ (n : ℕ) (f : Frame) (h : BundleHash) (s s' : State) (l : List Effect),
    s.bundle h = .FullyExecuted → exec .deployed n f s = some (s', l) →
    s'.bundle h = .FullyExecuted) ∧
  ∀ (n : ℕ) (e : Entry) (cs : List Callee) (s : State),
    s.bundle e.bundle.hash = .FullyExecuted → exec .deployed n (.entry e cs) s = none

/-- **THE RESULTS ABOVE ARE ABOUT REAL NESTING.** From fresh storage, in `wNested`, call 0 of
`wA` reaches a target that executes `wB` re-entrantly, then tries `wA` again and catches the
refusal: the transaction commits both bundles, each call once, with `wB`'s effects nested
inside `wA`'s first delivery. In `wNestedUncaught` the target does not catch the refusal, and
the whole transaction, including `wB`'s nested execution, reverts. -/
def Properties.ReentrantExecutionWitness : Prop :=
  (submit .deployed init wNested).2 =
      [.delivered 1 0, .delivered 2 0, .executed 2, .delivered 1 1, .executed 1] ∧
    (submit .deployed init wNested).1.bundle 1 = .FullyExecuted ∧
    (submit .deployed init wNested).1.bundle 2 = .FullyExecuted ∧
    (submit .deployed init wNestedUncaught).2 = [] ∧
    (submit .deployed init wNestedUncaught).1.bundle 1 = .Unreceived ∧
    (submit .deployed init wNestedUncaught).1.bundle 2 = .Unreceived

/-! ## (b) A failing call rolls the execution back -/

/-- **A REVERTING TARGET REVERTS THE WHOLE EXECUTION.** In every order, if the target of one of
bundle `b`'s calls is the leaf `Callee.reverts`, then `executeAtomicBundle` and `executeBundle` of
`b` revert, whatever the targets before it did and committed in their own frames. The premise is
syntactic, on the top-level callee list: a target that does nested work and then reverts, or whose
uncaught re-entrant call fails, does not satisfy it although it reverts the execution. Those are
`ReentrancyStrong.AlwaysRevertingTargetRevertsTheExecution` (a target that reverts from every state)
and `TargetRevertingWhereReachedRevertsTheExecution` (one that reverts where the loop reaches
it). -/
def Properties.RevertingCallRevertsTheExecution : Prop :=
  ∀ (v : Variant) (n : ℕ) (b : Bundle) (ok : Bool) (cs : List Callee) (s : State),
    Callee.reverts ∈ cs.take b.calls →
    exec v n (.entry (.executeAtomicBundle b ok) cs) s = none ∧
      exec v n (.entry (.executeBundle b ok) cs) s = none

/-- **SO A FAILED ATTEMPT CAN BE RETRIED.** If bundle `b` is `Unreceived` and one of its calls'
targets is the leaf `Callee.reverts` (for every target that reverts from every state, see
`ReentrancyStrong.FailedAttemptWithAlwaysRevertingTargetCanBeRetried`), the transaction
`executeAtomicBundle(b)` leaves the state exactly as it was
and commits nothing: the status write before the calls is undone, so `b` is still
`Unreceived`. From that same state, a retry whose targets return delivers each of `b`'s calls
once, in order, executes `b`, and leaves it `FullyExecuted` with its calls `Executed`. -/
def Properties.FailedAttemptCanBeRetried : Prop :=
  ∀ (s : State) (b : Bundle) (fuel : ℕ) (cs : List Callee),
    s.bundle b.hash = .Unreceived → Callee.reverts ∈ cs.take b.calls →
    submit .deployed s ⟨fuel, .executeAtomicBundle b true, cs⟩ = (s, []) ∧
    submit .deployed s
        ⟨b.calls + 2, .executeAtomicBundle b true, List.replicate b.calls .returns⟩ =
      ((s.setBundle b.hash .FullyExecuted).executeAll b.hash b.calls,
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash])

/-- **`FailedAttemptCanBeRetried` IS NOT VACUOUS, AND THE ROLLBACK REACHES NESTED WORK.** From
fresh storage, `wAttempt` reverts at `wA`'s second call. Its first call's target had executed
`wB` re-entrantly: with the second target returning instead (`wAttemptOk`) that commits. After
the failed attempt both bundles are still `Unreceived`, and the retry `wRetry` executes `wA`,
each call once. -/
def Properties.FailedAttemptRetryWitness : Prop :=
  (exec .deployed wAttempt.fuel (.entry wAttempt.entry wAttempt.callees) init).isNone = true ∧
    (submit .deployed init wAttemptOk).2 =
      [.delivered 1 0, .delivered 2 0, .executed 2, .delivered 1 1, .executed 1] ∧
    (submitAll .deployed init [wAttempt]).2 = [] ∧
    (submitAll .deployed init [wAttempt]).1.bundle 1 = .Unreceived ∧
    (submitAll .deployed init [wAttempt]).1.bundle 2 = .Unreceived ∧
    (submitAll .deployed init [wAttempt, wRetry]).2 =
      [.delivered 1 0, .delivered 1 1, .executed 1] ∧
    (submitAll .deployed init [wAttempt, wRetry]).1.bundle 1 = .FullyExecuted

/-- **A CAUGHT RE-ENTRANT REVERT IS UNDONE ALONE.** From fresh storage, in `wCaught` the target
of `wA`'s first call executes `wB`, whose only call reverts; the target catches the failure.
`wA` commits, `wB`'s status write is undone, and `wB` is executed later by `wRunB`. -/
def Properties.CaughtReentrantRevertWitness : Prop :=
  (submitAll .deployed init [wCaught]).2 = [.delivered 1 0, .delivered 1 1, .executed 1] ∧
    (submitAll .deployed init [wCaught]).1.bundle 1 = .FullyExecuted ∧
    (submitAll .deployed init [wCaught]).1.bundle 2 = .Unreceived ∧
    (submitAll .deployed init [wCaught, wRunB]).2 =
      [.delivered 1 0, .delivered 1 1, .executed 1, .delivered 2 0, .executed 2]

/-! ## (c) The order of the writes is load-bearing -/

/-- **WITH THE STATUS WRITE AFTER THE CALLS, RE-ENTRY RUNS A BUNDLE TWICE.** From fresh storage,
in the order `statusWriteAfterCalls`: atomic execution of `wC` whose target re-enters it
delivers `wC`'s call twice and completes `wC` twice, in one committed transaction; so does
`executeBundle` with a valid proof whose target re-enters it with no valid proof (the outer
`_verifyBundle` already wrote `Verified`). In the deployed order the same transactions revert,
and with the failure caught the atomic one commits one execution. -/
def Properties.StatusWriteAfterCallsRunsTwice : Prop :=
  (submit .statusWriteAfterCalls init (wReenterAtomic false)).2 =
      [.delivered 3 0, .delivered 3 0, .executed 3, .executed 3] ∧
    (submit .statusWriteAfterCalls init (wReenterAtomic false)).1.bundle 3 = .FullyExecuted ∧
    (submit .statusWriteAfterCalls init wReenterPublic).2 =
      [.delivered 3 0, .delivered 3 0, .executed 3, .executed 3] ∧
    (submit .deployed init (wReenterAtomic false)).2 = [] ∧
    (submit .deployed init wReenterPublic).2 = [] ∧
    (submit .deployed init (wReenterAtomic true)).2 = [.delivered 3 0, .executed 3]

/-- **WITH THE CALL WRITE AFTER THE CALLS, RE-ENTRY RUNS AN UNBUNDLED CALL TWICE.** From fresh
storage, after `wVerifyC`, in the order `callWriteAfterCalls`: `unbundleBundle` of `wC`
requesting its call, whose target makes the same request again, delivers the call twice in
one committed transaction. In the deployed order that transaction reverts, and with the
failure caught it commits the call once. -/
def Properties.CallWriteAfterCallsRunsTwice : Prop :=
  (submitAll .callWriteAfterCalls init [wVerifyC, wReenterUnbundle false]).2 =
      [.delivered 3 0, .delivered 3 0] ∧
    (submitAll .deployed init [wVerifyC, wReenterUnbundle false]).2 = [] ∧
    (submitAll .deployed init [wVerifyC, wReenterUnbundle true]).2 = [.delivered 3 0]

/-- **IN THAT ORDER, EVERY BUNDLE CAN BE RUN TWICE.** For every bundle `b` with at least one
call, in the order `statusWriteAfterCalls`:
* from every state where `b` is `Unreceived`, `executeAtomicBundle(b)` whose first call's
  target re-enters `executeAtomicBundle(b)` commits a log with a repeated effect;
* from every state where `executeBundle(b)` with a valid proof is admitted (`b` is
  `Unreceived` or `Verified`), `executeBundle(b)` whose first call's target re-enters
  `executeBundle(b)` with no valid proof does too.
In the deployed order, from every state where `b` is `Unreceived`, the atomic transaction
commits nothing. -/
def Properties.StatusWriteAfterCallsRunsAnyBundleTwice : Prop :=
  ∀ (s : State) (b : Bundle), 0 < b.calls →
    (s.bundle b.hash = .Unreceived →
      ¬ (submit .statusWriteAfterCalls s ⟨b.calls + 5, .executeAtomicBundle b true,
          [reenter (.executeAtomicBundle b true) false]⟩).2.Nodup ∧
      submit .deployed s ⟨b.calls + 5, .executeAtomicBundle b true,
          [reenter (.executeAtomicBundle b true) false]⟩ = (s, [])) ∧
    (s.bundle b.hash = .Unreceived ∨ s.bundle b.hash = .Verified →
      ¬ (submit .statusWriteAfterCalls s ⟨b.calls + 5, .executeBundle b true,
          [reenter (.executeBundle b false) false]⟩).2.Nodup)

/-- **IN THAT ORDER, EVERY UNBUNDLED CALL CAN BE RUN TWICE.** For every bundle `b` with at least
one call and every state where `unbundleBundle(b)` is admitted (`b` is `Verified` or
`Unbundled`) and call 0 is `Unprocessed`, in the order `callWriteAfterCalls`:
`unbundleBundle(b)` requesting call 0 only, whose target makes the same request again, commits
call 0's delivery twice. In the deployed order the same transaction commits nothing. -/
def Properties.CallWriteAfterCallsRunsAnyCallTwice : Prop :=
  ∀ (s : State) (b : Bundle), 0 < b.calls →
    (s.bundle b.hash = .Verified ∨ s.bundle b.hash = .Unbundled) →
    s.call b.hash 0 = .Unprocessed →
    (submit .callWriteAfterCalls s ⟨6, .unbundleBundle b (requestFirst b.calls),
        [reenter (.unbundleBundle b (requestFirst b.calls)) false]⟩).2 =
      [.delivered b.hash 0, .delivered b.hash 0] ∧
    submit .deployed s ⟨6, .unbundleBundle b (requestFirst b.calls),
        [reenter (.unbundleBundle b (requestFirst b.calls)) false]⟩ = (s, [])

end Contracts.InteropHandler
