import EraSpec.Contracts.InteropHandlerBase.Specs.ReentrancyStrong

/-!
# Properties: a target that reverts — not only the leaf `reverts` — rolls the execution back

Statements about `EraSpec.Contracts.InteropHandlerBase.Specs.ReentrancyStrong`. Proofs are in
`EraSpec.Contracts.InteropHandlerBase.Proofs.ReentrancyStrong`.

These strengthen `Properties.RevertingCallRevertsTheExecution` and
`Properties.FailedAttemptCanBeRetried` (topic `Reentrancy`), whose premise
`Callee.reverts ∈ cs.take b.calls` only recognises the leaf `Callee.reverts`:

* **A target that reverts from every state** (`AlwaysRevertingTargetRevertsTheExecution`):
  if any of the first `b.calls` targets is `AlwaysReverts`, both whole-bundle entry points
  revert, in every write order, at every budget, from every state. The leaf premise is the
  special case `c = Callee.reverts`.
* **A target that reverts where the loop reaches it**
  (`TargetRevertingWhereReachedRevertsTheExecution`): if the first `k` targets commit, from the
  state the entry point's writes leave, to some state `t`, and the target of call `k` reverts
  from `t`, the execution reverts. This is "whatever the targets before it did and committed
  in their own frames" with nothing assumed about the reverting target elsewhere.
* **So the failed attempt can be retried** (`FailedAttemptWithAlwaysRevertingTargetCanBeRetried`).
* `EndsInRevertAlwaysReverts` is a syntactic sufficient condition for `AlwaysReverts`, and
  `RevertingTargetBeyondTheLeafWitness` shows both new premises fire where the leaf premise
  is false.
-/

namespace Contracts.InteropHandler

/-- **A TARGET THAT REVERTS FROM EVERY STATE REVERTS THE WHOLE EXECUTION.** In every write order,
at every budget and from every state: if the target of one of bundle `b`'s first `b.calls`
calls is `AlwaysReverts`, then `executeAtomicBundle(b)` and `executeBundle(b)` revert. -/
def Properties.AlwaysRevertingTargetRevertsTheExecution : Prop :=
  ∀ (v : Variant) (n : ℕ) (b : Bundle) (ok : Bool) (cs : List Callee) (s : State),
    (∃ c ∈ cs.take b.calls, AlwaysReverts v c) →
    exec v n (.entry (.executeAtomicBundle b ok) cs) s = none ∧
      exec v n (.entry (.executeBundle b ok) cs) s = none

/-- **A TARGET THAT REVERTS WHERE THE LOOP REACHES IT REVERTS THE WHOLE EXECUTION.** In every
write order: let `k < b.calls` be a call whose target `cs[k]` is given. If the call loop over the
first `k` calls, run from the state the entry point's writes leave (`beforeCalls`, after
`_verifyBundle` for `executeBundle`), commits to `t`, and `cs[k]` reverts from `t` at the budget
the loop gives it, then the execution of `b` reverts. Nothing is assumed about how `cs[k]` would
behave from any other state. -/
def Properties.TargetRevertingWhereReachedRevertsTheExecution : Prop :=
  ∀ (v : Variant) (m : ℕ) (b : Bundle) (ok : Bool) (cs : List Callee) (s : State) (k : ℕ)
    (hk : k < cs.length) (t : State) (l : List Effect), k < b.calls →
    (exec v (m + 1 + k) (.calls b.hash (List.range k) (cs.take k)) (beforeCalls v b s) =
          some (t, l) →
        exec v m (.target cs[k]) t = none →
        exec v (m + 2 + k) (.entry (.executeAtomicBundle b ok) cs) s = none) ∧
    (exec v (m + 1 + k) (.calls b.hash (List.range k) (cs.take k))
          (beforeCalls v b (s.verifyIfUnreceived b.hash)) = some (t, l) →
        exec v m (.target cs[k]) t = none →
        exec v (m + 2 + k) (.entry (.executeBundle b ok) cs) s = none)

/-- **SO A FAILED ATTEMPT CAN BE RETRIED, FOR EVERY TARGET THAT REVERTS FROM EVERY STATE.** If
bundle `b` is `Unreceived` and one of its first `b.calls` targets is `AlwaysReverts`, the
transaction `executeAtomicBundle(b)` leaves the state exactly as it was and commits nothing —
including whatever that target and the targets before it committed in their own frames. From
that same state, a retry whose targets return delivers each of `b`'s calls once, in order,
executes `b`, and leaves it `FullyExecuted` with its calls `Executed`. -/
def Properties.FailedAttemptWithAlwaysRevertingTargetCanBeRetried : Prop :=
  ∀ (s : State) (b : Bundle) (fuel : ℕ) (cs : List Callee),
    s.bundle b.hash = .Unreceived → (∃ c ∈ cs.take b.calls, AlwaysReverts .deployed c) →
    submit .deployed s ⟨fuel, .executeAtomicBundle b true, cs⟩ = (s, []) ∧
    submit .deployed s
        ⟨b.calls + 2, .executeAtomicBundle b true, List.replicate b.calls .returns⟩ =
      ((s.setBundle b.hash .FullyExecuted).executeAll b.hash b.calls,
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash])

/-- **A TARGET WHOSE CONTINUATION ENDS IN `reverts` ALWAYS REVERTS.** In every write order. -/
def Properties.EndsInRevertAlwaysReverts : Prop :=
  ∀ (v : Variant) (c : Callee), c.endsInRevert = true → AlwaysReverts v c

/-- **THE NEW PREMISES FIRE WHERE THE LEAF PREMISE IS FALSE.**

* `wRevertsAfterWork` always reverts, in every order, but is not the leaf `reverts`, so the leaf
  premise fails on `wAttemptAfterWork`'s targets. The attempt commits nothing from fresh storage
  and leaves `wA` and `wB` `Unreceived`, although the work before the revert
  (`wWorkThenReturn`, executing `wB`) commits on its own from the state `wA`'s writes leave.
* `wReenterOuterUncaught` is not the leaf either. It reverts from the state `wA`'s writes leave
  (its re-entry into `wA` is refused there), so the state-dependent premise holds for call 0 of
  `wNestedUncaught` with `k = 0`; yet from fresh storage it commits, so it is not
  `AlwaysReverts`. `wNestedUncaught` commits nothing.
* With a nontrivial prefix (`k = 1`), in `wLateReentry`: the loop over call 0 (whose target
  executes `wB` re-entrantly) commits to some state `t`, and call 1's target `wReenterOuter`
  reverts from `t` at the budget the loop gives it — the premises of
  `TargetRevertingWhereReachedRevertsTheExecution` with `m = 5`, `k = 1` — although it commits from
  fresh storage. The transaction commits nothing, `wB`'s nested execution included. -/
def Properties.RevertingTargetBeyondTheLeafWitness : Prop :=
  (∀ v : Variant, AlwaysReverts v wRevertsAfterWork) ∧
    Callee.reverts ∉ wAttemptAfterWork.callees.take wA.calls ∧
    (submit .deployed init wAttemptAfterWork).2 = [] ∧
    (submit .deployed init wAttemptAfterWork).1.bundle wA.hash = .Unreceived ∧
    (submit .deployed init wAttemptAfterWork).1.bundle wB.hash = .Unreceived ∧
    (exec .deployed 6 (.target wWorkThenReturn) (beforeCalls .deployed wA init)).isSome = true ∧
    Callee.reverts ∉ wNestedUncaught.callees.take wA.calls ∧
    exec .deployed 6 (.target wReenterOuterUncaught) (beforeCalls .deployed wA init) = none ∧
    (exec .deployed 6 (.target wReenterOuterUncaught) init).isSome = true ∧
    ¬ AlwaysReverts .deployed wReenterOuterUncaught ∧
    (submit .deployed init wNestedUncaught).2 = [] ∧
    Callee.reverts ∉ wLateReentry.callees.take wA.calls ∧
    (∃ (t : State) (l : List Effect),
      exec .deployed (5 + 1 + 1) (.calls wA.hash (List.range 1) (wLateReentry.callees.take 1))
          (beforeCalls .deployed wA init) = some (t, l) ∧
        exec .deployed 5 (.target wReenterOuter) t = none) ∧
    (exec .deployed 5 (.target wReenterOuter) init).isSome = true ∧
    (submit .deployed init wLateReentry).2 = [] ∧
    (submit .deployed init wLateReentry).1.bundle wB.hash = .Unreceived

end Contracts.InteropHandler
