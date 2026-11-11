import EraSpec.Contracts.InteropHandlerBase.Specs.Reentrancy

/-!
# Model additions: a delivered call's target that reverts, read semantically

Source: era-contracts at the pin `c67894b9`, as in `Specs/Reentrancy.lean` (paths relative to
`l1-contracts/contracts/interop/interop-handler/`).

**This file is definitions only.** The results are in
`EraSpec.Contracts.InteropHandlerBase.Properties.ReentrancyStrong` and are proved in
`EraSpec.Contracts.InteropHandlerBase.Proofs.ReentrancyStrong`.

## Why this file exists

`Properties.RevertingCallRevertsTheExecution` and `Properties.FailedAttemptCanBeRetried`
(topic `Reentrancy`) take the premise `Callee.reverts ∈ cs.take b.calls`: one of the bundle's
targets is the LEAF `Callee.reverts`. That is a syntactic test on the top-level callee list. It
misses every target that reverts after doing something, which is the case the source comment
at `InteropHandlerBase.sol:135-136` is about ("if either of the calls fail, the
`_executeCalls` will fail as well, thus making the whole flow revert, no changes will be
applied to the state"):

* a target that re-enters the handler, commits a nested execution in its own frame, and then
  reverts (`wRevertsAfterWork` below);
* a target whose uncaught re-entrant call fails, and which therefore reverts although its own
  continuation would return (`wReenterOuterUncaught`, the first target of `wNestedUncaught`).

This file names the two semantic readings of "the target of call `k` reverts":

* `AlwaysReverts v c` — `c`, run as a target, reverts from every state at every budget. The
  leaf `Callee.reverts` is one such target; so is every target whose own continuation ends in
  `reverts` (`Callee.endsInRevert`), whatever it calls first.
* "reverts where the loop reaches it" — the target of call `k` reverts from the state the first
  `k` targets left. This is stated directly in the property, over `exec`; it needs no new
  definition. It covers `wReenterOuterUncaught`, which reverts inside `wA`'s execution only
  because `wA` is already `FullyExecuted` there, and commits from fresh storage.
-/

namespace Contracts.InteropHandler

/-- **A TARGET THAT REVERTS FROM EVERY STATE.** Run as the target of a delivered call
(`IERC7786Recipient(to).receiveMessage`, `:282-286`), `c` reverts in the order `v` whatever the
state and the budget. -/
def AlwaysReverts (v : Variant) (c : Callee) : Prop :=
  ∀ (m : ℕ) (t : State), exec v m (.target c) t = none

/-- **A TARGET WHOSE OWN CONTINUATION ENDS IN A REVERT.** Whatever entry points `c` calls on the
way, and whether or not those calls fail or are caught, `c` goes on as its `next` target; if that
chain of continuations ends in `reverts`, so does `c`. A sufficient, syntactic condition for
`AlwaysReverts` (`Properties.EndsInRevertAlwaysReverts`). -/
def Callee.endsInRevert : Callee → Bool
  | .returns => false
  | .reverts => true
  | .calls _ _ _ next => next.endsInRevert

/-! ## Witness data -/

/-- A target that executes `wB` re-entrantly (committing it in its own frame) and then
reverts. It is not the leaf `Callee.reverts`. -/
def wRevertsAfterWork : Callee := .calls (.executeAtomicBundle wB true) [] false .reverts

/-- The same target without the final revert: it executes `wB` re-entrantly and returns. -/
def wWorkThenReturn : Callee := .calls (.executeAtomicBundle wB true) [] false .returns

/-- Atomic execution of `wA`: call 0's target is `wRevertsAfterWork`, call 1's returns. -/
def wAttemptAfterWork : Tx := ⟨8, .executeAtomicBundle wA true, [wRevertsAfterWork, .returns]⟩

/-- The first target of `wNestedUncaught`: it executes `wB` re-entrantly, then calls
`executeAtomicBundle(wA)` without catching a failure, then returns. Inside `wA`'s own execution
that re-entry fails (`wA` is `FullyExecuted`), so the target reverts there; from fresh storage
it commits. -/
def wReenterOuterUncaught : Callee :=
  .calls (.executeAtomicBundle wB true) [] false (reenter (.executeAtomicBundle wA true) false)

/-- A target that calls `executeAtomicBundle(wA)` without catching a failure, then returns. -/
def wReenterOuter : Callee := reenter (.executeAtomicBundle wA true) false

/-- Atomic execution of `wA`: call 0's target executes `wB` re-entrantly and returns; call 1's
target is `wReenterOuter`, which reverts there because `wA` is already `FullyExecuted`. -/
def wLateReentry : Tx := ⟨8, .executeAtomicBundle wA true, [wWorkThenReturn, wReenterOuter]⟩

end Contracts.InteropHandler
