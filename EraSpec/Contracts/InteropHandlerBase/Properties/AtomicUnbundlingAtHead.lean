import EraSpec.Contracts.InteropHandlerBase.Specs.AtomicUnbundlingAtHead

/-!
# Properties: an atomic bundle on the unbundled route at head

Statements about `EraSpec.Contracts.InteropHandlerBase.Specs.AtomicUnbundlingAtHead`, which uses the
model of `Specs/ReentrancyAtHead.lean`: the L2 handler at main `3605e82` (and, with the same logic,
`e561b9cc2` and v0.35 `d9f6789`). Proofs are in
`EraSpec.Contracts.InteropHandlerBase.Proofs.AtomicUnbundlingAtHead`.

As in `Properties/ReentrancyAtHead.lean`, the general results quantify over every target behaviour
and every budget and take no hash premise: the handler keys its state by the bundle hash, and so do
the statements. `CallsClosed` (only bundles that left both entry states have processed calls) holds
of fresh storage and of every state reached from it
(`NestedExecutionFollowsTheStatusMachineAtHead`).

## The finding: all-or-nothing does not hold at head

* **A verified atomic bundle can be partly executed, for good**
  (`AtomicBundleCanBePartlyExecutedForGoodAtHead`). For every bundle with at least two calls that
  is still `Unreceived`, the two ordinary transactions of `partialRun` (`verifyAtomicBundle` with a
  passing flow gate, then `unbundleBundle` requesting `[Executed, Cancelled, skip…]`) commit call 0
  and leave call 1 `Cancelled`; and whatever is submitted afterwards, call 1 is never delivered and
  the bundle never completes `executeAtomicBundle`.
* **A cancelled call never runs** (`CancelledCallNeverRunsAtHead`): the permanence on its own, from
  any state.
* `PartialExecutionWitnessAtHead`: the premises hold on `wA` from fresh storage, and
  `executeAtomicBundle` of `wA` reverts on a failing second call while the unbundled route commits
  the first call alone.
* **The pinned atomic sub-machine does not describe head**
  (`HeadStatusesLeaveThePinnedAtomicSubMachine`): `BundleStatusMachine.AtomicReach` reaches neither
  `Verified` nor `Unbundled` from `Unreceived`; the head handler reaches both.

## What does hold

* **Every delivery follows the flow gate** (`EveryDeliveryFollowsTheFlowGateAtHead`): in the
  committed log of any sequence of transactions, a delivery of a call of a bundle hash that started
  `Unreceived` comes after a flow-gate event for that hash. A gate event is logged only on a passing
  verdict (`FailingFlowGateRefusesAnUnverifiedBundleAtHead`). So the gate decides whether a bundle's
  calls may run, not that all of them do.
* **Partial execution needs a committed `verifyAtomicBundle`**
  (`PartialExecutionNeedsVerifyAtomicBundleAtHead`): a delivered call belongs to a bundle hash that
  completed `executeAtomicBundle` or that `verifyAtomicBundle` verified.
* `ReentrancyAtHead` has the rest: no effect twice, and one successful `executeAtomicBundle` runs
  every call.

## Who may unbundle

`DefaultUnbundlerUsesTheRescuePathAtHead` and `DefaultUnbundlerWitnessAtHead` are about the two
permission gates alone (`DirectUnbundleAllowed`, `RescueUnbundleAllowed`), which the exec model
omits. They do not model `InteropCenter`, message delivery or address parsing.

## What is not claimed

Nothing here is about tokens or refunds: the model has the handler's two status mappings and its
log, no balances and no `AtomicFlowManager`. That a cancelled call's source-side funds are not
returned is argued from the source in the Specs header, not proved.
-/

namespace Contracts.InteropHandlerAtHead

open AttackVectors.BundleStatusMachine (Status CallStatus AtomicReach)
open Contracts.InteropHandler (BundleHash Bundle State Effect CallsClosed init wA)

/-! ## The finding -/

/-- **AT HEAD, A VERIFIED ATOMIC BUNDLE CAN BE PARTLY EXECUTED, FOR GOOD.** Take any state in which
only closed bundles have processed calls (`CallsClosed`), and any bundle `b` with at least two calls
whose hash is `Unreceived` there. Then `partialRun b` (anyone's `verifyAtomicBundle(b)` with a
passing flow gate, then `unbundleBundle(b, [Executed, Cancelled, skip, …])`, both ordinary
successful transactions) commits exactly the gate event and the delivery of call 0, and leaves
`b.hash` `Unbundled`, call 0 `Executed` and call 1 `Cancelled`. And for every sequence `txs`
submitted after it, with every target behaviour: call 1 of `b.hash` is never delivered, and `b.hash`
never completes `executeAtomicBundle`. -/
def Properties.AtomicBundleCanBePartlyExecutedForGoodAtHead : Prop :=
  ∀ (s : State) (b : Bundle) (txs : List Tx),
    CallsClosed s → s.bundle b.hash = .Unreceived → 2 ≤ b.calls →
    (submitAll s (partialRun b)).2 = [.verified b.hash, .effect (.delivered b.hash 0)] ∧
    (submitAll s (partialRun b)).1.bundle b.hash = .Unbundled ∧
    (submitAll s (partialRun b)).1.call b.hash 0 = .Executed ∧
    (submitAll s (partialRun b)).1.call b.hash 1 = .Cancelled ∧
    Effect.delivered b.hash 1 ∉ effects (submitAll s (partialRun b ++ txs)).2 ∧
    Effect.executed b.hash ∉ effects (submitAll s (partialRun b ++ txs)).2

/-- **A CANCELLED CALL NEVER RUNS, AT HEAD.** From any state satisfying `CallsClosed` in which call
`i` of bundle hash `h` is recorded `Cancelled`, along any sequence of transactions: the call stays
`Cancelled`, it is never delivered, and `h` never completes `executeAtomicBundle`. -/
def Properties.CancelledCallNeverRunsAtHead : Prop :=
  ∀ (s : State) (txs : List Tx) (h : BundleHash) (i : ℕ),
    CallsClosed s → s.call h i = .Cancelled →
    (submitAll s txs).1.call h i = .Cancelled ∧
    Effect.delivered h i ∉ effects (submitAll s txs).2 ∧
    Effect.executed h ∉ effects (submitAll s txs).2

/-- **THE FINDING ON A CONCRETE BUNDLE.** Fresh storage and `wA` (hash `1`, two calls) satisfy the
premises of `AtomicBundleCanBePartlyExecutedForGoodAtHead`, and `partialRun wA` commits the gate
event and call 0's delivery. Next to it: `wFailingExecute`, the atomic execution of `wA` whose second
target reverts, reverts and commits nothing; `wSkipFailing`, which verifies `wA` and unbundles it
requesting call 0 only, commits call 0's delivery and leaves `wA` `Unbundled` with call 1
`Unprocessed`: call 1 is not delivered, so its target is not called. -/
def Properties.PartialExecutionWitnessAtHead : Prop :=
  CallsClosed init ∧ init.bundle wA.hash = .Unreceived ∧ 2 ≤ wA.calls ∧
    (submitAll init (partialRun wA)).2 = [.verified 1, .effect (.delivered 1 0)] ∧
    (exec wFailingExecute.fuel (.entry wFailingExecute.entry wFailingExecute.callees) init).isNone
      = true ∧
    (submit init wFailingExecute).2 = [] ∧
    (submit init wFailingExecute).1.bundle 1 = .Unreceived ∧
    (submitAll init wSkipFailing).2 = [.verified 1, .effect (.delivered 1 0)] ∧
    (submitAll init wSkipFailing).1.bundle 1 = .Unbundled ∧
    (submitAll init wSkipFailing).1.call 1 0 = .Executed ∧
    (submitAll init wSkipFailing).1.call 1 1 = .Unprocessed

/-- **THE PINNED ATOMIC SUB-MACHINE DOES NOT DESCRIBE HEAD.** `BundleStatusMachine.AtomicReach`, the
pin's one-edge machine for atomic bundles, reaches neither `Verified` nor `Unbundled` from
`Unreceived`. At head, from any `CallsClosed` state in which `b.hash` is `Unreceived`,
`verifyAtomicBundle(b)` with a passing gate leaves it `Verified`, and (for `b` with at least two
calls) `partialRun b` leaves it `Unbundled`. -/
def Properties.HeadStatusesLeaveThePinnedAtomicSubMachine : Prop :=
  ¬ AtomicReach .Unreceived .Verified ∧ ¬ AtomicReach .Unreceived .Unbundled ∧
  ∀ (s : State) (b : Bundle), CallsClosed s → s.bundle b.hash = .Unreceived →
    (submit s ⟨1, .verifyAtomicBundle b true, []⟩).1.bundle b.hash = .Verified ∧
    (2 ≤ b.calls → (submitAll s (partialRun b)).1.bundle b.hash = .Unbundled)

/-! ## What does hold -/

/-- **EVERY DELIVERY FOLLOWS THE FLOW GATE, AT HEAD.** From any state in which bundle hash `h` is
`Unreceived`, along any sequence of transactions with every target behaviour: wherever the committed
log delivers a call of `h`, the log before that point has a flow-gate event for `h`, logged by
`executeAtomicBundle` (`Event.gated h`) or by `verifyAtomicBundle` (`Event.verified h`).

The gate event is for the hash, not for the call: this does not say that the other calls of `h` run. -/
def Properties.EveryDeliveryFollowsTheFlowGateAtHead : Prop :=
  ∀ (s : State) (txs : List Tx) (h : BundleHash) (i : ℕ) (l₁ l₂ : List Event),
    s.bundle h = .Unreceived →
    (submitAll s txs).2 = l₁ ++ .effect (.delivered h i) :: l₂ →
    GatePassed h l₁

/-- **A FAILING FLOW GATE REFUSES AN UNVERIFIED BUNDLE, AT HEAD.** With the verdict `false`,
`verifyAtomicBundle` reverts from every state, and `executeAtomicBundle` reverts from every state in
which the bundle is not `Verified`. So a gate event in a log records a passing verdict. -/
def Properties.FailingFlowGateRefusesAnUnverifiedBundleAtHead : Prop :=
  ∀ (n : ℕ) (b : Bundle) (cs : List Callee) (s : State),
    exec n (.entry (.verifyAtomicBundle b false) cs) s = none ∧
    (s.bundle b.hash ≠ .Verified → exec n (.entry (.executeAtomicBundle b false) cs) s = none)

/-- **PARTIAL EXECUTION NEEDS A COMMITTED `verifyAtomicBundle`, AT HEAD.** From any state in which
bundle hash `h` is `Unreceived`, along any sequence of transactions: if the committed log delivers a
call of `h`, then it also has `verifyAtomicBundle`'s event for `h` or `h`'s `BundleExecuted`. A hash
whose calls ran without a committed `verifyAtomicBundle` completed `executeAtomicBundle`, which runs
every call (`WholeAtomicExecutionRunsEachCallOnceAtHead`). -/
def Properties.PartialExecutionNeedsVerifyAtomicBundleAtHead : Prop :=
  ∀ (s : State) (txs : List Tx) (h : BundleHash) (i : ℕ),
    s.bundle h = .Unreceived →
    Event.effect (.delivered h i) ∈ (submitAll s txs).2 →
    Event.verified h ∈ (submitAll s txs).2 ∨ Event.effect (.executed h) ∈ (submitAll s txs).2

/-! ## Who may unbundle -/

/-- **THE DEFAULT UNBUNDLER REACHES `unbundleBundle` ONLY THROUGH THE RESCUE PATH.** Let the bundle's
unbundler be the default, the sender on the source chain (`defaultUnbundler source sender`), with
the source chain's id non-zero and different from the destination's (`here`). Then:
* the direct gate (`InteropHandlerBase.sol:124-132`) admits a caller only if it is the handler
  itself;
* the `receiveMessage` gate (`:427-430`) admits a wrapped message exactly when its sender is that
  same account on the source chain.
And an unbundler named on the destination chain (`⟨here, r⟩`) passes the direct gate exactly as the
handler itself or as `r`. -/
def Properties.DefaultUnbundlerUsesTheRescuePathAtHead : Prop :=
  ∀ (here self caller source sender : ℕ), source ≠ here → source ≠ 0 →
    (DirectUnbundleAllowed here self caller (defaultUnbundler source sender) ↔ caller = self) ∧
    (∀ m : InteropAddress,
      RescueUnbundleAllowed m (defaultUnbundler source sender) ↔ m = ⟨source, sender⟩) ∧
    ∀ r : ℕ, DirectUnbundleAllowed here self caller ⟨here, r⟩ ↔ (caller = self ∨ caller = r)

/-- **THOSE PREMISES HOLD.** Source chain `1`, destination chain `2`, sender `7`, handler `9`: the
sender's direct call is refused, the handler's own call is admitted, and the sender's wrapped message
passes the rescue gate. -/
def Properties.DefaultUnbundlerWitnessAtHead : Prop :=
  (1 : ℕ) ≠ 2 ∧ (1 : ℕ) ≠ 0 ∧
    ¬ DirectUnbundleAllowed 2 9 7 (defaultUnbundler 1 7) ∧
    DirectUnbundleAllowed 2 9 9 (defaultUnbundler 1 7) ∧
    RescueUnbundleAllowed ⟨1, 7⟩ (defaultUnbundler 1 7)

end Contracts.InteropHandlerAtHead
