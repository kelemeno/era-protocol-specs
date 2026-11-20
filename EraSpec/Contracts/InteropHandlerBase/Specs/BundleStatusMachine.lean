import Mathlib.Tactic


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/BundleStatusMachine.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  THE BUNDLE STATUS MACHINE — one delivery per bundle, by two routes that exclude each other.

  Source: era-contracts `draft/v0.35.0` at `b17415d20`, `l1-contracts/contracts/interop/interop-handler/`
  (`IHB` = `InteropHandlerBase.sol`, `L2` = `L2InteropHandler.sol`, `L1` = `L1InteropHandler.sol`).
  The handlers spread the bundle-status transitions across their entry points, each with its own guard:

      L1 verifyBundle / L2 verifyAtomicBundle   require(status == Unreceived) -> Verified
                                                (IHB:313 in _validateVerifiable; write IHB:318)
      L1 executeBundle / L2 executeAtomicBundle require(status == Unreceived || status == Verified)
                                                -> FullyExecuted (IHB:282-287; write IHB:326)
      unbundleBundle                            require(status == Verified || status == Unbundled)
                                                -> Unbundled (IHB:139; write IHB:147)

  `Step` has one constructor per edge. `executeFresh` and `executeAtomic` are the same pair of states
  (`Unreceived → FullyExecuted`): at `b17415d20` the second is the L2 entry point's fresh case, the
  first the L1 one's. The pin `c67894b9`'s `executeAtomicBundle` admitted `Unreceived` only; its
  atomic sub-machine is in `History/Specs/BundleStatusMachine.lean`.

  Read one at a time these are guards; read together they are a state machine, and the safety property
  is a REACHABILITY claim no single function states: a bundle is delivered at most once, and the
  whole-bundle route and the per-call unbundled route cannot both happen.  That matters because each
  route delivers the same calls -- doing both would deliver twice.
-/

namespace AttackVectors.BundleStatusMachine


inductive Status
  | Unreceived | Verified | FullyExecuted | Unbundled
  deriving DecidableEq, Repr


/-- The transitions, one constructor per deployed edge. -/
inductive Step : Status → Status → Prop
  | verify : Step .Unreceived .Verified
  | executeFresh : Step .Unreceived .FullyExecuted
  | executeVerified : Step .Verified .FullyExecuted
  | unbundleFirst : Step .Verified .Unbundled
  | unbundleAgain : Step .Unbundled .Unbundled
  | executeAtomic : Step .Unreceived .FullyExecuted


/-- Reflexive-transitive closure: the states a bundle can reach. -/
inductive Reach : Status → Status → Prop
  | refl (s : Status) : Reach s s
  | tail {a b c : Status} : Reach a b → Step b c → Reach a c


/-! ## The per-call machine — where a double delivery would actually land

Bundle-level exclusivity says a bundle takes one route.  It does NOT by itself say a CALL is delivered
once: the unbundled route processes calls individually, across as many `unbundleBundle` transactions as
the unbundler likes (`Unbundled -> Unbundled` is a legal edge).  The per-call guard is what closes it:

    if (requested == Executed)  { require(recorded == Unprocessed, CallNotExecutable);  recorded = Executed; }
    else if (requested == Cancelled) { require(recorded != Executed, CallAlreadyExecuted);
                                       if (recorded == Unprocessed) recorded = Cancelled; }
    // any other request is skipped

Note the asymmetry in the second branch: cancelling is IDEMPOTENT (re-cancelling a `Cancelled` call is
a silent no-op, not a revert), while executing is not.  That is what lets an unbundler resubmit a
status array without the transaction reverting on already-cancelled entries. -/

inductive CallStatus
  | Unprocessed | Executed | Cancelled
  deriving DecidableEq, Repr


/-- The per-call transitions, one constructor per reachable edge of the loop above. -/
inductive CallStep : CallStatus → CallStatus → Prop
  | execute : CallStep .Unprocessed .Executed
  | cancel : CallStep .Unprocessed .Cancelled
  | cancelAgain : CallStep .Cancelled .Cancelled


inductive CallReach : CallStatus → CallStatus → Prop
  | refl (s : CallStatus) : CallReach s s
  | tail {a b c : CallStatus} : CallReach a b → CallStep b c → CallReach a c


/-! ## No inflation: the destination never releases more than the source collected

The two sides handle the SAME field.  At send, `InteropCenter` accumulates

    totalBurnedCallsValue += _callStarters[i].callAttributes.interopCallValue;

over every call (`InteropCenter.sol:681`), and `_ensureCorrectTotalValue` (`:418-460`) requires those
tokens to have been received.  The call that lands in the bundle (`bundle.calls[i] = interopCall`, `:680`) carries
that same number: `_processCallStarter` builds it with `value: _callStarter.callAttributes.interopCallValue`
(`InteropCenter.sol:819` for an indirect call, `:828` for a direct one), and at the destination `_executeCalls` releases
exactly `interopCall.value` — but only for calls it executes.

So the source collects over ALL calls and the destination releases over the EXECUTED ones.  Two things
make that a conservation statement rather than an accounting coincidence:

* each executed call contributes at most once (`callExecuted_terminal` plus `routes_exclusive`, i.e.
  `value_released_at_most_once` above) — without it a call could be summed twice;
* executed calls are a subset of all calls, which is the bound below.

The gap is real and intended: a CANCELLED call's value was collected at the source and is never
released at the destination.  That is the unbundler's choice, and this file does not claim the
difference is recoverable — only that it never goes the other way. -/

/-- Per-call value paired with the call's final status. -/
abbrev Ledger := List (ℕ × CallStatus)


/-- What the destination releases: the value of calls that ended `Executed`. -/
def releasedSum : Ledger → ℕ
  | [] => 0
  | (v, s) :: rest => (if s = CallStatus.Executed then v else 0) + releasedSum rest


/-- What the source collected: the value of every call in the bundle. -/
def collectedSum : Ledger → ℕ
  | [] => 0
  | (v, _) :: rest => v + collectedSum rest


end AttackVectors.BundleStatusMachine
