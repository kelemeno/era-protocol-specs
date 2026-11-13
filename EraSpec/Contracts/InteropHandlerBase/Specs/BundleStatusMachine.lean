import Mathlib.Tactic


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/BundleStatusMachine.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  THE BUNDLE STATUS MACHINE — one delivery per bundle, by two routes that exclude each other.

  `InteropHandlerBase` spreads its transitions across four functions, each with its own guard:

      verifyBundle        require(status == Unreceived)                      -> Verified
      executeBundle       require(status == Unreceived || status == Verified) -> FullyExecuted
      unbundleBundle      require(status == Verified  || status == Unbundled) -> Unbundled
      executeAtomicBundle require(status == Unreceived)                      -> FullyExecuted

  Read one at a time these are guards; read together they are a state machine, and the safety property
  is a REACHABILITY claim no single function states: a bundle is delivered at most once, and the
  whole-bundle route and the per-call unbundled route cannot both happen.  That matters because each
  route delivers the same calls -- doing both would deliver twice.

  The file also names a cross-contract dependency that the guards make load-bearing but do not state.
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

over every call, and `_handleValueCollection` requires those tokens to have been received.  The call
that lands in the bundle carries that same number (`InteropCenter.sol:738`,
`value: _callStarter.callAttributes.interopCallValue`), and at the destination `_executeCalls` releases
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


/-! ## The atomic sub-machine — a stronger guarantee, not a weaker one

Applying the same scope question to `routes_exclusive`: is it non-trivial for ATOMIC bundles?  It is
not, and the reason turns out to strengthen the atomic case rather than weaken it.

An atomic bundle cannot reach `Verified`: that edge is `verifyBundle`, which requires an L1 message
inclusion proof, and atomic bundles are never published to L1.  `unbundleBundle` requires
`Verified || Unbundled`.  So `Unbundled` is unreachable for an atomic bundle — it has exactly ONE
route, and `routes_exclusive` is satisfied vacuously for it.

That means the two machines divide by path:

* ATOMIC bundles — one route, so delivery-once follows from bundle-status terminality ALONE
  (`reach_from_fullyExecuted`).  The per-call machine is not needed: `executeAtomicBundle` writes every
  call `Executed` in one transaction, and there is no second transaction to worry about.
* PUBLIC bundles — two routes, so delivery-once genuinely needs BOTH machines, as recorded above.

So the earlier composition is not wrong for atomic bundles, it is more than they require.  Worth
knowing which half is load-bearing where.

The argument above is prose: `AtomicStep` below builds it into a definition.  Topic
`BundleStatusMachineStrong` proves it over the handler model, up to named clashes. -/

/-- **TAKEN AS A DEFINITION.**  The transitions available to an ATOMIC bundle, on the premise that
`verify` is unreachable for it (no L1 proof exists), and with it every edge that needs `Verified`.
That premise is assumed here, not proved: any one-edge relation gives the results stated about this
one.  Topic `BundleStatusMachineStrong` derives the sub-machine from the handler's guards
(`NoProofKeepsBundleInAtomicMachine`) and the premise from the source chain
(`AtomicLegStaysAtomicAtDestinationOrClash`). -/
inductive AtomicStep : Status → Status → Prop
  | executeAtomic : AtomicStep .Unreceived .FullyExecuted


inductive AtomicReach : Status → Status → Prop
  | refl (s : Status) : AtomicReach s s
  | tail {a b c : Status} : AtomicReach a b → AtomicStep b c → AtomicReach a c


end AttackVectors.BundleStatusMachine
