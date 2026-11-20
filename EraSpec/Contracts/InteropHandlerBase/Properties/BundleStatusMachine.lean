import EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachine

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


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


/-! ## Safety -/

/-- **DELIVERY IS TERMINAL.**  No guard admits `FullyExecuted`, so nothing follows it — the CEI write
that precedes the calls is what makes a reentrant or repeated execution hit a closed door. -/
abbrev Properties.fullyExecuted_terminal {t : Status} :=
  ¬ Step .FullyExecuted t


/-- Hence a delivered bundle stays delivered. -/
abbrev Properties.reach_from_fullyExecuted {t : Status} (h : Reach .FullyExecuted t) :=
  t = .FullyExecuted


/-- **THE UNBUNDLED ROUTE IS ABSORBING TOO.**  Once unbundled, the whole-bundle execution path is
closed: the only edge out of `Unbundled` returns to `Unbundled`. -/
abbrev Properties.reach_from_unbundled {t : Status} (h : Reach .Unbundled t) :=
  t = .Unbundled


/-- **THE TWO DELIVERY ROUTES EXCLUDE EACH OTHER.**  A bundle cannot be both executed as a whole and
unbundled for per-call execution, in either order — so the same call cannot be delivered twice by
taking one route and then the other. -/
abbrev Properties.routes_exclusive :=
  (¬ Reach .FullyExecuted .Unbundled) ∧ (¬ Reach .Unbundled .FullyExecuted)


/-- Both delivery states are reachable from a fresh bundle, so the exclusivity above is not vacuous —
each route is genuinely available until the other is taken. -/
abbrev Properties.both_routes_available :=
  Reach .Unreceived .FullyExecuted ∧ Reach .Unreceived .Unbundled


/-! ## No edge returns to `Unreceived`

At the pin `c67894b9` the atomic entry point admitted `Unreceived` only, and the prose here argued
that an atomic bundle never reaches `Verified`; that record is
`History/Properties/BundleStatusMachine.lean`. At `b17415d20` `executeAtomicBundle` admits
`Verified` too (`IHB:282-287`) and skips the flow gate for it (`L2:73-75`), so a `Verified` bundle of
either layer is deliverable whole or unbundled. The gate results at `b17415d20` are in topic
`Reentrancy` (`DeliveryNeedsTheGateAtV35`, `VerifiedBundleExecutesWithoutTheGateAtV35`). -/

/-- **NO EDGE FROM `Verified` BACK TO `Unreceived`.**  As stated this is only
`¬ Step .Verified .Unreceived`, the `s := .Verified` case of `unreceived_unreachable`; the name is
the pin's (where it supported a claim about the atomic entry point, now in History). -/
abbrev Properties.verified_blocks_atomic_execution :=
  ¬ Step .Verified .Unreceived


/-- And no state returns to `Unreceived` at all: it is the machine's unique initial state, so a bundle
that leaves it can never be treated as fresh again. -/
abbrev Properties.unreceived_unreachable {s : Status} :=
  ¬ Step s .Unreceived


/-- **A CALL IS EXECUTED AT MOST ONCE.**  `Executed` has no outgoing edge: the `require(recorded ==
Unprocessed)` on the execute branch is what makes a second execution of the same call impossible, no
matter how many `unbundleBundle` transactions are submitted. -/
abbrev Properties.callExecuted_terminal {t : CallStatus} :=
  ¬ CallStep .Executed t


abbrev Properties.callReach_from_executed {t : CallStatus} (h : CallReach .Executed t) :=
  t = .Executed


/-- **AND A CANCELLED CALL IS NEVER EXECUTED.**  The execute branch demands `Unprocessed`, so
cancellation is a one-way door — `Cancelled` only loops to itself. -/
abbrev Properties.callReach_from_cancelled {t : CallStatus} (h : CallReach .Cancelled t) :=
  t = .Cancelled


/-- The per-call counterpart of `routes_exclusive`: executed and cancelled are mutually unreachable. -/
abbrev Properties.call_outcomes_exclusive :=
  (¬ CallReach .Executed .Cancelled) ∧ (¬ CallReach .Cancelled .Executed)


/-- Both outcomes are reachable from a fresh call, so the exclusivity is not vacuous. -/
abbrev Properties.call_outcomes_available :=
  CallReach .Unprocessed .Executed ∧ CallReach .Unprocessed .Cancelled


/-- **CANCELLATION IS IDEMPOTENT, EXECUTION IS NOT.**  Re-cancelling is a legal edge; there is no
`Executed -> Executed`.  The asymmetry is deliberate in the source (a resubmitted status array must not
revert on entries already cancelled) and it is why `Cancelled` needs its self-loop while `Executed`
does not. -/
abbrev Properties.cancel_idempotent_execute_not :=
  CallStep .Cancelled .Cancelled ∧ ¬ CallStep .Executed .Executed


/-! ## The two levels compose

A call reaches `Executed` by exactly one of two routes:

* the whole-bundle route, where `executeBundle` / `executeAtomicBundle` set every call to `Executed` in
  one transaction, from bundle status `Unreceived` or `Verified`; or
* the unbundled route, where each call transitions individually, from bundle status `Unbundled`.

`routes_exclusive` rules out taking both, and `callReach_from_executed` rules out repeating either.
Neither alone suffices: bundle-level exclusivity says nothing about repeated per-call execution within
the unbundled route, and the per-call guard says nothing about a bundle being both fully executed and
unbundled.  Together they give "each call is delivered at most once", which is the property the
destination side of no-theft needs. -/

/-! ## Base-token value is released at most once per call

The destination side's value statement.  `_executeCalls` releases a call's base-token `value` through a
chain with one call site at each link:

    BaseTokenHolder.give            onlyInteropHandler; releases from a pre-funded holder, not a mint,
                                    and notifies L2_ASSET_TRACKER before transferring
      <- L2:152                     the SOLE caller of give, inside _handleCallValue
      <- IHB:371                    the SOLE caller of _handleCallValue, inside _executeCalls

and `_executeCalls` pays call `i` exactly when that call is being executed:

    if (!_executeAllCalls) { if (_providedCallStatus[i] != Executed) continue; }   // unbundled route
    _handleCallValue(interopCall.value, _sourceChainId);

Both routes record the payment in the SAME place — `callStatus[bundleHash][i] = Executed`
(`IHB:330` in `_markFullyExecutedAndRun` for the whole bundle, `IHB:155` per call).  So "paid"
and "the call's status is `Executed`" are the same event, and at-most-once payment is at-most-once
entry into `Executed`.

That needs BOTH machines, and this is the composition rather than a new argument:

* WITHIN the unbundled route, `callExecuted_terminal` — a call cannot re-enter `Executed`, however many
  `unbundleBundle` transactions are sent.
* ACROSS routes, `routes_exclusive` — an unbundled bundle cannot then be executed whole (which would
  pay every call again, since the whole-bundle route writes `Executed` unconditionally rather than
  checking it first).

Neither alone suffices, and the second is the one that is easy to miss: the whole-bundle route does NOT
guard on the per-call status, so nothing at the call level would stop it re-paying. It is the BUNDLE
status that does. -/

/-- **PAID AT MOST ONCE.**  The two facts that jointly bound base-token release per call: no second
entry into `Executed` within a route, and no taking both routes. -/
abbrev Properties.value_released_at_most_once :=
  (∀ t : CallStatus, ¬ CallStep .Executed t) ∧
        (¬ Reach .FullyExecuted .Unbundled ∧ ¬ Reach .Unbundled .FullyExecuted)


/-- **AS STATED, A FACT ABOUT THE PER-CALL GRAPH ONLY.**  The proposition is one `execute` edge and
the absence of an `Executed → Executed` edge.  It never mentions the whole-bundle write, and its
second conjunct is a property of the abstract machine, whereas the code's write maps `Executed` to
`Executed` without a check.  What the text below describes was stated over the engine in the pin
topic `BundleStatusMachineStrong`, now History (`Contracts.InteropHandler.History`):
`WholeBundleWriteIgnoresCallStatus` (the write, as the handler model's `State.executeAll`),
`CallStatusDoesNotStopWholeBundleRedelivery` (only the bundle status stops a second payment) and
`AdmittedBundleHasOnlyUnprocessedCalls` (the deployed guards never reach a state where it would
have to).

The gap the whole-bundle route leaves at the call level, stated so the reliance on bundle status is
explicit: `Unprocessed → Executed` and a re-entry attempt are not distinguished by anything in the
per-call machine when `_executeAllCalls` is true, since that path writes the status without reading it.
`routes_exclusive` is what closes it.

CONFIRMED AGAINST THE COMPILED YUL rather than inferred from the Solidity.  The whole-bundle route's
status write was, at the pin `c67894b9`, `for_4476381376322263891` in `InteropHandler`, whose body is:

    mstore(0, var_bundleHash); mstore(32, 2); let dataSlot_1 := keccak256(0, 64)   -- callStatus base
    mstore(0, var_i); mstore(32, dataSlot_1); let slot := keccak256(0, 64)         -- leaf slot
    let split_expr_5 := sload(slot)
    let split_expr_7 := and(split_expr_5, not(255))
    let split_expr_8 := or(split_expr_7, 1)
    sstore(slot, split_expr_8)

The `sload` feeds only the MASK — `and(·, not(255))` preserves the high bytes — and the low byte is
then `or`-ed to `1`, which is `CallStatus.Executed`.  There is no comparison and no branch: the write
happens whatever the previous status was.  So the claim above is not a reading of intent, it is what
the code does, and `routes_exclusive` is genuinely the only thing preventing a second payment.

The specs of that loop body's three blocks (`block_2862394693737849679`, `block_5612315614323394231`,
`block_8179420195348823280`) belong to the sibling contracts-formal-verification development; this
package has no Yul.  Here the loop's closed form is the model's `State.executeAll`. -/
abbrev Properties.wholeBundle_route_does_not_check_callStatus :=
  CallReach .Unprocessed .Executed ∧ ¬ CallStep .Executed .Executed


/-- **NO INFLATION.**  Whatever the per-call outcomes, the destination releases no more than the source
collected for that bundle.

What is proved here is about an arbitrary `Ledger`: nothing ties `l` to the handler's state, so on its
own this is a list inequality. The link to the handler (one entry per call, its final `callStatus`,
and the base token actually released) is `Contracts.InteropHandler.Faithful.ReleaseIsTheHandlerLedger`,
and the handler-level statement is `HandlerReleasesAtMostCollected`, both in `ValueLedgerFaithful`. -/
abbrev Properties.released_le_collected (l : Ledger) :=
  releasedSum l ≤ collectedSum l


/-- **AND THE BOUND IS TIGHT.**  A bundle whose calls all execute releases exactly what was collected,
so the inequality is not slack hiding a systematic shortfall. -/
abbrev Properties.released_eq_collected_of_all_executed :=
  ∀ l : Ledger, (∀ p ∈ l, p.2 = CallStatus.Executed) → releasedSum l = collectedSum l


/-- The shortfall named: value collected for calls that did not execute.  Recorded so the gap is
visible rather than implied by the inequality. -/
abbrev Properties.shortfall_is_unexecuted (v : ℕ) (tl : Ledger) :=
  collectedSum ((v, CallStatus.Cancelled) :: tl) - releasedSum ((v, CallStatus.Cancelled) :: tl)
        = v + (collectedSum tl - releasedSum tl)


end AttackVectors.BundleStatusMachine
