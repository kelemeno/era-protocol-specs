import EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachine

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


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


/-! ## The cross-contract dependency the guards rely on

`executeAtomicBundle` is stricter than `executeBundle`: it admits ONLY `Unreceived`, where
`executeBundle` also admits `Verified`.  So an atomic bundle that ever reached `Verified` could never
be executed atomically — the source funds are already burned, and the flow could only end in the
timeout path, whose recovery `RecoveryLimits` shows is partial.

The guard is nonetheless safe, and the reason is not in this contract:

  * `verifyBundle` reaches `Verified` only through `_verifyBundle`, which requires `_proveInclusion` —
    an L1 message inclusion proof.
  * Atomic bundles are NEVER published to L1: `InteropCenter._dispatchBundle` takes the `isAtomic`
    branch to `append` and skips `_sendBundleToL1` entirely.
  * So no valid inclusion proof for an atomic bundle exists, `verifyBundle` cannot succeed on one, and
    the `Unreceived -> Verified` edge is unreachable for atomic bundles.

That is a liveness dependency spanning two contracts, and it is of the same fragile species as
`LocalHonesty.sole_call_site`: nothing in the type system enforces it, and a future change that
published atomic bundles to L1 — for observability, say — would make `verifyBundle` succeed on them
and permanently brick their execution.  Recorded, not reported as a defect: the current code is
correct. -/

/-- **THE CONDITIONAL.**  If an atomic bundle ever reached `Verified`, atomic execution would be
permanently unavailable — `Verified` has no edge to `FullyExecuted` via the atomic entry point, whose
only enabling state is `Unreceived`, and no edge returns to `Unreceived`. -/
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
      <- L2InteropHandler:118       the SOLE caller of give, inside _handleCallValue
      <- InteropHandlerBase:279     the SOLE caller of _handleCallValue, inside _executeCalls

and `_executeCalls` pays call `i` exactly when that call is being executed:

    if (!_executeAllCalls) { if (_providedCallStatus[i] != Executed) continue; }   // unbundled route
    _handleCallValue(interopCall.value, _sourceChainId);

Both routes record the payment in the SAME place — `callStatus[bundleHash][i] = Executed`
(`InteropHandlerBase:131` and `L2InteropHandler:89` for the whole bundle, `:208` per call).  So "paid"
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


/-- The gap the whole-bundle route leaves at the call level, stated so the reliance on bundle status is
explicit: `Unprocessed → Executed` and a re-entry attempt are not distinguished by anything in the
per-call machine when `_executeAllCalls` is true, since that path writes the status without reading it.
`routes_exclusive` is what closes it.

CONFIRMED AGAINST THE COMPILED YUL rather than inferred from the Solidity.  The whole-bundle route's
status write is `for_4476381376322263891` in `InteropHandler`, whose body is:

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

All three blocks of that loop body now have proven specs
(`block_2862394693737849679`, `block_5612315614323394231`, `block_8179420195348823280`); the loop's own
closed form is the remaining piece. -/
abbrev Properties.wholeBundle_route_does_not_check_callStatus :=
  CallReach .Unprocessed .Executed ∧ ¬ CallStep .Executed .Executed


/-- **NO INFLATION.**  Whatever the per-call outcomes, the destination releases no more than the source
collected for that bundle. -/
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


/-! ### Scope: where the no-inflation result is non-trivial

`_validateAtomicBundle` rejects any call carrying native value:

    if (_bundle.calls[i].value != 0) revert AtomicBundleCallCarriesValue(i, _bundle.calls[i].value);

and `calls[i].value` is exactly the `interopCallValue` summed into `totalBurnedCallsValue`
(`InteropCenter.sol:738`).  So for an ATOMIC bundle every entry of the ledger is zero and both sums
vanish — the inequality holds trivially and says nothing.

The result above is therefore about the PUBLIC interop path.  That is not a defect in either: atomic
legs deliberately move value through the asset router as `indirectCallMessageValue`, precisely because
`IAtomicRecoverable.recoverAtomicCall` can reverse an asset-router deposit but cannot reverse a
base-token transfer.  Banning native value is what keeps the timeout path meaningful for them, and
`RecoveryLimits` is where that path's own limits live.

Stating this because the inequality reads like a global conservation law and is not one. -/

/-- An atomic bundle's ledger is all zeros, so both sides vanish. -/
abbrev Properties.atomic_ledger_trivial (l : Ledger) (h : ∀ p ∈ l, p.1 = 0) :=
  releasedSum l = 0 ∧ collectedSum l = 0


/-- **AN ATOMIC BUNDLE HAS ONE ROUTE.**  From fresh, the only reachable states are fresh and
delivered. -/
abbrev Properties.atomic_reach_two_states {t : Status} (h : AtomicReach .Unreceived t) :=
  t = .Unreceived ∨ t = .FullyExecuted


/-- **SO IT IS NEVER UNBUNDLED**, and `routes_exclusive` holds vacuously for it — the per-call route
does not exist on this path. -/
abbrev Properties.atomic_never_unbundled :=
  ¬ AtomicReach .Unreceived .Unbundled


/-- And delivery-once for an atomic bundle needs only the BUNDLE machine: `FullyExecuted` is terminal
here too, since `AtomicStep` has no edge out of it. -/
abbrev Properties.atomic_delivery_terminal {t : Status} :=
  ¬ AtomicStep .FullyExecuted t


end AttackVectors.BundleStatusMachine
