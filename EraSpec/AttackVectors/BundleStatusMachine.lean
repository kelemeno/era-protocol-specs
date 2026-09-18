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

/-! ## Safety -/

/-- **DELIVERY IS TERMINAL.**  No guard admits `FullyExecuted`, so nothing follows it — the CEI write
that precedes the calls is what makes a reentrant or repeated execution hit a closed door. -/
theorem fullyExecuted_terminal {t : Status} : ¬ Step .FullyExecuted t := by
  rintro ⟨⟩

/-- Hence a delivered bundle stays delivered. -/
theorem reach_from_fullyExecuted {t : Status} (h : Reach .FullyExecuted t) : t = .FullyExecuted := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact absurd (ih ▸ hstep) fullyExecuted_terminal

/-- **THE UNBUNDLED ROUTE IS ABSORBING TOO.**  Once unbundled, the whole-bundle execution path is
closed: the only edge out of `Unbundled` returns to `Unbundled`. -/
theorem reach_from_unbundled {t : Status} (h : Reach .Unbundled t) : t = .Unbundled := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    cases hstep
    rfl

/-- **THE TWO DELIVERY ROUTES EXCLUDE EACH OTHER.**  A bundle cannot be both executed as a whole and
unbundled for per-call execution, in either order — so the same call cannot be delivered twice by
taking one route and then the other. -/
theorem routes_exclusive :
    (¬ Reach .FullyExecuted .Unbundled) ∧ (¬ Reach .Unbundled .FullyExecuted) := by
  constructor
  · intro h; exact absurd (reach_from_fullyExecuted h) (by decide)
  · intro h; exact absurd (reach_from_unbundled h) (by decide)

/-- Both delivery states are reachable from a fresh bundle, so the exclusivity above is not vacuous —
each route is genuinely available until the other is taken. -/
theorem both_routes_available :
    Reach .Unreceived .FullyExecuted ∧ Reach .Unreceived .Unbundled :=
  ⟨.tail (.refl _) .executeFresh, .tail (.tail (.refl _) .verify) .unbundleFirst⟩

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
theorem verified_blocks_atomic_execution : ¬ Step .Verified .Unreceived := by
  rintro ⟨⟩

/-- And no state returns to `Unreceived` at all: it is the machine's unique initial state, so a bundle
that leaves it can never be treated as fresh again. -/
theorem unreceived_unreachable {s : Status} : ¬ Step s .Unreceived := by
  cases s <;> rintro ⟨⟩

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

/-- **A CALL IS EXECUTED AT MOST ONCE.**  `Executed` has no outgoing edge: the `require(recorded ==
Unprocessed)` on the execute branch is what makes a second execution of the same call impossible, no
matter how many `unbundleBundle` transactions are submitted. -/
theorem callExecuted_terminal {t : CallStatus} : ¬ CallStep .Executed t := by
  rintro ⟨⟩

theorem callReach_from_executed {t : CallStatus} (h : CallReach .Executed t) : t = .Executed := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact absurd (ih ▸ hstep) callExecuted_terminal

/-- **AND A CANCELLED CALL IS NEVER EXECUTED.**  The execute branch demands `Unprocessed`, so
cancellation is a one-way door — `Cancelled` only loops to itself. -/
theorem callReach_from_cancelled {t : CallStatus} (h : CallReach .Cancelled t) : t = .Cancelled := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    cases hstep
    rfl

/-- The per-call counterpart of `routes_exclusive`: executed and cancelled are mutually unreachable. -/
theorem call_outcomes_exclusive :
    (¬ CallReach .Executed .Cancelled) ∧ (¬ CallReach .Cancelled .Executed) := by
  constructor
  · intro h; exact absurd (callReach_from_executed h) (by decide)
  · intro h; exact absurd (callReach_from_cancelled h) (by decide)

/-- Both outcomes are reachable from a fresh call, so the exclusivity is not vacuous. -/
theorem call_outcomes_available :
    CallReach .Unprocessed .Executed ∧ CallReach .Unprocessed .Cancelled :=
  ⟨.tail (.refl _) .execute, .tail (.refl _) .cancel⟩

/-- **CANCELLATION IS IDEMPOTENT, EXECUTION IS NOT.**  Re-cancelling is a legal edge; there is no
`Executed -> Executed`.  The asymmetry is deliberate in the source (a resubmitted status array must not
revert on entries already cancelled) and it is why `Cancelled` needs its self-loop while `Executed`
does not. -/
theorem cancel_idempotent_execute_not :
    CallStep .Cancelled .Cancelled ∧ ¬ CallStep .Executed .Executed :=
  ⟨.cancelAgain, callExecuted_terminal⟩

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
theorem value_released_at_most_once :
    (∀ t : CallStatus, ¬ CallStep .Executed t) ∧
      (¬ Reach .FullyExecuted .Unbundled ∧ ¬ Reach .Unbundled .FullyExecuted) :=
  ⟨fun _ => callExecuted_terminal, routes_exclusive⟩

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
theorem wholeBundle_route_does_not_check_callStatus :
    CallReach .Unprocessed .Executed ∧ ¬ CallStep .Executed .Executed :=
  ⟨.tail (.refl _) .execute, callExecuted_terminal⟩

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

/-- **NO INFLATION.**  Whatever the per-call outcomes, the destination releases no more than the source
collected for that bundle. -/
theorem released_le_collected (l : Ledger) : releasedSum l ≤ collectedSum l := by
  induction l with
  | nil => simp [releasedSum, collectedSum]
  | cons hd tl ih =>
    obtain ⟨v, st⟩ := hd
    by_cases h : st = CallStatus.Executed <;>
      simp [releasedSum, collectedSum, h] <;> omega

/-- **AND THE BOUND IS TIGHT.**  A bundle whose calls all execute releases exactly what was collected,
so the inequality is not slack hiding a systematic shortfall. -/
theorem released_eq_collected_of_all_executed :
    ∀ l : Ledger, (∀ p ∈ l, p.2 = CallStatus.Executed) → releasedSum l = collectedSum l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons hd tl ih =>
    intro h
    obtain ⟨v, st⟩ := hd
    have hhd : st = CallStatus.Executed := h (v, st) (List.mem_cons_self _ _)
    have htl : ∀ p ∈ tl, p.2 = CallStatus.Executed := fun p hp => h p (List.mem_cons_of_mem _ hp)
    simp [releasedSum, collectedSum, hhd, ih htl]

/-- The shortfall named: value collected for calls that did not execute.  Recorded so the gap is
visible rather than implied by the inequality. -/
theorem shortfall_is_unexecuted (v : ℕ) (tl : Ledger) :
    collectedSum ((v, CallStatus.Cancelled) :: tl) - releasedSum ((v, CallStatus.Cancelled) :: tl)
      = v + (collectedSum tl - releasedSum tl) := by
  have h := released_le_collected tl
  simp [releasedSum, collectedSum]
  omega

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
theorem atomic_ledger_trivial (l : Ledger) (h : ∀ p ∈ l, p.1 = 0) :
    releasedSum l = 0 ∧ collectedSum l = 0 := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons hd tl ih =>
    obtain ⟨v, st⟩ := hd
    have hv : v = 0 := h (v, st) (List.mem_cons_self _ _)
    have htl := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    subst hv
    constructor
    · by_cases hst : st = CallStatus.Executed <;> simp [releasedSum, hst, htl.1]
    · simp [collectedSum, htl.2]

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
knowing which half is load-bearing where. -/

/-- The transitions available to an ATOMIC bundle: `verify` is unreachable (no L1 proof exists), and
with it every edge that needs `Verified`. -/
inductive AtomicStep : Status → Status → Prop
  | executeAtomic : AtomicStep .Unreceived .FullyExecuted

inductive AtomicReach : Status → Status → Prop
  | refl (s : Status) : AtomicReach s s
  | tail {a b c : Status} : AtomicReach a b → AtomicStep b c → AtomicReach a c

/-- **AN ATOMIC BUNDLE HAS ONE ROUTE.**  From fresh, the only reachable states are fresh and
delivered. -/
theorem atomic_reach_two_states {t : Status} (h : AtomicReach .Unreceived t) :
    t = .Unreceived ∨ t = .FullyExecuted := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep _ => cases hstep; exact Or.inr rfl

/-- **SO IT IS NEVER UNBUNDLED**, and `routes_exclusive` holds vacuously for it — the per-call route
does not exist on this path. -/
theorem atomic_never_unbundled : ¬ AtomicReach .Unreceived .Unbundled := by
  intro h
  rcases atomic_reach_two_states h with h1 | h1 <;> exact absurd h1 (by decide)

/-- And delivery-once for an atomic bundle needs only the BUNDLE machine: `FullyExecuted` is terminal
here too, since `AtomicStep` has no edge out of it. -/
theorem atomic_delivery_terminal {t : Status} : ¬ AtomicStep .FullyExecuted t := by
  rintro ⟨⟩

end AttackVectors.BundleStatusMachine
