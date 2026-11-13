import EraSpec.Contracts.Governance.Specs.Timelock

/-!
# Properties: the Governance timelock

Statements about `EraSpec.Contracts.Governance.Specs.Timelock`.  Proofs are in
`EraSpec.Contracts.Governance.Proofs.Timelock`.

Run-level results quantify over every reachable state (`Reach`): any interleaving of every entry
point by any outside caller, with arbitrary re-entrant calls inside each execution, and the clock
moving forward between transactions.  "The log" is the ghost event log of that run
(`Specs/Timelock.lean`, "The ghost log"); "an entry of the log" means `log = pre ++ x :: post`,
and `pre` is everything that happened before it.

* `OperationStateMatchesHistory`: the contract's `getOperationState` is exactly what the log says:
  unset (never executed and no outstanding schedule), done (executed), or waiting/ready by the
  outstanding schedule's time plus delay.  The stored `minDelay` is the last one logged.
* `DoneIffExecutedOnce`: an id is executed at most once in any run, and is done exactly when it was.
* `DoneIsPermanent`: a done id stays done, and is never executed again, along any later run.
* `ExecutionRespectsTimelock` (headline): every execution has an outstanding schedule made by an
  earlier `scheduleTransparent`/`scheduleShadow`, with delay at least the minimum delay then in
  force; a non-instant execution happens no earlier than schedule time plus delay.
* `ScheduleRespectsMinDelay`: every schedule's delay is at least the minimum delay in force, and
  only an id that is neither pending nor ever executed can be scheduled.
* `CancelOnlyPending`: every cancel hits a pending, never-executed id.
* `PredecessorExecutedFirst`: an operation with a nonzero predecessor runs only after its
  predecessor's execution.
* `CallerAuthority` and `ExecuteAuthority`: who may call what (one call).
* `ConfigOnlyThroughExecution`: a transaction that changes `minDelay` or `securityCouncil` is an
  execution of an operation (`onlySelf` is reachable only from `_execute`).
* `ReadyIsExecutable`: a ready operation whose predecessor is done can be executed by the owner.
* `SelfUpdatesTouchOnlyTheirField`: `updateDelay` and `updateSecurityCouncil` write only their own
  variable, so already scheduled operations keep their times ("for future operations", G:286).

Load-bearing checks and boundaries:

* `NoRecheckDoubleExecution` (countermodel): without the re-check after the calls (G:197-201), a
  re-entrant execution of the same operation makes it run twice.
* `LowClockScheduleMarksDone` (boundary; refutes G:40's reading "1 means the operation is already
  executed" for `block.timestamp ≤ 1`): at a clock of 1, `scheduleShadow(id, 0)` marks `id` done
  without execution, and an operation with that predecessor then runs.  On any real chain the clock
  is far above 1; `Reach` assumes `≥ 2`.

Witness: `TimelockRunSatisfiable`.
-/

namespace Contracts.Governance

/-- **THE OPERATION STATE IS THE LOG'S.**  In every reachable state, `getOperationState` of every id
is the one the log predicts (`stateFromLog`): with no outstanding schedule it is `unset` if the id
was never executed and `done` otherwise; with an outstanding schedule at time `t` with delay `d` it
is `waiting` before `t + d` and `ready` from then on.  The stored `minDelay` is the last minimum delay the log set, and
the clock is at least 2. -/
def Properties.OperationStateMatchesHistory : Prop :=
  ∀ (e : Env) (s : State) (log : List Ev), Reach e s log →
    s.minDelay = lastDelay log ∧ 2 ≤ s.now.val ∧
    ∀ id : OpId, getOperationState s id = stateFromLog s.now id log

/-- **EXECUTED AT MOST ONCE; DONE EXACTLY WHEN EXECUTED.**  In every reachable state, every id has
been executed at most once in the run, and it is done exactly when it has been executed. -/
def Properties.DoneIffExecutedOnce : Prop :=
  ∀ (e : Env) (s : State) (log : List Ev), Reach e s log → ∀ id : OpId,
    execCount id log ≤ 1 ∧ (isOperationDone s id = true ↔ execCount id log = 1)

/-- **DONE IS PERMANENT.**  From a reachable state, along any further run, a done id stays done and
the run never executes it again. -/
def Properties.DoneIsPermanent : Prop :=
  ∀ (e : Env) (s t : State) (log evs : List Ev), Reach e s log → TopRun e s evs t →
    ∀ id : OpId, isOperationDone s id = true →
      isOperationDone t id = true ∧ execCount id evs = 0

/-- **EVERY EXECUTION RESPECTS THE TIMELOCK.**  For every execution entry in a reachable log, of
`id` at time `τ`: before it, `id` had an outstanding schedule at time `t ≤ τ` with delay `d`, made
while the minimum delay in force was `m ≤ d`.  If the execution was not `executeInstant`, then
`t + d ≤ τ`: the full delay had passed. -/
def Properties.ExecutionRespectsTimelock : Prop :=
  ∀ (e : Env) (s : State) (log : List Ev), Reach e s log →
    ∀ (pre post : List Ev) (id p : OpId) (instant : Bool) (τ : UInt256),
      log = pre ++ .executed id p instant τ :: post →
      ∃ t d m, pendingSched id pre = some (t, d, m) ∧ m ≤ d ∧ t.val ≤ τ.val ∧
        (instant = false → t.val + d.val ≤ τ.val)

/-- **SCHEDULES RESPECT THE MINIMUM DELAY AND ARE FRESH.**  For every schedule entry in a reachable
log, its delay is at least the minimum delay in force (`lastDelay pre`), and the id had no
outstanding schedule and had never been executed. -/
def Properties.ScheduleRespectsMinDelay : Prop :=
  ∀ (e : Env) (s : State) (log : List Ev), Reach e s log →
    ∀ (pre post : List Ev) (id : OpId) (t d : UInt256),
      log = pre ++ .scheduled id t d :: post →
      lastDelay pre ≤ d ∧ pendingSched id pre = none ∧ execCount id pre = 0

/-- **ONLY PENDING OPERATIONS ARE CANCELLED.**  For every cancel entry in a reachable log, the id
had an outstanding schedule and had never been executed. -/
def Properties.CancelOnlyPending : Prop :=
  ∀ (e : Env) (s : State) (log : List Ev), Reach e s log →
    ∀ (pre post : List Ev) (id : OpId), log = pre ++ .cancelled id :: post →
      pendingSched id pre ≠ none ∧ execCount id pre = 0

/-- **PREDECESSORS RUN FIRST.**  For every execution entry in a reachable log whose predecessor `p`
is nonzero, an execution of `p` appears earlier in the log. -/
def Properties.PredecessorExecutedFirst : Prop :=
  ∀ (e : Env) (s : State) (log : List Ev), Reach e s log →
    ∀ (pre post : List Ev) (id p : OpId) (instant : Bool) (τ : UInt256),
      log = pre ++ .executed id p instant τ :: post → p ≠ 0 →
      ∃ q i τ', Ev.executed p q i τ' ∈ pre

/-- **WHO MAY CALL WHAT.**  A successful call (top level or re-entrant) to `scheduleTransparent`,
`scheduleShadow`, `cancel`, `transferOwnership` or `renounceOwnership` is by the owner;
`updateDelay` and `updateSecurityCouncil` by Governance itself; `acceptOwnership` by the pending
owner. -/
def Properties.CallerAuthority : Prop :=
  ∀ (e : Env) (caller : Address) (s t : State) (ev : Ev),
    (∀ op d, (Entry.scheduleTransparent op d).run e caller s = some (ev, t) → caller = s.owner) ∧
    (∀ id d, (Entry.scheduleShadow id d).run e caller s = some (ev, t) → caller = s.owner) ∧
    (∀ id, (Entry.cancel id).run e caller s = some (ev, t) → caller = s.owner) ∧
    (∀ a, (Entry.transferOwnership a).run e caller s = some (ev, t) → caller = s.owner) ∧
    (Entry.renounceOwnership.run e caller s = some (ev, t) → caller = s.owner) ∧
    (∀ d, (Entry.updateDelay d).run e caller s = some (ev, t) → caller = e.self) ∧
    (∀ a, (Entry.updateSecurityCouncil a).run e caller s = some (ev, t) → caller = e.self) ∧
    (Entry.acceptOwnership.run e caller s = some (ev, t) → caller = s.pendingOwner)

/-- **WHO MAY EXECUTE WHAT.**  An execution passes its entry checks only if: for `executeInstant`
the caller is the security council and the operation is pending (waiting or ready); for `execute`
the caller is the owner or the security council and the operation is ready; in both cases the
predecessor is zero or done. -/
def Properties.ExecuteAuthority : Prop :=
  ∀ (e : Env) (instant : Bool) (caller : Address) (s : State) (op : Operation),
    preCheck e instant caller s op = true →
    (instant = true → caller = s.securityCouncil ∧ isOperationPending s (e.hashOp op) = true) ∧
    (instant = false → (caller = s.owner ∨ caller = s.securityCouncil) ∧
        isOperationReady s (e.hashOp op) = true) ∧
    (op.predecessor = 0 ∨ isOperationDone s op.predecessor = true)

/-- **CONFIGURATION CHANGES ONLY THROUGH AN EXECUTION.**  From a reachable state, a transaction that
changes `minDelay` or `securityCouncil` is an execution: its last log entry is an
`OperationExecuted`. -/
def Properties.ConfigOnlyThroughExecution : Prop :=
  ∀ (e : Env) (s t : State) (log evs : List Ev), Reach e s log → TopStep e s evs t →
    (t.minDelay ≠ s.minDelay ∨ t.securityCouncil ≠ s.securityCouncil) →
    ∃ id p instant τ, evs.getLast? = some (.executed id p instant τ)

/-- **SELF-UPDATES TOUCH ONLY THEIR FIELD.**  A successful `updateDelay(d)` sets `minDelay` to `d`
and changes nothing else (so every scheduled timestamp is kept); `updateSecurityCouncil(a)` sets
the council to `a` and changes nothing else. -/
def Properties.SelfUpdatesTouchOnlyTheirField : Prop :=
  ∀ (e : Env) (caller : Address) (s t : State) (ev : Ev),
    (∀ d, (Entry.updateDelay d).run e caller s = some (ev, t) → t = { s with minDelay := d }) ∧
    (∀ a, (Entry.updateSecurityCouncil a).run e caller s = some (ev, t) →
      t = { s with securityCouncil := a })

/-- **A READY OPERATION CAN BE EXECUTED.**  From any state, if an operation is ready and its
predecessor is zero or done, and the owner is not Governance itself, then the owner's `execute` with
calls that do not re-enter Governance is a transaction, and it leaves the operation done. -/
def Properties.ReadyIsExecutable : Prop :=
  ∀ (e : Env) (s : State) (op : Operation), s.owner ≠ e.self →
    isOperationReady s (e.hashOp op) = true → predecessorDone s op.predecessor = true →
    TopStep e s [.executed (e.hashOp op) op.predecessor false s.now] (markDone s (e.hashOp op)) ∧
      isOperationDone (markDone s (e.hashOp op)) (e.hashOp op) = true

/-- **COUNTERMODEL: THE RE-CHECK IS LOAD-BEARING.**  In the variant without the re-check after the
calls (G:197-201, G:222-226), some reachable log executes one id twice: the operation's calls
re-enter `execute` for the same operation, which completes, and the outer call then completes too.
The source's `DoneIffExecutedOnce` rules this out. -/
def Properties.NoRecheckDoubleExecution : Prop :=
  ∃ (e : Env) (s : State) (log : List Ev) (id : OpId), ReachWith false e s log ∧ execCount id log = 2

/-- **BOUNDARY: AT A CLOCK OF 1, SCHEDULING CAN MARK DONE.**  G:40 says timestamp `1` "means the
operation is already executed".  That fails if `block.timestamp + _delay = 1`: from a state at clock
1 with minimum delay 0, a run of three transactions and a clock tick schedules a predecessor that
becomes done without being executed, then executes an operation that names it as predecessor.
`Reach` excludes this by starting at a clock of at least 2; real chains are far above it. -/
def Properties.LowClockScheduleMarksDone : Prop :=
  ∃ (e : Env) (s t : State) (evs : List Ev) (op : Operation),
    s.now.val = 1 ∧ TopRun e s evs t ∧ op.predecessor ≠ 0 ∧
    isOperationDone s op.predecessor = false ∧ execCount op.predecessor evs = 0 ∧
    isOperationDone t op.predecessor = true ∧ execCount (e.hashOp op) evs = 1

/-- **WITNESS.**  A reachable run in which: an operation `a` is executed through the timelock by the
owner, and its calls re-enter Governance to change `minDelay`; an operation `b` with predecessor `a`
is executed instantly by the security council before its scheduled time; both end done. -/
def Properties.TimelockRunSatisfiable : Prop :=
  ∃ (e : Env) (s : State) (log : List Ev) (a b pa : OpId) (ta tb t d d0 : UInt256),
    Reach e s log ∧ a ≠ 0 ∧ a ≠ b ∧
    Ev.executed a pa false ta ∈ log ∧ Ev.executed b a true tb ∈ log ∧
    Ev.scheduled b t d ∈ log ∧ tb.val < t.val + d.val ∧
    Ev.minDelayChanged d0 s.minDelay ∈ log ∧ d0 ≠ s.minDelay ∧
    isOperationDone s a = true ∧ isOperationDone s b = true

end Contracts.Governance
