import EraSpec.Contracts.Governance.Specs.Timelock
import EraSpec.Core.Headline

/-!
# Properties: what the `Governance` timelock guarantees, across re-entrant execution

Statements about `EraSpec.Contracts.Governance.Specs.Timelock` (source `Governance.sol` at
`draft/v0.35.0` `b17415d2`; OpenZeppelin v4.9.6 `Ownable2Step`). Proofs are in
`EraSpec.Contracts.Governance.Proofs.Timelock`.

Every general result quantifies over every target behaviour (`Callee` trees: re-entrant calls
to any entry point, as any caller but Governance itself, at any depth, caught or not), every
self-call decoder `Env.dec`, every hash `Env.H`, and every budget. None takes a hash premise.
The witnesses and countermodels are concrete runs.
The run results are about the committed log of any sequence of transactions (`submitAll`, in
the deployed order unless the result says either variant); the frame results are about one
committed frame anywhere in a transaction, nested or not.

## The guards

* `EntryGuards`: each entry point's transcribed guard and write, in either variant.
  `EntryGuardsWitness`: runs in which every entry point commits, so no guard is vacuous.

## The state is the log

* `StateIsLogReplay`: in either variant, the state a committed frame or a sequence of
  transactions leaves is the replay of its committed log (`replay`: each entry's write,
  `Effect.apply`, applied in order). So `getOperationState` of every id, the owner, the pending
  owner, the council and `minDelay` are functions of the start state and the log
  (`StateIsLogReplayWitness`).
* `LoggedEntriesPassedTheirChecks`: every logged entry satisfies `Effect.CheckedAt` on the
  state its predecessors in the log replay to. A schedule found its id `Unset`, recorded the
  stored `minDelay` and had a delay at least that; a cancel found its id pending; an execution
  of `op` has id `H op`, and after the operation's calls its predecessor was zero or `Done` and
  its id pending (ready, for `execute`); a `minDelay` or council change recorded the stored old
  value; an ownership transfer went to the zero address or to the pending owner
  (`LoggedEntriesPassedTheirChecksWitness`: checks on entries made re-entrantly).
* `NothingAfterExecution`: no entry after an execution of `x` schedules, cancels, delivers or
  executes `x` (`NothingAfterExecutionWitness`).

## (a) Once only

* `DoneIsPermanent`: in either variant, a `Done` operation (`timestamps = 1`) stays `Done`
  across every frame and every sequence of transactions (`DoneIsPermanentWitness`: a later
  schedule of an executed operation commits nothing).
* `OnceOnly` (headline): in the committed log of any sequence of transactions, from any
  state, no operation id is executed twice and no call of an operation is delivered twice.
  `CommittedRunsWereOpen`: each logged delivery or execution of `x` was not `Done` at the
  start of the sequence, and `x` is `Done` at its end.
* `DoneIffExecuted`: along transactions whose block times are all at least `2`, an id ends
  `Done` exactly when it was `Done` at the start or the log executes it, at most once
  (`DoneIffExecutedWitness`; `SentinelCollision` shows the time premise is needed).
* `ExecutionRunsEachCallOnce`: in the log of a committed `execute(op)`/`executeInstant(op)`,
  the deliveries and executions of its id are exactly the deliveries of its calls
  `0, …, n-1`, in order, then its own execution; the id ends `Done`. Re-entrant frames inside
  it deliver and execute other ids only (they may cancel and schedule its id: see (f)).

## (e) The re-check

* `ReentrantReexecutionReverts`: if the calls of an execution of `op` commit, inside them,
  an execution of `op`'s id (re-entrantly, by any caller, through any operation with that
  id), the outer execution reverts: at the latest, its re-check (:199-201, :224-226) finds the
  id `Done`.
* `ReentrantReexecutionWitness`: a concrete case. The inner execution commits inside the
  calls, the outer reverts, and the transaction commits nothing.
* **Countermodel** `WithoutRecheckReexecutes`: without the re-checks, the same transaction
  commits the operation's call twice and its execution twice. `WithoutRecheckAnyOpRunsTwice`:
  the same holds for every operation with at least one call, all to other contracts, from every
  state where an owner other than Governance may execute it; in the source, that transaction
  commits nothing (`WithoutRecheckAnyOpRunsTwiceWitness`: its premises hold).

## (b) The delay, and (h) the published payload

* `OwnerPathWaited`: from a state with nothing pending (the constructor's), every committed
  `execute` (the owner's and the council's delayed path) of an id at time `τ` is preceded in
  the log by a schedule of that id. Its last such schedule had a delay at least the
  `minDelay` in force when it was scheduled, and it was made at least that delay before `τ`.
  Only `executeInstant` skips this, and only the security council can call it (`EntryGuards`):
  `EarlyExecutionIsInstant` says every execution before its schedule's ready time was instant
  (`EarlyExecutionIsInstantWitness` shows one).
* `TransparentBinding`: in the same setting, every committed execution of `op` (either
  path) has id `H op`. Its last schedule had a delay at least the `minDelay` then, and if that
  schedule was transparent, it published `op`, or a different operation `op₀` with
  `H op₀ = H op`. That collision is on two logged values: the payload in the schedule event,
  and the executed calldata.
* Witnesses: `OwnerPathWaitedWitness` (the bound is attained), `TransparentBindingWitness`,
  and `TransparentCollisionExecutesAnotherOp`, which shows the collision disjunct can fire.
* `OutgoingCallsWaitedOrInstant` (headline): in the same setting, every call Governance commits
  is followed, later in the log, by an execution of its id (the only one, by `OnceOnly`) that
  was `executeInstant`, or whose last schedule waited its delay as in `OwnerPathWaited`
  (`OutgoingCallsWaitedOrInstantWitness`: both cases).
* `ExecutionNotBeforeSchedule`: when block times never decrease, an execution on either path
  comes no earlier than its last schedule (`ExecutionNotBeforeScheduleWitness`, which also shows
  an instant execution timed before its schedule when the times are out of order).

## (c) Predecessors, and (d) the sentinel

* `PredecessorDone`: in any sequence of transactions whose block times are all at least `2`,
  every committed execution of an operation with a nonzero predecessor `p` is preceded in the
  log by an execution of `p`, or `p` was already `Done` at the start.
* `PredecessorDoneOrSentinel`: the same with no premise on times. The extra case is a
  schedule of `p` logged earlier whose time plus delay is `1`, the executed sentinel (:125).
* `PredecessorDoneWitness`: the premises hold and the predecessor case fires.
* **Countermodel** `SentinelCollision`: a schedule at `τ + delay = 1` marks the operation
  `Done` without executing it (and at `τ + delay = 0` leaves it `Unset`). At time `1` with
  `minDelay = 0`, a shadow schedule of id `14` with delay `0` lets a successor naming `14`
  pass `_checkPredecessorDone` though `14` never ran. Mainnet block times are far above `1`.

## (f) Cancelling an operation while it runs

* `InFlightCancelNeedsReschedule`: in a committed execution of `op`, every cancel of `op`'s id
  is followed, later in that execution's log, by a schedule of the id. So a cancel made from
  inside the operation's own calls never stands: either the execution reverts and takes the
  cancel with it, or the id was scheduled again and the execution overwrites that schedule
  with `Done` (`ExecutionRunsEachCallOnce`).
* **Countermodel** `InFlightCancelIneffective`: the owner's `cancel` succeeds in its own frame
  during the council's `executeInstant`, whose call loop then commits with the id `Unset`. The
  re-check reverts the execution, so the transaction commits nothing, the operation is still
  pending afterwards, and the council executes it later. When the owner also schedules it
  again inside the same execution, the execution commits, and the new schedule is overwritten.

## (g) Raising the delay

* `MinDelayChangeKeepsTimestamps`: a committed `updateDelay` leaves every `timestamps` entry as
  it was (it writes only `minDelay`, `EntryGuards`), and no operation state reads `minDelay`.
  Only `_schedule` does (:249).
* **Countermodel** `DelayRaiseNotRetroactive`: an operation scheduled with the old minimum
  delay `10` runs `10` seconds later, after an operation raised the minimum to `100`. A new
  schedule with delay `10` is then refused.

## Authority

* `ConfigChangesNeedExecution`: a transaction that changes `minDelay` or the security council
  is a call of `execute(op)` or `executeInstant(op)`, and its committed log ends with that
  execution: `onlySelf` is reachable only through `_execute`
  (`ConfigChangesNeedExecutionWitness`).
* `DeliveriesBelongToExecutions`: every call Governance commits (`delivered x i`) is followed,
  later in the committed log, by an execution of `x`.
* `NewOwnerWasNominated`: every ownership transfer to a nonzero address `a` in the committed
  log comes after a nomination of `a` (`OwnershipTransferStarted`, which only the owner can
  log, `EntryGuards`), with no nomination or ownership transfer in between; or nothing before
  it wrote the pending owner and `a` was the pending owner at the start. This holds for
  acceptances made re-entrantly, inside an execution (`NewOwnerWasNominatedWitness`).

## Enabledness

* `ReadyIsExecutable`: an operation whose calls all go to other contracts, `Ready` at `τ` with
  its predecessor zero or `Done`, is executed by a transaction of the owner or the council
  (not Governance itself) at `τ` whose targets return without calling back.
  `PendingIsInstantlyExecutable`: the same for a pending operation, `executeInstant` and the
  council. Witnesses: `ReadyIsExecutableWitness`, `PendingIsInstantlyExecutableWitness`, with
  a nonzero `Done` predecessor.
-/

namespace Contracts.Governance

/-! ## The guards -/

/-- **EACH ENTRY POINT'S GUARD AND WRITE** (success implies the guard), at any time, budget and
variant:
* a schedule needs the owner, an `Unset` id, `delay ≥ minDelay` and no overflow, and writes
  `timestamps[id] = τ + delay`;
* `cancel` needs the owner and a pending id, and deletes it;
* `execute` needs the owner or the council, the predecessor done or zero, and the id ready; it
  leaves the id `Done`;
* `executeInstant` needs the council, the predecessor done or zero, and the id pending; it
  leaves the id `Done`;
* `updateDelay` and `updateSecurityCouncil` need Governance itself as the caller, and write
  only their field;
* `transferOwnership` and `renounceOwnership` need the owner; `acceptOwnership` needs the
  pending owner, and makes it the owner. -/
@[headline] def Properties.EntryGuards : Prop :=
  ∀ (v : Variant) (E : Env) (τ n : ℕ) (c : Address) (cbs : List Callee) (s s' : State)
    (l : List Effect),
    (∀ op d, exec v E τ n (.entry c (.scheduleTransparent op d) cbs) s = some (s', l) →
      c = s.owner ∧ s.ts (E.H op) = 0 ∧ s.minDelay ≤ d ∧ τ + d < UInt256.size ∧
        s' = s.setTs (E.H op) (τ + d) ∧ l = [.scheduled (E.H op) τ d s.minDelay (some op)]) ∧
    (∀ x d, exec v E τ n (.entry c (.scheduleShadow x d) cbs) s = some (s', l) →
      c = s.owner ∧ s.ts x = 0 ∧ s.minDelay ≤ d ∧ τ + d < UInt256.size ∧
        s' = s.setTs x (τ + d) ∧ l = [.scheduled x τ d s.minDelay none]) ∧
    (∀ x, exec v E τ n (.entry c (.cancel x) cbs) s = some (s', l) →
      c = s.owner ∧ s.ts x ≠ 0 ∧ s.ts x ≠ EXECUTED ∧ s' = s.setTs x 0 ∧ l = [.cancelled x]) ∧
    (∀ op, exec v E τ n (.entry c (.execute op) cbs) s = some (s', l) →
      (c = s.owner ∨ c = s.council) ∧ (op.predecessor = 0 ∨ s.ts op.predecessor = EXECUTED) ∧
        s.ts (E.H op) ≠ 0 ∧ s.ts (E.H op) ≠ EXECUTED ∧ s.ts (E.H op) ≤ τ ∧
        s'.ts (E.H op) = EXECUTED) ∧
    (∀ op, exec v E τ n (.entry c (.executeInstant op) cbs) s = some (s', l) →
      c = s.council ∧ (op.predecessor = 0 ∨ s.ts op.predecessor = EXECUTED) ∧
        s.ts (E.H op) ≠ 0 ∧ s.ts (E.H op) ≠ EXECUTED ∧ s'.ts (E.H op) = EXECUTED) ∧
    (∀ d, exec v E τ n (.entry c (.updateDelay d) cbs) s = some (s', l) →
      c = E.self ∧ s' = { s with minDelay := d }) ∧
    (∀ a, exec v E τ n (.entry c (.updateSecurityCouncil a) cbs) s = some (s', l) →
      c = E.self ∧ s' = { s with council := a }) ∧
    (∀ a, exec v E τ n (.entry c (.transferOwnership a) cbs) s = some (s', l) →
      c = s.owner ∧ s' = { s with pendingOwner := a }) ∧
    (exec v E τ n (.entry c .acceptOwnership cbs) s = some (s', l) →
      c = s.pendingOwner ∧ s' = { s with owner := c, pendingOwner := 0 }) ∧
    (exec v E τ n (.entry c .renounceOwnership cbs) s = some (s', l) →
      c = s.owner ∧ s' = { s with owner := 0, pendingOwner := 0 })

/-- **EVERY ENTRY POINT'S PREMISE IS SATISFIABLE.** From fresh Governance:
`timelockOwnershipRun` commits a nomination, its acceptance, a schedule, an execution whose
self-call changes the council, and a renunciation; `timelockCancelRescheduleRun` commits a
cancel, a shadow schedule and an instant execution; `timelockRaiseRun` commits a self-called
`updateDelay`. -/
@[witness] def Properties.EntryGuardsWitness : Prop :=
  (submitAll .deployed timelockEnv timelockInit timelockOwnershipRun).2 =
    [.ownershipTransferStarted 5, .ownershipTransferred 5,
      .scheduled 16 100 10 10 (some timelockCouncilOp), .delivered 16 0, .councilChanged 2 3,
      .executed 16 timelockCouncilOp 110 false, .ownershipTransferred 0] ∧
  (submitAll .deployed timelockEnv timelockInit timelockOwnershipRun).1.owner = 0 ∧
  (submitAll .deployed timelockEnv timelockInit timelockOwnershipRun).1.council = 3 ∧
  (submitAll .deployed timelockEnv timelockInit timelockCancelRescheduleRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0, .cancelled 12,
      .scheduled 12 105 10 10 none, .executed 12 timelockPlainOp 105 true] ∧
  (submitAll .deployed timelockEnv timelockInit timelockRaiseRun).1.minDelay = 100

/-! ## The state is the log -/

/-- **THE STATE IS THE REPLAY OF THE COMMITTED LOG.** In either variant: every frame that
commits from `s` (an entry point, a call loop or a target, nested or not, at any time and
budget) leaves exactly `replay s l`, the state that applying the writes of its log `l` to `s`
in order gives (`Effect.apply`); and every sequence of transactions from `s` leaves the replay
of its committed log. -/
def Properties.StateIsLogReplay : Prop :=
  (∀ (v : Variant) (E : Env) (τ n : ℕ) (f : Frame) (s s' : State) (l : List Effect),
    exec v E τ n f s = some (s', l) → replay s l = s') ∧
  ∀ (v : Variant) (E : Env) (s : State) (txs : List Tx),
    replay s (submitAll v E s txs).2 = (submitAll v E s txs).1

/-- **THE REPLAY RECOMPUTES RE-ENTRANT RUNS.** Replaying the committed log of `timelockRaiseRun`
on fresh Governance gives `minDelay = 100`, set by a self-call inside an execution, as the run
leaves it, and ids `11` and `12` `Done`; replaying that of `timelockOwnershipRun` gives owner `0`
and council `3`, as the run leaves them. -/
@[witness] def Properties.StateIsLogReplayWitness : Prop :=
  (replay timelockInit (submitAll .deployed timelockEnv timelockInit timelockRaiseRun).2).minDelay =
    100 ∧
  (submitAll .deployed timelockEnv timelockInit timelockRaiseRun).1.minDelay = 100 ∧
  (replay timelockInit (submitAll .deployed timelockEnv timelockInit timelockRaiseRun).2).ts 11 =
    EXECUTED ∧
  (replay timelockInit (submitAll .deployed timelockEnv timelockInit timelockRaiseRun).2).ts 12 =
    EXECUTED ∧
  (replay timelockInit
      (submitAll .deployed timelockEnv timelockInit timelockOwnershipRun).2).owner = 0 ∧
  (submitAll .deployed timelockEnv timelockInit timelockOwnershipRun).1.owner = 0 ∧
  (replay timelockInit
      (submitAll .deployed timelockEnv timelockInit timelockOwnershipRun).2).council = 3 ∧
  (submitAll .deployed timelockEnv timelockInit timelockOwnershipRun).1.council = 3

/-- **EVERY LOGGED ENTRY PASSED ITS CHECK.** In the deployed order: in the log of every frame
that commits from `s`, and in the committed log of every sequence of transactions from `s`,
each entry `e` satisfies `e.CheckedAt E (replay s l₁)`, where `l₁` is the part of the log before
it. On that state: a schedule of `x` with recorded minimum delay `m` and delay `d` found `x`
`Unset` and `m = minDelay ≤ d`, did not overflow, and, if transparent, published an operation
whose hash is `x`; a cancel of `x` found `x` pending; an execution of `x` with operation `op`
at time `τ` has `x = H op`, `op`'s predecessor zero or `Done`, and `x` pending, and, for
`execute`, `timestamps[x] ≤ τ`; a `ChangeMinDelay` or `ChangeSecurityCouncil` entry's old
value was the stored one; an `OwnershipTransferred` entry's new owner is the zero address or
was the pending owner. For an execution that state is the one after the operation's
calls. -/
def Properties.LoggedEntriesPassedTheirChecks : Prop :=
  (∀ (E : Env) (τ n : ℕ) (f : Frame) (s s' : State) (l : List Effect),
    exec .deployed E τ n f s = some (s', l) →
    ∀ (l₁ l₂ : List Effect) (e : Effect), l = l₁ ++ e :: l₂ → e.CheckedAt E (replay s l₁)) ∧
  ∀ (E : Env) (s : State) (txs : List Tx) (l₁ l₂ : List Effect) (e : Effect),
    (submitAll .deployed E s txs).2 = l₁ ++ e :: l₂ → e.CheckedAt E (replay s l₁)

/-- **CHECKS ON RE-ENTRANT ENTRIES.** The committed log of `timelockCancelRescheduleRun` is a
schedule of id `12`, the delivery of its call, the in-flight cancel, a new shadow schedule of
`12` at `105` with delay `10`, and the instant execution. On the replay of the first three
entries, `12` is `Unset` and `minDelay` is `10`, as the new schedule's check requires; on the
replay of the first four, `timestamps[12] = 115`, so `12` is pending, as the execution's check
requires. -/
@[witness] def Properties.LoggedEntriesPassedTheirChecksWitness : Prop :=
  (submitAll .deployed timelockEnv timelockInit timelockCancelRescheduleRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0, .cancelled 12] ++
      .scheduled 12 105 10 10 none :: [.executed 12 timelockPlainOp 105 true] ∧
  (replay timelockInit
      [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0, .cancelled 12]).ts 12 =
    0 ∧
  (replay timelockInit
      [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0, .cancelled 12]).minDelay =
    10 ∧
  (replay timelockInit
      [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0, .cancelled 12,
        .scheduled 12 105 10 10 none]).ts 12 = 115

/-- **NOTHING CONCERNS AN ID AFTER ITS EXECUTION.** In the committed log of any sequence of
transactions from any state, no entry after an execution of `x` schedules, cancels, delivers
a call of, or executes `x` (`Effect.opId`). -/
def Properties.NothingAfterExecution : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx) (l₁ l₂ : List Effect) (x : OpId) (op : Operation)
    (τ : ℕ) (b : Bool),
    (submitAll .deployed E s txs).2 = l₁ ++ .executed x op τ b :: l₂ →
    ∀ e ∈ l₂, e.opId ≠ some x

/-- **AN EXECUTION FOLLOWED BY MORE ENTRIES.** From fresh Governance, `timelockPlainRun`
executes id `12` at `110`; then, at `120`, the owner's `scheduleTransparent` of the same
operation commits nothing, and the schedule of `timelockSuccOp` (id `13`) commits. -/
@[witness] def Properties.NothingAfterExecutionWitness : Prop :=
  (submitAll .deployed timelockEnv timelockInit (timelockPlainRun ++ timelockAfterDoneRun)).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0,
      .executed 12 timelockPlainOp 110 false, .scheduled 13 120 10 10 (some timelockSuccOp)]

/-! ## (a) Once only -/

/-- **`Done` IS PERMANENT.** In either variant, every frame that commits from a state where
operation `x` is `Done` leaves it `Done`, and so does every sequence of transactions. -/
def Properties.DoneIsPermanent : Prop :=
  (∀ (v : Variant) (E : Env) (τ n : ℕ) (f : Frame) (s s' : State) (l : List Effect) (x : OpId),
    s.ts x = EXECUTED → exec v E τ n f s = some (s', l) → s'.ts x = EXECUTED) ∧
  ∀ (v : Variant) (E : Env) (s : State) (txs : List Tx) (x : OpId), s.ts x = EXECUTED →
    (submitAll v E s txs).1.ts x = EXECUTED

/-- **A LATER SCHEDULE OF A DONE OPERATION COMMITS NOTHING.** After `timelockPlainRun` id `12`
is `Done`; the owner's later `scheduleTransparent` of the same operation commits nothing, and
`12` stays `Done`. -/
@[witness] def Properties.DoneIsPermanentWitness : Prop :=
  (submitAll .deployed timelockEnv timelockInit timelockPlainRun).1.ts 12 = EXECUTED ∧
  (submitAll .deployed timelockEnv timelockInit
      (timelockPlainRun ++ [timelockTx 1 120 (.scheduleTransparent timelockPlainOp 10)])).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0,
      .executed 12 timelockPlainOp 110 false] ∧
  (submitAll .deployed timelockEnv timelockInit
      (timelockPlainRun ++ [timelockTx 1 120 (.scheduleTransparent timelockPlainOp 10)])).1.ts 12 =
    EXECUTED

/-- **HEADLINE (a): ONCE ONLY.** For every deployment, every state and every sequence of
transactions, with every behaviour of every target at every depth: the committed log never
executes one operation id twice, and never delivers call `i` of one operation id twice. -/
@[headline] def Properties.OnceOnly : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx),
    ((submitAll .deployed E s txs).2.filterMap Effect.runKey).Nodup

/-- **EACH COMMITTED RUN WAS OPEN, AND IS DONE.** Every delivery or execution of operation `x`
in the committed log of a sequence of transactions: `x` was not `Done` where the sequence
started, and is `Done` where it ends. -/
def Properties.CommittedRunsWereOpen : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx) (e : Effect) (x : OpId),
    e ∈ (submitAll .deployed E s txs).2 → e.runId = some x →
    s.ts x ≠ EXECUTED ∧ (submitAll .deployed E s txs).1.ts x = EXECUTED

/-- **`Done` EXACTLY WHEN EXECUTED.** From any state, along any sequence of transactions whose
block times are all at least `2`: an operation id `x` ends `Done` if and only if it was `Done`
at the start or the committed log has an execution of `x`; and the log has at most one
execution of `x`. -/
def Properties.DoneIffExecuted : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx), (∀ t ∈ txs, 2 ≤ t.time) → ∀ x : OpId,
    ((submitAll .deployed E s txs).1.ts x = EXECUTED ↔
      s.ts x = EXECUTED ∨ ∃ op τ b, Effect.executed x op τ b ∈ (submitAll .deployed E s txs).2) ∧
    ((submitAll .deployed E s txs).2.filterMap Effect.runKey).count (.executed x) ≤ 1

/-- **`DoneIffExecuted`'S PREMISE HOLDS, AND AN ID BECOMES `Done` BY EXECUTION.** The block times
of `timelockPlainRun` are at least `2`; id `12` is not `Done` in fresh Governance, ends `Done`,
and the committed log executes it. -/
@[witness] def Properties.DoneIffExecutedWitness : Prop :=
  (∀ t ∈ timelockPlainRun, 2 ≤ t.time) ∧ timelockInit.ts 12 ≠ EXECUTED ∧
  (submitAll .deployed timelockEnv timelockInit timelockPlainRun).1.ts 12 = EXECUTED ∧
  Effect.executed 12 timelockPlainOp 110 false ∈
    (submitAll .deployed timelockEnv timelockInit timelockPlainRun).2

/-- **AN EXECUTION RUNS EACH OF ITS CALLS ONCE.** If `execute(op)` or `executeInstant(op)`
commits, from any state and with any targets, then the deliveries and executions its log
records for the id `H op` (the entries whose `Effect.runId` is `H op`) are exactly the
deliveries of its calls `0, …, n-1`, in order, then its own execution; and the id ends
`Done`. -/
def Properties.ExecutionRunsEachCallOnce : Prop :=
  ∀ (E : Env) (τ n : ℕ) (c : Address) (op : Operation) (instant : Bool) (cbs : List Callee)
    (s s' : State) (l : List Effect),
    exec .deployed E τ n (.entry c (GovEntry.execution op instant) cbs) s = some (s', l) →
    l.filter (fun e => e.runId = some (E.H op)) =
        (List.range op.calls.length).map (Effect.delivered (E.H op)) ++
          [.executed (E.H op) op τ instant] ∧
      s'.ts (E.H op) = EXECUTED

/-! ## (e) The re-check -/

/-- **(e) A RE-ENTRANT RE-EXECUTION REVERTS THE OUTER ONE.** If the call loop of an execution
of `op` commits, with any targets, and its log contains an execution of the id `H op` (of
`op` itself or of any operation with that id, by any caller, at any depth), then
`execute(op)` and `executeInstant(op)` with those targets revert, whoever calls them: if the
entry checks pass, the re-check after the calls finds the id `Done`. -/
@[headline] def Properties.ReentrantReexecutionReverts : Prop :=
  ∀ (E : Env) (τ n : ℕ) (c : Address) (op : Operation) (instant : Bool) (cbs : List Callee)
    (s s₂ : State) (l : List Effect),
    exec .deployed E τ n (.calls (E.H op) 0 op.calls cbs) s = some (s₂, l) →
    (∃ op' τ' b, Effect.executed (E.H op) op' τ' b ∈ l) →
    exec .deployed E τ (n + 1) (.entry c (GovEntry.execution op instant) cbs) s = none

/-- **THE RE-ENTRANT CASE OCCURS.** After the first transaction of `timelockReenterRun`, the
call loop of `timelockPlainOp` (whose first target calls `execute(timelockPlainOp)` again as
the owner) commits the inner execution of id `12`. The outer `execute` then reverts, and the
transaction commits nothing; the operation is still pending. -/
@[witness] def Properties.ReentrantReexecutionWitness : Prop :=
  (exec .deployed timelockEnv 110 9 (.calls 12 0 timelockPlainOp.calls
      [timelockCallback 1 (.execute timelockPlainOp)])
      (submitAll .deployed timelockEnv timelockInit (timelockReenterRun.take 1)).1).map
        Prod.snd =
    some [.delivered 12 0, .delivered 12 0, .executed 12 timelockPlainOp 110 false] ∧
  exec .deployed timelockEnv 110 10 (.entry 1 (.execute timelockPlainOp)
      [timelockCallback 1 (.execute timelockPlainOp)])
      (submitAll .deployed timelockEnv timelockInit (timelockReenterRun.take 1)).1 = none ∧
  (submitAll .deployed timelockEnv timelockInit timelockReenterRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp)] ∧
  (submitAll .deployed timelockEnv timelockInit timelockReenterRun).1.ts 12 = 110

/-- **COUNTERMODEL: WITHOUT THE RE-CHECK, RE-ENTRY RUNS AN OPERATION TWICE.** In the variant
with the re-checks removed, the same run commits the call of `timelockPlainOp` twice and its
execution twice. -/
@[countermodel] def Properties.WithoutRecheckReexecutes : Prop :=
  (submitAll .noRecheck timelockEnv timelockInit timelockReenterRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0, .delivered 12 0,
      .executed 12 timelockPlainOp 110 false, .executed 12 timelockPlainOp 110 false] ∧
  ¬ ((submitAll .noRecheck timelockEnv timelockInit timelockReenterRun).2.filterMap
      Effect.runKey).Nodup

/-- **IN THAT VARIANT, EVERY OPERATION CAN RUN TWICE.** For every deployment and every
operation with at least one call, none of them a self-call: from every state where the owner
(not Governance itself) may `execute` it at time `τ`, the owner's `execute` whose first target
calls `execute` of the same operation again as the owner commits a log with a repeated
execution, when the re-checks are removed. In the source the same transaction commits
nothing. -/
@[countermodel] def Properties.WithoutRecheckAnyOpRunsTwice : Prop :=
  ∀ (E : Env) (s : State) (op : Operation) (τ : ℕ),
    op.calls ≠ [] → (∀ c ∈ op.calls, c.target ≠ E.self) → s.owner ≠ E.self →
    s.predecessorDone τ op.predecessor → s.opState τ (E.H op) = .Ready →
    ¬ ((submit .noRecheck E s ⟨s.owner, τ, op.calls.length + 5, .execute op,
        [timelockCallback s.owner (.execute op)]⟩).2.filterMap Effect.runKey).Nodup ∧
    submit .deployed E s ⟨s.owner, τ, op.calls.length + 5, .execute op,
        [timelockCallback s.owner (.execute op)]⟩ = (s, [])

/-- **`WithoutRecheckAnyOpRunsTwice`'s PREMISES HOLD.** After the first transaction of
`timelockReenterRun`, `timelockPlainOp` has a call to a foreign target, the owner is not
Governance, it has no predecessor, and it is ready at `110`. -/
@[witness] def Properties.WithoutRecheckAnyOpRunsTwiceWitness : Prop :=
  timelockPlainOp.calls ≠ [] ∧ (∀ c ∈ timelockPlainOp.calls, c.target ≠ timelockEnv.self) ∧
  (submitAll .deployed timelockEnv timelockInit (timelockReenterRun.take 1)).1.owner ≠
    timelockEnv.self ∧
  (submitAll .deployed timelockEnv timelockInit (timelockReenterRun.take 1)).1.predecessorDone
    110 timelockPlainOp.predecessor ∧
  (submitAll .deployed timelockEnv timelockInit (timelockReenterRun.take 1)).1.opState 110
    (timelockEnv.H timelockPlainOp) = .Ready

/-! ## (b) The delay, and (h) the published payload -/

/-- **HEADLINE (b): THE DELAYED PATH WAITED.** From any state with no operation pending (the
constructor's state is one), along any sequence of transactions: every committed `execute`
of an id `x` at time `τ` has a schedule of `x` earlier in the log. The last one has
`delay ≥` the `minDelay` in force when it was made, and was made at least `delay` before
`τ`. "Earlier in the log" is before the `executed` entry, which follows the execution's own
calls: the schedule reported may be a re-entrant reschedule made during the execution. -/
@[headline] def Properties.OwnerPathWaited : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx), NoPending s →
    ∀ (l₁ l₂ : List Effect) (x : OpId) (op : Operation) (τ : ℕ),
      (submitAll .deployed E s txs).2 = l₁ ++ .executed x op τ false :: l₂ →
      ∃ r, lastSchedule x l₁ = some r ∧ r.minDelay ≤ r.delay ∧ r.time + r.delay ≤ τ

/-- **ONLY `executeInstant` RUNS AN OPERATION EARLY.** From any state with nothing pending,
along any sequence of transactions: a committed execution of `x` at a time `τ` before the ready
time of the last schedule of `x` preceding it was `executeInstant`, which only the security
council may call (`EntryGuards`). -/
def Properties.EarlyExecutionIsInstant : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx), NoPending s →
    ∀ (l₁ l₂ : List Effect) (x : OpId) (op : Operation) (τ : ℕ) (b : Bool) (r : SchedRec),
      (submitAll .deployed E s txs).2 = l₁ ++ .executed x op τ b :: l₂ →
      lastSchedule x l₁ = some r → τ < r.time + r.delay → b = true

/-- **AN EARLY EXECUTION OCCURS.** In `timelockCancelRun` the council executes id `12` at `105`,
before the ready time `110` of its schedule. -/
@[witness] def Properties.EarlyExecutionIsInstantWitness : Prop :=
  (submitAll .deployed timelockEnv timelockInit timelockCancelRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0,
      .executed 12 timelockPlainOp 105 true] ∧
  lastSchedule 12 [.scheduled 12 100 10 10 (some timelockPlainOp)] =
    some ⟨100, 10, 10, some timelockPlainOp⟩ ∧
  105 < 100 + 10

/-- **HEADLINE: EVERY OUTGOING CALL WAITED OR WAS INSTANT.** From any state with no operation
pending (the constructor's state is one), along any sequence of transactions: every call
Governance commits (`delivered x i`) is followed in the log by an execution of `x`, with some
operation `op` at some time `τ`, where `x = H op`. That execution is `executeInstant` (which
only the security council may call, `EntryGuards`), or the last schedule of `x` before it had a
delay at least the `minDelay` in force when it was made, and was made at least that delay
before `τ`. The schedule reported is the last one before the execution's end, which may be a
re-entrant reschedule made inside the execution after the call was delivered (as in
`timelockCancelRescheduleRun`), possibly after a self-call `updateDelay(0)`; it need not be the
schedule that gated the execution at entry. -/
@[headline] def Properties.OutgoingCallsWaitedOrInstant : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx), NoPending s →
    ∀ (l₁ l₂ : List Effect) (x : OpId) (i : ℕ),
      (submitAll .deployed E s txs).2 = l₁ ++ .delivered x i :: l₂ →
      ∃ (l₃ l₄ : List Effect) (op : Operation) (τ : ℕ) (b : Bool),
        l₂ = l₃ ++ .executed x op τ b :: l₄ ∧ x = E.H op ∧
        (b = true ∨ ∃ r, lastSchedule x (l₁ ++ .delivered x i :: l₃) = some r ∧
          r.minDelay ≤ r.delay ∧ r.time + r.delay ≤ τ)

/-- **BOTH CASES OCCUR.** From fresh Governance (nothing pending): in `timelockPlainRun` the
delivered call of id `12` belongs to the owner's `execute` at `110`, ten seconds after its
schedule with the minimum delay `10`; in `timelockCancelRun` it belongs to the council's
`executeInstant` at `105`. -/
@[witness] def Properties.OutgoingCallsWaitedOrInstantWitness : Prop :=
  NoPending timelockInit ∧
  (submitAll .deployed timelockEnv timelockInit timelockPlainRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0,
      .executed 12 timelockPlainOp 110 false] ∧
  (submitAll .deployed timelockEnv timelockInit timelockCancelRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0,
      .executed 12 timelockPlainOp 105 true]

/-- **WITH NONDECREASING BLOCK TIMES, NO EXECUTION PRECEDES ITS SCHEDULE.** From any state with no
operation pending, along any sequence of transactions whose block times never decrease
(`TimesMonotone`): every committed execution of `x` at time `τ`, on either path, has a last
schedule of `x` earlier in the log, made at a time at most `τ`, with a delay at least the
`minDelay` in force when it was made; on the `execute` path it was made at least that delay
before `τ`. -/
def Properties.ExecutionNotBeforeSchedule : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx), NoPending s → TimesMonotone txs →
    ∀ (l₁ l₂ : List Effect) (x : OpId) (op : Operation) (τ : ℕ) (b : Bool),
      (submitAll .deployed E s txs).2 = l₁ ++ .executed x op τ b :: l₂ →
      ∃ r, lastSchedule x l₁ = some r ∧ r.minDelay ≤ r.delay ∧ r.time ≤ τ ∧
        (b = false → r.time + r.delay ≤ τ)

/-- **`ExecutionNotBeforeSchedule`'S PREMISES HOLD ON THE INSTANT PATH, AND ITS TIME PREMISE IS
NEEDED.** The block times of `timelockCancelRun` never decrease, and its instant execution at
`105` comes after the schedule at `100`, before the ready time `110`. With the times out of order
(schedule at `100`, then the council's `executeInstant` at `50`), the execution commits at `50`,
before its schedule's time. -/
@[witness] def Properties.ExecutionNotBeforeScheduleWitness : Prop :=
  NoPending timelockInit ∧ TimesMonotone timelockCancelRun ∧
  (submitAll .deployed timelockEnv timelockInit timelockCancelRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0,
      .executed 12 timelockPlainOp 105 true] ∧
  ¬ TimesMonotone [timelockTx 1 100 (.scheduleTransparent timelockPlainOp 10),
    timelockTx 2 50 (.executeInstant timelockPlainOp)] ∧
  (submitAll .deployed timelockEnv timelockInit
      [timelockTx 1 100 (.scheduleTransparent timelockPlainOp 10),
        timelockTx 2 50 (.executeInstant timelockPlainOp)]).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0,
      .executed 12 timelockPlainOp 50 true]

/-- **THE BOUND IS ATTAINED.** From fresh Governance, `timelockPlainRun` schedules id `12` at
`100` with the minimum delay `10` and executes it by the owner at `110`. -/
@[witness] def Properties.OwnerPathWaitedWitness : Prop :=
  NoPending timelockInit ∧
  (submitAll .deployed timelockEnv timelockInit timelockPlainRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0,
      .executed 12 timelockPlainOp 110 false] ∧
  lastSchedule 12 [.scheduled 12 100 10 10 (some timelockPlainOp)] =
    some ⟨100, 10, 10, some timelockPlainOp⟩

/-- **HEADLINE (h): A TRANSPARENT SCHEDULE BINDS ITS PAYLOAD, OR TWO LOGGED OPERATIONS
COLLIDE.** From any state with nothing pending, along any sequence of transactions: every
committed execution of `op` (either path) has id `H op` and a schedule of that id earlier in
the log; the last one had `delay ≥ minDelay` then; and if it was transparent with payload
`op₀`, then `op₀ = op`, or `op₀ ≠ op` and `H op₀ = H op`. That disjunction is equivalent to
`H op₀ = H op`: the published payload hashes to the executed id, so the schedule binds its
payload only up to a keccak collision. The content beyond it is that `x = H op`, that a last
schedule exists on either path, and that its delay is at least the `minDelay` recorded with it. -/
@[headline] def Properties.TransparentBinding : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx), NoPending s →
    ∀ (l₁ l₂ : List Effect) (x : OpId) (op : Operation) (τ : ℕ) (b : Bool),
      (submitAll .deployed E s txs).2 = l₁ ++ .executed x op τ b :: l₂ →
      x = E.H op ∧ ∃ r, lastSchedule x l₁ = some r ∧ r.minDelay ≤ r.delay ∧
        ∀ op₀, r.op = some op₀ → op₀ = op ∨ (op₀ ≠ op ∧ E.H op₀ = E.H op)

/-- **THE BINDING CASE.** In `timelockPlainRun` the published and the executed operation are
the same. -/
@[witness] def Properties.TransparentBindingWitness : Prop :=
  (submitAll .deployed timelockEnv timelockInit timelockPlainRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0,
      .executed 12 timelockPlainOp 110 false]

/-- **THE COLLISION CASE FIRES.** In `timelockCollideRun` the owner publishes
`timelockPlainOp` and then executes `timelockCollideOp`, a different operation with the same
id. The log carries both. -/
@[countermodel] def Properties.TransparentCollisionExecutesAnotherOp : Prop :=
  (submitAll .deployed timelockEnv timelockInit timelockCollideRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0,
      .executed 12 timelockCollideOp 110 false] ∧
  timelockPlainOp ≠ timelockCollideOp ∧
  timelockEnv.H timelockPlainOp = timelockEnv.H timelockCollideOp

/-! ## (c) Predecessors, and (d) the sentinel -/

/-- **HEADLINE (c): THE PREDECESSOR RAN FIRST.** For any state and any sequence of transactions
whose block times are all at least `2`: every committed execution of an operation whose
predecessor `p` is nonzero has an execution of `p` earlier in the log, or `p` was already
`Done` where the sequence started. -/
@[headline] def Properties.PredecessorDone : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx), (∀ t ∈ txs, 2 ≤ t.time) →
    ∀ (l₁ l₂ : List Effect) (x : OpId) (op : Operation) (τ : ℕ) (b : Bool),
      (submitAll .deployed E s txs).2 = l₁ ++ .executed x op τ b :: l₂ →
      op.predecessor ≠ 0 →
      s.ts op.predecessor = EXECUTED ∨
        ∃ op' τ' b', Effect.executed op.predecessor op' τ' b' ∈ l₁

/-- **(c) WITHOUT THE TIME PREMISE: THE PREDECESSOR RAN, OR HIT THE SENTINEL.** For any state
and any sequence of transactions: every committed execution whose predecessor `p` is nonzero
has, earlier in the log, an execution of `p` or a schedule of `p` whose time plus delay is
`1`; or `p` was already `Done` at the start. -/
def Properties.PredecessorDoneOrSentinel : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx) (l₁ l₂ : List Effect) (x : OpId) (op : Operation)
    (τ : ℕ) (b : Bool),
    (submitAll .deployed E s txs).2 = l₁ ++ .executed x op τ b :: l₂ →
    op.predecessor ≠ 0 →
    s.ts op.predecessor = EXECUTED ∨
      (∃ op' τ' b', Effect.executed op.predecessor op' τ' b' ∈ l₁) ∨
      ∃ t d m o, Effect.scheduled op.predecessor t d m o ∈ l₁ ∧ t + d = EXECUTED

/-- **`PredecessorDone`'s PREMISES HOLD, AND THE PREDECESSOR CASE FIRES.** In
`timelockPredRun` every block time is at least `2`; `timelockSuccOp`, whose predecessor is
`12`, is executed after `12` is. -/
@[witness] def Properties.PredecessorDoneWitness : Prop :=
  (∀ t ∈ timelockPredRun, 2 ≤ t.time) ∧ timelockSuccOp.predecessor = 12 ∧
  (submitAll .deployed timelockEnv timelockInit timelockPredRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .scheduled 13 100 10 10 (some timelockSuccOp),
      .delivered 12 0, .executed 12 timelockPlainOp 110 false,
      .delivered 13 0, .executed 13 timelockSuccOp 110 false]

/-- **COUNTERMODEL (d): THE SENTINEL.** A schedule whose time plus delay is `1` (the value
that means "executed", :125) leaves the operation `Done`; one whose time plus delay is `0`
leaves it `Unset` (as a schedule of id `14` at time `0` with delay `0` does, from fresh
Governance with `minDelay = 0`). In `timelockSentinelRun`, from that state: at time
`1` the owner shadow-schedules id `14` with delay `0`, then schedules and later executes
`timelockSentinelSuccOp`, whose predecessor is `14`. The execution commits, though `14` was
never executed and was not `Done` at the start; `14` ends `Done`, so by `DoneIsPermanent` and
`EntryGuards` no later schedule or execution of `14` commits. -/
@[countermodel] def Properties.SentinelCollision : Prop :=
  (∀ (τ : ℕ) (s : State) (x : OpId) (d : ℕ) (o : Option Operation) (s' : State)
      (l : List Effect),
    schedule τ s x d o = some (s', l) → τ + d = EXECUTED → s'.opState τ x = .Done) ∧
  (∀ (τ : ℕ) (s : State) (x : OpId) (d : ℕ) (o : Option Operation) (s' : State)
      (l : List Effect),
    schedule τ s x d o = some (s', l) → τ + d = 0 → s'.opState τ x = .Unset) ∧
  (schedule 0 timelockInitZero 14 0 none).map (fun r => r.1.opState 0 14) = some .Unset ∧
  timelockSentinelSuccOp.predecessor = 14 ∧ timelockInitZero.ts 14 ≠ EXECUTED ∧
  (submitAll .deployed timelockEnv timelockInitZero timelockSentinelRun).2 =
    [.scheduled 14 1 0 0 none, .scheduled 15 1 5 0 (some timelockSentinelSuccOp),
      .delivered 15 0, .executed 15 timelockSentinelSuccOp 6 false] ∧
  (submitAll .deployed timelockEnv timelockInitZero timelockSentinelRun).1.ts 14 = EXECUTED

/-! ## (f) Cancelling an operation while it runs -/

/-- **(f) AN IN-FLIGHT CANCEL STANDS ONLY IF THE OPERATION IS SCHEDULED AGAIN.** If
`execute(op)` or `executeInstant(op)` commits, from any state and with any targets, then every
cancel of the id `H op` in its log is followed, later in that log, by a schedule of `H op`. -/
def Properties.InFlightCancelNeedsReschedule : Prop :=
  ∀ (E : Env) (τ n : ℕ) (c : Address) (op : Operation) (instant : Bool) (cbs : List Callee)
    (s s' : State) (l : List Effect),
    exec .deployed E τ n (.entry c (GovEntry.execution op instant) cbs) s = some (s', l) →
    ∀ l₁ l₂, l = l₁ ++ .cancelled (E.H op) :: l₂ →
      ∃ t d m o, Effect.scheduled (E.H op) t d m o ∈ l₂

/-- **COUNTERMODEL (f): AN IN-FLIGHT CANCEL DOES NOT CANCEL.** After the owner schedules
`timelockPlainOp` (id `12`), the owner's `cancel(12)` succeeds on its own, as a frame, at time
`105`. In `timelockCancelRun` the council executes the operation instantly and its first target
makes exactly that cancel: the execution's call loop (budget `9`, inside the transaction's `10`)
commits, logging the delivery and the cancel, and leaves `timestamps[12] = 0`, so `12` is no
longer pending and the re-check reverts the execution. The transaction commits nothing: the
operation is still pending (`timestamps[12] = 110`), and the council's next `executeInstant`
runs it. In `timelockCancelRescheduleRun` the owner also shadow-schedules id `12` again inside
the execution. The execution commits, logs the cancel and the new schedule, and leaves `12`
`Done`, overwriting both. -/
@[countermodel] def Properties.InFlightCancelIneffective : Prop :=
  (exec .deployed timelockEnv 105 1 (.entry 1 (.cancel 12) [])
      (submitAll .deployed timelockEnv timelockInit (timelockCancelRun.take 1)).1).map
        Prod.snd = some [.cancelled 12] ∧
  (exec .deployed timelockEnv 105 9 (.calls 12 0 timelockPlainOp.calls
      [timelockCallback 1 (.cancel 12)])
      (submitAll .deployed timelockEnv timelockInit (timelockCancelRun.take 1)).1).map
        (fun r => (r.1.ts 12, r.2)) = some (0, [.delivered 12 0, .cancelled 12]) ∧
  exec .deployed timelockEnv 105 10 (.entry 2 (.executeInstant timelockPlainOp)
      [timelockCallback 1 (.cancel 12)])
      (submitAll .deployed timelockEnv timelockInit (timelockCancelRun.take 1)).1 = none ∧
  (submitAll .deployed timelockEnv timelockInit (timelockCancelRun.take 2)).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp)] ∧
  (submitAll .deployed timelockEnv timelockInit (timelockCancelRun.take 2)).1.ts 12 = 110 ∧
  (submitAll .deployed timelockEnv timelockInit timelockCancelRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0,
      .executed 12 timelockPlainOp 105 true] ∧
  (submitAll .deployed timelockEnv timelockInit timelockCancelRescheduleRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0, .cancelled 12,
      .scheduled 12 105 10 10 none, .executed 12 timelockPlainOp 105 true] ∧
  (submitAll .deployed timelockEnv timelockInit timelockCancelRescheduleRun).1.ts 12 = EXECUTED

/-! ## (g) Raising the delay -/

/-- **A DELAY CHANGE TOUCHES NO OPERATION.** A committed `updateDelay` frame leaves every
`timestamps` entry as it was, and no operation's state depends on `minDelay`. -/
def Properties.MinDelayChangeKeepsTimestamps : Prop :=
  (∀ (v : Variant) (E : Env) (τ n : ℕ) (c : Address) (d : ℕ) (cbs : List Callee)
      (s s' : State) (l : List Effect),
    exec v E τ n (.entry c (.updateDelay d) cbs) s = some (s', l) → s'.ts = s.ts) ∧
  ∀ (s : State) (m τ : ℕ) (x : OpId), ({ s with minDelay := m } : State).opState τ x = s.opState τ x

/-- **COUNTERMODEL (g): RAISING THE DELAY IS NOT RETROACTIVE.** In `timelockRaiseRun` (block
times nondecreasing), the owner schedules `timelockRaiseOp` and `timelockPlainOp` at `100`
with the minimum delay `10`. At `110` the first raises the minimum delay to `100`, and the
second still executes at `110`, ten seconds after it was scheduled, though `110 < 100 + 100`.
A new schedule with delay `10` is now refused. -/
@[countermodel] def Properties.DelayRaiseNotRetroactive : Prop :=
  TimesMonotone timelockRaiseRun ∧
  (submitAll .deployed timelockEnv timelockInit timelockRaiseRun).2 =
    [.scheduled 11 100 10 10 (some timelockRaiseOp), .scheduled 12 100 10 10 (some timelockPlainOp),
      .delivered 11 0, .minDelayChanged 10 100, .executed 11 timelockRaiseOp 110 false,
      .delivered 12 0, .executed 12 timelockPlainOp 110 false] ∧
  (submitAll .deployed timelockEnv timelockInit timelockRaiseRun).1.minDelay = 100 ∧
  110 < 100 + (submitAll .deployed timelockEnv timelockInit timelockRaiseRun).1.minDelay ∧
  schedule 110 (submitAll .deployed timelockEnv timelockInit timelockRaiseRun).1 13 10 none = none

/-! ## Authority -/

/-- **ONLY AN EXECUTION CHANGES THE DELAY OR THE COUNCIL.** If a transaction changes
`minDelay` or the security council, from any state, then it called `execute(op)` or
`executeInstant(op)` (`GovEntry.execution op b`) for some operation `op`, and its committed
log ends with the execution of `op`, at the transaction's block time, on that path. -/
@[headline] def Properties.ConfigChangesNeedExecution : Prop :=
  ∀ (E : Env) (s : State) (t : Tx),
    ((submit .deployed E s t).1.minDelay ≠ s.minDelay ∨
      (submit .deployed E s t).1.council ≠ s.council) →
    ∃ op b, t.entry = GovEntry.execution op b ∧
      (submit .deployed E s t).2.getLast? = some (.executed (E.H op) op t.time b)

/-- **A TRANSACTION THAT CHANGES THE DELAY.** After the first two transactions of
`timelockRaiseRun`, its third, the owner's `execute(timelockRaiseOp)` at `110`, changes
`minDelay` from `10` to `100` through the operation's self-call. -/
@[witness] def Properties.ConfigChangesNeedExecutionWitness : Prop :=
  (submitAll .deployed timelockEnv timelockInit (timelockRaiseRun.take 2)).1.minDelay = 10 ∧
  (submit .deployed timelockEnv
      (submitAll .deployed timelockEnv timelockInit (timelockRaiseRun.take 2)).1
      (timelockTx 1 110 (.execute timelockRaiseOp))).1.minDelay = 100 ∧
  (submit .deployed timelockEnv
      (submitAll .deployed timelockEnv timelockInit (timelockRaiseRun.take 2)).1
      (timelockTx 1 110 (.execute timelockRaiseOp))).2 =
    [.delivered 11 0, .minDelayChanged 10 100, .executed 11 timelockRaiseOp 110 false]

/-- **EVERY COMMITTED OUTGOING CALL BELONGS TO A COMMITTED EXECUTION.** In the committed log of
any sequence of transactions, every delivery of a call of operation `x` is followed, later in
the log, by the execution of `x`. -/
def Properties.DeliveriesBelongToExecutions : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx) (l₁ l₂ : List Effect) (x : OpId) (i : ℕ),
    (submitAll .deployed E s txs).2 = l₁ ++ .delivered x i :: l₂ →
    ∃ op τ b, Effect.executed x op τ b ∈ l₂

/-- **A NEW OWNER ACCEPTED A NOMINATION (`Ownable2Step`).** In the committed log of any
sequence of transactions from any state, with every target behaviour: every
`OwnershipTransferred` entry whose new owner `a` is not the zero address comes after a
nomination of `a` (`OwnershipTransferStarted`, logged only by `transferOwnership`, which needs
the owner, `EntryGuards`) with no entry between them that writes the pending owner
(`Effect.pendingWrite`: a nomination or an ownership transfer); or no entry before it writes the
pending owner, and `a` was the pending owner at the start. -/
@[headline] def Properties.NewOwnerWasNominated : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx) (l₁ l₂ : List Effect) (a : Address),
    (submitAll .deployed E s txs).2 = l₁ ++ .ownershipTransferred a :: l₂ → a ≠ 0 →
    (∃ l₃ l₄, l₁ = l₃ ++ .ownershipTransferStarted a :: l₄ ∧ ∀ e ∈ l₄, e.pendingWrite = none) ∨
      (s.pendingOwner = a ∧ ∀ e ∈ l₁, e.pendingWrite = none)

/-- **A NOMINATION ACCEPTED INSIDE AN EXECUTION.** From fresh Governance, in
`timelockAcceptInsideRun` the owner `1` nominates `5` and schedules `timelockPlainOp`; the
council's `executeInstant` of it at `105` commits, and inside it `5` accepts. The committed
log has the transfer to `5` after the nomination of `5`, with the schedule and the delivery,
which write no pending owner, between them; `5` ends the owner. -/
@[witness] def Properties.NewOwnerWasNominatedWitness : Prop :=
  (submitAll .deployed timelockEnv timelockInit timelockAcceptInsideRun).2 =
    [.ownershipTransferStarted 5, .scheduled 12 100 10 10 (some timelockPlainOp),
      .delivered 12 0] ++ .ownershipTransferred 5 :: [.executed 12 timelockPlainOp 105 true] ∧
  (5 : Address) ≠ 0 ∧
  (∀ e ∈ [Effect.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0],
    e.pendingWrite = none) ∧
  (submitAll .deployed timelockEnv timelockInit timelockAcceptInsideRun).1.owner = 5

/-! ## Enabledness -/

/-- **A READY OPERATION CAN BE EXECUTED.** For every deployment, every state and every
operation whose calls all go to other contracts: if the operation is `Ready` at time `τ` and
its predecessor is zero or `Done`, then a transaction at `τ` by the owner or the council, when
that caller is not Governance itself, calling `execute(op)` with budget at least the number of
calls plus `2` and targets that all return without calling back (`callees = []`), commits. It
leaves the operation `Done` and the rest of the state as it was, and logs the delivery of each
call in order, then the execution. -/
@[headline] def Properties.ReadyIsExecutable : Prop :=
  ∀ (E : Env) (s : State) (op : Operation) (c : Address) (τ n : ℕ),
    (c = s.owner ∨ c = s.council) → c ≠ E.self → (∀ call ∈ op.calls, call.target ≠ E.self) →
    op.calls.length + 2 ≤ n →
    s.predecessorDone τ op.predecessor → s.opState τ (E.H op) = .Ready →
    submit .deployed E s ⟨c, τ, n, .execute op, []⟩ =
      (s.setTs (E.H op) EXECUTED,
        (List.range op.calls.length).map (Effect.delivered (E.H op)) ++
          [.executed (E.H op) op τ false])

/-- **A PENDING OPERATION CAN BE EXECUTED INSTANTLY.** For every deployment, every state and
every operation whose calls all go to other contracts: if the operation is pending (`Waiting` or
`Ready`) at time `τ` and its predecessor is zero or `Done`, and the council is not Governance
itself, then the council's transaction at `τ` calling `executeInstant(op)` with budget at least
the number of calls plus `2` and targets that all return without calling back commits. It
leaves the operation `Done` and the rest of the state as it was, and logs the delivery of each
call in order, then the instant execution. -/
def Properties.PendingIsInstantlyExecutable : Prop :=
  ∀ (E : Env) (s : State) (op : Operation) (τ n : ℕ),
    s.council ≠ E.self → (∀ call ∈ op.calls, call.target ≠ E.self) →
    op.calls.length + 2 ≤ n →
    s.predecessorDone τ op.predecessor → s.isPending τ (E.H op) →
    submit .deployed E s ⟨s.council, τ, n, .executeInstant op, []⟩ =
      (s.setTs (E.H op) EXECUTED,
        (List.range op.calls.length).map (Effect.delivered (E.H op)) ++
          [.executed (E.H op) op τ true])

/-- **`ReadyIsExecutable`'S PREMISES HOLD, WITH A NONZERO PREDECESSOR.** In the state
`timelockAfterDoneRun` leaves from `timelockPlainDone` (id `12` `Done`, `timelockSuccOp`
scheduled at `120` with delay `10`): `timelockSuccOp` has one call, to the foreign target
`50`; its predecessor `12` is nonzero and `Done`; at `130` it is `Ready`; the owner `1` is not
Governance. The owner's `execute(timelockSuccOp)` at `130` with budget `3` logs the delivery and
the execution of id `13`. -/
@[witness] def Properties.ReadyIsExecutableWitness : Prop :=
  timelockSuccOp.calls.length = 1 ∧
  (∀ call ∈ timelockSuccOp.calls, call.target ≠ timelockEnv.self) ∧
  (1 : Address) = (submitAll .deployed timelockEnv timelockPlainDone timelockAfterDoneRun).1.owner ∧
  (1 : Address) ≠ timelockEnv.self ∧ timelockSuccOp.predecessor ≠ 0 ∧
  (submitAll .deployed timelockEnv timelockPlainDone timelockAfterDoneRun).1.predecessorDone 130
    timelockSuccOp.predecessor ∧
  (submitAll .deployed timelockEnv timelockPlainDone timelockAfterDoneRun).1.opState 130
    (timelockEnv.H timelockSuccOp) = .Ready ∧
  (submit .deployed timelockEnv
      (submitAll .deployed timelockEnv timelockPlainDone timelockAfterDoneRun).1
      ⟨1, 130, 3, .execute timelockSuccOp, []⟩).2 =
    [.delivered 13 0, .executed 13 timelockSuccOp 130 false]

/-- **`PendingIsInstantlyExecutable`'S PREMISES HOLD, BEFORE THE READY TIME.** In the same state,
at `125`: `timelockSuccOp` is `Waiting` (pending, not ready), its predecessor `12` is nonzero
and `Done`, and the council `2` is not Governance. The council's `executeInstant` of it at `125`
with budget `3` logs the delivery and the instant execution of id `13`. -/
@[witness] def Properties.PendingIsInstantlyExecutableWitness : Prop :=
  (submitAll .deployed timelockEnv timelockPlainDone timelockAfterDoneRun).1.council = 2 ∧
  (2 : Address) ≠ timelockEnv.self ∧ timelockSuccOp.predecessor ≠ 0 ∧
  (submitAll .deployed timelockEnv timelockPlainDone timelockAfterDoneRun).1.predecessorDone 125
    timelockSuccOp.predecessor ∧
  (submitAll .deployed timelockEnv timelockPlainDone timelockAfterDoneRun).1.opState 125
    (timelockEnv.H timelockSuccOp) = .Waiting ∧
  (submitAll .deployed timelockEnv timelockPlainDone timelockAfterDoneRun).1.isPending 125
    (timelockEnv.H timelockSuccOp) ∧
  (submit .deployed timelockEnv
      (submitAll .deployed timelockEnv timelockPlainDone timelockAfterDoneRun).1
      ⟨2, 125, 3, .executeInstant timelockSuccOp, []⟩).2 =
    [.delivered 13 0, .executed 13 timelockSuccOp 125 true]

end Contracts.Governance
