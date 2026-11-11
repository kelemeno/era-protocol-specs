import EraSpec.Contracts.Governance.Specs.Timelock

/-!
# Properties: what the `Governance` timelock guarantees, across re-entrant execution

Statements about `EraSpec.Contracts.Governance.Specs.Timelock` (source `e561b9cc2`,
identical at `c67894b9`). Proofs are in `EraSpec.Contracts.Governance.Proofs.Timelock`.

Every result quantifies over every target behaviour (`Callee` trees: re-entrant calls to any
entry point, as any caller but Governance itself, at any depth, caught or not), every
self-call decoder `Env.dec`, every hash `Env.H`, and every budget. None takes a hash premise.
The run results are about the committed log of any sequence of transactions
(`submitAll .deployed`); the frame results are about one committed frame anywhere in a
transaction, nested or not.

## The guards

* `EntryGuards`: each entry point's transcribed guard and write, in either variant.
  `EntryGuardsWitness`: runs in which every entry point commits, so no guard is vacuous.

## (a) Once only

* `DoneIsPermanent`: a `Done` operation (`timestamps = 1`) stays `Done` across every frame and
  every sequence of transactions. Nothing can schedule, cancel or execute it again
  (`DoneIsPermanentWitness`: a later schedule of an executed operation commits nothing).
* `OnceOnly` (headline): in the committed log of any sequence of transactions, from any
  state, no operation id is executed twice and no call of an operation is delivered twice.
  `CommittedRunsWereOpen`: each logged delivery or execution of `x` was not `Done` at the
  start of the sequence, and `x` is `Done` at its end.
* `ExecutionRunsEachCallOnce`: a committed `execute(op)`/`executeInstant(op)` logs, for its
  id, exactly the deliveries of its calls `0, …, n-1`, in order, then its own execution, and
  leaves the id `Done`. Whatever its targets did re-entrantly concerns other ids only.

## (e) The re-check

* `ReentrantReexecutionReverts`: if the calls of an execution of `op` commit, inside them,
  an execution of `op`'s id (re-entrantly, by any caller, through any operation with that
  id), the outer execution reverts at its re-check (:199-201, :224-226).
* `ReentrantReexecutionWitness`: a concrete case. The inner execution commits inside the
  calls, the outer reverts, and the transaction commits nothing.
* **Countermodel** `WithoutRecheckReexecutes`: without the re-checks, the same transaction
  commits the operation's call twice and its execution twice. `WithoutRecheckAnyOpRunsTwice`:
  the same holds for every operation whose calls go to other contracts, from every state where
  the owner may execute it; in the source, that transaction commits nothing
  (`WithoutRecheckAnyOpRunsTwiceWitness`: its premises hold).

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
  inside the operation's own calls never stands: either the execution reverts at its re-check
  and takes the cancel with it, or the id was scheduled again and the execution overwrites
  that schedule with `Done`.
* **Countermodel** `InFlightCancelIneffective`: the owner's `cancel` succeeds in its own frame
  during the council's `executeInstant`. The transaction still reverts, so the operation is
  still pending afterwards and the council executes it later. When the owner also schedules it
  again inside the same execution, the execution commits, and the new schedule is overwritten.

## (g) Raising the delay

* `MinDelayChangeKeepsTimestamps`: `updateDelay` writes only `minDelay`, and no operation state
  reads it. Only `_schedule` does (:249).
* **Countermodel** `DelayRaiseNotRetroactive`: an operation scheduled with the old minimum
  delay `10` runs `10` seconds later, after an operation raised the minimum to `100`. A new
  schedule with delay `10` is then refused.

## Authority

* `ConfigChangesNeedExecution`: a transaction that changes `minDelay` or the security council
  commits the execution of some operation: `onlySelf` is reachable only through `_execute`.
* `DeliveriesBelongToExecutions`: every call Governance commits (`delivered x i`) is followed,
  later in the committed log, by the execution of `x`. So every committed outgoing call is
  part of a committed execution.
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
def Properties.EntryGuards : Prop :=
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
def Properties.EntryGuardsWitness : Prop :=
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

/-! ## (a) Once only -/

/-- **`Done` IS PERMANENT.** In either variant, every frame that commits from a state where
operation `x` is `Done` leaves it `Done`; so does every sequence of transactions. -/
def Properties.DoneIsPermanent : Prop :=
  (∀ (v : Variant) (E : Env) (τ n : ℕ) (f : Frame) (s s' : State) (l : List Effect) (x : OpId),
    s.ts x = EXECUTED → exec v E τ n f s = some (s', l) → s'.ts x = EXECUTED) ∧
  ∀ (E : Env) (s : State) (txs : List Tx) (x : OpId), s.ts x = EXECUTED →
    (submitAll .deployed E s txs).1.ts x = EXECUTED

/-- **A DONE OPERATION CANNOT BE SCHEDULED AGAIN.** After `timelockPlainRun` id `12` is `Done`;
the owner's later `scheduleTransparent` of the same operation commits nothing, and `12` stays
`Done`. -/
def Properties.DoneIsPermanentWitness : Prop :=
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
def Properties.OnceOnly : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx),
    ((submitAll .deployed E s txs).2.filterMap Effect.runKey).Nodup

/-- **EACH COMMITTED RUN WAS OPEN, AND IS DONE.** Every delivery or execution of operation `x`
in the committed log of a sequence of transactions: `x` was not `Done` where the sequence
started, and is `Done` where it ends. -/
def Properties.CommittedRunsWereOpen : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx) (e : Effect) (x : OpId),
    e ∈ (submitAll .deployed E s txs).2 → e.runId = some x →
    s.ts x ≠ EXECUTED ∧ (submitAll .deployed E s txs).1.ts x = EXECUTED

/-- **AN EXECUTION RUNS EACH OF ITS CALLS ONCE.** If `execute(op)` or `executeInstant(op)`
commits, from any state and with any targets, then the entries of its log for the id
`H op` are exactly the deliveries of its calls `0, …, n-1`, in order, then its own
execution; and the id ends `Done`. -/
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
`execute(op)` and `executeInstant(op)` with those targets revert, whoever calls them: the
re-check finds the id `Done`. -/
def Properties.ReentrantReexecutionReverts : Prop :=
  ∀ (E : Env) (τ n : ℕ) (c : Address) (op : Operation) (instant : Bool) (cbs : List Callee)
    (s s₂ : State) (l : List Effect),
    exec .deployed E τ n (.calls (E.H op) 0 op.calls cbs) s = some (s₂, l) →
    (∃ op' τ' b, Effect.executed (E.H op) op' τ' b ∈ l) →
    exec .deployed E τ (n + 1) (.entry c (GovEntry.execution op instant) cbs) s = none

/-- **THE RE-ENTRANT CASE OCCURS.** After the first transaction of `timelockReenterRun`, the
call loop of `timelockPlainOp` (whose first target calls `execute(timelockPlainOp)` again as
the owner) commits the inner execution of id `12`. The outer `execute` then reverts, and the
transaction commits nothing; the operation is still pending. -/
def Properties.ReentrantReexecutionWitness : Prop :=
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
def Properties.WithoutRecheckReexecutes : Prop :=
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
def Properties.WithoutRecheckAnyOpRunsTwice : Prop :=
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
def Properties.WithoutRecheckAnyOpRunsTwiceWitness : Prop :=
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
`τ`. -/
def Properties.OwnerPathWaited : Prop :=
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
def Properties.EarlyExecutionIsInstantWitness : Prop :=
  (submitAll .deployed timelockEnv timelockInit timelockCancelRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0,
      .executed 12 timelockPlainOp 105 true] ∧
  lastSchedule 12 [.scheduled 12 100 10 10 (some timelockPlainOp)] =
    some ⟨100, 10, 10, some timelockPlainOp⟩ ∧
  105 < 100 + 10

/-- **THE BOUND IS ATTAINED.** From fresh Governance, `timelockPlainRun` schedules id `12` at
`100` with the minimum delay `10` and executes it by the owner at `110`. -/
def Properties.OwnerPathWaitedWitness : Prop :=
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
`op₀`, then `op₀ = op`, or `op₀ ≠ op` and `H op₀ = H op`. -/
def Properties.TransparentBinding : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx), NoPending s →
    ∀ (l₁ l₂ : List Effect) (x : OpId) (op : Operation) (τ : ℕ) (b : Bool),
      (submitAll .deployed E s txs).2 = l₁ ++ .executed x op τ b :: l₂ →
      x = E.H op ∧ ∃ r, lastSchedule x l₁ = some r ∧ r.minDelay ≤ r.delay ∧
        ∀ op₀, r.op = some op₀ → op₀ = op ∨ (op₀ ≠ op ∧ E.H op₀ = E.H op)

/-- **THE BINDING CASE.** In `timelockPlainRun` the published and the executed operation are
the same. -/
def Properties.TransparentBindingWitness : Prop :=
  (submitAll .deployed timelockEnv timelockInit timelockPlainRun).2 =
    [.scheduled 12 100 10 10 (some timelockPlainOp), .delivered 12 0,
      .executed 12 timelockPlainOp 110 false]

/-- **THE COLLISION CASE FIRES.** In `timelockCollideRun` the owner publishes
`timelockPlainOp` and then executes `timelockCollideOp`, a different operation with the same
id. The log carries both. -/
def Properties.TransparentCollisionExecutesAnotherOp : Prop :=
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
def Properties.PredecessorDone : Prop :=
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
def Properties.PredecessorDoneWitness : Prop :=
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
never executed and was not `Done` at the start; `14` stays `Done`, so it can never run. -/
def Properties.SentinelCollision : Prop :=
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
makes exactly that cancel. The transaction reverts at the re-check, so it commits nothing: the
operation is still pending (`timestamps[12] = 110`), and the council's next `executeInstant`
runs it. In `timelockCancelRescheduleRun` the owner also shadow-schedules id `12` again inside
the execution. The execution commits, logs the cancel and the new schedule, and leaves `12`
`Done`, overwriting both. -/
def Properties.InFlightCancelIneffective : Prop :=
  (exec .deployed timelockEnv 105 1 (.entry 1 (.cancel 12) [])
      (submitAll .deployed timelockEnv timelockInit (timelockCancelRun.take 1)).1).map
        Prod.snd = some [.cancelled 12] ∧
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
def Properties.DelayRaiseNotRetroactive : Prop :=
  TimesMonotone timelockRaiseRun ∧
  (submitAll .deployed timelockEnv timelockInit timelockRaiseRun).2 =
    [.scheduled 11 100 10 10 (some timelockRaiseOp), .scheduled 12 100 10 10 (some timelockPlainOp),
      .delivered 11 0, .minDelayChanged 10 100, .executed 11 timelockRaiseOp 110 false,
      .delivered 12 0, .executed 12 timelockPlainOp 110 false] ∧
  (submitAll .deployed timelockEnv timelockInit timelockRaiseRun).1.minDelay = 100 ∧
  110 < 100 + (submitAll .deployed timelockEnv timelockInit timelockRaiseRun).1.minDelay ∧
  schedule 110 (submitAll .deployed timelockEnv timelockInit timelockRaiseRun).1 13 10 none = none

/-! ## Authority -/

/-- **ONLY AN EXECUTED OPERATION CHANGES THE DELAY OR THE COUNCIL.** If a transaction changes
`minDelay` or the security council, its committed log contains an execution. -/
def Properties.ConfigChangesNeedExecution : Prop :=
  ∀ (E : Env) (s : State) (t : Tx),
    ((submit .deployed E s t).1.minDelay ≠ s.minDelay ∨
      (submit .deployed E s t).1.council ≠ s.council) →
    ∃ x op τ b, Effect.executed x op τ b ∈ (submit .deployed E s t).2

/-- **EVERY COMMITTED OUTGOING CALL BELONGS TO A COMMITTED EXECUTION.** In the committed log of
any sequence of transactions, every delivery of a call of operation `x` is followed, later in
the log, by the execution of `x`. -/
def Properties.DeliveriesBelongToExecutions : Prop :=
  ∀ (E : Env) (s : State) (txs : List Tx) (l₁ l₂ : List Effect) (x : OpId) (i : ℕ),
    (submitAll .deployed E s txs).2 = l₁ ++ .delivered x i :: l₂ →
    ∃ op τ b, Effect.executed x op τ b ∈ l₂

end Contracts.Governance
