import EraSpec.Contracts.EcosystemUpgradeExecutor.Specs.Lifecycle

/-!
# Properties: the stage guards exactly, and abandonment as a live escape hatch

Strengthenings of `EraSpec.Contracts.EcosystemUpgradeExecutor.Properties.Lifecycle`, over the
same model (`EraSpec.Contracts.EcosystemUpgradeExecutor.Specs.Lifecycle`, source commit
`afa407085`; the coordinator is deleted at `e561b9cc2`). Proofs are in
`EraSpec.Contracts.EcosystemUpgradeExecutor.Proofs.LifecycleStrong`.

**What this repairs.** `StageGuards` states necessary conditions only, and
`StagesMoveForward` is a safety statement. Both still hold for a variant of the model in
which `abandonPendingOperation` always reverts: the abandon conjunct of `StageGuards` and the
"occupied to free" move of `StagesMoveForward` say nothing about abandonment ever
succeeding, and no witness in `Properties.Lifecycle` takes an `abandon` step. The statements
here show that the guards are also sufficient, that abandonment is live, and what it leaves
behind.

## The guards, exactly

* With the CTM-reservation (`active`) conjuncts that `StageGuards` leaves out, each stage's
  transcribed guard is necessary **and sufficient** for the stage to succeed
  (`LifecycleStageGuardsExact`).
* Abandonment succeeds exactly when an operation is pending and the CTM domain is
  reserved. It then frees the slot and the reservation and changes nothing else: not the
  clock, not any timer, not the record of applied CTM legs (`LifecycleAbandonExact`).

## Abandonment is live

* **The escape hatch (headline).** Along any run from an idle state that uses no `forward`
  path, whenever an operation is pending (at `Prepared` or at `Executed`, before or after its
  timer's deadline), abandonment succeeds and leaves the coordinator idle
  (`LifecycleAbandonEnabledWhilePending`). It happens at `Prepared`, during the delay
  (`LifecycleAbandonDuringDelayWitness`), and at `Executed`, where the CTM leg that `stage1`
  applied stays applied (`LifecycleAbandonAfterExecuteWitness`).
* **Only abandonment frees a prepared slot.** A step that empties an occupied slot is
  abandonment or a `stage2` from `Executed` (`LifecycleFreeingIsStage2OrAbandon`).
* **Abandonment does not give the operation back.** It frees the slot, not the timer. An
  operation that names a `GovernanceUpgradeTimer`, once prepared in a run that starts at a
  positive timestamp, is refused by `stage0` at every later state, abandoned or not
  (`LifecyclePreparedGovernanceOpStaysRefused`). A retry needs an operation whose timer has
  not been started. The positive timestamp is needed, here and in
  `GovernanceTimerPreparesOnce`: at time `0` a zero-delay timer reads as unstarted after
  `startTimer()` (`LifecycleTimestampZeroReprepares`).
* **`forward` can block the escape hatch.** Through `forward` the coordinator's owner can
  release the CTM reservation while an operation is pending. Every coordinator entry point,
  abandonment included, is then refused (`LifecycleForwardReleaseWedgesCoordinator`), so the
  headline needs its "no `forward`" premise. In the model the owner can still return the
  coordinator to idle from every reachable state in at most two transactions, by first
  re-reserving the CTM domain through `forward` where needed
  (`LifecycleOwnerCanAlwaysReturnToIdle`). Two are sometimes needed
  (`LifecycleOwnerCanAlwaysReturnToIdleSatisfiable`).

**Liveness is about the model.** A step is a transaction the model allows. The model's
`abandon` omits two things the real `abandonPendingOperation(_unpauseMigrations)` does: the
core domain's release (`EcosystemUpgradeExecutor.sol:171-173`; the core domain is not
modelled) and, when `_unpauseMigrations` is true, `releaseMigrationPause` (:175-177). Either
can add a revert that these statements do not see. `LifecycleOwnerCanAlwaysReturnToIdle`
also relies on a forwarded `beginOperation`, whose `_reserveLeg` checks on the owner-supplied
manifest (`CTMUpgradeExecutor.sol:166-182`) the model omits. Refusals (`¬ ∃ s', Step …`)
are unaffected by these omissions, which only add runs.
-/

namespace Contracts.EcosystemUpgradeExecutor

/-! ## The guards, exactly -/

/-- **EACH STAGE'S GUARD, EXACTLY.** For every configuration, state and operation:
`stage0(op)` succeeds iff the slot is free, the CTM domain is idle, `op` is nonzero and names
a timer, and that timer's `startTimer()` succeeds. `stage1(op)` succeeds iff `op` is pending
at `Prepared`, the CTM domain is reserved, and `op`'s timer's deadline has passed; `stage2(op)`
the same at `Executed`. Abandonment succeeds iff something is pending and the CTM domain is
reserved. This is `StageGuards` with the `active` conjuncts added, in both directions. -/
def Properties.LifecycleStageGuardsExact : Prop :=
  ∀ (K : Config) (s : Sys) (op : Address),
    ((∃ s', Step K s (.stage0 op) s') ↔
      s.pending = 0 ∧ s.active = 0 ∧ op ≠ 0 ∧ ∃ t, K.opTimer op = some t ∧ StartOk K s t) ∧
    ((∃ s', Step K s (.stage1 op) s') ↔
      s.pending = op ∧ s.stage = .prepared ∧ s.active ≠ 0 ∧
        ∃ t, K.opTimer op = some t ∧ DeadlinePassed K s t) ∧
    ((∃ s', Step K s (.stage2 op) s') ↔
      s.pending = op ∧ s.stage = .executed ∧ s.active ≠ 0 ∧
        ∃ t, K.opTimer op = some t ∧ DeadlinePassed K s t) ∧
    ((∃ s', Step K s .abandon s') ↔ s.pending ≠ 0 ∧ s.active ≠ 0)

/-- **ABANDONMENT, EXACTLY.** `abandonPendingOperation` takes `s` to `s'` iff an operation is
pending, the CTM domain is reserved, and `s'` is `s` with the slot freed (`pendingOperation`
zero, `pendingStage` `None`) and the reservation released, and nothing else changed. The
clock, every timer's `deadline` and `maxDeadline`, `preparedAt` and the record of applied CTM
legs stay as they were. So abandonment does not reset the operation's timer, and does not
undo a CTM leg that `stage1` applied (the contract: "Whatever stage 1 already committed
stands", `EcosystemUpgradeExecutor.sol:156-157`). -/
def Properties.LifecycleAbandonExact : Prop :=
  ∀ (K : Config) (s s' : Sys),
    Step K s .abandon s' ↔
      s.pending ≠ 0 ∧ s.active ≠ 0 ∧ s' = { s with pending := 0, stage := .none, active := 0 }

/-! ## Abandonment is live -/

/-- **HEADLINE: ABANDONMENT IS ENABLED WHILE AN OPERATION IS PENDING.** Along any run from an
idle state that uses no `forward` path, whenever an operation is pending (at `Prepared` or at
`Executed`, whether or not its timer's deadline has passed), `abandonPendingOperation`
succeeds. The coordinator is then idle, and the clock, every timer and the record of applied
CTM legs are unchanged. This is the liveness side of the "occupied to free by abandonment"
move that `StagesMoveForward` allows. It is liveness in the model: see the module doc for
what the model's `abandon` omits. -/
def Properties.LifecycleAbandonEnabledWhilePending : Prop :=
  ∀ (K : Config) (s0 s : Sys) (ls : List Label), Idle s0 → Run K s0 ls s →
    (∀ l ∈ ls, ¬ l.isForward) → s.pending ≠ 0 →
    ∃ s', Step K s .abandon s' ∧ Idle s' ∧ s'.now = s.now ∧ s'.deadline = s.deadline ∧
      s'.maxDeadline = s.maxDeadline ∧ s'.legAppliedAt = s.legAppliedAt

/-- **ONLY `stage2` AND ABANDONMENT FREE THE SLOT.** For every configuration, every step that
empties an occupied slot is abandonment, or `stage2` of the pending operation from
`Executed`. So from `Prepared` the slot is freed only by abandonment. -/
def Properties.LifecycleFreeingIsStage2OrAbandon : Prop :=
  ∀ (K : Config) (s s' : Sys) (l : Label), s.pending ≠ 0 → s'.pending = 0 → Step K s l s' →
    l = .abandon ∨ (l = .stage2 s.pending ∧ s.stage = .executed)

/-- **A PREPARED OPERATION WITH A GOVERNANCE TIMER STAYS REFUSED.** Take a run that starts at a
positive timestamp and contains `stage0(op)`, where `op` names a `GovernanceUpgradeTimer`.
Then `stage0(op)` is refused at every state reachable from the run's end: after `stage2`,
after abandonment, however much time passes, and whatever other operations run. Nothing
resets the timer's `deadline`, and stage 0 refuses a started timer. -/
def Properties.LifecyclePreparedGovernanceOpStaysRefused : Prop :=
  ∀ (K : Config) (s0 s s' : Sys) (ls ls' : List Label) (op t : Address) (d a : ℕ) (g : Address),
    0 < s0.now → K.opTimer op = some t → K.timer t = .governance d a g →
    Run K s0 ls s → .stage0 op ∈ ls → Run K s ls' s' →
    ¬ ∃ s'', Step K s' (.stage0 op) s''

/-- **THE OWNER CAN ALWAYS RETURN THE COORDINATOR TO IDLE, IN THE MODEL.** From every state
reachable from an idle state, `forward` paths included, at most two transactions reach an
idle state. They are abandonment and `forward` paths only, and they leave the clock and every
timer's `deadline` unchanged. The statement asserts only that such a sequence exists; the
proof builds it by cases. If an operation is pending and the CTM domain is reserved,
abandonment suffices. If an operation is pending but the reservation was released through
`forward`, a forwarded `beginOperation` comes first. If nothing is pending but a forwarded
reservation is held, a forwarded release suffices; if neither, the state is already idle.
The real `beginOperation` runs `_reserveLeg` on the manifest the owner forwards
(`CTMUpgradeExecutor.sol:166-182`), checks the model omits. So the real recovery also needs
that leg to pass. -/
def Properties.LifecycleOwnerCanAlwaysReturnToIdle : Prop :=
  ∀ (K : Config) (s0 s : Sys) (ls : List Label), Idle s0 → Run K s0 ls s →
    ∃ ls' s', Run K s ls' s' ∧ ls'.length ≤ 2 ∧ (∀ l ∈ ls', l = .abandon ∨ l.isForward) ∧
      Idle s' ∧ s'.now = s.now ∧ s'.deadline = s.deadline

/-! ## Witnesses and the countermodel -/

/-- **ABANDONMENT DURING THE DELAY, AND WHAT IT LEAVES.** Operation `2` names timer `8`, a
`GovernanceUpgradeTimer` with a 10-second delay. Right after `stage0(2)` at time `100`, while
`stage1(2)` is still refused, abandonment succeeds and the coordinator is idle again. Timer
`8` stays started, with deadline `110`. So `stage0(2)` is refused from then on, while
`stage0(1)` succeeds: operation `1` names timer `7`, which has not been started. -/
def Properties.LifecycleAbandonDuringDelayWitness : Prop :=
  ∃ s s', Run wK w0 [.stage0 2] s ∧ (¬ ∃ s'', Step wK s (.stage1 2) s'') ∧
    Step wK s .abandon s' ∧ Idle s' ∧ s'.deadline 8 = 110 ∧
    (¬ ∃ s'', Step wK s' (.stage0 2) s'') ∧ ∃ s'', Step wK s' (.stage0 1) s''

/-- **ABANDONMENT AFTER STAGE 1 KEEPS THE APPLIED LEG.** With the zero-delay timer `7`,
`stage0(1)` and `stage1(1)` run at time `100`. Abandonment from `Executed` then returns the
coordinator to idle, and the CTM leg applied at `100` stays recorded. -/
def Properties.LifecycleAbandonAfterExecuteWitness : Prop :=
  ∃ s s', Run wK w0 [.stage0 1, .stage1 1] s ∧ s.stage = .executed ∧ Step wK s .abandon s' ∧
    Idle s' ∧ s'.legAppliedAt 1 = some 100

/-- **COUNTERMODEL: `forward` CAN BLOCK ABANDONMENT.** After `stage0(2)` at time `100`, the
coordinator's owner forwards the CTM executor's release, and the clock reaches `110`, timer
`8`'s deadline. Operation `2` is still pending at `Prepared` and its deadline has passed.
Yet abandonment is refused, because the CTM domain is no longer reserved, and so is every
stage of every operation. So `LifecycleAbandonEnabledWhilePending` needs its "no `forward`"
premise. In the model a forwarded `beginOperation(2, _)` re-reserves the domain, and
abandonment then returns the coordinator to idle. -/
def Properties.LifecycleForwardReleaseWedgesCoordinator : Prop :=
  ∃ s, Run wK w0 [.stage0 2, .forwardRelease, .tick 110] s ∧ s.pending = 2 ∧
    s.stage = .prepared ∧ DeadlinePassed wK s 8 ∧ (¬ ∃ s', Step wK s .abandon s') ∧
    (∀ op, (¬ ∃ s', Step wK s (.stage0 op) s') ∧ (¬ ∃ s', Step wK s (.stage1 op) s') ∧
      ¬ ∃ s', Step wK s (.stage2 op) s') ∧
    ∃ s1 s2, Step wK s (.forwardBegin 2) s1 ∧ Step wK s1 .abandon s2 ∧ Idle s2

/-- **COUNTERMODEL: THE POSITIVE-TIMESTAMP PREMISES ARE NEEDED.** At timestamp `0`,
`startTimer()` on the zero-delay timer `7` sets `deadline = 0 + 0 = 0`, which the timer reads
as not started. So from the idle witness state moved back to time `0`, the run `stage0(1)`,
abandonment, `stage0(1)` succeeds, and operation `1`, whose timer is a
`GovernanceUpgradeTimer`, is prepared twice. Neither `LifecyclePreparedGovernanceOpStaysRefused`
nor `GovernanceTimerPreparesOnce` holds without its `0 < s0.now` premise. -/
def Properties.LifecycleTimestampZeroReprepares : Prop :=
  ∃ s, Idle { w0 with now := 0 } ∧ Run wK { w0 with now := 0 } [.stage0 1, .abandon, .stage0 1] s ∧
    wK.opTimer 1 = some 7 ∧ wK.timer 7 = .governance 0 1209600 10 ∧
    [Label.stage0 1, .abandon, .stage0 1].count (.stage0 1) = 2

/-- **`LifecycleAbandonEnabledWhilePending`'s PREMISES HOLD, AT BOTH STAGES.** From the idle
witness state, `forward`-free runs reach a state where operation `2` is pending at
`Prepared`, and one where operation `1` is pending at `Executed`. -/
def Properties.LifecycleAbandonEnabledWhilePendingSatisfiable : Prop :=
  Idle w0 ∧
    (∃ s, Run wK w0 [.stage0 2] s ∧ (∀ l ∈ [Label.stage0 2], ¬ l.isForward) ∧
      s.pending ≠ 0 ∧ s.stage = .prepared) ∧
    ∃ s, Run wK w0 [.stage0 1, .stage1 1] s ∧
      (∀ l ∈ [Label.stage0 1, .stage1 1], ¬ l.isForward) ∧ s.pending ≠ 0 ∧ s.stage = .executed

/-- **`LifecycleFreeingIsStage2OrAbandon`'s PREMISES HOLD, FOR BOTH DISJUNCTS.** Abandonment
empties the slot at `Prepared`, and `stage2` empties it at `Executed`. -/
def Properties.LifecycleFreeingIsStage2OrAbandonSatisfiable : Prop :=
  (∃ s s', Run wK w0 [.stage0 2] s ∧ s.pending ≠ 0 ∧ s'.pending = 0 ∧ Step wK s .abandon s') ∧
    ∃ s s', Run wK w0 [.stage0 1, .stage1 1] s ∧ s.pending ≠ 0 ∧ s'.pending = 0 ∧
      Step wK s (.stage2 1) s'

/-- **`LifecyclePreparedGovernanceOpStaysRefused`'s PREMISES HOLD.** Operation `2` names timer
`8`, a `GovernanceUpgradeTimer`. From the witness state at time `100`, `stage0(2)` and
abandonment run, and then the clock moves on to `200`. -/
def Properties.LifecyclePreparedGovernanceOpStaysRefusedSatisfiable : Prop :=
  0 < w0.now ∧ wK.opTimer 2 = some 8 ∧ wK.timer 8 = .governance 10 1209600 10 ∧
    ∃ s s', Run wK w0 [.stage0 2, .abandon] s ∧ Label.stage0 2 ∈ [Label.stage0 2, .abandon] ∧
      Run wK s [.tick 200] s'

/-- **`LifecycleOwnerCanAlwaysReturnToIdle`'s PREMISES HOLD WHERE ONE TRANSACTION IS NOT
ENOUGH.** From the idle witness state, `stage0(2)` and a forwarded release reach a state that
is not idle, and from which no single transaction leads to an idle state. So the bound of
two is attained. -/
def Properties.LifecycleOwnerCanAlwaysReturnToIdleSatisfiable : Prop :=
  Idle w0 ∧ ∃ s, Run wK w0 [.stage0 2, .forwardRelease] s ∧ ¬ Idle s ∧
    ∀ (l : Label) (s' : Sys), Step wK s l s' → ¬ Idle s'

end Contracts.EcosystemUpgradeExecutor
