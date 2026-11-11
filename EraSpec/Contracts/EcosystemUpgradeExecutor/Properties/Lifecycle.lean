import EraSpec.Contracts.EcosystemUpgradeExecutor.Specs.Lifecycle

/-!
# Properties: the coordinator's lifecycle, and what its timer guarantees

Statements about `EraSpec.Contracts.EcosystemUpgradeExecutor.Specs.Lifecycle` (source
commit `afa407085`; the coordinator is deleted at `e561b9cc2`). Proofs are in
`EraSpec.Contracts.EcosystemUpgradeExecutor.Proofs.Lifecycle`.

## The lifecycle

* Each stage needs its transcribed guard (`StageGuards`: necessary conditions only, without
  the CTM-reservation conjunct), and the slot moves only forward: free → `Prepared` →
  `Executed` → free, or from occupied to free by abandonment; never back from `Executed` to
  `Prepared` (`StagesMoveForward`). From an idle start the operation slot is empty exactly
  when the stage is `None` (`SlotEmptyIffStageNone`).
* `StageGuards` and `StagesMoveForward` are safety statements. Both would still hold if
  abandonment always reverted, and no witness below takes an `abandon` step. That the guards,
  with the reservation conjunct, are also sufficient, and that abandonment succeeds whenever
  an operation is pending, are separate results in
  `EraSpec.Contracts.EcosystemUpgradeExecutor.Properties.LifecycleStrong`
  (`LifecycleStageGuardsExact`, `LifecycleAbandonEnabledWhilePending`).
* Without `forward`, the CTM domain's reservation is exactly the pending operation
  (`ReservationTracksSlot`).
* A `GovernanceUpgradeTimer` starts once, so stage 0 refuses a timer bound to someone else
  or already started (`Stage0RefusesForeignOrStartedTimer`), and an operation whose timer is
  one is prepared at most once in any run that starts at a positive timestamp
  (`GovernanceTimerPreparesOnce`).

## The timer

The delay is exactly what the manifest-named timer enforces, and the coordinator checks
nothing else about it:

* **The bound.** If the named timer is a `GovernanceUpgradeTimer` with `INITIAL_DELAY = d`,
  every `stage1` of the operation comes at least `d` seconds after the `stage0` that
  prepared it (`ExecutionWaitsForTheNamedTimer`), and that is attained
  (`TimerBoundIsTight`: stage 1 is refused at 9 seconds and admitted at 10).
* **The boundary.** A manifest naming a `GovernanceUpgradeTimer` with zero delay passes every
  check, and all three stages run at one timestamp (`ZeroDelayTimerPasses`). So does a
  manifest naming any contract whose fallback does not revert
  (`PermissiveTimerPasses`).
* **The bound is on `stage1`, not on the CTM leg.** The coordinator's owner can forward
  `applyOperation` to the reserved CTM executor right after stage 0, in the same block,
  while `stage1` is still refused (`ForwardAppliesLegBeforeTheDelay`).
-/

namespace Contracts.EcosystemUpgradeExecutor

/-! ## The lifecycle -/

/-- **EACH STAGE'S GUARD.** `stage0` needs the slot free, the CTM domain idle, a nonzero
operation naming a timer, and that timer's `startTimer()` to succeed; `stage1` needs the
operation pending at `Prepared` and its timer's deadline passed; `stage2` the same at
`Executed`; abandonment needs something pending.  These are necessary conditions (one
direction), and the `active ≠ 0` conjunct of `stage1`/`stage2`/`abandon` is not listed. The
abandon conjunct would hold even if abandonment always reverted. Sufficiency, with the
`active` conjuncts, is `LifecycleStageGuardsExact` (`Properties.LifecycleStrong`). -/
def Properties.StageGuards : Prop :=
  ∀ (K : Config) (s s' : Sys) (op : Address),
    (Step K s (.stage0 op) s' →
      s.pending = 0 ∧ s.active = 0 ∧ op ≠ 0 ∧ ∃ t, K.opTimer op = some t ∧ StartOk K s t) ∧
    (Step K s (.stage1 op) s' →
      s.pending = op ∧ s.stage = .prepared ∧ ∃ t, K.opTimer op = some t ∧ DeadlinePassed K s t) ∧
    (Step K s (.stage2 op) s' →
      s.pending = op ∧ s.stage = .executed ∧ ∃ t, K.opTimer op = some t ∧ DeadlinePassed K s t) ∧
    (Step K s .abandon s' → s.pending ≠ 0)

/-- **THE STAGES MOVE ONLY FORWARD.** From a state whose slot is empty exactly when its
stage is `None`, every transaction either leaves the slot alone, fills an empty slot at
`Prepared`, moves the pending operation from `Prepared` to `Executed`, or empties an
occupied slot. This is a safety statement: it does not say that any of these moves can
happen. That abandonment empties the slot whenever an operation is pending (on runs without
`forward`) is `LifecycleAbandonEnabledWhilePending`, and that only abandonment or `stage2`
empty it is `LifecycleFreeingIsStage2OrAbandon` (both in `Properties.LifecycleStrong`). -/
def Properties.StagesMoveForward : Prop :=
  ∀ (K : Config) (s s' : Sys) (l : Label), (s.pending = 0 ↔ s.stage = .none) →
    Step K s l s' → Advances s s'

/-- **THE SLOT IS EMPTY EXACTLY WHEN THE STAGE IS `None`**, along any run from an idle
state. -/
def Properties.SlotEmptyIffStageNone : Prop :=
  ∀ (K : Config) (s0 s : Sys) (ls : List Label), Idle s0 → Run K s0 ls s →
    (s.pending = 0 ↔ s.stage = .none)

/-- **WITHOUT `forward`, THE CTM DOMAIN IS RESERVED FOR EXACTLY THE PENDING OPERATION.**
Along any run from an idle state that uses no `forward` path, the CTM executor's
`activeOperation` is the coordinator's `pendingOperation`. -/
def Properties.ReservationTracksSlot : Prop :=
  ∀ (K : Config) (s0 s : Sys) (ls : List Label), Idle s0 → Run K s0 ls s →
    (∀ l ∈ ls, ¬ l.isForward) → s.active = s.pending

/-- **STAGE 0 REFUSES A FOREIGN OR STARTED TIMER.** If an operation names a
`GovernanceUpgradeTimer` whose `TIMER_GOVERNANCE` is not the coordinator, or whose deadline
is already set, `stage0` of that operation has no successful execution. -/
def Properties.Stage0RefusesForeignOrStartedTimer : Prop :=
  ∀ (K : Config) (s : Sys) (op t : Address) (d a : ℕ) (g : Address),
    K.opTimer op = some t → K.timer t = .governance d a g → (g ≠ K.C ∨ s.deadline t ≠ 0) →
    ¬ ∃ s', Step K s (.stage0 op) s'

/-- **AN OPERATION WITH A GOVERNANCE TIMER IS PREPARED AT MOST ONCE.** In any run starting
at a positive timestamp, `stage0(op)` occurs at most once if `op`'s timer is a
`GovernanceUpgradeTimer`. -/
def Properties.GovernanceTimerPreparesOnce : Prop :=
  ∀ (K : Config) (s0 s : Sys) (ls : List Label) (op t : Address) (d a : ℕ) (g : Address),
    0 < s0.now → K.opTimer op = some t → K.timer t = .governance d a g → Run K s0 ls s →
    ls.count (.stage0 op) ≤ 1

/-! ## The timer -/

/-- **HEADLINE: STAGE 1 WAITS `INITIAL_DELAY` AFTER THE STAGE 0 THAT PREPARED IT.** Along
any run from an idle state (`forward` paths included), if `stage1(op)` succeeds and `op`
names a `GovernanceUpgradeTimer` with `INITIAL_DELAY = d`, then the run so far contains a
`stage0(op)` that no later `stage0` of any operation follows, and that `stage0` ran at least
`d` seconds before. -/
def Properties.ExecutionWaitsForTheNamedTimer : Prop :=
  ∀ (K : Config) (s0 s s' : Sys) (ls : List Label) (op t : Address) (d a : ℕ) (g : Address),
    Idle s0 → Run K s0 ls s → Step K s (.stage1 op) s' →
    K.opTimer op = some t → K.timer t = .governance d a g →
    ∃ l1 l2 sa sb, ls = l1 ++ .stage0 op :: l2 ∧ Run K s0 l1 sa ∧ Step K sa (.stage0 op) sb ∧
      Run K sb l2 s ∧ (∀ l ∈ l2, ∀ op', l ≠ .stage0 op') ∧ sa.now + d ≤ s.now

/-- **A ZERO-DELAY TIMER PASSES.** Operation `1` names timer `7`, a `GovernanceUpgradeTimer`
bound to the coordinator with `INITIAL_DELAY = 0`. From the idle witness state at time
`100`, all three stages succeed without the clock moving; the CTM leg is applied at `100`,
the timestamp of stage 0, and the coordinator ends idle. -/
def Properties.ZeroDelayTimerPasses : Prop :=
  ∃ s, Run wK w0 [.stage0 1, .stage1 1, .stage2 1] s ∧
    wK.timer 7 = .governance 0 1209600 10 ∧ s.now = 100 ∧ s.legAppliedAt 1 = some 100 ∧ Idle s

/-- **A PERMISSIVE TIMER PASSES.** Operation `3` names timer `9`, a contract whose
`startTimer()` and `checkDeadline()` return without reverting. All three stages succeed at
time `100`. -/
def Properties.PermissiveTimerPasses : Prop :=
  ∃ s, Run wK w0 [.stage0 3, .stage1 3, .stage2 3] s ∧
    wK.timer 9 = .permissive ∧ s.now = 100 ∧ s.legAppliedAt 3 = some 100 ∧ Idle s

/-- **THE DELAY GATES `stage1`, NOT THE CTM LEG.** Operation `2` names a timer with a
10-second delay. Right after `stage0(2)` at time `100`, the coordinator's owner forwards
`applyOperation` to the CTM executor: the leg is applied at `100`, while `stage1(2)` is
still refused. -/
def Properties.ForwardAppliesLegBeforeTheDelay : Prop :=
  ∃ s, Run wK w0 [.stage0 2, .forwardApply] s ∧ wK.timer 8 = .governance 10 1209600 10 ∧
    s.now = 100 ∧ s.legAppliedAt 2 = some 100 ∧ ¬ ∃ s', Step wK s (.stage1 2) s'

/-! ## Witnesses -/

/-- **THE BOUND IS ATTAINED.** Operation `2` names a timer with a 10-second delay; after
`stage0(2)` at `100`, `stage1(2)` is refused at `109` and succeeds at `110`. -/
def Properties.TimerBoundIsTight : Prop :=
  ∃ s, Run wK w0 [.stage0 2, .tick 109] s ∧ wK.timer 8 = .governance 10 1209600 10 ∧
    (¬ ∃ s', Step wK s (.stage1 2) s') ∧
    ∃ s'' s''', Step wK s (.tick 110) s'' ∧ Step wK s'' (.stage1 2) s''' ∧ s''.now = 110

end Contracts.EcosystemUpgradeExecutor
