import EraSpec.Contracts.AtomicFlowManager.Specs.ModelStrong

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


/-!
# Properties: `AtomicFlowManager`, stated over runs and over reentrant claims

Statements about `EraSpec.Contracts.AtomicFlowManager.Specs.ModelStrong`; proofs are in
`EraSpec.Contracts.AtomicFlowManager.Proofs.ModelStrong`.

Each section takes a claim from a docstring in `EraSpec.Contracts.AtomicFlowManager.Properties.Model` and states
it over the object the claim is about.  The one-state properties there stay as they are.

* `claim_requires_authorization` ("a refund requires a prior authorization") is about the state alone.  Here:
  only `authorize` makes a leg `Revertable` (`step_into_revertable_is_authorize`).  In every run, every claim of a
  leg that starts the run below `Revertable` comes after an `authorize` of that leg in the same run
  (`claim_event_preceded_by_authorize`).  The `Reach` form is `claimable_reach_passed_authorize`.
* `committed_not_claimable` and `unset_not_claimable` are constructor disequalities.  Here: from `Committed`,
  every run that makes the leg claimable touches it exactly once, by `authorize`
  (`committed_claimable_trace`).  From `Unset` it touches it exactly twice, by `append` then `authorize`
  (`unset_claimable_trace`).
* `rank_le_three` ("no run can move a leg more than three times") bounds `rank` and mentions no run.  Here: in
  every run, the number of steps that change a leg is the leg's rank gain (`legRun_changes_eq_rank_gain`), at
  most `3 - rank` of its starting state (`legRun_changes_le_three`).  `legRun_leg_trace` gives the steps
  themselves.
* `claim_closes_gate_before_interaction` cannot express an order between the write and the external calls.
  Here, `claimRefund`'s callback may re-enter the manager.  Under the deployed order the callback cannot claim
  the same leg (`writeFirst_callback_never_reclaims`), and each leg pays out exactly once, if at all
  (`writeFirst_payouts_exact`).  Under the reversed order one `Revertable` leg pays out any number of times
  (`writeAfter_unbounded_payouts`).  `claim_order_decides_double_payout` sets the two side by side from one start
  state.
-/

namespace Contracts.AtomicFlowManager.ModelStrong


/-! ## The labelled machine is the machine -/

/-- **A LABEL ADDS NOTHING TO A STEP.**  `LegStep` relates exactly the states `Step` relates. -/
abbrev Properties.legStep_iff_step {M N : Manager} :=
  Step M N ↔ ∃ e, LegStep M e N


/-- **A TRACE ADDS NOTHING TO REACHABILITY.**  A state is reachable exactly when some labelled run reaches it.  So
the run-level statements below cover every `Reach`, and say something about every run behind it. -/
abbrev Properties.reach_iff_legRun {M N : Manager} :=
  Reach M N ↔ ∃ es, LegRun M es N


/-! ## A refund requires a prior authorization -/

/-- **ONLY `authorize` MAKES A LEG `Revertable`.**  Suppose one step takes leg `(f, b)` from any other state to
`Revertable`.  Then the step was `authorize` of that leg: the leg was `Committed` before it, and the step wrote
nothing else. -/
abbrev Properties.step_into_revertable_is_authorize {M N : Manager} (h : Step M N) {f b : UInt256}
    (hpre : M.legState f b ≠ .Revertable) (hpost : N.legState f b = .Revertable) :=
  AuthorizeGuard M f b ∧ N = M.set f b .Revertable


/-- **A REFUND REQUIRES A PRIOR AUTHORIZATION, ON EVERY RUN.**  Take any run whose start state has leg `(f, b)`
below `Revertable`.  Every `claim` of the leg in it comes after an `authorize` of the same leg, earlier in the same
run. -/
abbrev Properties.claim_event_preceded_by_authorize {M N : Manager} {es : List LegEvent}
    (h : LegRun M es N) {f b : UInt256} (hpre : M.legState f b ≠ .Revertable)
    {es₁ es₂ : List LegEvent} (hsplit : es = es₁ ++ ⟨.claim, f, b⟩ :: es₂) :=
  (⟨.authorize, f, b⟩ : LegEvent) ∈ es₁


/-- **…IN `Reach` FORM.**  If leg `(f, b)` starts below `Revertable` and ends claimable, the run passed through
an `authorize` of the leg.  There is a state `P` on the way where `authorize` was enabled, and the run continued
from the state `authorize` wrote. -/
abbrev Properties.claimable_reach_passed_authorize {M N : Manager} (h : Reach M N) {f b : UInt256}
    (hpre : M.legState f b ≠ .Revertable) (hg : ClaimGuard N f b) :=
  ∃ P, Reach M P ∧ AuthorizeGuard P f b ∧ Reach (P.set f b .Revertable) N


/-! ## From `Committed` or `Unset`, the claim gate opens only through `authorize` -/

/-- **FROM `Committed`, ONE `authorize` AND NOTHING ELSE.**  Suppose leg `(f, b)` is `Committed` at the start of a
run and claimable at its end.  Then exactly one step of the run touched the leg, and it was `authorizeRefund`'s,
where the timeout proof is checked. -/
abbrev Properties.committed_claimable_trace {M N : Manager} {es : List LegEvent} (h : LegRun M es N)
    {f b : UInt256} (hc : M.legState f b = .Committed) (hg : ClaimGuard N f b) :=
  (legTrace f b es).map LegEvent.op = [.authorize]


/-- **FROM `Unset`, `append` THEN `authorize`.**  If leg `(f, b)` is `Unset` at the start of a run (as every leg is
in `empty`) and claimable at its end, then the steps that touched the leg were `append` and then `authorize`,
exactly those two. -/
abbrev Properties.unset_claimable_trace {M N : Manager} {es : List LegEvent} (h : LegRun M es N)
    {f b : UInt256} (hu : M.legState f b = .Unset) (hg : ClaimGuard N f b) :=
  (legTrace f b es).map LegEvent.op = [.append, .authorize]


/-! ## How often a run moves a leg -/

/-- **ONE STEP MOVES A LEG BY AT MOST ONE RANK.**  For every leg, a step either leaves it alone or moves it to the
next rank.  It never skips a state and never stays put while writing.  This strict per-step fact is what
`step_rank_mono`'s `≤` leaves out. -/
abbrev Properties.step_leg_same_or_next {M N : Manager} (h : Step M N) (f b : UInt256) :=
  N.legState f b = M.legState f b ∨ rank (N.legState f b) = rank (M.legState f b) + 1


/-- **A STEP CHANGES A LEG EXACTLY WHEN ITS LABEL NAMES THE LEG.** -/
abbrev Properties.legStep_changes_iff_names {M N : Manager} {e : LegEvent} (h : LegStep M e N)
    (f b : UInt256) :=
  N.legState f b ≠ M.legState f b ↔ (e.flow = f ∧ e.bundle = b)


/-- **WHAT A RUN DOES TO ONE LEG.**  The steps of a run that touch leg `(f, b)` are, in order, exactly the
lifecycle operations between the leg's state at the start and its state at the end. -/
abbrev Properties.legRun_leg_trace {M N : Manager} {es : List LegEvent} (h : LegRun M es N)
    (f b : UInt256) :=
  (legTrace f b es).map LegEvent.op = opsBetween (M.legState f b) (N.legState f b)


/-- **A RUN CHANGES A LEG EXACTLY AS OFTEN AS IT RAISES ITS RANK.**  Count the steps of the run that change leg
`(f, b)`'s state, or count the steps that name the leg.  Either way the number is the leg's rank at the end minus
its rank at the start. -/
abbrev Properties.legRun_changes_eq_rank_gain {M N : Manager} {es : List LegEvent} (h : LegRun M es N)
    (f b : UInt256) :=
  legChanges f b M es = rank (N.legState f b) - rank (M.legState f b) ∧
    (legTrace f b es).length = rank (N.legState f b) - rank (M.legState f b)


/-- **NO RUN MOVES A LEG MORE THAN THREE TIMES.**  More precisely, no run moves it more than `3 - rank` of its
starting state times, however long the run is and however many other legs it moves. -/
abbrev Properties.legRun_changes_le_three {M N : Manager} {es : List LegEvent} (h : LegRun M es N)
    (f b : UInt256) :=
  legChanges f b M es ≤ 3 - rank (M.legState f b)


/-! ## The premises are satisfiable, and the bound is attained -/

/-- **ONE RUN MEETS EVERY PREMISE ABOVE.**  From fresh storage the witness run appends leg `(0, 0)`, appends leg
`(0, 1)`, authorizes `(0, 0)` and claims it.
* Its trace splits around the claim, with `(0, 0)` starting `Unset`.  This meets
  `claim_event_preceded_by_authorize` and the premises of the run-level statements.
* Its prefix ends with `(0, 0)` claimable, as a labelled run and as a `Reach`.  This meets `unset_claimable_trace`
  and `claimable_reach_passed_authorize`.
* From `witness₁` the leg starts `Committed`, which meets `committed_claimable_trace`.
* Its third step makes the leg `Revertable`, which meets `step_into_revertable_is_authorize`,
  `step_leg_same_or_next` and `legStep_changes_iff_names`.
* It moves `(0, 0)` three times, the bound from `Unset`, and moves `(0, 1)` once. -/
abbrev Properties.modelStrong_runs_witness :=
  LegRun empty witnessTrace witness₄ ∧
    witnessTrace = witnessTrace.take 3 ++ ⟨.claim, 0, 0⟩ :: [] ∧ empty.legState 0 0 = .Unset ∧
    LegRun empty (witnessTrace.take 3) witness₃ ∧ Reach empty witness₃ ∧ ClaimGuard witness₃ 0 0 ∧
    LegRun witness₁ [⟨.append, 0, 1⟩, ⟨.authorize, 0, 0⟩] witness₃ ∧
      witness₁.legState 0 0 = .Committed ∧
    LegStep witness₂ ⟨.authorize, 0, 0⟩ witness₃ ∧ Step witness₂ witness₃ ∧
      witness₂.legState 0 0 ≠ .Revertable ∧ witness₃.legState 0 0 = .Revertable ∧
    legChanges 0 0 empty witnessTrace = 3 ∧ legChanges 0 1 empty witnessTrace = 1


/-! ## Reentrant claims: the order of the write is what matters -/

/-- **WRITE-FIRST EXECUTIONS ARE RUNS OF THE ATOMIC MACHINE.**  However deeply `claimRefund`'s recovery calls
re-enter the manager, under the deployed order the manager's state moves only by `Step`s.  So every `Reach`
result in `Properties/Model.lean` covers reentrant executions too. -/
abbrev Properties.writeFirst_nestedRun_reach {M N : Manager} {log : List LegKey}
    (h : NestedRun .writeFirst M log N) :=
  Reach M N


/-- **EVERY ATOMIC RUN IS AN EXECUTION, UNDER EITHER ORDER.**  Unnested claims are the same under both orders.  The
two orders differ only through what a callback can do. -/
abbrev Properties.reach_nestedRun (o : ClaimOrder) {M N : Manager} (h : Reach M N) :=
  ∃ log, NestedRun o M log N


/-- **(i) UNDER THE DEPLOYED ORDER, A CLAIM'S CALLBACK CANNOT CLAIM THE SAME LEG.**  Take `claimRefund(f, b)` on a
claimable leg.  Its callback runs from the state the claim wrote.  Nothing the callback does, nested to any depth,
completes a claim of `(f, b)`, and the leg is still `Reverted` when the callback returns.  This is the formal
content of the comment at `AtomicFlowManager.sol:171-174`. -/
abbrev Properties.writeFirst_callback_never_reclaims {M N₁ : Manager} {f b : UInt256}
    {callback : List LegKey} (hg : ClaimGuard M f b)
    (hcb : NestedRun .writeFirst (M.set f b .Reverted) callback N₁) :=
  (f, b) ∉ callback ∧ N₁.legState f b = .Reverted


/-- **UNDER THE DEPLOYED ORDER, EACH LEG PAYS OUT EXACTLY ONCE, IF AT ALL.**  In every execution, however nested,
count the completed claims of leg `(f, b)`.  The count is `1` if the execution took the leg to `Reverted` and `0`
otherwise. -/
abbrev Properties.writeFirst_payouts_exact {M N : Manager} {log : List LegKey}
    (h : NestedRun .writeFirst M log N) (f b : UInt256) :=
  log.count (f, b) = if M.legState f b ≠ .Reverted ∧ N.legState f b = .Reverted then 1 else 0


/-- **…SO AT MOST ONCE.** -/
abbrev Properties.writeFirst_payout_at_most_once {M N : Manager} {log : List LegKey}
    (h : NestedRun .writeFirst M log N) (f b : UInt256) :=
  log.count (f, b) ≤ 1


/-- **(ii) UNDER THE REVERSED ORDER, ONE `Revertable` LEG PAYS OUT ANY NUMBER OF TIMES.**  Fix a claimable leg
and any `k`.  Some execution completes `k` claims of it: each claim's callback re-enters `claimRefund(f, b)`.
Each nested claim passes its guard, because the leg is still `Revertable` while the callback runs. -/
abbrev Properties.writeAfter_unbounded_payouts {M : Manager} {f b : UInt256} (hg : ClaimGuard M f b)
    (k : ℕ) :=
  ∃ N, NestedRun .writeAfter M (List.replicate k (f, b)) N


/-- **THE ORDER DECIDES WHETHER A LEG CAN BE PAID TWICE.**  Start from one claimable leg.  Under the deployed order
no execution pays it twice.  Under the reversed order there is an execution that pays it twice: `claimRefund(f, b)`
whose callback calls `claimRefund(f, b)` once. -/
abbrev Properties.claim_order_decides_double_payout {M : Manager} {f b : UInt256} (hg : ClaimGuard M f b) :=
  (∀ log N, NestedRun .writeFirst M log N → log.count (f, b) ≤ 1) ∧
    ∃ N, NestedRun .writeAfter M [(f, b), (f, b)] N


/-- **THE PREMISES ARE SATISFIABLE, AND NESTING IS REAL UNDER THE DEPLOYED ORDER TOO.**  From fresh storage, a run
makes legs `(0, 0)` and `(0, 1)` claimable.  Then, under the deployed order, `claimRefund(0, 0)`'s callback claims
leg `(0, 1)`, a different leg, which the source comment calls "independent and equally guarded".  Each leg pays
once.  So the nesting in the deployed-order results above does real work. -/
abbrev Properties.nestedRun_witness :=
  ∃ M N₁ N, Reach empty M ∧ ClaimGuard M 0 0 ∧ ClaimGuard M 0 1 ∧
    NestedRun .writeFirst (M.set 0 0 .Reverted) [(0, 1)] N₁ ∧
    NestedRun .writeFirst M [(0, 1), (0, 0)] N ∧
    N.legState 0 0 = .Reverted ∧ N.legState 0 1 = .Reverted


end Contracts.AtomicFlowManager.ModelStrong
