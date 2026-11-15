import EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimitsStrong

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


/-!
# Properties: recovery limits, on the manager's runs and across retries

Statements about `EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimitsStrong`; proofs are in
`EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimitsStrong`.

Each section takes a property of `EraSpec.Contracts.AtomicFlowManager.Properties.RecoveryLimits` and ties it to the
loop that produces the outcomes and to the manager whose leg the claim closes.  The properties there stay as they
are.

* **Limit 1.**  `stranding_is_terminal` is `accepted_below_full_recovery` together with `no_second_claim`.  Its
  last conjunct is a constant fact about the copy of `LegState`, independent of the outcome list.  Here: a
  successful claim is the manager's `Step.claim`, on outcomes the loop accepted (`legClaim_success_is_step`).
  After it, no run of the manager lets any claim of that leg succeed, whatever the world, the targets and the
  bundle data (`legClaim_success_closes_leg`).  And such a claim exists with fewer recoveries than calls, from a
  reachable leg (`partial_stranding_is_terminal`).
* **Limit 2.**  `retry_does_not_help` restates its premise, and no retry appears in it.  Here: if some call of
  the bundle reverts in every world that keeps an invariant, the loop's outcome list contains a revert in every
  later world that keeps it.  The claim is then refused in every such world (`blocked_retry_reverts`).  In the
  system where the leg is retried while the world changes and other legs move, the leg stays `Revertable` on
  every run (`blocked_leg_stays_revertable`).  `blocked_retry_witness` meets the premises with a world that does
  change, a bundle with a call that would recover, and an invariant that is the whole obstacle.  Without the
  condition the docstring's "a second attempt against the same targets fails identically" is false:
  `retry_succeeds_once_blocker_clears` is a claim that reverts, then succeeds once the blocking target's state
  changes.
-/

namespace Contracts.AtomicFlowManager.RecoveryLimitsStrong

open Contracts.AssetRouter.AtomicRecovery (World Call claimRefund outcomes)
open AttackVectors.RecoveryLimits (Outcome recoveredCount ClaimAccepted claimEnabled afterClaim)


/-! ## The copy is the manager's leg state -/

/-- **`RecoveryLimits`' LEG STATE IS THE MANAGER'S, RENAMED.**  `toModelLeg` and `ofModelLeg` are inverse.
`claimEnabled` is `ClaimGuard` read through them, and `afterClaim` is the manager's `Reverted`.  So
`RecoveryLimits.no_second_claim` says, of the manager's state, that `Reverted ≠ Revertable`. -/
abbrev Properties.leg_copy_is_model_leg :=
  (∀ s, toModelLeg (ofModelLeg s) = s) ∧ (∀ s, ofModelLeg (toModelLeg s) = s) ∧
    (∀ s, claimEnabled s ↔ toModelLeg s = .Revertable) ∧ toModelLeg afterClaim = .Reverted ∧
    ∀ (M : Manager) (f b : UInt256), ClaimGuard M f b ↔ claimEnabled (ofModelLeg (M.legState f b))


/-! ## Limit 1: an accepted claim closes the leg, on the manager's runs -/

/-- **A SUCCESSFUL CLAIM IS THE MANAGER'S `claim` STEP, ON OUTCOMES THE LOOP ACCEPTED.**  Suppose
`claimRefund(f, b)` succeeds on the manager.  Then the leg was claimable, the manager moved by exactly `Step.claim`
of that leg, and the outcomes the loop produced on the threaded world satisfy `ClaimAccepted`. -/
abbrev Properties.legClaim_success_is_step {X : Type} (step : World X → Call → Option (World X × Bool))
    {M : Manager} {f b : UInt256} {w : World X} {calls : List Call} {M' : Manager} {w' : World X}
    (h : legClaimRefund step M f b w calls = some (M', w')) :=
  ClaimGuard M f b ∧ M' = M.set f b .Reverted ∧ Step M M' ∧ ClaimAccepted (outcomes step w calls)


/-- **…AND IT CLOSES THE LEG FOR GOOD.**  After a successful `claimRefund(f, b)`, in every state the manager can
reach, every later `claimRefund(f, b)` reverts.  This holds for any world, any behaviour of the targets, and any
bundle data. -/
abbrev Properties.legClaim_success_closes_leg {X : Type} (step : World X → Call → Option (World X × Bool))
    {M : Manager} {f b : UInt256} {w : World X} {calls : List Call} {M' : Manager} {w' : World X}
    (h : legClaimRefund step M f b w calls = some (M', w')) :=
  ∀ N, Reach M' N → ∀ (Y : Type) (step' : World Y → Call → Option (World Y × Bool)) (u : World Y)
    (calls' : List Call), legClaimRefund step' N f b u calls' = none


/-- **SO PARTIAL STRANDING IS PERMANENT, ON THE REAL LOOP AND THE MANAGER'S RUNS.**  There is a leg reached from
fresh storage, and a bundle and target behaviour for it, such that three things hold.  The manager's
`claimRefund` succeeds.  Strictly fewer of the bundle's calls recover than the bundle contains, counted on the
outcomes the loop produced.  And from the state the claim leaves, no run of the manager lets any claim of that leg
succeed again.  The unrecovered calls get no second attempt.  This also meets the premises of the two statements
above. -/
abbrev Properties.partial_stranding_is_terminal :=
  ∃ (X : Type) (step : World X → Call → Option (World X × Bool)) (M : Manager) (f b : UInt256)
    (w : World X) (calls : List Call) (M' : Manager) (w' : World X),
    Reach empty M ∧ legClaimRefund step M f b w calls = some (M', w') ∧
      recoveredCount (outcomes step w calls) < calls.length ∧
      ∀ N, Reach M' N → ∀ (Y : Type) (step' : World Y → Call → Option (World Y × Bool)) (u : World Y)
        (calls' : List Call), legClaimRefund step' N f b u calls' = none


/-! ## Limit 2: a reverting target blocks every retry -/

/-- **A RETRY FAILS IN EVERY LATER WORLD THAT KEEPS THE BLOCKER BLOCKING.**  Suppose three things.  An invariant
`Inv` survives every successful call of the bundle.  It survives every step `Env` allows between attempts.  And
some call of the bundle reverts in every world where `Inv` holds.  Then in every world reached by `Env` steps from
one where `Inv` holds, the loop's outcome list contains a revert, the claim is not accepted, and `claimRefund`
reverts, whatever the leg's state.  `RecoveryLimits.retry_does_not_help` assumes the revert in its premise; here
it is derived for each later attempt. -/
abbrev Properties.blocked_retry_reverts {X : Type} (step : World X → Call → Option (World X × Bool))
    (Env : World X → World X → Prop) (Inv : World X → Prop) (calls : List Call)
    (hpres : ∀ c ∈ calls, ∀ u u' r, Inv u → step u c = some (u', r) → Inv u')
    (henv : ∀ u v, Inv u → Env u v → Inv v)
    (hblock : ∃ c ∈ calls, ∀ u, Inv u → step u c = none)
    {w w' : World X} (hw : Inv w) (hreach : Relation.ReflTransGen Env w w') :=
  Outcome.reverts ∈ outcomes step w' calls ∧ ¬ ClaimAccepted (outcomes step w' calls) ∧
    ∀ s, claimRefund step s w' calls = none


/-- **…SO THE LEG STAYS `Revertable`.**  Take the premises of `blocked_retry_reverts`, and a leg that is
`Revertable` in a world where `Inv` holds.  Then along every run of the retry system the leg stays `Revertable`
and `Inv` keeps holding.  That run may change the world, move other legs, and attempt the claim any number of
times.  The claim reverts in every state the run reaches. -/
abbrev Properties.blocked_leg_stays_revertable {X : Type} (step : World X → Call → Option (World X × Bool))
    (Env : World X → World X → Prop) (Inv : World X → Prop) (f b : UInt256) (calls : List Call)
    (hpres : ∀ c ∈ calls, ∀ u u' r, Inv u → step u c = some (u', r) → Inv u')
    (henv : ∀ u v, Inv u → Env u v → Inv v)
    (hblock : ∃ c ∈ calls, ∀ u, Inv u → step u c = none)
    {M : Manager} {w : World X} (hleg : M.legState f b = .Revertable) (hw : Inv w)
    {S : Manager × World X} (hrun : Relation.ReflTransGen (RetryStep step Env f b calls) (M, w) S) :=
  S.1.legState f b = .Revertable ∧ Inv S.2 ∧ legClaimRefund step S.1 f b S.2 calls = none


/-- **…BUT ONLY WHILE THE BLOCKER KEEPS BLOCKING.**  Read without a condition, "a second attempt against the
same targets fails identically" is false once the targets have state.  Here is a leg reached from fresh storage
whose claim reverts in a world `w`.  The same claim of the same leg, with the same bundle, succeeds in the world
that differs from `w` only in the blocking target's flag.  So `blocked_retry_reverts` needs its invariant
premises, and the true form of Limit 2 is conditional on the revert persisting. -/
abbrev Properties.retry_succeeds_once_blocker_clears :=
  ∃ (X : Type) (step : World X → Call → Option (World X × Bool)) (calls : List Call) (M : Manager)
    (w : World X),
    Reach empty M ∧ M.legState 0 0 = .Revertable ∧ legClaimRefund step M 0 0 w calls = none ∧
      (legClaimRefund step M 0 0 { w with paused := false } calls).isSome = true


/-- **THE PREMISES ARE SATISFIABLE, AND NOT TRIVIALLY.**  One setting meets every premise of
`blocked_retry_reverts` and `blocked_leg_stays_revertable`, with all of the following.
* The leg is reached from fresh storage.
* The retry run changes the world and moves another leg.
* The bundle has a call that recovers in every world where the invariant holds, so the revert blocks a real
  recovery.
* In the world that differs from the start only in the blocker's flag, the invariant fails and the same claim of
  the same leg succeeds.  So the invariant is the whole obstacle. -/
abbrev Properties.blocked_retry_witness :=
  ∃ (X : Type) (step : World X → Call → Option (World X × Bool)) (Env : World X → World X → Prop)
    (Inv : World X → Prop) (calls : List Call) (w : World X) (M : Manager) (S : Manager × World X),
    (∀ c ∈ calls, ∀ u u' r, Inv u → step u c = some (u', r) → Inv u') ∧
    (∀ u v, Inv u → Env u v → Inv v) ∧
    (∃ c ∈ calls, ∀ u, Inv u → step u c = none) ∧
    Inv w ∧ Reach empty M ∧ M.legState 0 0 = .Revertable ∧
    Relation.ReflTransGen (RetryStep step Env 0 0 calls) (M, w) S ∧
    Relation.ReflTransGen Env w S.2 ∧ S.2 ≠ w ∧ S.1 ≠ M ∧
    (∃ c ∈ calls, ∀ u, Inv u → ∃ u', step u c = some (u', true)) ∧
    ¬ Inv { w with paused := false } ∧
    (legClaimRefund step M 0 0 { w with paused := false } calls).isSome = true


end Contracts.AtomicFlowManager.RecoveryLimitsStrong
