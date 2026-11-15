import EraSpec.Contracts.AtomicFlowManager.Properties.RecoveryLimitsStrong
import EraSpec.Contracts.AtomicFlowManager.Proofs.Model
import EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimits
import EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery


/-!
# Proofs: recovery limits, on the manager's runs and across retries

Proofs of `EraSpec.Contracts.AtomicFlowManager.Properties.RecoveryLimitsStrong`.

Limit 1 has two parts.  A successful `claimRefund` came through the `Revertable` branch and returned `Reverted`
(`claimRefund_some`).  `AtomicRecovery.claimSucceedsIffAccepted` turns that success into `ClaimAccepted` of the
threaded outcomes.  Terminality is `reverted_absorbing`, plus the guard at the top of `claimRefund`.  Limit 2 is
`AtomicRecovery.recoverBundle_eq_none_of_blocking`, applied at every world an `Env` run reaches.  The invariant
travels along the run, and the retry system carries it, together with the leg's `Revertable`, as one invariant.
-/

namespace Contracts.AtomicFlowManager.RecoveryLimitsStrong

open Contracts.AssetRouter.AtomicRecovery
  (World Call CallData claimRefund recoverBundle outcomes recoverBundle_eq_none_of_blocking
    recoverBundle_none_outcomes claimRefund_eq_none claimSucceedsIffAccepted)
open AttackVectors.RecoveryLimits (Outcome LoopCompletes recoveredCount ClaimAccepted claimEnabled afterClaim)

variable {X : Type}


/-! ## The leg-state bijection -/

lemma to_of (s : LegState) : toModelLeg (ofModelLeg s) = s := by
  cases s <;> rfl

lemma of_to (s : AttackVectors.RecoveryLimits.LegState) : ofModelLeg (toModelLeg s) = s := by
  cases s <;> rfl

theorem leg_copy_is_model_leg : Properties.leg_copy_is_model_leg := by
  unfold Properties.leg_copy_is_model_leg
  refine ⟨to_of, of_to, ?_, rfl, ?_⟩
  · intro s
    cases s <;> decide
  · intro M f b
    unfold ClaimGuard claimEnabled
    cases M.legState f b <;> decide


/-! ## What a successful `claimRefund` was -/

/-- A successful `claimRefund` started from `Revertable` and returns `Reverted`. -/
lemma claimRefund_some {step : World X → Call → Option (World X × Bool)}
    {s s' : AttackVectors.RecoveryLimits.LegState} {w w' : World X} {calls : List Call}
    (h : claimRefund step s w calls = some (s', w')) :
    s = .Revertable ∧ s' = .Reverted := by
  unfold claimRefund at h
  by_cases hs : s = .Revertable
  · rw [ite_eq_right (not_not.mpr hs)] at h
    refine ⟨hs, ?_⟩
    rcases hr : recoverBundle step w calls with _ | ⟨w'', n⟩ <;> rw [hr] at h
    · cases h
    · dsimp only at h
      by_cases hn : n = 0
      · rw [ite_eq_left hn] at h
        cases h
      · rw [ite_eq_right hn] at h
        cases h
        rfl
  · rw [ite_eq_left hs] at h
    cases h

/-- From any state but `Revertable`, the manager's claim reverts. -/
lemma legClaimRefund_of_not_revertable (step : World X → Call → Option (World X × Bool)) {M : Manager}
    {f b : UInt256} (w : World X) (calls : List Call) (hM : M.legState f b ≠ .Revertable) :
    legClaimRefund step M f b w calls = none := by
  unfold legClaimRefund
  have hs : ofModelLeg (M.legState f b) ≠ .Revertable := by
    intro h
    apply hM
    rw [← to_of (M.legState f b), h]
    rfl
  unfold claimRefund
  rw [ite_eq_left hs]
  rfl

theorem legClaim_success_is_step (step : World X → Call → Option (World X × Bool))
    {M : Manager} {f b : UInt256} {w : World X} {calls : List Call} {M' : Manager} {w' : World X}
    (h : legClaimRefund step M f b w calls = some (M', w')) :
    Properties.legClaim_success_is_step step (h := h) := by
  unfold Properties.legClaim_success_is_step
  unfold legClaimRefund at h
  obtain ⟨⟨s', w''⟩, hc, he⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hs, hs'⟩ := claimRefund_some hc
  have hM : M.legState f b = .Revertable := by
    rw [← to_of (M.legState f b), hs]
    rfl
  have hM' : M' = M.set f b .Reverted := by
    have h1 := congrArg Prod.fst he
    dsimp only at h1
    rw [← h1, hs']
    rfl
  have hacc : ClaimAccepted (outcomes step w calls) := by
    rw [← claimSucceedsIffAccepted]
    rw [hs] at hc
    rw [hc]
    rfl
  refine ⟨hM, hM', ?_, hacc⟩
  rw [hM']
  exact Step.claim hM

theorem legClaim_success_closes_leg (step : World X → Call → Option (World X × Bool))
    {M : Manager} {f b : UInt256} {w : World X} {calls : List Call} {M' : Manager} {w' : World X}
    (h : legClaimRefund step M f b w calls = some (M', w')) :
    Properties.legClaim_success_closes_leg step (h := h) := by
  unfold Properties.legClaim_success_closes_leg
  intro N hN Y step' u calls'
  obtain ⟨-, hM', -, -⟩ := legClaim_success_is_step step h
  have hw : M'.legState f b = .Reverted := by
    rw [hM']
    exact set_same
  have hrev : N.legState f b = .Reverted := reverted_absorbing hN hw
  exact legClaimRefund_of_not_revertable step' u calls' (by rw [hrev]; decide)


/-! ## Limit 1, concretely -/

/-- A world with fresh router and vault storage, unpaused, and `()` for the rest. -/
def unitWorld : World Unit :=
  ⟨Contracts.AssetRouter.empty, Contracts.NativeTokenVault.empty.vault, false, ()⟩

/-- Targets: `1` recovers, `2` declines, anything else reverts. -/
def partialStep : World Unit → Call → Option (World Unit × Bool) := fun w c =>
  if c.target = 1 then some (w, true) else if c.target = 2 then some (w, false) else none

/-- One recovering call and two declining ones. -/
def partialCalls : List Call := [⟨1, 0, 0, .other⟩, ⟨2, 0, 0, .other⟩, ⟨2, 0, 0, .other⟩]

/-- Leg `(0, 0)` appended and authorized. -/
def revertableLeg : Manager := (empty.set 0 0 .Committed).set 0 0 .Revertable

lemma revertableLeg_reach : Reach empty revertableLeg :=
  Reach.tail (Reach.tail Reach.refl (Step.append (by unfold AppendGuard; decide)))
    (Step.authorize (by unfold AuthorizeGuard; decide))

lemma partial_claim :
    legClaimRefund partialStep revertableLeg 0 0 unitWorld partialCalls =
      some (revertableLeg.set 0 0 .Reverted, unitWorld) :=
  rfl

theorem partial_stranding_is_terminal : Properties.partial_stranding_is_terminal := by
  unfold Properties.partial_stranding_is_terminal
  refine ⟨Unit, partialStep, revertableLeg, 0, 0, unitWorld, partialCalls, _, _, revertableLeg_reach,
    partial_claim, by decide, ?_⟩
  exact legClaim_success_closes_leg partialStep partial_claim


/-! ## Limit 2 -/

/-- `Inv` travels along an `Env` run. -/
lemma inv_along {Env : World X → World X → Prop} {Inv : World X → Prop}
    (henv : ∀ u v, Inv u → Env u v → Inv v) {w w' : World X} (hw : Inv w)
    (hreach : Relation.ReflTransGen Env w w') : Inv w' := by
  induction hreach with
  | refl => exact hw
  | tail _ he ih => exact henv _ _ ih he

/-- The single-world core: in a world where `Inv` holds, the loop reverts. -/
lemma recoverBundle_blocked {step : World X → Call → Option (World X × Bool)} {Inv : World X → Prop}
    {calls : List Call} (hpres : ∀ c ∈ calls, ∀ u u' r, Inv u → step u c = some (u', r) → Inv u')
    (hblock : ∃ c ∈ calls, ∀ u, Inv u → step u c = none) {u : World X} (hu : Inv u) :
    recoverBundle step u calls = none := by
  obtain ⟨c₀, hc₀, hb₀⟩ := hblock
  refine recoverBundle_eq_none_of_blocking Inv (· = c₀) calls u hpres ?_ ⟨c₀, hc₀, rfl⟩ hu
  intro c _ hc v hv
  subst hc
  exact hb₀ v hv

theorem blocked_retry_reverts (step : World X → Call → Option (World X × Bool))
    (Env : World X → World X → Prop) (Inv : World X → Prop) (calls : List Call)
    (hpres : ∀ c ∈ calls, ∀ u u' r, Inv u → step u c = some (u', r) → Inv u')
    (henv : ∀ u v, Inv u → Env u v → Inv v)
    (hblock : ∃ c ∈ calls, ∀ u, Inv u → step u c = none)
    {w w' : World X} (hw : Inv w) (hreach : Relation.ReflTransGen Env w w') :
    Properties.blocked_retry_reverts step Env Inv calls hpres henv hblock (hw := hw) (hreach := hreach) := by
  unfold Properties.blocked_retry_reverts
  have hnone := recoverBundle_blocked hpres hblock (inv_along henv hw hreach)
  have hrev : Outcome.reverts ∈ outcomes step w' calls := by
    have h := recoverBundle_none_outcomes calls w' hnone
    unfold LoopCompletes at h
    exact not_not.mp h
  exact ⟨hrev, fun hacc => hacc.1 hrev, fun _ => claimRefund_eq_none hnone⟩

theorem blocked_leg_stays_revertable (step : World X → Call → Option (World X × Bool))
    (Env : World X → World X → Prop) (Inv : World X → Prop) (f b : UInt256) (calls : List Call)
    (hpres : ∀ c ∈ calls, ∀ u u' r, Inv u → step u c = some (u', r) → Inv u')
    (henv : ∀ u v, Inv u → Env u v → Inv v)
    (hblock : ∃ c ∈ calls, ∀ u, Inv u → step u c = none)
    {M : Manager} {w : World X} (hleg : M.legState f b = .Revertable) (hw : Inv w)
    {S : Manager × World X} (hrun : Relation.ReflTransGen (RetryStep step Env f b calls) (M, w) S) :
    Properties.blocked_leg_stays_revertable step Env Inv f b calls hpres henv hblock (hleg := hleg) (hw := hw)
      (hrun := hrun) := by
  unfold Properties.blocked_leg_stays_revertable
  have key : ∀ (N : Manager) (u : World X), Inv u → legClaimRefund step N f b u calls = none := by
    intro N u hu
    unfold legClaimRefund
    rw [claimRefund_eq_none (recoverBundle_blocked hpres hblock hu)]
    rfl
  have hinv : S.1.legState f b = .Revertable ∧ Inv S.2 := by
    induction hrun with
    | refl => exact ⟨hleg, hw⟩
    | tail _ hstep ih =>
      obtain ⟨h₁, h₂⟩ := ih
      cases hstep with
      | env he => exact ⟨h₁, henv _ _ h₂ he⟩
      | other _ hsame => exact ⟨hsame.trans h₁, h₂⟩
      | claim hc =>
        rw [key _ _ h₂] at hc
        cases hc
  exact ⟨hinv.1, hinv.2, key _ _ hinv.2⟩


/-! ## Limit 2, concretely -/

/-- Targets on a world whose `rest` counts: `3` reverts while the world is paused and recovers otherwise, `1`
recovers and bumps the counter, anything else declines. -/
def blockStep : World ℕ → Call → Option (World ℕ × Bool) := fun u c =>
  if c.target = 3 then (if u.paused = true then none else some (u, true))
  else if c.target = 1 then some ({ u with rest := u.rest + 1 }, true)
  else some (u, false)

/-- A recovering call, then the blocker. -/
def blockCalls : List Call := [⟨1, 0, 0, .other⟩, ⟨3, 0, 0, .other⟩]

/-- Fresh router and vault storage, paused, counter `0`. -/
def pausedWorld : World ℕ :=
  ⟨Contracts.AssetRouter.empty, Contracts.NativeTokenVault.empty.vault, true, 0⟩

lemma blockStep_pres : ∀ c ∈ blockCalls, ∀ u u' r, (fun v : World ℕ => v.paused = true) u →
    blockStep u c = some (u', r) → (fun v : World ℕ => v.paused = true) u' := by
  intro c _ u u' r hu hs
  unfold blockStep at hs
  by_cases h3 : c.target = 3
  · rw [ite_eq_left h3, ite_eq_left hu] at hs
    cases hs
  · rw [ite_eq_right h3] at hs
    by_cases h1 : c.target = 1
    · rw [ite_eq_left h1] at hs
      cases hs
      exact hu
    · rw [ite_eq_right h1] at hs
      cases hs
      exact hu

theorem retry_succeeds_once_blocker_clears : Properties.retry_succeeds_once_blocker_clears := by
  unfold Properties.retry_succeeds_once_blocker_clears
  have hnone : legClaimRefund blockStep revertableLeg 0 0 pausedWorld blockCalls = none := rfl
  exact ⟨ℕ, blockStep, blockCalls, revertableLeg, pausedWorld, revertableLeg_reach, by decide, hnone, rfl⟩

theorem blocked_retry_witness : Properties.blocked_retry_witness := by
  unfold Properties.blocked_retry_witness
  let Inv : World ℕ → Prop := fun v => v.paused = true
  let Env : World ℕ → World ℕ → Prop := fun u v => v.paused = u.paused
  let w₁ : World ℕ := { pausedWorld with rest := 5 }
  let M₁ : Manager := revertableLeg.set 0 1 .Committed
  have hother : Step revertableLeg M₁ := Step.append (by unfold AppendGuard; decide)
  have hsame : M₁.legState 0 0 = revertableLeg.legState 0 0 := by decide
  have hrun : Relation.ReflTransGen (RetryStep blockStep Env 0 0 blockCalls) (revertableLeg, pausedWorld)
      (M₁, w₁) :=
    Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single (RetryStep.env (show Env pausedWorld w₁ from rfl)))
      (RetryStep.other hother hsame)
  have hmem₃ : (⟨3, 0, 0, .other⟩ : Call) ∈ blockCalls := List.mem_cons_of_mem _ List.mem_cons_self
  have hmem₁ : (⟨1, 0, 0, .other⟩ : Call) ∈ blockCalls := List.mem_cons_self
  refine ⟨ℕ, blockStep, Env, Inv, blockCalls, pausedWorld, revertableLeg, (M₁, w₁), blockStep_pres,
    fun u v hu he => he.trans hu, ⟨⟨3, 0, 0, .other⟩, hmem₃, fun u hu => ?_⟩, rfl, revertableLeg_reach,
    by decide, hrun, Relation.ReflTransGen.single (show Env pausedWorld w₁ from rfl), ?_, ?_,
    ⟨⟨1, 0, 0, .other⟩, hmem₁, fun u _ => ⟨{ u with rest := u.rest + 1 }, rfl⟩⟩, by decide, rfl⟩
  · show (if (3 : UInt256) = 3 then (if u.paused = true then none else some (u, true))
      else if (3 : UInt256) = 1 then some ({ u with rest := u.rest + 1 }, true) else some (u, false)) = none
    rw [ite_eq_left rfl, ite_eq_left hu]
  · intro h
    have := congrArg World.rest h
    exact absurd this (by decide)
  · intro h
    have := congrArg (fun M : Manager => M.legState 0 1) h
    exact absurd this (by decide)


end Contracts.AtomicFlowManager.RecoveryLimitsStrong
