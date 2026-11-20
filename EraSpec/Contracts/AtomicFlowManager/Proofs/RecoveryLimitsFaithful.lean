import EraSpec.Contracts.AtomicFlowManager.Properties.RecoveryLimitsFaithful
import EraSpec.Contracts.InteropCenter.Proofs.Dispatch

/-!
# Proofs: the refund loop's external call at `draft/v0.35.0`

The `draft/v0.35.0` sufficiency result is one induction over the calls (`v35Loop_some`). The
witnesses compute on `Unit` and `ℕ` worlds and never evaluate a bundle hash. The pin's loop is
proved in `History/Proofs/RecoveryLimitsFaithful.lean`.
-/

namespace Contracts.AtomicFlowManager.RecoveryLimitsFaithful

open AttackVectors.RecoveryLimits (Outcome LoopCompletes ClaimAccepted recoveredCount)
open Contracts.InteropCenter (Address Word InteropCall Bundle CallStarter Dispatch FormsCall
  FormedBy)

variable {W : Type}

/-! ## One call -/

theorem CodelessCallReturnsNoData : Properties.CodelessCallReturnsNoData := by
  intro W S w a dest data h
  simp [SourceChain.call, h]

theorem abiBool_length (b : Bool) : (abiBool b).length = 32 := by
  cases b <;> rfl

theorem abiBool_true_ne_false : abiBool true ≠ abiBool false := by
  decide

theorem ShortReturnDataDoesNotDecode : Properties.ShortReturnDataDoesNotDecode := by
  intro rd h
  have ht : (rd.take 32).length < 32 := by
    rw [List.length_take]
    omega
  have h0 : rd.take 32 ≠ abiBool false := fun he => by
    rw [he, abiBool_length] at ht
    omega
  have h1 : rd.take 32 ≠ abiBool true := fun he => by
    rw [he, abiBool_length] at ht
    omega
  unfold decodeBool
  rw [ite_eq_right h0, ite_eq_right h1]

theorem AbiBoolDecodes : Properties.AbiBoolDecodes := by
  intro b rest
  have ht : (abiBool b ++ rest).take 32 = abiBool b := by
    rw [List.take_append_of_le_length (by rw [abiBool_length])]
    exact List.take_of_length_le (by rw [abiBool_length])
  unfold decodeBool
  rw [ht]
  cases b
  · rw [ite_eq_left rfl]
  · rw [ite_eq_right abiBool_true_ne_false, ite_eq_left rfl]

theorem decodeBool_abiBool (b : Bool) : decodeBool (abiBool b) = some b := by
  have h := AbiBoolDecodes b []
  rwa [List.append_nil] at h

theorem decodeBool_nil : decodeBool [] = none :=
  ShortReturnDataDoesNotDecode [] (by simp)

theorem DecodeBoolWitness : Properties.DecodeBoolWitness :=
  ⟨rfl, rfl, by decide, decodeBool_nil, by decide, AbiBoolDecodes true [7]⟩

/-- A call to an address that runs no code reverts once its `bool` is decoded. -/
theorem probeAt_codeless {S : SourceChain W} {dest : Word} {w : W} {a : Address}
    {data : List UInt8} (h : S.runsCode w a = false) : probeAt S dest w a data = none := by
  unfold probeAt
  rw [CodelessCallReturnsNoData W S w a dest data h]
  dsimp only
  rw [decodeBool_nil]
  rfl

/-! ## Witnesses -/

theorem mixD_calls : mixD.bundle.calls = [wRouterCall, wDirectCall] := rfl

/-! ## The loop at `draft/v0.35.0` -/

/-- The `draft/v0.35.0` step reads the source chain only at the router. -/
theorem v35Step_congr {S S' : SourceChain W} {router : Address}
    {baseRecover : W → Word → Word → Address → ℕ → Option W} {dest baseAsset : Word}
    (hr : ∀ w, S.runsCode w router = S'.runsCode w router)
    (he : ∀ w dest data, S.exec w router dest data = S'.exec w router dest data) :
    v35Step S router baseRecover dest baseAsset
      = v35Step S' router baseRecover dest baseAsset := by
  funext w c
  have hp : ∀ a, a = router → probeAt S dest w a c.data = probeAt S' dest w a c.data := by
    rintro a rfl
    unfold probeAt SourceChain.call
    rw [hr w, he w dest c.data]
  unfold v35Step
  by_cases hc : c.fromAddr = router
  · rw [ite_eq_left hc, ite_eq_left hc, hp _ hc]
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem V35ClaimReadsOnlyRouterCode : Properties.V35ClaimReadsOnlyRouterCode := by
  intro W S S' router l1 baseRecover s w b hr he
  unfold claimRefundV35
  rw [v35Step_congr hr he]

theorem V35SkipsZeroValueNonRouterCalls : Properties.V35SkipsZeroValueNonRouterCalls := by
  intro W S router baseRecover dest baseAsset w c hfrom hval
  unfold v35Step
  rw [ite_eq_right hfrom]
  dsimp only
  rw [ite_eq_right (fun h => h.2 hval)]

theorem V35ClaimRejectsL1Destination : Properties.V35ClaimRejectsL1Destination := by
  intro W S router l1 baseRecover s w b h
  unfold claimRefundV35
  by_cases hs : s ≠ .Revertable
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs, ite_eq_left h]

/-- With conforming code at the router and a base-token refund that never reverts, every step of
the `draft/v0.35.0` loop returns. -/
theorem v35Step_some {S : SourceChain W} {router : Address}
    {baseRecover : W → Word → Word → Address → ℕ → Option W} {dest baseAsset : Word}
    (hconf : Conforms S router)
    (hbase : ∀ w dest asset receiver amount, (baseRecover w dest asset receiver amount).isSome = true)
    (w : W) (c : InteropCall) : ∃ w', v35Step S router baseRecover dest baseAsset w c = some w' := by
  unfold v35Step
  by_cases hc : c.fromAddr = router
  · obtain ⟨hr, b, w₁, he⟩ := hconf w dest c.data
    have hp : (probeAt S dest w c.fromAddr c.data).map Prod.fst = some w₁ := by
      rw [hc]
      unfold probeAt SourceChain.call
      rw [ite_eq_left hr, he]
      dsimp only
      rw [decodeBool_abiBool]
      rfl
    rw [ite_eq_left hc, hp]
    refine ⟨w₁, ?_⟩
    dsimp only
    rw [ite_eq_right (fun h => h.1 hc)]
  · rw [ite_eq_right hc]
    dsimp only
    by_cases hv : c.value = 0
    · exact ⟨w, by rw [ite_eq_right (fun h => h.2 hv)]⟩
    · rw [ite_eq_left ⟨hc, hv⟩]
      exact Option.isSome_iff_exists.mp (hbase w dest baseAsset c.fromAddr c.value)

/-- A loop whose every step returns, returns. -/
theorem v35Loop_some {step : W → InteropCall → Option W} (h : ∀ w c, ∃ w', step w c = some w') :
    ∀ (cs : List InteropCall) (w : W), ∃ w', v35Loop step w cs = some w'
  | [], w => ⟨w, rfl⟩
  | c :: cs, w => by
    obtain ⟨w₁, h₁⟩ := h w c
    obtain ⟨w₂, h₂⟩ := v35Loop_some h cs w₁
    refine ⟨w₂, ?_⟩
    unfold v35Loop
    rw [h₁]
    exact h₂

theorem V35ClaimSucceedsWithConformingRouter :
    Properties.V35ClaimSucceedsWithConformingRouter := by
  intro W S router l1 baseRecover w b hdest hconf hbase
  obtain ⟨w', hw'⟩ := v35Loop_some (v35Step_some (dest := b.destinationChainId)
    (baseAsset := b.destinationBaseTokenAssetId) hconf hbase) b.calls w
  refine ⟨w', ?_⟩
  unfold claimRefundV35
  rw [ite_eq_right (by simp), ite_eq_right hdest, hw']
  rfl

theorem V35ClaimWitness : Properties.V35ClaimWitness := by
  refine ⟨by decide, fun w _ _ => ⟨rfl, _, w, rfl⟩, fun _ _ _ _ _ => rfl, by decide, by decide, rfl,
    ?_, ?_⟩
  · exact V35SkipsZeroValueNonRouterCalls ℕ (wSourceOver ℕ) 9 wBaseRecover 325 1 4 wDirectCall
      (by decide) rfl
  · exact V35ClaimRejectsL1Destination ℕ (wSourceOver ℕ) 9 wL1 wBaseRecover .Revertable 0 _ rfl

theorem V35ClaimSucceedsOnMixedBundle : Properties.V35ClaimSucceedsOnMixedBundle := by
  intro baseRecover
  have hrouter : v35Step wSource 9 baseRecover 325 1 () wRouterCall = some () := by
    unfold v35Step
    rw [ite_eq_left (show wRouterCall.fromAddr = 9 from rfl)]
    have hp : (probeAt wSource 325 () wRouterCall.fromAddr wRouterCall.data).map Prod.fst
        = some () := by
      decide
    rw [hp]
    dsimp only
    rw [ite_eq_right (fun h => h.1 rfl)]
  have hdirect : v35Step wSource 9 baseRecover 325 1 () wDirectCall = some () :=
    V35SkipsZeroValueNonRouterCalls Unit wSource 9 baseRecover 325 1 () wDirectCall
      (by decide) rfl
  unfold claimRefundV35
  rw [ite_eq_right (by simp), ite_eq_right (by decide), mixD_calls]
  show (v35Loop (v35Step wSource 9 baseRecover 325 1) () [wRouterCall, wDirectCall]).map _ = _
  unfold v35Loop
  rw [hrouter]
  dsimp only
  unfold v35Loop
  rw [hdirect]
  dsimp only
  unfold v35Loop
  rfl

end Contracts.AtomicFlowManager.RecoveryLimitsFaithful
