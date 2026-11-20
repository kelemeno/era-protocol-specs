import EraSpec.Contracts.AtomicFlowManager.History.Properties.RecoveryLimitsFaithful
import EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimitsFaithful

/-!
# Proofs (History): the pinned refund loop over each call's `to`

Proofs of `EraSpec.Contracts.AtomicFlowManager.History.Properties.RecoveryLimitsFaithful`. The loop
lemmas mirror `Contracts.AssetRouter.AtomicRecovery`'s, for this file's call type. One induction
(`recoverLoop_blocked`) gives Limit 2 on the threaded world. The witnesses reuse
`Contracts.InteropCenter`'s step lemmas.

**History.** This is the record of the refund loop at era-contracts `c67894b9`
(`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`), not a claim about `draft/v0.35.0` `b17415d20`. At the
pin, `_recoverBundle` (`atomic-interop/AtomicFlowManager.sol:219-230`) called
`IAtomicRecoverable(c.to).recoverAtomicCall(destChainId, c.data)` on every call, counted the calls
that answered `true`, and reverted when none did (`:229`); `claimRefund` (`:165-180`) gated on
`Revertable` (`:169-170`) and wrote `Reverted` first (`:175`). At `b17415d20` the loop calls only
the asset router and counts nothing: that loop is `claimRefundV35` in
`Specs/RecoveryLimitsFaithful.lean`. Line numbers here are at the pin. `c.to` is what the pin's
`_processCallStarter` (`interop/InteropCenter.sol:701-751`) wrote into the bundle: for a direct
call the starter's recipient (`:745`), for an indirect call the address the indirect sender
returned (`:736`). The bundles are `Contracts.InteropCenter`'s, at the pin (`MODEL-CENTER`).
-/

namespace Contracts.AtomicFlowManager.RecoveryLimitsFaithful.History

open AttackVectors.RecoveryLimits (Outcome LoopCompletes ClaimAccepted recoveredCount)
open Contracts.InteropCenter (Address Word InteropCall Bundle CallStarter Dispatch FormsCall
  FormedBy)

variable {W : Type}

theorem CodelessTargetReverts : Properties.CodelessTargetReverts := by
  intro W S dest w c cs h
  have hp : pinnedProbe S dest w c = none := probeAt_codeless h
  refine ⟨hp, ?_⟩
  unfold outcomes
  rw [hp]

theorem PinnedCallRevertsIff : Properties.PinnedCallRevertsIff := by
  intro W S dest w c
  unfold pinnedProbe
  by_cases hr : S.runsCode w c.target = true
  · have hf : ¬ S.runsCode w c.target = false := by simp [hr]
    unfold probeAt SourceChain.call
    rw [ite_eq_left hr]
    rcases he : S.exec w c.target dest c.data with _ | ⟨rd, w'⟩
    · dsimp only
      refine ⟨fun _ => Or.inr fun rd w' h => ?_, fun _ => rfl⟩
      cases h
    · dsimp only
      constructor
      · intro hm
        refine Or.inr fun rd' w'' h => ?_
        cases h
        cases hd : decodeBool rd with
        | none => rfl
        | some b => rw [hd] at hm; cases hm
      · rintro (h | h)
        · exact absurd h hf
        · rw [h rd w' rfl]
          rfl
  · have hf : S.runsCode w c.target = false := by simpa using hr
    rw [probeAt_codeless hf]
    exact ⟨fun _ => Or.inl hf, fun _ => rfl⟩

/-! ## The loop is `RecoveryLimits`' acceptance rule -/

theorem recoverLoop_some_outcomes {step : W → InteropCall → Option (W × Bool)} :
    ∀ (calls : List InteropCall) (w w' : W) (n : ℕ), recoverLoop step w calls = some (w', n) →
      LoopCompletes (outcomes step w calls) ∧ recoveredCount (outcomes step w calls) = n
  | [], w, w', n, h => by
    unfold recoverLoop at h
    cases h
    exact ⟨List.not_mem_nil, rfl⟩
  | c :: cs, w, w', n, h => by
    unfold recoverLoop at h
    rcases hs : step w c with _ | ⟨w₁, b⟩ <;> rw [hs] at h
    · cases h
    dsimp only at h
    rcases hr : recoverLoop step w₁ cs with _ | ⟨w₂, k⟩ <;> rw [hr] at h
    · cases h
    dsimp only at h
    have hn : (if b then 1 else 0) + k = n := (Prod.mk.inj (Option.some.inj h)).2
    subst hn
    obtain ⟨hl, hk⟩ := recoverLoop_some_outcomes cs w₁ w₂ k hr
    unfold outcomes
    rw [hs]
    dsimp only
    refine ⟨?_, ?_⟩
    · intro hm
      rcases List.mem_cons.mp hm with he | hm
      · cases b <;> simp at he
      · exact hl hm
    · cases b <;> simp [recoveredCount] at hk ⊢ <;> omega

theorem recoverLoop_none_outcomes {step : W → InteropCall → Option (W × Bool)} :
    ∀ (calls : List InteropCall) (w : W), recoverLoop step w calls = none →
      ¬ LoopCompletes (outcomes step w calls)
  | [], w, h => by unfold recoverLoop at h; cases h
  | c :: cs, w, h => by
    unfold recoverLoop at h
    unfold outcomes
    rcases hs : step w c with _ | ⟨w₁, b⟩ <;> rw [hs] at h
    · dsimp only
      exact fun hl => hl List.mem_cons_self
    dsimp only at h ⊢
    rcases hr : recoverLoop step w₁ cs with _ | ⟨w₂, k⟩ <;> rw [hr] at h
    · intro hl
      exact recoverLoop_none_outcomes cs w₁ hr (fun hm => hl (List.mem_cons_of_mem _ hm))
    · cases h

theorem PinnedClaimSucceedsIffAccepted : Properties.PinnedClaimSucceedsIffAccepted := by
  intro W S w b
  unfold claimRefundPinned
  rw [ite_eq_right (by simp)]
  rcases hr : recoverLoop (pinnedProbe S b.destinationChainId) w b.calls with _ | ⟨w', n⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun hacc => recoverLoop_none_outcomes b.calls w hr hacc.1
  · obtain ⟨hl, hc⟩ := recoverLoop_some_outcomes b.calls w w' n hr
    dsimp only
    constructor
    · intro hs
      refine ⟨hl, ?_⟩
      rw [hc]
      intro h0
      rw [ite_eq_left h0] at hs
      cases hs
    · rintro ⟨-, hn⟩
      rw [hc] at hn
      rw [ite_eq_right hn]
      rfl

/-- A successful pinned claim found the leg `Revertable` and returns `Reverted`. -/
theorem claimRefundPinned_some {S : SourceChain W} {s : LegState} {w : W} {b : Bundle}
    {r : LegState × W} (h : claimRefundPinned S s w b = some r) :
    s = .Revertable ∧ r.1 = .Reverted := by
  unfold claimRefundPinned at h
  by_cases hs : s ≠ .Revertable
  · rw [ite_eq_left hs] at h
    cases h
  rw [ite_eq_right hs] at h
  refine ⟨not_not.mp hs, ?_⟩
  rcases hl : recoverLoop (pinnedProbe S b.destinationChainId) w b.calls with _ | ⟨w', n⟩ <;>
    rw [hl] at h
  · cases h
  · dsimp only at h
    by_cases hn : n = 0
    · rw [ite_eq_left hn] at h
      cases h
    · rw [ite_eq_right hn] at h
      cases h
      rfl

theorem PinnedClaimIsAManagerClaimStep : Properties.PinnedClaimIsAManagerClaimStep := by
  intro W S M f h w b r hr
  obtain ⟨hs, h1⟩ := claimRefundPinned_some hr
  refine ⟨hs, h1, ?_⟩
  rw [h1]
  exact Contracts.AtomicFlowManager.Step.claim hs

/-- **The loop through a blocking call reverts.** If the call `c` reverts in every world the
calls before it can leave, the loop over `pre ++ c :: post` reverts. -/
theorem recoverLoop_blocked {step : W → InteropCall → Option (W × Bool)} {c : InteropCall}
    {post : List InteropCall} :
    ∀ (pre : List InteropCall) (w : W),
      (∀ w' n, recoverLoop step w pre = some (w', n) → step w' c = none) →
      recoverLoop step w (pre ++ c :: post) = none
  | [], w, h => by
    have hc : step w c = none := h w 0 (by unfold recoverLoop; rfl)
    rw [List.nil_append]
    unfold recoverLoop
    rw [hc]
  | p :: ps, w, h => by
    rw [List.cons_append]
    unfold recoverLoop
    rcases hs : step w p with _ | ⟨w₁, b₁⟩
    · rfl
    · dsimp only
      have hrest : recoverLoop step w₁ (ps ++ c :: post) = none := by
        refine recoverLoop_blocked ps w₁ ?_
        intro w' n hr
        refine h w' ((if b₁ then 1 else 0) + n) ?_
        unfold recoverLoop
        rw [hs]
        dsimp only
        rw [hr]
      rw [hrest]

theorem claimRefundPinned_of_loop_none {S : SourceChain W} {s : LegState} {w : W} {b : Bundle}
    (h : recoverLoop (pinnedProbe S b.destinationChainId) w b.calls = none) :
    claimRefundPinned S s w b = none := by
  unfold claimRefundPinned
  split_ifs
  · rfl
  · rw [h]

theorem PinnedRevertAnywhereBlocks : Properties.PinnedRevertAnywhereBlocks := by
  intro W S s w b pre post c hb h
  apply claimRefundPinned_of_loop_none
  rw [hb]
  exact recoverLoop_blocked pre w h

/-! ## A target that runs no code -/

theorem CodelessTargetBlocksClaim : Properties.CodelessTargetBlocksClaim := by
  intro W S s w b pre post c hb h
  exact PinnedRevertAnywhereBlocks W S s w b pre post c hb
    (fun w' n hr => probeAt_codeless (h w' n hr))

theorem NonAnsweringTargetBlocksEveryClaim : Properties.NonAnsweringTargetBlocksEveryClaim := by
  intro W S b c hc hnone s w
  obtain ⟨pre, post, hb⟩ := List.append_of_mem hc
  exact PinnedRevertAnywhereBlocks W S s w b pre post c hb (fun w' _ _ => hnone w')

theorem CodelessTargetBlocksEveryClaim : Properties.CodelessTargetBlocksEveryClaim := by
  intro W S b c hc hnever
  exact NonAnsweringTargetBlocksEveryClaim W S b c hc (fun w => probeAt_codeless (hnever w))

/-- A member of the left list of a `Forall₂` has a related member of the right list. -/
theorem forall₂_exists_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a : α}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hab hrest, _, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, hr⟩ := forall₂_exists_right hrest h'
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem DirectCallWithoutSourceCodeBlocksClaim :
    Properties.DirectCallWithoutSourceCodeBlocksClaim := by
  intro P d cs W S hd hcs hdirect hnever s w
  obtain ⟨c, hc, hf⟩ := forall₂_exists_right hd.calls hcs
  have ht : c.target = cs.target := (hf.direct hdirect).1
  exact CodelessTargetBlocksEveryClaim W S d.bundle c hc (by rw [ht]; exact hnever) s w

/-! ## What a successful claim needs, and what suffices -/

/-- Every call of a loop that completed answered in some world. -/
theorem recoverLoop_some_each {step : W → InteropCall → Option (W × Bool)} :
    ∀ (calls : List InteropCall) (w : W) (r : W × ℕ), recoverLoop step w calls = some r →
      ∀ c ∈ calls, ∃ w₀ x, step w₀ c = some x
  | [], _, _, _, _, hc => absurd hc List.not_mem_nil
  | c' :: cs, w, r, h, c, hc => by
    unfold recoverLoop at h
    rcases hs : step w c' with _ | ⟨w₁, b⟩ <;> rw [hs] at h
    · cases h
    dsimp only at h
    rcases hr : recoverLoop step w₁ cs with _ | ⟨w₂, k⟩ <;> rw [hr] at h
    · cases h
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨w, _, hs⟩
    · exact recoverLoop_some_each cs w₁ (w₂, k) hr c hc'

/-- A call that answered ran code, and its code returned a decodable `bool`. -/
theorem probe_some_runs {S : SourceChain W} {dest : Word} {w : W} {c : InteropCall}
    {x : W × Bool} (h : pinnedProbe S dest w c = some x) :
    S.runsCode w c.target = true ∧
      ∃ rd w'', S.exec w c.target dest c.data = .returned rd w'' ∧ decodeBool rd ≠ none := by
  unfold pinnedProbe at h
  by_cases hr : S.runsCode w c.target = true
  · refine ⟨hr, ?_⟩
    unfold probeAt SourceChain.call at h
    rw [ite_eq_left hr] at h
    rcases he : S.exec w c.target dest c.data with _ | ⟨rd, w''⟩ <;> rw [he] at h
    · cases h
    · refine ⟨rd, w'', rfl, ?_⟩
      intro hd
      dsimp only at h
      rw [hd] at h
      cases h
  · have hf : S.runsCode w c.target = false := by simpa using hr
    rw [probeAt_codeless hf] at h
    cases h

theorem ClaimSuccessNeedsCodeAtEveryTarget : Properties.ClaimSuccessNeedsCodeAtEveryTarget := by
  intro W S s w b r h c hc
  unfold claimRefundPinned at h
  by_cases hs : s ≠ .Revertable
  · rw [ite_eq_left hs] at h
    cases h
  rw [ite_eq_right hs] at h
  rcases hl : recoverLoop (pinnedProbe S b.destinationChainId) w b.calls with _ | ⟨w', n⟩ <;>
    rw [hl] at h
  · cases h
  obtain ⟨w₀, x, hx⟩ := recoverLoop_some_each b.calls w (w', n) hl c hc
  obtain ⟨hrun, rd, w'', he, hd⟩ := probe_some_runs hx
  exact ⟨w₀, hrun, rd, w'', he, hd⟩

/-- A conforming target answers its decoded `bool`. -/
theorem probe_conforms {S : SourceChain W} {dest : Word} {w : W} {c : InteropCall}
    (h : Conforms S c.target) :
    ∃ b w', pinnedProbe S dest w c = some (w', b) ∧
      S.exec w c.target dest c.data = .returned (abiBool b) w' := by
  obtain ⟨hr, b, w', he⟩ := h w dest c.data
  refine ⟨b, w', ?_, he⟩
  unfold pinnedProbe probeAt SourceChain.call
  rw [ite_eq_left hr, he]
  dsimp only
  rw [decodeBool_abiBool]
  rfl

/-- Over conforming targets the loop completes, and it counts a recovery for a call whose target
always recovers it. -/
theorem recoverLoop_conforming {S : SourceChain W} {dest : Word} {c : InteropCall} :
    ∀ (calls : List InteropCall) (w : W), (∀ c' ∈ calls, Conforms S c'.target) →
      ∃ w' n, recoverLoop (pinnedProbe S dest) w calls = some (w', n) ∧
        (c ∈ calls → AlwaysRecovers S c.target dest c.data → n ≠ 0)
  | [], w, _ => ⟨w, 0, by unfold recoverLoop; rfl, fun h => absurd h List.not_mem_nil⟩
  | c' :: cs, w, hconf => by
    obtain ⟨b, w₁, hp, he⟩ :=
      probe_conforms (dest := dest) (w := w) (hconf c' List.mem_cons_self)
    obtain ⟨w', m, hl, hm⟩ :=
      recoverLoop_conforming cs w₁ (fun c'' hc'' => hconf c'' (List.mem_cons_of_mem _ hc''))
    refine ⟨w', (if b then 1 else 0) + m, ?_, ?_⟩
    · unfold recoverLoop
      rw [hp]
      dsimp only
      rw [hl]
    · intro hc hrec
      rcases List.mem_cons.mp hc with hcc | hc'
      · subst hcc
        obtain ⟨w₂, he₂⟩ := hrec w
        rw [he] at he₂
        have hb : abiBool b = abiBool true := (CallResult.returned.inj he₂).1
        cases b
        · exact absurd hb.symm abiBool_true_ne_false
        · simp
      · have := hm hc' hrec
        omega

theorem ConformingTargetsRefund : Properties.ConformingTargetsRefund := by
  intro W S w b c hconf hc hrec
  obtain ⟨w', n, hl, hn⟩ :=
    recoverLoop_conforming (S := S) (dest := b.destinationChainId) (c := c) b.calls w hconf
  refine ⟨w', ?_⟩
  unfold claimRefundPinned
  rw [ite_eq_right (by simp), hl]
  dsimp only
  rw [ite_eq_right (hn hc hrec)]

theorem mixD_dest : mixD.bundle.destinationChainId = 325 := rfl

theorem wRouterCall_mem : wRouterCall ∈ mixD.bundle.calls := by
  rw [mixD_calls]
  exact List.mem_cons_self

theorem wDirectCall_mem : wDirectCall ∈ mixD.bundle.calls := by
  rw [mixD_calls]
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem never_wSource_direct : NeverRunsCode wSource 5 := by
  intro w
  rfl

theorem CodelessTargetBlocksClaimWitness : Properties.CodelessTargetBlocksClaimWitness :=
  ⟨rfl, by decide, fun _ _ _ => rfl, by decide⟩

theorem NonAnsweringTargetWitness : Properties.NonAnsweringTargetWitness := by
  have hnone : ∀ w, pinnedProbe wSourceNoHook mixD.bundle.destinationChainId w wDirectCall = none :=
    fun w => by cases w; decide
  exact ⟨rfl, wDirectCall_mem, hnone,
    NonAnsweringTargetBlocksEveryClaim Unit wSourceNoHook mixD.bundle wDirectCall wDirectCall_mem
      hnone⟩

theorem conforms_wSourceConforming (a : Address) (ha : a = 9 ∨ a = 5) :
    Conforms wSourceConforming a := by
  intro w dest data
  refine ⟨?_, _, w, rfl⟩
  rcases ha with rfl | rfl <;> rfl

theorem ConformingTargetsRefundSatisfiable : Properties.ConformingTargetsRefundSatisfiable := by
  refine ⟨?_, wRouterCall_mem, ?_, ?_, ?_⟩
  · intro c' hc'
    rw [mixD_calls] at hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl
    · exact conforms_wSourceConforming 9 (Or.inl rfl)
    · exact conforms_wSourceConforming 5 (Or.inr rfl)
  · intro w
    exact ⟨w, rfl⟩
  · decide
  · decide

theorem mixD_formed : FormedBy Contracts.InteropCenter.wParams mixD :=
  ⟨rfl, rfl, List.Forall₂.cons
    (⟨rfl, fun _ => rfl, fun h => absurd h (by decide)⟩ :
      FormsCall 1 Contracts.InteropCenter.wIndirect wRouterCall)
    (List.Forall₂.cons (Contracts.InteropCenter.formsCall_direct 1 0) List.Forall₂.nil)⟩

theorem mixD_validated : Contracts.InteropCenter.Validated mixD.bundle := by
  intro c hc
  rw [mixD_calls] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> rfl

theorem mixStep1 :
    Contracts.InteropCenter.Step Contracts.InteropCenter.deployed Contracts.InteropCenter.wParams
      Contracts.InteropCenter.init mixS1 :=
  Contracts.InteropCenter.Step.send mixD (fun _ => rfl) mixD_formed
    (fun _ _ => mixD_validated) (fun _ => rfl)

theorem mixS1_leg :
    mixS1.manager.legState 7
      (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams mixD.bundle)
      = .Committed := by
  rw [mixS1, Contracts.InteropCenter.afterSend_legState, ite_eq_left ⟨rfl, rfl, rfl⟩]

theorem mixStep2 :
    Contracts.InteropCenter.Step Contracts.InteropCenter.deployed Contracts.InteropCenter.wParams
      mixS1 mixS2 :=
  Contracts.InteropCenter.Step.authorize 7
    (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams mixD.bundle) mixS1_leg

theorem mixS2_leg :
    mixS2.manager.legState 7
      (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams mixD.bundle)
      = .Revertable := by
  show (mixS1.manager.set 7
      (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams mixD.bundle)
        .Revertable).legState 7
      (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams mixD.bundle)
      = .Revertable
  rw [Contracts.InteropCenter.legState_set, ite_eq_left ⟨rfl, rfl⟩]

theorem mixS2_reach :
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed Contracts.InteropCenter.wParams
      Contracts.InteropCenter.init mixS2 :=
  .tail (.tail .refl mixStep1) mixStep2

theorem DirectCallWithoutSourceCodeBlocksClaimWitness :
    Properties.DirectCallWithoutSourceCodeBlocksClaimWitness :=
  ⟨mixS2_reach, mixS2_leg, mixD_formed, List.mem_cons_of_mem _ List.mem_cons_self, rfl,
    mixD_validated, never_wSource_direct, wDirectCall_mem, rfl, rfl, by decide,
    CodelessTargetBlocksEveryClaim Unit wSource mixD.bundle wDirectCall wDirectCall_mem
      never_wSource_direct⟩

theorem PinnedClaimStepWitness : Properties.PinnedClaimStepWitness := by
  have hc : claimRefundPinned wSourceConforming
      (mixS2.manager.legState 7
        (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams mixD.bundle))
      () mixD.bundle = some (.Reverted, ()) := by
    rw [mixS2_leg]
    exact ConformingTargetsRefundSatisfiable.2.2.2.2
  exact ⟨hc, .tail mixS2_reach (Contracts.InteropCenter.Step.claim 7
    (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams mixD.bundle) mixS2_leg)⟩

theorem DirectTargetCodeDecidesOnlyThePinnedClaim :
    Properties.DirectTargetCodeDecidesOnlyThePinnedClaim := by
  have hpin : claimRefundPinned wSource .Revertable () mixD.bundle = none :=
    CodelessTargetBlocksEveryClaim Unit wSource mixD.bundle wDirectCall wDirectCall_mem
      never_wSource_direct _ _
  have hconf : claimRefundPinned wSourceConforming .Revertable () mixD.bundle
      = some (.Reverted, ()) := ConformingTargetsRefundSatisfiable.2.2.2.2
  refine ⟨fun _ => rfl, fun _ _ _ => rfl, by decide, ?_, fun baseRecover => ?_⟩
  · rw [hpin, hconf]
    exact (Option.some_ne_none _).symm
  · exact V35ClaimReadsOnlyRouterCode Unit wSource wSourceConforming 9 wL1 baseRecover
      .Revertable () mixD.bundle (fun _ => rfl) (fun _ _ _ => rfl)

end Contracts.AtomicFlowManager.RecoveryLimitsFaithful.History
