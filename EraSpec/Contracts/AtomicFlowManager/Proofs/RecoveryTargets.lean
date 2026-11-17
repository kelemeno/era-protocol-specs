import EraSpec.Contracts.AtomicFlowManager.Properties.RecoveryTargets
import EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery

/-!
# Proofs: what `_recoverBundle` finds at each call's `to`

Everything rests on one per-call case split (`recoverStep_cases`): under `VmCall`, a call returns
only if its target holds a recoverer, and then it is that recoverer. The loop results are
inductions over the call list: a returning loop is exactly a run of recoverers
(`recoverers_of_recoverBundle_some`, `recoverBundle_of_recoverers`), and a non-recoverer anywhere
makes the loop revert in every world (`recoverBundle_none_of_noRecoverer`). The router instance
reuses the B1 proofs (`PreparedBurnRefundsDepositor`, `recoverAtomicCall_known`) and B1's witness
data.
-/

namespace Contracts.AtomicFlowManager.RecoveryTargets

open Contracts.AtomicFlowManager (LegState)

variable {W D A C : Type}

/-! ## One call -/

theorem vmCall_holds (W D : Type) : VmCall (vmCall : CallSem W D) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem VmCallHolds : Properties.VmCallHolds := vmCall_holds

theorem recoverStep_noRecoverer {sem : CallSem W D} {code : A → Code W D} {target : C → A}
    {data : C → D} {dest : UInt256} {w : W} {c : C} (hvm : VmCall sem)
    (h : NoRecovererAt code (target c)) : recoverStep sem code target data dest w c = none := by
  unfold recoverStep
  rcases h with h | h <;> rw [h]
  · exact hvm.noCode _ _ _
  · exact hvm.noEntry _ _ _

theorem recoverStep_recoverer {sem : CallSem W D} {code : A → Code W D} {target : C → A}
    {data : C → D} {dest : UInt256} {w : W} {c : C} {f : W → UInt256 → D → Option (W × Bool)}
    (hvm : VmCall sem) (h : code (target c) = .recoverer f) :
    recoverStep sem code target data dest w c = f w dest (data c) := by
  unfold recoverStep
  rw [h, hvm.recoverer]

/-- **A call returns only from a recoverer.** -/
theorem recoverStep_cases {sem : CallSem W D} {code : A → Code W D} {target : C → A}
    {data : C → D} {dest : UInt256} {w : W} {c : C} {p : W × Bool} (hvm : VmCall sem)
    (h : recoverStep sem code target data dest w c = some p) :
    ∃ f, code (target c) = .recoverer f ∧ f w dest (data c) = some p := by
  unfold recoverStep at h
  cases hc : code (target c) with
  | none => rw [hc, hvm.noCode] at h; cases h
  | recoverer f => rw [hc, hvm.recoverer] at h; exact ⟨f, rfl, h⟩
  | other => rw [hc, hvm.noEntry] at h; cases h

/-! ## The loop -/

theorem count_true_cons (b : Bool) (bs : List Bool) :
    (b :: bs).count true = (if b then 1 else 0) + bs.count true := by
  cases b <;> simp [Nat.add_comm]

/-- **A run of recoverers is a returning loop.** -/
theorem recoverBundle_of_recoverers {sem : CallSem W D} {code : A → Code W D} {target : C → A}
    {data : C → D} {dest : UInt256} (hvm : VmCall sem) {w w' : W} {calls : List C}
    {bs : List Bool} (h : RecoverersReturn code target data dest w calls bs w') :
    recoverBundle (recoverStep sem code target data dest) w calls = some (w', bs.count true) := by
  induction h with
  | nil => rfl
  | cons f hcode hf _ ih =>
    unfold recoverBundle
    rw [recoverStep_recoverer hvm hcode, hf]
    dsimp only
    rw [ih, count_true_cons]

/-- **A returning loop is a run of recoverers.** -/
theorem recoverers_of_recoverBundle_some {sem : CallSem W D} {code : A → Code W D}
    {target : C → A} {data : C → D} {dest : UInt256} (hvm : VmCall sem) :
    ∀ (calls : List C) (w w' : W) (n : ℕ),
      recoverBundle (recoverStep sem code target data dest) w calls = some (w', n) →
        ∃ bs, RecoverersReturn code target data dest w calls bs w' ∧ bs.count true = n
  | [], w, w', n, h => by
    unfold recoverBundle at h
    cases h
    exact ⟨[], .nil, rfl⟩
  | c :: cs, w, w', n, h => by
    unfold recoverBundle at h
    rcases hs : recoverStep sem code target data dest w c with _ | ⟨w₁, b⟩ <;> rw [hs] at h
    · cases h
    dsimp only at h
    rcases hr : recoverBundle (recoverStep sem code target data dest) w₁ cs with _ | ⟨w₂, k⟩ <;>
      rw [hr] at h
    · cases h
    dsimp only at h
    obtain ⟨hw, hn⟩ := Prod.mk.inj (Option.some.inj h)
    subst hw hn
    obtain ⟨f, hcode, hf⟩ := recoverStep_cases hvm hs
    obtain ⟨bs, hbs, hk⟩ := recoverers_of_recoverBundle_some hvm cs w₁ w₂ k hr
    exact ⟨b :: bs, .cons f hcode hf hbs, by rw [count_true_cons, hk]⟩

/-- **A non-recoverer anywhere makes the loop revert, in every world.** -/
theorem recoverBundle_none_of_noRecoverer {sem : CallSem W D} {code : A → Code W D}
    {target : C → A} {data : C → D} {dest : UInt256} (hvm : VmCall sem) :
    ∀ (calls : List C) (w : W), (∃ c ∈ calls, NoRecovererAt code (target c)) →
      recoverBundle (recoverStep sem code target data dest) w calls = none
  | [], _, ⟨_, hc, _⟩ => absurd hc List.not_mem_nil
  | c :: cs, w, ⟨c', hc', hn⟩ => by
    unfold recoverBundle
    rcases List.mem_cons.mp hc' with rfl | hmem
    · rw [recoverStep_noRecoverer hvm hn]
    · rcases recoverStep sem code target data dest w c with _ | ⟨w₁, b⟩
      · rfl
      · dsimp only
        rw [recoverBundle_none_of_noRecoverer hvm cs w₁ ⟨c', hmem, hn⟩]

theorem claimRefund_none_of_loop {step : W → C → Option (W × Bool)} {s : LegState} {w : W}
    {calls : List C} (h : recoverBundle step w calls = none) :
    claimRefund step s w calls = none := by
  unfold claimRefund
  split_ifs
  · rfl
  · rw [h]

/-- A claim succeeds only on a `Revertable` leg. -/
theorem claimRefund_revertable {step : W → C → Option (W × Bool)} {s : LegState} {w : W}
    {calls : List C} {p : LegState × W} (h : claimRefund step s w calls = some p) :
    s = LegState.Revertable := by
  unfold claimRefund at h
  by_contra hs
  rw [ite_eq_left hs] at h
  cases h

/-- A successful claim ends in `Reverted`. -/
theorem claimRefund_reverted {step : W → C → Option (W × Bool)} {s s' : LegState} {w w' : W}
    {calls : List C} (h : claimRefund step s w calls = some (s', w')) : s' = LegState.Reverted := by
  unfold claimRefund at h
  split_ifs at h
  rcases hr : recoverBundle step w calls with _ | ⟨w₂, n⟩ <;> rw [hr] at h
  · cases h
  · dsimp only at h
    split_ifs at h
    exact (Prod.mk.inj (Option.some.inj h)).1.symm

/-! ## Characterization -/

theorem ClaimSucceedsIff : Properties.ClaimSucceedsIff := by
  intro W D A C sem code target data dest w w' calls hvm
  unfold claimRefund
  rw [ite_eq_right (by simp)]
  constructor
  · intro h
    rcases hr : recoverBundle (recoverStep sem code target data dest) w calls with _ | ⟨w₂, n⟩ <;>
      rw [hr] at h
    · cases h
    dsimp only at h
    by_cases hn : n = 0
    · rw [ite_eq_left hn] at h; cases h
    rw [ite_eq_right hn] at h
    have hw : w₂ = w' := (Prod.mk.inj (Option.some.inj h)).2
    subst hw
    obtain ⟨bs, hbs, hc⟩ := recoverers_of_recoverBundle_some hvm calls w w₂ n hr
    refine ⟨bs, hbs, ?_⟩
    rw [← List.count_pos_iff]
    omega
  · rintro ⟨bs, hbs, ht⟩
    rw [recoverBundle_of_recoverers hvm hbs]
    dsimp only
    have hpos := List.count_pos_iff.mpr ht
    rw [ite_eq_right (by omega)]

theorem RecoveryReadsOnlyTargetAndData : Properties.RecoveryReadsOnlyTargetAndData := by
  intro W D A C sem code target data dest w c c' ht hd
  unfold recoverStep
  rw [ht, hd]

/-! ## A target with no recoverer -/

theorem NonRecovererTargetBlocksClaim : Properties.NonRecovererTargetBlocksClaim := by
  intro W D A C sem code target data dest calls hvm hex s w
  exact claimRefund_none_of_loop (recoverBundle_none_of_noRecoverer hvm calls w hex)

/-! ## Any `true` counts -/

theorem recoverBundle_trueNoOps {sem : CallSem W D} {code : A → Code W D} {target : C → A}
    {data : C → D} {dest : UInt256} (hvm : VmCall sem) :
    ∀ (calls : List C) (w : W),
      (∀ c ∈ calls, ∃ f, code (target c) = .recoverer f ∧ ∀ u, f u dest (data c) = some (u, true)) →
      recoverBundle (recoverStep sem code target data dest) w calls = some (w, calls.length)
  | [], _, _ => rfl
  | c :: cs, w, h => by
    obtain ⟨f, hcode, hf⟩ := h c List.mem_cons_self
    unfold recoverBundle
    rw [recoverStep_recoverer hvm hcode, hf]
    dsimp only
    rw [recoverBundle_trueNoOps hvm cs w (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    simp only [ite_true, List.length_cons]
    congr 2
    omega

theorem ForeignTrueCountsAsRecovered : Properties.ForeignTrueCountsAsRecovered := by
  intro W D A C sem code target data dest w calls hvm hne h
  unfold claimRefund
  rw [ite_eq_right (by simp), recoverBundle_trueNoOps hvm calls w h]
  dsimp only
  rw [ite_eq_right (by simpa [List.length_eq_zero_iff] using hne)]

/-! ## The router instance -/

section RouterInstance

open Contracts.AssetRouter (AssetIdOf AssetId Address Chain)
open Contracts.AssetRouter.AtomicRecovery (Config Hooks World Call CallData MintData routerCall
  directCall AtomicBundleValid)

variable {X : Type}

theorem recoverCall_eq_recoverStep {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {other : Address → World X → Chain → CallData → Option (World X × Bool)} {dest : Chain}
    {sem : CallSem (World X) CallData} (hvm : VmCall sem) (w : World X) (c : Call) :
    Contracts.AssetRouter.AtomicRecovery.recoverCall enc cfg hk other dest w c
      = recoverStep sem (routerCodeMap enc cfg hk other) Call.target Call.data dest w c := by
  unfold Contracts.AssetRouter.AtomicRecovery.recoverCall recoverStep routerCodeMap
  by_cases h : c.target = cfg.router
  · rw [ite_eq_left h, ite_eq_left h, hvm.recoverer]
    rfl
  · rw [ite_eq_right h, ite_eq_right h, hvm.recoverer]

theorem b1_recoverBundle_eq (step : World X → Call → Option (World X × Bool)) :
    ∀ (w : World X) (calls : List Call),
      Contracts.AssetRouter.AtomicRecovery.recoverBundle step w calls = recoverBundle step w calls
  | _, [] => rfl
  | w, c :: cs => by
    unfold Contracts.AssetRouter.AtomicRecovery.recoverBundle recoverBundle
    rcases step w c with _ | ⟨w', b⟩
    · rfl
    · dsimp only
      rw [b1_recoverBundle_eq step w' cs]
      rcases recoverBundle step w' cs with _ | ⟨w'', n⟩ <;> rfl

theorem RouterModelIsACodeMap : Properties.RouterModelIsACodeMap := by
  intro X enc cfg hk other dest sem hvm
  exact ⟨recoverCall_eq_recoverStep hvm, fun step w calls => b1_recoverBundle_eq step w calls⟩

/-- The manager's call of a code map holding the router at the router's address is the router. -/
theorem recoverStep_routerCall {enc : AssetIdOf} {cfg : Config} {hk : Hooks X}
    {sem : CallSem (World X) CallData} {code : Address → Code (World X) CallData} {dest : Chain}
    (hvm : VmCall sem) (hcode : code cfg.router = .recoverer (routerRecoverer enc cfg hk))
    (w : World X) (a : AssetId) (md : MintData) :
    recoverStep sem code Call.target Call.data dest w (routerCall cfg a md)
      = Contracts.AssetRouter.AtomicRecovery.recoverCall enc cfg hk (fun _ _ _ _ => none) dest w
          (routerCall cfg a md) := by
  have ht : (routerCall cfg a md).target = cfg.router := rfl
  rw [recoverStep_recoverer hvm (by rw [ht]; exact hcode)]
  unfold Contracts.AssetRouter.AtomicRecovery.recoverCall
  rw [ite_eq_left ht]
  rfl

theorem SourceRouterTargetRefundsDepositor : Properties.SourceRouterTargetRefundsDepositor := by
  intro Acc prepHooks s r out hw hprep X enc cfg hk sem code dest w x₁ hvm hcode hp hn ht hf
  rw [recoverStep_routerCall hvm hcode]
  exact Contracts.AssetRouter.AtomicRecovery.PreparedBurnRefundsDepositor Acc prepHooks s r out hw
    hprep X enc cfg hk _ dest w x₁ hp hn ht hf

theorem SourceRouterTargetRefundsDepositorWitness :
    Properties.SourceRouterTargetRefundsDepositorWitness := by
  obtain ⟨Acc, prepHooks, s, r, out, X, enc, cfg, hk, other, dest, w, x₁, hw, hprep, hne, hp, hn,
    ht, hf, hout⟩ := Contracts.AssetRouter.AtomicRecovery.PreparedBurnRefundSatisfiable
  refine ⟨Acc, prepHooks, s, r, out, X, enc, cfg, hk, vmCall, routerCodeMap enc cfg hk other, dest,
    w, x₁, hw, hprep, hne, vmCall_holds _ _, by simp [routerCodeMap], hp, hn, ht, hf, ?_⟩
  rw [← recoverCall_eq_recoverStep (vmCall_holds _ _)]
  revert hout
  rcases Contracts.AssetRouter.AtomicRecovery.recoverCall enc cfg hk other dest w
    (routerCall cfg r.assetId out.data) with _ | ⟨w', _ | _⟩ <;>
    simp [Contracts.AssetRouter.AtomicRecovery.outcomeOf]

theorem DestinationOnlyTargetBlocksRefund : Properties.DestinationOnlyTargetBlocksRefund := by
  open Contracts.AssetRouter.AtomicRecovery in
  refine ⟨Unit, wEnc, wCfg, okHooks, declineOther, vmCall, 8, wWorld, 1, wMd, 55, 77, .other,
    vmCall_holds _ _, by decide, ?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> rfl
  · have hstep : recoverStep vmCall (routerAndAppCodeMap wEnc wCfg okHooks 55 declineOther)
        Call.target Call.data 8 wWorld (routerCall wCfg 1 wMd) = some ({ wWorld with rest := () }, true) := by
      have hcode : routerAndAppCodeMap wEnc wCfg okHooks 55 declineOther
          (routerCall wCfg 1 wMd).target = .recoverer (routerRecoverer wEnc wCfg okHooks) := by
        simp [routerAndAppCodeMap, routerCall]
      rw [recoverStep_recoverer (vmCall_holds _ _) hcode]
      show recoverAtomicCall wEnc wCfg okHooks wWorld wCfg.manager 8
        (.finalizeDeposit wCfg.thisChain 1 (some wMd)) = _
      rw [recoverAtomicCall_known rfl wVault_known_one.1 wVault_known_one.2 rfl]
      rfl
    unfold claimRefund recoverBundle
    rw [ite_eq_right (by simp), hstep]
    rfl
  · intro s w'
    refine NonRecovererTargetBlocksClaim _ _ _ _ vmCall _ Call.target Call.data 8 _
      (vmCall_holds _ _) ⟨directCall 55 77 .other, by simp, ?_⟩ s w'
    left
    simp [routerAndAppCodeMap, directCall, wCfg]

end RouterInstance

/-! ## The escrow witnesses -/

theorem escrowCode_two : escrowCode 2 = .recoverer trueNoOp := by
  simp [escrowCode]

theorem ForeignTrueStrandsEscrow : Properties.ForeignTrueStrandsEscrow := by
  refine ⟨vmCall, (2, 1, ()), vmCall_holds _ _, by decide,
    ⟨trueNoOp, escrowCode_two, fun _ => rfl⟩, ?_, ?_, ?_⟩
  · exact ForeignTrueCountsAsRecovered ℕ Unit ℕ TriCall vmCall escrowCode TriCall.target
      TriCall.data 0 5 [(2, 1, ())] (vmCall_holds _ _) (by simp)
      (fun c hc => by
        rw [List.mem_singleton] at hc
        subst hc
        exact ⟨trueNoOp, escrowCode_two, fun _ => rfl⟩)
  · intro w
    unfold claimRefund
    rw [ite_eq_left (by decide)]
  · simp [recoverStep, escrowCode, vmCall]

theorem ClaimSucceedsIffWitness : Properties.ClaimSucceedsIffWitness := by
  have h1 : escrowCode 1 = .recoverer (fun _ _ _ => some (0, true)) := by simp [escrowCode]
  have h3 : escrowCode 3 = .recoverer (fun w _ _ => some (w, false)) := by simp [escrowCode]
  have hrun : RecoverersReturn escrowCode TriCall.target TriCall.data 0 5
      [((1 : ℕ), (0 : ℕ), ()), ((3 : ℕ), (0 : ℕ), ())] [true, false] 0 :=
    .cons _ h1 rfl (.cons _ h3 rfl .nil)
  refine ⟨vmCall, [(1, 0, ()), (3, 0, ())], (3, 0, ()), 0, vmCall_holds _ _, rfl,
    ⟨[true, false], hrun, by simp, by simp⟩, ?_, ?_⟩
  · exact (ClaimSucceedsIff ℕ Unit ℕ TriCall vmCall escrowCode TriCall.target TriCall.data 0 5 0 _
      (vmCall_holds _ _)).mpr ⟨[true, false], hrun, by simp⟩
  · have hrun3 : RecoverersReturn escrowCode TriCall.target TriCall.data 0 5
        [((3 : ℕ), (0 : ℕ), ())] [false] 5 := .cons _ h3 rfl .nil
    unfold claimRefund
    rw [ite_eq_right (by simp), recoverBundle_of_recoverers (vmCall_holds _ _) hrun3]
    rfl

theorem RecoveryReadsOnlyTargetAndDataWitness :
    Properties.RecoveryReadsOnlyTargetAndDataWitness :=
  ⟨(2, 1, ()), (2, 7, ()), by decide, rfl, rfl⟩

theorem NonRecovererTargetBlocksClaimWitness : Properties.NonRecovererTargetBlocksClaimWitness := by
  have h1 : escrowCode 1 = .recoverer (fun _ _ _ => some (0, true)) := by simp [escrowCode]
  refine ⟨vmCall, [(1, 0, ()), (4, 0, ())], vmCall_holds _ _, rfl,
    ⟨(4, 0, ()), by simp, Or.inl (by simp [escrowCode, TriCall.target])⟩, (1, 0, ()), by simp, ?_⟩
  have hrun : RecoverersReturn escrowCode TriCall.target TriCall.data 0 5
      [((1 : ℕ), (0 : ℕ), ())] [true] 0 := .cons _ h1 rfl .nil
  rw [(ClaimSucceedsIff ℕ Unit ℕ TriCall vmCall escrowCode TriCall.target TriCall.data 0 5 0 _
      (vmCall_holds _ _)).mpr ⟨[true], hrun, by simp⟩]
  rfl

end Contracts.AtomicFlowManager.RecoveryTargets
