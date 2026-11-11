import EraSpec.Contracts.ChainTypeManager.Properties.ExecutorEngineAtV35
import EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorForward
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsUnvalidated

/-!
# Proofs: `applyInfrastructureUpgrade` at `draft/v0.35.0`, with an arbitrary engine

A leg whose engine meets `EngineReviewed` is three `ExecutorForward` transactions: a `forward`
of the `_beforeSwaps` calls, the `e561b9cc2` infrastructure step, and a `forward` of the
`_afterSwaps` calls (`reviewed_leg`). The hook calls are tame CTM calls, so a `d9f6789` run of
tame transactions with reviewed engines maps to a tame `ExecutorForward` run (`reviewed_run`),
and `TameRunPreservesSysInv` and `TameRunKeepsChainsOnTheirRelease` transfer. Hook runs move no
proxy (`hookRun_impl`), so the row library's `OnlyNamedEdgesAcrossCallAnyRows` and
`applyLoop_source` give the proxy results. The countermodels are concrete legs; that their
engines are not reviewed follows from the positive results.
-/

namespace Contracts.ChainTypeManager.ExecutorEngineAtV35

/-! ## Hooks -/

lemma reviewedHookCall_tame {c : FCall} (h : ReviewedHookCall c) : c.Tame := by
  cases c with
  | sys l => exact h
  | upgradeProxy _ _ => exact h.elim
  | swapCtm _ _ => exact h.elim

lemma frun_hook_impl {X : XConfig} {x x' : XState} {cs : List FCall} (h : FRun X x cs x') :
    (∀ c ∈ cs, ReviewedHookCall c) → x'.impl = x.impl := by
  induction h with
  | nil => intro _; rfl
  | cons hstep _ ih =>
      intro hc
      have h1 := hc _ List.mem_cons_self
      rw [ih (fun c hc' => hc c (List.mem_cons_of_mem _ hc'))]
      cases hstep with
      | sys _ => rfl
      | upgradeProxy _ _ _ => exact h1.elim
      | swapCtm _ _ => exact h1.elim

/-- A hook run moves no proxy. -/
lemma hookRun_impl {X : XConfig} {x x' : XState} (h : HookRun X x x') : x'.impl = x.impl := by
  obtain ⟨cs, hc, hr⟩ := h
  exact frun_hook_impl hr hc

/-! ## The core -/

lemma engineCore_xstep {X : XConfig} {T : V35Transition} {x x' : XState}
    (h : EngineCore X T x x') (hcode : X.rc.hasCode T.addr) (hd : T.domain = .ctm) :
    XStep X x (.infra T.toCurrent) x' ∧ X.rc.adminOwner = X.rc.self := by
  cases h with
  | mk ho happ hc => exact ⟨XStep.infra ⟨hcode, hd, happ⟩ hc, ho⟩

lemma xstep_engineCore {X : XConfig} {T : V35Transition} {x x' : XState}
    (h : XStep X x (.infra T.toCurrent) x') (ho : X.rc.adminOwner = X.rc.self) :
    EngineCore X T x x' ∧ X.rc.hasCode T.addr ∧ T.domain = .ctm := by
  cases h with
  | infra happ hc => exact ⟨EngineCore.mk ho happ.2.2 hc, happ.1, happ.2.1⟩

lemma engineCore_rows {X : XConfig} {T : V35Transition} {x x' : XState}
    (h : EngineCore X T x x') : ProxyUpgradeCurrent.RowsApplied x'.impl T.rows := by
  cases h with
  | mk _ happ _ => exact happ.verified

/-! ## Steps -/

lemma infra_inv {X : V35Config} {s s' : V35State} {T : V35Transition}
    (h : V35Step X s (.infra T) s') :
    X.base.rc.hasCode T.addr ∧ T.domain = .ctm ∧ X.base.rc.hasCode T.engine ∧
      T.inventory.length = X.inventoryLength .ctm ∧ X.code T.engine T s s' ∧
      PostChecks X T s s' := by
  cases h with
  | infra h1 h2 h3 h4 h5 h6 => exact ⟨h1, h2, h3, h4, h5, h6⟩
  | other hl _ => simp [V35Label.toX?] at hl

lemma toX?_none {l : V35Label} (h : l.toX? = none) : ∃ T, l = .infra T := by
  cases l with
  | infra T => exact ⟨T, rfl⟩
  | _ => simp [V35Label.toX?] at h

lemma other_inv {X : V35Config} {s s' : V35State} {l : V35Label} {x : XLabel}
    (hl : l.toX? = some x) (h : V35Step X s l s') : XStep X.base s.x x s'.x := by
  cases h with
  | infra _ _ _ _ _ _ => simp [V35Label.toX?] at hl
  | other hl' hs =>
      rw [hl] at hl'
      cases hl'
      exact hs

lemma tame_toX {X : V35Config} {l : V35Label} {x : XLabel} (hl : l.toX? = some x)
    (ht : l.Tame X) : x.Tame X.base := by
  cases l with
  | infra _ => simp [V35Label.toX?] at hl
  | commit _ =>
      simp only [V35Label.toX?, Option.some.injEq] at hl
      subst hl; trivial
  | upgradeChain _ =>
      simp only [V35Label.toX?, Option.some.injEq] at hl
      subst hl; trivial
  | forward _ =>
      simp only [V35Label.toX?, Option.some.injEq] at hl
      subst hl; exact ht
  | env _ =>
      simp only [V35Label.toX?, Option.some.injEq] at hl
      subst hl; trivial

/-! ## A reviewed leg is an `e561b9cc2` executor run -/

lemma reviewed_leg {X : V35Config} {T : V35Transition} {s s' : V35State}
    (hr : EngineReviewed X T) (h : V35Step X s (.infra T) s') :
    ∃ pre post : List FCall, (∀ c ∈ pre, ReviewedHookCall c) ∧ (∀ c ∈ post, ReviewedHookCall c) ∧
      XRun X.base s.x [.forward pre, .infra T.toCurrent, .forward post] s'.x := by
  obtain ⟨hcode, hd, _, _, hc, _⟩ := infra_inv h
  obtain ⟨x₁, x₂, ⟨pre, hpre, hr₁⟩, hcore, ⟨post, hpost, hr₂⟩⟩ := hr s s' hc
  obtain ⟨hx, _⟩ := engineCore_xstep hcore hcode hd
  exact ⟨pre, post, hpre, hpost,
    XRun.cons (XStep.forward hr₁) (XRun.cons hx (XRun.cons (XStep.forward hr₂) XRun.nil))⟩

lemma xrun_append {X : XConfig} {s s₁ s₂ : XState} {xs ys : List XLabel}
    (h₁ : XRun X s xs s₁) (h₂ : XRun X s₁ ys s₂) : XRun X s (xs ++ ys) s₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact XRun.cons hs (ih h₂)

lemma v35run_append {X : V35Config} {s s₁ s₂ : V35State} {ls ms : List V35Label}
    (h₁ : V35Run X s ls s₁) (h₂ : V35Run X s₁ ms s₂) : V35Run X s (ls ++ ms) s₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact V35Run.cons hs (ih h₂)

/-- A reviewed engine is tame, for rows that do not name the CTM proxy. -/
lemma reviewed_tame {X : V35Config} {T : V35Transition} (hr : EngineReviewed X T)
    (ht : V35Label.Tame X (.infra T)) : EngineIsTame X T := by
  intro s s' h
  obtain ⟨pre, post, hpre, hpost, hrun⟩ := reviewed_leg hr h
  refine ⟨_, hrun, ?_⟩
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl
  · exact fun c hc => reviewedHookCall_tame (hpre c hc)
  · exact ht
  · exact fun c hc => reviewedHookCall_tame (hpost c hc)

/-- One `d9f6789` transaction as tame `ExecutorForward` transactions. -/
lemma tame_step {X : V35Config} {s s' : V35State} {l : V35Label} (h : V35Step X s l s')
    (ht : l.Tame X) (hr : ∀ T, l = .infra T → EngineIsTame X T) :
    ∃ ys : List XLabel, XRun X.base s.x ys s'.x ∧ ∀ y ∈ ys, y.Tame X.base := by
  rcases hlx : l.toX? with _ | x
  · obtain ⟨T, rfl⟩ := toX?_none hlx
    exact hr T rfl s s' h
  · exact ⟨[x], XRun.cons (other_inv hlx h) XRun.nil, fun y hy => by
      rw [List.mem_singleton.mp hy]; exact tame_toX hlx ht⟩

lemma tame_run {X : V35Config} {s s' : V35State} {ls : List V35Label} (h : V35Run X s ls s') :
    (∀ l ∈ ls, l.Tame X) → (∀ T, V35Label.infra T ∈ ls → EngineIsTame X T) →
    ∃ xs : List XLabel, XRun X.base s.x xs s'.x ∧ ∀ x ∈ xs, x.Tame X.base := by
  induction h with
  | nil => intro _ _; exact ⟨[], XRun.nil, fun _ h => absurd h List.not_mem_nil⟩
  | cons hstep _ ih =>
      intro ht hr
      obtain ⟨xs, hxs, hxt⟩ := ih (fun l' hl' => ht l' (List.mem_cons_of_mem _ hl'))
        (fun T hT => hr T (List.mem_cons_of_mem _ hT))
      obtain ⟨ys, hys, hyt⟩ := tame_step hstep (ht _ List.mem_cons_self)
        (fun T hT => hr T (by rw [← hT]; exact List.mem_cons_self))
      exact ⟨ys ++ xs, xrun_append hys hxs,
        fun y hy => (List.mem_append.mp hy).elim (hyt y) (hxt y)⟩

end Contracts.ChainTypeManager.ExecutorEngineAtV35

/-! ## Certificates -/

namespace Contracts.ChainTypeManager.ExecutorEngineAtV35

theorem ExecutorChecksAfterAnyEngine : Properties.ExecutorChecksAfterAnyEngine := by
  intro X T s s' h
  obtain ⟨hcode, hd, hcodeE, _, _, hp⟩ := infra_inv h
  refine ⟨hcode, hd, hcodeE, hp.rows, hp.owner, hp.pendingOwner, ?_⟩
  by_cases heq : s'.holders = s.holders
  · exact Or.inl heq
  · exact Or.inr ⟨heq, hp.holders⟩

theorem EveryForwardIsAnEngineLeg : Properties.EveryForwardIsAnEngineLeg := by
  intro X T s calls x' hcodeEq hcode hd hcodeE hlen
  constructor
  · intro h
    obtain ⟨_, _, _, _, hc, hp⟩ := infra_inv h
    rw [hcodeEq] at hc
    exact ⟨XStep.forward hc.1, hp.rows⟩
  · rintro ⟨hx, hrows⟩
    cases hx with
    | forward hr =>
        refine V35Step.infra hcode hd hcodeE hlen ?_ ⟨rfl, rfl, rfl, hrows⟩
        rw [hcodeEq]
        exact ⟨hr, rfl, rfl⟩

theorem DefaultEngineLegIsAnInfraStep : Properties.DefaultEngineLegIsAnInfraStep := by
  intro X T s s' hdef h
  obtain ⟨hcode, hd, _, _, hc, _⟩ := infra_inv h
  rw [EngineIsDefault] at hdef
  rw [hdef] at hc
  obtain ⟨hcore, ho, hp⟩ := hc
  obtain ⟨hx, hown⟩ := engineCore_xstep hcore hcode hd
  exact ⟨hx, hown, ho, hp⟩

theorem InfraStepIsADefaultEngineLeg : Properties.InfraStepIsADefaultEngineLeg := by
  intro X T s x' hdef hx ho hcodeE hlen
  obtain ⟨hcore, hcode, hd⟩ := xstep_engineCore hx ho
  refine V35Step.infra hcode hd hcodeE hlen ?_ ⟨rfl, rfl, rfl, engineCore_rows hcore⟩
  rw [EngineIsDefault] at hdef
  rw [hdef]
  exact ⟨hcore, rfl, rfl⟩

theorem DefaultEngineIsReviewed : Properties.DefaultEngineIsReviewed := by
  intro X T hdef s s' hc
  rw [EngineIsDefault] at hdef
  rw [hdef] at hc
  obtain ⟨hcore, _, _⟩ := hc
  exact ⟨s.x, s'.x, ⟨[], fun _ h => absurd h List.not_mem_nil, FRun.nil⟩, hcore,
    ⟨[], fun _ h => absurd h List.not_mem_nil, FRun.nil⟩⟩

theorem ReviewedLegIsAnExecutorRun : Properties.ReviewedLegIsAnExecutorRun := by
  intro X T s s' hr h
  obtain ⟨pre, post, hpre, hpost, hrun⟩ := reviewed_leg hr h
  exact ⟨pre, post, fun c hc => (List.mem_append.mp hc).elim (hpre c) (hpost c), hrun⟩

theorem ReviewedEngineIsTame : Properties.ReviewedEngineIsTame :=
  fun _ _ hr ht => reviewed_tame hr ht

theorem TameEngineRunIsATameExecutorRun : Properties.TameEngineRunIsATameExecutorRun :=
  fun _ _ _ _ h ht hr => tame_run h ht hr

theorem TameEngineRunPreservesSysInv : Properties.TameEngineRunPreservesSysInv := by
  intro X s s' ls hf hI h ht hr
  obtain ⟨xs, hxs, hxt⟩ := tame_run h ht hr
  exact TameRunPreservesSysInv X.base s.x s'.x xs hf hI hxs hxt

theorem TameEngineRunKeepsChainsOnTheirRelease :
    Properties.TameEngineRunKeepsChainsOnTheirRelease := by
  intro X s s' ls hf hI h ht hr
  obtain ⟨xs, hxs, hxt⟩ := tame_run h ht hr
  exact TameRunKeepsChainsOnTheirRelease X.base s.x s'.x xs hf hI hxs hxt

theorem ReviewedRunKeepsChainsOnTheirRelease :
    Properties.ReviewedRunKeepsChainsOnTheirRelease :=
  fun X s s' ls hf hI h ht hr => TameEngineRunKeepsChainsOnTheirRelease X s s' ls hf hI h ht
    (fun T hT => reviewed_tame (hr T hT) (ht _ hT))

theorem DefaultEngineRunKeepsChainsOnTheirRelease :
    Properties.DefaultEngineRunKeepsChainsOnTheirRelease :=
  fun X s s' ls hf hI h ht hd => ReviewedRunKeepsChainsOnTheirRelease X s s' ls hf hI h ht
    (fun T hT => DefaultEngineIsReviewed X T (hd T hT))

theorem ReviewedLegsMoveProxiesOnlyAlongRows :
    Properties.ReviewedLegsMoveProxiesOnlyAlongRows := by
  intro X s s' l hf h hnf hrev p
  cases h with
  | @infra s' T _ _ _ _ hc _ =>
      obtain ⟨x₁, x₂, h₁, hcore, h₂⟩ := hrev T rfl s s' hc
      have e₁ := hookRun_impl h₁
      have e₂ := hookRun_impl h₂
      cases hcore with
      | @mk J _ _ happ _ =>
          rcases ProxyUpgradeCurrent.OnlyNamedEdgesAcrossCallAnyRows X.base.rc x₁.impl J T.rows hf
              happ p with h1 | ⟨r, hr, hp, h2, h3⟩
          · left
            rw [e₂, ← e₁]
            exact h1
          · right
            refine ⟨T, r, rfl, hr, hp, ?_, ?_⟩
            · rw [← e₁]; exact h2
            · rw [e₂]; exact h3
  | @other l x x' hl hs =>
      left
      cases hs with
      | infra _ _ => cases l <;> simp [V35Label.toX?] at hl
      | commit _ _ _ => rfl
      | upgradeChain _ => rfl
      | forward _ =>
          exfalso
          cases l <;> simp [V35Label.toX?] at hl
          subst hl
          exact hnf _ rfl
      | env _ _ => rfl

theorem ReviewedEngineRefusesStaleRows : Properties.ReviewedEngineRefusesStaleRows := by
  rintro X T s r hf hrev hd hr hsrc htgt ⟨s', h⟩
  obtain ⟨_, _, _, _, hc, _⟩ := infra_inv h
  obtain ⟨x₁, x₂, h₁, hcore, _⟩ := hrev s s' hc
  have e₁ := hookRun_impl h₁
  cases hcore with
  | mk _ happ _ =>
      rcases ProxyUpgradeCurrent.applyLoop_source hf happ.loop hd r hr with h1 | h1
      · exact htgt (by rw [← e₁]; exact h1)
      · exact hsrc (by rw [← e₁]; exact h1)

end Contracts.ChainTypeManager.ExecutorEngineAtV35

/-! ## Countermodels and the witness -/

namespace Contracts.ChainTypeManager.ExecutorEngineAtV35

/-! ### The witness engines and objects -/

lemma wCode70 : wCode 70 = defaultEngine wX := by
  unfold wCode; rw [ite_eq_left rfl]

lemma wCode71 : wCode 71 = subclassEngine wX [] wHookCalls := by
  unfold wCode; rw [ite_eq_right (by decide), ite_eq_left rfl]

lemma wCode72 : wCode 72 = subclassEngine wX [] wCutCalls := by
  unfold wCode; rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

lemma wCode73 : wCode 73 = subclassEngine wX [] wSwapCalls := by
  unfold wCode; rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

lemma wCode74 : wCode 74 = callingEngine wX [.upgradeProxy 5 11] := by
  unfold wCode
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

lemma wCode75 : wCode 75 = subclassEngine wX [] [.upgradeProxy 7 42] := by
  unfold wCode
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_left rfl]

lemma wCode76 : wCode 76 = subclassEngine wX [.upgradeProxy 5 10] [] := by
  unfold wCode
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

lemma wTAB_rows (e : Address) :
    (wTAB e).rows = [ProxyUpgradeCurrent.rowA, ProxyUpgradeCurrent.rowB] := by
  show ProxyUpgradeCurrent.toRows [ProxyUpgradeCurrent.rowA, ProxyUpgradeCurrent.rowB] = _
  decide

lemma wTA_rows (a e : Address) : (wTA a e).rows = [ProxyUpgradeCurrent.rowA] := by
  show ProxyUpgradeCurrent.toRows [ProxyUpgradeCurrent.rowA, ProxyUpgradeCurrent.slotInert] = _
  decide

lemma wTA2_rows : wTA2.rows = [ProxyUpgradeCurrent.rowA2] := by
  show ProxyUpgradeCurrent.toRows [ProxyUpgradeCurrent.rowA2, ProxyUpgradeCurrent.slotInert] = _
  decide

lemma wTAB_genuine (e : Address) (he : e ≠ 0) : (wTAB e).Genuine 2 := by
  refine ⟨rfl, ?_, ?_, he⟩
  · rw [wTAB_rows]; simp
  · rw [wTAB_rows]; exact ProxyUpgradeCurrent.valid_AB

lemma wTA_genuine (a e : Address) (he : e ≠ 0) : (wTA a e).Genuine 2 := by
  refine ⟨rfl, ?_, ?_, he⟩
  · rw [wTA_rows]; simp
  · rw [wTA_rows]; exact ProxyUpgradeCurrent.valid_A

lemma wTAB_tame (e : Address) : V35Label.Tame wV35 (.infra (wTAB e)) := by
  intro r hr
  rw [wTAB_rows] at hr
  rcases ProxyUpgradeCurrent.mem_AB hr with rfl | rfl <;> decide

lemma wTA_tame (a e : Address) : V35Label.Tame wV35 (.infra (wTA a e)) := by
  intro r hr
  rw [wTA_rows, List.mem_singleton] at hr
  subst hr; decide

lemma wTA2_tame : V35Label.Tame wV35 (.infra wTA2) := by
  intro r hr
  rw [wTA2_rows, List.mem_singleton] at hr
  subst hr; decide

/-! ### Building legs -/

lemma default_leg {X : V35Config} {T : V35Transition} {s : V35State} {x' : XState}
    (hcodeEq : X.code T.engine = defaultEngine X.base) (hcode : X.base.rc.hasCode T.addr)
    (hd : T.domain = .ctm) (hcodeE : X.base.rc.hasCode T.engine)
    (hlen : T.inventory.length = X.inventoryLength .ctm) (h : EngineCore X.base T s.x x') :
    V35Step X s (.infra T) { s with x := x' } := by
  refine V35Step.infra hcode hd hcodeE hlen ?_ ⟨rfl, rfl, rfl, engineCore_rows h⟩
  rw [hcodeEq]
  exact ⟨h, rfl, rfl⟩

lemma subclass_leg {X : V35Config} {T : V35Transition} {s : V35State} {pre post : List FCall}
    {x₁ x₂ x₃ : XState} (hcodeEq : X.code T.engine = subclassEngine X.base pre post)
    (hcode : X.base.rc.hasCode T.addr) (hd : T.domain = .ctm) (hcodeE : X.base.rc.hasCode T.engine)
    (hlen : T.inventory.length = X.inventoryLength .ctm)
    (h₁ : FRun X.base s.x pre x₁) (h₂ : EngineCore X.base T x₁ x₂) (h₃ : FRun X.base x₂ post x₃)
    (hrows : ProxyUpgradeCurrent.RowsApplied x₃.impl T.rows) :
    V35Step X s (.infra T) { s with x := x₃ } := by
  refine V35Step.infra hcode hd hcodeE hlen ?_ ⟨rfl, rfl, rfl, hrows⟩
  rw [hcodeEq]
  exact ⟨⟨x₁, x₂, h₁, h₂, h₃⟩, rfl, rfl⟩

lemma calling_leg {X : V35Config} {T : V35Transition} {s : V35State} {calls : List FCall}
    {x' : XState} (hcodeEq : X.code T.engine = callingEngine X.base calls)
    (hcode : X.base.rc.hasCode T.addr) (hd : T.domain = .ctm) (hcodeE : X.base.rc.hasCode T.engine)
    (hlen : T.inventory.length = X.inventoryLength .ctm) (h : FRun X.base s.x calls x')
    (hrows : ProxyUpgradeCurrent.RowsApplied x'.impl T.rows) :
    V35Step X s (.infra T) { s with x := x' } := by
  refine V35Step.infra hcode hd hcodeE hlen ?_ ⟨rfl, rfl, rfl, hrows⟩
  rw [hcodeEq]
  exact ⟨h, rfl, rfl⟩

lemma subclass_reviewed {X : V35Config} {T : V35Transition} {pre post : List FCall}
    (hcodeEq : X.code T.engine = subclassEngine X.base pre post)
    (hpre : ∀ c ∈ pre, ReviewedHookCall c) (hpost : ∀ c ∈ post, ReviewedHookCall c) :
    EngineReviewed X T := by
  intro s s' hc
  rw [hcodeEq] at hc
  obtain ⟨⟨x₁, x₂, h₁, h₂, h₃⟩, _, _⟩ := hc
  exact ⟨x₁, x₂, ⟨pre, hpre, h₁⟩, h₂, ⟨post, hpost, h₃⟩⟩

/-! ### The row applications of the witnesses -/

/-- `applyRows` of `5: 10 → 11`, `6: 10 → 12` from the fresh implementations. -/
lemma wApplyAB (e : Address) : ProxyUpgradeCurrent.ApplyRows wX.rc wX0.impl (wTAB e).rows wJ := by
  rw [wTAB_rows]; exact ProxyUpgradeCurrent.applyRows_AB

/-- The same rows again, once applied: every row skips. -/
lemma wApplyAB_again (e : Address) : ProxyUpgradeCurrent.ApplyRows wX.rc wJ (wTAB e).rows wJ := by
  rw [wTAB_rows]
  exact ProxyUpgradeCurrent.ApplyRowsIdempotent _ _ _ _ ProxyUpgradeCurrent.applyRows_AB

/-- The implementations after `5: 10 → 11`. -/
abbrev wI1 : ProxyUpgradeCurrent.Impl :=
  ProxyUpgradeCurrent.swap ProxyUpgradeCurrent.wConfig ProxyUpgradeCurrent.rowA
    ProxyUpgradeCurrent.wImpl

/-- The implementations after `5: 11 → 12`. -/
abbrev wI2 : ProxyUpgradeCurrent.Impl :=
  ProxyUpgradeCurrent.swap ProxyUpgradeCurrent.wConfig ProxyUpgradeCurrent.rowA2 wI1

lemma wApplyA (a e : Address) :
    ProxyUpgradeCurrent.ApplyRows wX.rc wX0.impl (wTA a e).rows wI1 := by
  rw [wTA_rows]
  refine ⟨ProxyUpgradeCurrent.code_all _ (fun _ => trivial) _,
    ProxyUpgradeCurrent.ApplyLoop.cons
      (ProxyUpgradeCurrent.ApplyRow.upgrade rfl (by decide) (by decide))
      ProxyUpgradeCurrent.ApplyLoop.nil, ?_⟩
  intro r hr
  rw [List.mem_singleton.mp hr]; decide

lemma wApplyA2 : ProxyUpgradeCurrent.ApplyRows wX.rc wI1 wTA2.rows wI2 := by
  rw [wTA2_rows]
  refine ⟨ProxyUpgradeCurrent.code_all _ (fun _ => trivial) _,
    ProxyUpgradeCurrent.ApplyLoop.cons
      (ProxyUpgradeCurrent.ApplyRow.upgrade rfl (by decide) (by decide))
      ProxyUpgradeCurrent.ApplyLoop.nil, ?_⟩
  intro r hr
  rw [List.mem_singleton.mp hr]; decide

/-- The stale row `5: 10 → 11` after a hook moved proxy `5` back to `10`. -/
lemma wApplyA_back (a e : Address) :
    ProxyUpgradeCurrent.ApplyRows wX.rc (ProxyUpgradeCurrent.upd wI2 5 10) (wTA a e).rows
      (ProxyUpgradeCurrent.swap ProxyUpgradeCurrent.wConfig ProxyUpgradeCurrent.rowA
        (ProxyUpgradeCurrent.upd wI2 5 10)) := by
  rw [wTA_rows]
  refine ⟨ProxyUpgradeCurrent.code_all _ (fun _ => trivial) _,
    ProxyUpgradeCurrent.ApplyLoop.cons
      (ProxyUpgradeCurrent.ApplyRow.upgrade rfl (by decide) (by decide))
      ProxyUpgradeCurrent.ApplyLoop.nil, ?_⟩
  intro r hr
  rw [List.mem_singleton.mp hr]; decide

end Contracts.ChainTypeManager.ExecutorEngineAtV35

namespace Contracts.ChainTypeManager.ExecutorEngineAtV35

/-! ### A hook engine is not the default engine -/

lemma frun_replace_slot {X : XConfig} {x x' : XState} {e r : Address}
    (h : FRun X x [.sys (.ctm (.replace e r))] x') : x.sys.ctm.ut (X.W.tr e).old = e := by
  cases h with
  | cons hstep _ =>
      cases hstep with
      | sys hs =>
          cases hs with
          | ctm hc =>
              cases hc with
              | replace _ _ hslot _ _ _ _ _ => exact hslot

/-- From the fresh state the default engine applies `wTAB 71`'s rows, while the hook engine
`71` reverts: there is no committed transition `300` to replace. -/
lemma hook_not_default : ¬ EngineIsDefault wV35 (wTAB 71) := by
  intro h
  have hd : defaultEngine wX (wTAB 71) wV0
      { wV0 with x := ⟨{ wX0.sys with ctm := wX0.sys.ctm }, wJ⟩ } :=
    ⟨EngineCore.mk rfl (wApplyAB 71) (fun _ => rfl), rfl, rfl⟩
  have h' : wCode 71 = defaultEngine wX := h
  rw [← h', wCode71] at hd
  obtain ⟨⟨x₁, x₂, h₁, h₂, h₃⟩, _, _⟩ := hd
  cases h₁
  cases h₂ with
  | mk _ happ hc =>
      have hJ := ProxyUpgradeCurrent.UnmovedProxiesFrame _ _ _ _ ProxyUpgradeCurrent.wConfig_frames
        happ 8 (by
          rw [wTAB_rows]; intro r hr
          rcases ProxyUpgradeCurrent.mem_AB hr with rfl | rfl <;> decide)
      have hslot := frun_replace_slot h₃
      rw [hc hJ] at hslot
      have h0 : wV0.x.sys.ctm.ut (wX.W.tr 300).old = 300 := hslot
      exact absurd h0 (by decide)

/-! ### Tame engines -/

lemma subclass_tame {X : V35Config} {T : V35Transition} {pre post : List FCall}
    (hcodeEq : X.code T.engine = subclassEngine X.base pre post)
    (hpre : ∀ c ∈ pre, c.Tame) (hpost : ∀ c ∈ post, c.Tame) (ht : V35Label.Tame X (.infra T)) :
    EngineIsTame X T := by
  intro s s' h
  obtain ⟨hcode, hd, _, _, hc, _⟩ := infra_inv h
  rw [hcodeEq] at hc
  obtain ⟨⟨x₁, x₂, h₁, h₂, h₃⟩, _, _⟩ := hc
  obtain ⟨hx, _⟩ := engineCore_xstep h₂ hcode hd
  refine ⟨[.forward pre, .infra T.toCurrent, .forward post],
    XRun.cons (XStep.forward h₁) (XRun.cons hx (XRun.cons (XStep.forward h₃) XRun.nil)), ?_⟩
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl
  · exact hpre
  · exact ht
  · exact hpost

lemma calling_tame {X : V35Config} {T : V35Transition} {calls : List FCall}
    (hcodeEq : X.code T.engine = callingEngine X.base calls) (hcs : ∀ c ∈ calls, c.Tame) :
    EngineIsTame X T := by
  intro s s' h
  obtain ⟨_, _, _, _, hc, _⟩ := infra_inv h
  rw [hcodeEq] at hc
  exact ⟨[.forward calls], XRun.cons (XStep.forward hc.1) XRun.nil, fun y hy => by
    rw [List.mem_singleton.mp hy]; exact hcs⟩

/-! ### Countermodels -/

theorem CuttingEngineBreaksTheHeadline : Properties.CuttingEngineBreaksTheHeadline := by
  have hrun := V35Run.cons (X := wV35) (s := wV0) (l := .env (.genesis 0))
    (V35Step.other rfl (XStep.env trivial
      (Step.genesis (id := 0) rfl (addAll_empty_eq xNodup100))))
    (V35Run.cons (subclass_leg (T := wTAB 72) wCode72 trivial rfl trivial rfl FRun.nil
        (EngineCore.mk rfl (wApplyAB 72) (fun _ => rfl))
        (FRun.cons (FStep.sys (Step.arbitraryCut (id := 0) 1 bgExtra rfl)) FRun.nil)
        (by
          rw [wTAB_rows]; intro r hr
          rcases ProxyUpgradeCurrent.mem_AB hr with rfl | rfl <;> decide))
      V35Run.nil)
  have htame : ∀ l ∈ [V35Label.env (.genesis 0), .infra (wTAB 72)], l.Tame wV35 := by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · trivial
    · exact wTAB_tame 72
  have hdrift : bgExtra ≠ rowsRouting (wRows 100) := fun h => absurd (congrFun h 9) (by decide)
  have hntame : ¬ EngineIsTame wV35 (wTAB 72) := by
    intro htm
    have h := TameEngineRunKeepsChainsOnTheirRelease wV35 wV0 _ _
      ProxyUpgradeCurrent.wConfig_frames wX0_inv hrun htame (fun T hT => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
          V35Label.infra.injEq] at hT
        subst hT; exact htm) 0 ⟨1, bgExtra⟩ rfl (by decide)
    exact hdrift h.2
  exact ⟨ProxyUpgradeCurrent.wConfig_frames, wX0_inv, wTAB_genuine 72 (by decide), htame, hntame,
    fun hrev => hntame (reviewed_tame hrev (wTAB_tame 72)),
    _, hrun, rfl, rfl, rfl, ⟨1, bgExtra⟩, rfl, rfl, by decide, hdrift⟩

theorem CtmSwappingEngineBreaksSysInv : Properties.CtmSwappingEngineBreaksSysInv := by
  have hc : CStep wWorld (initState wWorld 100) (.commit 300) _ :=
    CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨p1, p2⟩ := ExecutorPostcheckPasses _ _ _ _ hc
  have hrun := V35Run.cons (X := wV35) (s := wV0) (l := .env (.genesis 0))
    (V35Step.other rfl (XStep.env trivial
      (Step.genesis (id := 0) rfl (addAll_empty_eq xNodup100))))
    (V35Run.cons (V35Step.other (l := .commit 300) rfl (XStep.commit (Step.ctm hc) p1 p2))
    (V35Run.cons (V35Step.other (l := .upgradeChain 0) rfl (XStep.upgradeChain
        (Step.transition (id := 0) rfl (by decide) rfl
          (applyDerived_rows_eq xNodup100 xNodup200) (by decide)))) V35Run.nil))
  have htame3 : ∀ l ∈ [V35Label.env (.genesis 0), .commit 300, .upgradeChain 0], l.Tame wV35 := by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> trivial
  have hex : ∃ s s', V35Run wV35 wV0 [.env (.genesis 0), .commit 300, .upgradeChain 0] s ∧
      SysInv wV35.base.W s.x.sys ∧ V35Step wV35 s (.infra (wTAB 73)) s' ∧
      s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner ∧ s'.holders = s.holders ∧
      s'.x.impl wX.ctmProxy ≠ s.x.impl wX.ctmProxy ∧
      s'.x.sys.ctm.pv < s.x.sys.ctm.pv ∧ ¬ SysInv wV35.base.W s'.x.sys := by
    refine ⟨_, _, hrun,
      (TameEngineRunPreservesSysInv wV35 wV0 _ _ ProxyUpgradeCurrent.wConfig_frames wX0_inv hrun
        htame3 (fun T hT => by simp at hT)).1,
      subclass_leg (T := wTAB 73) wCode73 trivial rfl trivial rfl FRun.nil
        (EngineCore.mk rfl (wApplyAB 73) (fun _ => rfl))
        (FRun.cons (FStep.swapCtm (x := 42) (c' := initState wWorld 100) rfl trivial) FRun.nil)
        (by
          rw [wTAB_rows]; intro r hr
          rcases ProxyUpgradeCurrent.mem_AB hr with rfl | rfl <;> decide),
      rfl, rfl, rfl, by decide, by decide, ?_⟩
    intro hI
    exact absurd (hI.2 0 _ rfl).1 (by decide)
  have hex2 := hex
  obtain ⟨s, s', hrun', _, hleg, _, _, _, _, _, hnI⟩ := hex2
  have hntame : ¬ EngineIsTame wV35 (wTAB 73) := by
    intro hrev
    apply hnI
    refine (TameEngineRunPreservesSysInv wV35 wV0 s' _ ProxyUpgradeCurrent.wConfig_frames wX0_inv
      (v35run_append hrun' (V35Run.cons hleg V35Run.nil)) ?_ ?_).1
    · intro l hl
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · trivial
      · trivial
      · trivial
      · exact wTAB_tame 73
    · intro T hT
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
        reduceCtorEq, false_or, V35Label.infra.injEq] at hT
      subst hT; exact hrev
  exact ⟨ProxyUpgradeCurrent.wConfig_frames, wTAB_genuine 73 (by decide), wTAB_tame 73,
    wTAB_tame 73, hntame, fun hrev => hntame (reviewed_tame hrev (wTAB_tame 73)), hex⟩

theorem ProxyMovingEngineMovesAnUnnamedProxy :
    Properties.ProxyMovingEngineMovesAnUnnamedProxy := by
  have hex : ∃ s', V35Step wV35 wV0 (.infra (wTAB 75)) s' ∧ wV0.x.impl 7 = 10 ∧
      s'.x.impl 7 = 42 ∧ s'.owner = wV0.owner ∧ s'.pendingOwner = wV0.pendingOwner ∧
      s'.holders = wV0.holders ∧ ¬ V35MovesOnlyAlongRows wV0 s' (.infra (wTAB 75)) := by
    refine ⟨_, subclass_leg (X := wV35) (T := wTAB 75) (s := wV0) wCode75 trivial rfl trivial rfl
      FRun.nil (EngineCore.mk rfl (wApplyAB 75) (fun _ => rfl))
      (FRun.cons (FStep.upgradeProxy (p := 7) (x := 42) rfl trivial (by decide)) FRun.nil)
      (by
        rw [wTAB_rows]; intro r hr
        rcases ProxyUpgradeCurrent.mem_AB hr with rfl | rfl <;> decide),
      by decide, by decide, rfl, rfl, rfl, ?_⟩
    intro hm
    rcases hm 7 with h | ⟨T, r, hT, hr, hp, _, _⟩
    · exact absurd h (by decide)
    · cases hT
      rw [wTAB_rows] at hr
      rcases ProxyUpgradeCurrent.mem_AB hr with rfl | rfl <;> exact absurd hp (by decide)
  have hex2 := hex
  obtain ⟨s', hleg, _, _, _, _, _, hnm⟩ := hex2
  refine ⟨ProxyUpgradeCurrent.wConfig_frames, wTAB_genuine 75 (by decide), ?_, ?_,
    subclass_tame wCode75 (fun _ h => absurd h List.not_mem_nil)
      (fun c hc => by rw [List.mem_singleton.mp hc]; trivial) (wTAB_tame 75), ?_, hex⟩
  · rw [wTAB_rows]; exact ProxyUpgradeCurrent.valid_AB.distinctProxies
  · intro r hr
    rw [wTAB_rows] at hr
    rcases ProxyUpgradeCurrent.mem_AB hr with rfl | rfl <;> decide
  · intro hrev
    exact hnm (ReviewedLegsMoveProxiesOnlyAlongRows wV35 wV0 _ _ ProxyUpgradeCurrent.wConfig_frames
      hleg (fun _ h => by cases h) (fun T hT => by cases hT; exact hrev))

/-- The two default-engine legs of `wStaleRun`: proxy `5` goes `10 → 11 → 12`. -/
lemma wStaleRun_run : V35Run wV35 wV0 wStaleRun
    { { wV0 with x := ⟨{ wX0.sys with ctm := wX0.sys.ctm }, wI1⟩ } with
      x := ⟨{ ({ wX0.sys with ctm := wX0.sys.ctm } : Sys) with
        ctm := ({ wX0.sys with ctm := wX0.sys.ctm } : Sys).ctm }, wI2⟩ } :=
  V35Run.cons (default_leg (T := wTA 30 70) wCode70 trivial rfl trivial rfl
      (EngineCore.mk rfl (wApplyA 30 70) (fun _ => rfl)))
    (V35Run.cons (default_leg (T := wTA2) wCode70 trivial rfl trivial rfl
      (EngineCore.mk rfl wApplyA2 (fun _ => rfl))) V35Run.nil)

/-- After `wStaleRun` the default engine refuses the stale object `wTA 30 70`. -/
lemma wStale_refused (s : V35State) (h5 : s.x.impl 5 = 12) :
    ¬ ∃ s', V35Step wV35 s (.infra (wTA 30 70)) s' :=
  ReviewedEngineRefusesStaleRows wV35 (wTA 30 70) s ProxyUpgradeCurrent.rowA
    ProxyUpgradeCurrent.wConfig_frames (DefaultEngineIsReviewed _ _ wCode70)
    (by rw [wTA_rows]; exact List.pairwise_singleton _ _)
    (by rw [wTA_rows]; exact List.mem_singleton_self _)
    (by show s.x.impl 5 ≠ 10; rw [h5]; decide) (by show s.x.impl 5 ≠ 11; rw [h5]; decide)

theorem DirectEngineSkipsTheSourceCheck : Properties.DirectEngineSkipsTheSourceCheck := by
  have hex : ∃ s, V35Run wV35 wV0 wStaleRun s ∧ s.x.impl 5 = 12 ∧
      s.x.impl ProxyUpgradeCurrent.rowA.proxy ≠ ProxyUpgradeCurrent.rowA.expectedOldImpl ∧
      s.x.impl ProxyUpgradeCurrent.rowA.proxy ≠ ProxyUpgradeCurrent.rowA.implNew ∧
      (¬ ∃ s', V35Step wV35 s (.infra (wTA 30 70)) s') ∧
      ∃ s', V35Step wV35 s (.infra (wTA 34 74)) s' ∧ s'.x.impl 5 = 11 ∧
        s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner ∧ s'.holders = s.holders ∧
        ¬ V35MovesOnlyAlongRows s s' (.infra (wTA 34 74)) := by
    refine ⟨_, wStaleRun_run, by decide, by decide, by decide, wStale_refused _ (by decide), _,
      calling_leg (T := wTA 34 74) wCode74 trivial rfl trivial rfl
        (FRun.cons (FStep.upgradeProxy (p := 5) (x := 11) rfl trivial (by decide)) FRun.nil)
        (by rw [wTA_rows]; intro r hr; rw [List.mem_singleton.mp hr]; decide),
      by decide, rfl, rfl, rfl, ?_⟩
    intro hm
    rcases hm 5 with h | ⟨T, r, hT, hr, _, h2, _⟩
    · exact absurd h (by decide)
    · cases hT
      rw [wTA_rows, List.mem_singleton] at hr
      subst hr
      exact absurd h2 (by decide)
  have hex2 := hex
  obtain ⟨s, _, _, hsrc, htgt, _, s', hleg, _⟩ := hex2
  refine ⟨ProxyUpgradeCurrent.wConfig_frames, DefaultEngineIsReviewed _ _ wCode70,
    wTA_genuine 30 70 (by decide), wTA_genuine 34 74 (by decide), by rw [wTA_rows, wTA_rows],
    by rw [wTA_rows]; exact List.pairwise_singleton _ _, wCode74,
    calling_tame wCode74 (fun c hc => by rw [List.mem_singleton.mp hc]; trivial), ?_, hex⟩
  intro hrev
  exact ReviewedEngineRefusesStaleRows wV35 (wTA 34 74) s ProxyUpgradeCurrent.rowA
    ProxyUpgradeCurrent.wConfig_frames hrev
    (by rw [wTA_rows]; exact List.pairwise_singleton _ _)
    (by rw [wTA_rows]; exact List.mem_singleton_self _) hsrc htgt ⟨s', hleg⟩

theorem BeforeHookDefeatsTheSourceCheck : Properties.BeforeHookDefeatsTheSourceCheck := by
  have hex : ∃ s, V35Run wV35 wV0 wStaleRun s ∧ s.x.impl 5 = 12 ∧
      ∃ s', V35Step wV35 s (.infra (wTA 36 76)) s' ∧ s'.x.impl 5 = 11 ∧
        s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner ∧ s'.holders = s.holders ∧
        ¬ V35MovesOnlyAlongRows s s' (.infra (wTA 36 76)) := by
    refine ⟨_, wStaleRun_run, by decide, _,
      subclass_leg (T := wTA 36 76) wCode76 trivial rfl trivial rfl
        (FRun.cons (FStep.upgradeProxy (p := 5) (x := 10) rfl trivial (by decide)) FRun.nil)
        (EngineCore.mk rfl (wApplyA_back 36 76) (fun _ => rfl)) FRun.nil
        (by rw [wTA_rows]; intro r hr; rw [List.mem_singleton.mp hr]; decide),
      by decide, rfl, rfl, rfl, ?_⟩
    intro hm
    rcases hm 5 with h | ⟨T, r, hT, hr, _, h2, _⟩
    · exact absurd h (by decide)
    · cases hT
      rw [wTA_rows, List.mem_singleton] at hr
      subst hr
      exact absurd h2 (by decide)
  have hex2 := hex
  obtain ⟨s, _, h5, s', hleg, _⟩ := hex2
  refine ⟨ProxyUpgradeCurrent.wConfig_frames, wTA_genuine 36 76 (by decide),
    subclass_tame wCode76 (fun c hc => by rw [List.mem_singleton.mp hc]; trivial)
      (fun _ h => absurd h List.not_mem_nil) (wTA_tame 36 76), ?_, hex⟩
  intro hrev
  exact ReviewedEngineRefusesStaleRows wV35 (wTA 36 76) s ProxyUpgradeCurrent.rowA
    ProxyUpgradeCurrent.wConfig_frames hrev
    (by rw [wTA_rows]; exact List.pairwise_singleton _ _)
    (by rw [wTA_rows]; exact List.mem_singleton_self _)
    (by show s.x.impl 5 ≠ 10; rw [h5]; decide) (by show s.x.impl 5 ≠ 11; rw [h5]; decide)
    ⟨s', hleg⟩

/-! ### The `e561b9cc2` premises no longer suffice -/

theorem TameRunsNoLongerPreserveSysInv : Properties.TameRunsNoLongerPreserveSysInv := by
  intro hall
  obtain ⟨hf, hgen, htame, _, _, _, s, s', hrun, _, hleg, _, _, _, _, _, hnI⟩ :=
    CtmSwappingEngineBreaksSysInv
  apply hnI
  refine hall wV35 wV0 s' _ hf wX0_inv (v35run_append hrun (V35Run.cons hleg V35Run.nil)) ?_ ?_
  · intro l hl
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · trivial
    · trivial
    · trivial
    · exact htame
  · intro T hT
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, false_or, V35Label.infra.injEq] at hT
    subst hT; exact hgen

theorem TameRunsNoLongerKeepChainsOnTheirRelease :
    Properties.TameRunsNoLongerKeepChainsOnTheirRelease := by
  intro hall
  obtain ⟨hf, hI, hgen, htame, _, _, s', hrun, _, _, _, c, hc, hpv, hrel, hne⟩ :=
    CuttingEngineBreaksTheHeadline
  apply hne
  have h := hall wV35 wV0 s' _ hf hI hrun htame (fun T hT => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
        V35Label.infra.injEq] at hT
      subst hT; exact hgen) 0 c hc (by rw [hpv, hrel]; decide)
  rw [hpv, hrel] at h
  exact h

theorem FixedEntrypointsNoLongerMoveOnlyAlongRows :
    Properties.FixedEntrypointsNoLongerMoveOnlyAlongRows := by
  intro hall
  obtain ⟨hf, hgen, _, _, _, _, s', hleg, _, _, _, _, _, hnm⟩ :=
    ProxyMovingEngineMovesAnUnnamedProxy
  exact hnm (hall wV35 wV0 s' _ hf hleg (fun _ h => by cases h) (fun T hT => by cases hT; exact hgen))

/-! ### The witness -/

theorem ReviewedRunWitness : Properties.ReviewedRunWitness := by
  have hc : CStep wWorld (initState wWorld 100) (.commit 300) _ :=
    CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨p1, p2⟩ := ExecutorPostcheckPasses _ _ _ _ hc
  have hrun := V35Run.cons (X := wV35) (s := wV0) (l := .infra (wTAB 70))
    (default_leg wCode70 trivial rfl trivial rfl (EngineCore.mk rfl (wApplyAB 70) (fun _ => rfl)))
    (V35Run.cons (V35Step.other (l := .env (.genesis 0)) rfl (XStep.env trivial
        (Step.genesis (id := 0) rfl (addAll_empty_eq xNodup100))))
    (V35Run.cons (V35Step.other (l := .commit 300) rfl (XStep.commit (Step.ctm hc) p1 p2))
    (V35Run.cons (V35Step.other (l := .upgradeChain 0) rfl (XStep.upgradeChain
        (Step.transition (id := 0) rfl (by decide) rfl
          (applyDerived_rows_eq xNodup100 xNodup200) (by decide))))
    (V35Run.cons (subclass_leg (T := wTAB 71) wCode71 trivial rfl trivial rfl FRun.nil
        (EngineCore.mk rfl (wApplyAB_again 71) (fun _ => rfl))
        (FRun.cons (FStep.sys (Step.ctm (CStep.replace (e := 300) (r := 400)
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide)))) FRun.nil)
        (by
          rw [wTAB_rows]; intro r hr
          rcases ProxyUpgradeCurrent.mem_AB hr with rfl | rfl <;> decide))
    V35Run.nil))))
  have hhook : ∀ c ∈ wHookCalls, ReviewedHookCall c := by
    intro c hc
    rw [wHookCalls, List.mem_singleton] at hc
    subst hc
    simp [ReviewedHookCall, Label.isArbitrary]
  have hrev70 : EngineReviewed wV35 (wTAB 70) := DefaultEngineIsReviewed _ _ wCode70
  have hrev71 : EngineReviewed wV35 (wTAB 71) :=
    subclass_reviewed wCode71 (fun _ h => absurd h List.not_mem_nil) hhook
  refine ⟨ProxyUpgradeCurrent.wConfig_frames, wX0_inv, rfl, wCode70, hrev70, hrev71,
    hook_not_default, reviewed_tame hrev70 (wTAB_tame 70), reviewed_tame hrev71 (wTAB_tame 71),
    wTAB_genuine 70 (by decide), wTAB_genuine 71 (by decide), trivial, trivial,
    ⟨_, XStep.infra ⟨trivial, rfl, wApplyAB 70⟩ (fun _ => rfl)⟩, ?_, _, hrun,
    by decide, by decide, by decide, by decide, ⟨_, rfl, by decide, rfl⟩, rfl, rfl, rfl⟩
  intro l hl
  simp only [wReviewedRun, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · exact wTAB_tame 70
  · trivial
  · trivial
  · trivial
  · exact wTAB_tame 71

end Contracts.ChainTypeManager.ExecutorEngineAtV35
