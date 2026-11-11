import EraSpec.Contracts.ChainTypeManager.Properties.ExecutorForward
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainRouting
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsCurrent

/-!
# Proofs: which invariants survive the CTM executor's `forward`

A forwarded CTM call is a `ChainRouting` step, so the invariant results lift through
`step_sysInv`. An infrastructure transition that names no CTM-proxy row leaves the CTM
proxy alone by the row library's frame (`ProxyUpgradeCurrent.UnmovedProxiesFrame`), and a
fixed entry point moves proxies only along row edges by
`ProxyUpgradeCurrent.OnlyNamedEdgesAcrossCall`. The two countermodels are concrete runs.
-/

namespace Contracts.ChainTypeManager

/-! ## One step -/

lemma step_pv_le {W : World} {s s' : Sys} {l : Label} (h : Step W s l s') :
    s.ctm.pv ≤ s'.ctm.pv := by
  cases h with
  | ctm hc => exact (cstep_pv hc).1
  | _ => exact le_rfl

lemma env_not_arbitrary {l : Label} (h : l.isEnv) : ¬ l.isArbitrary := by
  cases l <;> simp_all [Label.isEnv, Label.isArbitrary]

/-- What a tame step keeps: the invariant, the version's lower bound, the CTM's code. -/
def Keeps (X : XConfig) (s s' : XState) : Prop :=
  SysInv X.W s'.sys ∧ s.sys.ctm.pv ≤ s'.sys.ctm.pv ∧ s'.impl X.ctmProxy = s.impl X.ctmProxy

lemma keeps_trans {X : XConfig} {s₁ s₂ s₃ : XState} (h₁ : Keeps X s₁ s₂) (h₂ : Keeps X s₂ s₃) :
    Keeps X s₁ s₃ :=
  ⟨h₂.1, le_trans h₁.2.1 h₂.2.1, h₂.2.2.trans h₁.2.2⟩

lemma sys_step_keeps {X : XConfig} {s : XState} {l : Label} {sys' : Sys}
    (hI : SysInv X.W s.sys) (h : Step X.W s.sys l sys') (hl : ¬ l.isArbitrary) :
    Keeps X s { s with sys := sys' } :=
  ⟨step_sysInv hI h hl, step_pv_le h, rfl⟩

lemma fstep_keeps {X : XConfig} {s s' : XState} {c : FCall} (hI : SysInv X.W s.sys)
    (h : FStep X s c s') (ht : c.Tame) : Keeps X s s' := by
  cases h with
  | sys hs => exact sys_step_keeps hI hs ht
  | upgradeProxy _ _ hp => exact ⟨hI, le_rfl, ProxyUpgradeCurrent.upd_ne _ _ (Ne.symm hp)⟩
  | swapCtm _ _ => exact ht.elim

lemma frun_keeps {X : XConfig} {s s' : XState} {cs : List FCall} (h : FRun X s cs s') :
    SysInv X.W s.sys → (∀ c ∈ cs, c.Tame) → Keeps X s s' := by
  induction h with
  | nil => intro hI _; exact ⟨hI, le_rfl, rfl⟩
  | cons hstep _ ih =>
      intro hI ht
      have h₁ := fstep_keeps hI hstep (ht _ (List.mem_cons_self))
      exact keeps_trans h₁ (ih h₁.1 (fun c hc => ht c (List.mem_cons_of_mem _ hc)))

lemma xstep_keeps {X : XConfig} {s s' : XState} {x : XLabel}
    (hf : ProxyUpgradeCurrent.ReinitFrames X.rc) (hI : SysInv X.W s.sys)
    (h : XStep X s x s') (ht : x.Tame X) : Keeps X s s' := by
  cases h with
  | @infra T J c' happ hc =>
      have ht' : ∀ r ∈ T.rows, r.proxy ≠ X.ctmProxy := ht
      have hJ : J X.ctmProxy = s.impl X.ctmProxy :=
        ProxyUpgradeCurrent.UnmovedProxiesFrame X.rc s.impl J T.rows hf happ.2.2 X.ctmProxy ht'
      have hc' := hc hJ
      subst hc'
      exact ⟨hI, le_rfl, hJ⟩
  | commit hs _ _ | upgradeChain hs => exact sys_step_keeps hI hs (by simp [Label.isArbitrary])
  | forward hr => exact frun_keeps hr hI ht
  | env he hs => exact sys_step_keeps hI hs (env_not_arbitrary he)

lemma xrun_keeps {X : XConfig} {s s' : XState} {xs : List XLabel}
    (hf : ProxyUpgradeCurrent.ReinitFrames X.rc) (h : XRun X s xs s') :
    SysInv X.W s.sys → (∀ x ∈ xs, x.Tame X) → Keeps X s s' := by
  induction h with
  | nil => intro hI _; exact ⟨hI, le_rfl, rfl⟩
  | cons hstep _ ih =>
      intro hI ht
      have h₁ := xstep_keeps hf hI hstep (ht _ (List.mem_cons_self))
      exact keeps_trans h₁ (ih h₁.1 (fun x hx => ht x (List.mem_cons_of_mem _ hx)))

/-! ## Forwarded CTM calls -/

lemma frun_map_sys {X : XConfig} (ls : List Label) :
    ∀ {s s' : XState}, FRun X s (ls.map FCall.sys) s' →
      Run X.W s.sys ls s'.sys ∧ s'.impl = s.impl := by
  induction ls with
  | nil => intro s s' h; cases h; exact ⟨Run.nil, rfl⟩
  | cons l ls ih =>
      intro s s' h
      rw [List.map_cons] at h
      cases h with
      | cons hstep hrest =>
          cases hstep with
          | sys hs =>
              obtain ⟨hr, hi⟩ := ih hrest
              exact ⟨Run.cons hs hr, hi⟩

lemma run_map_sys {X : XConfig} (ls : List Label) :
    ∀ {s : XState} {sys' : Sys}, Run X.W s.sys ls sys' →
      FRun X s (ls.map FCall.sys) { s with sys := sys' } := by
  induction ls with
  | nil => intro s sys' h; cases h; exact FRun.nil
  | cons l ls ih =>
      intro s sys' h
      cases h with
      | cons hs hr =>
          exact FRun.cons (FStep.sys hs) (ih (s := { s with sys := _ }) hr)

end Contracts.ChainTypeManager

/-! ## Certificates -/

namespace Contracts.ChainTypeManager

theorem ForwardOfCtmCallsIsARun : Properties.ForwardOfCtmCallsIsARun :=
  fun _ _ ls => ⟨fun _ h => frun_map_sys ls h, fun _ h => run_map_sys ls h⟩

theorem TameRunPreservesSysInv : Properties.TameRunPreservesSysInv :=
  fun _ _ _ _ hf hI h ht => xrun_keeps hf h hI ht

theorem TameRunKeepsChainsOnTheirRelease : Properties.TameRunKeepsChainsOnTheirRelease := by
  intro X s s' xs hf hI h ht id c hc hrel
  obtain ⟨hC, hch⟩ := (xrun_keeps hf h hI ht).1
  exact ⟨(hC.relAtSound _ hrel).2, (hch id c hc).2 hrel⟩

theorem FixedEntrypointsMoveProxiesOnlyAlongRows :
    Properties.FixedEntrypointsMoveProxiesOnlyAlongRows := by
  intro X s s' x hf h hnf hd
  show ∀ p, _
  intro p
  cases h with
  | @infra T J c' happ _ =>
      rcases ProxyUpgradeCurrent.OnlyNamedEdgesAcrossCall X.rc s.impl J T.rows (hd T rfl) hf
          happ.2.2 p with h1 | ⟨r, hr, hp, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨T, r, rfl, hr, hp, h2, h3⟩
  | forward _ => exact absurd rfl (hnf _)
  | _ => exact Or.inl rfl

end Contracts.ChainTypeManager

/-! ## Countermodels and the witness -/

namespace Contracts.ChainTypeManager

lemma xNodup100 : ((wWorld.relRows 100).map Prod.fst).Nodup := by decide
lemma xNodup200 : ((wWorld.relRows 200).map Prod.fst).Nodup := by decide

lemma wX0_inv : SysInv wX.W wX0.sys := FreshSystemSatisfiesInvariant wWorld 100 (by decide)

/-- The state the witness transition reaches, as a term. -/
abbrev wJ : ProxyUpgradeCurrent.Impl :=
  ProxyUpgradeCurrent.swap ProxyUpgradeCurrent.wConfig ProxyUpgradeCurrent.rowB
    (ProxyUpgradeCurrent.swap ProxyUpgradeCurrent.wConfig ProxyUpgradeCurrent.rowA ProxyUpgradeCurrent.wImpl)

lemma wInfra_apply : ProxyUpgradeCurrent.ApplyTransition wX.rc .ctm wInfra ProxyUpgradeCurrent.wImpl wJ :=
  ⟨trivial, rfl, ProxyUpgradeCurrent.applyRows_AB⟩

lemma wInfra_distinct : wInfra.rows.Pairwise (fun a b => a.proxy ≠ b.proxy) :=
  ProxyUpgradeCurrent.valid_AB.distinctProxies

theorem ForwardDowngradesAProxy : Properties.ForwardDowngradesAProxy := by
  have h5 : wJ 5 = 11 := by decide
  have hinfra : XStep wX wX0 (.infra wInfra) ⟨{ wX0.sys with ctm := wX0.sys.ctm }, wJ⟩ :=
    XStep.infra wInfra_apply (fun _ => rfl)
  refine ⟨ProxyUpgradeCurrent.wConfig_frames, wInfra_distinct, _, _,
    XRun.cons hinfra XRun.nil,
    XStep.forward (FRun.cons (FStep.upgradeProxy rfl trivial (by decide)) FRun.nil),
    ?_, h5, ProxyUpgradeCurrent.upd_same wJ 5 10, ?_⟩
  · intro c hc
    rw [List.mem_singleton.mp hc]
    trivial
  · intro hm
    rcases hm 5 with h | ⟨T, r, hx, _⟩
    · have h' : ProxyUpgradeCurrent.upd wJ 5 10 5 = wJ 5 := h
      rw [ProxyUpgradeCurrent.upd_same, h5] at h'
      exact absurd h' (by decide)
    · cases hx

theorem ForwardCtmSwapBreaksInvariants : Properties.ForwardCtmSwapBreaksInvariants := by
  have hc : CStep wWorld (initState wWorld 100) (.commit 300) _ :=
    CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨p1, p2⟩ := ExecutorPostcheckPasses _ _ _ _ hc
  have hrun := XRun.cons (X := wX) (s := wX0)
    (XStep.env (l := .genesis 0) trivial (Step.genesis (id := 0) rfl (addAll_empty_eq xNodup100)))
    (XRun.cons (XStep.commit (Step.ctm hc) p1 p2)
      (XRun.cons (XStep.upgradeChain (Step.transition (id := 0) rfl (by decide) rfl
          (applyDerived_rows_eq xNodup100 xNodup200) (by decide))) XRun.nil))
  have htame : ∀ x ∈ [XLabel.env (.genesis 0), .commit 300, .upgradeChain 0], x.Tame wX := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> trivial
  refine ⟨wX0_inv, _, _, hrun, htame,
    (xrun_keeps (X := wX) ProxyUpgradeCurrent.wConfig_frames hrun wX0_inv htame).1,
    XStep.forward (FRun.cons (FStep.swapCtm (c' := initState wWorld 100) rfl trivial) FRun.nil),
    fun h => h _ (List.mem_singleton_self _), by decide, ?_⟩
  intro hI
  exact absurd (hI.2 0 _ rfl).1 (by decide)

theorem ExecutorWitness : Properties.ExecutorWitness := by
  have hinfra : XStep wX wX0 (.infra wInfra) ⟨{ wX0.sys with ctm := wX0.sys.ctm }, wJ⟩ :=
    XStep.infra wInfra_apply (fun _ => rfl)
  have hc : CStep wWorld (initState wWorld 100) (.commit 300) _ :=
    CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨p1, p2⟩ := ExecutorPostcheckPasses _ _ _ _ hc
  have hrun := XRun.cons hinfra
    (XRun.cons (XStep.env (l := .genesis 0) trivial
        (Step.genesis (id := 0) rfl (addAll_empty_eq xNodup100)))
    (XRun.cons (XStep.commit (Step.ctm hc) p1 p2)
      (XRun.cons (XStep.upgradeChain (Step.transition (id := 0) rfl (by decide) rfl
          (applyDerived_rows_eq xNodup100 xNodup200) (by decide)))
        (XRun.cons (XStep.forward
            (FRun.cons (FStep.sys (Step.ctm (CStep.replace (e := 300) (r := 400)
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide))))
              (FRun.cons (FStep.upgradeProxy (p := 7) (x := 42) rfl trivial (by decide))
                FRun.nil)))
          XRun.nil))))
  refine ⟨ProxyUpgradeCurrent.wConfig_frames, wX0_inv, wInfra_distinct, ?_, _, hrun,
    ?_, ?_, by decide, by decide, by decide, by decide, _, rfl, by decide⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · intro r hr
      rcases ProxyUpgradeCurrent.mem_AB hr with rfl | rfl <;> decide
    · trivial
    · trivial
    · trivial
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · simp [FCall.Tame, Label.isArbitrary]
      · trivial
  · decide
  · decide

end Contracts.ChainTypeManager
