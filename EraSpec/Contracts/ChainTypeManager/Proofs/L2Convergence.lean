import EraSpec.Contracts.ChainTypeManager.Properties.L2Convergence
import EraSpec.Contracts.ChainTypeManager.Proofs.VersionRegistry
import EraSpec.Contracts.ChainTypeManager.Proofs.L2Derivation

/-!
# Proofs: the L2 implementations of the chains on a `ChainTypeManager`

One invariant, `L2Inv`, carries the headline. The CTM half is `VersionRegistry`'s `CtmInv`
(`step_inv`), which gives, for a committed slot `v`, that its transition departs from `R_v` and
lands on `R_w`. The chain half is the step lemma `l2step_inv`: a crossing applies exactly the
deployments `ctm_derived` describes (`applyPlan_genuine`), which leave the proxies of unchanged
rows alone and point those of new or changed rows at the target rows; an unchanged row is
keccak-equal, so it is equal or the step names a clash. The run lemma `l2run_inv` threads the
disjunction. Witnesses are concrete runs over `cvWorld` and `fzWorld`, checked by `decide`.
-/

namespace Contracts.ChainTypeManager.L2Tables

/-! ## Applying deployments -/

lemma applyProxies_cons (d : ProxyDeployment) (ds : List ProxyDeployment) (σ : L2State) :
    applyProxies (d :: ds) σ = applyProxies ds (applyProxy σ d) := rfl

lemma applyProxies_frame {ds : List ProxyDeployment} {σ : L2State} {a : L2Addr}
    (h : a ∉ ds.map ProxyDeployment.addr) : applyProxies ds σ a = σ a := by
  induction ds generalizing σ with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [applyProxies_cons, ih h.2]
    simp [applyProxy, h.1]

/-- With pairwise distinct addresses, each deployment's address ends pointing at its row,
behind the shell already there or, if none, its own. -/
lemma applyProxies_hit {ds : List ProxyDeployment} {σ : L2State} {d : ProxyDeployment}
    (hnd : (ds.map ProxyDeployment.addr).Nodup) (hd : d ∈ ds) :
    applyProxies ds σ d.addr = some ((σ d.addr).elim d.shell Prod.fst, d.impl) := by
  induction ds generalizing σ with
  | nil => simp at hd
  | cons d0 ds ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [applyProxies_cons]
    rcases List.mem_cons.1 hd with rfl | hd'
    · rw [applyProxies_frame hnd.1]
      simp [applyProxy]
    · have hne : d.addr ≠ d0.addr := fun h => hnd.1 (h ▸ List.mem_map_of_mem hd')
      rw [ih hnd.2 hd']
      simp [applyProxy, hne]

lemma mem_filterMap_proxyPart {deps : List Deployment} {d : ProxyDeployment} :
    d ∈ deps.filterMap Deployment.proxyPart ↔ Deployment.proxy d ∈ deps := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hpx⟩
    cases x with
    | proxy d' =>
        simp only [Deployment.proxyPart, Option.some.injEq] at hpx
        subst hpx
        exact hx
    | unsafeForce _ _ => simp [Deployment.proxyPart] at hpx
  · intro hd
    exact ⟨_, hd, rfl⟩

/-- **What an L2-genuine plan does to the proxies.** At the fixed address of a new or changed
row, the proxy points at the target row; everywhere else nothing changes. -/
lemma applyPlan_genuine {H : Type} [DecidableEq H] {kec : Bytes → H} {rnd : Bytes → L2Addr}
    {vFrom vNew : ℕ} {Rf Rn : ReleaseL2} {e : EdgeInput} {p : L2Plan}
    (h : ctmTransitionL2 kec rnd vFrom vNew Rf Rn e = some p) (σ : L2State) (a : L2Addr) :
    (∀ i, fixedAddress i = some a → RowChanged kec Rf.table Rn.table i →
      applyPlan p σ a = some ((σ a).elim Rn.shell Prod.fst, rowAt Rn.table i)) ∧
    ((¬ ∃ i, fixedAddress i = some a ∧ RowChanged kec Rf.table Rn.table i) →
      applyPlan p σ a = σ a) := by
  obtain ⟨hmem, hnd, _⟩ := ctm_derived h
  unfold applyPlan
  constructor
  · intro i hi hch
    have hd : (⟨a, rowAt Rn.table i, Rn.shell⟩ : ProxyDeployment) ∈
        p.deployments.filterMap Deployment.proxyPart :=
      mem_filterMap_proxyPart.2 ((hmem _).2 ⟨i, a, hi, hch, rfl⟩)
    exact applyProxies_hit hnd hd
  · intro hno
    apply applyProxies_frame
    intro ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ha
    obtain ⟨i, a', hi, hch, rfl⟩ := (hmem d).1 (mem_filterMap_proxyPart.1 hd)
    exact hno ⟨i, hi, hch⟩

/-- A whole-table install puts the release's shell over each nonempty row. -/
lemma fullInstall_holds (R : ReleaseL2) {i : ℕ} {a : L2Addr} (hfix : fixedAddress i = some a)
    (hrow : rowAt R.table i ≠ []) : fullInstall R a = some (R.shell, rowAt R.table i) := by
  have hd : (⟨a, rowAt R.table i, R.shell⟩ : ProxyDeployment) ∈ deriveOut R.table R.shell :=
    mem_deriveOut.2 ⟨i, a, hrow, hfix, rfl⟩
  exact applyProxies_hit deriveOut_addrs_nodup hd

/-- A world whose genesis images are whole-table installs meets `GenesisImageHolds` everywhere. -/
lemma genesisImageHolds_of_fullInstall {W : L2World} {R : Address}
    (h : W.image R = fullInstall (W.rel R)) : GenesisImageHolds W R := by
  intro i a hfix hrow
  rw [h]
  exact fullInstall_holds _ hfix hrow

lemma runs_of_image {W : L2World} {R : Address} (h : GenesisImageHolds W R) :
    RunsReleaseL2 W R (W.image R) :=
  fun i a hfix hrow => ⟨_, h i a hfix hrow⟩

/-- With an injective hash there is no clash. -/
lemma not_crossClash_id (W : L2World) (t : Address) : ¬ CrossClash (fun x : Bytes => x) W t :=
  fun ⟨_, hne, heq⟩ => hne heq

/-! ## The chains -/

@[simp] lemma setChain_ctm (s : L2Sys) (cid : ChainId) (c : L2Chain) :
    (s.setChain cid c).ctm = s.ctm := rfl

@[simp] lemma setChain_chains (s : L2Sys) (cid : ChainId) (c : L2Chain) :
    (s.setChain cid c).chains = upd s.chains cid (some c) := rfl

lemma upd_chain_some {f : ChainId → Option L2Chain} {cid cid' : ChainId} {x y : L2Chain}
    (h : upd f cid (some x) cid' = some y) :
    (cid' = cid ∧ y = x) ∨ (cid' ≠ cid ∧ f cid' = some y) := by
  by_cases hid : cid' = cid
  · subst hid; simp at h; exact Or.inl ⟨rfl, h.symm⟩
  · rw [upd_ne _ _ hid] at h; exact Or.inr ⟨hid, h⟩

lemma l2step_ctm {W : L2World} {s s' : L2Sys} {l : L2Label} (h : L2Step W s l s') :
    (∃ op, l = .ctm op ∧ CStep W.base s.ctm op s'.ctm) ∨ s'.ctm = s.ctm := by
  cases h with
  | ctm hc => exact Or.inl ⟨_, rfl, hc⟩
  | genesis _ => exact Or.inr rfl
  | cross _ _ _ _ => exact Or.inr rfl
  | bootstrapCross _ _ _ _ => exact Or.inr rfl
  | breakGlass _ _ _ => exact Or.inr rfl

lemma l2step_pv {W : L2World} {s s' : L2Sys} {l : L2Label} (h : L2Step W s l s') :
    s.ctm.pv ≤ s'.ctm.pv := by
  rcases l2step_ctm h with ⟨op, _, hc⟩ | heq
  · exact (cstep_pv hc).1
  · rw [heq]

lemma l2step_relAt_low {W : L2World} {s s' : L2Sys} {l : L2Label} (h : L2Step W s l s') :
    ∀ w, w ≤ s.ctm.pv → s'.ctm.relAt w = s.ctm.relAt w := by
  rcases l2step_ctm h with ⟨op, _, hc⟩ | heq
  · exact cstep_relAt_low hc
  · intro w _; rw [heq]

lemma l2run_relAt_low {W : L2World} {s s' : L2Sys} {ls : List L2Label} (h : L2Run W s ls s') :
    ∀ w, w ≤ s.ctm.pv → s'.ctm.relAt w = s.ctm.relAt w := by
  induction h with
  | nil => intro w _; rfl
  | cons hs _ ih =>
    intro w hw
    rw [ih w (le_trans hw (l2step_pv hs)), l2step_relAt_low hs w hw]

/-! ## The invariant -/

theorem l2step_inv {H : Type} [DecidableEq H] {kec : Bytes → H} {rnd : Bytes → L2Addr}
    {W : L2World} {s s' : L2Sys} {l : L2Label}
    (hI : L2Inv W s) (h : L2Step W s l s') (hbg : ¬ l.IsBreakGlass) (hex : l.L2Executed)
    (hgen : ∀ cid t b, l = .cross cid t b → L2Genuine kec rnd W t)
    (himg : ∀ cid, l = .genesis cid → GenesisImageHolds W s.ctm.cur) :
    L2Inv W s' ∨ ∃ cid t, l = .cross cid t true ∧ CrossClash kec W t := by
  obtain ⟨hC, hch⟩ := hI
  cases h with
  | @ctm op c' hc =>
    left
    refine ⟨step_inv hC hc, fun cid c hcid => ?_⟩
    obtain ⟨hle, hrun⟩ := hch cid c hcid
    refine ⟨le_trans hle (cstep_pv hc).1, ?_⟩
    rw [cstep_relAt_low hc c.pv hle]
    exact hrun
  | @genesis cid hfree =>
    left
    refine ⟨hC, fun cid' c hcid => ?_⟩
    simp only [setChain_chains, setChain_ctm] at hcid ⊢
    rcases upd_chain_some hcid with ⟨_, rfl⟩ | ⟨_, h'⟩
    · refine ⟨le_rfl, fun _ => ?_⟩
      rw [hC.curAtVersion]
      exact runs_of_image (himg cid rfl)
    · exact hch cid' c h'
  | @cross cid c t b hc hut ht0 hlt =>
    simp only [L2Label.L2Executed] at hex
    subst hex
    obtain ⟨_, e, hcon⟩ := hgen cid t true rfl
    have hslot : s.ctm.ut c.pv ≠ 0 := by rw [hut]; exact ht0
    obtain ⟨_, hfrom, hrv, _, hnew, hrw⟩ := hC.slots c.pv hslot
    rw [hut] at hfrom hnew hrw
    have hwle := (hC.relAtSound _ hrw).1
    by_cases hcl : CrossClash kec W t
    · exact Or.inr ⟨cid, t, rfl, hcl⟩
    · left
      refine ⟨hC, fun cid' c' hcid => ?_⟩
      simp only [setChain_chains, setChain_ctm] at hcid ⊢
      rcases upd_chain_some hcid with ⟨_, rfl⟩ | ⟨_, h'⟩
      · refine ⟨hwle, fun _ => ?_⟩
        simp only [↓reduceIte]
        intro i a hfix hrow
        rw [← hnew] at hrow ⊢
        have hgp := applyPlan_genuine hcon c.l2 a
        by_cases hchg : RowChanged kec (W.rel (W.base.tr t).fromRel).table
            (W.rel (W.base.tr t).newRel).table i
        · exact ⟨_, hgp.1 i hfix hchg⟩
        · have hno : ¬ ∃ j, fixedAddress j = some a ∧ RowChanged kec
              (W.rel (W.base.tr t).fromRel).table (W.rel (W.base.tr t).newRel).table j := by
            rintro ⟨j, hj, hchj⟩
            rw [fixedAddress_inj hj hfix] at hchj
            exact hchg hchj
          rw [hgp.2 hno]
          simp only [RowChanged, not_and, not_or, ne_eq, not_not] at hchg
          obtain ⟨_, heq⟩ := hchg hrow
          have hrows : rowAt (W.rel (W.base.tr t).fromRel).table i =
              rowAt (W.rel (W.base.tr t).newRel).table i := by
            by_contra hne
            exact hcl ⟨i, hne, heq⟩
          rw [← hrows]
          rw [← hrows] at hrow
          rw [hfrom] at hrow ⊢
          exact (hch cid c hc).2 hrv i a hfix hrow
      · exact hch cid' c' h'
  | @bootstrapCross cid c R ds b hc hleg hlt hder =>
    simp only [L2Label.L2Executed] at hex
    subst hex
    left
    obtain ⟨_, hrel, _⟩ := hC.bootstraps c.pv R hleg
    have hR0 : s.ctm.relAt (W.base.relVersion R) ≠ 0 := by rw [hrel]; exact (hC.bootstraps c.pv R hleg).2.2
    have hwle := (hC.relAtSound _ hR0).1
    obtain ⟨_, rfl⟩ := derive_some.1 hder
    refine ⟨hC, fun cid' c' hcid => ?_⟩
    simp only [setChain_chains, setChain_ctm] at hcid ⊢
    rcases upd_chain_some hcid with ⟨_, rfl⟩ | ⟨_, h'⟩
    · refine ⟨hwle, fun _ => ?_⟩
      simp only [↓reduceIte]
      rw [hrel]
      intro i a hfix hrow
      have hd : (⟨a, rowAt (W.rel R).table i, (W.rel R).shell⟩ : ProxyDeployment) ∈
          deriveOut (W.rel R).table (W.rel R).shell := mem_deriveOut.2 ⟨i, a, hrow, hfix, rfl⟩
      exact ⟨_, applyProxies_hit deriveOut_addrs_nodup hd⟩
    · exact hch cid' c' h'
  | breakGlass _ _ _ => exact absurd trivial hbg

theorem l2run_inv {H : Type} [DecidableEq H] {kec : Bytes → H} {rnd : Bytes → L2Addr}
    {W : L2World} {s s' : L2Sys} {ls : List L2Label} (h : L2Run W s ls s') :
    L2Inv W s → (∀ l ∈ ls, ¬ l.IsBreakGlass) → (∀ l ∈ ls, l.L2Executed) →
    (∀ cid t b, L2Label.cross cid t b ∈ ls → L2Genuine kec rnd W t) →
    (∀ v, s'.ctm.relAt v ≠ 0 → GenesisImageHolds W (s'.ctm.relAt v)) →
    L2Inv W s' ∨ ∃ cid t, L2Label.cross cid t true ∈ ls ∧ CrossClash kec W t := by
  induction h with
  | nil => intro hI _ _ _ _; exact Or.inl hI
  | @cons s s1 s2 l ls hs hrest ih =>
    intro hI hbg hex hgen himg
    have himg_s : ∀ cid, l = .genesis cid → GenesisImageHolds W s.ctm.cur := by
      intro _ _
      have hlow := l2run_relAt_low (L2Run.cons hs hrest) s.ctm.pv le_rfl
      have hne : s2.ctm.relAt s.ctm.pv ≠ 0 := by
        rw [hlow, hI.1.curAtVersion]; exact hI.1.curNonzero
      have := himg _ hne
      rwa [hlow, hI.1.curAtVersion] at this
    rcases l2step_inv hI hs (hbg l List.mem_cons_self) (hex l List.mem_cons_self)
        (fun cid t b he => hgen cid t b (by rw [← he]; exact List.mem_cons_self)) himg_s with
      hI1 | ⟨cid, t, hl, hcl⟩
    · rcases ih hI1 (fun l hl => hbg l (List.mem_cons_of_mem _ hl))
          (fun l hl => hex l (List.mem_cons_of_mem _ hl))
          (fun cid t b hm => hgen cid t b (List.mem_cons_of_mem _ hm)) himg with
        h' | ⟨cid, t, hm, hcl⟩
      · exact Or.inl h'
      · exact Or.inr ⟨cid, t, List.mem_cons_of_mem _ hm, hcl⟩
    · subst hl
      exact Or.inr ⟨cid, t, List.mem_cons_self, hcl⟩

/-! ## Starting states -/

theorem FreshL2SysSatisfiesInvariant : Properties.FreshL2SysSatisfiesInvariant := by
  intro W R hR
  exact ⟨InitSatisfiesInvariant W.base R hR, fun _ _ h => by simp [freshL2Sys] at h⟩

theorem BootstrapL2SysSatisfiesInvariant : Properties.BootstrapL2SysSatisfiesInvariant := by
  intro W old R pre hR hlt hpre
  refine ⟨BootstrapSatisfiesInvariant W.base old R hR hlt, fun cid c h => ?_⟩
  have hle := hpre cid c h
  refine ⟨by simp only [bootstrapL2Sys, bootstrapState]; omega, fun hne => ?_⟩
  exfalso
  apply hne
  simp only [bootstrapL2Sys, bootstrapState]
  rw [upd_ne _ _ (by omega)]

/-! ## One crossing -/

theorem CrossingWritesExactlyTheChangedRows :
    Properties.CrossingWritesExactlyTheChangedRows := by
  intro H _ kec rnd W s s' cid t hgen h
  cases h with
  | @cross _ c _ _ hc _ _ _ =>
    obtain ⟨_, e, hcon⟩ := hgen
    refine ⟨c, ⟨(W.base.tr t).new, applyPlan (W.plan t) c.l2⟩, hc, ?_, rfl, fun a => ⟨?_, ?_⟩, ?_⟩
    · simp [L2Sys.setChain]
    · intro i hfix hch
      show (applyPlan (W.plan t) c.l2 a).map Prod.snd = _
      rw [(applyPlan_genuine hcon c.l2 a).1 i hfix hch]
      rfl
    · intro hno
      exact (applyPlan_genuine hcon c.l2 a).2 hno
    · intro cid' hne
      simp [L2Sys.setChain, upd_ne _ _ hne]

/-! ## Convergence -/

theorem L2StepPreservesInvariant : Properties.L2StepPreservesInvariant := by
  intro H _ kec rnd W s s' l hI h hbg hex hgen himg
  exact l2step_inv hI h hbg hex hgen himg

theorem ChainsRunTheirVersionsL2Rows : Properties.ChainsRunTheirVersionsL2Rows := by
  intro H _ kec rnd W s s' ls hI h hbg hex hgen himg
  rcases l2run_inv h hI hbg hex hgen himg with hI' | hcl
  · exact Or.inl fun cid c hc hne => (hI'.2 cid c hc).2 hne
  · exact Or.inr hcl

theorem ChainsOnOneVersionRunOneL2 : Properties.ChainsOnOneVersionRunOneL2 := by
  intro H _ kec rnd W s s' ls hI h hbg hex hgen himg
  rcases ChainsRunTheirVersionsL2Rows kec rnd W s s' ls hI h hbg hex hgen himg with hrun | hcl
  · left
    intro cid₁ cid₂ c₁ c₂ i a h₁ h₂ hpv hne hfix hrow
    obtain ⟨sh₁, hs₁⟩ := hrun cid₁ c₁ h₁ hne i a hfix hrow
    rw [hpv] at hne hrow
    obtain ⟨sh₂, hs₂⟩ := hrun cid₂ c₂ h₂ hne i a hfix hrow
    rw [hs₁, hs₂, hpv]
    simp
  · exact Or.inr hcl

/-! ## Rows along CTM runs -/

theorem NonemptyRowsStayNonemptyAlongRegistryRuns :
    Properties.NonemptyRowsStayNonemptyAlongRegistryRuns := by
  intro H _ kec rnd W c c' ops h
  induction h with
  | nil => intro _ _ i hrow; exact hrow
  | @cons c c1 c2 op ops hs hrest ih =>
    intro hleg hgen i hrow
    have hstep : rowAt (W.rel c1.cur).table i ≠ [] := by
      cases hs with
      | @commit t _ hfrom _ _ _ _ =>
        obtain ⟨_, e, hcon⟩ := hgen t List.mem_cons_self
        rw [hfrom] at hcon
        exact NonemptyRowStaysNonempty kec rnd _ _ _ _ e _ hcon i hrow
      | replace _ _ _ _ _ _ _ _ => exact hrow
      | @legacyCommit R b _ _ => exact absurd List.mem_cons_self (hleg R b)
      | legacyRecut _ _ => exact hrow
    exact ih (fun R b hm => hleg R b (List.mem_cons_of_mem _ hm))
      (fun t hm => hgen t (List.mem_cons_of_mem _ hm)) i hstep

theorem NoFixedAddressRowFrozenAlongRegistryRuns :
    Properties.NoFixedAddressRowFrozenAlongRegistryRuns := by
  intro H _ kec rnd W c c' ops h
  induction h with
  | nil =>
    intro _ _ i _ hrow
    exact ⟨hrow, rfl, Or.inl rfl⟩
  | @cons c c1 c2 op ops hs hrest ih =>
    intro hleg hgen i hfix hrow
    -- the step: the current release's row keeps its hash
    have hstep : rowAt (W.rel c1.cur).table i ≠ [] ∧
        kec (rowAt (W.rel c1.cur).table i) = kec (rowAt (W.rel c.cur).table i) ∧
        (rowAt (W.rel c1.cur).table i = rowAt (W.rel c.cur).table i ∨
          ∃ t, Op.commit t ∈ op :: ops ∧ CrossClash kec W t) := by
      cases hs with
      | @commit t _ hfrom _ _ _ _ =>
        obtain ⟨_, e, hcon⟩ := hgen t List.mem_cons_self
        rw [hfrom] at hcon
        obtain ⟨hn, hor⟩ := NoFixedAddressRowIsFrozen kec rnd _ _ _ _ e _ hcon i hfix hrow
        refine ⟨hn, ?_, ?_⟩
        · rcases hor with heq | ⟨_, heq⟩
          · simp only at heq ⊢; rw [heq]
          · exact heq.symm
        · rcases hor with heq | hcl
          · exact Or.inl heq
          · right
            refine ⟨t, List.mem_cons_self, i, ?_⟩
            rw [hfrom]
            exact hcl
      | replace _ _ _ _ _ _ _ _ => exact ⟨hrow, rfl, Or.inl rfl⟩
      | @legacyCommit R b _ _ => exact absurd List.mem_cons_self (hleg R b)
      | legacyRecut _ _ => exact ⟨hrow, rfl, Or.inl rfl⟩
    obtain ⟨hn1, hk1, he1⟩ := hstep
    obtain ⟨hn2, hk2, he2⟩ := ih (fun R b hm => hleg R b (List.mem_cons_of_mem _ hm))
      (fun t hm => hgen t (List.mem_cons_of_mem _ hm)) i hfix hn1
    refine ⟨hn2, hk2.trans hk1, ?_⟩
    rcases he2 with h2 | ⟨t, hm, hcl⟩
    · rcases he1 with h1 | hcl
      · exact Or.inl (h2.trans h1)
      · exact Or.inr hcl
    · exact Or.inr ⟨t, List.mem_cons_of_mem _ hm, hcl⟩

end Contracts.ChainTypeManager.L2Tables

/-! ## Witnesses -/

namespace Contracts.ChainTypeManager.L2Tables

/-- The witness world's transitions `300`, `600`, `700` are L2-genuine. -/
lemma cv_genuine {t : Address} (ht : t = 300 ∨ t = 600 ∨ t = 700) :
    L2Genuine (fun x : Bytes => x) wRnd cvWorld t := by
  rcases ht with rfl | rfl | rfl
  · exact ⟨⟨by decide, by decide⟩, wMinorEdge, by decide⟩
  · exact ⟨⟨by decide, by decide⟩, wMinorEdge, by decide⟩
  · exact ⟨⟨by decide, by decide⟩, wMinorEdge, by decide⟩

/-- The witness run, step by step. -/
lemma cv_run : ∃ s', L2Run cvWorld cvSys0 cvLabels s' ∧
    s'.ctm.ut (cvV 1) = 700 ∧
    ∃ c₀ c₁ c₂, s'.chains 0 = some c₀ ∧ s'.chains 1 = some c₁ ∧ s'.chains 2 = some c₂ ∧
      c₀.pv = cvV 3 ∧ c₁.pv = cvV 3 ∧ c₂.pv = cvV 3 ∧
      (∀ a ∈ ([0x10002, 0x10003, 0x10004] : List L2Addr),
        (c₀.l2 a).map Prod.snd = (c₁.l2 a).map Prod.snd ∧
        (c₁.l2 a).map Prod.snd = (c₂.l2 a).map Prod.snd ∧ (c₀.l2 a).isSome = true) ∧
      (c₀.l2 0x10002).map Prod.snd = (c₂.l2 0x10002).map Prod.snd ∧
      (c₀.l2 0x10002).map Prod.fst = some (cvRel 100).shell ∧
      (c₂.l2 0x10002).map Prod.fst = some (cvRel 250).shell := by
  have hrun := L2Run.cons (W := cvWorld) (L2Step.genesis (s := cvSys0) (id := 0) rfl)
    (L2Run.cons (L2Step.genesis (id := 1) rfl)
    (L2Run.cons (L2Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)))
    (L2Run.cons (L2Step.cross (id := 0) (t := 300) (b := true) rfl (by decide) (by decide)
        (by decide))
    (L2Run.cons (L2Step.ctm (CStep.commit (t := 600) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)))
    (L2Run.cons (L2Step.cross (id := 0) (t := 600) (b := true) rfl (by decide) (by decide)
        (by decide))
    (L2Run.cons (L2Step.ctm (CStep.replace (e := 300) (r := 700) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
    (L2Run.cons (L2Step.cross (id := 1) (t := 700) (b := true) rfl (by decide) (by decide)
        (by decide))
    (L2Run.cons (L2Step.genesis (id := 2) rfl) L2Run.nil))))))))
  exact ⟨_, hrun, by decide, _, _, _, rfl, rfl, rfl, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

/-- A chain whose proxy at a fixed member's address does not point at the release's row does
not run the release. -/
lemma not_runs_of {W : L2World} {R : Address} {σ : L2State} (i : ℕ) (a : L2Addr)
    (hfix : fixedAddress i = some a) (hrow : rowAt (W.rel R).table i ≠ [])
    (hdiff : (σ a).map Prod.snd ≠ some (rowAt (W.rel R).table i)) : ¬ RunsReleaseL2 W R σ := by
  intro h
  obtain ⟨sh, hsh⟩ := h i a hfix hrow
  rw [hsh] at hdiff
  exact hdiff rfl

theorem L2ConvergenceWitness : Properties.L2ConvergenceWitness := by
  obtain ⟨s', hrun, hut, c₀, c₁, c₂, h₀, h₁, h₂, p₀, p₁, p₂, hagree, _, _, _⟩ := cv_run
  refine ⟨s', hrun, FreshL2SysSatisfiesInvariant cvWorld 100 (by decide), by decide, by decide, ?_,
    fun v _ => genesisImageHolds_of_fullInstall rfl, ?_, hut, by decide, c₀, c₁, c₂, h₀, h₁, h₂,
    p₀, p₁, p₂, hagree⟩
  · intro cid t b hm
    apply cv_genuine
    simp only [cvLabels, List.mem_cons, reduceCtorEq, L2Label.cross.injEq, List.not_mem_nil,
      false_or, or_false] at hm
    rcases hm with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩

theorem BootstrapConvergenceWitness : Properties.BootstrapConvergenceWitness := by
  have hpre : ∀ cid c, cvPre cid = some c → c.pv ≤ 0 := by
    intro cid c h
    rcases upd_chain_some h with ⟨_, rfl⟩ | ⟨_, h'⟩
    · exact le_rfl
    · simp at h'
  have hI := BootstrapL2SysSatisfiesInvariant cvWorld 0 100 cvPre (by decide) (by decide) hpre
  have hgen := cv_genuine (Or.inl rfl)
  have hrun := L2Run.cons (W := cvWorld)
    (L2Step.bootstrapCross (s := bootstrapL2Sys cvWorld 0 100 cvPre) (id := 5) (R := 100)
      (ds := deriveOut (cvWorld.rel 100).table (cvWorld.rel 100).shell)
      (b := true) rfl (by decide) (by decide) (by decide))
    (L2Run.cons (L2Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)))
    (L2Run.cons (L2Step.cross (id := 5) (t := 300) (b := true) rfl (by decide) (by decide)
        (by decide)) L2Run.nil))
  have himg : ∀ R, GenesisImageHolds cvWorld R := fun _ => genesisImageHolds_of_fullInstall rfl
  refine ⟨_, hrun, by decide, by decide, hpre, hI, hgen, fun _ _ => himg _, _, rfl, by decide,
    by decide, ?_, by decide⟩
  rcases ChainsRunTheirVersionsL2Rows (fun x : Bytes => x) wRnd cvWorld _ _ _ hI hrun
      (by decide) (by decide)
      (fun cid t b hm => by
        simp only [List.mem_cons, reduceCtorEq, L2Label.cross.injEq, List.not_mem_nil,
          false_or, or_false] at hm
        obtain ⟨_, rfl, _⟩ := hm
        exact hgen) (fun _ _ => himg _) with h | ⟨_, t, _, hcl⟩
  · exact h 5 _ rfl (by decide)
  · exact absurd hcl (not_crossClash_id _ _)

theorem ShellsDoNotConverge : Properties.ShellsDoNotConverge := by
  obtain ⟨s', hrun, _, c₀, _, c₂, h₀, _, h₂, p₀, _, p₂, _, hsnd, hf₀, hf₂⟩ := cv_run
  exact ⟨s', hrun, c₀, c₂, h₀, h₂, by rw [p₀, p₂], hsnd, hf₀, hf₂, by decide⟩

theorem UnexecutedL2TxLeavesTheOldRow : Properties.UnexecutedL2TxLeavesTheOldRow := by
  have hrun := L2Run.cons (W := cvWorld) (L2Step.genesis (s := cvSys0) (id := 0) rfl)
    (L2Run.cons (L2Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)))
    (L2Run.cons (L2Step.cross (id := 0) (t := 300) (b := false) rfl (by decide) (by decide)
        (by decide)) L2Run.nil))
  exact ⟨_, hrun, FreshL2SysSatisfiesInvariant cvWorld 100 (by decide), cv_genuine (Or.inl rfl),
    fun v _ => genesisImageHolds_of_fullInstall rfl, not_crossClash_id cvWorld, _, rfl, by decide,
    not_runs_of 0 0x10002 rfl (by decide) (by decide)⟩

theorem NonGenuinePlanLeavesTheOldRow : Properties.NonGenuinePlanLeavesTheOldRow := by
  have hrun := L2Run.cons (W := cvWorldStalePlan)
    (L2Step.genesis (s := freshL2Sys cvWorldStalePlan 100) (id := 0) rfl)
    (L2Run.cons (L2Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)))
    (L2Run.cons (L2Step.cross (id := 0) (t := 300) (b := true) rfl (by decide) (by decide)
        (by decide)) L2Run.nil))
  refine ⟨_, hrun, FreshL2SysSatisfiesInvariant _ 100 (by decide), ⟨by decide, by decide⟩, ?_,
    fun v _ => genesisImageHolds_of_fullInstall rfl, not_crossClash_id _, _, rfl, by decide,
    not_runs_of 0 0x10002 rfl (by decide) (by decide)⟩
  rintro ⟨_, e, he⟩
  have hd := ((ctm_derived he).1 ⟨0x10002, wDesc 3, wDesc 50⟩).2
    ⟨0, 0x10002, rfl, by decide, by decide⟩
  revert hd
  decide

theorem StaleGenesisImageSplitsAVersion : Properties.StaleGenesisImageSplitsAVersion := by
  have hrun := L2Run.cons (W := cvWorldStaleImage)
    (L2Step.genesis (s := freshL2Sys cvWorldStaleImage 100) (id := 0) rfl)
    (L2Run.cons (L2Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)))
    (L2Run.cons (L2Step.cross (id := 0) (t := 300) (b := true) rfl (by decide) (by decide)
        (by decide))
    (L2Run.cons (L2Step.genesis (id := 1) rfl) L2Run.nil)))
  refine ⟨_, hrun, FreshL2SysSatisfiesInvariant _ 100 (by decide),
    ⟨⟨by decide, by decide⟩, wMinorEdge, by decide⟩, ?_, not_crossClash_id _, _, _, rfl, rfl,
    by decide, by decide⟩
  intro h
  have h0 := h 0 0x10002 rfl (by decide)
  revert h0
  decide

theorem FrozenRowAlongRunsWitness : Properties.FrozenRowAlongRunsWitness :=
  ⟨_, CRun.cons (W := fzBase) (CStep.commit (s := initState fzBase 100) (t := 300) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)) CRun.nil,
    ⟨⟨by decide, by decide⟩, wMinorEdge, by decide⟩, rfl, by decide, by decide, by decide,
    by decide⟩

theorem LegacyCommitMovesTheFrozenRow : Properties.LegacyCommitMovesTheFrozenRow :=
  ⟨_, CRun.cons (W := fzBase) (CStep.legacyCommit (s := initState fzBase 100) (R := 250)
      (b := false) (by decide) (by decide)) CRun.nil, by decide, by decide, by decide⟩

end Contracts.ChainTypeManager.L2Tables
