import EraSpec.Contracts.ChainTypeManager.Properties.ExecutorUpgradeChain
import EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorForward

/-!
# Proofs: the executor's `upgradeChain`, and what a replacement must report

Every refined transaction is an `ExecutorForward` transaction (`ustep_toX`), so the safety results
carry over by projection. Enabledness is read off the constructor: `upgradeChain(t, id)` needs
`t` to be the slot at the chain's version and to report that version. Along tame runs the CTM
changes only through its own writers (`urun_ctm`, a generic preservation lemma). Two invariants
follow from that. Reporting slots survive genuine replacements, by `SlotsDepartFromTheirVersion`.
A misreporting slot survives every writer (`cstep_frozen`). The countermodel and the witnesses
are concrete runs over the witness world, checked by `decide`.
-/

namespace Contracts.ChainTypeManager

/-! ## Projection to `ExecutorForward` -/

lemma ustep_toX {X : XConfig} {s s' : XState} {u : ULabel} (h : UStep X s u s') :
    XStep X s u.toX s' := by
  cases h with
  | x _ h => exact h
  | upgradeChain _ _ _ _ hs => exact XStep.upgradeChain hs
  | adminUpgrade _ _ hs => exact XStep.upgradeChain hs

lemma urun_toX {X : XConfig} {s s' : XState} {us : List ULabel} (h : URun X s us s') :
    XRun X s (us.map ULabel.toX) s' := by
  induction h with
  | nil => exact XRun.nil
  | cons hs _ ih => exact XRun.cons (ustep_toX hs) ih

lemma tame_toX {X : XConfig} {us : List ULabel} (ht : ∀ u ∈ us, u.Tame X) :
    ∀ x ∈ us.map ULabel.toX, x.Tame X := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
  exact ht u hu

lemma xstep_ofX {X : XConfig} {s s' : XState} {x : XLabel} (h : XStep X s x s') :
    UStep X s (ULabel.ofX x) s' := by
  cases h with
  | infra happ hc => exact UStep.x (fun h => h) (XStep.infra happ hc)
  | commit hs h1 h2 => exact UStep.x (fun h => h) (XStep.commit hs h1 h2)
  | upgradeChain hs =>
    exact UStep.x (fun h => h) (XStep.forward (FRun.cons (FStep.sys hs) FRun.nil))
  | forward hr => exact UStep.x (fun h => h) (XStep.forward hr)
  | env he hs => exact UStep.x (fun h => h) (XStep.env he hs)

lemma xrun_ofX {X : XConfig} {s s' : XState} {xs : List XLabel} (h : XRun X s xs s') :
    URun X s (xs.map ULabel.ofX) s' := by
  induction h with
  | nil => exact URun.nil
  | cons hs _ ih => exact URun.cons (xstep_ofX hs) ih

lemma urun_snoc {X : XConfig} {s s1 s2 : XState} {us : List ULabel} {u : ULabel}
    (h : URun X s us s1) (h' : UStep X s1 u s2) : URun X s (us ++ [u]) s2 := by
  induction h with
  | nil => exact URun.cons h' URun.nil
  | cons hs _ ih => exact URun.cons hs (ih h')

/-! ## The transition step -/

/-- A transition reads a committed slot at the chain's version, leaves the CTM alone, and lands
the chain on that slot's target version. -/
lemma transition_facts {W : World} {s sys' : Sys} {id : ChainId} {c : Chain}
    (hc : s.chains id = some c) (h : Step W s (.transition id) sys') :
    s.ctm.ut c.pv ≠ 0 ∧ sys'.ctm = s.ctm ∧
      ∃ ρ, sys'.chains id = some ⟨(W.tr (s.ctm.ut c.pv)).new, ρ⟩ := by
  cases h with
  | @transition _ c0 ρ hc0 hut _ _ _ =>
    obtain rfl : c0 = c := Option.some.inj (hc0.symm.trans hc)
    exact ⟨hut, rfl, ρ, by simp⟩

lemma transition_chain {W : World} {s sys' : Sys} {id : ChainId}
    (h : Step W s (.transition id) sys') : ∃ c, s.chains id = some c := by
  cases h with
  | transition hc0 _ _ _ _ => exact ⟨_, hc0⟩

/-- `upgradeChain` with the slot's own transition, when that transition reports the chain's
version. -/
lemma upgradeChain_of_transition {X : XConfig} {s : XState} {id : ChainId} {c : Chain}
    {sys' : Sys} (hc : s.sys.chains id = some c)
    (hrep : (X.W.tr (s.sys.ctm.ut c.pv)).old = c.pv) (h : Step X.W s.sys (.transition id) sys') :
    UStep X s (.upgradeChain (s.sys.ctm.ut c.pv) id) { s with sys := sys' } :=
  UStep.upgradeChain (transition_facts hc h).1 (by rw [hrep]) hc hrep.symm h

/-! ## Along tame runs the CTM changes only through its writers -/

lemma step_ctm_cases {W : World} {s s' : Sys} {l : Label} (h : Step W s l s') :
    s'.ctm = s.ctm ∨ ∃ op, l = .ctm op ∧ CStep W s.ctm op s'.ctm := by
  cases h with
  | ctm hc => exact Or.inr ⟨_, rfl, hc⟩
  | _ => exact Or.inl rfl

section Preservation

variable {X : XConfig} {Q : CTM → Prop} {G : Address → Address → Prop}

lemma fstep_ctm
    (hQ : ∀ c op c', Q c → (∀ e r, op = .replace e r → G e r) →
      CStep X.W c op c' → Q c')
    {s s' : XState} {f : FCall} (h : FStep X s f s') (ht : f.Tame)
    (hG : ∀ e r, f = .sys (.ctm (.replace e r)) → G e r) (hq : Q s.sys.ctm) : Q s'.sys.ctm := by
  cases h with
  | sys hs =>
    rcases step_ctm_cases hs with heq | ⟨op, rfl, hc⟩
    · exact heq ▸ hq
    · exact hQ _ _ _ hq (fun e r hop => hG e r (by rw [hop])) hc
  | upgradeProxy _ _ _ => exact hq
  | swapCtm _ _ => exact ht.elim

lemma frun_ctm
    (hQ : ∀ c op c', Q c → (∀ e r, op = .replace e r → G e r) →
      CStep X.W c op c' → Q c')
    {s s' : XState} {fs : List FCall} (h : FRun X s fs s') :
    (∀ f ∈ fs, f.Tame) → (∀ e r, FCall.sys (.ctm (.replace e r)) ∈ fs → G e r) →
    Q s.sys.ctm → Q s'.sys.ctm := by
  induction h with
  | nil => intro _ _ hq; exact hq
  | cons hstep _ ih =>
    intro ht hG hq
    exact ih (fun f hf => ht f (List.mem_cons_of_mem _ hf))
      (fun e r hm => hG e r (List.mem_cons_of_mem _ hm))
      (fstep_ctm hQ hstep (ht _ List.mem_cons_self)
        (fun e r he => hG e r (he ▸ List.mem_cons_self)) hq)

lemma xstep_ctm
    (hQ : ∀ c op c', Q c → (∀ e r, op = .replace e r → G e r) →
      CStep X.W c op c' → Q c')
    (hf : ProxyUpgradeCurrent.ReinitFrames X.rc) {s s' : XState} {x : XLabel}
    (h : XStep X s x s') (ht : x.Tame X) (hG : ∀ e r, x.ForwardsReplace e r → G e r)
    (hq : Q s.sys.ctm) : Q s'.sys.ctm := by
  cases h with
  | @infra T J c' happ hc =>
    have ht' : ∀ r ∈ T.rows, r.proxy ≠ X.ctmProxy := ht
    have hJ : J X.ctmProxy = s.impl X.ctmProxy :=
      ProxyUpgradeCurrent.UnmovedProxiesFrame X.rc s.impl J T.rows hf happ.2.2 X.ctmProxy ht'
    show Q c'
    rw [hc hJ]
    exact hq
  | commit hs _ _ =>
    rcases step_ctm_cases hs with heq | ⟨op, hop, hc⟩
    · exact heq ▸ hq
    · cases hop
      exact hQ _ _ _ hq (fun e r h => by cases h) hc
  | upgradeChain hs =>
    rcases step_ctm_cases hs with heq | ⟨op, hop, _⟩
    · exact heq ▸ hq
    · cases hop
  | forward hr => exact frun_ctm hQ hr ht hG hq
  | env he hs =>
    rcases step_ctm_cases hs with heq | ⟨op, rfl, _⟩
    · exact heq ▸ hq
    · exact he.elim

lemma xrun_ctm
    (hQ : ∀ c op c', Q c → (∀ e r, op = .replace e r → G e r) →
      CStep X.W c op c' → Q c')
    (hf : ProxyUpgradeCurrent.ReinitFrames X.rc) {s s' : XState} {xs : List XLabel}
    (h : XRun X s xs s') :
    (∀ x ∈ xs, x.Tame X) → (∀ e r, (∃ x ∈ xs, x.ForwardsReplace e r) → G e r) →
    Q s.sys.ctm → Q s'.sys.ctm := by
  induction h with
  | nil => intro _ _ hq; exact hq
  | cons hstep _ ih =>
    intro ht hG hq
    exact ih (fun x hx => ht x (List.mem_cons_of_mem _ hx))
      (fun e r ⟨x, hx, hfr⟩ => hG e r ⟨x, List.mem_cons_of_mem _ hx, hfr⟩)
      (xstep_ctm hQ hf hstep (ht _ List.mem_cons_self)
        (fun e r hfr => hG e r ⟨_, List.mem_cons_self, hfr⟩) hq)

/-- **Generic preservation.** A property of the CTM's version state that every writer preserves
(a replacement only under `G`) holds along every tame refined run whose forwarded replacements
satisfy `G`. -/
lemma urun_ctm
    (hQ : ∀ c op c', Q c → (∀ e r, op = .replace e r → G e r) →
      CStep X.W c op c' → Q c')
    (hf : ProxyUpgradeCurrent.ReinitFrames X.rc) {s s' : XState} {us : List ULabel}
    (h : URun X s us s') (ht : ∀ u ∈ us, u.Tame X)
    (hG : ∀ e r, (∃ u ∈ us, u.ForwardsReplace e r) → G e r) (hq : Q s.sys.ctm) :
    Q s'.sys.ctm :=
  xrun_ctm hQ hf (urun_toX h) (tame_toX ht)
    (fun e r ⟨x, hx, hfr⟩ => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      exact hG e r ⟨u, hu, hfr⟩) hq

end Preservation

/-! ## The two invariants on slots -/

/-- One writer keeps a misreporting slot as it is. -/
lemma cstep_frozen {W : World} {s s' : CTM} {op : Op} {v : ℕ} (hI : CtmInv W s)
    (hv : s.ut v ≠ 0) (hmis : (W.tr (s.ut v)).old ≠ v) (h : CStep W s op s') :
    s'.ut v = s.ut v := by
  cases h with
  | commit _ _ hpv _ _ _ =>
    have := (hI.slots v hv).1
    exact upd_ne _ _ (by omega)
  | replace _ _ hslot _ _ _ _ _ =>
    refine upd_ne _ _ (fun hve => hmis ?_)
    subst hve
    rw [hslot]
  | _ => rfl

/-- One writer keeps every slot reporting its version, if a replacement reports its departing
release's version. -/
lemma cstep_slotsReport {W : World} {s s' : CTM} {op : Op} (hI : CtmInv W s)
    (hrep : SlotsReport W s)
    (hgen : ∀ e r, op = .replace e r → (W.tr r).old = W.relVersion (W.tr r).fromRel)
    (h : CStep W s op s') : SlotsReport W s' :=
  SlotsDepartFromTheirVersion W s s' [op] hI hrep
    (fun e r hm => hgen e r (List.mem_singleton.mp hm).symm) (CRun.cons h CRun.nil)

end Contracts.ChainTypeManager

/-! ## Certificates -/

namespace Contracts.ChainTypeManager

theorem UpgradeChainRunsTheCommittedEdge : Properties.UpgradeChainRunsTheCommittedEdge := by
  intro X s s' t id h
  refine ⟨ustep_toX h, ?_⟩
  cases h with
  | @upgradeChain _ _ c sys' _ hslot hc hpv hstep =>
    obtain ⟨_, _, ρ, hc'⟩ := transition_facts hc hstep
    have ht : s.sys.ctm.ut c.pv = t := by rw [hpv]; exact hslot
    refine ⟨c, _, hc, ht, hc', ?_⟩
    show (X.W.tr (s.sys.ctm.ut c.pv)).new = (X.W.tr t).new
    rw [ht]

theorem RefinedRunIsAnExecutorRun : Properties.RefinedRunIsAnExecutorRun :=
  fun _ _ _ _ h => urun_toX h

theorem ExecutorRunsNeedNoUpgradeChain : Properties.ExecutorRunsNeedNoUpgradeChain := by
  intro X s s' xs h
  refine ⟨xrun_ofX h, fun x => ?_, ?_⟩
  · cases x with
    | upgradeChain id =>
      show (∀ f ∈ [FCall.sys (.transition id)], f.Tame) ↔ True
      simp [FCall.Tame, Label.isArbitrary]
    | _ => exact Iff.rfl
  · intro u hu t id hue
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hu
    cases x <;> cases hue

theorem RefinedTameRunKeepsChainsOnTheirRelease :
    Properties.RefinedTameRunKeepsChainsOnTheirRelease :=
  fun X s s' _ hf hI h ht =>
    TameRunKeepsChainsOnTheirRelease X s s' _ hf hI (urun_toX h) (tame_toX ht)

theorem UpgradeChainEnabledIff : Properties.UpgradeChainEnabledIff := by
  intro X s id
  constructor
  · rintro ⟨t, s', h⟩
    cases h with
    | @upgradeChain _ _ c sys' _ hslot hc hpv hstep =>
      refine ⟨c, hc, ?_, sys', hstep⟩
      rw [hpv, hslot]
  · rintro ⟨c, hc, hrep, sys', hstep⟩
    exact ⟨_, _, upgradeChain_of_transition hc hrep hstep⟩

theorem ReportingSlotsMakeUpgradeChainTheTransition :
    Properties.ReportingSlotsMakeUpgradeChainTheTransition := by
  intro X s s' id hrep
  constructor
  · rintro ⟨t, h⟩
    exact ustep_toX h
  · intro h
    cases h with
    | upgradeChain hstep =>
      obtain ⟨c, hc⟩ := transition_chain hstep
      exact ⟨_, upgradeChain_of_transition hc (hrep _ (transition_facts hc hstep).1) hstep⟩

theorem GenuineReplacementsKeepUpgradeChainLive :
    Properties.GenuineReplacementsKeepUpgradeChainLive := by
  intro X s s' us hf hI hrep h ht hgen
  have hQ : ∀ c op c', (CtmInv X.W c ∧ SlotsReport X.W c) →
      (∀ e r, op = .replace e r → (X.W.tr r).old = X.W.relVersion (X.W.tr r).fromRel) →
      CStep X.W c op c' → (CtmInv X.W c' ∧ SlotsReport X.W c') :=
    fun _ _ _ hc hg hs => ⟨step_inv hc.1 hs, cstep_slotsReport hc.1 hc.2 hg hs⟩
  obtain ⟨_, hrep'⟩ := urun_ctm hQ hf h ht hgen ⟨hI, hrep⟩
  refine ⟨hrep', fun id s'' => ⟨?_, ?_⟩⟩
  · rintro ⟨t, h'⟩
    cases h' with
    | @upgradeChain _ _ c _ _ _ hc _ hstep => exact ⟨_, UStep.adminUpgrade hc rfl hstep⟩
  · rintro ⟨old, h'⟩
    cases h' with
    | @adminUpgrade _ _ c _ hc _ hstep =>
      exact ⟨_, upgradeChain_of_transition hc (hrep' _ (transition_facts hc hstep).1) hstep⟩

theorem MisreportingSlotIsFrozen : Properties.MisreportingSlotIsFrozen := by
  intro W s s' ops v hI hv hmis h
  induction h with
  | nil => rfl
  | cons hs _ ih =>
    have h1 := cstep_frozen hI hv hmis hs
    rw [ih (step_inv hI hs) (by rw [h1]; exact hv) (by rw [h1]; exact hmis), h1]

theorem MisreportingSlotStaysFrozen : Properties.MisreportingSlotStaysFrozen := by
  intro X s s' us v hf hI hv hmis h ht
  have hQ : ∀ c op c', (CtmInv X.W c ∧ c.ut v = s.sys.ctm.ut v) →
      (∀ e r, op = .replace e r → True) →
      CStep X.W c op c' → (CtmInv X.W c' ∧ c'.ut v = s.sys.ctm.ut v) := by
    rintro c op c' ⟨hIc, hcv⟩ _ hs
    refine ⟨step_inv hIc hs, ?_⟩
    rw [cstep_frozen hIc (by rw [hcv]; exact hv) (by rw [hcv]; exact hmis) hs, hcv]
  obtain ⟨_, hfrozen⟩ :=
    urun_ctm (G := fun _ _ => True) hQ hf h ht (fun _ _ _ => trivial) ⟨hI, rfl⟩
  refine ⟨hfrozen, ?_⟩
  rintro id c hc hpv ⟨t, s'', h'⟩
  obtain ⟨c0, hc0, hrep, _⟩ := (UpgradeChainEnabledIff X s' id).mp ⟨t, s'', h'⟩
  obtain rfl : c0 = c := Option.some.inj (hc0.symm.trans hc)
  rw [hpv, hfrozen] at hrep
  exact hmis hrep

end Contracts.ChainTypeManager

/-! ## The countermodel and the witnesses -/

namespace Contracts.ChainTypeManager

/-- In the witness world, a chain at version 1 routing release `100` crosses a slot-1
transition from release `100` to release `200` at version 2, onto release `200`'s routing. -/
private lemma w_cross {S : Sys} {t : Address}
    (hch : S.chains 0 = some ⟨1, rowsRouting (wWorld.relRows 100)⟩) (hut : S.ctm.ut 1 = t)
    (ht0 : t ≠ 0) (hfrom : (wWorld.tr t).fromRel = 100) (hnr : (wWorld.tr t).newRel = 200)
    (hnew : (wWorld.tr t).new = 2) :
    ∃ sys', Step wWorld S (.transition 0) sys' ∧ sys'.ctm = S.ctm ∧
      sys'.chains 0 = some ⟨2, rowsRouting (wWorld.relRows 200)⟩ := by
  refine ⟨_, Step.transition (c := ⟨1, rowsRouting (wWorld.relRows 100)⟩)
    (ρ := rowsRouting (wWorld.relRows 200)) hch ?_ ?_ ?_ ?_, rfl, ?_⟩
  · show S.ctm.ut 1 ≠ 0
    rw [hut]
    exact ht0
  · show rowsRouting (wWorld.relRows 100) =
      rowsRouting (wWorld.relRows (wWorld.tr (S.ctm.ut 1)).fromRel)
    rw [hut, hfrom]
  · show applyDerived (rowsRouting (wWorld.relRows 100))
      (wWorld.relRows (wWorld.tr (S.ctm.ut 1)).fromRel)
      (wWorld.relRows (wWorld.tr (S.ctm.ut 1)).newRel) = some (rowsRouting (wWorld.relRows 200))
    rw [hut, hfrom, hnr]
    exact applyDerived_rows_eq xNodup100 xNodup200
  · show 1 < (wWorld.tr (S.ctm.ut 1)).new
    rw [hut, hnew]
    decide
  · show upd S.chains 0
        (some ⟨(wWorld.tr (S.ctm.ut 1)).new, rowsRouting (wWorld.relRows 200)⟩) 0 =
      some ⟨2, rowsRouting (wWorld.relRows 200)⟩
    rw [hut, hnew, upd_same]

/-- The first two transactions of both concrete runs: chain `0` is created on the fresh witness
system, and `300` is committed through `applyCTMUpgrade`. -/
private lemma w_prefix : ∃ s1, URun wX wX0 [.x (.env (.genesis 0)), .x (.commit 300)] s1 ∧
    s1.sys.chains 0 = some ⟨1, rowsRouting (wWorld.relRows 100)⟩ ∧ s1.sys.ctm.ut 1 = 300 ∧
    s1.sys.ctm.pv = 2 ∧ s1.sys.ctm.cur = 200 ∧ s1.sys.ctm.relAt 2 = 200 := by
  have hc : CStep wWorld (initState wWorld 100) (.commit 300) _ :=
    CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨p1, p2⟩ := ExecutorPostcheckPasses _ _ _ _ hc
  exact ⟨_, URun.cons (X := wX) (s := wX0)
    (UStep.x (l := .env (.genesis 0)) (fun h => h)
      (XStep.env trivial (Step.genesis (id := 0) rfl (addAll_empty_eq xNodup100))))
    (URun.cons (UStep.x (l := .commit 300) (fun h => h) (XStep.commit (Step.ctm hc) p1 p2))
      URun.nil), rfl, by decide, by decide, by decide, by decide⟩

/-- A forwarded replacement of `300` by `r` after the prefix. -/
private lemma w_replace {s1 : XState} {r : Address} (hut : s1.sys.ctm.ut 1 = 300)
    (hpv : s1.sys.ctm.pv = 2) (hcur : s1.sys.ctm.cur = 200) (hr0 : r ≠ 0) (hr : r ≠ 300)
    (hfrom : (wWorld.tr r).fromRel = 100) (hnew : (wWorld.tr r).new = 2)
    (hnr : (wWorld.tr r).newRel = 200) :
    ∃ s, UStep wX s1 (.x (.forward [.sys (.ctm (.replace 300 r))])) s ∧
      s.sys.chains = s1.sys.chains ∧ s.sys.ctm.ut 1 = r ∧
      s.sys.ctm.relAt = s1.sys.ctm.relAt := by
  have h300 : (wWorld.tr 300).old = 1 := rfl
  have hstep : CStep wWorld s1.sys.ctm (.replace 300 r) _ :=
    CStep.replace (e := 300) (r := r) (by decide) hr0 (by rw [h300, hut])
      hr (by rw [hfrom]; rfl) (by rw [hnew]; decide)
      (fun _ => by rw [hnr, hcur])
      (fun h => absurd (by rw [hnew, hpv]) h)
  refine ⟨_, UStep.x (fun h => h)
    (XStep.forward (FRun.cons (FStep.sys (Step.ctm hstep)) FRun.nil)), rfl, ?_, rfl⟩
  show upd s1.sys.ctm.ut (wWorld.tr 300).old r 1 = r
  rw [h300, upd_same]

theorem NonGenuineReplacementBricksUpgradeChain :
    Properties.NonGenuineReplacementBricksUpgradeChain := by
  obtain ⟨s1, hpre, hch1, hut1, hpv1, hcur1, _⟩ := w_prefix
  obtain ⟨s, hrep, hchs, huts, _⟩ := w_replace (r := 500) hut1 hpv1 hcur1 (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hch : s.sys.chains 0 = some ⟨1, rowsRouting (wWorld.relRows 100)⟩ := by rw [hchs, hch1]
  have htame : ∀ u ∈ [ULabel.x (.env (.genesis 0)), .x (.commit 300),
      .x (.forward [.sys (.ctm (.replace 300 500))])], u.Tame wX := by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · trivial
    · trivial
    · intro f hf
      rw [List.mem_singleton.mp hf]
      simp [FCall.Tame, Label.isArbitrary]
  have hS : SysInv wX.W s.sys :=
    (TameRunPreservesSysInv wX wX0 s _ ProxyUpgradeCurrent.wConfig_frames wX0_inv
      (urun_toX (urun_snoc hpre hrep)) (tame_toX htame)).1
  obtain ⟨sys1, hstep1, _, _⟩ := w_cross (S := s1.sys) hch1 hut1 (by decide) (by decide)
    (by decide) (by decide)
  obtain ⟨sys2, hstep2, _, hch2⟩ := w_cross (S := s.sys) hch huts (by decide) (by decide)
    (by decide) (by decide)
  refine ⟨ProxyUpgradeCurrent.wConfig_frames, wX0_inv, s1, s, hpre,
    ⟨_, UStep.upgradeChain (t := 300) (by decide)
      (by rw [show (wX.W.tr 300).old = 1 from rfl]; exact hut1) hch1 (by decide) hstep1⟩,
    hrep, htame _ (by simp), hS, ⟨_, hch, rfl⟩, huts, by decide,
    fun h => absurd h.1 (by decide), ?_, ?_,
    ⟨_, UStep.adminUpgrade hch rfl hstep2, step_sysInv hS hstep2 (by simp [Label.isArbitrary]),
      _, hch2, rfl, rfl⟩,
    ⟨_, UStep.x (fun h => h) (XStep.forward (FRun.cons (FStep.sys hstep2) FRun.nil)),
      step_sysInv hS hstep2 (by simp [Label.isArbitrary]), _, hch2, rfl, rfl⟩⟩
  · rintro ⟨t, s', h⟩
    obtain ⟨c, hc, hrep', _⟩ := (UpgradeChainEnabledIff wX s 0).mp ⟨t, s', h⟩
    rw [hch] at hc
    cases hc
    rw [huts] at hrep'
    exact absurd hrep' (by decide)
  · intro us s'' hr ht
    obtain ⟨h1, h2⟩ := MisreportingSlotStaysFrozen wX s s'' us 1
      ProxyUpgradeCurrent.wConfig_frames hS.1 (by rw [huts]; decide) (by rw [huts]; decide) hr ht
    exact ⟨h1.trans huts, h2⟩

theorem ExecutorUpgradeChainWitness : Properties.ExecutorUpgradeChainWitness := by
  obtain ⟨s1, hpre, hch1, hut1, hpv1, hcur1, hrel1⟩ := w_prefix
  obtain ⟨s, hrep, hchs, huts, hrel⟩ := w_replace (r := 400) hut1 hpv1 hcur1 (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hch : s.sys.chains 0 = some ⟨1, rowsRouting (wWorld.relRows 100)⟩ := by rw [hchs, hch1]
  have hrun : URun wX wX0 [.x (.env (.genesis 0)), .x (.commit 300),
      .x (.forward [.sys (.ctm (.replace 300 400))])] s := urun_snoc hpre hrep
  have htame : ∀ u ∈ [ULabel.x (.env (.genesis 0)), .x (.commit 300),
      .x (.forward [.sys (.ctm (.replace 300 400))]), .upgradeChain 400 0], u.Tame wX := by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · trivial
    · trivial
    · intro f hf
      rw [List.mem_singleton.mp hf]
      simp [FCall.Tame, Label.isArbitrary]
    · trivial
  have hgen : ∀ e r, (∃ u ∈ [ULabel.x (.env (.genesis 0)), .x (.commit 300),
      .x (.forward [.sys (.ctm (.replace 300 400))])], u.ForwardsReplace e r) →
      (wWorld.tr r).old = wWorld.relVersion (wWorld.tr r).fromRel := by
    rintro e r ⟨u, hu, hfr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl <;> try exact hfr.elim
    · have hm : FCall.sys (.ctm (.replace e r)) = FCall.sys (.ctm (.replace 300 400)) :=
        List.mem_singleton.mp hfr
      cases hm
      decide
  have hrep0 : SlotsReport wX.W wX0.sys.ctm := fun _ hv => absurd rfl hv
  obtain ⟨hrepS, _⟩ := GenuineReplacementsKeepUpgradeChainLive wX wX0 s _
    ProxyUpgradeCurrent.wConfig_frames wX0_inv.1 hrep0 hrun
    (fun u hu => htame u (List.mem_append_left [_] hu)) hgen
  obtain ⟨sys', hstep, hctm, hch'⟩ := w_cross (S := s.sys) hch huts (by decide) (by decide)
    (by decide) (by decide)
  refine ⟨ProxyUpgradeCurrent.wConfig_frames, wX0_inv, hrep0, htame, hgen,
    List.mem_singleton_self _, s, _, hrun, huts, hrepS, ?_,
    UStep.upgradeChain (t := 400) (by decide)
      (by rw [show (wX.W.tr 400).old = 1 from rfl]; exact huts) hch (by decide) hstep,
    _, hch', rfl, ?_, rfl⟩
  · rintro ⟨s'', h⟩
    cases h with
    | upgradeChain _ hslot _ _ _ =>
      rw [show (wX.W.tr 300).old = 1 from rfl, huts] at hslot
      exact absurd hslot (by decide)
  · show sys'.ctm.relAt 2 = 200
    rw [hctm, hrel, hrel1]

theorem MisreportingSlotWitness : Properties.MisreportingSlotWitness := by
  obtain ⟨c, hrun, hut1, hut7, hpv, hcur⟩ : ∃ c, CRun wWorld (initState wWorld 100)
      [.commit 300, .replace 300 500] c ∧
      c.ut 1 = 500 ∧ c.ut 7 = 0 ∧ c.pv = 2 ∧ c.cur = 200 :=
    ⟨_, CRun.cons (CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))
      (CRun.cons (CStep.replace (e := 300) (r := 500) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)) CRun.nil),
      by decide, by decide, by decide, by decide⟩
  have hI : CtmInv wWorld c := run_inv (InitSatisfiesInvariant wWorld 100 (by decide)) hrun
  have hc600 : CStep wWorld c (.commit 600) _ :=
    CStep.commit (t := 600) (by decide) (by rw [hcur]; decide) (by rw [hpv]; decide) (by decide)
      (by decide) (by decide)
  refine ⟨c, _, hrun, hI, hut1, by rw [hut1]; decide, ?_, CRun.cons hc600 CRun.nil, ?_,
    show (wWorld.tr 600).new = 3 by decide⟩
  · rintro r ⟨c'', h⟩
    cases h with
    | replace _ _ hslot _ _ _ _ _ =>
      rw [show (wWorld.tr 500).old = 7 from rfl, hut7] at hslot
      exact absurd hslot (by decide)
  · show upd c.ut (wWorld.tr 600).old 600 1 = 500
    rw [upd_ne c.ut 600 (show (1 : ℕ) ≠ (wWorld.tr 600).old by decide), hut1]

end Contracts.ChainTypeManager
