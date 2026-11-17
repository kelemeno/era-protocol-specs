import EraSpec.Contracts.SecondProofSystem.Properties.UpgradeGateV35
import EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTiming
import EraSpec.Contracts.ChainTypeManager.Proofs.Enabledness

/-!
# Proofs: the second-proof gate on every chain upgrade (draft/v0.35.0)

Every upgrade step of the gated system is one `UpgradeTiming` step together with a
`VerifierGate` on the verifier of the edge committed at the chain's own version
(`upgrade_gate`). The gate results read that record. The lock results split a state into the
chain's own fields and a predicate on the CTM's version state (`LockedCtm`, `StuckCtm`). Every
step that is neither an upgrade nor a break-glass cut of the chain leaves the chain's fields
alone and either leaves the CTM alone or is a `CStep` (`gstep_view`), and each predicate is
preserved by the `CStep`s the statement allows. The release-policy results carry `PolicyInv`
along a run step by step (`policyInv_step`) and read the edge's verifier off it
(`policy_edge_multi`); the enabledness half projects the gated run to a routing run
(`GatedRunIsATimedRun`, then `TimedRunIsARun`) and reuses `Enabledness.UpgradesStayEnabled`. The
countermodel and the witnesses are concrete runs over the `ChainRouting` witness world, extended
in the Specs.
-/

namespace Contracts.SecondProofSystem.UpgradeGateV35

open Contracts.ChainTypeManager

/-! ## Reading a step -/

/-- Every timed upgrade step is one diamond call at the path's departing version, and changes
only the routing system. -/
private lemma timed_upgrade_inv {T : TimedConfig} {s s' : TimedSys} {id : ChainId}
    {path : UpgradePath} {caller : Address} {τ : ℕ}
    (h : TimedStep T s (.upgrade id path caller τ) s') :
    ∃ c' sys', DiamondUpgrade T s id (departure T.X.W path) c' τ sys' ∧
      s' = { s with sys := sys' } := by
  cases h with
  | direct d => exact ⟨_, _, d, rfl⟩
  | ctm _ d => exact ⟨_, _, d, rfl⟩
  | executor _ _ _ d => exact ⟨_, _, d, rfl⟩

/-- A base step of the timed system is a `ChainRouting` step, and changes only the routing
system. -/
private lemma timed_base_inv {T : TimedConfig} {s s' : TimedSys} {l : Label}
    (h : TimedStep T s (.base l) s') :
    ∃ sys', Step T.X.W s.sys l sys' ∧ s' = { s with sys := sys' } := by
  cases h with
  | base _ hs => exact ⟨_, hs, rfl⟩

/-- The chain a `ChainRouting` label acts on; `none` for a CTM writer. -/
private def labelChain : Label → Option ChainId
  | .ctm _ => none
  | .genesis i => some i
  | .migrateIn i => some i
  | .transition i => some i
  | .bootstrapReset i => some i
  | .arbitraryCut i _ _ => some i

/-- A chain step of `ChainRouting` leaves the CTM and every other chain as they were. -/
private lemma chain_frame {W : World} {s s' : Sys} {l : Label} {i : ChainId}
    (h : Step W s l s') (hl : labelChain l = some i) :
    s'.ctm = s.ctm ∧ ∀ id, id ≠ i → s'.chains id = s.chains id := by
  cases h with
  | ctm _ => simp [labelChain] at hl
  | genesis _ _ =>
      simp only [labelChain, Option.some.injEq] at hl
      subst hl
      exact ⟨rfl, fun id hid => upd_ne _ _ hid⟩
  | migrateIn _ _ _ _ =>
      simp only [labelChain, Option.some.injEq] at hl
      subst hl
      exact ⟨rfl, fun id hid => upd_ne _ _ hid⟩
  | transition _ _ _ _ _ =>
      simp only [labelChain, Option.some.injEq] at hl
      subst hl
      exact ⟨rfl, fun id hid => upd_ne _ _ hid⟩
  | bootstrapReset _ _ _ _ =>
      simp only [labelChain, Option.some.injEq] at hl
      subst hl
      exact ⟨rfl, fun id hid => upd_ne _ _ hid⟩
  | arbitraryCut _ _ _ =>
      simp only [labelChain, Option.some.injEq] at hl
      subst hl
      exact ⟨rfl, fun id hid => upd_ne _ _ hid⟩

/-- **The gate of an upgrade.** A successful upgrade of chain `id`, by any path, passed the
verifier checks on the verifier of the release that the edge committed at the chain's own
version lands on. -/
private lemma upgrade_gate {G : GateConfig} {s s' : GSys} {id : ChainId} {path : UpgradePath}
    {caller : Address} {τ : ℕ} {c : Chain} (h : GStep G s (.upgrade id path caller τ) s')
    (hc : s.ts.sys.chains id = some c) :
    VerifierGate G (s.gate id).flag
      (G.relVerifier (G.T.X.W.tr (s.ts.sys.ctm.ut c.pv)).newRel) := by
  cases h with
  | upgrade ht hg =>
      obtain ⟨_, _, d, -⟩ := timed_upgrade_inv ht
      obtain ⟨c', hc', hv⟩ := d.atVersion
      have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
      subst hcc
      rw [← hv] at hg
      exact hg

private lemma upd_flag_ne {gate : ChainId → GateState} {i id : ChainId} (g : GateState)
    (hi : id ≠ i) (hf : (gate id).flag = true) : (upd gate i g id).flag = true := by
  rw [upd_ne _ _ hi]
  exact hf

/-- Updating one chain's gate fields to a state that passes the gate keeps `GateInv`. -/
private lemma gateInv_upd {G : GateConfig} {gate : ChainId → GateState}
    (hI : ∀ id, (gate id).flag = true → IsMulti G (gate id).verifier) (i : ChainId)
    (g : GateState) (hg : g.flag = true → IsMulti G g.verifier) :
    ∀ id, (upd gate i g id).flag = true → IsMulti G (upd gate i g id).verifier := by
  intro id
  by_cases hi : id = i
  · subst hi
    rw [upd_same]
    exact hg
  · rw [upd_ne _ _ hi]
    exact hI id

/-! ## The gate holds -/

theorem FlaggedCutsKeepMultiProof : Properties.FlaggedCutsKeepMultiProof := by
  intro G s s' l id h hcut hflag
  cases h with
  | upgrade ht hg =>
      simp only [GLabel.CutsChain] at hcut
      subst hcut
      simp only [upd_same] at hflag ⊢
      exact hg.postCut hflag
  | genesis ht hv =>
      simp only [GLabel.CutsChain] at hcut
      subst hcut
      simp [upd_same, freshGate] at hflag
  | migrateIn ht hv =>
      simp only [GLabel.CutsChain] at hcut
      subst hcut
      simp [upd_same, freshGate] at hflag
  | bootstrapReset hc hl ht hg =>
      simp only [GLabel.CutsChain] at hcut
      subst hcut
      simp only [upd_same] at hflag ⊢
      exact hg.postCut hflag
  | breakGlass ht hg =>
      simp only [GLabel.CutsChain] at hcut
      subst hcut
      simp only [upd_same] at hflag ⊢
      exact hg hflag
  | other _ _ => exact False.elim hcut
  | requireSecondProof _ _ _ _ _ => exact False.elim hcut
  | setProofSystemStatus _ _ => exact False.elim hcut

/-- What a step that is neither an upgrade nor a break-glass cut of chain `id` does to that
chain, when it is registered and flagged and no legacy cut is recorded at its version: it leaves
the chain and its flag as they were, and either leaves the CTM's version state alone or is a
CTM writer. -/
private lemma gstep_view {G : GateConfig} {s s' : GSys} {l : GLabel} {id : ChainId} {c : Chain}
    (h : GStep G s l s') (hc : s.ts.sys.chains id = some c) (hf : (s.gate id).flag = true)
    (hnl : s.ts.sys.ctm.legacy c.pv = LegacyCut.none)
    (hbg : ¬ l.BreakGlassOf id) (hup : ∀ path caller τ, l ≠ .upgrade id path caller τ) :
    s'.ts.sys.chains id = some c ∧ (s'.gate id).flag = true ∧
      (s'.ts.sys.ctm = s.ts.sys.ctm ∨
        ∃ op, l = .other (.base (.ctm op)) ∧ CStep G.T.X.W s.ts.sys.ctm op s'.ts.sys.ctm) := by
  cases h with
  | @upgrade i path caller τ ts' ht hg =>
      have hi : id ≠ i := fun hid => hup path caller τ (by subst hid; rfl)
      obtain ⟨_, sys', d, rfl⟩ := timed_upgrade_inv ht
      obtain ⟨hctm, hch⟩ := chain_frame d.routing rfl
      exact ⟨(hch id hi).trans hc, upd_flag_ne _ hi hf, Or.inl hctm⟩
  | @genesis i ts' ht hv =>
      obtain ⟨sys', hs, rfl⟩ := timed_base_inv ht
      have hi : id ≠ i := by
        rintro rfl
        cases hs with
        | genesis hnone _ =>
            rw [hnone] at hc
            cases hc
      obtain ⟨hctm, hch⟩ := chain_frame hs rfl
      exact ⟨(hch id hi).trans hc, upd_flag_ne _ hi hf, Or.inl hctm⟩
  | @migrateIn i ts' ht hv =>
      obtain ⟨sys', hs, rfl⟩ := timed_base_inv ht
      have hi : id ≠ i := by
        rintro rfl
        cases hs with
        | migrateIn _ _ hnone _ =>
            rw [hnone] at hc
            cases hc
      obtain ⟨hctm, hch⟩ := chain_frame hs rfl
      exact ⟨(hch id hi).trans hc, upd_flag_ne _ hi hf, Or.inl hctm⟩
  | @bootstrapReset i c0 R ts' hc0 hleg ht hg =>
      have hi : id ≠ i := by
        rintro rfl
        have hcc : c0 = c := Option.some.inj (hc0.symm.trans hc)
        subst hcc
        rw [hnl] at hleg
        cases hleg
      obtain ⟨sys', hs, rfl⟩ := timed_base_inv ht
      obtain ⟨hctm, hch⟩ := chain_frame hs rfl
      exact ⟨(hch id hi).trans hc, upd_flag_ne _ hi hf, Or.inl hctm⟩
  | @breakGlass i v ρ g ts' ht hg =>
      have hi : id ≠ i := fun hid => hbg hid.symm
      obtain ⟨sys', hs, rfl⟩ := timed_base_inv ht
      obtain ⟨hctm, hch⟩ := chain_frame hs rfl
      exact ⟨(hch id hi).trans hc, upd_flag_ne _ hi hf, Or.inl hctm⟩
  | @other l' ts' hfree ht =>
      cases ht with
      | direct _ => exact False.elim hfree
      | ctm _ _ => exact False.elim hfree
      | executor _ _ _ _ => exact False.elim hfree
      | base _ hs =>
          cases hs with
          | ctm hcs => exact ⟨hc, hf, Or.inr ⟨_, rfl, hcs⟩⟩
          | genesis _ _ => exact False.elim hfree
          | migrateIn _ _ _ _ => exact False.elim hfree
          | transition _ _ _ _ _ => exact False.elim hfree
          | bootstrapReset _ _ _ _ => exact False.elim hfree
          | arbitraryCut _ _ _ => exact False.elim hfree
      | setUpgradeTimestamp _ _ _ _ => exact ⟨hc, hf, Or.inl rfl⟩
      | swapNotifier => exact ⟨hc, hf, Or.inl rfl⟩
      | setAux => exact ⟨hc, hf, Or.inl rfl⟩
  | @requireSecondProof i caller c0 hc0 hcaller hsl hflag hmode =>
      refine ⟨hc, ?_, Or.inl rfl⟩
      by_cases hi : id = i
      · subst hi
        show (upd s.gate id _ id).flag = true
        simp [upd_same]
      · exact upd_flag_ne _ hi hf
  | @setProofSystemStatus i caller enabled c0 hc0 hcaller =>
      refine ⟨hc, ?_, Or.inl rfl⟩
      by_cases hi : id = i
      · subst hi
        show (upd s.gate id _ id).flag = true
        simpa [upd_same] using hf
      · exact upd_flag_ne _ hi hf

theorem FlagSurvivesAllButBreakGlass : Properties.FlagSurvivesAllButBreakGlass := by
  intro G s s' l id h hreg hnb hflag
  cases h with
  | @upgrade i path caller τ ts' ht hg =>
      by_cases hi : id = i
      · subst hi
        show (upd s.gate id _ id).flag = true
        simpa [upd_same] using hflag
      · exact upd_flag_ne _ hi hflag
  | @genesis i ts' ht hv =>
      obtain ⟨sys', hs, rfl⟩ := timed_base_inv ht
      have hi : id ≠ i := by
        rintro rfl
        cases hs with
        | genesis hnone _ => exact hreg hnone
      exact upd_flag_ne _ hi hflag
  | @migrateIn i ts' ht hv =>
      obtain ⟨sys', hs, rfl⟩ := timed_base_inv ht
      have hi : id ≠ i := by
        rintro rfl
        cases hs with
        | migrateIn _ _ hnone _ => exact hreg hnone
      exact upd_flag_ne _ hi hflag
  | @bootstrapReset i c0 R ts' hc0 hleg ht hg =>
      by_cases hi : id = i
      · subst hi
        show (upd s.gate id _ id).flag = true
        simpa [upd_same] using hflag
      · exact upd_flag_ne _ hi hflag
  | @breakGlass i v ρ g ts' ht hg =>
      have hi : id ≠ i := by
        rintro rfl
        exact hnb v ρ g rfl
      exact upd_flag_ne _ hi hflag
  | other _ _ => exact hflag
  | @requireSecondProof i caller c0 hc0 hcaller hsl hfl hmode =>
      by_cases hi : id = i
      · subst hi
        show (upd s.gate id _ id).flag = true
        simp [upd_same]
      · exact upd_flag_ne _ hi hflag
  | @setProofSystemStatus i caller enabled c0 hc0 hcaller =>
      by_cases hi : id = i
      · subst hi
        show (upd s.gate id _ id).flag = true
        simpa [upd_same] using hflag
      · exact upd_flag_ne _ hi hflag

/-- One step keeps `GateInv`, given mask-monotone verifiers. -/
private lemma gstep_gateInv {G : GateConfig} {s s' : GSys} {l : GLabel} (hM : MaskMonotone G)
    (hI : GateInv G s) (h : GStep G s l s') : GateInv G s' := by
  cases h with
  | upgrade ht hg => exact gateInv_upd hI _ _ (fun hf => hg.postCut hf)
  | genesis ht hv => exact gateInv_upd hI _ _ (fun hf => by simp [freshGate] at hf)
  | migrateIn ht hv => exact gateInv_upd hI _ _ (fun hf => by simp [freshGate] at hf)
  | bootstrapReset hc hl ht hg => exact gateInv_upd hI _ _ (fun hf => hg.postCut hf)
  | breakGlass ht hg => exact gateInv_upd hI _ _ hg
  | other _ _ => exact hI
  | requireSecondProof hc hcaller hsl hfl hmode =>
      exact gateInv_upd hI _ _ (fun _ => hM _ _ hmode)
  | setProofSystemStatus hc hcaller => exact gateInv_upd hI _ _ (fun hf => hI _ hf)

theorem FlaggedChainsStayMultiProof : Properties.FlaggedChainsStayMultiProof := by
  intro G s s' ls hM hI hrun
  induction hrun with
  | nil => exact hI
  | cons hs _ ih => exact ih (gstep_gateInv hM hI hs)

/-- Every witness configuration is mask-monotone, whatever verifier each release ships. -/
private lemma gMaskMonotone (rv : Address → Address) :
    MaskMonotone { gCfg with relVerifier := rv } := by
  intro a d h
  change gProofMode a d = some MULTI at h
  change gProofMode a 0 = some MULTI
  by_cases h1 : a = 700
  · subst h1
    decide
  · by_cases h2 : a = 701
    · subst h2
      simp [gProofMode, singleProofMode, PLONK, MULTI] at h
    · simp [gProofMode, h1, h2] at h

set_option maxRecDepth 8192 in
theorem MaskMonotoneHoldsForDeployedVerifiers :
    Properties.MaskMonotoneHoldsForDeployedVerifiers := by
  refine ⟨by decide, fun d h => by simp [singleProofMode, PLONK, MULTI] at h, by decide,
    gMaskMonotone _, gMaskMonotone _, gMaskMonotone _⟩

/-! ## The witness state

`gLockRun` reaches `gLock` in each witness configuration: they differ only in the verifier of
releases other than `100`, and the run reads only release `100`'s. -/

private lemma gNodup100 : ((gWorld.relRows 100).map Prod.fst).Nodup := by decide
private lemma gNodup200 : ((gWorld.relRows 200).map Prod.fst).Nodup := by decide
private lemma gNodup210 : ((gWorld.relRows 210).map Prod.fst).Nodup := by decide
private lemma gNodup250 : ((gWorld.relRows 250).map Prod.fst).Nodup := by decide

/-- The multi-proof verifier `700` passes the gate. -/
private lemma multi_700 (rv : Address → Address) :
    IsMulti { gCfg with relVerifier := rv } 700 := by
  change gProofMode 700 0 = some MULTI
  decide

/-- The single-proof verifier `701` fails the gate. -/
private lemma not_multi_701 (rv : Address → Address) :
    ¬ IsMulti { gCfg with relVerifier := rv } 701 := by
  change ¬ gProofMode 701 0 = some MULTI
  decide

private lemma gLock_run_gCfg : GRun gCfg gSys0 gLockRun gLock :=
  GRun.cons (GStep.genesis (TimedStep.base (l := .genesis 0) (fun h => h)
      (Step.genesis rfl (addAll_empty_eq gNodup100))) (by decide))
  (GRun.cons (GStep.other True.intro TimedStep.setAux)
  (GRun.cons (GStep.genesis (TimedStep.base (l := .genesis 1) (fun h => h)
      (Step.genesis rfl (addAll_empty_eq gNodup100))) (by decide))
  (GRun.cons (GStep.other True.intro TimedStep.setAux)
  (GRun.cons (GStep.requireSecondProof (c := ⟨1, rowsRouting (wRows 100)⟩) rfl rfl rfl rfl
      (by decide))
  (GRun.cons (GStep.other True.intro (TimedStep.base (l := .ctm (.commit 300)) (fun h => h)
      (Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)))))
  GRun.nil)))))

private lemma gLock_run_gCfgMulti : GRun gCfgMulti gSys0 gLockRun gLock :=
  GRun.cons (GStep.genesis (TimedStep.base (l := .genesis 0) (fun h => h)
      (Step.genesis rfl (addAll_empty_eq gNodup100))) (by decide))
  (GRun.cons (GStep.other True.intro TimedStep.setAux)
  (GRun.cons (GStep.genesis (TimedStep.base (l := .genesis 1) (fun h => h)
      (Step.genesis rfl (addAll_empty_eq gNodup100))) (by decide))
  (GRun.cons (GStep.other True.intro TimedStep.setAux)
  (GRun.cons (GStep.requireSecondProof (c := ⟨1, rowsRouting (wRows 100)⟩) rfl rfl rfl rfl
      (by decide))
  (GRun.cons (GStep.other True.intro (TimedStep.base (l := .ctm (.commit 300)) (fun h => h)
      (Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)))))
  GRun.nil)))))

private lemma gLockRun_no_breakGlass : ∀ l ∈ gLockRun, ¬ l.IsBreakGlass := by
  intro l hl
  simp only [gLockRun, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h | h | h <;> subst h <;> exact fun h => h

private lemma gLock_ctmInv : CtmInv gWorld gLock.ts.sys.ctm :=
  step_inv (InitSatisfiesInvariant gWorld 100 (by decide))
    (CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))

/-- Chain `0` is locked in `gLock` whenever release `200`'s verifier fails the gate. -/
private lemma gLock_locked (rv : Address → Address)
    (h : ¬ IsMulti { gCfg with relVerifier := rv } (rv 200)) :
    Locked { gCfg with relVerifier := rv } gLock 0 1 := by
  refine ⟨⟨_, rfl, rfl⟩, rfl, by decide, rfl, rfl, h, fun w hw => ?_, rfl⟩
  have hw2 : 2 ≤ w := hw
  have hw1 : w ≠ 1 := by omega
  show upd (fun _ => (0 : Address)) 1 300 w = 0
  simp [upd, hw1]

/-- Every flagged chain of `gLock` is on the multi-proof verifier `700`. -/
private lemma gLock_gateInv (rv : Address → Address) :
    GateInv { gCfg with relVerifier := rv } gLock := by
  intro id hf
  by_cases h0 : id = 0
  · subst h0
    exact multi_700 rv
  · exfalso
    have hfalse : (gLock.gate id).flag = false := by
      by_cases h1 : id = 1
      · subst h1
        rfl
      · simp [gLock, upd, h0, h1]
    rw [hfalse] at hf
    cases hf

/-- The routing transition of chains `0` and `1` across `300` in `gLock`. -/
private lemma gLock_transition (id : ChainId) (hid : id = 0 ∨ id = 1) :
    ∃ sys', Step gWorld gLockSys (.transition id) sys' := by
  rcases hid with rfl | rfl
  · exact ⟨_, Step.transition (s := gLockSys) (id := 0) rfl (by decide) rfl
      (applyDerived_rows_eq gNodup100 gNodup200) (by decide)⟩
  · exact ⟨_, Step.transition (s := gLockSys) (id := 1) rfl (by decide) rfl
      (applyDerived_rows_eq gNodup100 gNodup200) (by decide)⟩

/-! ## The emergency switch and the CTM -/

theorem EmergencyOffDoesNotBlockUpgrades : Properties.EmergencyOffDoesNotBlockUpgrades := by
  intro G s id path caller τ d
  have hflag : ((s.withMask id d).gate id).flag = (s.gate id).flag := by
    simp [GSys.withMask, upd_same]
  constructor
  · rintro ⟨s', h⟩
    cases h with
    | upgrade ht hg =>
        refine ⟨_, GStep.upgrade (s := s.withMask id d) ht ?_⟩
        rw [hflag]
        exact hg
  · rintro ⟨s', h⟩
    cases h with
    | upgrade ht hg =>
        rw [hflag] at hg
        exact ⟨_, GStep.upgrade (s := s) ht hg⟩

theorem CommitIgnoresProofMode : Properties.CommitIgnoresProofMode := by
  intro G s s' op
  refine ⟨⟨fun h => ?_, ?_⟩, fun pm rv => ⟨fun h => ?_, fun h => ?_⟩⟩
  · cases h with
    | other _ ht =>
        cases ht with
        | base _ hs =>
            cases hs with
            | ctm hc => exact ⟨_, hc, rfl⟩
  · rintro ⟨c', hc, rfl⟩
    exact GStep.other True.intro (TimedStep.base (fun h => h) (Step.ctm hc))
  · cases h with
    | other hf ht => exact GStep.other hf ht
  · cases h with
    | other hf ht => exact GStep.other hf ht

/-! ## The repaired characterisation -/

theorem UpgradeChainEnabledIffTimedV35 : Properties.UpgradeChainEnabledIffTimedV35 := by
  intro G s id t caller τ
  have hev : s.ts.sys.ctm.ut (G.T.X.W.tr t).old = t →
      edgeVerifier G s (departure G.T.X.W (.executor t)) =
        G.relVerifier (G.T.X.W.tr t).newRel := by
    intro hut
    simp only [edgeVerifier, departure, Sys.edge]
    rw [hut]
  constructor
  · rintro ⟨s', h⟩
    cases h with
    | upgrade ht hg =>
        obtain ⟨hc, hut, hown, hch, hts, hb, hsl, hstep⟩ :=
          (UpgradeChainEnabledIffTimed G.T s.ts id t caller τ).mp ⟨_, ht⟩
        rw [hev hut] at hg
        exact ⟨hc, hut, hown, hch, hts, hb, hsl, hstep, hg.nonzero, hg.setVerifier⟩
  · rintro ⟨hc, hut, hown, hch, hts, hb, hsl, hstep, hnz, hm⟩
    obtain ⟨ts', ht⟩ := (UpgradeChainEnabledIffTimed G.T s.ts id t caller τ).mpr
      ⟨hc, hut, hown, hch, hts, hb, hsl, hstep⟩
    refine ⟨_, GStep.upgrade ht ?_⟩
    rw [hev hut]
    exact ⟨hnz, hm, hm⟩

/-- `upgradeChain(300, id)` by the chain's admin at time `10` in `gLock`, for chains `0` and `1`,
once the verifier checks on release `200`'s verifier pass. -/
private lemma gLock_exec (rv : Address → Address) (id : ChainId) (hid : id = 0 ∨ id = 1)
    (hnz : rv 200 ≠ 0)
    (hm : (gLock.gate id).flag = true → IsMulti { gCfg with relVerifier := rv } (rv 200)) :
    ∃ s', GStep { gCfg with relVerifier := rv } gLock (.upgrade id (.executor 300) 3 10) s' := by
  have haux : gLock.ts.aux id = wTimingAux := by
    rcases hid with rfl | rfl <;> rfl
  have hch : gLock.ts.sys.chains id = some ⟨1, rowsRouting (wRows 100)⟩ := by
    rcases hid with rfl | rfl <;> rfl
  refine (UpgradeChainEnabledIffTimedV35 _ gLock id 300 3 10).mpr
    ⟨Or.inr (by rw [haux]; rfl), rfl, rfl, ⟨_, hch, rfl⟩, ?_, (by rw [haux]; rfl), ?_,
      gLock_transition id hid, hnz, hm⟩
  · show (wTimingSched 300).upgradeTimestamp ≤ 10
    decide
  · intro w hw
    rw [haux] at hw
    cases hw

theorem EmergencyOffFlaggedChainStillUpgrades :
    Properties.EmergencyOffFlaggedChainStillUpgrades := by
  refine ⟨_, GStep.setProofSystemStatus (id := 0) (c := ⟨1, rowsRouting (wRows 100)⟩) rfl rfl,
    rfl, rfl, by decide, by decide, ?_⟩
  exact (EmergencyOffDoesNotBlockUpgrades gCfgMulti gLock 0 (.executor 300) 3 10 _).mp
    (gLock_exec (fun _ => 700) 0 (Or.inl rfl) (by decide) (fun _ => multi_700 _))

/-! ## Locked chains -/

/-- The part of `Locked` that is about the CTM's version state. -/
private def LockedCtm (G : GateConfig) (c : CTM) (v : ℕ) : Prop :=
  c.ut v ≠ 0 ∧ (G.T.X.W.tr (c.ut v)).new = c.pv ∧ (G.T.X.W.tr (c.ut v)).newRel = c.cur ∧
    ¬ IsMulti G (G.relVerifier c.cur) ∧ (∀ w, c.pv ≤ w → c.ut w = 0) ∧
    c.legacy v = LegacyCut.none

private lemma locked_iff {G : GateConfig} {s : GSys} {id : ChainId} {v : ℕ} :
    Locked G s id v ↔ (∃ c, s.ts.sys.chains id = some c ∧ c.pv = v) ∧
      (s.gate id).flag = true ∧ LockedCtm G s.ts.sys.ctm v :=
  ⟨fun h => ⟨h.chain, h.flagged, h.committed, h.targetVersion, h.targetRelease, h.notMulti,
      h.noSlotsAhead, h.noLegacy⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

private lemma locked_no_upgrade {G : GateConfig} {s : GSys} {id : ChainId} {v : ℕ}
    (hL : Locked G s id v) (path : UpgradePath) (caller : Address) (τ : ℕ) (s' : GSys) :
    ¬ GStep G s (.upgrade id path caller τ) s' := by
  intro h
  obtain ⟨c, hc, rfl⟩ := hL.chain
  have hm := (upgrade_gate h hc).setVerifier hL.flagged
  rw [hL.targetRelease] at hm
  exact hL.notMulti hm

theorem LockedChainCannotUpgrade : Properties.LockedChainCannotUpgrade :=
  fun _ _ _ _ hL path caller τ s' => locked_no_upgrade hL path caller τ s'

theorem ReplacementAtCurrentVersionIsPinned : Properties.ReplacementAtCurrentVersionIsPinned := by
  intro W c c' e r h hpv
  cases h with
  | replace _ _ _ _ _ _ hpin _ => exact hpin hpv

/-- A CTM writer that does not move the CTM's version keeps the CTM part of `Locked`. -/
private lemma lockedCtm_cstep {G : GateConfig} {c c' : CTM} {v : ℕ} {op : Op}
    (hL : LockedCtm G c v) (h : CStep G.T.X.W c op c') (hne : op.isEdge ≠ true) :
    LockedCtm G c' v := by
  obtain ⟨hcm, htv, htr, hnm, hns, hnl⟩ := hL
  cases h with
  | commit _ _ _ _ _ _ => exact absurd rfl hne
  | legacyCommit _ _ => exact absurd rfl hne
  | @replace e r he hr hut hre hfrom hle hpin honward =>
      have heold : ¬ c.pv ≤ (G.T.X.W.tr e).old := fun hle' => he (by
        rw [← hut]
        exact hns _ hle')
      by_cases hev : (G.T.X.W.tr e).old = v
      · have hee : c.ut v = e := by
          rw [← hev]
          exact hut
        rw [hee] at htv
        have hnew : (G.T.X.W.tr r).new = c.pv := by
          by_contra hne'
          exact (honward hne').1 (hns _ (by omega))
        refine ⟨?_, ?_, ?_, hnm, fun w hw => ?_, hnl⟩
        · show upd c.ut (G.T.X.W.tr e).old r v ≠ 0
          rw [hev, upd_same]
          exact hr
        · show (G.T.X.W.tr (upd c.ut (G.T.X.W.tr e).old r v)).new = c.pv
          rw [hev, upd_same]
          exact hnew
        · show (G.T.X.W.tr (upd c.ut (G.T.X.W.tr e).old r v)).newRel = c.cur
          rw [hev, upd_same]
          exact hpin hnew
        · have hw' : c.pv ≤ w := hw
          have hwe : w ≠ (G.T.X.W.tr e).old := by omega
          show upd c.ut (G.T.X.W.tr e).old r w = 0
          rw [upd_ne _ _ hwe]
          exact hns w hw
      · have hve : v ≠ (G.T.X.W.tr e).old := fun h => hev h.symm
        have hutv : upd c.ut (G.T.X.W.tr e).old r v = c.ut v := upd_ne _ _ hve
        refine ⟨?_, ?_, ?_, hnm, fun w hw => ?_, hnl⟩
        · show upd c.ut (G.T.X.W.tr e).old r v ≠ 0
          rw [hutv]
          exact hcm
        · show (G.T.X.W.tr (upd c.ut (G.T.X.W.tr e).old r v)).new = c.pv
          rw [hutv]
          exact htv
        · show (G.T.X.W.tr (upd c.ut (G.T.X.W.tr e).old r v)).newRel = c.cur
          rw [hutv]
          exact htr
        · have hw' : c.pv ≤ w := hw
          have hwe : w ≠ (G.T.X.W.tr e).old := by omega
          show upd c.ut (G.T.X.W.tr e).old r w = 0
          rw [upd_ne _ _ hwe]
          exact hns w hw
  | @legacyRecut v' hut hleg =>
      have hvv : v ≠ v' := fun h => hcm (h ▸ hut)
      refine ⟨hcm, htv, htr, hnm, hns, ?_⟩
      show upd c.legacy v' LegacyCut.opaque v = LegacyCut.none
      rw [upd_ne _ _ hvv]
      exact hnl

/-- A step other than an escape keeps a locked chain locked. -/
private lemma locked_step {G : GateConfig} {s s' : GSys} {l : GLabel} {id : ChainId} {v : ℕ}
    (hL : Locked G s id v) (h : GStep G s l s') (hne : ¬ l.Escapes id) : Locked G s' id v := by
  obtain ⟨⟨c, hc, rfl⟩, hf, hLc⟩ := locked_iff.mp hL
  have hup : ∀ path caller τ, l ≠ .upgrade id path caller τ := by
    rintro path caller τ rfl
    exact locked_no_upgrade hL _ _ _ _ h
  have hbg : ¬ l.BreakGlassOf id := fun hb => hne (by
    cases l <;> first | exact hb | exact False.elim hb)
  obtain ⟨hc', hf', hctm⟩ := gstep_view h hc hf hLc.2.2.2.2.2 hbg hup
  refine locked_iff.mpr ⟨⟨c, hc', rfl⟩, hf', ?_⟩
  rcases hctm with hctm | ⟨op, rfl, hcs⟩
  · rw [hctm]
    exact hLc
  · exact lockedCtm_cstep hLc hcs hne

theorem LockHoldsUntilAnEscape : Properties.LockHoldsUntilAnEscape := by
  intro G s s' ls id v hL hrun hne
  induction hrun with
  | nil => exact hL
  | cons hs _ ih =>
      exact ih (locked_step hL hs (hne _ (by simp)))
        (fun l hl => hne l (List.mem_cons_of_mem _ hl))

theorem LockedChainNeedsDeadlineOverride : Properties.LockedChainNeedsDeadlineOverride := by
  intro G d s id v τ hL
  refine ⟨fun hd hlt hact => ?_, fun x hx => ?_⟩
  · have h1 : versionDeadline G.T d s.ts.sys.ctm v =
        some (G.T.sched (s.ts.sys.ctm.ut v)).deadline := by
      simp [versionDeadline, hd, hL.committed]
    have := hact _ h1
    omega
  · have h1 : versionDeadline G.T (upd d v x) s.ts.sys.ctm v = some x := by
      simp [versionDeadline, upd_same, hx]
    constructor
    · intro hact
      exact hact _ h1
    · intro hle y hy
      rw [h1] at hy
      cases hy
      exact hle

/-! ## Stuck chains -/

/-- The part of `Stuck` that is about the CTM's version state. -/
private def StuckCtm (G : GateConfig) (c : CTM) (v : ℕ) : Prop :=
  c.ut v ≠ 0 ∧ CtmInv G.T.X.W c ∧
    (∀ w, (G.T.X.W.tr (c.ut v)).new ≤ w → c.relAt w ≠ 0 →
      ¬ IsMulti G (G.relVerifier (c.relAt w))) ∧
    c.legacy v = LegacyCut.none

private lemma stuck_iff {G : GateConfig} {s : GSys} {id : ChainId} {v : ℕ} :
    Stuck G s id v ↔ (∃ c, s.ts.sys.chains id = some c ∧ c.pv = v) ∧
      (s.gate id).flag = true ∧ StuckCtm G s.ts.sys.ctm v :=
  ⟨fun h => ⟨h.chain, h.flagged, h.committed, h.inv, h.noMultiAhead, h.noLegacy⟩,
    fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩⟩

private lemma stuck_no_upgrade {G : GateConfig} {s : GSys} {id : ChainId} {v : ℕ}
    (hS : Stuck G s id v) (path : UpgradePath) (caller : Address) (τ : ℕ) (s' : GSys) :
    ¬ GStep G s (.upgrade id path caller τ) s' := by
  intro h
  obtain ⟨c, hc, rfl⟩ := hS.chain
  obtain ⟨-, -, -, -, hnr, hnz⟩ := hS.inv.slots c.pv hS.committed
  have hm := (upgrade_gate h hc).setVerifier hS.flagged
  rw [hnr] at hm
  exact hS.noMultiAhead _ le_rfl hnz hm

theorem StuckChainCannotUpgrade : Properties.StuckChainCannotUpgrade :=
  fun _ _ _ _ hS path caller τ s' => stuck_no_upgrade hS path caller τ s'

theorem LockedIsStuck : Properties.LockedIsStuck := by
  intro G s hI
  have hns : ∀ w, s.ts.sys.ctm.pv ≤ w → s.ts.sys.ctm.ut w = 0 := by
    intro w hw
    by_contra h
    have := (hI.slots w h).1
    omega
  refine ⟨hns, fun id v hL => ⟨hL.chain, hL.flagged, hL.committed, hI, ?_, hL.noLegacy⟩⟩
  intro w hw hrel
  have hle := (hI.relAtSound w hrel).1
  rw [hL.targetVersion] at hw
  have hwe : w = s.ts.sys.ctm.pv := le_antisymm hle hw
  rw [hwe, hI.curAtVersion]
  exact hL.notMulti

theorem ReplacementLandsOnAnInstalledRelease :
    Properties.ReplacementLandsOnAnInstalledRelease := by
  intro W c c' e r hI h
  cases h with
  | replace he hr hut hre hfrom hle hpin honward =>
      refine ⟨hle, ?_⟩
      by_cases hpv : (W.tr r).new = c.pv
      · refine ⟨?_, ?_, rfl⟩
        · rw [hpv, hI.curAtVersion]
          exact hI.curNonzero
        · rw [hpin hpv, hpv, hI.curAtVersion]
      · obtain ⟨hnz, hrel⟩ := honward hpv
        obtain ⟨-, hfrom', hnz', -⟩ := hI.slots _ hnz
        exact ⟨hnz', by rw [hrel, hfrom'], rfl⟩

/-- A CTM writer that installs no release passing the gate keeps the CTM part of `Stuck`. -/
private lemma stuckCtm_cstep {G : GateConfig} {c c' : CTM} {v : ℕ} {op : Op}
    (hS : StuckCtm G c v) (h : CStep G.T.X.W c op c')
    (hne : ¬ (GLabel.other (.base (.ctm op))).InstallsMulti G) : StuckCtm G c' v := by
  obtain ⟨hcm, hI, hnm, hnl⟩ := hS
  have hI' := step_inv hI h
  have hvlt : v < c.pv := (hI.slots v hcm).1
  cases h with
  | @commit t ht hfrom hpv hlt hnr hrv =>
      have hvt : v ≠ (G.T.X.W.tr t).old := by omega
      have hutv : upd c.ut (G.T.X.W.tr t).old t v = c.ut v := upd_ne _ _ hvt
      refine ⟨?_, hI', fun w hw hrel => ?_, hnl⟩
      · show upd c.ut (G.T.X.W.tr t).old t v ≠ 0
        rw [hutv]
        exact hcm
      · have hw' : (G.T.X.W.tr (upd c.ut (G.T.X.W.tr t).old t v)).new ≤ w := hw
        rw [hutv] at hw'
        have hrel' : upd c.relAt (G.T.X.W.tr t).new (G.T.X.W.tr t).newRel w ≠ 0 := hrel
        show ¬ IsMulti G
          (G.relVerifier (upd c.relAt (G.T.X.W.tr t).new (G.T.X.W.tr t).newRel w))
        by_cases hwn : w = (G.T.X.W.tr t).new
        · rw [hwn, upd_same]
          exact hne
        · rw [upd_ne _ _ hwn] at hrel' ⊢
          exact hnm w hw' hrel'
  | @legacyCommit R b hR hlt =>
      refine ⟨hcm, hI', fun w hw hrel => ?_, ?_⟩
      · have hrel' : upd c.relAt (G.T.X.W.relVersion R) R w ≠ 0 := hrel
        show ¬ IsMulti G (G.relVerifier (upd c.relAt (G.T.X.W.relVersion R) R w))
        by_cases hwn : w = G.T.X.W.relVersion R
        · rw [hwn, upd_same]
          exact hne
        · rw [upd_ne _ _ hwn] at hrel' ⊢
          exact hnm w hw hrel'
      · have hvp : v ≠ c.pv := by omega
        show upd c.legacy c.pv _ v = LegacyCut.none
        rw [upd_ne _ _ hvp]
        exact hnl
  | @replace e r he hr hut hre hfrom hle hpin honward =>
      by_cases hev : (G.T.X.W.tr e).old = v
      · have hee : c.ut v = e := by
          rw [← hev]
          exact hut
        refine ⟨?_, hI', fun w hw hrel => ?_, hnl⟩
        · show upd c.ut (G.T.X.W.tr e).old r v ≠ 0
          rw [hev, upd_same]
          exact hr
        · have hw' : (G.T.X.W.tr (upd c.ut (G.T.X.W.tr e).old r v)).new ≤ w := hw
          rw [hev, upd_same] at hw'
          refine hnm w ?_ hrel
          rw [hee]
          exact le_trans hle hw'
      · have hve : v ≠ (G.T.X.W.tr e).old := fun h => hev h.symm
        have hutv : upd c.ut (G.T.X.W.tr e).old r v = c.ut v := upd_ne _ _ hve
        refine ⟨?_, hI', fun w hw hrel => ?_, hnl⟩
        · show upd c.ut (G.T.X.W.tr e).old r v ≠ 0
          rw [hutv]
          exact hcm
        · have hw' : (G.T.X.W.tr (upd c.ut (G.T.X.W.tr e).old r v)).new ≤ w := hw
          rw [hutv] at hw'
          exact hnm w hw' hrel
  | @legacyRecut v' hut hleg =>
      have hvv : v ≠ v' := fun h => hcm (h ▸ hut)
      refine ⟨hcm, hI', hnm, ?_⟩
      show upd c.legacy v' LegacyCut.opaque v = LegacyCut.none
      rw [upd_ne _ _ hvv]
      exact hnl

/-- A step that is neither a break-glass cut of the chain nor installs a release passing the gate
keeps a stuck chain stuck. -/
private lemma stuck_step {G : GateConfig} {s s' : GSys} {l : GLabel} {id : ChainId} {v : ℕ}
    (hS : Stuck G s id v) (h : GStep G s l s') (hbg : ¬ l.BreakGlassOf id)
    (hnm : ¬ l.InstallsMulti G) : Stuck G s' id v := by
  obtain ⟨⟨c, hc, rfl⟩, hf, hSc⟩ := stuck_iff.mp hS
  have hup : ∀ path caller τ, l ≠ .upgrade id path caller τ := by
    rintro path caller τ rfl
    exact stuck_no_upgrade hS _ _ _ _ h
  obtain ⟨hc', hf', hctm⟩ := gstep_view h hc hf hSc.2.2.2 hbg hup
  refine stuck_iff.mpr ⟨⟨c, hc', rfl⟩, hf', ?_⟩
  rcases hctm with hctm | ⟨op, rfl, hcs⟩
  · rw [hctm]
    exact hSc
  · exact stuckCtm_cstep hSc hcs hnm

theorem StuckUntilMultiReleaseOrBreakGlass : Properties.StuckUntilMultiReleaseOrBreakGlass := by
  intro G s s' ls id v hS hrun hne
  induction hrun with
  | nil => exact hS
  | cons hs _ ih =>
      exact ih (stuck_step hS hs (hne _ (by simp)).1 (hne _ (by simp)).2)
        (fun l hl => hne l (List.mem_cons_of_mem _ hl))


/-! ## The e561 statements fail -/

theorem UpgradeChainEnabledIffTimedFailsV35 : Properties.UpgradeChainEnabledIffTimedFailsV35 := by
  intro H
  obtain ⟨s', h⟩ := (H gCfg gLock 0 300 3 10).mpr
    ⟨Or.inr rfl, rfl, rfl, ⟨_, rfl, rfl⟩, (by decide), rfl, (fun w hw => by cases hw),
      gLock_transition 0 (Or.inl rfl)⟩
  exact locked_no_upgrade (gLock_locked gRelVerifier (not_multi_701 _)) _ _ _ _ h

theorem UpgradesStayEnabledFailsV35 : Properties.UpgradesStayEnabledFailsV35 := by
  intro H
  obtain ⟨path, caller, τ, s'', h⟩ := H gCfg gSys0 gLock gLockRun
    (FreshSystemSatisfiesInvariant gWorld 100 (by decide))
    (fun id c hc => by cases hc) gLock_run_gCfg gLockRun_no_breakGlass
    0 ⟨1, rowsRouting (wRows 100)⟩ rfl (by decide) gNodup200 rfl rfl
  exact locked_no_upgrade (gLock_locked gRelVerifier (not_multi_701 _)) _ _ _ _ h

/-! ## A gated run is a timed run -/

private lemma gatedTimedRun_append {T : TimedConfig} {s s' s'' : TimedSys}
    {l1 l2 : List TimedLabel} (h1 : TimedRun T s l1 s') (h2 : TimedRun T s' l2 s'') :
    TimedRun T s (l1 ++ l2) s'' := by
  induction h1 with
  | nil => exact h2
  | cons hs _ ih => exact TimedRun.cons hs (ih h2)

/-- One gated step is its timed image. -/
private lemma gstep_timed {G : GateConfig} {s s' : GSys} {l : GLabel} (h : GStep G s l s') :
    TimedRun G.T s.ts l.timed s'.ts := by
  cases h with
  | upgrade ht _ => exact TimedRun.cons ht TimedRun.nil
  | genesis ht _ => exact TimedRun.cons ht TimedRun.nil
  | migrateIn ht _ => exact TimedRun.cons ht TimedRun.nil
  | bootstrapReset _ _ ht _ => exact TimedRun.cons ht TimedRun.nil
  | breakGlass ht _ => exact TimedRun.cons ht TimedRun.nil
  | other _ ht => exact TimedRun.cons ht TimedRun.nil
  | requireSecondProof _ _ _ _ _ => exact TimedRun.nil
  | setProofSystemStatus _ _ => exact TimedRun.nil

theorem GatedRunIsATimedRun : Properties.GatedRunIsATimedRun := by
  intro G s s' ls h
  induction h with
  | nil => exact TimedRun.nil
  | cons hs _ ih =>
      rw [List.flatMap_cons]
      exact gatedTimedRun_append (gstep_timed hs) ih

/-- The routing labels of a gated run with no break-glass cut include no break-glass cut. -/
private lemma grun_untimed_not_arbitrary {G : GateConfig} {s s' : GSys} {ls : List GLabel}
    (h : GRun G s ls s') (hbg : ∀ l ∈ ls, ¬ l.IsBreakGlass) :
    ∀ x ∈ (ls.flatMap GLabel.timed).flatMap TimedLabel.untimed, ¬ x.isArbitrary := by
  induction h with
  | nil => intro x hx; simp at hx
  | @cons s0 s1 s2 l ls hs _ ih =>
      intro x hx
      rw [List.flatMap_cons, List.flatMap_append] at hx
      rcases List.mem_append.mp hx with hx | hx
      · have hl := hbg l List.mem_cons_self
        cases hs with
        | upgrade _ _ =>
            simp only [GLabel.timed, TimedLabel.untimed, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_singleton] at hx
            subst hx
            exact fun h => h
        | genesis _ _ =>
            simp only [GLabel.timed, TimedLabel.untimed, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_singleton] at hx
            subst hx
            exact fun h => h
        | migrateIn _ _ =>
            simp only [GLabel.timed, TimedLabel.untimed, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_singleton] at hx
            subst hx
            exact fun h => h
        | bootstrapReset _ _ _ _ =>
            simp only [GLabel.timed, TimedLabel.untimed, List.flatMap_cons, List.flatMap_nil,
              List.append_nil, List.mem_singleton] at hx
            subst hx
            exact fun h => h
        | breakGlass _ _ => exact absurd trivial hl
        | @other l' _ hfree _ =>
            cases l' with
            | upgrade _ _ _ _ => exact absurd hfree id
            | base b =>
                cases b with
                | ctm op =>
                    simp only [GLabel.timed, TimedLabel.untimed, List.flatMap_cons,
                      List.flatMap_nil, List.append_nil, List.mem_singleton] at hx
                    subst hx
                    exact fun h => h
                | genesis _ => exact absurd hfree id
                | migrateIn _ => exact absurd hfree id
                | transition _ => exact absurd hfree id
                | bootstrapReset _ => exact absurd hfree id
                | arbitraryCut _ _ _ => exact absurd hfree id
            | setUpgradeTimestamp _ _ _ => simp [GLabel.timed, TimedLabel.untimed] at hx
            | swapNotifier _ => simp [GLabel.timed, TimedLabel.untimed] at hx
            | setAux _ _ => simp [GLabel.timed, TimedLabel.untimed] at hx
        | requireSecondProof _ _ _ _ _ => simp [GLabel.timed] at hx
        | setProofSystemStatus _ _ => simp [GLabel.timed] at hx
      · exact ih (fun l hl => hbg l (List.mem_cons_of_mem _ hl)) x hx

/-! ## The release policy -/

/-- A step that writes only gate fields keeps `PolicyInv` when the written chain's verifier is
unchanged and the new record passes the gate. -/
private lemma policyInv_gate_only {G : GateConfig} {s : GSys} (hP : PolicyInv G s) (i : ChainId)
    (g : GateState) (hv : g.verifier = (s.gate i).verifier)
    (hg : g.flag = true → IsMulti G g.verifier) :
    PolicyInv G ⟨s.ts, upd s.gate i g⟩ := by
  refine ⟨hP.sys, gateInv_upd hP.gate i g hg, fun id c hc hrel => ?_, hP.slotsKeep⟩
  by_cases hid : id = i
  · subst hid
    show (upd s.gate id g id).verifier = _
    rw [upd_same, hv]
    exact hP.onRelease id c hc hrel
  · show (upd s.gate i g id).verifier = _
    rw [upd_ne _ _ hid]
    exact hP.onRelease id c hc hrel

/-- **One step of a policy-respecting run keeps `PolicyInv`.** -/
private lemma policyInv_step {G : GateConfig} {s s' : GSys} {l : GLabel} (hM : MaskMonotone G)
    (hP : PolicyInv G s) (h : GStep G s l s') (hbg : ¬ l.IsBreakGlass)
    (hpol : l.PassesReleasePolicy G) : PolicyInv G s' := by
  have hC : CtmInv G.T.X.W s.ts.sys.ctm := hP.sys.1
  cases h with
  | @upgrade id path caller τ ts' ht hg =>
      obtain ⟨_, sys', d, rfl⟩ := timed_upgrade_inv ht
      obtain ⟨c0, hc0, hv0⟩ := d.atVersion
      have hroute := d.routing
      have hsys' := step_sysInv hP.sys hroute (fun h => h)
      cases hroute with
      | @transition _ c ρ hc hut hguard happ hlt =>
          have hcc : c0 = c := Option.some.inj (hc0.symm.trans hc)
          subst hcc
          refine ⟨hsys', gateInv_upd hP.gate id _ hg.setVerifier, ?_, hP.slotsKeep⟩
          intro id' c' hc' hrel'
          by_cases hid : id' = id
          · subst hid
            have hc'' : c' = ⟨(s.ts.sys.edge G.T.X.W c0.pv).new, ρ⟩ := by
              have := hc'
              simp only [upd_same, Option.some.injEq] at this
              exact this.symm
            subst hc''
            obtain ⟨-, -, -, -, hnr, -, -⟩ := edge_facts hC hut
            show (upd s.gate id' _ id').verifier = _
            rw [upd_same]
            show G.relVerifier (s.ts.sys.edge G.T.X.W (departure G.T.X.W path)).newRel = _
            rw [← hv0]
            exact congrArg G.relVerifier hnr
          · have hc'' : s.ts.sys.chains id' = some c' := by
              have := hc'
              simp only [upd_ne _ _ hid] at this
              exact this
            show (upd s.gate id _ id').verifier = _
            rw [upd_ne _ _ hid]
            exact hP.onRelease id' c' hc'' hrel'
  | @genesis id ts' ht hv =>
      obtain ⟨sys', hs, rfl⟩ := timed_base_inv ht
      have hsys' := step_sysInv hP.sys hs (fun h => h)
      cases hs with
      | @genesis _ ρ hnone hadd =>
          refine ⟨hsys', gateInv_upd hP.gate id _ (fun hf => by simp [freshGate] at hf), ?_,
            hP.slotsKeep⟩
          intro id' c' hc' hrel'
          by_cases hid : id' = id
          · subst hid
            have hc'' : c' = ⟨s.ts.sys.ctm.pv, ρ⟩ := by
              have := hc'
              simp only [upd_same, Option.some.injEq] at this
              exact this.symm
            subst hc''
            show (upd s.gate id' _ id').verifier = _
            rw [upd_same]
            show G.relVerifier s.ts.sys.ctm.cur = G.relVerifier (s.ts.sys.ctm.relAt s.ts.sys.ctm.pv)
            rw [hC.curAtVersion]
          · have hc'' : s.ts.sys.chains id' = some c' := by
              have := hc'
              simp only [upd_ne _ _ hid] at this
              exact this
            show (upd s.gate id _ id').verifier = _
            rw [upd_ne _ _ hid]
            exact hP.onRelease id' c' hc'' hrel'
  | @migrateIn id ts' ht hv =>
      obtain ⟨sys', hs, rfl⟩ := timed_base_inv ht
      have hsys' := step_sysInv hP.sys hs (fun h => h)
      cases hs with
      | @migrateIn _ ρ v hvv hnone hadd =>
          refine ⟨hsys', gateInv_upd hP.gate id _ (fun hf => by simp [freshGate] at hf), ?_,
            hP.slotsKeep⟩
          intro id' c' hc' hrel'
          by_cases hid : id' = id
          · subst hid
            have hc'' : c' = ⟨v, ρ⟩ := by
              have := hc'
              simp only [upd_same, Option.some.injEq] at this
              exact this.symm
            subst hc''
            subst hvv
            show (upd s.gate id' _ id').verifier = _
            rw [upd_same]
            show G.relVerifier s.ts.sys.ctm.cur = G.relVerifier (s.ts.sys.ctm.relAt s.ts.sys.ctm.pv)
            rw [hC.curAtVersion]
          · have hc'' : s.ts.sys.chains id' = some c' := by
              have := hc'
              simp only [upd_ne _ _ hid] at this
              exact this
            show (upd s.gate id _ id').verifier = _
            rw [upd_ne _ _ hid]
            exact hP.onRelease id' c' hc'' hrel'
  | @bootstrapReset id c0 R ts' hc0 hleg ht hg =>
      obtain ⟨sys', hs, rfl⟩ := timed_base_inv ht
      have hsys' := step_sysInv hP.sys hs (fun h => h)
      cases hs with
      | @bootstrapReset _ c R' ρ hc hleg' hadd hlt =>
          have hcc : c0 = c := Option.some.inj (hc0.symm.trans hc)
          subst hcc
          have hRR : R' = R := by
            rw [hleg] at hleg'
            cases hleg'
            rfl
          subst hRR
          refine ⟨hsys', gateInv_upd hP.gate id _ hg.setVerifier, ?_, hP.slotsKeep⟩
          intro id' c' hc' hrel'
          by_cases hid : id' = id
          · subst hid
            have hc'' : c' = ⟨G.T.X.W.relVersion R', ρ⟩ := by
              have := hc'
              simp only [upd_same, Option.some.injEq] at this
              exact this.symm
            subst hc''
            obtain ⟨-, hrel, -⟩ := hC.bootstraps _ R' hleg
            show (upd s.gate id' _ id').verifier = _
            rw [upd_same]
            show G.relVerifier R' = G.relVerifier (s.ts.sys.ctm.relAt (G.T.X.W.relVersion R'))
            rw [hrel]
          · have hc'' : s.ts.sys.chains id' = some c' := by
              have := hc'
              simp only [upd_ne _ _ hid] at this
              exact this
            show (upd s.gate id _ id').verifier = _
            rw [upd_ne _ _ hid]
            exact hP.onRelease id' c' hc'' hrel'
  | breakGlass _ _ => exact absurd trivial hbg
  | @other l' ts' hfree ht =>
      cases ht with
      | direct _ => exact absurd hfree id
      | ctm _ _ => exact absurd hfree id
      | executor _ _ _ _ => exact absurd hfree id
      | @base lb sys' hnt hs =>
          have hsys' := step_sysInv hP.sys hs (by
            cases lb with
            | arbitraryCut _ _ _ => exact absurd hfree id
            | _ => exact fun h => h)
          cases hs with
          | @ctm _ c' hcs =>
              have hlow := cstep_relAt_low hcs
              refine ⟨hsys', hP.gate, fun id c hc hrel => ?_, ?_⟩
              · have hle : c.pv ≤ s.ts.sys.ctm.pv := (hP.sys.2 id c hc).1
                have hrel0 : s.ts.sys.ctm.relAt c.pv ≠ 0 := by
                  rw [← hlow c.pv hle]
                  exact hrel
                show (s.gate id).verifier = G.relVerifier (c'.relAt c.pv)
                rw [hlow c.pv hle]
                exact hP.onRelease id c hc hrel0
              · intro v hv
                cases hcs with
                | @commit t ht0 hfrom hpv hlt hnr hrv =>
                    show KeepsProofMode G (upd s.ts.sys.ctm.ut (G.T.X.W.tr t).old t v)
                    have hv' : upd s.ts.sys.ctm.ut (G.T.X.W.tr t).old t v ≠ 0 := hv
                    by_cases hvt : v = (G.T.X.W.tr t).old
                    · subst hvt
                      rw [upd_same]
                      exact hpol
                    · rw [upd_ne _ _ hvt] at hv' ⊢
                      exact hP.slotsKeep v hv'
                | @replace e r he hr hut hre hfrom hle hpin honward =>
                    show KeepsProofMode G (upd s.ts.sys.ctm.ut (G.T.X.W.tr e).old r v)
                    have hv' : upd s.ts.sys.ctm.ut (G.T.X.W.tr e).old r v ≠ 0 := hv
                    by_cases hve : v = (G.T.X.W.tr e).old
                    · subst hve
                      rw [upd_same]
                      exact hpol
                    · rw [upd_ne _ _ hve] at hv' ⊢
                      exact hP.slotsKeep v hv'
                | legacyCommit _ _ => exact hP.slotsKeep v hv
                | legacyRecut _ _ => exact hP.slotsKeep v hv
          | genesis _ _ => exact absurd hfree id
          | migrateIn _ _ _ _ => exact absurd hfree id
          | transition _ _ _ _ _ => exact absurd hfree id
          | bootstrapReset _ _ _ _ => exact absurd hfree id
          | arbitraryCut _ _ _ => exact absurd hfree id
      | setUpgradeTimestamp _ _ _ _ => exact ⟨hP.sys, hP.gate, hP.onRelease, hP.slotsKeep⟩
      | swapNotifier => exact ⟨hP.sys, hP.gate, hP.onRelease, hP.slotsKeep⟩
      | setAux => exact ⟨hP.sys, hP.gate, hP.onRelease, hP.slotsKeep⟩
  | @requireSecondProof id caller c0 hc0 hcaller hsl hfl hmode =>
      exact policyInv_gate_only hP id _ rfl (fun _ => hM _ _ hmode)
  | @setProofSystemStatus id caller enabled c0 hc0 hcaller =>
      exact policyInv_gate_only hP id _ rfl (fun hf => hP.gate id hf)

/-- Under `PolicyInv`, a flagged chain at a version with a committed edge passes the edge's flag
check. -/
private lemma policy_edge_multi {G : GateConfig} {s : GSys} (hP : PolicyInv G s) {id : ChainId}
    {c : Chain} (hc : s.ts.sys.chains id = some c) (hut : s.ts.sys.ctm.ut c.pv ≠ 0)
    (hf : (s.gate id).flag = true) : IsMulti G (edgeVerifier G s c.pv) := by
  obtain ⟨hfrom, hrz, -⟩ := edge_facts hP.sys.1 hut
  have hm := hP.gate id hf
  rw [hP.onRelease id c hc hrz] at hm
  have hk := hP.slotsKeep c.pv hut
  unfold KeepsProofMode at hk
  rw [hfrom] at hk
  exact hk hm

private lemma policyInv_run {G : GateConfig} {s s' : GSys} {ls : List GLabel}
    (hM : MaskMonotone G) (hP : PolicyInv G s) (h : GRun G s ls s')
    (hls : ∀ l ∈ ls, ¬ l.IsBreakGlass ∧ l.PassesReleasePolicy G) : PolicyInv G s' := by
  induction h with
  | nil => exact hP
  | cons hs _ ih =>
      have h0 := hls _ List.mem_cons_self
      exact ih (policyInv_step hM hP hs h0.1 h0.2)
        (fun l hl => hls l (List.mem_cons_of_mem _ hl))

theorem ReleasePolicyKeepsFlaggedChainsCrossable :
    Properties.ReleasePolicyKeepsFlaggedChainsCrossable := by
  intro G s s' ls hM hP hrun hls
  have hP' := policyInv_run hM hP hrun hls
  exact ⟨hP', fun id c hc hut hf => policy_edge_multi hP' hc hut hf⟩

theorem UpgradesStayEnabledUnderReleasePolicy :
    Properties.UpgradesStayEnabledUnderReleasePolicy := by
  intro G s s' ls hM hP hW hrun hls id c hc hut hB hnz hbat hsl τ hτ
  have hP' := policyInv_run hM hP hrun hls
  have hr := TimedRunIsARun G.T s.ts s'.ts _ (GatedRunIsATimedRun G s s' ls hrun)
  have hna := grun_untimed_not_arbitrary hrun (fun l hl => (hls l hl).1)
  have hstep := UpgradesStayEnabled G.T.X.W s.ts.sys s'.ts.sys _ hP.sys hW hr hna id c hc hut hB
  have hdu : DiamondUpgrade G.T s'.ts id c.pv (s'.ts.aux id).admin τ
      (s'.ts.sys.crossEdge G.T.X.W id c) :=
    { authorized := Or.inl rfl
      atVersion := ⟨c, hc, rfl⟩
      notifierGate := fun h => absurd rfl h
      batchesExecuted := hbat
      routing := hstep
      manifestTime := hτ
      settlementLayer := fun w hw => by rw [hsl] at hw; cases hw }
  exact ⟨_, GStep.upgrade (TimedStep.direct hdu)
    ⟨hnz, fun hf => policy_edge_multi hP' hc hut hf, fun hf => policy_edge_multi hP' hc hut hf⟩⟩

/-- The fresh state satisfies `PolicyInv` in every witness configuration. -/
private lemma gSys0_policyInv (rv : Address → Address) :
    PolicyInv { gCfg with relVerifier := rv } gSys0 :=
  ⟨FreshSystemSatisfiesInvariant gWorld 100 (by decide), (by intro id hf; cases hf),
    (by intro id c hc; cases hc), (by intro v hv; exact absurd rfl hv)⟩

private lemma gSys0_chainsOnWf : ChainsOnWfReleases gWorld gSys0.ts.sys := by
  intro id c hc
  cases hc

/-- The labels of `gLockRun` other than the commit carry no transition. -/
private lemma gLockRun_policy_except_commit (G : GateConfig) :
    ∀ l ∈ gLockRun, l ≠ .other (.base (.ctm (.commit 300))) → l.PassesReleasePolicy G := by
  intro l hl hne
  simp only [gLockRun, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h | h | h <;> subst h
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · exact absurd rfl hne

theorem ReleasePolicyIsLoadBearing : Properties.ReleasePolicyIsLoadBearing := by
  refine ⟨gMaskMonotone _, gSys0_policyInv gRelVerifier, gSys0_chainsOnWf, gLock_run_gCfg,
    gLockRun_no_breakGlass, gLockRun_policy_except_commit gCfg, ?_, rfl, rfl, (by decide),
    gNodup200, (by decide), rfl, rfl, not_multi_701 gRelVerifier,
    fun path caller τ s' => locked_no_upgrade (gLock_locked gRelVerifier (not_multi_701 _))
      path caller τ s'⟩
  intro h
  exact not_multi_701 gRelVerifier (h (multi_700 gRelVerifier))

theorem ReleasePolicyWitness : Properties.ReleasePolicyWitness := by
  have hpol : ∀ l ∈ gLockRun, ¬ l.IsBreakGlass ∧ l.PassesReleasePolicy gCfgMulti := by
    intro l hl
    refine ⟨gLockRun_no_breakGlass l hl, ?_⟩
    by_cases hne : l = .other (.base (.ctm (.commit 300)))
    · subst hne
      exact fun _ => multi_700 _
    · exact gLockRun_policy_except_commit gCfgMulti l hl hne
  have hP := gSys0_policyInv (fun _ => 700)
  have hP' := (ReleasePolicyKeepsFlaggedChainsCrossable gCfgMulti gSys0 gLock gLockRun
    (gMaskMonotone _) hP gLock_run_gCfgMulti hpol).1
  refine ⟨gMaskMonotone _, hP, gSys0_chainsOnWf, gLock_run_gCfgMulti, hpol, multi_700 _, hP',
    rfl, rfl, (by decide), gNodup200, (by decide), rfl, rfl, rfl, multi_700 _, ?_⟩
  exact UpgradesStayEnabledUnderReleasePolicy gCfgMulti gSys0 gLock gLockRun (gMaskMonotone _) hP
    gSys0_chainsOnWf gLock_run_gCfgMulti hpol 0 ⟨1, rowsRouting (wRows 100)⟩ rfl (by decide)
    gNodup200 (by decide) rfl rfl 10 (by decide)

/-! ## The escapes -/

/-- The CTM after `gLock`'s CTM commits `600` (2→3 onto `250`). -/
private def gCtm600 : CTM :=
  { gLockSys.ctm with
    pv := 3
    cur := 250
    ut := upd gLockSys.ctm.ut 2 600
    relAt := upd gLockSys.ctm.relAt 3 250 }

private lemma gCommit600 : CStep gWorld gLockSys.ctm (.commit 600) gCtm600 :=
  CStep.commit (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- ... and then replaces `300` by the skip transition `420` (1→3 onto `250`). -/
private def gCtm420 : CTM := { gCtm600 with ut := upd gCtm600.ut 1 420 }

private lemma gReplace420 : CStep gWorld gCtm600 (.replace 300 420) gCtm420 :=
  CStep.replace (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

/-- A CTM writer on the gated system. -/
private lemma gstep_ctm {G : GateConfig} {s : GSys} {op : Op} {c' : CTM}
    (h : CStep G.T.X.W s.ts.sys.ctm op c') :
    GStep G s (.other (.base (.ctm op)))
      ⟨{ s.ts with sys := { s.ts.sys with ctm := c' } }, s.gate⟩ :=
  GStep.other True.intro (TimedStep.base (fun h => h) (Step.ctm h))

theorem EscapesUnlockTheLockedChain : Properties.EscapesUnlockTheLockedChain := by
  refine ⟨⟨_, _, _,
      GStep.other True.intro (TimedStep.base (l := .ctm (.commit 600)) (fun h => h)
        (Step.ctm (CStep.commit (t := 600) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)))),
      GStep.other True.intro (TimedStep.base (l := .ctm (.replace 300 420)) (fun h => h)
        (Step.ctm (CStep.replace (e := 300) (r := 420) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)))),
      GStep.upgrade (TimedStep.executor (Or.inr rfl) (by decide) rfl
          ⟨Or.inr (Or.inl rfl), ⟨_, rfl, rfl⟩, fun _ h => absurd rfl h, rfl,
            Step.transition rfl (by decide) rfl (applyDerived_rows_eq gNodup100 gNodup250)
              (by decide), (by decide), (fun w hw => by cases hw)⟩)
        ⟨(by decide), fun _ => multi_700 _, fun _ => multi_700 _⟩,
      rfl, _, rfl, rfl⟩, ?_, ?_, ?_⟩
  · exact ⟨_, GStep.breakGlass (TimedStep.base (fun h => h)
      (Step.arbitraryCut (c := ⟨1, rowsRouting (wRows 100)⟩) 2 _ rfl)) (fun _ => multi_700 _)⟩
  · exact ⟨_, GStep.breakGlass (TimedStep.base (fun h => h)
      (Step.arbitraryCut (c := ⟨1, rowsRouting (wRows 100)⟩) 2 _ rfl))
      (fun h => by cases h)⟩
  · intro v ρ s' h
    cases h with
    | breakGlass _ hg => exact not_multi_701 gRelVerifier (hg rfl)

theorem SkipOntoSingleProofReleaseDoesNotHelp :
    Properties.SkipOntoSingleProofReleaseDoesNotHelp := by
  have hS : Stuck gCfgSingle gLock 0 1 :=
    (LockedIsStuck gCfgSingle gLock gLock_ctmInv).2 0 1 (gLock_locked _ (not_multi_701 _))
  have h1 := gstep_ctm (G := gCfgSingle) (s := gLock) gCommit600
  have h2 := gstep_ctm (G := gCfgSingle)
    (s := ⟨{ gLock.ts with sys := { gLock.ts.sys with ctm := gCtm600 } }, gLock.gate⟩) gReplace420
  have hn1 : ¬ (GLabel.other (.base (.ctm (.commit 600)))).InstallsMulti gCfgSingle :=
    not_multi_701 _
  have hS2 := StuckUntilMultiReleaseOrBreakGlass gCfgSingle gLock _ _ 0 1 hS
    (GRun.cons h1 (GRun.cons h2 GRun.nil)) (by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with h | h <;> subst h
      · exact ⟨fun h => h, hn1⟩
      · exact ⟨fun h => h, fun h => h⟩)
  exact ⟨hS, _, _, h1, h2, hn1, fun hL => absurd hL.targetVersion (by decide), rfl, hS2,
    fun path caller τ s' => stuck_no_upgrade hS2 path caller τ s'⟩

/-! ## The countermodel and the witness -/

theorem FlaggedChainCannotCrossNonMultiProofEdge :
    Properties.FlaggedChainCannotCrossNonMultiProofEdge := by
  have hL : Locked gCfg gLock 0 1 := gLock_locked gRelVerifier (not_multi_701 _)
  refine ⟨gLock_run_gCfg, rfl, rfl, rfl, rfl, not_multi_701 gRelVerifier,
    gLock_exec gRelVerifier 1 (Or.inr rfl) (by decide) (fun h => by cases h),
    fun ls s' hr hne => LockedChainCannotUpgrade gCfg s' 0 1
      (LockHoldsUntilAnEscape gCfg gLock s' ls 0 1 hL hr hne),
    gLock_exec (fun _ => 700) 0 (Or.inl rfl) (by decide) (fun _ => multi_700 _), ?_,
    ⟨(by decide), (by decide), (by decide), (by decide), (by decide), (by decide), (by decide)⟩,
    ?_⟩
  · intro c' h
    cases h with
    | replace _ _ _ _ _ _ hpin _ => exact absurd (hpin rfl) (by decide)
  · exact (UpgradeChainEnabledIffTimedV35 gCfg
        ⟨{ gLock.ts with sys := { gLockSys with
          ctm := { gLockSys.ctm with ut := upd gLockSys.ctm.ut 1 410 } } }, gLock.gate⟩
        0 410 3 10).mpr
      ⟨Or.inr rfl, rfl, rfl, ⟨_, rfl, rfl⟩, (by decide), rfl, (fun w hw => by cases hw),
        ⟨_, Step.transition (id := 0) rfl (by decide) rfl
          (applyDerived_rows_eq gNodup100 gNodup210) (by decide)⟩,
        (by decide), fun _ => multi_700 _⟩

theorem UpgradeGateV35Witness : Properties.UpgradeGateV35Witness := by
  have hL : Locked gCfg gLock 0 1 := gLock_locked gRelVerifier (not_multi_701 _)
  obtain ⟨s', h⟩ := gLock_exec (fun _ => 700) 0 (Or.inl rfl) (by decide) (fun _ => multi_700 _)
  have hrep : CStep gWorld gLock.ts.sys.ctm (.replace 300 400)
      { gLock.ts.sys.ctm with ut := upd gLock.ts.sys.ctm.ut 1 400 } :=
    CStep.replace (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have hrun : GRun gCfg gLock [.other (.base (.ctm (.replace 300 400)))] _ :=
    GRun.cons (gstep_ctm hrep) GRun.nil
  have hne : ∀ l ∈ [GLabel.other (.base (.ctm (.replace 300 400)))], ¬ l.Escapes 0 := by
    intro l hl
    simp only [List.mem_singleton] at hl
    subst hl
    exact fun h => by cases h
  exact ⟨gLock_run_gCfg, hL, (by intro id hf; cases hf), gMaskMonotone _, gLock_gateInv _,
    gLock_ctmInv, (LockedIsStuck gCfg gLock gLock_ctmInv).2 0 1 hL, gLockRun_no_breakGlass,
    ⟨_, hrep, rfl⟩, ⟨_, hrun, hne, LockHoldsUntilAnEscape gCfg gLock _ _ 0 1 hL hrun hne, rfl⟩,
    gLock_run_gCfgMulti, gMaskMonotone _, s', h,
    FlagSurvivesAllButBreakGlass gCfgMulti gLock s' _ 0 h (by decide)
      (fun v ρ g hl => by cases hl) rfl⟩

theorem MaskMonotoneIsLoadBearing : Properties.MaskMonotoneIsLoadBearing := by
  refine ⟨{ gCfg with proofMode := fun _ m => if m = ziskBit then some MULTI else some PLONK },
    ⟨gLock.ts, fun _ => ⟨false, 700, ziskBit⟩⟩, _, 0, 3, (by intro id hf; cases hf),
    GStep.requireSecondProof (c := ⟨1, rowsRouting (wRows 100)⟩) rfl rfl rfl rfl (by decide),
    fun hI => ?_⟩
  have h := hI 0 rfl
  revert h
  unfold IsMulti
  decide

end Contracts.SecondProofSystem.UpgradeGateV35
