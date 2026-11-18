import EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.ExecutorOwnerCallsV35
import EraSpec.Contracts.ChainTypeManager.Proofs.VersionRegistry

/-!
# Proofs: which CTM executor frames make the CTM's owner calls, and what the executor logs (v0.35)

Every frame's owner calls and log are computed from its entry (`frame_logs`), by induction
over the calls of a `forward` and the acts of an engine. The origin and logging statements
read off that computation; the holders statement reads the leg's post-check premise; the
version invariant lifts `Contracts.ChainTypeManager.step_inv` through every route. The
witnesses are concrete frames over the `VersionRegistry` witness world, checked by `decide`.
-/

namespace Contracts.ExecutorOwnerCallsV35

open Contracts.ChainTypeManager (Address World CTM CStep CtmInv upd initState wWorld)

/-! ## Traces -/

lemma filterMap_cons_toList {α β : Type} (f : α → Option β) (a : α) (l : List α) :
    (a :: l).filterMap f = (f a).toList ++ l.filterMap f := by
  cases h : f a <;> simp [h]

@[simp] lemma ownerCalls_append (tr₁ tr₂ : List Obs) :
    ownerCalls (tr₁ ++ tr₂) = ownerCalls tr₁ ++ ownerCalls tr₂ := by
  simp [ownerCalls, List.filterMap_append]

@[simp] lemma exLog_append (tr₁ tr₂ : List Obs) :
    exLog (tr₁ ++ tr₂) = exLog tr₁ ++ exLog tr₂ := by
  simp [exLog, List.filterMap_append]

@[simp] lemma ownerCalls_cons (o : Obs) (tr : List Obs) :
    ownerCalls (o :: tr) = o.ownerCall?.toList ++ ownerCalls tr :=
  filterMap_cons_toList _ _ _

@[simp] lemma exLog_cons (o : Obs) (tr : List Obs) :
    exLog (o :: tr) = o.exEvent?.toList ++ exLog tr :=
  filterMap_cons_toList _ _ _

@[simp] lemma ownerCalls_nil : ownerCalls [] = [] := rfl

@[simp] lemma exLog_nil : exLog [] = [] := rfl

@[simp] lemma ownerCalls_map_ctmEvent (l : List CtmEvent) :
    ownerCalls (l.map Obs.ctmEvent) = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [Obs.ownerCall?, ih]

@[simp] lemma exLog_map_ctmEvent (l : List CtmEvent) : exLog (l.map Obs.ctmEvent) = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [Obs.exEvent?, ih]

lemma mem_ownerCalls {op : CtmOp} {tr : List Obs} :
    op ∈ ownerCalls tr ↔ Obs.ctmCall op ∈ tr := by
  unfold ownerCalls
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨o, ho, h⟩
    cases o <;> simp [Obs.ownerCall?] at h
    subst h; exact ho
  · intro h; exact ⟨_, h, rfl⟩

lemma mem_exLog {e : ExEvent} {tr : List Obs} : e ∈ exLog tr ↔ Obs.exEvent e ∈ tr := by
  unfold exLog
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨o, ho, h⟩
    cases o <;> simp [Obs.exEvent?] at h
    subst h; exact ho
  · intro h; exact ⟨_, h, rfl⟩

/-! ## What a frame records -/

lemma fwdStep_logs {cfg : Config} {s s' : State} {c : FwdCall} {tr : List Obs}
    (h : FwdStep cfg s c s' tr) :
    ownerCalls tr = c.ctmOp?.toList ∧ exLog tr = [.callForwarded c] := by
  cases h with
  | ctm _ _ => simp [Obs.ownerCall?, Obs.exEvent?, FwdCall.ctmOp?]
  | other _ => simp [Obs.ownerCall?, Obs.exEvent?, FwdCall.ctmOp?]

lemma fwdRun_logs {cfg : Config} {s s' : State} {cs : List FwdCall} {tr : List Obs}
    (h : FwdRun cfg s cs s' tr) :
    ownerCalls tr = cs.filterMap FwdCall.ctmOp? ∧ exLog tr = cs.map ExEvent.callForwarded := by
  induction h with
  | nil => simp
  | cons hstep _ ih =>
      obtain ⟨h₁, h₂⟩ := fwdStep_logs hstep
      rw [filterMap_cons_toList, ownerCalls_append, exLog_append, h₁, h₂, ih.1, ih.2]
      simp

lemma engStep_logs {cfg : Config} {s s' : State} {a : EngAct} {tr : List Obs}
    (h : EngStep cfg s a s' tr) :
    ownerCalls tr = a.ctmOp?.toList ∧ exLog tr = a.emitted?.toList := by
  cases h with
  | ctm _ => simp [Obs.ownerCall?, Obs.exEvent?, EngAct.ctmOp?, EngAct.emitted?]
  | upgradeProxy _ _ _ _ => simp [EngAct.ctmOp?, EngAct.emitted?]
  | emit => simp [Obs.ownerCall?, Obs.exEvent?, EngAct.ctmOp?, EngAct.emitted?]
  | other => simp [EngAct.ctmOp?, EngAct.emitted?]

lemma engRun_logs {cfg : Config} {s s' : State} {as : List EngAct} {tr : List Obs}
    (h : EngRun cfg s as s' tr) :
    ownerCalls tr = as.filterMap EngAct.ctmOp? ∧ exLog tr = as.filterMap EngAct.emitted? := by
  induction h with
  | nil => simp
  | cons hstep _ ih =>
      obtain ⟨h₁, h₂⟩ := engStep_logs hstep
      rw [filterMap_cons_toList, filterMap_cons_toList, ownerCalls_append, exLog_append, h₁, h₂,
        ih.1, ih.2]
      exact ⟨rfl, rfl⟩

/-- Every frame's owner calls and executor log, read off its entry. -/
lemma frame_logs {cfg : Config} {s s' : State} {caller : Address} {e : Entry} {tr : List Obs}
    (h : Frame cfg s caller e s' tr) :
    ownerCalls tr = e.ownerCalls cfg.W ∧ exLog tr = e.exLog cfg.W := by
  cases h with
  | acceptCTMOwnership _ _ => simp [Entry.ownerCalls, Entry.exLog]
  | applyInfrastructureUpgrade _ _ _ _ _ hrun _ _ _ _ =>
      obtain ⟨h₁, h₂⟩ := engRun_logs hrun
      simp [Entry.ownerCalls, Entry.exLog, h₁, h₂, Obs.ownerCall?, Obs.exEvent?]
  | applyCTMUpgrade _ _ _ _ _ =>
      simp [Entry.ownerCalls, Entry.exLog, Obs.ownerCall?, Obs.exEvent?]
  | upgradeChain _ _ _ =>
      simp [Entry.ownerCalls, Entry.exLog, Obs.ownerCall?, Obs.exEvent?]
  | forward _ hrun => exact fwdRun_logs hrun
  | transferOwnership _ => simp [Entry.ownerCalls, Entry.exLog]
  | acceptOwnership _ => simp [Entry.ownerCalls, Entry.exLog]

lemma mem_entry_ownerCalls {cfg : Config} {s s' : State} {caller : Address} {e : Entry}
    {tr : List Obs} (h : Frame cfg s caller e s' tr) {op : CtmOp} (hop : Obs.ctmCall op ∈ tr) :
    op ∈ e.ownerCalls cfg.W := by
  rw [← (frame_logs h).1]
  exact mem_ownerCalls.2 hop

lemma engAct_of_mem {op : CtmOp} {acts : List EngAct}
    (h : op ∈ acts.filterMap EngAct.ctmOp?) : EngAct.ctm op ∈ acts := by
  rw [List.mem_filterMap] at h
  obtain ⟨a, ha, hao⟩ := h
  cases a <;> simp [EngAct.ctmOp?] at hao
  subst hao; exact ha

lemma fwdCall_of_mem {op : CtmOp} {calls : List FwdCall}
    (h : op ∈ calls.filterMap FwdCall.ctmOp?) : FwdCall.ctm op ∈ calls := by
  rw [List.mem_filterMap] at h
  obtain ⟨c, hc, hco⟩ := h
  cases c <;> simp [FwdCall.ctmOp?] at hco
  subst hco; exact hc

/-! ## For every frame -/

theorem EntryFixesOwnerCallsAndLog : Properties.EntryFixesOwnerCallsAndLog :=
  fun _ _ _ _ _ _ h => frame_logs h

theorem OwnerCallOrigins : Properties.OwnerCallOrigins := by
  intro cfg s s' caller e tr h op hop
  have hmem := mem_entry_ownerCalls h hop
  cases h with
  | acceptCTMOwnership _ _ => simp [Entry.ownerCalls] at hmem
  | applyInfrastructureUpgrade hc hT hD hE _ _ _ _ _ _ =>
      exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, engAct_of_mem hmem, hD, hT, hE, hc⟩))
  | applyCTMUpgrade hc hcode _ _ _ =>
      simp only [Entry.ownerCalls, List.mem_singleton] at hmem
      exact Or.inl ⟨_, rfl, hmem, hcode, hc⟩
  | upgradeChain hc hut _ =>
      simp only [Entry.ownerCalls, List.mem_singleton] at hmem
      exact Or.inr (Or.inl ⟨_, _, rfl, hmem, hut, hc⟩)
  | forward hc _ =>
      exact Or.inr (Or.inr (Or.inl ⟨_, rfl, fwdCall_of_mem hmem, hc⟩))
  | transferOwnership _ => simp [Entry.ownerCalls] at hmem
  | acceptOwnership _ => simp [Entry.ownerCalls] at hmem

theorem OwnerCallsOutsideEngineLegsAreLogged :
    Properties.OwnerCallsOutsideEngineLegsAreLogged := by
  intro cfg s s' caller e tr h hq op hop
  have hmem := mem_entry_ownerCalls h hop
  have hlog := (frame_logs h).2
  cases h with
  | acceptCTMOwnership _ _ => simp [Entry.ownerCalls] at hmem
  | applyInfrastructureUpgrade _ _ _ _ _ _ _ _ _ _ =>
      exact absurd (engAct_of_mem hmem) (hq op)
  | applyCTMUpgrade _ _ _ _ _ =>
      simp only [Entry.ownerCalls, List.mem_singleton] at hmem
      subst hmem
      exact Or.inr (Or.inl ⟨_, rfl, by simp⟩)
  | upgradeChain _ _ _ =>
      simp only [Entry.ownerCalls, List.mem_singleton] at hmem
      subst hmem
      exact Or.inr (Or.inr ⟨_, _, rfl, by simp⟩)
  | forward _ _ =>
      refine Or.inl (mem_exLog.1 ?_)
      rw [hlog]
      exact List.mem_map_of_mem (fwdCall_of_mem hmem)
  | transferOwnership _ => simp [Entry.ownerCalls] at hmem
  | acceptOwnership _ => simp [Entry.ownerCalls] at hmem

theorem HoldersViewUnchangedIff : Properties.HoldersViewUnchangedIff := by
  intro cfg s s'
  unfold holdersView HoldersKept
  by_cases h : s.ctm.notifier = 0 <;> by_cases h' : s'.ctm.notifier = 0
  · simp [h, h']
  · simp [h, h']
  · simp [h, h']
    intro _ _ _ _ _ hn
    exact absurd hn.symm h
  · simp [h, h']
    intro _ _ _ _ _ hn
    rw [hn]

theorem EngineLegKeepsHoldersOrCollides : Properties.EngineLegKeepsHoldersOrCollides := by
  intro cfg s s' caller T acts tr h
  cases h with
  | applyInfrastructureUpgrade _ _ _ _ _ _ hown hpend hH hrows =>
      refine ⟨hown, hpend, hrows, ?_⟩
      by_cases hv : holdersView cfg s' = holdersView cfg s
      · exact Or.inl ((HoldersViewUnchangedIff cfg s s').1 hv)
      · exact Or.inr ⟨hv, hH⟩

/-! ## The version invariant along every route -/

/-- What a frame keeps of the CTM's version state. -/
def KeepsVersionInv (W : World) (s s' : State) : Prop :=
  (CtmInv W s.ctm.reg → CtmInv W s'.ctm.reg) ∧ s.ctm.reg.pv ≤ s'.ctm.reg.pv

lemma keepsVersionInv_refl {W : World} {s s' : State} (h : s'.ctm.reg = s.ctm.reg) :
    KeepsVersionInv W s s' :=
  ⟨fun hI => h ▸ hI, le_of_eq (congrArg CTM.pv h).symm⟩

lemma keepsVersionInv_trans {W : World} {s₁ s₂ s₃ : State} (h₁ : KeepsVersionInv W s₁ s₂)
    (h₂ : KeepsVersionInv W s₂ s₃) : KeepsVersionInv W s₁ s₃ :=
  ⟨fun hI => h₂.1 (h₁.1 hI), le_trans h₁.2 h₂.2⟩

lemma ctmCall_keeps {W : World} {sender : Address} {s : State} {op : CtmOp} {c' : CtmSide}
    (h : CtmCall W sender s.ctm op c') (ht : op.Tame) :
    KeepsVersionInv W s { s with ctm := c' } := by
  cases h with
  | commit _ hs =>
      exact ⟨fun hI => Contracts.ChainTypeManager.step_inv hI hs,
        (Contracts.ChainTypeManager.cstep_pv hs).1⟩
  | replace _ hs =>
      exact ⟨fun hI => Contracts.ChainTypeManager.step_inv hI hs,
        (Contracts.ChainTypeManager.cstep_pv hs).1⟩
  | setDeadline _ => exact keepsVersionInv_refl rfl
  | upgradeChain _ => exact keepsVersionInv_refl rfl
  | transferOwnership _ => exact keepsVersionInv_refl rfl
  | setPendingAdmin _ => exact keepsVersionInv_refl rfl
  | setServerNotifier _ => exact keepsVersionInv_refl rfl
  | other _ => exact ht.elim

lemma fwdRun_keeps {cfg : Config} {s s' : State} {cs : List FwdCall} {tr : List Obs}
    (h : FwdRun cfg s cs s' tr) (ht : ∀ c ∈ cs, c.Tame) : KeepsVersionInv cfg.W s s' := by
  induction h with
  | nil => exact keepsVersionInv_refl rfl
  | cons hstep _ ih =>
      refine keepsVersionInv_trans ?_ (ih fun c hc => ht c (List.mem_cons_of_mem _ hc))
      have hc := ht _ List.mem_cons_self
      cases hstep with
      | ctm _ hcall => exact ctmCall_keeps hcall hc
      | other _ => exact hc.elim

lemma engRun_keeps {cfg : Config} {s s' : State} {as : List EngAct} {tr : List Obs}
    (h : EngRun cfg s as s' tr) (ht : ∀ a ∈ as, a.Tame) : KeepsVersionInv cfg.W s s' := by
  induction h with
  | nil => exact keepsVersionInv_refl rfl
  | cons hstep _ ih =>
      refine keepsVersionInv_trans ?_ (ih fun a ha => ht a (List.mem_cons_of_mem _ ha))
      have ha := ht _ List.mem_cons_self
      cases hstep with
      | ctm hcall => exact ctmCall_keeps hcall ha
      | upgradeProxy _ _ _ _ => exact keepsVersionInv_refl rfl
      | emit => exact keepsVersionInv_refl rfl
      | other => exact ha.elim

theorem TameFramesKeepTheVersionInvariant :
    Properties.TameFramesKeepTheVersionInvariant := by
  intro cfg s s' caller e tr h ht hI
  suffices hk : KeepsVersionInv cfg.W s s' from ⟨hk.1 hI, hk.2⟩
  cases h with
  | acceptCTMOwnership _ _ => exact keepsVersionInv_refl rfl
  | applyInfrastructureUpgrade _ _ _ _ _ hrun _ _ _ _ => exact engRun_keeps hrun ht
  | applyCTMUpgrade _ _ hcall _ _ => exact ctmCall_keeps hcall trivial
  | upgradeChain _ _ hcall => exact ctmCall_keeps hcall trivial
  | forward _ hrun => exact fwdRun_keeps hrun ht
  | transferOwnership _ => exact keepsVersionInv_refl rfl
  | acceptOwnership _ => exact keepsVersionInv_refl rfl

/-! ## Witness frames -/

lemma Frame.congr_tr {cfg : Config} {s s' : State} {caller : Address} {e : Entry}
    {tr tr' : List Obs} (h : Frame cfg s caller e s' tr) (htr : tr = tr') :
    Frame cfg s caller e s' tr' := htr ▸ h

/-- `applyCTMUpgrade(300)` from `ocS0`. -/
lemma oc_commit_frame (H : List Address → UInt256) :
    Frame (ocCfg H) ocS0 2 (.applyCTMUpgrade 300) ocS1 ocCommitTrace := by
  refine (Frame.applyCTMUpgrade (cfg := ocCfg H) (s := ocS0) (caller := 2) (t := 300)
    (c' := ocS1.ctm) rfl ?_ (CtmCall.commit rfl (CStep.commit ?_ ?_ ?_ ?_ ?_ ?_)) ?_ ?_).congr_tr ?_
  all_goals first | decide | (dsimp only [ocCfg]; done) | (dsimp only [ocCfg]; decide)

/-- The witness leg from `ocS1`: the row, its log, the replacement and the deadline. -/
lemma oc_leg_frame (H : List Address → UInt256) :
    ∃ s', Frame (ocCfg H) ocS1 2 (.applyInfrastructureUpgrade ocT ocActs) s' ocLegTrace ∧
      s'.ctm.reg.ut 1 = 400 ∧ s'.ctm.dl 1 = 77 ∧ s'.impl 5 = 11 ∧
      holdersView (ocCfg H) s' = holdersView (ocCfg H) ocS1 := by
  refine ⟨_, (Frame.applyInfrastructureUpgrade (cfg := ocCfg H) (s := ocS1) (caller := 2)
    (T := ocT) (acts := ocActs) rfl ?_ ?_ ?_ ?_
    (EngRun.cons (EngStep.upgradeProxy ?_ ?_ ?_ ?_)
      (EngRun.cons EngStep.emit
        (EngRun.cons (EngStep.ctm (CtmCall.replace rfl (CStep.replace ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)))
          (EngRun.cons (EngStep.ctm (CtmCall.setDeadline rfl)) EngRun.nil))))
    rfl rfl rfl ?_).congr_tr ?_, ?_, ?_, ?_, rfl⟩
  all_goals first | decide | (dsimp only [ocCfg]; done) | (dsimp only [ocCfg]; decide)

/-- `upgradeChain(300, 0)` from `ocS1`, by chain `0`'s admin. -/
lemma oc_upgradeChain_frame (H : List Address → UInt256) :
    ∃ s' tr, Frame (ocCfg H) ocS1 50 (.upgradeChain 300 0) s' tr ∧
      tr = [.ctmCall (.upgradeChain 0 1), .exEvent (.chainUpgradeApplied 0 2)] := by
  refine ⟨_, _, Frame.upgradeChain (cfg := ocCfg H) (s := ocS1) (caller := 50) (t := 300)
    (id := 0) (Or.inr rfl) ?_ (CtmCall.upgradeChain rfl), ?_⟩
  all_goals (dsimp only [ocCfg]; decide)

/-- `forward(ocFwdCalls)` from `ocS1`; the call to `33` has no effect. -/
lemma oc_forward_frame (H : List Address → UInt256) :
    ∃ s' tr, Frame (ocCfg H) ocS1 2 (.forward ocFwdCalls) s' tr ∧
      tr = [.ctmCall (.setDeadline 1 77), .ctmEvent (.updateProtocolVersionDeadline 1 77),
        .exEvent (.callForwarded (.ctm (.setDeadline 1 77))),
        .exEvent (.callForwarded (.other 33 true 0))] ∧ s'.ctm.dl 1 = 77 := by
  refine ⟨{ ocS1 with ctm := { ocS1.ctm with dl := upd ocS1.ctm.dl 1 77 } }, _,
    Frame.forward (cfg := ocCfg H) (s := ocS1) (caller := 2) rfl
      (FwdRun.cons (FwdStep.ctm ?_ (CtmCall.setDeadline rfl))
        (FwdRun.cons (FwdStep.other ?_) FwdRun.nil)), ?_, ?_⟩
  all_goals first | decide | (dsimp only [ocCfg]; done) | (dsimp only [ocCfg]; decide)

/-- With `ocHPending`, the leg that nominates `42` as the CTM's owner has no frame. -/
lemma oc_nominateOwner_refused (s' : State) (tr : List Obs) :
    ¬ Frame (ocCfg ocHPending) ocS1 2 (.applyInfrastructureUpgrade ocT ocNominateOwner) s' tr := by
  intro h
  cases h with
  | applyInfrastructureUpgrade _ _ _ _ _ hrun _ _ hH _ =>
    cases hrun with
    | cons h1 hrun2 =>
      cases h1 with
      | upgradeProxy _ _ _ _ =>
        cases hrun2 with
        | cons h2 hrun3 =>
          cases h2 with
          | ctm hc =>
            cases hc with
            | transferOwnership _ =>
              cases hrun3 with
              | nil =>
                revert hH
                dsimp only [ocCfg, ocHPending, holdersView]
                decide

/-- With `ocHConst`, the same leg has a frame, and it nominates `42`. -/
lemma oc_nominateOwner_passes :
    ∃ s' tr, Frame (ocCfg ocHConst) ocS1 2 (.applyInfrastructureUpgrade ocT ocNominateOwner)
      s' tr ∧ s'.ctm.pending = 42 := by
  refine ⟨_, _, Frame.applyInfrastructureUpgrade (cfg := ocCfg ocHConst) (s := ocS1)
    (caller := 2) (T := ocT) (acts := ocNominateOwner) rfl ?_ ?_ ?_ ?_
    (EngRun.cons (EngStep.upgradeProxy ?_ ?_ ?_ ?_)
      (EngRun.cons (EngStep.ctm (CtmCall.transferOwnership rfl)) EngRun.nil))
    rfl rfl rfl ?_, ?_⟩
  all_goals first | decide | (dsimp only [ocCfg]; done) | (dsimp only [ocCfg]; decide)

/-- For every hash, the leg that nominates `42` as the CTM's admin has a frame. -/
lemma oc_nominateAdmin_passes (H : List Address → UInt256) :
    ∃ s' tr, Frame (ocCfg H) ocS1 2 (.applyInfrastructureUpgrade ocT ocNominateAdmin) s' tr ∧
      s'.ctm.pendingAdmin = 42 ∧ holdersView (ocCfg H) s' = holdersView (ocCfg H) ocS1 := by
  refine ⟨_, _, Frame.applyInfrastructureUpgrade (cfg := ocCfg H) (s := ocS1) (caller := 2)
    (T := ocT) (acts := ocNominateAdmin) rfl ?_ ?_ ?_ ?_
    (EngRun.cons (EngStep.upgradeProxy ?_ ?_ ?_ ?_)
      (EngRun.cons (EngStep.ctm (CtmCall.setPendingAdmin rfl)) EngRun.nil))
    rfl rfl rfl ?_, ?_, rfl⟩
  all_goals first | decide | (dsimp only [ocCfg]; done) | (dsimp only [ocCfg]; decide)

lemma oc_leg_ownerCalls :
    ownerCalls ocLegTrace = [.replace 300 400, .setDeadline 1 77] := by decide

/-- The witness leg's log names neither of its owner calls. -/
lemma oc_leg_unlogged {op : CtmOp} (hop : op ∈ ownerCalls ocLegTrace) :
    ¬ LoggedByExecutor wWorld ocLegTrace op := by
  rw [oc_leg_ownerCalls] at hop
  rintro (h | ⟨t, rfl, _⟩ | ⟨t, id, rfl, _⟩)
  · simp [ocLegTrace] at h
  · simp at hop
  · simp at hop

/-! ## Witnesses and countermodels -/

theorem OwnerCallOriginsEachOccur : Properties.OwnerCallOriginsEachOccur := by
  intro H
  refine ⟨⟨oc_commit_frame H, by decide, ⟨300, rfl, rfl, by dsimp only [ocCfg]; decide, rfl⟩,
    Or.inr (Or.inl ⟨300, rfl, by decide⟩)⟩, ?_, ?_, ?_⟩
  · obtain ⟨s', tr, hf, rfl⟩ := oc_upgradeChain_frame H
    refine ⟨s', _, hf, by decide, by decide,
      ⟨300, 0, rfl, by dsimp only [ocCfg]; decide, by dsimp only [ocCfg]; decide, Or.inr rfl⟩,
      Or.inr (Or.inr ⟨300, 0, by decide, by decide⟩)⟩
  · obtain ⟨s', tr, hf, rfl, hdl⟩ := oc_forward_frame H
    exact ⟨s', _, hf, by decide, ⟨ocFwdCalls, rfl, by decide, rfl⟩, by decide,
      Or.inl (by decide), hdl⟩
  · obtain ⟨s', hf, -⟩ := oc_leg_frame H
    exact ⟨s', _, hf, by decide,
      ⟨ocT, ocActs, rfl, by decide, rfl, by dsimp only [ocCfg]; decide,
        by dsimp only [ocCfg]; decide, rfl⟩⟩

theorem EngineLegReplacesAndMovesDeadlineWithoutForward :
    Properties.EngineLegReplacesAndMovesDeadlineWithoutForward := by
  intro H
  obtain ⟨s', hf, hut, hdl, himpl, hv⟩ := oc_leg_frame H
  exact ⟨oc_commit_frame H, s', hf, hut, hdl, himpl, oc_leg_ownerCalls, by decide, by decide,
    fun _ hop => oc_leg_unlogged hop, (HoldersViewUnchangedIff _ _ _).1 hv, fun h => h.1 hv⟩

theorem EngineOwnerCallsNotLoggedByExecutor :
    Properties.EngineOwnerCallsNotLoggedByExecutor := by
  intro hall
  obtain ⟨s', hf, -⟩ := oc_leg_frame ocHConst
  have hop : Obs.ctmCall (.replace 300 400) ∈ ocLegTrace := by decide
  exact oc_leg_unlogged (mem_ownerCalls.2 hop) (hall _ _ _ _ _ _ hf _ hop)

theorem EngineNominationRefusedOnlyByHoldersHash :
    Properties.EngineNominationRefusedOnlyByHoldersHash := by
  refine ⟨oc_nominateOwner_refused, ?_⟩
  obtain ⟨s', tr, hf, hpend⟩ := oc_nominateOwner_passes
  have hnk : ¬ HoldersKept (ocCfg ocHConst) ocS1 s' := by
    intro hk
    have := hk.2.2.1
    rw [hpend] at this
    exact absurd this (by decide)
  refine ⟨s', tr, hf, by decide, hpend, hnk, ?_, rfl⟩
  exact fun hv => hnk ((HoldersViewUnchangedIff _ _ _).1 hv)

theorem EngineLegNominatesCtmAdmin : Properties.EngineLegNominatesCtmAdmin := by
  intro H
  obtain ⟨s', tr, hf, hpa, hv⟩ := oc_nominateAdmin_passes H
  exact ⟨s', tr, hf, by decide, hpa, (HoldersViewUnchangedIff _ _ _).1 hv⟩

theorem ForwardNominatesCtmOwner : Properties.ForwardNominatesCtmOwner := by
  intro H
  refine ⟨_, _, Frame.forward (cfg := ocCfg H) (s := ocS1) (caller := 2) rfl
    (FwdRun.cons (FwdStep.ctm ?_ (CtmCall.transferOwnership rfl)) FwdRun.nil), ?_, ?_, ?_⟩
  all_goals first | decide | (dsimp only [ocCfg]; done) | (dsimp only [ocCfg]; decide)

/-- The commit step of the witness, at the registry level. -/
lemma oc_commit_cstep : CStep wWorld ocS0.ctm.reg (.commit 300) ocS1.ctm.reg :=
  CStep.commit (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem VersionInvariantPremisesMetAndNeeded :
    Properties.VersionInvariantPremisesMetAndNeeded := by
  have h0 : CtmInv wWorld ocS0.ctm.reg :=
    Contracts.ChainTypeManager.InitSatisfiesInvariant wWorld 100 (by decide)
  have h1 : CtmInv wWorld ocS1.ctm.reg := Contracts.ChainTypeManager.step_inv h0 oc_commit_cstep
  have ht : (Entry.applyInfrastructureUpgrade ocT ocActs).Tame := by
    intro a ha
    simp only [ocActs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> simp [EngAct.Tame, CtmOp.Tame]
  refine ⟨h0, h1, ht, ?_, ?_⟩
  · intro H
    obtain ⟨s', hf, hut, -⟩ := oc_leg_frame H
    exact ⟨s', hf, hut, (TameFramesKeepTheVersionInvariant _ _ _ _ _ _ hf ht h1).1⟩
  · intro H
    refine ⟨_, Frame.applyInfrastructureUpgrade (cfg := ocCfg H) (s := ocS1) (caller := 2)
      (T := ocT) (acts := ocOpaqueActs) rfl ?_ ?_ ?_ ?_
      (EngRun.cons (EngStep.upgradeProxy ?_ ?_ ?_ ?_) (EngRun.cons EngStep.other EngRun.nil))
      rfl rfl rfl ?_, fun hI => absurd hI.curNonzero (by decide),
      (HoldersViewUnchangedIff _ _ _).1 rfl⟩
    all_goals first | decide | (dsimp only [ocCfg]; done) | (dsimp only [ocCfg]; decide)

end Contracts.ExecutorOwnerCallsV35
