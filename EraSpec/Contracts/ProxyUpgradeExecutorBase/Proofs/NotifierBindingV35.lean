import EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.NotifierBindingV35
import EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTiming

/-!
# Proofs: the ServerNotifier binding at `d9f6789`

The post-check results read off `holders`: it does not mention `ctmNotifier` or any notifier's
`chainTypeManager`, so a leg that writes only those leaves the tuple unchanged, and every hash of
it. The writer results are a case split on the step. The shape invariant is the same case split:
each step either is by one of the executor's authorities or leaves every field of the shape. The
bound results rewrite the notifier's CTM to the real one and its `getChainAdmin` to `s.admin`,
then build the `TimedStep` of `Specs/UpgradeTiming.lean` and apply that model's
`NotifierWrittenOnlyByItsChainAdmin`. The countermodels are concrete states over `wEnv`.
-/

namespace Contracts.NotifierBindingV35

open Contracts.ChainTypeManager

/-! ## Frame lemmas -/

/-- A point update of the notifier map leaves a field unchanged everywhere when it leaves it
unchanged at the updated address. -/
private lemma upd_field {β : Type} (g : NotifierStore → β) (f : Address → NotifierStore)
    (m : Address) (y : NotifierStore) (h : g y = g (f m)) (n : Address) :
    g (upd f m y n) = g (f n) := by
  unfold upd
  split_ifs with hn
  · subst hn; exact h
  · rfl

/-- A point update at another address. -/
private lemma upd_other {β : Type} (f : Address → β) {m sn : Address} (y : β) (hm : m ≠ sn) :
    upd f m y sn = f sn :=
  upd_ne f y (Ne.symm hm)

/-- The binding only reads the CTM's pointer and three fields of the notifier. -/
private lemma handed_frame {E : Env} {s s' : State} {sn exec : Address}
    (h : NotifierHandedOver E s sn exec) (h1 : s'.ctmNotifier = s.ctmNotifier)
    (h2 : (s'.notifiers sn).ctm = (s.notifiers sn).ctm)
    (h3 : (s'.notifiers sn).owner = (s.notifiers sn).owner)
    (h4 : (s'.notifiers sn).pending = (s.notifiers sn).pending) :
    NotifierHandedOver E s' sn exec :=
  ⟨h1.trans h.ctmPointsAtNotifier, h2.trans h.notifierPointsAtCtm, h3.trans h.ownedByExecutor,
    h4.trans h.noNomination⟩

/-- The shape reads nine things. -/
private lemma shape_frame {E : Env} {s s' : State} {sn exec pa : Address}
    (h : CtmDomainShape E s sn exec pa) (h1 : s'.ctmNotifier = s.ctmNotifier)
    (h2 : (s'.notifiers sn).ctm = (s.notifiers sn).ctm)
    (h3 : (s'.notifiers sn).owner = (s.notifiers sn).owner)
    (h4 : (s'.notifiers sn).pending = (s.notifiers sn).pending)
    (h5 : s'.ctmOwner = s.ctmOwner) (h6 : s'.ctmPending = s.ctmPending)
    (h7 : s'.paOwner pa = s.paOwner pa) (h8 : s'.ctmAdmin = s.ctmAdmin)
    (h9 : s'.proxyAdminOf sn = s.proxyAdminOf sn) : CtmDomainShape E s' sn exec pa :=
  ⟨handed_frame h.handedOver h1 h2 h3 h4, h5.trans h.ctmOwned, h6.trans h.ctmNoNomination,
    h7.trans h.proxyAdminOwned, h8.trans h.ctmUnderProxyAdmin,
    h9.trans h.notifierUnderProxyAdmin⟩

/-! ## What the post-check reads -/

theorem DomainHoldersIgnoreBinding : Properties.DomainHoldersIgnoreBinding := by
  intro s t pa sn h1 h2 h3 h4 h5 h6 h7
  simp only [holders, h1, h2, h3, h4, h5, h6, h7]

theorem PostCheckIsHolderReadingsEqual : Properties.PostCheckIsHolderReadingsEqual := by
  intro s s' pa
  refine ⟨?_, fun h H f => congrArg f h, fun H f hf hn => ⟨_, _, hn, hf⟩⟩
  by_cases h0 : s.ctmNotifier = 0
  · simp [PostCheck, holders, h0]
  · simp [PostCheck, holders, h0]

/-! ## (a) Re-pointing -/

theorem EngineRepointsServerNotifier : Properties.EngineRepointsServerNotifier := by
  intro E s exec pa N' H h hown
  refine ⟨⟨Leg.cons (Step.setServerNotifier hown.symm) Leg.nil, rfl⟩, fun _ _ => rfl, ?_, ?_⟩
  · intro hne exec' hh
    exact hne hh.ctmPointsAtNotifier
  · intro sn' exec' hh
    have h1 : N' = sn' := hh.ctmPointsAtNotifier
    subst h1
    exact ⟨rfl, hh.notifierPointsAtCtm, hh.ownedByExecutor, hh.noNomination⟩

theorem PostReadCatchesOnlyHolderChange : Properties.PostReadCatchesOnlyHolderChange := by
  intro s pa N'
  simp [PostCheckAfterRead, holders]

/-! ## (b) Re-binding -/

theorem EngineRebindsNotifierCtm : Properties.EngineRebindsNotifierCtm := by
  intro E s exec pa C' H h hown hC
  have hsame : holders { s with notifiers := upd s.notifiers s.ctmNotifier
      ({ s.notifiers s.ctmNotifier with ctm := C' }) } pa s.ctmNotifier =
      holders s pa s.ctmNotifier := by
    simp [holders, upd]
  refine ⟨_, ⟨Leg.cons (Step.setChainTypeManager hown.symm hC) Leg.nil, ?_⟩, ?_, rfl, ?_, ?_, ?_⟩
  · exact congrArg h hsame
  · exact congrArg h hsame
  · simp [upd]
  · intro id v
    simp [liveEntry, upd]
  · intro hne sn exec' hh
    have h1 := hh.ctmPointsAtNotifier
    have h2 := hh.notifierPointsAtCtm
    simp only at h1
    subst h1
    simp [upd] at h2
    exact hne h2

/-! ## What the check does catch -/

theorem PostCheckCatchesNotifierNomination : Properties.PostCheckCatchesNotifierNomination := by
  intro E s exec pa o hown h0 ho
  have hdiff : holders { s with notifiers := upd s.notifiers s.ctmNotifier
      ({ s.notifiers s.ctmNotifier with pending := o }) } pa s.ctmNotifier ≠
      holders s pa s.ctmNotifier := by
    intro heq
    simp [holders, h0, upd] at heq
    exact ho heq
  exact ⟨_, Leg.cons (Step.notifierTransferOwnership hown.symm) Leg.nil, hdiff, hdiff,
    fun H h hacc => hacc.2⟩

/-! ## (c) Writers -/

theorem NotifierEntryWritersV35 : Properties.NotifierEntryWritersV35 := by
  intro E s s' caller op n id v hstep hne
  cases hstep with
  | @upgradeNotifierProxy m st hc =>
      by_cases hn : n = m
      · subst hn
        exact Or.inr ⟨st, rfl, hc⟩
      · exfalso
        apply hne
        simp [upd, hn]
  | @setUpgradeTimestamp m id0 ts0 hc hts _ _ =>
      by_cases hn : n = m
      · subst hn
        by_cases hid : id = id0
        · subst hid
          by_cases hv : v = E.pvVia (s.notifiers n).ctm id
          · subst hv
            exact Or.inl ⟨ts0, rfl, hc, rfl, hts, by simp [upd, setEntry]⟩
          · exfalso
            apply hne
            simp [upd, setEntry, hv]
        · exfalso
          apply hne
          simp [upd, setEntry, hid]
      · exfalso
        apply hne
        simp [upd, hn]
  | _ =>
      first
        | exact absurd rfl hne
        | exact absurd (congrFun (congrFun (upd_field NotifierStore.entry _ _ _ rfl n) id) v) hne

theorem NotifierBindingWritersV35 : Properties.NotifierBindingWritersV35 := by
  intro E s s' caller op hstep
  cases hstep with
  | setServerNotifier hc =>
      exact ⟨fun _ => Or.inl ⟨rfl, hc⟩, fun _ h => absurd rfl h⟩
  | upgradeCtmProxy hc =>
      exact ⟨fun _ => Or.inr ⟨_, _, rfl, hc⟩, fun _ h => absurd rfl h⟩
  | @setChainTypeManager m c hc hC =>
      refine ⟨fun h => absurd rfl h, fun n h => ?_⟩
      by_cases hn : n = m
      · subst hn
        left
        refine ⟨by simp [upd], hc, by simpa [upd] using hC⟩
      · exact absurd (congrArg NotifierStore.ctm (upd_ne _ _ hn)) h
  | @upgradeNotifierProxy m st hc =>
      refine ⟨fun h => absurd rfl h, fun n h => ?_⟩
      by_cases hn : n = m
      · subst hn
        exact Or.inr ⟨st, rfl, hc⟩
      · exact absurd (congrArg NotifierStore.ctm (upd_ne _ _ hn)) h
  | _ =>
      refine ⟨fun h => absurd rfl h, fun n h => ?_⟩
      first
        | exact absurd rfl h
        | exact absurd (upd_field NotifierStore.ctm _ _ _ rfl n) h

theorem LiveEntryWritersV35 : Properties.LiveEntryWritersV35 := by
  intro E s s' caller op id v hstep hne
  have hw := NotifierEntryWritersV35 E s s' caller op s.ctmNotifier id v hstep
  cases hstep with
  | setServerNotifier hc => exact Or.inr (Or.inr (Or.inl ⟨_, rfl, hc⟩))
  | upgradeCtmProxy hc => exact Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl, hc⟩))
  | _ =>
      rcases hw hne with ⟨ts, hop, hc, hv, hts, he⟩ | ⟨st, hop, hc⟩
      · exact Or.inl ⟨ts, hop, hc, hv, hts, he⟩
      · exact Or.inr (Or.inl ⟨st, hop, hc⟩)

theorem BindingMovedOnlyByItsHolders : Properties.BindingMovedOnlyByItsHolders := by
  intro E s s' caller op sn exec hb hstep hnot
  have hown := hb.ownedByExecutor
  have hpend := hb.noNomination
  cases hstep with
  | setServerNotifier hc => exact Or.inr (Or.inl hc)
  | upgradeCtmProxy hc => exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
  | @setChainTypeManager m c hc _ =>
      by_cases hm : m = sn
      · subst hm
        exact Or.inl (hc.trans hown)
      · exact absurd (handed_frame hb rfl (congrArg NotifierStore.ctm (upd_other _ _ hm))
          (congrArg NotifierStore.owner (upd_other _ _ hm))
          (congrArg NotifierStore.pending (upd_other _ _ hm))) hnot
  | @notifierTransferOwnership m o hc =>
      by_cases hm : m = sn
      · subst hm
        exact Or.inl (hc.trans hown)
      · exact absurd (handed_frame hb rfl (congrArg NotifierStore.ctm (upd_other _ _ hm))
          (congrArg NotifierStore.owner (upd_other _ _ hm))
          (congrArg NotifierStore.pending (upd_other _ _ hm))) hnot
  | @notifierAcceptOwnership m hc =>
      by_cases hm : m = sn
      · subst hm
        exact Or.inr (Or.inr (Or.inr (Or.inr (hc.trans hpend))))
      · exact absurd (handed_frame hb rfl (congrArg NotifierStore.ctm (upd_other _ _ hm))
          (congrArg NotifierStore.owner (upd_other _ _ hm))
          (congrArg NotifierStore.pending (upd_other _ _ hm))) hnot
  | @notifierRenounceOwnership m hc =>
      by_cases hm : m = sn
      · subst hm
        exact Or.inl (hc.trans hown)
      · exact absurd (handed_frame hb rfl (congrArg NotifierStore.ctm (upd_other _ _ hm))
          (congrArg NotifierStore.owner (upd_other _ _ hm))
          (congrArg NotifierStore.pending (upd_other _ _ hm))) hnot
  | @upgradeNotifierProxy m st hc =>
      by_cases hm : m = sn
      · subst hm
        exact Or.inr (Or.inr (Or.inl hc))
      · exact absurd (handed_frame hb rfl (congrArg NotifierStore.ctm (upd_other _ _ hm))
          (congrArg NotifierStore.owner (upd_other _ _ hm))
          (congrArg NotifierStore.pending (upd_other _ _ hm))) hnot
  | _ =>
      first
        | exact absurd (handed_frame hb rfl rfl rfl rfl) hnot
        | exact absurd (handed_frame hb rfl (upd_field NotifierStore.ctm _ _ _ rfl sn)
            (upd_field NotifierStore.owner _ _ _ rfl sn)
            (upd_field NotifierStore.pending _ _ _ rfl sn)) hnot

/-- One step by anyone but the executor and the zero address keeps the shape. -/
private lemma shape_step {E : Env} {s s' : State} {sn exec pa caller : Address} {op : Op}
    (h : CtmDomainShape E s sn exec pa) (hstep : Step E s caller op s') (hc : caller ≠ exec)
    (h0 : caller ≠ 0) : CtmDomainShape E s' sn exec pa := by
  have hown := h.handedOver.ownedByExecutor
  have hpend := h.handedOver.noNomination
  have hctm := h.ctmOwned
  have hcp := h.ctmNoNomination
  have hpa := h.proxyAdminOwned
  have hca := h.ctmUnderProxyAdmin
  have hna := h.notifierUnderProxyAdmin
  cases hstep with
  | setServerNotifier hcal => exact absurd (hcal.trans hctm) hc
  | ctmTransferOwnership hcal => exact absurd (hcal.trans hctm) hc
  | ctmAcceptOwnership hcal => exact absurd (hcal.trans hcp) h0
  | ctmRenounceOwnership hcal => exact absurd (hcal.trans hctm) hc
  | upgradeCtmProxy hcal =>
      rw [hca, hpa] at hcal
      exact absurd hcal hc
  | changeCtmProxyAdmin hcal _ =>
      rw [hca, hpa] at hcal
      exact absurd hcal hc
  | setUpgradePreconditionChecker _ =>
      exact shape_frame h rfl (upd_field NotifierStore.ctm _ _ _ rfl sn)
        (upd_field NotifierStore.owner _ _ _ rfl sn)
        (upd_field NotifierStore.pending _ _ _ rfl sn) rfl rfl rfl rfl rfl
  | setUpgradeTimestamp _ _ _ _ =>
      exact shape_frame h rfl (upd_field NotifierStore.ctm _ _ _ rfl sn)
        (upd_field NotifierStore.owner _ _ _ rfl sn)
        (upd_field NotifierStore.pending _ _ _ rfl sn) rfl rfl rfl rfl rfl
  | @setChainTypeManager m c hcal _ =>
      by_cases hm : m = sn
      · subst hm
        exact absurd (hcal.trans hown) hc
      · exact shape_frame h rfl (congrArg NotifierStore.ctm (upd_other _ _ hm))
          (congrArg NotifierStore.owner (upd_other _ _ hm))
          (congrArg NotifierStore.pending (upd_other _ _ hm)) rfl rfl rfl rfl rfl
  | @notifierTransferOwnership m o hcal =>
      by_cases hm : m = sn
      · subst hm
        exact absurd (hcal.trans hown) hc
      · exact shape_frame h rfl (congrArg NotifierStore.ctm (upd_other _ _ hm))
          (congrArg NotifierStore.owner (upd_other _ _ hm))
          (congrArg NotifierStore.pending (upd_other _ _ hm)) rfl rfl rfl rfl rfl
  | @notifierAcceptOwnership m hcal =>
      by_cases hm : m = sn
      · subst hm
        exact absurd (hcal.trans hpend) h0
      · exact shape_frame h rfl (congrArg NotifierStore.ctm (upd_other _ _ hm))
          (congrArg NotifierStore.owner (upd_other _ _ hm))
          (congrArg NotifierStore.pending (upd_other _ _ hm)) rfl rfl rfl rfl rfl
  | @notifierRenounceOwnership m hcal =>
      by_cases hm : m = sn
      · subst hm
        exact absurd (hcal.trans hown) hc
      · exact shape_frame h rfl (congrArg NotifierStore.ctm (upd_other _ _ hm))
          (congrArg NotifierStore.owner (upd_other _ _ hm))
          (congrArg NotifierStore.pending (upd_other _ _ hm)) rfl rfl rfl rfl rfl
  | @upgradeNotifierProxy m st hcal =>
      by_cases hm : m = sn
      · subst hm
        rw [hna, hpa] at hcal
        exact absurd hcal hc
      · exact shape_frame h rfl (congrArg NotifierStore.ctm (upd_other _ _ hm))
          (congrArg NotifierStore.owner (upd_other _ _ hm))
          (congrArg NotifierStore.pending (upd_other _ _ hm)) rfl rfl rfl rfl rfl
  | @changeNotifierProxyAdmin m a hcal _ =>
      by_cases hm : m = sn
      · subst hm
        rw [hna, hpa] at hcal
        exact absurd hcal hc
      · exact shape_frame h rfl rfl rfl rfl rfl rfl rfl rfl (upd_other _ _ hm)
  | @paTransferOwnership p o hcal _ =>
      by_cases hp : p = pa
      · subst hp
        exact absurd (hcal.trans hpa) hc
      · exact shape_frame h rfl rfl rfl rfl rfl rfl (upd_other _ _ hp) rfl rfl
  | @paRenounceOwnership p hcal =>
      by_cases hp : p = pa
      · subst hp
        exact absurd (hcal.trans hpa) hc
      · exact shape_frame h rfl rfl rfl rfl rfl rfl (upd_other _ _ hp) rfl rfl

theorem ShapeKeptByOtherCallers : Properties.ShapeKeptByOtherCallers := by
  intro E s s' cs sn exec pa hsh hrun hcs
  induction hrun with
  | nil => exact hsh
  | cons hstep _ ih =>
      have hhead := hcs _ (List.mem_cons_self ..)
      exact ih (shape_step hsh hstep hhead.1 hhead.2)
        (fun c hc => hcs c (List.mem_cons_of_mem _ hc))

/-! ## (d) Under the binding -/

theorem BoundNotifierAdminIsDiamondAdmin : Properties.BoundNotifierAdminIsDiamondAdmin := by
  intro E s s' sn exec caller id ts hctm hb hstep
  have hctmeq : (s.notifiers sn).ctm = E.ctm := hb.notifierPointsAtCtm
  have hsn : s.ctmNotifier = sn := hb.ctmPointsAtNotifier
  cases hstep with
  | setUpgradeTimestamp hc _ _ _ =>
      refine ⟨?_, ?_⟩
      · rw [hc, hctmeq]
        exact hctm id
      · simp [liveEntry, hsn, upd, setEntry, hctmeq]

theorem BoundStepRefinesUpgradeTiming : Properties.BoundStepRefinesUpgradeTiming := by
  intro E T ts s s' sn exec caller id t hctm hb hag hstep
  obtain ⟨c, hc, hpv⟩ := hag.chain
  obtain ⟨hcaller, _⟩ :=
    BoundNotifierAdminIsDiamondAdmin E s s' sn exec caller id t hctm hb hstep
  have hctmeq : (s.notifiers sn).ctm = E.ctm := hb.notifierPointsAtCtm
  have hsn : s.ctmNotifier = sn := hb.ctmPointsAtNotifier
  cases hstep with
  | setUpgradeTimestamp _ hts hsch _ =>
      have hsch' : E.scheduledVia E.ctm c.pv := by
        rw [hpv, ← hctmeq]
        exact hsch
      have key : liveEntry { s with notifiers := upd s.notifiers sn
          ({ s.notifiers sn with
              entry := setEntry (s.notifiers sn).entry id (E.pvVia (s.notifiers sn).ctm id) t }) } =
          setNotifierEntry ts.notifier id c.pv t := by
        rw [hag.notifier]
        funext a b
        subst hsn
        simp [liveEntry, setNotifierEntry, setEntry, upd, hctmeq, hpv]
      rw [key]
      exact TimedStep.setUpgradeTimestamp hc (by rw [hag.admin]; exact hcaller) hts
        (hag.scheduled _ hsch')

theorem BoundLiveEntryWrittenOnlyByItsChainAdmin :
    Properties.BoundLiveEntryWrittenOnlyByItsChainAdmin := by
  intro E T ts s s' sn exec caller n id id' v t hctm hb hag hstep hne
  rcases LiveEntryWritersV35 E s s' caller _ id v hstep hne with
    ⟨t', hop, _, _, _, _⟩ | ⟨_, hop, _⟩ | ⟨_, hop, _⟩ | ⟨_, _, _, hop, _⟩
  · injection hop with h1 h2 h3
    subst h1 h2 h3
    have hsn : s.ctmNotifier = sn := hb.ctmPointsAtNotifier
    have hstep' : Step E s caller (.setUpgradeTimestamp sn id t) s' := hsn ▸ hstep
    have htimed :=
      BoundStepRefinesUpgradeTiming E T ts s s' sn exec caller id t hctm hb hag hstep'
    have hne' : ({ ts with notifier := liveEntry s' } : TimedSys).notifier id v ≠
        ts.notifier id v := by
      rw [hag.notifier]
      exact hne
    rcases Contracts.ChainTypeManager.NotifierWrittenOnlyByItsChainAdmin T ts _ _ id v htimed hne'
      with ⟨caller', ts', c, hl, hc', hch, hpv, hts', he'⟩ | ⟨_, hl⟩
    · injection hl with _ h2 h3
      subst h2 h3
      exact ⟨hc', ⟨c, hch, hpv⟩, hts', he'⟩
    · cases hl
  · cases hop
  · cases hop
  · cases hop

theorem BoundLiveEntryWritersV35 : Properties.BoundLiveEntryWritersV35 := by
  intro E s s' sn exec pa caller op id v hctm hsh hstep hne
  have hb := hsh.handedOver
  have hsn : s.ctmNotifier = sn := hb.ctmPointsAtNotifier
  subst hsn
  have hctmeq : (s.notifiers s.ctmNotifier).ctm = E.ctm := hb.notifierPointsAtCtm
  rcases LiveEntryWritersV35 E s s' caller op id v hstep hne with
    ⟨ts, hop, hc, hv, hts, he⟩ | ⟨st, hop, hc⟩ | ⟨n, hop, hc⟩ | ⟨n, o, p, hop, hc⟩
  · left
    rw [hctmeq] at hc hv
    exact ⟨ts, hop, hc.trans (hctm id), hv, hts, he⟩
  · right
    rw [hsh.notifierUnderProxyAdmin, hsh.proxyAdminOwned] at hc
    exact hc
  · right
    exact hc.trans hsh.ctmOwned
  · right
    rw [hsh.ctmUnderProxyAdmin, hsh.proxyAdminOwned] at hc
    exact hc

/-! ## Countermodels and witnesses -/

/-- After the re-bind: notifier `6` asks contract `9` for chain admins. -/
private def rb1 : State :=
  { wState0 with notifiers := upd wState0.notifiers 6 ({ wState0.notifiers 6 with ctm := 9 }) }

/-- After `5` schedules chain `0` on notifier `6`. -/
private def rb2 : State :=
  { rb1 with notifiers := upd rb1.notifiers 6
      ({ rb1.notifiers 6 with
          entry := setEntry (rb1.notifiers 6).entry 0 (wEnv.pvVia (rb1.notifiers 6).ctm 0) 12 }) }

/-- After the repoint: the CTM points at the foreign notifier `7`. -/
private def rp1 : State := { wState0 with ctmNotifier := 7 }

/-- After `5` schedules chain `0` on notifier `7`. -/
private def rp2 : State :=
  { rp1 with notifiers := upd rp1.notifiers 7
      ({ rp1.notifiers 7 with
          entry := setEntry (rp1.notifiers 7).entry 0 (wEnv.pvVia (rp1.notifiers 7).ctm 0) 12 }) }

/-- The registry shape, with notifier `7` held exactly as `6` but bound to contract `9`. -/
private def sh0 : State :=
  { wState0 with
      notifiers := fun a => if a = 7 then ⟨9, 1, 0, fun _ _ => 0, fun _ => 0⟩ else wBound }

/-- After the repoint to `7`. -/
private def sh1 : State := { sh0 with ctmNotifier := 7 }

/-- `wState0` after a caller schedules chain `0` on the bound notifier `6` for time `12`. -/
private def sat1 : State :=
  { wState0 with notifiers := upd wState0.notifiers 6
      ({ wState0.notifiers 6 with
          entry := setEntry (wState0.notifiers 6).entry 0
            (wEnv.pvVia (wState0.notifiers 6).ctm 0) 12 }) }

private lemma wEnv_ctm : CtmAnswersDiamondAdmin wEnv := by
  intro id
  decide

private lemma w_shape : CtmDomainShape wEnv wState0 6 1 2 :=
  ⟨⟨rfl, by decide, by decide, by decide⟩, rfl, rfl, rfl, rfl, rfl⟩

private lemma w_shape_wrong : CtmDomainShape wEnvWrongAdmin wState0 6 1 2 :=
  ⟨⟨rfl, by decide, by decide, by decide⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- `wTimed` agrees with a state whose live schedule is empty, under an environment with
`wEnv`'s diamond admin, versions and schedule. -/
private lemma w_agrees {E : Env} {s : State} (hd : E.diamondAdmin = wEnv.diamondAdmin)
    (hp : E.pvVia = wEnv.pvVia) (hs : E.scheduledVia = wEnv.scheduledVia)
    (hn : liveEntry s = fun _ _ => 0) : AgreesAt E wTimed s 0 := by
  refine ⟨hn.symm, by rw [hd]; rfl, ⟨⟨1, fun _ => none⟩, rfl, by rw [hp]; rfl⟩, ?_⟩
  intro v hv
  rw [hs] at hv
  have hv1 : v = 1 := hv
  subst hv1
  left
  decide

private lemma wState0_live : liveEntry wState0 = fun _ _ => 0 := by
  funext a b
  rfl

private lemma rb1_live : liveEntry rb1 = fun _ _ => 0 := by
  funext a b
  rfl

/-- From the bound state, `5` cannot schedule chain `0` on notifier `6`. -/
private lemma w_bound_refuses (s' : State) :
    ¬ Step wEnv wState0 5 (.setUpgradeTimestamp 6 0 12) s' := by
  intro h
  cases h with
  | setUpgradeTimestamp hc _ _ _ => exact absurd hc (by decide)

/-- `5` is not chain `0`'s admin in `wTimed`, so it takes no admin step there. -/
private lemma wTimed_refuses (T : TimedConfig) (ts' : TimedSys) :
    ¬ TimedStep T wTimed (.setUpgradeTimestamp 0 5 12) ts' := by
  intro h
  cases h with
  | setUpgradeTimestamp _ hcal _ _ => exact absurd hcal (by decide)

theorem RebindNotifierCtmLetsForeignAdminSchedule :
    Properties.RebindNotifierCtmLetsForeignAdminSchedule := by
  have hsame : holders rb1 2 6 = holders wState0 2 6 := by decide
  refine ⟨wEnv, wState0, rb1, rb2, 1, 2, 6, 9, 5, 0, 1, 12, wEnv_ctm, w_shape, ?_, ?_,
    by decide, by decide, rfl, by decide, by decide, w_bound_refuses⟩
  · intro H h
    exact ⟨⟨Leg.cons (Step.setChainTypeManager (by decide) (by decide)) Leg.nil,
      congrArg h hsame⟩, congrArg h hsame⟩
  · exact Step.setUpgradeTimestamp (by decide) (by decide) rfl (Or.inl (by decide))

theorem RepointLetsForeignAdminSchedule : Properties.RepointLetsForeignAdminSchedule := by
  refine ⟨wEnv, wState0, rp1, rp2, 1, 2, 6, 7, 5, 0, 1, 12, wEnv_ctm, w_shape, ?_, ?_,
    by decide, ?_, by decide, by decide, rfl, by decide, by decide, w_bound_refuses⟩
  · intro H h
    exact ⟨Leg.cons (Step.setServerNotifier rfl) Leg.nil, rfl⟩
  · show holders rp1 2 7 ≠ holders wState0 2 6
    decide
  · exact Step.setUpgradeTimestamp (by decide) (by decide) rfl (Or.inl (by decide))

theorem SameHolderRepointPassesBothReads : Properties.SameHolderRepointPassesBothReads := by
  have hsame : holders sh1 2 7 = holders sh0 2 6 := by decide
  refine ⟨wEnv, sh0, sh1, 1, 2, 6, 7,
    ⟨⟨rfl, by decide, by decide, by decide⟩, rfl, rfl, rfl, rfl, rfl⟩, by decide, ?_, ?_⟩
  · intro H h
    exact ⟨⟨Leg.cons (Step.setServerNotifier rfl) Leg.nil, rfl⟩, congrArg h hsame⟩
  · intro sn' exec' hh
    have h1 := hh.ctmPointsAtNotifier
    have h2 := hh.notifierPointsAtCtm
    subst h1
    revert h2
    decide

theorem BoundRefinementPremisesAreLoadBearing :
    Properties.BoundRefinementPremisesAreLoadBearing := by
  refine ⟨⟨wEnv, wTimed, rb1, rb2, 5, 0, 1, 12, wEnv_ctm, w_agrees rfl rfl rfl rb1_live, ?_,
      by decide, by decide, wTimed_refuses⟩,
    ⟨wEnvWrongAdmin, wTimed, wState0, sat1, 6, 1, 2, 5, 0, 1, 12, w_shape_wrong,
      w_agrees rfl rfl rfl wState0_live, ?_, by decide, by decide, wTimed_refuses⟩⟩
  · exact Step.setUpgradeTimestamp (n := 6) (by decide) (by decide) rfl (Or.inl (by decide))
  · exact Step.setUpgradeTimestamp (n := 6) (by decide) (by decide) rfl (Or.inl (by decide))

theorem BoundPremisesSatisfiable : Properties.BoundPremisesSatisfiable := by
  exact ⟨wEnv, wTimed, wState0, sat1, 6, 1, 2, 3, 0, 12, wEnv_ctm, w_shape,
    w_agrees rfl rfl rfl wState0_live,
    Step.setUpgradeTimestamp (by decide) (by decide) rfl (Or.inl (by decide)),
    by decide, by decide, by decide⟩

end Contracts.NotifierBindingV35
