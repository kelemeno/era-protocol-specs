import EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.NotifierBindingV35
import EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTiming

/-!
# Proofs: the ServerNotifier binding at `b17415d20`

The post-check results read off `domainHolders`: `dh_after_eq_iff` says when the reading after
the engine is the reading before, field by field, and everything about the comparison follows
from it. The shape results combine it with the check before the engine, which pins the CTM
proxy's admin slot. The writer results are a case split on the step; the shape invariant for
other callers is the same case split. The bound results rewrite the notifier's CTM to the real
one and its `getChainAdmin` to `s.admin`, then build the `TimedStep` of
`Specs/UpgradeTiming.lean` and apply that model's `NotifierWrittenOnlyByItsChainAdmin`. The
countermodels and witnesses are concrete states over `nbEnv`.
-/

namespace Contracts.NotifierBindingV35

open Contracts.ChainTypeManager (Address ChainId upd TimedSys TimedConfig TimedStep LegacyCut
  setNotifierEntry upd_ne upd_same)

/-! ## Frame lemmas -/

/-- A point update of the notifier map leaves a field unchanged everywhere when it leaves it
unchanged at the updated address. -/
private lemma nb_upd_field {β : Type} (g : NotifierStore → β) (f : Address → NotifierStore)
    (m : Address) (y : NotifierStore) (h : g y = g (f m)) (n : Address) :
    g (upd f m y n) = g (f n) := by
  unfold upd
  split_ifs with hn
  · subst hn; exact h
  · rfl

/-- A point update at another address. -/
private lemma nb_upd_other {β : Type} (f : Address → β) {m sn : Address} (y : β) (hm : m ≠ sn) :
    upd f m y sn = f sn :=
  upd_ne f y (Ne.symm hm)

/-- The binding reads the CTM's pointer and three fields of the notifier. -/
private lemma nb_handed_frame {E : Env} {s s' : State} {sn exec : Address}
    (h : NotifierHandedOver E s sn exec) (h1 : s'.ctm.serverNotifier = s.ctm.serverNotifier)
    (h2 : (s'.notifiers sn).chainTypeManager = (s.notifiers sn).chainTypeManager)
    (h3 : (s'.notifiers sn).owner = (s.notifiers sn).owner)
    (h4 : (s'.notifiers sn).pendingOwner = (s.notifiers sn).pendingOwner) :
    NotifierHandedOver E s' sn exec :=
  ⟨h1.trans h.ctmPointsAtNotifier, h.notifierNonzero, h2.trans h.notifierPointsAtCtm,
    h3.trans h.ownedByExecutor, h4.trans h.noNomination⟩

/-- The shape reads ten things. -/
private lemma nb_shape_frame {E : Env} {s s' : State} {sn exec pa : Address}
    (h : CtmDomainShape E s sn exec pa) (h1 : s'.ctm.serverNotifier = s.ctm.serverNotifier)
    (h2 : (s'.notifiers sn).chainTypeManager = (s.notifiers sn).chainTypeManager)
    (h3 : (s'.notifiers sn).owner = (s.notifiers sn).owner)
    (h4 : (s'.notifiers sn).pendingOwner = (s.notifiers sn).pendingOwner)
    (h5 : s'.ctm.owner = s.ctm.owner) (h6 : s'.ctm.pendingOwner = s.ctm.pendingOwner)
    (h7 : s'.paOwner pa = s.paOwner pa) (h8 : s'.ctm.adminSlot = s.ctm.adminSlot)
    (h9 : (s'.notifiers sn).adminSlot = (s.notifiers sn).adminSlot) :
    CtmDomainShape E s' sn exec pa :=
  ⟨nb_handed_frame h.handedOver h1 h2 h3 h4, h5.trans h.ctmOwned, h6.trans h.ctmNoNomination,
    h7.trans h.proxyAdminOwned, h8.trans h.ctmUnderProxyAdmin,
    h9.trans h.notifierUnderProxyAdmin⟩

/-- A notifier-map update that keeps the four fields the shape reads at the updated address. -/
private lemma nb_shape_frame_notifiers {E : Env} {s : State} {sn exec pa m : Address}
    {y : NotifierStore} (h : CtmDomainShape E s sn exec pa)
    (h1 : y.chainTypeManager = (s.notifiers m).chainTypeManager)
    (h2 : y.owner = (s.notifiers m).owner) (h3 : y.pendingOwner = (s.notifiers m).pendingOwner)
    (h4 : y.adminSlot = (s.notifiers m).adminSlot) :
    CtmDomainShape E { s with notifiers := upd s.notifiers m y } sn exec pa :=
  nb_shape_frame h rfl (nb_upd_field NotifierStore.chainTypeManager _ _ _ h1 sn)
    (nb_upd_field NotifierStore.owner _ _ _ h2 sn)
    (nb_upd_field NotifierStore.pendingOwner _ _ _ h3 sn) rfl rfl rfl rfl
    (nb_upd_field NotifierStore.adminSlot _ _ _ h4 sn)

/-- A notifier-map update at another address than the shape's notifier. -/
private lemma nb_shape_frame_other {E : Env} {s : State} {sn exec pa m : Address}
    {y : NotifierStore} (h : CtmDomainShape E s sn exec pa) (hm : m ≠ sn) :
    CtmDomainShape E { s with notifiers := upd s.notifiers m y } sn exec pa :=
  nb_shape_frame h rfl (congrArg NotifierStore.chainTypeManager (nb_upd_other _ _ hm))
    (congrArg NotifierStore.owner (nb_upd_other _ _ hm))
    (congrArg NotifierStore.pendingOwner (nb_upd_other _ _ hm)) rfl rfl rfl rfl
    (congrArg NotifierStore.adminSlot (nb_upd_other _ _ hm))

/-! ## The domain-holders reading -/

/-- When the reading is defined, and what it is. -/
private lemma nb_dh_some_iff (s : State) (pa : Address) (t : Holders) :
    domainHolders s pa = some t ↔
      (s.ctm.serverNotifier = 0 ∧
        t = ⟨s.paOwner pa, s.ctm.owner, s.ctm.pendingOwner, s.ctm.admin,
          ctmProxyAdminSeen s.ctm pa, 0, none⟩) ∨
      (s.ctm.serverNotifier ≠ 0 ∧ (s.notifiers s.ctm.serverNotifier).adminSlot = pa ∧
        t = ⟨s.paOwner pa, s.ctm.owner, s.ctm.pendingOwner, s.ctm.admin,
          ctmProxyAdminSeen s.ctm pa, s.ctm.serverNotifier,
          some ((s.notifiers s.ctm.serverNotifier).owner,
            (s.notifiers s.ctm.serverNotifier).pendingOwner, pa,
            (s.notifiers s.ctm.serverNotifier).chainTypeManager)⟩) := by
  unfold domainHolders
  by_cases h0 : s.ctm.serverNotifier = 0
  · simp only [h0, ite_true, Option.some.injEq, true_and, ne_eq, not_true_eq_false, false_and,
      or_false]
    exact eq_comm
  · by_cases ha : (s.notifiers s.ctm.serverNotifier).adminSlot = pa
    · simp only [h0, ha, ite_false, ite_true, Option.some.injEq, false_and, ne_eq,
        not_false_eq_true, true_and, false_or]
      exact eq_comm
    · simp [h0, ha]

/-- The reading after the engine equals the reading `t` before it exactly when the holders
agree. -/
private lemma nb_dh_after_eq_iff {s s' : State} {pa : Address} {t : Holders}
    (hs : domainHolders s pa = some t) :
    domainHolders s' pa = some t ↔
      (s'.paOwner pa = s.paOwner pa ∧ s'.ctm.owner = s.ctm.owner ∧
        s'.ctm.pendingOwner = s.ctm.pendingOwner ∧ s'.ctm.admin = s.ctm.admin ∧
        ctmProxyAdminSeen s'.ctm pa = ctmProxyAdminSeen s.ctm pa ∧
        s'.ctm.serverNotifier = s.ctm.serverNotifier ∧
        (s.ctm.serverNotifier ≠ 0 →
          (s'.notifiers s.ctm.serverNotifier).adminSlot = pa ∧
          (s'.notifiers s.ctm.serverNotifier).owner = (s.notifiers s.ctm.serverNotifier).owner ∧
          (s'.notifiers s.ctm.serverNotifier).pendingOwner =
            (s.notifiers s.ctm.serverNotifier).pendingOwner ∧
          (s'.notifiers s.ctm.serverNotifier).chainTypeManager =
            (s.notifiers s.ctm.serverNotifier).chainTypeManager)) := by
  rw [nb_dh_some_iff] at hs ⊢
  rcases hs with ⟨h0, rfl⟩ | ⟨h0, ha, rfl⟩
  · constructor
    · rintro (⟨h0', ht⟩ | ⟨h0', _, ht⟩)
      · simp only [Holders.mk.injEq] at ht
        obtain ⟨e1, e2, e3, e4, e5, -, -⟩ := ht
        exact ⟨e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, h0'.trans h0.symm,
          fun h => absurd h0 h⟩
      · simp only [Holders.mk.injEq] at ht
        exact absurd ht.2.2.2.2.2.1.symm h0'
    · rintro ⟨e1, e2, e3, e4, e5, e6, -⟩
      left
      refine ⟨e6.trans h0, ?_⟩
      rw [e1, e2, e3, e4, e5]
  · constructor
    · rintro (⟨h0', ht⟩ | ⟨h0', ha', ht⟩)
      · simp only [Holders.mk.injEq] at ht
        exact absurd ht.2.2.2.2.2.1 h0
      · simp only [Holders.mk.injEq, Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, -, e9⟩ := ht
        refine ⟨e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm, fun _ => ?_⟩
        rw [← e6] at e7 e8 e9 ha'
        exact ⟨ha', e7.symm, e8.symm, e9.symm⟩
    · rintro ⟨e1, e2, e3, e4, e5, e6, hn⟩
      obtain ⟨e7, e8, e9, e10⟩ := hn h0
      right
      rw [e6]
      refine ⟨h0, e7, ?_⟩
      rw [e1, e2, e3, e4, e5, e8, e9, e10]

/-- The reading's `serverNotifier` component is the CTM's pointer. -/
private lemma nb_dh_notifier {s : State} {pa : Address} {t : Holders}
    (hs : domainHolders s pa = some t) : t.serverNotifier = s.ctm.serverNotifier := by
  rw [nb_dh_some_iff] at hs
  rcases hs with ⟨h0, rfl⟩ | ⟨_, _, rfl⟩
  · exact h0.symm
  · rfl

/-- In the registry shape, the reading is defined. -/
private lemma nb_dh_of_shape {E : Env} {s : State} {sn exec pa : Address}
    (h : CtmDomainShape E s sn exec pa) : ∃ t, domainHolders s pa = some t := by
  have h0 : s.ctm.serverNotifier ≠ 0 := by
    rw [h.handedOver.ctmPointsAtNotifier]
    exact h.handedOver.notifierNonzero
  have ha : (s.notifiers s.ctm.serverNotifier).adminSlot = pa := by
    rw [h.handedOver.ctmPointsAtNotifier]
    exact h.notifierUnderProxyAdmin
  exact ⟨_, (nb_dh_some_iff s pa _).2 (Or.inr ⟨h0, ha, rfl⟩)⟩

/-! ## What the post-check reads -/

theorem DomainHoldersReadOnly : Properties.DomainHoldersReadOnly := by
  intro s t pa h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  unfold domainHolders ctmProxyAdminSeen
  rw [h6, h7, h8, h9, h10, h1, h2, h3, h4, h5]

theorem PostCheckComparesExactly : Properties.PostCheckComparesExactly := by
  intro s s' pa t hs
  have key := nb_dh_after_eq_iff (s' := s') hs
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨t1, t1', h1, h1', he⟩
      rw [hs, Option.some.injEq] at h1
      subst h1
      have he' : t1' = t := he
      rw [he'] at h1'
      exact key.1 h1'
    · intro hag
      exact ⟨t, t, hs, key.2 hag, rfl⟩
  · intro hag H h
    exact ⟨t, t, hs, key.2 hag, rfl⟩
  · intro hnag H h ⟨t1, t1', h1, h1', he⟩
    rw [hs, Option.some.injEq] at h1
    subst h1
    refine ⟨t1', h1', fun heq => hnag (key.1 (heq ▸ h1')), he⟩

/-! ## Both pointers of the binding are compared -/

theorem PostCheckRejectsRepoint : Properties.PostCheckRejectsRepoint := by
  intro s s' pa t hs hne H h hpc
  exact (PostCheckComparesExactly s s' pa t hs).2.2 (fun hag => hne hag.2.2.2.2.2.1) H h hpc

theorem PostCheckRejectsRebind : Properties.PostCheckRejectsRebind := by
  intro s s' pa t hs h0 _ hne H h hpc
  exact (PostCheckComparesExactly s s' pa t hs).2.2
    (fun hag => hne (hag.2.2.2.2.2.2 h0).2.2.2) H h hpc

/-! ## An accepted leg keeps the registry shape -/

/-- The core of `AcceptedLegKeepsShape`: it reads only the start state, the check before the
engine and the equality of the readings. -/
private lemma nb_shape_of_readings {E : Env} {s s' : State} {sn exec pa : Address} {t : Holders}
    (h : CtmDomainShape E s sn exec pa) (hpre : PreCheck s pa)
    (hs : domainHolders s pa = some t) (hs' : domainHolders s' pa = some t) :
    CtmDomainShape E s' sn exec pa := by
  obtain ⟨e1, e2, e3, e4, e5, e6, hn⟩ := (nb_dh_after_eq_iff hs).1 hs'
  have hsn := h.handedOver.ctmPointsAtNotifier
  rw [hsn] at hn e6
  obtain ⟨e7, e8, e9, e10⟩ := hn h.handedOver.notifierNonzero
  have hslot : s'.ctm.adminSlot = pa := by
    by_contra hne
    simp only [ctmProxyAdminSeen, hne, h.ctmUnderProxyAdmin, ite_true, ite_false] at e5
    exact hpre (e4 ▸ e5)
  exact ⟨⟨e6, h.handedOver.notifierNonzero, e10.trans h.handedOver.notifierPointsAtCtm,
      e8.trans h.handedOver.ownedByExecutor, e9.trans h.handedOver.noNomination⟩,
    e2.trans h.ctmOwned, e3.trans h.ctmNoNomination, e1.trans h.proxyAdminOwned, hslot, e7⟩

theorem AcceptedLegKeepsShape : Properties.AcceptedLegKeepsShape := by
  intro E s s' cs sn exec pa h ⟨hpre, _, t, t', hs, hs', he⟩
  have he' : t' = t := he
  subst he'
  exact nb_shape_of_readings h hpre hs hs'

theorem AcceptedLegKeepsShapeOrCollision : Properties.AcceptedLegKeepsShapeOrCollision := by
  intro E H h s s' cs sn exec pa hsh ⟨hpre, _, t, t', hs, hs', he⟩
  by_cases heq : t' = t
  · subst heq
    exact Or.inl (nb_shape_of_readings hsh hpre hs hs')
  · exact Or.inr ⟨t, t', hs, hs', heq, he⟩

theorem DomainHashCollisionIsKeccakCollision :
    Properties.DomainHashCollisionIsKeccakCollision := by
  intro k t t' hne he
  by_cases hpre : domainPreimage k t' = domainPreimage k t
  · obtain ⟨a1, a2, a3, a4, a5, a6, np⟩ := t
    obtain ⟨b1, b2, b3, b4, b5, b6, np'⟩ := t'
    rcases np with _ | ⟨o, p, a, c⟩ <;> rcases np' with _ | ⟨o', p', a', c'⟩
    · simp only [domainPreimage, innerPreimage, List.cons.injEq, and_true] at hpre
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpre
      exact absurd rfl hne
    · simp [domainPreimage, innerPreimage] at hpre
    · simp [domainPreimage, innerPreimage] at hpre
    · simp only [domainPreimage, List.cons.injEq, and_true] at hpre
      obtain ⟨hk, rfl, rfl, rfl, rfl⟩ := hpre
      right
      refine ⟨fun hin => ?_, hk⟩
      simp only [innerPreimage, List.cons.injEq, and_true] at hin
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hin
      exact hne rfl
  · exact Or.inl ⟨hpre, he⟩

theorem AcceptedLegKeepsShapeOrKeccakCollision :
    Properties.AcceptedLegKeepsShapeOrKeccakCollision := by
  intro E k s s' cs sn exec pa hsh hacc
  rcases AcceptedLegKeepsShapeOrCollision E Address (domainHash k) s s' cs sn exec pa hsh hacc
    with hsh' | ⟨t, t', hs, hs', hne, he⟩
  · exact Or.inl hsh'
  · exact Or.inr ⟨t, t', hs, hs', DomainHashCollisionIsKeccakCollision k t t' hne he⟩

/-! ## Runs of the CTM domain -/

/-- One step by anyone but the executor and the zero address keeps the shape. -/
private lemma nb_shape_step {E : Env} {s s' : State} {sn exec pa caller : Address} {op : Op}
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
  | ctmSetPendingAdmin _ => exact nb_shape_frame h rfl rfl rfl rfl rfl rfl rfl rfl rfl
  | ctmAcceptAdmin _ => exact nb_shape_frame h rfl rfl rfl rfl rfl rfl rfl rfl rfl
  | ctmTransferOwnership hcal => exact absurd (hcal.trans hctm) hc
  | ctmAcceptOwnership hcal => exact absurd (hcal.trans hcp) h0
  | ctmRenounceOwnership hcal => exact absurd (hcal.trans hctm) hc
  | upgradeCtmProxy hcal =>
      rw [hca, hpa] at hcal
      exact absurd hcal hc
  | changeCtmProxyAdmin hcal _ =>
      rw [hca, hpa] at hcal
      exact absurd hcal hc
  | setUpgradePreconditionChecker _ => exact nb_shape_frame_notifiers h rfl rfl rfl rfl
  | setUpgradeTimestamp _ _ _ _ => exact nb_shape_frame_notifiers h rfl rfl rfl rfl
  | @setChainTypeManager m c hcal _ =>
      by_cases hm : m = sn
      · subst hm
        exact absurd (hcal.trans hown) hc
      · exact nb_shape_frame_other h hm
  | @notifierTransferOwnership m o hcal =>
      by_cases hm : m = sn
      · subst hm
        exact absurd (hcal.trans hown) hc
      · exact nb_shape_frame_other h hm
  | @notifierAcceptOwnership m hcal =>
      by_cases hm : m = sn
      · subst hm
        exact absurd (hcal.trans hpend) h0
      · exact nb_shape_frame_other h hm
  | @notifierRenounceOwnership m hcal =>
      by_cases hm : m = sn
      · subst hm
        exact absurd (hcal.trans hown) hc
      · exact nb_shape_frame_other h hm
  | @upgradeNotifierProxy m st hcal =>
      by_cases hm : m = sn
      · subst hm
        rw [hna, hpa] at hcal
        exact absurd hcal hc
      · exact nb_shape_frame_other h hm
  | @changeNotifierProxyAdmin m a hcal _ =>
      by_cases hm : m = sn
      · subst hm
        rw [hna, hpa] at hcal
        exact absurd hcal hc
      · exact nb_shape_frame_other h hm
  | @paTransferOwnership p o hcal _ =>
      by_cases hp : p = pa
      · subst hp
        exact absurd (hcal.trans hpa) hc
      · exact nb_shape_frame h rfl rfl rfl rfl rfl rfl (nb_upd_other _ _ hp) rfl rfl
  | @paRenounceOwnership p hcal =>
      by_cases hp : p = pa
      · subst hp
        exact absurd (hcal.trans hpa) hc
      · exact nb_shape_frame h rfl rfl rfl rfl rfl rfl (nb_upd_other _ _ hp) rfl rfl

theorem ShapeKeptByOtherCallers : Properties.ShapeKeptByOtherCallers := by
  intro E s s' cs sn exec pa hsh hrun hcs
  induction hrun with
  | nil => exact hsh
  | cons hstep _ ih =>
      have hhead := hcs _ (List.mem_cons_self ..)
      exact ih (nb_shape_step hsh hstep hhead.1 hhead.2)
        (fun c hc => hcs c (List.mem_cons_of_mem _ hc))

/-- The executor's `acceptCTMOwnership` keeps the shape: in the shape, no nomination is
outstanding, so the call succeeds only for the zero address, and then changes nothing the shape
reads. -/
private lemma nb_shape_accept {E : Env} {s s' : State} {sn exec pa : Address}
    (h : CtmDomainShape E s sn exec pa) (hstep : Step E s exec .ctmAcceptOwnership s') :
    CtmDomainShape E s' sn exec pa := by
  cases hstep with
  | ctmAcceptOwnership hcal =>
      have he : exec = 0 := hcal.trans h.ctmNoNomination
      refine nb_shape_frame h rfl rfl rfl rfl ?_ ?_ rfl rfl rfl
      · show exec = s.ctm.owner
        exact h.ctmOwned.symm
      · show (0 : Address) = s.ctm.pendingOwner
        exact h.ctmNoNomination.symm

theorem ShapeKeptAlongDomainRunsOrCollision :
    Properties.ShapeKeptAlongDomainRunsOrCollision := by
  intro E H h s s' es sn exec pa hsh hrun
  induction hrun with
  | nil => exact Or.inl hsh
  | call hc h0 hstep _ ih =>
      rcases ih (nb_shape_step hsh hstep hc h0) with hsh' | ⟨cs, t, t', hmem, hne, he⟩
      · exact Or.inl hsh'
      · exact Or.inr ⟨cs, t, t', List.mem_cons_of_mem _ hmem, hne, he⟩
  | @leg s1 s2 s3 cs t t' es hpre _ hs hs' he _ ih =>
      by_cases heq : t' = t
      · subst heq
        rcases ih (nb_shape_of_readings hsh hpre hs hs') with hsh' | ⟨cs', u, u', hmem, hne, hu⟩
        · exact Or.inl hsh'
        · exact Or.inr ⟨cs', u, u', List.mem_cons_of_mem _ hmem, hne, hu⟩
      · exact Or.inr ⟨cs, t, t', List.mem_cons_self .., heq, he⟩
  | acceptCtmOwnership hstep _ ih =>
      rcases ih (nb_shape_accept hsh hstep) with hsh' | ⟨cs, t, t', hmem, hne, he⟩
      · exact Or.inl hsh'
      · exact Or.inr ⟨cs, t, t', List.mem_cons_of_mem _ hmem, hne, he⟩

theorem ShapeKeptAlongDomainRuns : Properties.ShapeKeptAlongDomainRuns := by
  intro E s s' es sn exec pa hsh hrun
  rcases ShapeKeptAlongDomainRunsOrCollision E Holders (fun x => x) s s' es sn exec pa hsh hrun
    with hsh' | ⟨_, _, _, _, hne, he⟩
  · exact hsh'
  · exact absurd he hne

/-! ## Writers -/

theorem NotifierEntryWritersV35 : Properties.NotifierEntryWritersV35 := by
  intro E s s' caller op n id v hstep hne
  cases hstep with
  | @upgradeNotifierProxy m st hc =>
      by_cases hn : n = m
      · subst hn
        exact Or.inr ⟨by simp [upd], hc⟩
      · exfalso
        apply hne
        simp [upd, hn]
  | @setUpgradeTimestamp m id0 ts0 hc hts _ _ =>
      by_cases hn : n = m
      · subst hn
        by_cases hid : id = id0
        · subst hid
          by_cases hv : v = E.pvVia (s.notifiers n).chainTypeManager id
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
      exfalso
      apply hne
      first
        | rfl
        | (simp only [upd]; split_ifs with hh <;> (try subst hh) <;> rfl)

theorem NotifierBindingWritersV35 : Properties.NotifierBindingWritersV35 := by
  intro E s s' caller op hstep
  cases hstep with
  | setServerNotifier hc =>
      exact ⟨fun _ => Or.inl ⟨rfl, hc⟩, fun _ h => absurd rfl h⟩
  | upgradeCtmProxy hc =>
      exact ⟨fun _ => Or.inr ⟨rfl, hc⟩, fun _ h => absurd rfl h⟩
  | @setChainTypeManager m c hc hC =>
      refine ⟨fun h => absurd rfl h, fun n h => ?_⟩
      by_cases hn : n = m
      · subst hn
        left
        refine ⟨by simp [upd], hc, by simpa [upd] using hC⟩
      · exact absurd (congrArg NotifierStore.chainTypeManager (upd_ne _ _ hn)) h
  | @upgradeNotifierProxy m st hc =>
      refine ⟨fun h => absurd rfl h, fun n h => ?_⟩
      by_cases hn : n = m
      · subst hn
        exact Or.inr ⟨by simp [upd], hc⟩
      · exact absurd (congrArg NotifierStore.chainTypeManager (upd_ne _ _ hn)) h
  | _ =>
      refine ⟨fun h => absurd rfl h, fun n h => ?_⟩
      exfalso
      apply h
      first
        | rfl
        | (simp only [upd]; split_ifs with hh <;> (try subst hh) <;> rfl)

theorem LiveEntryWritersV35 : Properties.LiveEntryWritersV35 := by
  intro E s s' caller op id v hstep hne
  have hw := NotifierEntryWritersV35 E s s' caller op s.ctm.serverNotifier id v hstep
  cases hstep with
  | setServerNotifier hc => exact Or.inr (Or.inr (Or.inl ⟨_, rfl, hc⟩))
  | upgradeCtmProxy hc => exact Or.inr (Or.inr (Or.inr ⟨_, rfl, hc⟩))
  | _ =>
      rcases hw hne with ⟨ts, hop, hc, hv, hts, he⟩ | ⟨hop, hc⟩
      · exact Or.inl ⟨ts, hop, hc, hv, hts, he⟩
      · exact Or.inr (Or.inl ⟨_, hop, hc⟩)

theorem BindingMovedOnlyByItsHolders : Properties.BindingMovedOnlyByItsHolders := by
  intro E s s' caller op sn exec hb hstep hnot
  have hown := hb.ownedByExecutor
  have hpend := hb.noNomination
  have frame_other : ∀ {m : Address} {y : NotifierStore}, m ≠ sn →
      NotifierHandedOver E { s with notifiers := upd s.notifiers m y } sn exec := fun hm =>
    nb_handed_frame hb rfl (congrArg NotifierStore.chainTypeManager (nb_upd_other _ _ hm))
      (congrArg NotifierStore.owner (nb_upd_other _ _ hm))
      (congrArg NotifierStore.pendingOwner (nb_upd_other _ _ hm))
  cases hstep with
  | setServerNotifier hc => exact Or.inr (Or.inl hc)
  | upgradeCtmProxy hc => exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
  | @setChainTypeManager m c hc _ =>
      by_cases hm : m = sn
      · subst hm
        exact Or.inl (hc.trans hown)
      · exact absurd (frame_other hm) hnot
  | @notifierTransferOwnership m o hc =>
      by_cases hm : m = sn
      · subst hm
        exact Or.inl (hc.trans hown)
      · exact absurd (frame_other hm) hnot
  | @notifierAcceptOwnership m hc =>
      by_cases hm : m = sn
      · subst hm
        exact Or.inr (Or.inr (Or.inr (Or.inr (hc.trans hpend))))
      · exact absurd (frame_other hm) hnot
  | @notifierRenounceOwnership m hc =>
      by_cases hm : m = sn
      · subst hm
        exact Or.inl (hc.trans hown)
      · exact absurd (frame_other hm) hnot
  | @upgradeNotifierProxy m st hc =>
      by_cases hm : m = sn
      · subst hm
        exact Or.inr (Or.inr (Or.inl hc))
      · exact absurd (frame_other hm) hnot
  | _ =>
      exfalso
      apply hnot
      refine nb_handed_frame hb rfl ?_ ?_ ?_ <;>
        first
          | rfl
          | (simp only [upd]; split_ifs with hh <;> (try subst hh) <;> rfl)

/-! ## Under the binding -/

theorem BoundNotifierAdminIsDiamondAdmin : Properties.BoundNotifierAdminIsDiamondAdmin := by
  intro E s s' sn exec caller id ts hctm hb hstep
  have hctmeq : (s.notifiers sn).chainTypeManager = E.ctm := hb.notifierPointsAtCtm
  have hsn : s.ctm.serverNotifier = sn := hb.ctmPointsAtNotifier
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
  have hctmeq : (s.notifiers sn).chainTypeManager = E.ctm := hb.notifierPointsAtCtm
  have hsn : s.ctm.serverNotifier = sn := hb.ctmPointsAtNotifier
  cases hstep with
  | setUpgradeTimestamp _ hts hsch _ =>
      have hsch' : E.scheduledVia E.ctm c.pv := by
        rw [hpv, ← hctmeq]
        exact hsch
      have key : liveEntry { s with notifiers := upd s.notifiers sn (
          { s.notifiers sn with
              entry := setEntry (s.notifiers sn).entry id
                (E.pvVia (s.notifiers sn).chainTypeManager id) t }) } =
          setNotifierEntry ts.notifier id c.pv t := by
        rw [hag.notifier]
        subst hsn
        funext a b
        unfold liveEntry setNotifierEntry setEntry upd
        simp [hctmeq, hpv]
      rw [key]
      exact TimedStep.setUpgradeTimestamp hc (by rw [hag.admin]; exact hcaller) hts
        (hag.scheduled _ hsch')

theorem BoundLiveEntryWrittenOnlyByItsChainAdmin :
    Properties.BoundLiveEntryWrittenOnlyByItsChainAdmin := by
  intro E ts s s' sn exec caller n id id' v t hctm hb hag hstep hne
  rcases LiveEntryWritersV35 E s s' caller _ id v hstep hne with
    ⟨t', hop, _, _, _, _⟩ | ⟨_, hop, _⟩ | ⟨_, hop, _⟩ | ⟨_, hop, _⟩
  · injection hop with h1 h2 h3
    subst n
    subst id'
    subst t'
    have hsn : s.ctm.serverNotifier = sn := hb.ctmPointsAtNotifier
    have hstep' : Step E s caller (.setUpgradeTimestamp sn id t) s' := hsn ▸ hstep
    have htimed :=
      BoundStepRefinesUpgradeTiming E Contracts.ChainTypeManager.wTiming ts
        s s' sn exec caller id t hctm hb hag hstep'
    have hne' : ({ ts with notifier := liveEntry s' } : TimedSys).notifier id v ≠
        ts.notifier id v := by
      rw [hag.notifier]
      exact hne
    rcases Contracts.ChainTypeManager.NotifierWrittenOnlyByItsChainAdmin _ ts _ _ id v htimed hne'
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
  have hsn : s.ctm.serverNotifier = sn := hb.ctmPointsAtNotifier
  subst hsn
  have hctmeq : (s.notifiers s.ctm.serverNotifier).chainTypeManager = E.ctm :=
    hb.notifierPointsAtCtm
  rcases LiveEntryWritersV35 E s s' caller op id v hstep hne with
    ⟨ts, hop, hc, hv, hts, he⟩ | ⟨st, hop, hc⟩ | ⟨n, hop, hc⟩ | ⟨c, hop, hc⟩
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

theorem OnlyDiamondAdminSchedulesAlongDomainRuns :
    Properties.OnlyDiamondAdminSchedulesAlongDomainRuns := by
  intro E s s₁ s₂ es sn exec pa caller op id v hctm hsh hrun hc hstep hne
  have hsh₁ := ShapeKeptAlongDomainRuns E s s₁ es sn exec pa hsh hrun
  rcases BoundLiveEntryWritersV35 E s₁ s₂ sn exec pa caller op id v hctm hsh₁ hstep hne with
    hw | hce
  · exact hw
  · exact absurd hce hc

/-! ## Countermodels and witnesses -/

/-- The registry-shape reading of `nbState0`. -/
private def nbReading : Holders := ⟨1, 1, 0, 4, 2, 6, some (1, 0, 2, 8)⟩

private lemma nb_reading0 : domainHolders nbState0 2 = some nbReading := by decide

private lemma nb_shape0 : CtmDomainShape nbEnv nbState0 6 1 2 :=
  ⟨⟨rfl, by decide, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

private lemma nb_env_answers : CtmAnswersDiamondAdmin nbEnv := fun _ => rfl

/-- After the re-bind: notifier `6` asks contract `9` for chain admins. -/
private def nbRebound : State :=
  { nbState0 with notifiers := upd nbState0.notifiers 6 (
      { nbState0.notifiers 6 with chainTypeManager := 9 }) }

/-- After `5` schedules chain `0` on notifier `6` of `nbRebound`. -/
private def nbReboundScheduled : State :=
  { nbRebound with notifiers := upd nbRebound.notifiers 6 (
      { nbRebound.notifiers 6 with
          entry := setEntry (nbRebound.notifiers 6).entry 0
            (nbEnv.pvVia (nbRebound.notifiers 6).chainTypeManager 0) 12 }) }

/-- After the repoint: the CTM points at the foreign notifier `7`. -/
private def nbRepointed : State := { nbState0 with ctm := { nbCtm with serverNotifier := 7 } }

/-- After `5` schedules chain `0` on notifier `7` of `nbRepointed`. -/
private def nbRepointedScheduled : State :=
  { nbRepointed with notifiers := upd nbRepointed.notifiers 7 (
      { nbRepointed.notifiers 7 with
          entry := setEntry (nbRepointed.notifiers 7).entry 0
            (nbEnv.pvVia (nbRepointed.notifiers 7).chainTypeManager 0) 12 }) }

/-- `nbState0` after a caller schedules chain `0` on the bound notifier `6` for time `12`. -/
private def nbScheduled : State :=
  { nbState0 with notifiers := upd nbState0.notifiers 6 (
      { nbState0.notifiers 6 with
          entry := setEntry (nbState0.notifiers 6).entry 0
            (nbEnv.pvVia (nbState0.notifiers 6).chainTypeManager 0) 12 }) }

/-- The leg of `AcceptedLegWitness`: a precondition checker for version `1` on the bound
notifier, then a CTM admin nomination. -/
private def nbLeg : List (Address × Op) :=
  [(1, .setUpgradePreconditionChecker 6 1 9), (1, .ctmSetPendingAdmin 5)]

/-- What `nbLeg` does to a state. -/
private def nbAfterLeg (s : State) : State :=
  { s with
      notifiers := upd s.notifiers 6 (
        { s.notifiers 6 with checker := upd (s.notifiers 6).checker 1 9 })
      ctm := { s.ctm with pendingAdmin := 5 } }

/-- `nbLeg` runs from any state where `1` owns notifier `6` and the CTM. -/
private lemma nb_leg_run (s : State) (h6 : (s.notifiers 6).owner = 1) (hc : s.ctm.owner = 1) :
    Run nbEnv s nbLeg (nbAfterLeg s) :=
  Run.cons (Step.setUpgradePreconditionChecker h6.symm)
    (Run.cons (Step.ctmSetPendingAdmin (Or.inr hc.symm)) Run.nil)

/-- `nbTimed` agrees at chain `0` with a state whose live schedule is empty, under an
environment with `nbEnv`'s diamond admin, versions and schedule. -/
private lemma nb_agrees {E : Env} {s : State} (hd : E.diamondAdmin = nbEnv.diamondAdmin)
    (hp : E.pvVia = nbEnv.pvVia) (hs : E.scheduledVia = nbEnv.scheduledVia)
    (hn : liveEntry s = fun _ _ => 0) : AgreesAt E nbTimed s 0 := by
  refine ⟨hn.symm, by rw [hd]; rfl, ⟨⟨1, fun _ => none⟩, rfl, by rw [hp]; rfl⟩, ?_⟩
  intro v hv
  rw [hs] at hv
  have hv1 : v = 1 := hv
  subst hv1
  left
  decide

private lemma nb_state0_live : liveEntry nbState0 = fun _ _ => 0 := by
  funext a b
  rfl

private lemma nb_rebound_live : liveEntry nbRebound = fun _ _ => 0 := by
  funext a b
  rfl

/-- From the bound state, `5` cannot schedule chain `0` on notifier `6`. -/
private lemma nb_bound_refuses (s' : State) :
    ¬ Step nbEnv nbState0 5 (.setUpgradeTimestamp 6 0 12) s' := by
  intro h
  cases h with
  | setUpgradeTimestamp hc _ _ _ => exact absurd hc (by decide)

/-- `5` is not chain `0`'s admin in `nbTimed`, so it takes no admin step there. -/
private lemma nb_timed_refuses (T : TimedConfig) (ts' : TimedSys) :
    ¬ TimedStep T nbTimed (.setUpgradeTimestamp 0 5 12) ts' := by
  intro h
  cases h with
  | setUpgradeTimestamp _ hcal _ _ => exact absurd hcal (by decide)

/-- The check before the engine passes for any state whose CTM `admin` is `4`. -/
private lemma nb_precheck {s : State} (h : s.ctm.admin = 4) : PreCheck s 2 := by
  unfold PreCheck
  rw [h]
  decide

/-- A gate with entry `0` is closed. -/
private lemma nb_gate_closed {s : State} {id : ChainId} {v τ : ℕ} (h : liveEntry s id v = 0) :
    ¬ ValidatorGateOpen s id v τ :=
  fun hg => hg.1 h

/-- A gate whose entry is `τ ≠ 0` is open at `τ`. -/
private lemma nb_gate_open {s : State} {id : ChainId} {v τ : ℕ} (h : liveEntry s id v = τ)
    (hτ : τ ≠ 0) : ValidatorGateOpen s id v τ :=
  ⟨h ▸ hτ, h.le⟩

theorem PreCheckIsLoadBearing : Properties.PreCheckIsLoadBearing := by
  let s : State := { nbState0 with ctm := { nbCtm with admin := 2 } }
  let s' : State := { s with ctm := { s.ctm with adminSlot := 7 } }
  have hsame : domainHolders s' 2 = domainHolders s 2 := by decide
  have hdef : domainHolders s 2 = some ⟨1, 1, 0, 2, 2, 6, some (1, 0, 2, 8)⟩ := by decide
  refine ⟨nbEnv, s, s', 6, 1, 2, 7,
    ⟨⟨rfl, by decide, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩, fun h => h rfl, by decide,
    Run.cons (Step.changeCtmProxyAdmin rfl (by decide)) Run.nil, rfl, ?_, ?_⟩
  · intro H h
    exact ⟨_, _, hdef, hsame.trans hdef, rfl⟩
  · intro hsh
    exact absurd hsh.ctmUnderProxyAdmin (by decide)

theorem AcceptedLegWitness : Properties.AcceptedLegWitness := by
  have hsame : domainHolders (nbAfterLeg nbState0) 2 = some nbReading := by decide
  refine ⟨nbAfterLeg nbState0, nb_shape0, ?_, by decide, by decide⟩
  intro H h
  exact ⟨nb_precheck rfl, nb_leg_run nbState0 rfl rfl, _, _, nb_reading0, hsame, rfl⟩

theorem EngineRepointAndRebindRejected : Properties.EngineRepointAndRebindRejected := by
  refine ⟨nbRepointed, nbRebound, nb_shape0, nb_precheck rfl,
    Run.cons (Step.setServerNotifier rfl) Run.nil, by decide, ?_, ?_,
    Run.cons (Step.setChainTypeManager rfl (by decide)) Run.nil, by decide, ?_, ?_⟩
  · intro hpc
    obtain ⟨t', _, hne, he⟩ :=
      PostCheckRejectsRepoint nbState0 nbRepointed 2 nbReading nb_reading0 (by decide) _ _ hpc
    exact hne he
  · intro hb
    exact absurd hb.ctmPointsAtNotifier (by decide)
  · intro hpc
    obtain ⟨t', _, hne, he⟩ :=
      PostCheckRejectsRebind nbState0 nbRebound 2 nbReading nb_reading0 (by decide) rfl
        (by decide) _ _ hpc
    exact hne he
  · intro hb
    exact absurd hb.notifierPointsAtCtm (by decide)

theorem CallsOutsideLegsMoveTheBinding : Properties.CallsOutsideLegsMoveTheBinding := by
  refine ⟨nbEnv, nbState0, nbRepointed, nbRepointedScheduled, nbRebound, nbReboundScheduled,
    1, 2, 6, 7, 9, 5, 0, 1, 12, nb_env_answers, nb_shape0, by decide, by decide, rfl,
    nb_gate_closed rfl, nb_bound_refuses,
    Step.setServerNotifier rfl, ?_, ?_, nb_gate_open (by decide) (by decide),
    Step.setChainTypeManager rfl (by decide), ?_, ?_, nb_gate_open (by decide) (by decide)⟩
  · intro hb
    exact absurd hb.ctmPointsAtNotifier (by decide)
  · exact Step.setUpgradeTimestamp rfl (by decide) rfl (Or.inl rfl)
  · intro hb
    exact absurd hb.notifierPointsAtCtm (by decide)
  · exact Step.setUpgradeTimestamp rfl (by decide) rfl (Or.inl rfl)

theorem DomainRunWitness : Properties.DomainRunWitness := by
  have hA : domainHolders nbScheduled 2 = some nbReading := by decide
  have hB : domainHolders (nbAfterLeg nbScheduled) 2 = some nbReading := by decide
  refine ⟨nbAfterLeg nbScheduled, nbReading, nb_shape0, ?_, by decide⟩
  intro H h
  refine DomainRun.call (by decide) (by decide)
    (Step.setUpgradeTimestamp rfl (by decide) rfl (Or.inl rfl)) ?_
  exact DomainRun.leg (nb_precheck rfl) (nb_leg_run nbScheduled rfl rfl) hA hB rfl DomainRun.nil

theorem OnlyDiamondAdminSchedulesWitness : Properties.OnlyDiamondAdminSchedulesWitness := by
  have hB : domainHolders (nbAfterLeg nbState0) 2 = some nbReading := by decide
  refine ⟨nbAfterLeg nbState0, _, nbReading, nb_env_answers, nb_shape0,
    DomainRun.leg (nb_precheck rfl) (nb_leg_run nbState0 rfl rfl) nb_reading0 hB rfl
      DomainRun.nil,
    Step.setUpgradeTimestamp rfl (by decide) rfl (Or.inr trivial), by decide⟩

theorem BoundRefinementPremisesAreLoadBearing :
    Properties.BoundRefinementPremisesAreLoadBearing := by
  refine ⟨⟨nbEnv, nbTimed, nbRebound, nbReboundScheduled, 5, 0, 1, 12, nb_env_answers,
      nb_agrees rfl rfl rfl nb_rebound_live, ?_, by decide, by decide, nb_timed_refuses⟩,
    ⟨nbEnvWrongAdmin, nbTimed, nbState0, nbScheduled, 6, 1, 2, 5, 0, 1, 12,
      ⟨⟨rfl, by decide, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩,
      nb_agrees rfl rfl rfl nb_state0_live, ?_, by decide, by decide, nb_timed_refuses⟩⟩
  · exact Step.setUpgradeTimestamp (n := 6) rfl (by decide) rfl (Or.inl rfl)
  · exact Step.setUpgradeTimestamp (n := 6) rfl (by decide) rfl (Or.inl rfl)

theorem BoundPremisesSatisfiable : Properties.BoundPremisesSatisfiable := by
  exact ⟨nbEnv, nbTimed, nbState0, nbScheduled, 6, 1, 2, 3, 0, 12, nb_env_answers, nb_shape0,
    nb_agrees rfl rfl rfl nb_state0_live,
    Step.setUpgradeTimestamp rfl (by decide) rfl (Or.inl rfl),
    by decide, by decide, by decide⟩

end Contracts.NotifierBindingV35
