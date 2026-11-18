import EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.DomainHoldersV35

/-!
# Proofs: what the domain-holder check catches, at `b17415d`

`leg_eq_some` unpacks a successful `b17415d` leg into its checks, `leg_of_holders_eq` and
`leg_of_preimage_eq` build one. `leg_pins` is the core: a successful leg read the same CTM
tuple (and notifier reads) before and after the engine, or the compared pair collides.
`MovedCtmCaught` combines it with the check at `:75-77`. The `d9f6789` leg has its own
`leg_eq_some`, `leg_of_holders_eq` and `leg_of_reads_unchanged` in `D9`, and
`AliasingPassesAtD9CaughtAtB17` computes the three aliasing calls (`aliasCtmProxyAdmin_eq`).
The witnesses are the concrete worlds of `DomainHoldersWitness`.
-/

namespace Contracts.DomainHoldersV35

/-! ## Mappings and reads -/

@[simp] lemma upd_same {α : Type} (f : Address → α) (p : Address) (v : α) : upd f p v p = v := by
  simp [upd]

lemma upd_ne {α : Type} (f : Address → α) {q p : Address} (v : α) (h : q ≠ p) :
    upd f p v q = f q := by
  simp [upd, h]

lemma adminCall_of_ne {w : World} {s p : Address} (h : s ≠ (w.proxy p).adminSlot) :
    adminCall w s p = w.adminAnswer p := by
  simp [adminCall, h]

lemma adminCall_of_eq {w : World} {s p : Address} (h : (w.proxy p).adminSlot = s) :
    adminCall w s p = some s := by
  simp [adminCall, h]

/-! ## Unpacking the holder reads -/

lemma ctmTuple_eq_some {B : Bindings} {w : World} {e : List Word} :
    ctmTuple B w = some e ↔ B.self ≠ (w.proxy B.ctm).adminSlot ∧ ∃ a ca,
      adminCall w B.self B.ctm = some a ∧ adminCall w B.pa B.ctm = some ca
      ∧ e = [w.paOwner, w.owner B.ctm, w.pendingOwner B.ctm, a, ca, w.serverNotifier] := by
  unfold ctmTuple
  by_cases hs : B.self = (w.proxy B.ctm).adminSlot
  · simp [hs]
  · simp only [hs, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
    rcases h1 : adminCall w B.self B.ctm with _ | a <;>
      rcases h2 : adminCall w B.pa B.ctm with _ | ca <;> simp [eq_comm]

lemma notifierReads_eq_some {B : Bindings} {w : World} {n : Address} {r : List Word} :
    notifierReads B w n = some r ↔ B.self ≠ (w.proxy n).adminSlot ∧ ∃ na,
      adminCall w B.pa n = some na ∧ r = [w.owner n, w.pendingOwner n, na, w.notifierCtm n] := by
  unfold notifierReads
  by_cases hs : B.self = (w.proxy n).adminSlot
  · simp [hs]
  · simp only [hs, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
    rcases h1 : adminCall w B.pa n with _ | na <;> simp [eq_comm]

lemma ctmTuple_shape {B : Bindings} {w : World} {e : List Word} (he : ctmTuple B w = some e) :
    e.length = 6 ∧ e.getLast? = some w.serverNotifier := by
  obtain ⟨-, a, ca, -, -, rfl⟩ := ctmTuple_eq_some.mp he
  simp

lemma notifierReads_length {B : Bindings} {w : World} {n : Address} {r : List Word}
    (hr : notifierReads B w n = some r) : r.length = 4 := by
  obtain ⟨-, na, -, rfl⟩ := notifierReads_eq_some.mp hr
  simp

/-- What `holderPreimage` is when there is a CTM. -/
lemma holderPreimage_eq_some {B : Bindings} {H : Hash} {w : World} {p : List Word}
    (hctm : B.ctm ≠ 0) (hp : holderPreimage B H w = some p) :
    ∃ e, ctmTuple B w = some e ∧ (w.serverNotifier = 0 → p = e)
      ∧ (w.serverNotifier ≠ 0 →
          ∃ r, notifierReads B w w.serverNotifier = some r ∧ p = H e :: r) := by
  unfold holderPreimage at hp
  simp only [hctm, ↓reduceIte] at hp
  rcases he : ctmTuple B w with _ | e
  · rw [he] at hp; cases hp
  · rw [he] at hp
    refine ⟨e, rfl, fun hn => ?_, fun hn => ?_⟩
    · simp only [hn, ↓reduceIte, Option.some.injEq] at hp
      exact hp.symm
    · simp only [hn, ↓reduceIte, Option.map_eq_some_iff] at hp
      obtain ⟨r, hr, rfl⟩ := hp
      exact ⟨r, hr, rfl⟩

lemma holderPreimage_of_reads {B : Bindings} {H : Hash} {w : World} {e r : List Word}
    (hctm : B.ctm ≠ 0) (hc : ctmTuple B w = some e) (hn : w.serverNotifier ≠ 0)
    (hr : notifierReads B w w.serverNotifier = some r) :
    holderPreimage B H w = some (H e :: r) := by
  simp [holderPreimage, hctm, hc, hn, hr]

/-- Equal holder reads give equal preimages, for every hash. -/
lemma holderPreimage_congr {B : Bindings} (H : Hash) {w v : World}
    (hpa : v.paOwner = w.paOwner) (hc : ctmTuple B v = ctmTuple B w)
    (hn : v.serverNotifier = w.serverNotifier)
    (hnr : notifierReads B v w.serverNotifier = notifierReads B w w.serverNotifier) :
    holderPreimage B H v = holderPreimage B H w := by
  simp only [holderPreimage, hpa, hc, hn, hnr]

/-! ## Unpacking and building a `b17415d` leg -/

/-- A successful leg passed every check. -/
lemma leg_eq_some {E : Env} {B : Bindings} {tr : Address} {m : Manifest} {eng : Engine}
    {w v : World} (h : leg E B tr m eng w = some v) :
    Prechecks E B tr m ∧ CtmAdminOk B w ∧ ∃ before, domainHolders B E.H w = some before
      ∧ eng B.self (buildContext B tr m) m.proxyUpgrades w = some v
      ∧ v.execOwner = w.execOwner ∧ v.execPendingOwner = w.execPendingOwner
      ∧ domainHolders B E.H v = some before ∧ rowsApplied B v (toRows m.proxyUpgrades) := by
  unfold leg at h
  by_cases hp : Prechecks E B tr m
  · by_cases hok : CtmAdminOk B w
    · simp only [hp, hok, not_true_eq_false, ↓reduceIte] at h
      refine ⟨hp, hok, ?_⟩
      split at h
      · cases h
      · rename_i before hb
        split at h
        · cases h
        · rename_i v' hv
          by_cases ho : v'.execOwner ≠ w.execOwner ∨ v'.execPendingOwner ≠ w.execPendingOwner
          · simp only [ho, ↓reduceIte] at h; cases h
          · simp only [ho, ↓reduceIte] at h
            simp only [not_or, ne_eq, not_not] at ho
            split at h
            · cases h
            · rename_i after ha
              by_cases hne : after = before
              · subst hne
                simp only [ne_eq, not_true_eq_false, ↓reduceIte] at h
                by_cases hr : rowsApplied B v' (toRows m.proxyUpgrades)
                · simp only [hr, ↓reduceIte] at h
                  cases h
                  exact ⟨after, hb, hv, ho.1, ho.2, ha, hr⟩
                · simp only [hr, ↓reduceIte] at h; cases h
              · simp only [ne_eq, hne, not_false_eq_true, ↓reduceIte] at h; cases h
    · simp only [hp, hok, not_true_eq_false, not_false_eq_true, ↓reduceIte] at h; cases h
  · simp only [hp, not_false_eq_true, ↓reduceIte] at h; cases h

/-- A leg passes when the check at `:75-77` passes and the engine returns a world whose holder
hash equals the pre-state's, whose executor ownership is unchanged and whose rows are
applied. -/
lemma leg_of_holders_eq {E : Env} {B : Bindings} {tr : Address} {m : Manifest}
    {eng : Engine} {w v : World} {h : Word}
    (hp : Prechecks E B tr m) (hok : CtmAdminOk B w)
    (hb : domainHolders B E.H w = some h)
    (hv : eng B.self (buildContext B tr m) m.proxyUpgrades w = some v)
    (ho : v.execOwner = w.execOwner) (hpo : v.execPendingOwner = w.execPendingOwner)
    (ha : domainHolders B E.H v = some h)
    (hr : rowsApplied B v (toRows m.proxyUpgrades)) :
    leg E B tr m eng w = some v := by
  unfold leg
  simp only [hp, hok, not_true_eq_false, hb, hv, ho, hpo, ne_eq, or_self, ha, hr, ↓reduceIte]

/-- A leg passes, for the environment's hash, when the engine returns a world whose holder
preimage equals the pre-state's (and the pre-state's reads succeed). -/
lemma leg_of_preimage_eq {E : Env} {B : Bindings} {tr : Address} {m : Manifest}
    {eng : Engine} {w v : World}
    (hp : Prechecks E B tr m) (hok : CtmAdminOk B w)
    (hb : (holderPreimage B E.H w).isSome)
    (hv : eng B.self (buildContext B tr m) m.proxyUpgrades w = some v)
    (ho : v.execOwner = w.execOwner) (hpo : v.execPendingOwner = w.execPendingOwner)
    (hpre : holderPreimage B E.H v = holderPreimage B E.H w)
    (hr : rowsApplied B v (toRows m.proxyUpgrades)) :
    leg E B tr m eng w = some v := by
  obtain ⟨p, hpw⟩ := Option.isSome_iff_exists.mp hb
  exact leg_of_holders_eq (h := E.H p) hp hok (by simp [domainHolders, hpw]) hv ho hpo
    (by simp [domainHolders, hpre, hpw]) hr

/-- **The core.** A successful leg with a CTM read the same CTM tuple before and after the
engine, and with a nonzero pre-leg notifier the same notifier reads, or the compared pair
collides. -/
lemma leg_pins {E : Env} {B : Bindings} {tr : Address} {m : Manifest} {eng : Engine}
    {w v : World} (hl : leg E B tr m eng w = some v) (hctm : B.ctm ≠ 0) :
    (∃ e, ctmTuple B w = some e ∧ ctmTuple B v = some e
       ∧ (w.serverNotifier ≠ 0 → ∃ r, notifierReads B w w.serverNotifier = some r
            ∧ notifierReads B v w.serverNotifier = some r))
    ∨ HolderPairCollides B E.H w v := by
  obtain ⟨_, _, before, hb, _, _, _, ha, _⟩ := leg_eq_some hl
  unfold domainHolders at hb ha
  obtain ⟨p, hp, hpb⟩ := Option.map_eq_some_iff.mp hb
  obtain ⟨p', hp', hpb'⟩ := Option.map_eq_some_iff.mp ha
  by_cases hpp : p = p'
  · subst hpp
    obtain ⟨e, he, he0, he1⟩ := holderPreimage_eq_some hctm hp
    obtain ⟨e', he', he0', he1'⟩ := holderPreimage_eq_some hctm hp'
    obtain ⟨hlen, hlast⟩ := ctmTuple_shape he
    obtain ⟨hlen', hlast'⟩ := ctmTuple_shape he'
    by_cases hn : w.serverNotifier = 0 <;> by_cases hn' : v.serverNotifier = 0
    · -- both without a notifier: the preimage is the CTM tuple itself
      have hee : e = e' := (he0 hn).symm.trans (he0' hn')
      subst hee
      exact Or.inl ⟨e, he, he', fun h => absurd hn h⟩
    · exfalso
      obtain ⟨r', hr', hpr'⟩ := he1' hn'
      have hl1 := congrArg List.length ((he0 hn).symm.trans hpr')
      simp [hlen, notifierReads_length hr'] at hl1
    · exfalso
      obtain ⟨r, hr, hpr⟩ := he1 hn
      have hl1 := congrArg List.length (hpr.symm.trans (he0' hn'))
      simp [hlen', notifierReads_length hr] at hl1
    · obtain ⟨r, hr, hpr⟩ := he1 hn
      obtain ⟨r', hr', hpr'⟩ := he1' hn'
      have hcons := hpr.symm.trans hpr'
      simp only [List.cons.injEq] at hcons
      obtain ⟨hH, hrr⟩ := hcons
      by_cases hee : e = e'
      · subst hee
        have hnn : v.serverNotifier = w.serverNotifier := by
          rw [hlast] at hlast'; exact (Option.some.inj hlast').symm
        refine Or.inl ⟨e, he, he', fun _ => ⟨r, hr, ?_⟩⟩
        rw [← hnn, hr', hrr]
      · exact Or.inr (Or.inl ⟨hctm, e, e', he, he', hee, hH⟩)
  · exact Or.inr (Or.inr ⟨p, p', hp, hp', hpp, by rw [hpb, hpb']⟩)

/-! ## Operations -/

lemma ctmSetPendingAdmin_owner {w : World} {ctm sender : Address} (y : Address)
    (hs : sender ≠ (w.proxy ctm).adminSlot) (ho : w.owner ctm = sender) :
    ctmSetPendingAdmin w ctm sender y = some { w with ctmPendingAdmin := y } := by
  simp [ctmSetPendingAdmin, hs, ho]

lemma paChangeProxyAdmin_eq {w : World} {pa sender p x : Address}
    (ho : sender = w.paOwner) (ha : pa = (w.proxy p).adminSlot) (hx : x ≠ 0) :
    paChangeProxyAdmin w pa sender p x
      = some { w with proxy := upd w.proxy p { (w.proxy p) with adminSlot := x } } := by
  simp [paChangeProxyAdmin, ho, ← ha, hx]

/-- The three aliasing calls, when the executor owns the CTM and the `ProxyAdmin` and the
`ProxyAdmin` administers the CTM proxy. -/
lemma aliasCtmProxyAdmin_eq {B : Bindings} {tr : Address} {m : Manifest} {w : World}
    {X : Address} (hslot : (w.proxy B.ctm).adminSlot = B.pa) (hsp : B.self ≠ B.pa)
    (hown : w.owner B.ctm = B.self) (hpaown : w.paOwner = B.self) (hX0 : X ≠ 0) :
    aliasCtmProxyAdmin X B.self (buildContext B tr m) m.proxyUpgrades w
      = some { w with adminAnswer := upd w.adminAnswer B.ctm (some B.pa), ctmPendingAdmin := 0,
                      proxy := upd w.proxy B.ctm { (w.proxy B.ctm) with adminSlot := X } } := by
  have hs1 : B.self ≠ (w.proxy B.ctm).adminSlot := by rw [hslot]; exact hsp
  have h1 := ctmSetPendingAdmin_owner B.pa hs1 hown
  have h2 : paReinstallAndAcceptAdmin { w with ctmPendingAdmin := B.pa } B.pa B.self B.ctm
      = some { w with adminAnswer := upd w.adminAnswer B.ctm (some B.pa),
                       ctmPendingAdmin := 0 } := by
    simp [paReinstallAndAcceptAdmin, hpaown, hslot, ctmAcceptAdminBody]
  have h3 := paChangeProxyAdmin_eq
    (w := { w with adminAnswer := upd w.adminAnswer B.ctm (some B.pa), ctmPendingAdmin := 0 })
    (pa := B.pa) (sender := B.self) (p := B.ctm) hpaown.symm hslot.symm hX0
  show (ctmSetPendingAdmin w B.ctm B.self B.pa).bind _ = _
  rw [h1]
  show (paReinstallAndAcceptAdmin _ B.pa B.self B.ctm).bind _ = _
  rw [h2]
  exact h3

/-! ## The standing configuration -/

lemma ExecutorHoldsCtm.self_ne_slot {B : Bindings} {w : World} (h : ExecutorHoldsCtm B w) :
    B.self ≠ (w.proxy B.ctm).adminSlot := by
  rw [h.paAdministersCtm]; exact h.selfNotPa

/-- With the check at `:75-77` passing, the `b17415d` CTM tuple reads. -/
lemma ExecutorHoldsCtm.ctmTuple_eq {B : Bindings} {w : World} (h : ExecutorHoldsCtm B w)
    (hok : CtmAdminOk B w) :
    ∃ a, a ≠ B.pa ∧ adminCall w B.self B.ctm = some a ∧ ctmTuple B w
      = some [w.paOwner, w.owner B.ctm, w.pendingOwner B.ctm, a, B.pa, w.serverNotifier] := by
  rcases hok with h0 | ⟨a, ha, hne⟩
  · exact absurd h0 h.ctmNonzero
  refine ⟨a, hne, ha, ctmTuple_eq_some.mpr ⟨h.self_ne_slot, a, B.pa, ha,
    adminCall_of_eq h.paAdministersCtm, rfl⟩⟩

lemma ExecutorHoldsCtm.preimage_isSome {B : Bindings} {w : World} (h : ExecutorHoldsCtm B w)
    (hok : CtmAdminOk B w) (H : Hash) : (holderPreimage B H w).isSome := by
  obtain ⟨a, -, -, hc⟩ := h.ctmTuple_eq hok
  by_cases hn : w.serverNotifier = 0
  · simp [holderPreimage, h.ctmNonzero, hc, hn]
  · rcases h.notifierReadable with h0 | ⟨hs, hna⟩
    · exact absurd h0 hn
    · obtain ⟨na, hna⟩ := Option.isSome_iff_exists.mp hna
      rw [holderPreimage_of_reads h.ctmNonzero hc hn
        (notifierReads_eq_some.mpr ⟨hs, na, hna, rfl⟩)]
      rfl

/-! ## (a) -/

theorem PassingLegKeepsHolderReads : Properties.PassingLegKeepsHolderReads := by
  intro E B tr m eng w w' hl
  by_cases hctm : B.ctm = 0
  · obtain ⟨_, _, before, hb, _, _, _, ha, _⟩ := leg_eq_some hl
    simp only [domainHolders, holderPreimage, hctm, ↓reduceIte, Option.map_some,
      Option.some.injEq] at hb ha
    by_cases hpo : w'.paOwner = w.paOwner
    · exact Or.inl ⟨hpo, fun h => absurd hctm h⟩
    · refine Or.inr (Or.inr ⟨[w.paOwner], [w'.paOwner], ?_, ?_, ?_, ?_⟩)
      · simp [holderPreimage, hctm]
      · simp [holderPreimage, hctm]
      · intro h
        simp only [List.cons.injEq, and_true] at h
        exact hpo h.symm
      · rw [hb, ha]
  · rcases leg_pins hl hctm with ⟨e, he, he', hn⟩ | hcol
    · left
      obtain ⟨-, a, ca, ha, hca, rfl⟩ := ctmTuple_eq_some.mp he
      obtain ⟨-, a', ca', ha', hca', heq⟩ := ctmTuple_eq_some.mp he'
      simp only [List.cons.injEq, and_true] at heq
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := heq
      refine ⟨h1.symm, fun _ => ⟨h2.symm, h3.symm, ?_, ?_, h6.symm, fun hn0 => ?_⟩⟩
      · rw [ha', ha, h4]
      · rw [hca', hca, h5]
      · obtain ⟨r, hr, hr'⟩ := hn hn0
        obtain ⟨-, na, hna, rfl⟩ := notifierReads_eq_some.mp hr
        obtain ⟨-, na', hna', heq'⟩ := notifierReads_eq_some.mp hr'
        simp only [List.cons.injEq, and_true] at heq'
        obtain ⟨g1, g2, g3, g4⟩ := heq'
        exact ⟨g1.symm, g2.symm, by rw [hna', hna, g3], g4.symm⟩
    · exact Or.inr hcol

/-! ## (b) -/

theorem MovedCtmCaught : Properties.MovedCtmCaught := by
  intro E B tr m eng w w' hctm hpre heng hpost
  rcases hl : leg E B tr m eng w with _ | v
  · exact Or.inl rfl
  right
  obtain ⟨_, hok, _, _, hv, _⟩ := leg_eq_some hl
  rw [heng] at hv
  cases hv
  rcases leg_pins hl hctm with ⟨e, he, he', -⟩ | hcol
  · exfalso
    obtain ⟨-, a, ca, ha, hca, rfl⟩ := ctmTuple_eq_some.mp he
    obtain ⟨hs', a', ca', ha', hca', heq⟩ := ctmTuple_eq_some.mp he'
    simp only [List.cons.injEq, and_true] at heq
    obtain ⟨-, -, -, h4, h5, -⟩ := heq
    -- Before: `getProxyAdmin(ctm)` is the slot, the `ProxyAdmin`; `admin()` is not.
    have hca0 : ca = B.pa := by
      rw [adminCall_of_eq hpre] at hca; exact (Option.some.inj hca).symm
    rcases hok with h0 | ⟨a0, ha0, hne⟩
    · exact hctm h0
    have haa : a = a0 := by rw [ha] at ha0; exact Option.some.inj ha0
    -- After: both `admin()` calls fall through to the implementation.
    have hpa' : B.pa ≠ (w'.proxy B.ctm).adminSlot := fun h => hpost h.symm
    rw [adminCall_of_ne hs'] at ha'
    rw [adminCall_of_ne hpa', ha'] at hca'
    have hac : a' = ca' := Option.some.inj hca'
    exact hne (by rw [← haa, h4, hac, ← h5, hca0])
  · exact hcol

/-! ## (c) -/

theorem CtmAdminIsProxyAdminReverts : Properties.CtmAdminIsProxyAdminReverts := by
  intro E B tr m eng w hctm hadm
  rcases hl : leg E B tr m eng w with _ | v
  · rfl
  exfalso
  obtain ⟨_, hok, _⟩ := leg_eq_some hl
  rcases hok with h0 | ⟨a, ha, hne⟩
  · exact hctm h0
  · rw [hadm] at ha; exact hne (Option.some.inj ha).symm

/-! ## (d) -/

theorem MovedNotifierReverts : Properties.MovedNotifierReverts := by
  intro E B tr m eng w w' hctm heng hn0 hslot hnone
  rcases hl : leg E B tr m eng w with _ | v
  · rfl
  exfalso
  obtain ⟨_, _, before, _, hv, _, _, ha, _⟩ := leg_eq_some hl
  rw [heng] at hv
  cases hv
  unfold domainHolders at ha
  obtain ⟨p', hp', -⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨_, -, -, he1⟩ := holderPreimage_eq_some hctm hp'
  obtain ⟨r, hr, -⟩ := he1 hn0
  obtain ⟨-, na, hna, -⟩ := notifierReads_eq_some.mp hr
  have hpa : B.pa ≠ (w'.proxy w'.serverNotifier).adminSlot := fun h => hslot h.symm
  rw [adminCall_of_ne hpa, hnone] at hna
  cases hna

/-! ## (e) -/

theorem CtmPendingAdminOutsideHash : Properties.CtmPendingAdminOutsideHash := by
  intro E B tr m w Y hp hh hok hr
  have heng : setCtmPendingAdmin Y B.self (buildContext B tr m) m.proxyUpgrades w
      = some { w with ctmPendingAdmin := Y } :=
    ctmSetPendingAdmin_owner Y hh.self_ne_slot hh.ownsCtm
  exact leg_of_preimage_eq hp hok (hh.preimage_isSome hok E.H) heng rfl rfl rfl hr

/-! ## The `d9f6789` leg -/

namespace D9

/-- A successful `d9f6789` leg passed every check. -/
lemma leg_eq_some {E : Env} {B : Bindings} {tr : Address} {m : Manifest} {eng : Engine}
    {w v : World} (h : D9.leg E B tr m eng w = some v) :
    Prechecks E B tr m ∧ ∃ n before, D9.preNotifier B w = some n
      ∧ D9.domainHolders B E.H w n = some before
      ∧ eng B.self (buildContext B tr m) m.proxyUpgrades w = some v
      ∧ v.execOwner = w.execOwner ∧ v.execPendingOwner = w.execPendingOwner
      ∧ D9.domainHolders B E.H v n = some before
      ∧ rowsApplied B v (toRows m.proxyUpgrades) := by
  unfold D9.leg at h
  by_cases hp : Prechecks E B tr m
  · simp only [hp, not_true_eq_false, ↓reduceIte] at h
    refine ⟨hp, ?_⟩
    split at h
    · cases h
    · rename_i n hn
      split at h
      · cases h
      · rename_i before hb
        split at h
        · cases h
        · rename_i v' hv
          by_cases ho : v'.execOwner ≠ w.execOwner ∨ v'.execPendingOwner ≠ w.execPendingOwner
          · simp only [ho, ↓reduceIte] at h; cases h
          · simp only [ho, ↓reduceIte] at h
            simp only [not_or, ne_eq, not_not] at ho
            split at h
            · cases h
            · rename_i after ha
              by_cases hne : after = before
              · subst hne
                simp only [ne_eq, not_true_eq_false, ↓reduceIte] at h
                by_cases hr : rowsApplied B v' (toRows m.proxyUpgrades)
                · simp only [hr, ↓reduceIte] at h
                  cases h
                  exact ⟨n, after, hn, hb, hv, ho.1, ho.2, ha, hr⟩
                · simp only [hr, ↓reduceIte] at h; cases h
              · simp only [ne_eq, hne, not_false_eq_true, ↓reduceIte] at h; cases h
  · simp only [hp, not_false_eq_true, ↓reduceIte] at h; cases h

/-- A `d9f6789` leg passes when the engine returns a world whose holder hash equals the
pre-state's, whose executor ownership is unchanged and whose rows are applied. -/
lemma leg_of_holders_eq {E : Env} {B : Bindings} {tr : Address} {m : Manifest}
    {eng : Engine} {w v : World} {n : Address} {h : Word}
    (hp : Prechecks E B tr m) (hn : D9.preNotifier B w = some n)
    (hb : D9.domainHolders B E.H w n = some h)
    (hv : eng B.self (buildContext B tr m) m.proxyUpgrades w = some v)
    (ho : v.execOwner = w.execOwner) (hpo : v.execPendingOwner = w.execPendingOwner)
    (ha : D9.domainHolders B E.H v n = some h)
    (hr : rowsApplied B v (toRows m.proxyUpgrades)) :
    D9.leg E B tr m eng w = some v := by
  unfold D9.leg
  simp only [hp, not_true_eq_false, hn, hb, hv, ho, hpo, ne_eq, or_self, ha, hr, ↓reduceIte]

/-- Equal `d9f6789` holder reads give equal holder hashes, for every hash. -/
lemma domainHolders_congr {B : Bindings} (H : Hash) {w v : World} {n : Address}
    (hpa : v.paOwner = w.paOwner) (hc : D9.ctmWords B v = D9.ctmWords B w)
    (hn : D9.notifierReads B v n = D9.notifierReads B w n) :
    D9.domainHolders B H v n = D9.domainHolders B H w n := by
  simp only [D9.domainHolders, D9.notifierWords, hc, hn, hpa]

/-- A `d9f6789` leg passes, for every hash, when the engine returns a world whose holder reads
equal the pre-state's, whose executor ownership is unchanged and whose rows are applied. -/
lemma leg_of_reads_unchanged {E : Env} {B : Bindings} {tr : Address} {m : Manifest}
    {eng : Engine} {w v : World} {n : Address}
    (hp : Prechecks E B tr m) (hn : D9.preNotifier B w = some n)
    (hb : (D9.domainHolders B E.H w n).isSome)
    (hv : eng B.self (buildContext B tr m) m.proxyUpgrades w = some v)
    (ho : v.execOwner = w.execOwner) (hpo : v.execPendingOwner = w.execPendingOwner)
    (hpa : v.paOwner = w.paOwner) (hc : D9.ctmWords B v = D9.ctmWords B w)
    (hnr : D9.notifierReads B v n = D9.notifierReads B w n)
    (hr : rowsApplied B v (toRows m.proxyUpgrades)) :
    D9.leg E B tr m eng w = some v := by
  obtain ⟨before, hbefore⟩ := Option.isSome_iff_exists.mp hb
  exact D9.leg_of_holders_eq hp hn hbefore hv ho hpo
    (by rw [D9.domainHolders_congr E.H hpa hc hnr, hbefore]) hr

lemma ctmWords_of_admin {B : Bindings} {w : World} (hs : B.self ≠ (w.proxy B.ctm).adminSlot)
    (ha : (w.proxy B.ctm).adminSlot = B.pa) :
    D9.ctmWords B w = some [w.paOwner, w.owner B.ctm, w.pendingOwner B.ctm, B.pa] := by
  simp [D9.ctmWords, hs, adminCall_of_eq ha]

lemma preNotifier_of_holds {B : Bindings} {w : World} (h : ExecutorHoldsCtm B w) :
    D9.preNotifier B w = some w.serverNotifier := by
  simp [D9.preNotifier, h.ctmNonzero, fallthrough, h.self_ne_slot]

lemma holders_isSome_of_holds {B : Bindings} {w : World} (h : ExecutorHoldsCtm B w)
    (H : Hash) : (D9.domainHolders B H w w.serverNotifier).isSome := by
  have hc := D9.ctmWords_of_admin h.self_ne_slot h.paAdministersCtm
  by_cases hn : w.serverNotifier = 0
  · simp [D9.domainHolders, h.ctmNonzero, hn, hc]
  · rcases h.notifierReadable with h0 | ⟨hs, hna⟩
    · exact absurd h0 hn
    · obtain ⟨na, hna⟩ := Option.isSome_iff_exists.mp hna
      simp [D9.domainHolders, h.ctmNonzero, hn, D9.notifierWords, hc, D9.notifierReads, hs, hna]

end D9

/-! ## (f) -/

theorem MovedCtmWithCtmRowReverts : Properties.MovedCtmWithCtmRowReverts := by
  intro E B tr m eng w w' heng hpost himpl ⟨r, hr, hrp⟩
  have hpa' : B.pa ≠ (w'.proxy B.ctm).adminSlot := fun h => hpost h.symm
  have hnot : ¬ rowsApplied B w' (toRows m.proxyUpgrades) := by
    intro hrows
    have := hrows r hr
    rw [hrp] at this
    simp [getProxyImplementation, hpa', himpl] at this
  constructor
  · rcases hl : leg E B tr m eng w with _ | v
    · rfl
    exfalso
    obtain ⟨_, _, _, _, hv, _, _, _, hrows⟩ := leg_eq_some hl
    rw [heng] at hv
    cases hv
    exact hnot hrows
  · rcases hl : D9.leg E B tr m eng w with _ | v
    · rfl
    exfalso
    obtain ⟨_, _, _, _, _, hv, _, _, _, hrows⟩ := D9.leg_eq_some hl
    rw [heng] at hv
    cases hv
    exact hnot hrows

/-! ## (g) -/

theorem AliasingPassesAtD9CaughtAtB17 : Properties.AliasingPassesAtD9CaughtAtB17 := by
  intro E B tr m pre w₀ w₁ X hp hh hpre hf hrows hnot hX0 hXs hXpa
  set n := w₀.serverNotifier with hndef
  have hnc : n ≠ B.ctm := hh.notifierNotCtm
  have hslot : (w₁.proxy B.ctm).adminSlot = B.pa := by
    rw [hf.ctmProxy]; exact hh.paAdministersCtm
  have hown : w₁.owner B.ctm = B.self := by rw [hf.ctmOwner]; exact hh.ownsCtm
  have hpaown : w₁.paOwner = B.self := by rw [hf.paOwner]; exact hh.ownsPa
  set w₂ : World :=
    { w₁ with adminAnswer := upd w₁.adminAnswer B.ctm (some B.pa), ctmPendingAdmin := 0,
              proxy := upd w₁.proxy B.ctm { (w₁.proxy B.ctm) with adminSlot := X } } with hw₂
  have halias : aliasCtmProxyAdmin X B.self (buildContext B tr m) m.proxyUpgrades w₁
      = some w₂ := aliasCtmProxyAdmin_eq hslot hh.selfNotPa hown hpaown hX0
  have heng : (pre.andThen (aliasCtmProxyAdmin X)) B.self (buildContext B tr m)
      m.proxyUpgrades w₀ = some w₂ := by
    show (pre B.self (buildContext B tr m) m.proxyUpgrades w₀).bind _ = _
    rw [hpre]
    exact halias
  -- Field facts about `w₂`.
  have hw2proxy : ∀ q, q ≠ B.ctm → w₂.proxy q = w₁.proxy q := by
    intro q hq; simp [hw₂, upd_ne _ _ hq]
  have hw2slot : (w₂.proxy B.ctm).adminSlot = X := by simp [hw₂]
  have hw2impl : (w₂.proxy B.ctm).impl = (w₀.proxy B.ctm).impl := by
    simp [hw₂, hf.ctmProxy]
  have hw2admin : w₂.adminAnswer B.ctm = some B.pa := by simp [hw₂]
  have hw2adminN : w₂.adminAnswer n = w₀.adminAnswer n := by
    simp only [hw₂]; rw [upd_ne _ _ hnc]; exact hf.notifierAdmin
  have hs2 : B.self ≠ (w₂.proxy B.ctm).adminSlot := by
    rw [hw2slot]; exact fun h => hXs h.symm
  have hpa2 : B.pa ≠ (w₂.proxy B.ctm).adminSlot := by
    rw [hw2slot]; exact fun h => hXpa h.symm
  -- The `d9f6789` CTM tuple, word for word.
  have hc : D9.ctmWords B w₂ = D9.ctmWords B w₀ := by
    rw [D9.ctmWords_of_admin hh.self_ne_slot hh.paAdministersCtm]
    simp only [D9.ctmWords, hs2, ↓reduceIte, adminCall_of_ne hpa2, hw2admin, Option.map_some]
    simp [hw₂, hf.paOwner, hf.ctmOwner, hf.ctmPendingOwner]
  -- The `d9f6789` notifier reads are untouched.
  have hnr : D9.notifierReads B w₂ n = D9.notifierReads B w₀ n := by
    have hpx : w₂.proxy n = w₀.proxy n := by rw [hw2proxy n hnc, hf.notifierProxy]
    have how : w₂.owner n = w₀.owner n := by simp [hw₂, hf.notifierOwner]
    have hpow : w₂.pendingOwner n = w₀.pendingOwner n := by
      simp [hw₂, hf.notifierPendingOwner]
    simp only [D9.notifierReads, adminCall, hpx, how, hpow, hw2adminN]
  have hnw : D9.notifierWords B E.H w₂ n = D9.notifierWords B E.H w₀ n := by
    simp only [D9.notifierWords, hc, hnr]
  -- The rows: none is on the CTM proxy, so the aliasing calls leave them applied.
  have hr : rowsApplied B w₂ (toRows m.proxyUpgrades) := by
    intro r hr
    have := hrows r hr
    simp only [getProxyImplementation] at this ⊢
    rw [hw2proxy r.proxy (hnot r hr)]
    simpa [hw₂] using this
  refine ⟨w₂, ?_, hw2slot, hw2impl, hw2admin, hc, hnw, ?_, ?_, ?_, ?_⟩
  · refine D9.leg_of_reads_unchanged hp (D9.preNotifier_of_holds hh)
      (D9.holders_isSome_of_holds hh E.H) heng ?_ ?_ ?_ hc hnr hr
    · simp [hw₂, hf.execOwner]
    · simp [hw₂, hf.execPendingOwner]
    · simp [hw₂, hf.paOwner]
  · intro impl himpl
    simp [tupAdminUpgradeTo, hw2slot, himpl]
  · intro a
    simp [paChangeProxyAdmin, hpa2]
  · intro impl
    simp [tupAdminUpgradeTo, hpa2]
  · exact MovedCtmCaught E B tr m _ w₀ w₂ hh.ctmNonzero hh.paAdministersCtm heng
      (by rw [hw2slot]; exact hXpa)

/-! ## Witnesses

One CTM executor: executor `1`, its `ProxyAdmin` `2`, the CTM proxy `3` (implementation `12`,
`ChainTypeManager.admin = 9`), the ServerNotifier proxy `4` (implementation `13`, no
`admin()`, `chainTypeManager() = 3`), one further proxy `5` under the same `ProxyAdmin`, and a
transition `21` whose engine is `20` and whose two-slot inventory upgrades proxy `5` to `11`. -/

namespace DomainHoldersWitness

/-- Executor `1`, `ProxyAdmin` `2`, CTM domain, CTM proxy `3`. -/
def B : Bindings := ⟨1, 2, .ctm, 3⟩

/-- Slot 0 upgrades proxy `5` to `11`; slot 1 is inert. Engine `20`. -/
def m : Manifest := ⟨.ctm, [⟨5, 11⟩, ⟨0, 0⟩], 20⟩

/-- Slot 0 upgrades the CTM proxy `3` to `12`; slot 1 is inert. Engine `20`. -/
def mCtmRow : Manifest := ⟨.ctm, [⟨3, 12⟩, ⟨0, 0⟩], 20⟩

/-- A hash separating the tuples compared here (the sum of the words), code at `20` and `21`,
two-slot inventories. -/
def E : Env := ⟨List.sum, fun a => decide (a = 20 ∨ a = 21), fun _ => 2⟩

/-- The same environment with the constant hash. -/
def EConst : Env := { E with H := fun _ => 0 }

/-- The standing configuration, with proxy `5` already at `11`. -/
def w : World where
  execOwner := 30
  execPendingOwner := 0
  paOwner := 1
  proxy := fun a =>
    if a = 3 then ⟨2, 12⟩ else if a = 4 then ⟨2, 13⟩ else if a = 5 then ⟨2, 11⟩ else ⟨0, 0⟩
  owner := fun a => if a = 3 ∨ a = 4 then 1 else 0
  pendingOwner := fun _ => 0
  adminAnswer := fun a => if a = 3 then some 9 else none
  implAnswer := fun _ => none
  ctmPendingAdmin := 0
  serverNotifier := 4
  notifierCtm := fun a => if a = 4 then 3 else 0

/-- `w` after `aliasCtmProxyAdmin 7`. -/
def wAliased : World :=
  { w with adminAnswer := upd w.adminAnswer 3 (some 2), ctmPendingAdmin := 0,
           proxy := upd w.proxy 3 { (w.proxy 3) with adminSlot := 7 } }

/-- `w` after `PA.changeProxyAdmin(ctm, 7)`. -/
def wMovedCtm : World :=
  { w with proxy := upd w.proxy 3 { (w.proxy 3) with adminSlot := 7 } }

/-- `w` after `PA.changeProxyAdmin(notifier, 7)`. -/
def wMovedNotifier : World :=
  { w with proxy := upd w.proxy 4 { (w.proxy 4) with adminSlot := 7 } }

/-- `w` with a notifier implementation that answers `admin()` with the `ProxyAdmin`. -/
def wGetter : World :=
  { w with adminAnswer := fun a => if a = 3 then some 9 else if a = 4 then some 2 else none }

/-- `wGetter` after `PA.changeProxyAdmin(notifier, 7)`. -/
def wGetterMoved : World :=
  { wGetter with proxy := upd wGetter.proxy 4 { (wGetter.proxy 4) with adminSlot := 7 } }

/-- `w` with `ChainTypeManager.admin` already the `ProxyAdmin`. -/
def wPaAdmin : World :=
  { w with adminAnswer := fun a => if a = 3 then some 2 else none }

/-- `wPaAdmin` after `PA.changeProxyAdmin(ctm, 7)`. -/
def wPaAdminMoved : World :=
  { wPaAdmin with proxy := upd wPaAdmin.proxy 3 { (wPaAdmin.proxy 3) with adminSlot := 7 } }

/-- `w` with proxy `5` still at its old implementation `10`. -/
def wOld : World := { w with proxy := upd w.proxy 5 ⟨2, 10⟩ }

/-- A rows prefix: it points proxy `5` at `11`. -/
def pre : Engine := fun _ _ _ v => some { v with proxy := upd v.proxy 5 ⟨2, 11⟩ }

/-- `wOld` after `pre`. -/
def wOldApplied : World := { wOld with proxy := upd wOld.proxy 5 ⟨2, 11⟩ }

lemma prechecks : Prechecks E B 21 m := by decide

lemma prechecks_ctmRow : Prechecks E B 21 mCtmRow := by decide

lemma holds : ExecutorHoldsCtm B w :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide, by decide, Or.inr (by decide)⟩

lemma holds_getter : ExecutorHoldsCtm B wGetter :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide, by decide, Or.inr (by decide)⟩

lemma holds_paAdmin : ExecutorHoldsCtm B wPaAdmin :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide, by decide, Or.inr (by decide)⟩

lemma holds_old : ExecutorHoldsCtm B wOld :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide, by decide, Or.inr (by decide)⟩

lemma ok : CtmAdminOk B w := by decide

lemma ok_getter : CtmAdminOk B wGetter := by decide

lemma ok_old : CtmAdminOk B wOld := by decide

lemma alias_w :
    aliasCtmProxyAdmin 7 B.self (buildContext B 21 m) m.proxyUpgrades w = some wAliased :=
  aliasCtmProxyAdmin_eq (B := B) (w := w) (by decide) (by decide) (by decide) (by decide)
    (by decide)

lemma move_ctm (mm : Manifest) :
    moveProxyAdmin B.ctm 7 B.self (buildContext B 21 mm) mm.proxyUpgrades w = some wMovedCtm :=
  paChangeProxyAdmin_eq (w := w) (pa := 2) (sender := 1) (p := 3) (by decide) (by decide)
    (by decide)

lemma move_notifier :
    moveProxyAdmin w.serverNotifier 7 B.self (buildContext B 21 m) m.proxyUpgrades w
      = some wMovedNotifier :=
  paChangeProxyAdmin_eq (w := w) (pa := 2) (sender := 1) (p := 4) (by decide) (by decide)
    (by decide)

lemma move_getter :
    moveProxyAdmin wGetter.serverNotifier 7 B.self (buildContext B 21 m) m.proxyUpgrades wGetter
      = some wGetterMoved :=
  paChangeProxyAdmin_eq (w := wGetter) (pa := 2) (sender := 1) (p := 4) (by decide) (by decide)
    (by decide)

lemma move_paAdmin :
    moveProxyAdmin B.ctm 7 B.self (buildContext B 21 m) m.proxyUpgrades wPaAdmin
      = some wPaAdminMoved :=
  paChangeProxyAdmin_eq (w := wPaAdmin) (pa := 2) (sender := 1) (p := 3) (by decide)
    (by decide) (by decide)

lemma frame : D9.HolderFrame B wOld.serverNotifier wOld wOldApplied :=
  ⟨rfl, rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end DomainHoldersWitness

open DomainHoldersWitness in
theorem PendingAdminLegWitness : Properties.PendingAdminLegWitness :=
  ⟨E, B, 21, m, w, 8, prechecks, holds, ok, by decide, by decide, by decide, by decide,
    CtmPendingAdminOutsideHash E B 21 m w 8 prechecks holds ok (by decide)⟩

open DomainHoldersWitness in
theorem MovedCtmCaughtNotVacuous : Properties.MovedCtmCaughtNotVacuous := by
  have hnc : ¬ HolderPairCollides B E.H w wAliased := by
    have hc : ctmTuple B w = some [1, 1, 0, 9, 2, 4] := by decide
    have hc' : ctmTuple B wAliased = some [1, 1, 0, 2, 2, 4] := by decide
    have ho : holderPreimage B E.H w = some [17, 1, 0, 2, 3] := by decide
    have ho' : holderPreimage B E.H wAliased = some [10, 1, 0, 2, 3] := by decide
    rintro (⟨-, e, e', he, he', -, hH⟩ | ⟨p, p', hp, hp', -, hH⟩)
    · rw [hc] at he; rw [hc'] at he'; cases he; cases he'
      exact absurd hH (by decide)
    · rw [ho] at hp; rw [ho'] at hp'; cases hp; cases hp'
      exact absurd hH (by decide)
  have hleg : leg E B 21 m (aliasCtmProxyAdmin 7) w = none := by
    rcases MovedCtmCaught E B 21 m (aliasCtmProxyAdmin 7) w wAliased (by decide) (by decide)
      alias_w (by decide) with h | h
    · exact h
    · exact absurd h hnc
  have hd9 : D9.leg E B 21 m (aliasCtmProxyAdmin 7) w = some wAliased :=
    D9.leg_of_reads_unchanged prechecks (D9.preNotifier_of_holds holds)
      (D9.holders_isSome_of_holds holds E.H) alias_w rfl rfl rfl (by decide) (by decide)
      (by decide)
  exact ⟨E, B, 21, m, w, wAliased, 7, prechecks, holds, ok, by decide, by decide, by decide,
    by decide, by decide, by decide, alias_w, by decide, hleg, hnc, hd9⟩

open DomainHoldersWitness in
theorem MovedCtmCollisionDisjunctLoadBearing :
    Properties.MovedCtmCollisionDisjunctLoadBearing := by
  refine ⟨EConst, B, 21, m, w, wAliased, 7, fun _ _ => rfl, prechecks, holds, ok, alias_w,
    by decide, ?_⟩
  exact leg_of_holders_eq (h := 0) prechecks ok (by decide) alias_w rfl rfl (by decide)
    (by decide)

open DomainHoldersWitness in
theorem CtmAdminCheckLoadBearing : Properties.CtmAdminCheckLoadBearing := by
  have hc : ctmTuple B wPaAdmin = some [1, 1, 0, 2, 2, 4] := by decide
  have hc' : ctmTuple B wPaAdminMoved = some [1, 1, 0, 2, 2, 4] := by decide
  have hnr : notifierReads B wPaAdmin 4 = some [1, 0, 2, 3] := by decide
  have hnr' : notifierReads B wPaAdminMoved 4 = some [1, 0, 2, 3] := by decide
  have hadm : adminCall wPaAdmin B.self B.ctm = some B.pa := by decide
  refine ⟨E, B, 21, m, wPaAdmin, wPaAdminMoved, 7, prechecks, holds_paAdmin, by decide, hadm,
    by decide, by decide, by decide, move_paAdmin, by decide, fun H => ⟨?_, ?_⟩, rfl, rfl,
    by decide, by decide, ?_⟩
  · rw [holderPreimage_of_reads (H := H) (by decide) hc (by decide) hnr]; rfl
  · exact holderPreimage_congr H rfl (hc'.trans hc.symm) rfl (hnr'.trans hnr.symm)
  · exact CtmAdminIsProxyAdminReverts E B 21 m _ wPaAdmin (by decide) hadm

open DomainHoldersWitness in
theorem MovedNotifierRevertsSatisfiable : Properties.MovedNotifierRevertsSatisfiable :=
  ⟨E, B, 21, m, w, wMovedNotifier, 7, prechecks, holds, ok, by decide, by decide, by decide,
    move_notifier, rfl, by decide, by decide⟩

open DomainHoldersWitness in
theorem NotifierAdminGetterLoadBearing : Properties.NotifierAdminGetterLoadBearing := by
  refine ⟨E, B, 21, m, wGetter, wGetterMoved, 7, prechecks, holds_getter, ok_getter, by decide,
    by decide, by decide, by decide, move_getter, rfl, by decide, fun H => ?_⟩
  exact leg_of_preimage_eq (E := { E with H := H }) prechecks ok_getter
    (holds_getter.preimage_isSome ok_getter H) move_getter rfl rfl
    (holderPreimage_congr H rfl (by decide) rfl (by decide)) (by decide)

open DomainHoldersWitness in
theorem MovedCtmWithCtmRowRevertsWitness : Properties.MovedCtmWithCtmRowRevertsWitness :=
  ⟨E, B, 21, mCtmRow, w, wMovedCtm, 7, prechecks_ctmRow, holds, ok, by decide, move_ctm mCtmRow,
    by decide, by decide, ⟨⟨3, 12⟩, by decide, rfl⟩⟩

open DomainHoldersWitness in
theorem AliasingPassesAtD9CaughtAtB17Satisfiable :
    Properties.AliasingPassesAtD9CaughtAtB17Satisfiable :=
  ⟨E, B, 21, m, pre, wOld, wOldApplied, 7, prechecks, holds_old, ok_old, by decide, rfl, frame,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Contracts.DomainHoldersV35
