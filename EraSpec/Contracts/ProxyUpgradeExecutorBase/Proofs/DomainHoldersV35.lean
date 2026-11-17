import EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.DomainHoldersV35

/-!
# Proofs: what the domain-holder check catches, at `d9f6789`

Three lemmas carry everything: `leg_eq_some` unpacks a successful leg into its checks,
`leg_of_holders_eq` builds one from an engine result whose holder hash equals the pre-state's,
and `leg_of_reads_unchanged` does so for every hash from equal holder reads. The refutation
`MovedCtmPassesHolderCheck` computes the three aliasing calls and applies the last lemma. The
witnesses are the concrete worlds of `Witness`.
-/

namespace Contracts.DomainHoldersV35

/-! ## Mappings -/

@[simp] lemma upd_same {α : Type} (f : Address → α) (p : Address) (v : α) : upd f p v p = v := by
  simp [upd]

lemma upd_ne {α : Type} (f : Address → α) {q p : Address} (v : α) (h : q ≠ p) :
    upd f p v q = f q := by
  simp [upd, h]

/-! ## Unpacking and building a leg -/

/-- A successful leg passed every check. -/
lemma leg_eq_some {E : Env} {B : Bindings} {tr : Address} {m : Manifest} {eng : Engine}
    {w v : World} (h : leg E B tr m eng w = some v) :
    Prechecks E B tr m ∧ ∃ n before, preNotifier B w = some n
      ∧ domainHolders B E.H w n = some before
      ∧ eng B.self (buildContext B tr m) m.proxyUpgrades w = some v
      ∧ v.execOwner = w.execOwner ∧ v.execPendingOwner = w.execPendingOwner
      ∧ domainHolders B E.H v n = some before ∧ rowsApplied B v (toRows m.proxyUpgrades) := by
  unfold leg at h
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

/-- A leg passes when the engine returns a world whose holder hash equals the pre-state's,
whose executor ownership is unchanged and whose rows are applied. -/
lemma leg_of_holders_eq {E : Env} {B : Bindings} {tr : Address} {m : Manifest}
    {eng : Engine} {w v : World} {n : Address} {h : Word}
    (hp : Prechecks E B tr m) (hn : preNotifier B w = some n)
    (hb : domainHolders B E.H w n = some h)
    (hv : eng B.self (buildContext B tr m) m.proxyUpgrades w = some v)
    (ho : v.execOwner = w.execOwner) (hpo : v.execPendingOwner = w.execPendingOwner)
    (ha : domainHolders B E.H v n = some h)
    (hr : rowsApplied B v (toRows m.proxyUpgrades)) :
    leg E B tr m eng w = some v := by
  unfold leg
  simp only [hp, not_true_eq_false, hn, hb, hv, ho, hpo, ne_eq, or_self, ha, hr, ↓reduceIte]

/-- Equal holder reads give equal holder hashes, for every hash. -/
lemma domainHolders_congr {B : Bindings} (H : Hash) {w v : World} {n : Address}
    (hpa : v.paOwner = w.paOwner) (hc : ctmWords B v = ctmWords B w)
    (hn : notifierReads B v n = notifierReads B w n) :
    domainHolders B H v n = domainHolders B H w n := by
  simp only [domainHolders, notifierWords, hc, hn, hpa]

/-- A leg passes, for every hash, when the engine returns a world whose holder reads equal the
pre-state's, whose executor ownership is unchanged and whose rows are applied. -/
lemma leg_of_reads_unchanged {E : Env} {B : Bindings} {tr : Address} {m : Manifest}
    {eng : Engine} {w v : World} {n : Address}
    (hp : Prechecks E B tr m) (hn : preNotifier B w = some n)
    (hb : (domainHolders B E.H w n).isSome)
    (hv : eng B.self (buildContext B tr m) m.proxyUpgrades w = some v)
    (ho : v.execOwner = w.execOwner) (hpo : v.execPendingOwner = w.execPendingOwner)
    (hpa : v.paOwner = w.paOwner) (hc : ctmWords B v = ctmWords B w)
    (hnr : notifierReads B v n = notifierReads B w n)
    (hr : rowsApplied B v (toRows m.proxyUpgrades)) :
    leg E B tr m eng w = some v := by
  obtain ⟨before, hbefore⟩ := Option.isSome_iff_exists.mp hb
  exact leg_of_holders_eq hp hn hbefore hv ho hpo
    (by rw [domainHolders_congr E.H hpa hc hnr, hbefore]) hr

/-- Equal tuples do not collide. -/
lemma not_collides_of_words_eq {B : Bindings} {H : Hash} {w w' : World} {n : Address}
    (hc : ctmWords B w' = ctmWords B w)
    (ho : notifierWords B H w' n = notifierWords B H w n) :
    ¬ HolderPairCollides B H w w' n := by
  rintro (⟨e, e', he, he', hne, -⟩ | ⟨-, o, o', hw, hw', hne, -⟩)
  · rw [hc, he] at he'; exact hne (Option.some.inj he')
  · rw [ho, hw] at hw'; exact hne (Option.some.inj hw')

/-! ## The operations, when their checks pass -/

lemma ctmSetPendingAdmin_owner {w : World} {ctm sender : Address} (y : Address)
    (hs : sender ≠ (w.proxy ctm).adminSlot) (ho : w.owner ctm = sender) :
    ctmSetPendingAdmin w ctm sender y = some { w with ctmPendingAdmin := y } := by
  simp [ctmSetPendingAdmin, hs, ho]

lemma paChangeProxyAdmin_eq {w : World} {pa sender p x : Address}
    (ho : sender = w.paOwner) (ha : pa = (w.proxy p).adminSlot) (hx : x ≠ 0) :
    paChangeProxyAdmin w pa sender p x
      = some { w with proxy := upd w.proxy p { (w.proxy p) with adminSlot := x } } := by
  simp [paChangeProxyAdmin, ho, ← ha, hx]

/-! ## Reads under the standing configuration -/

lemma ctmWords_of_admin {B : Bindings} {w : World} (hs : B.self ≠ (w.proxy B.ctm).adminSlot)
    (ha : (w.proxy B.ctm).adminSlot = B.pa) :
    ctmWords B w = some [w.paOwner, w.owner B.ctm, w.pendingOwner B.ctm, B.pa] := by
  have hs' : B.self ≠ B.pa := ha ▸ hs
  simp [ctmWords, hs', getProxyAdmin, ha]

lemma ExecutorHoldsCtm.self_ne_slot {B : Bindings} {w : World} (h : ExecutorHoldsCtm B w) :
    B.self ≠ (w.proxy B.ctm).adminSlot := by
  rw [h.paAdministersCtm]; exact h.selfNotPa

lemma ExecutorHoldsCtm.preNotifier_eq {B : Bindings} {w : World} (h : ExecutorHoldsCtm B w) :
    preNotifier B w = some w.serverNotifier := by
  simp [preNotifier, h.ctmNonzero, fallthrough, h.self_ne_slot]

lemma ExecutorHoldsCtm.holders_isSome {B : Bindings} {w : World} (h : ExecutorHoldsCtm B w)
    (H : Hash) : (domainHolders B H w w.serverNotifier).isSome := by
  have hc := ctmWords_of_admin h.self_ne_slot h.paAdministersCtm
  by_cases hn : w.serverNotifier = 0
  · simp [domainHolders, h.ctmNonzero, hn, hc]
  · rcases h.notifierReadable with h0 | hr
    · exact absurd h0 hn
    · obtain ⟨⟨a, b, c⟩, hrd⟩ := Option.isSome_iff_exists.mp hr
      simp [domainHolders, h.ctmNonzero, hn, notifierWords, hc, hrd]

/-- The notifier a successful or attempted leg fixed is the CTM's `serverNotifierAddress`. -/
lemma preNotifier_some {B : Bindings} {w : World} {n : Address} (hctm : B.ctm ≠ 0)
    (hn : preNotifier B w = some n) :
    B.self ≠ (w.proxy B.ctm).adminSlot ∧ n = w.serverNotifier := by
  have hs : B.self ≠ (w.proxy B.ctm).adminSlot := by
    intro hs; simp [preNotifier, hctm, fallthrough, hs] at hn
  refine ⟨hs, ?_⟩
  simp [preNotifier, hctm, fallthrough, hs] at hn
  exact hn.symm

/-! ## (a) -/

theorem MovedCtmProxyAdminCaught : Properties.MovedCtmProxyAdminCaught := by
  intro E B tr m eng w w' hctm hpre heng hpost hadm
  rcases hl : leg E B tr m eng w with _ | v
  · exact Or.inl rfl
  right
  obtain ⟨_, n, before, hn, hb, hv, _, _, ha, _⟩ := leg_eq_some hl
  rw [heng] at hv
  cases hv
  -- The notifier the leg fixed is the CTM's.
  obtain ⟨hs, hnn⟩ := preNotifier_some hctm hn
  subst hnn
  have he := ctmWords_of_admin hs hpre
  -- After the leg, `getProxyAdmin(ctm)` falls through to the CTM's `admin()`.
  have hfall : ∀ e', ctmWords B w' = some e' →
      e' ≠ [w.paOwner, w.owner B.ctm, w.pendingOwner B.ctm, B.pa] := by
    intro e' he' heq
    have hpa' : B.pa ≠ (w'.proxy B.ctm).adminSlot := fun h => hpost h.symm
    unfold ctmWords at he'
    split_ifs at he' with hs'
    simp only [getProxyAdmin, hpa', ite_false] at he'
    rcases hans : w'.adminAnswer B.ctm with _ | a
    · simp [hans] at he'
    · simp only [hans, Option.map_some, Option.some.injEq] at he'
      subst he'
      simp only [List.cons.injEq, and_true] at heq
      exact hadm (hans ▸ congrArg some heq.2.2.2)
  by_cases hn0 : w.serverNotifier = 0
  · simp only [domainHolders, hctm, ite_false, hn0, ite_true] at hb ha
    rw [he] at hb
    rcases he' : ctmWords B w' with _ | e'
    · simp [he'] at ha
    · simp only [he', Option.map_some, Option.some.injEq] at ha
      simp only [Option.map_some, Option.some.injEq] at hb
      exact Or.inl ⟨_, e', he, he', (hfall e' he').symm, by rw [hb, ha]⟩
  · simp only [domainHolders, hctm, ite_false, hn0] at hb ha
    rcases ho : notifierWords B E.H w w.serverNotifier with _ | o
    · simp [ho] at hb
    rcases ho' : notifierWords B E.H w' w.serverNotifier with _ | o'
    · simp [ho'] at ha
    simp only [ho, ho', Option.map_some, Option.some.injEq] at hb ha
    by_cases hoo : o = o'
    · -- Equal outer tuples: their first words are the two CTM hashes.
      subst hoo
      unfold notifierWords at ho ho'
      rw [he] at ho
      rcases he' : ctmWords B w' with _ | e'
      · simp [he'] at ho'
      rcases hr : notifierReads B w w.serverNotifier with _ | ⟨a, b, c⟩
      · simp [hr] at ho
      rcases hr' : notifierReads B w' w.serverNotifier with _ | ⟨a', b', c'⟩
      · simp [he', hr'] at ho'
      simp only [hr, Option.some.injEq] at ho
      simp only [he', hr', Option.some.injEq] at ho'
      rw [← ho] at ho'
      simp only [List.cons.injEq] at ho'
      exact Or.inl ⟨_, e', he, he', (hfall e' he').symm, ho'.1.symm⟩
    · exact Or.inr ⟨hn0, o, o', ho, ho', hoo, by rw [hb, ha]⟩

/-! ## (b) -/

theorem NotifierProxyAdminMoveReverts : Properties.NotifierProxyAdminMoveReverts := by
  intro E B tr m eng w w' hctm hn0 heng hpost hnone
  rcases hl : leg E B tr m eng w with _ | v
  · rfl
  exfalso
  obtain ⟨_, n, before, hn, _, hv, _, _, ha, _⟩ := leg_eq_some hl
  rw [heng] at hv
  cases hv
  obtain ⟨_, hnn⟩ := preNotifier_some hctm hn
  subst hnn
  have hpa' : B.pa ≠ (w'.proxy w.serverNotifier).adminSlot := fun h => hpost h.symm
  have hr : notifierReads B w' w.serverNotifier = none := by
    unfold notifierReads
    split_ifs
    · rfl
    · simp [getProxyAdmin, hpa', hnone]
  simp [domainHolders, hctm, hn0, notifierWords, hr] at ha

/-! ## (c) -/

theorem MovedCtmPassesHolderCheck : Properties.MovedCtmPassesHolderCheck := by
  intro E B tr m pre w₀ w₁ X hp hh hpre hf hrows hnot hX0 hXs hXpa
  set n := w₀.serverNotifier with hndef
  have hnc : n ≠ B.ctm := hh.notifierNotCtm
  have hslot : (w₁.proxy B.ctm).adminSlot = B.pa := by rw [hf.ctmProxy]; exact hh.paAdministersCtm
  have hs1 : B.self ≠ (w₁.proxy B.ctm).adminSlot := by rw [hslot]; exact hh.selfNotPa
  -- (i) `ctm.setPendingAdmin(PA)` as CTM owner.
  have hown : w₁.owner B.ctm = B.self := by rw [hf.ctmOwner]; exact hh.ownsCtm
  have h1 := ctmSetPendingAdmin_owner B.pa hs1 hown
  -- (ii) `PA.upgradeAndCall(ctm, liveImpl, acceptAdmin())`: `acceptAdmin` sees `msg.sender = PA`.
  have hpaown : w₁.paOwner = B.self := by rw [hf.paOwner]; exact hh.ownsPa
  have h2 : paReinstallAndAcceptAdmin { w₁ with ctmPendingAdmin := B.pa } B.pa B.self B.ctm
      = some { w₁ with adminAnswer := upd w₁.adminAnswer B.ctm (some B.pa),
                       ctmPendingAdmin := 0 } := by
    simp [paReinstallAndAcceptAdmin, hpaown, hslot, ctmAcceptAdminBody]
  -- (iii) `PA.changeProxyAdmin(ctm, X)`.
  have h3 := paChangeProxyAdmin_eq
    (w := { w₁ with adminAnswer := upd w₁.adminAnswer B.ctm (some B.pa), ctmPendingAdmin := 0 })
    (pa := B.pa) (sender := B.self) (p := B.ctm) hpaown.symm hslot.symm hX0
  set w₂ : World :=
    { w₁ with adminAnswer := upd w₁.adminAnswer B.ctm (some B.pa), ctmPendingAdmin := 0,
              proxy := upd w₁.proxy B.ctm { (w₁.proxy B.ctm) with adminSlot := X } } with hw₂
  have heng : (pre.andThen (aliasCtmProxyAdmin X)) B.self (buildContext B tr m)
      m.proxyUpgrades w₀ = some w₂ := by
    have halias : aliasCtmProxyAdmin X B.self (buildContext B tr m) m.proxyUpgrades w₁
        = some w₂ := by
      show (ctmSetPendingAdmin w₁ B.ctm B.self B.pa).bind _ = _
      rw [h1]
      show (paReinstallAndAcceptAdmin _ B.pa B.self B.ctm).bind _ = _
      rw [h2]
      exact h3
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
  have hs2 : B.self ≠ (w₂.proxy B.ctm).adminSlot := by rw [hw2slot]; exact fun h => hXs h.symm
  have hpa2 : B.pa ≠ (w₂.proxy B.ctm).adminSlot := by rw [hw2slot]; exact fun h => hXpa h.symm
  -- The CTM tuple, word for word.
  have hc : ctmWords B w₂ = ctmWords B w₀ := by
    rw [ctmWords_of_admin hh.self_ne_slot hh.paAdministersCtm]
    simp only [ctmWords, hs2, ite_false, getProxyAdmin, hpa2, hw2admin, Option.map_some]
    simp [hw₂, hf.paOwner, hf.ctmOwner, hf.ctmPendingOwner]
  -- The notifier reads are untouched.
  have hnr : notifierReads B w₂ n = notifierReads B w₀ n := by
    have hpx : w₂.proxy n = w₀.proxy n := by rw [hw2proxy n hnc, hf.notifierProxy]
    have how : w₂.owner n = w₀.owner n := by simp [hw₂, hf.notifierOwner]
    have hpow : w₂.pendingOwner n = w₀.pendingOwner n := by
      simp [hw₂, hf.notifierPendingOwner]
    simp only [notifierReads, getProxyAdmin, hpx, how, hpow, hw2adminN]
  have hnw : notifierWords B E.H w₂ n = notifierWords B E.H w₀ n := by
    simp only [notifierWords, hc, hnr]
  -- The rows: none is on the CTM proxy, so the aliasing calls leave them applied.
  have hr : rowsApplied B w₂ (toRows m.proxyUpgrades) := by
    intro r hr
    have := hrows r hr
    simp only [getProxyImplementation] at this ⊢
    rw [hw2proxy r.proxy (hnot r hr)]
    simpa [hw₂] using this
  refine ⟨w₂, ?_, hw2slot, hw2impl, hw2admin, hc, hnw, ?_, ?_, ?_⟩
  · refine leg_of_reads_unchanged hp hh.preNotifier_eq (hh.holders_isSome E.H) heng ?_ ?_ ?_ hc
      hnr hr
    · simp [hw₂, hf.execOwner]
    · simp [hw₂, hf.execPendingOwner]
    · simp [hw₂, hf.paOwner]
  · intro impl himpl
    simp [tupAdminUpgradeTo, hw2slot, himpl]
  · intro a
    simp [paChangeProxyAdmin, hpa2]
  · intro impl
    simp [tupAdminUpgradeTo, hpa2]

theorem MovedCtmWithCtmRowReverts : Properties.MovedCtmWithCtmRowReverts := by
  intro E B tr m eng w w' heng hpost himpl ⟨r, hr, hrp⟩
  rcases hl : leg E B tr m eng w with _ | v
  · rfl
  exfalso
  obtain ⟨_, n, before, _, _, hv, _, _, _, hrows⟩ := leg_eq_some hl
  rw [heng] at hv
  cases hv
  have hpa' : B.pa ≠ (w'.proxy B.ctm).adminSlot := fun h => hpost h.symm
  have := hrows r hr
  rw [hrp] at this
  simp [getProxyImplementation, hpa', himpl] at this

/-! ## (d) -/

theorem HolderHashIgnoresCtmAdminRole : Properties.HolderHashIgnoresCtmAdminRole := by
  intro B H w n a y
  refine ⟨rfl, fun hpa => ?_⟩
  refine domainHolders_congr H rfl ?_ ?_
  · simp [ctmWords, getProxyAdmin, hpa]
  · by_cases hn : n = B.ctm
    · subst hn; simp [notifierReads, getProxyAdmin, hpa]
    · simp [notifierReads, getProxyAdmin, upd_ne _ _ hn]

theorem CtmAdminRoleOutsideHash : Properties.CtmAdminRoleOutsideHash := by
  intro E B tr m w Y hp hh hr
  have heng : setCtmPendingAdmin Y B.self (buildContext B tr m) m.proxyUpgrades w
      = some { w with ctmPendingAdmin := Y } :=
    ctmSetPendingAdmin_owner Y hh.self_ne_slot hh.ownsCtm
  exact leg_of_reads_unchanged hp hh.preNotifier_eq (hh.holders_isSome E.H) heng rfl rfl rfl
    rfl rfl hr

theorem CtmAdminTakenByExecutorPasses : Properties.CtmAdminTakenByExecutorPasses := by
  intro E B tr m w hp hh hr
  have hs := hh.self_ne_slot
  set v : World := { w with adminAnswer := upd w.adminAnswer B.ctm (some B.self),
                            ctmPendingAdmin := 0 } with hv
  have heng : takeCtmAdmin B.self (buildContext B tr m) m.proxyUpgrades w = some v := by
    simp [takeCtmAdmin, buildContext, ctmSetPendingAdmin, hs, hh.ownsCtm, ctmAcceptAdmin,
      ctmAcceptAdminBody, hv]
  have hpa : B.pa = (w.proxy B.ctm).adminSlot := hh.paAdministersCtm.symm
  have hc : ctmWords B v = ctmWords B w := by
    simp [ctmWords, getProxyAdmin, hv, ← hpa]
  have hnr : notifierReads B v w.serverNotifier = notifierReads B w w.serverNotifier := by
    simp [notifierReads, getProxyAdmin, hv, upd_ne _ _ hh.notifierNotCtm]
  have hrv : rowsApplied B v (toRows m.proxyUpgrades) := by
    intro r hrr; simpa [getProxyImplementation, hv] using hr r hrr
  exact ⟨v, leg_of_reads_unchanged hp hh.preNotifier_eq (hh.holders_isSome E.H) heng rfl rfl rfl
    hc hnr hrv, by simp [hv], rfl⟩

/-! ## (e) -/

theorem ContextBindingFields : Properties.ContextBindingFields := by
  intro E B tr m
  exact ⟨rfl, rfl, rfl, fun hp => hp.2.1.symm⟩

theorem ContextNotFromBindings : Properties.ContextNotFromBindings := by
  refine ⟨fun B tr m => ⟨rfl, rfl⟩, ?_⟩
  intro E B ⟨a, b, hab, ha, hb⟩
  let slots : List Row := List.replicate (E.invLen B.domain) ⟨0, 0⟩
  let ma : Manifest := ⟨B.domain, slots, a⟩
  let mb : Manifest := ⟨B.domain, slots, b⟩
  have hpa : ∀ tr, E.hasCode tr = true → Prechecks E B tr ma :=
    fun tr htr => ⟨htr, rfl, ha, List.length_replicate⟩
  have hpb : Prechecks E B a mb := ⟨ha, rfl, hb, List.length_replicate⟩
  have hdiff1 : buildContext B a ma ≠ buildContext B b ma := by
    intro h; exact hab (congrArg Context.transition h)
  have hdiff2 : buildContext B a ma ≠ buildContext B a mb := by
    intro h; exact hab (congrArg Context.proxyUpgradeEngine h)
  refine ⟨⟨a, b, ma, hpa a ha, hpa b hb, hdiff1⟩, ⟨a, ma, mb, hpa a ha, hpb, hdiff2⟩, ?_⟩
  rintro ⟨c, hc⟩
  exact hdiff1 ((hc a ma (hpa a ha)).trans (hc b ma (hpa b hb)).symm)

/-! ## Witnesses

One CTM executor: executor `1`, its `ProxyAdmin` `2`, the CTM proxy `3` (implementation `12`,
`ChainTypeManager.admin = 9`), the ServerNotifier proxy `4` (implementation `13`, no
`admin()`), one further proxy `5` under the same `ProxyAdmin`, and a transition `21` whose
engine is `20` and whose two-slot inventory upgrades proxy `5` to `11`. -/

namespace Witness

/-- Executor `1`, `ProxyAdmin` `2`, CTM domain, CTM proxy `3`. -/
def B : Bindings := ⟨1, 2, .ctm, 3⟩

/-- Slot 0 upgrades proxy `5` to `11`; slot 1 is inert. Engine `20`. -/
def m : Manifest := ⟨.ctm, [⟨5, 11⟩, ⟨0, 0⟩], 20⟩

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

/-- `w` with proxy `5` still at its old implementation `10`. -/
def wOld : World := { w with proxy := upd w.proxy 5 ⟨2, 10⟩ }

/-- A rows prefix: it points proxy `5` at `11`. -/
def pre : Engine := fun _ _ _ v => some { v with proxy := upd v.proxy 5 ⟨2, 11⟩ }

/-- `wOld` after `pre`. -/
def wOldApplied : World := { wOld with proxy := upd wOld.proxy 5 ⟨2, 11⟩ }

lemma prechecks : Prechecks E B 21 m := by decide

lemma holds : ExecutorHoldsCtm B w :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide, by decide, Or.inr (by decide)⟩

lemma holds_getter : ExecutorHoldsCtm B wGetter :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide, by decide, Or.inr (by decide)⟩

lemma holds_old : ExecutorHoldsCtm B wOld :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide, by decide, Or.inr (by decide)⟩

lemma move_ctm :
    moveProxyAdmin B.ctm 7 B.self (buildContext B 21 m) m.proxyUpgrades w = some wMovedCtm :=
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

lemma frame : HolderFrame B wOld.serverNotifier wOld wOldApplied :=
  ⟨rfl, rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Witness

open Witness in
theorem MovedCtmProxyAdminCaughtNotVacuous : Properties.MovedCtmProxyAdminCaughtNotVacuous := by
  have hnc : ¬ HolderPairCollides B E.H w wMovedCtm w.serverNotifier := by
    have hc : ctmWords B w = some [1, 1, 0, 2] := by decide
    have hc' : ctmWords B wMovedCtm = some [1, 1, 0, 9] := by decide
    have ho : notifierWords B E.H w w.serverNotifier = some [4, 1, 0, 2] := by decide
    have ho' : notifierWords B E.H wMovedCtm w.serverNotifier = some [11, 1, 0, 2] := by decide
    rintro (⟨e, e', he, he', -, hH⟩ | ⟨-, o, o', hw, hw', -, hH⟩)
    · rw [hc] at he; rw [hc'] at he'; cases he; cases he'
      exact absurd hH (by decide)
    · rw [ho] at hw; rw [ho'] at hw'; cases hw; cases hw'
      exact absurd hH (by decide)
  refine ⟨E, B, 21, m, w, wMovedCtm, 7, prechecks, holds, by decide, by decide, by decide,
    move_ctm, by decide, by decide, ?_, hnc⟩
  rcases MovedCtmProxyAdminCaught E B 21 m (moveProxyAdmin B.ctm 7) w wMovedCtm (by decide)
    (by decide) move_ctm (by decide) (by decide) with h | h
  · exact h
  · exact absurd h hnc

open Witness in
theorem MovedCtmCollisionDisjunctLoadBearing :
    Properties.MovedCtmCollisionDisjunctLoadBearing := by
  refine ⟨EConst, B, 21, m, w, wMovedCtm, 7, fun _ _ => rfl, prechecks, holds, by decide,
    by decide, move_ctm, by decide, by decide, ?_⟩
  exact leg_of_holders_eq (n := 4) (h := 0) prechecks (by decide) (by decide) move_ctm rfl rfl
    (by decide) (by decide)

open Witness in
theorem NotifierProxyAdminMoveRevertsSatisfiable :
    Properties.NotifierProxyAdminMoveRevertsSatisfiable :=
  ⟨E, B, 21, m, w, wMovedNotifier, 7, prechecks, holds, by decide, by decide, move_notifier,
    by decide, by decide⟩

open Witness in
theorem NotifierAdminGetterLoadBearing : Properties.NotifierAdminGetterLoadBearing := by
  refine ⟨E, B, 21, m, wGetter, wGetterMoved, 7, prechecks, holds_getter, by decide, by decide,
    by decide, by decide, fun H => ?_⟩
  exact leg_of_reads_unchanged (E := { E with H := H }) prechecks holds_getter.preNotifier_eq
    (holds_getter.holders_isSome H) move_getter rfl rfl rfl (by decide) (by decide) (by decide)

open Witness in
theorem MovedCtmPassesHolderCheckSatisfiable :
    Properties.MovedCtmPassesHolderCheckSatisfiable :=
  ⟨E, B, 21, m, pre, wOld, wOldApplied, 7, prechecks, holds_old, by decide, by decide, rfl,
    frame, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

open Witness in
theorem CtmAdminPremiseLoadBearing : Properties.CtmAdminPremiseLoadBearing := by
  obtain ⟨w₂, hleg, hslot, -, -, hc, ho, -⟩ :=
    MovedCtmPassesHolderCheck E B 21 m pre wOld wOldApplied 7 prechecks holds_old rfl frame
      (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨-, -, -, -, -, heng, -⟩ := leg_eq_some hleg
  refine ⟨E, B, 21, m, pre.andThen (aliasCtmProxyAdmin 7), wOld, w₂, prechecks, holds_old,
    by decide, by decide, heng, ?_, hleg, not_collides_of_words_eq hc ho⟩
  rw [hslot]; decide

open Witness in
theorem CtmAdminRoleOutsideHashSatisfiable : Properties.CtmAdminRoleOutsideHashSatisfiable :=
  ⟨E, B, 21, m, w, prechecks, holds, by decide, by decide, by decide⟩

end Contracts.DomainHoldersV35
