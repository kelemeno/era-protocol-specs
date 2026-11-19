import EraSpec.Contracts.ProxyUpgradeExecutorBase.History.Properties.DomainHoldersD9
import EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.DomainHoldersV35

/-!
# History proofs: the `d9f6789` leg compared with the `b17415d20` one

**The record of an older commit, not a claim about `b17415d20`.** The `d9f6789` leg has its own
`leg_eq_some`, `leg_of_holders_eq` and `leg_of_reads_unchanged` in `D9`;
`AliasingPassesAtD9CaughtAtB17` computes the three aliasing calls (`aliasCtmProxyAdmin_eq`). The
witnesses reuse `Contracts.DomainHoldersV35.DomainHoldersWitness`.
-/

namespace Contracts.DomainHoldersV35.History

open Contracts.DomainHoldersV35

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

open DomainHoldersWitness in
/-- The witness prefix leaves the `d9f6789` holder reads alone. -/
lemma witnessFrame : D9.HolderFrame B wOld.serverNotifier wOld wOldApplied :=
  ⟨rfl, rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

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
theorem AliasingPassesAtD9CaughtAtB17Satisfiable :
    Properties.AliasingPassesAtD9CaughtAtB17Satisfiable :=
  ⟨E, B, 21, m, pre, wOld, wOldApplied, 7, prechecks, holds_old, ok_old, by decide, rfl, witnessFrame,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Contracts.DomainHoldersV35.History
