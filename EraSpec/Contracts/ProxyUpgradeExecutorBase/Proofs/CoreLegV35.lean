import EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.CoreLegV35
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsCurrent

/-!
# Proofs: the Core-domain leg at `b17415d20`

`applyL1Upgrade_eq_some` unfolds the leg into its checks; the zero-CTM branch of
`_domainHolders` turns the holder comparison into one on `keccakOwner` of the `ProxyAdmin`'s
owner. The row results read `requireRowsApplied` through `getProxyImplementation`.

For the default engine, two facts carry everything: its run changes neither the executor's
owners nor the `ProxyAdmin`'s owner (`applyRowsW_frame`), and it ends with its own
`requireRowsApplied`, so the executor's post-checks pass on its result
(`DefaultCoreLegIsTheEngineRun`). A replay skips every row because every row reads its `implNew`
(`applyLoopW_skip`). `applyRowsW_spec` relates the world-level loop to `RowsCurrent.ApplyRows` row
by row, under the premises that the `ProxyAdmin` administers each row's proxy and that no
reinitializer writes an admin slot; the loop then changes nothing but the implementation mapping,
so the first premise survives every step. The countermodels and witnesses are computations.
-/

namespace Contracts.ProxyUpgradeExecutorV35.CoreLeg

open Contracts.ProxyUpgradeCurrent (Address Row Impl upd toRows Domain ValidRows Config ApplyRows
  ApplyRow ApplyLoop RowCode RowsApplied ReinitFrames swap)

/-! ## Unfolding the leg -/

private lemma toRowsChecked_eq_some {slots : List Row} {n : Nat} {rows : List Row} :
    toRowsChecked slots n = some rows ↔ slots.length = n ∧ toRows slots = rows := by
  unfold toRowsChecked
  by_cases h : slots.length = n
  · simp [h]
  · simp [h]

private lemma domainHolders_zero (X : Exec) (W : World) :
    domainHolders X 0 W = some (X.keccakOwner W.paOwner) := by
  simp [domainHolders]

private lemma postChecks_eq_some {X : Exec} {d : Domain} {ctm : Address} {slots : List Row}
    {h : UInt256} {W M W' : World} :
    postChecks X d ctm slots h W M = some W' ↔
      M = W' ∧ M.owner = W.owner ∧ M.pendingOwner = W.pendingOwner ∧
      domainHolders X ctm M = some h ∧
      slots.length = inventoryLength d ∧ RowsAppliedW X M (toRows slots) := by
  unfold postChecks
  by_cases h1 : M.owner = W.owner ∧ M.pendingOwner = W.pendingOwner
  · rw [ite_eq_left h1]
    by_cases h2 : domainHolders X ctm M = some h
    · rw [ite_eq_left h2]
      unfold toRowsChecked
      by_cases h3 : slots.length = inventoryLength d
      · rw [ite_eq_left h3]
        by_cases h4 : RowsAppliedW X M (toRows slots)
        · simp [h4, h1, h2, h3]
        · simp [h4]
      · simp [h3]
    · rw [ite_eq_right h2]; simp [h2]
  · rw [ite_eq_right h1]
    simp only [reduceCtorEq, false_iff]
    rintro ⟨-, ho, hp, -⟩
    exact h1 ⟨ho, hp⟩

private lemma applyL1Upgrade_eq_some {X : Exec} {E : Engines} {caller : Address}
    {T : TransitionObj} {W W' : World} :
    applyL1Upgrade X E caller T W = some W' ↔
      (caller = W.owner ∧ X.hasCode T.addr = true ∧ T.manifest.domain = .core ∧
        X.hasCode T.manifest.engine = true ∧
        E T.manifest.engine (coreContext X T) T.manifest.proxyUpgrades W = some W' ∧
        W'.owner = W.owner ∧ W'.pendingOwner = W.pendingOwner ∧
        X.keccakOwner W'.paOwner = X.keccakOwner W.paOwner ∧
        T.manifest.proxyUpgrades.length = L1_ECOSYSTEM_CONTRACT_COUNT ∧
        RowsAppliedW X W' (toRows T.manifest.proxyUpgrades)) := by
  unfold applyL1Upgrade
  by_cases hc : caller = W.owner
  · rw [ite_eq_left hc]
    unfold applyProxyUpgradeTransition
    by_cases hpre : X.hasCode T.addr = true ∧ T.manifest.domain = .core ∧
        X.hasCode T.manifest.engine = true ∧ ((0 : Address) = 0 ∨ X.ctmCheck 0 W = true)
    · rw [ite_eq_left hpre, domainHolders_zero, Option.bind_some, Option.bind_eq_some_iff]
      constructor
      · rintro ⟨M, hE, hP⟩
        obtain ⟨rfl, h1, h2, h3, h4, h5⟩ := postChecks_eq_some.mp hP
        rw [domainHolders_zero] at h3
        exact ⟨hc, hpre.1, hpre.2.1, hpre.2.2.1, hE, h1, h2, Option.some.inj h3, h4, h5⟩
      · rintro ⟨-, -, -, -, hE, h1, h2, h3, h4, h5⟩
        refine ⟨W', hE, postChecks_eq_some.mpr ⟨rfl, h1, h2, ?_, h4, h5⟩⟩
        rw [domainHolders_zero, h3]
    · rw [ite_eq_right hpre]
      simp only [reduceCtorEq, false_iff]
      rintro ⟨-, h1, h2, h3, -⟩
      exact hpre ⟨h1, h2, h3, Or.inl rfl⟩
  · rw [ite_eq_right hc]
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h', -⟩
    exact hc h'

/-! ## The row reads -/

private lemma getProxyImplementation_admin {X : Exec} {W : World} {p : Address}
    (h : W.admin p = X.pa) : getProxyImplementation X W p = some (W.impl p) := by
  simp [getProxyImplementation, h]

private lemma getProxyImplementation_moved {X : Exec} {W : World} {p : Address}
    (h : W.admin p ≠ X.pa) : getProxyImplementation X W p = X.implAnswer (W.impl p) p W := by
  simp [getProxyImplementation, h]

/-! ## The default engine: frame, final check, replay -/

private lemma swapW_frame (X : Exec) (r : Row) (W : World) :
    (swapW X r W).owner = W.owner ∧ (swapW X r W).pendingOwner = W.pendingOwner ∧
      (swapW X r W).paOwner = W.paOwner := by
  unfold swapW
  by_cases h : r.callInitializeUpgrade = true
  · rw [ite_eq_left h]; exact ⟨rfl, rfl, rfl⟩
  · rw [ite_eq_right h]; exact ⟨rfl, rfl, rfl⟩

private lemma applyRowW_frame {X : Exec} {W W' : World} {r : Row}
    (h : applyRowW X W r = some W') :
    W'.owner = W.owner ∧ W'.pendingOwner = W.pendingOwner ∧ W'.paOwner = W.paOwner := by
  unfold applyRowW at h
  cases hg : getProxyImplementation X W r.proxy with
  | none => rw [hg] at h; cases h
  | some live =>
    rw [hg] at h
    simp only at h
    by_cases h1 : live = r.implNew
    · rw [ite_eq_left h1] at h; cases h; exact ⟨rfl, rfl, rfl⟩
    · rw [ite_eq_right h1] at h
      by_cases h2 : live ≠ r.expectedOldImpl
      · rw [ite_eq_left h2] at h; cases h
      · rw [ite_eq_right h2] at h
        by_cases h3 : W.paOwner = X.self ∧ W.admin r.proxy = X.pa
        · rw [ite_eq_left h3] at h; cases h; exact swapW_frame X r W
        · rw [ite_eq_right h3] at h; cases h

private lemma applyLoopW_frame {X : Exec} : ∀ {rows : List Row} {W W' : World},
    applyLoopW X W rows = some W' →
      W'.owner = W.owner ∧ W'.pendingOwner = W.pendingOwner ∧ W'.paOwner = W.paOwner
  | [], W, W', h => by
    simp only [applyLoopW, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl⟩
  | r :: rs, W, W', h => by
    simp only [applyLoopW, Option.bind_eq_some_iff] at h
    obtain ⟨W1, h1, h2⟩ := h
    obtain ⟨a1, b1, c1⟩ := applyRowW_frame h1
    obtain ⟨a2, b2, c2⟩ := applyLoopW_frame h2
    exact ⟨a2.trans a1, b2.trans b1, c2.trans c1⟩

private lemma applyRowsW_frame {X : Exec} {rows : List Row} {W W' : World}
    (h : applyRowsW X rows W = some W') :
    W'.owner = W.owner ∧ W'.pendingOwner = W.pendingOwner ∧ W'.paOwner = W.paOwner ∧
      RowsAppliedW X W' rows ∧ RowCodeW X rows := by
  unfold applyRowsW at h
  by_cases hc : RowCodeW X rows
  · rw [ite_eq_left hc, Option.bind_eq_some_iff] at h
    obtain ⟨M, hM, hP⟩ := h
    by_cases ha : RowsAppliedW X M rows
    · rw [ite_eq_left ha] at hP
      cases hP
      obtain ⟨a, b, c⟩ := applyLoopW_frame hM
      exact ⟨a, b, c, ha, hc⟩
    · rw [ite_eq_right ha] at hP; cases hP
  · rw [ite_eq_right hc] at h; cases h

private lemma applyLoopW_skip {X : Exec} {W : World} : ∀ {rows : List Row},
    RowsAppliedW X W rows → applyLoopW X W rows = some W
  | [], _ => rfl
  | r :: rs, h => by
    have hr : applyRowW X W r = some W := by
      unfold applyRowW
      rw [h r (by simp)]
      simp
    simp only [applyLoopW, hr, Option.bind_some]
    exact applyLoopW_skip (fun q hq => h q (by simp [hq]))

private lemma applyRowsW_replay {X : Exec} {W : World} {rows : List Row}
    (hc : RowCodeW X rows) (h : RowsAppliedW X W rows) : applyRowsW X rows W = some W := by
  unfold applyRowsW
  rw [ite_eq_left hc, applyLoopW_skip h, Option.bind_some, ite_eq_left h]

private lemma defaultEngine_eq_some {X : Exec} {ctx : Context} {inv : List Row} {W W' : World} :
    defaultEngine X ctx inv W = some W' ↔
      W.paOwner = X.self ∧ inv.length = inventoryLength ctx.domain ∧
      applyRowsW X (toRows inv) W = some W' := by
  unfold defaultEngine defaultEngineWith
  by_cases ho : W.paOwner ≠ X.self
  · rw [ite_eq_left ho]
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h, -⟩
    exact ho h
  · rw [ite_eq_right ho]
    have ho' : W.paOwner = X.self := not_not.mp ho
    simp only [noHook, Option.bind_some, Option.bind_eq_some_iff, ite_true]
    constructor
    · rintro ⟨rows, hr, W2, hA, hW⟩
      obtain ⟨hl, rfl⟩ := toRowsChecked_eq_some.mp hr
      cases hW
      exact ⟨ho', hl, hA⟩
    · rintro ⟨-, hl, hA⟩
      exact ⟨toRows inv, toRowsChecked_eq_some.mpr ⟨hl, rfl⟩, W', hA, rfl⟩

private lemma releaseEngine_of_default {X : Exec} {ops : List EngineOp} {ctx : Context}
    {inv : List Row} {W W' W'' : World} (h1 : defaultEngine X ctx inv W = some W')
    (h2 : runOps X ops W' = some W'') : releaseEngine X ops ctx inv W = some W'' := by
  obtain ⟨ho, hl, hA⟩ := defaultEngine_eq_some.mp h1
  unfold releaseEngine defaultEngineWith
  rw [ite_eq_right (not_not.mpr ho)]
  simp only [noHook, Option.bind_some]
  rw [toRowsChecked_eq_some.mpr ⟨hl, rfl⟩, Option.bind_some, hA, Option.bind_some, h2,
    Option.bind_some]
  rfl

/-! ## `RowsCurrent` relations, unfolded -/

private lemma applyRow_iff {C : Config} {I J : Impl} {r : Row} :
    ApplyRow C I r J ↔
      (I r.proxy = r.implNew ∧ J = I) ∨
      (C.adminOwner = C.self ∧ I r.proxy ≠ r.implNew ∧ I r.proxy = r.expectedOldImpl ∧
        J = swap C r I) := by
  constructor
  · intro h
    cases h with
    | alreadyAtTarget h1 => exact Or.inl ⟨h1, rfl⟩
    | upgrade h1 h2 h3 => exact Or.inr ⟨h1, h2, h3, rfl⟩
  · rintro (⟨h1, rfl⟩ | ⟨h1, h2, h3, rfl⟩)
    · exact ApplyRow.alreadyAtTarget h1
    · exact ApplyRow.upgrade h1 h2 h3

private lemma applyLoop_nil_iff {C : Config} {I K : Impl} : ApplyLoop C I [] K ↔ K = I := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact ApplyLoop.nil

private lemma applyLoop_cons_iff {C : Config} {I K : Impl} {r : Row} {rs : List Row} :
    ApplyLoop C I (r :: rs) K ↔ ∃ J, ApplyRow C I r J ∧ ApplyLoop C J rs K := by
  constructor
  · intro h
    cases h with
    | cons h1 h2 => exact ⟨_, h1, h2⟩
  · rintro ⟨J, h1, h2⟩
    exact ApplyLoop.cons h1 h2

/-! ## The default engine is `RowsCurrent.ApplyRows` -/

private lemma swapW_eq {X : Exec} (hK : ReinitKeepsAdmins X) (r : Row) (W : World) :
    swapW X r W = { W with impl := swap (rowsConfig X W) r W.impl } := by
  unfold swapW swap
  by_cases h : r.callInitializeUpgrade = true
  · rw [ite_eq_left h, ite_eq_left h, hK]
    rfl
  · rw [ite_eq_right h, ite_eq_right h]

private lemma applyRowW_spec {X : Exec} {W W1 : World} {r : Row} (hK : ReinitKeepsAdmins X)
    (hadm : W.admin r.proxy = X.pa) :
    applyRowW X W r = some W1 ↔
      ApplyRow (rowsConfig X W) W.impl r W1.impl ∧ W1 = { W with impl := W1.impl } := by
  rw [applyRow_iff]
  unfold applyRowW
  rw [getProxyImplementation_admin hadm]
  simp only
  by_cases h1 : W.impl r.proxy = r.implNew
  · rw [ite_eq_left h1]
    constructor
    · intro h; cases h; exact ⟨Or.inl ⟨h1, rfl⟩, rfl⟩
    · rintro ⟨(⟨-, hJ⟩ | ⟨-, hne, -⟩), hW⟩
      · rw [hW, hJ]
      · exact absurd h1 hne
  · rw [ite_eq_right h1]
    by_cases h2 : W.impl r.proxy ≠ r.expectedOldImpl
    · rw [ite_eq_left h2]
      simp only [reduceCtorEq, false_iff]
      rintro ⟨(⟨h, -⟩ | ⟨-, -, h, -⟩), -⟩
      · exact h1 h
      · exact h2 h
    · rw [ite_eq_right h2]
      have h2' : W.impl r.proxy = r.expectedOldImpl := not_not.mp h2
      by_cases h3 : W.paOwner = X.self ∧ W.admin r.proxy = X.pa
      · rw [ite_eq_left h3, swapW_eq hK]
        constructor
        · intro h
          cases h
          exact ⟨Or.inr ⟨h3.1, h1, h2', rfl⟩, rfl⟩
        · rintro ⟨(⟨h, -⟩ | ⟨-, -, -, hJ⟩), hW⟩
          · exact absurd h h1
          · rw [hW, hJ]
      · rw [ite_eq_right h3]
        simp only [reduceCtorEq, false_iff]
        rintro ⟨(⟨h, -⟩ | ⟨ho, -, -, -⟩), -⟩
        · exact h1 h
        · exact h3 ⟨ho, hadm⟩

private lemma applyLoopW_spec {X : Exec} (hK : ReinitKeepsAdmins X) :
    ∀ (rows : List Row) (W W' : World), (∀ r ∈ rows, W.admin r.proxy = X.pa) →
      (applyLoopW X W rows = some W' ↔
        ApplyLoop (rowsConfig X W) W.impl rows W'.impl ∧ W' = { W with impl := W'.impl })
  | [], W, W' => by
    intro _
    rw [applyLoop_nil_iff]
    simp only [applyLoopW, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h, hW⟩
      rw [hW, h]
  | r :: rs, W, W' => by
    intro hadm
    rw [applyLoop_cons_iff]
    simp only [applyLoopW, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨W1, h1, h2⟩
      obtain ⟨hr, hW1⟩ := (applyRowW_spec hK (hadm r (by simp))).mp h1
      have hadm1 : ∀ q ∈ rs, W1.admin q.proxy = X.pa := by
        intro q hq; rw [hW1]; exact hadm q (by simp [hq])
      obtain ⟨hl, hW'⟩ := (applyLoopW_spec hK rs W1 W' hadm1).mp h2
      have hc : rowsConfig X W1 = rowsConfig X W := by rw [hW1]; rfl
      refine ⟨⟨W1.impl, hr, hc ▸ hl⟩, ?_⟩
      rw [hW', hW1]
    · rintro ⟨⟨J, hr, hl⟩, hW'⟩
      refine ⟨{ W with impl := J }, (applyRowW_spec hK (hadm r (by simp))).mpr ⟨hr, rfl⟩, ?_⟩
      exact (applyLoopW_spec hK rs { W with impl := J } W'
        (fun q hq => hadm q (by simp [hq]))).mpr ⟨hl, hW'⟩

private lemma rowsAppliedW_iff {X : Exec} {W : World} {rows : List Row}
    (hadm : ∀ r ∈ rows, W.admin r.proxy = X.pa) :
    RowsAppliedW X W rows ↔ RowsApplied W.impl rows := by
  constructor
  · intro h r hr
    have := h r hr
    rw [getProxyImplementation_admin (hadm r hr)] at this
    exact Option.some.inj this
  · intro h r hr
    rw [getProxyImplementation_admin (hadm r hr), h r hr]

private lemma applyRowsW_spec {X : Exec} {rows : List Row} {W W' : World}
    (hK : ReinitKeepsAdmins X) (hadm : ∀ r ∈ rows, W.admin r.proxy = X.pa) :
    applyRowsW X rows W = some W' ↔
      ApplyRows (rowsConfig X W) W.impl rows W'.impl ∧ W' = { W with impl := W'.impl } := by
  unfold applyRowsW
  by_cases hc : RowCodeW X rows
  · rw [ite_eq_left hc, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨M, hM, hP⟩
      by_cases ha : RowsAppliedW X M rows
      · rw [ite_eq_left ha] at hP
        have hMW : M = W' := Option.some.inj hP
        subst hMW
        obtain ⟨hl, hW⟩ := (applyLoopW_spec hK rows W M hadm).mp hM
        have hadm' : ∀ r ∈ rows, M.admin r.proxy = X.pa := by
          intro r hr; rw [hW]; exact hadm r hr
        exact ⟨⟨hc, hl, (rowsAppliedW_iff hadm').mp ha⟩, hW⟩
      · rw [ite_eq_right ha] at hP; cases hP
    · rintro ⟨⟨-, hl, hv⟩, hW⟩
      refine ⟨W', (applyLoopW_spec hK rows W W' hadm).mpr ⟨hl, hW⟩, ?_⟩
      have hadm' : ∀ r ∈ rows, W'.admin r.proxy = X.pa := by
        intro r hr; rw [hW]; exact hadm r hr
      rw [ite_eq_left ((rowsAppliedW_iff hadm').mpr hv)]
  · rw [ite_eq_right hc]
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h, -⟩
    exact hc h.code

/-! ## Certificates: (a) -/

theorem CoreLegExact : Properties.CoreLegExact := fun _ _ _ _ _ _ => applyL1Upgrade_eq_some

theorem CoreLegChecks : Properties.CoreLegChecks := by
  intro X E caller T W W' h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := applyL1Upgrade_eq_some.mp h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, h9, h10⟩
  by_cases hp : W'.paOwner = W.paOwner
  · exact Or.inl hp
  · exact Or.inr ⟨hp, h8⟩

theorem CoreLegIgnoresCTMBranch : Properties.CoreLegIgnoresCTMBranch := by
  intro X h c E caller T W
  apply Option.ext
  intro W'
  rw [applyL1Upgrade_eq_some, applyL1Upgrade_eq_some]
  exact Iff.rfl

theorem CorePAOwnerMoveCaught : Properties.CorePAOwnerMoveCaught := by
  intro X E caller T W M hE hk
  cases hl : applyL1Upgrade X E caller T W with
  | none => rfl
  | some W' =>
    obtain ⟨-, -, -, -, h5, -, -, h8, -⟩ := applyL1Upgrade_eq_some.mp hl
    rw [hE] at h5
    cases h5
    exact absurd h8 hk

/-! ## Certificates: what the checks read -/

theorem CorePostCheckScopeIsRows : Properties.CorePostCheckScopeIsRows := by
  intro X E E' caller T W M M' hE hE' ho hp hk hread
  have happ : RowsAppliedW X M' (toRows T.manifest.proxyUpgrades) ↔
      RowsAppliedW X M (toRows T.manifest.proxyUpgrades) :=
    ⟨fun h r hr => (hread r hr).symm.trans (h r hr), fun h r hr => (hread r hr).trans (h r hr)⟩
  rw [applyL1Upgrade_eq_some, applyL1Upgrade_eq_some]
  constructor
  · rintro ⟨h1, h2, h3, h4, -, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h3, h4, hE', ho.trans h6, hp.trans h7, hk.trans h8, h9, happ.mpr h10⟩
  · rintro ⟨h1, h2, h3, h4, -, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h3, h4, hE, ho.symm.trans h6, hp.symm.trans h7, hk.symm.trans h8, h9,
      happ.mp h10⟩

theorem CorePostCheckScopeAdministered : Properties.CorePostCheckScopeAdministered := by
  intro X E E' caller T W M M' hE hE' ho hp hpa hrows
  refine CorePostCheckScopeIsRows X E E' caller T W M M' hE hE' ho hp (by rw [hpa]) ?_
  intro r hr
  obtain ⟨hm, hm', hi⟩ := hrows r hr
  rw [getProxyImplementation_admin hm, getProxyImplementation_admin hm', hi]

theorem CoreUnnamedAdminMoveAlwaysPasses : Properties.CoreUnnamedAdminMoveAlwaysPasses := by
  intro X E E' caller T W W' p a hE hE' h hrows hp ha
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := applyL1Upgrade_eq_some.mp h
  rw [hE] at h5
  obtain ⟨hpa, -, hA⟩ := defaultEngine_eq_some.mp h5
  obtain ⟨-, -, hpa', -⟩ := applyRowsW_frame hA
  have hrun : runOps X [.changeProxyAdmin p a] W' =
      some { W' with admin := upd W'.admin p a } := by
    show (paChangeProxyAdmin X p a W').bind (runOps X []) = _
    unfold paChangeProxyAdmin
    rw [ite_eq_left ⟨hpa'.trans hpa, hp, ha⟩]
    rfl
  refine applyL1Upgrade_eq_some.mpr ⟨h1, h2, h3, h4, ?_, h6, h7, h8, h9, ?_⟩
  · rw [hE']; exact releaseEngine_of_default h5 hrun
  · intro r hr
    obtain ⟨hne, hadm⟩ := hrows r hr
    have hadm' : ({ W' with admin := upd W'.admin p a } : World).admin r.proxy = X.pa := by
      show upd W'.admin p a r.proxy = X.pa
      rw [Contracts.ProxyUpgradeCurrent.upd_ne _ _ hne]; exact hadm
    rw [getProxyImplementation_admin hadm']
    have := h10 r hr
    rw [getProxyImplementation_admin hadm] at this
    exact this

theorem CoreUnnamedImplMoveAlwaysPasses : Properties.CoreUnnamedImplMoveAlwaysPasses := by
  intro X E E' caller T W W' p x hE hE' h hrows hp hx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := applyL1Upgrade_eq_some.mp h
  rw [hE] at h5
  obtain ⟨hpa, -, hA⟩ := defaultEngine_eq_some.mp h5
  obtain ⟨-, -, hpa', -⟩ := applyRowsW_frame hA
  have hrun : runOps X [.upgrade p x] W' = some { W' with impl := upd W'.impl p x } := by
    show (paUpgrade X p x W').bind (runOps X []) = _
    unfold paUpgrade
    rw [ite_eq_left ⟨hpa'.trans hpa, hp, hx⟩]
    rfl
  refine applyL1Upgrade_eq_some.mpr ⟨h1, h2, h3, h4, ?_, h6, h7, h8, h9, ?_⟩
  · rw [hE']; exact releaseEngine_of_default h5 hrun
  · intro r hr
    obtain ⟨hne, hadm⟩ := hrows r hr
    have hadm' : ({ W' with impl := upd W'.impl p x } : World).admin r.proxy = X.pa := hadm
    rw [getProxyImplementation_admin hadm']
    have := h10 r hr
    rw [getProxyImplementation_admin hadm] at this
    show some (upd W'.impl p x r.proxy) = some r.implNew
    rw [Contracts.ProxyUpgradeCurrent.upd_ne _ _ hne]
    exact this

/-! ## Certificates: (b) -/

theorem CoreRowAdministeredIsAtImplNew : Properties.CoreRowAdministeredIsAtImplNew := by
  intro X E caller T W W' h r hr ha
  obtain ⟨-, -, -, -, -, -, -, -, -, h10⟩ := applyL1Upgrade_eq_some.mp h
  have := h10 r hr
  rw [getProxyImplementation_admin ha] at this
  exact Option.some.inj this

theorem CoreRowAdminMoveCaught : Properties.CoreRowAdminMoveCaught := by
  intro X E caller T W W' h r hr ha
  obtain ⟨-, -, -, -, -, -, -, -, -, h10⟩ := applyL1Upgrade_eq_some.mp h
  have := h10 r hr
  rwa [getProxyImplementation_moved ha] at this

theorem CoreRowAdminMoveReverts : Properties.CoreRowAdminMoveReverts := by
  intro X E caller T W M hE r hr ha hans
  cases hl : applyL1Upgrade X E caller T W with
  | none => rfl
  | some W' =>
    obtain ⟨-, -, -, -, h5, -⟩ := applyL1Upgrade_eq_some.mp hl
    rw [hE] at h5
    cases h5
    exact absurd (CoreRowAdminMoveCaught X E caller T W M hl r hr ha) hans

/-! ## Certificates: (c) -/

theorem DefaultCoreLegIsTheEngineRun : Properties.DefaultCoreLegIsTheEngineRun := by
  intro X E caller T W W' hE
  rw [applyL1Upgrade_eq_some, hE]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, -⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨-, hl, hA⟩ := defaultEngine_eq_some.mp h5
    obtain ⟨ho, hp, hpa, hr, -⟩ := applyRowsW_frame hA
    exact ⟨h1, h2, h3, h4, h5, ho, hp, by rw [hpa], hl, hr⟩

theorem DefaultCoreLegReplayIsNoop : Properties.DefaultCoreLegReplayIsNoop := by
  intro X E caller T W W' hE h
  obtain ⟨h1, h2, h3, h4, h5⟩ := (DefaultCoreLegIsTheEngineRun X E caller T W W' hE).mp h
  obtain ⟨hpa, hl, hA⟩ := defaultEngine_eq_some.mp h5
  obtain ⟨ho, -, hpa', hr, hc⟩ := applyRowsW_frame hA
  refine (DefaultCoreLegIsTheEngineRun X E caller T W' W' hE).mpr
    ⟨h1.trans ho.symm, h2, h3, h4, ?_⟩
  exact defaultEngine_eq_some.mpr ⟨hpa'.trans hpa, hl, applyRowsW_replay hc hr⟩

theorem DefaultCoreLegNeedsOwnedAdmin : Properties.DefaultCoreLegNeedsOwnedAdmin := by
  intro X E caller T W hE ho
  cases hl : applyL1Upgrade X E caller T W with
  | none => rfl
  | some W' =>
    obtain ⟨-, -, -, -, h5, -⟩ := applyL1Upgrade_eq_some.mp hl
    rw [hE] at h5
    exact absurd (defaultEngine_eq_some.mp h5).1 ho

theorem DefaultCoreLegIsApplyRows : Properties.DefaultCoreLegIsApplyRows := by
  intro X E caller T W W' hE hadm hK
  rw [DefaultCoreLegIsTheEngineRun X E caller T W W' hE, defaultEngine_eq_some,
    applyRowsW_spec hK hadm]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, hl, hA, hW⟩
    exact ⟨h1, h2, h3, h4, h5, hl, hA, hW⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem DefaultCoreLegOnlyNamedEdges : Properties.DefaultCoreLegOnlyNamedEdges := by
  intro X E caller T W W' hE hadm hK hd hf h
  obtain ⟨-, -, -, -, -, -, hA, hW⟩ :=
    (DefaultCoreLegIsApplyRows X E caller T W W' hE hadm hK).mp h
  refine ⟨by rw [hW], by rw [hW], by rw [hW], by rw [hW], ?_⟩
  exact Contracts.ProxyUpgradeCurrent.OnlyNamedEdgesAcrossCall _ _ _ _ hd hf hA

/-! ## Witness facts -/

private lemma toRows_coreInventory : toRows coreInventory = [coreRow] := by decide

private lemma genuine_coreTransition : Genuine coreTransition := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · show toRows coreInventory ≠ []
    rw [toRows_coreInventory]; simp
  · show ValidRows (toRows coreInventory)
    rw [toRows_coreInventory]
    exact ⟨by simp [coreRow], by simp [coreRow], by simp⟩

private lemma toRows_coreInventoryInit : toRows coreInventoryInit = [coreRowInit] := by decide

private lemma genuine_coreTransitionInit : Genuine coreTransitionInit := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · show toRows coreInventoryInit ≠ []
    rw [toRows_coreInventoryInit]; simp
  · show ValidRows (toRows coreInventoryInit)
    rw [toRows_coreInventoryInit]
    exact ⟨by simp [coreRowInit], by simp [coreRowInit], by simp⟩

/-! ## Certificates: the checks are load-bearing -/

theorem CorePAOwnerMoveUnderCollisionPasses : Properties.CorePAOwnerMoveUnderCollisionPasses :=
  ⟨{ coreAfter with paOwner := 9 }, genuine_coreTransition, rfl, by decide, rfl, rfl, by decide,
    rfl⟩

theorem CorePAOwnerCheckIsLoadBearing : Properties.CorePAOwnerCheckIsLoadBearing := by
  refine ⟨{ coreAfter with paOwner := 9 }, genuine_coreTransition, rfl, rfl, rfl, ?_, by decide,
    by decide, rfl⟩
  show RowsAppliedW coreExec _ (toRows coreInventory)
  rw [toRows_coreInventory]; decide

theorem CoreExecutorOwnerCheckIsLoadBearing : Properties.CoreExecutorOwnerCheckIsLoadBearing := by
  refine ⟨{ coreAfter with owner := 9 }, genuine_coreTransition, rfl, by decide, rfl, rfl, ?_, rfl⟩
  show RowsAppliedW coreExec _ (toRows coreInventory)
  rw [toRows_coreInventory]; decide

theorem CorePendingOwnerCheckIsLoadBearing :
    Properties.CorePendingOwnerCheckIsLoadBearing := by
  refine ⟨{ coreAfter with pendingOwner := 9 }, genuine_coreTransition, rfl, rfl, by decide, rfl,
    ?_, rfl⟩
  show RowsAppliedW coreExec _ (toRows coreInventory)
  rw [toRows_coreInventory]; decide

theorem CoreRowsCheckIsLoadBearing : Properties.CoreRowsCheckIsLoadBearing := by
  refine ⟨genuine_coreTransition, rfl, ?_, rfl⟩
  show ¬ RowsAppliedW coreExec coreWorld (toRows coreInventory)
  rw [toRows_coreInventory]; decide

theorem CoreRowsCheckCatchesAfterHook : Properties.CoreRowsCheckCatchesAfterHook := by
  refine ⟨{ coreWorld with impl := upd coreAfter.impl 5 10 }, genuine_coreTransition, rfl, rfl,
    rfl, rfl, rfl, by decide, ?_, rfl⟩
  show ¬ RowsAppliedW coreExec _ (toRows coreInventory)
  rw [toRows_coreInventory]; decide

/-! ## Certificates: what the checks read, on concrete runs -/

theorem CorePostCheckScopeWitness : Properties.CorePostCheckScopeWitness := by
  refine ⟨coreAfter, { coreAfter with admin := upd coreAfter.admin 6 9 }, genuine_coreTransition,
    rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · show ∀ r ∈ toRows coreInventory, _
    rw [toRows_coreInventory]; decide
  · show ∀ r ∈ toRows coreInventory, _
    rw [toRows_coreInventory]; decide
  · intro h
    have := congrArg (fun w : World => w.admin 6) h
    revert this; decide

theorem CoreEngineMovesUnnamedSingletonAdmin :
    Properties.CoreEngineMovesUnnamedSingletonAdmin := by
  refine ⟨coreAfter, genuine_coreTransition, rfl, rfl, rfl, ?_, rfl, by decide, fun _ => rfl, rfl,
    by decide, by decide⟩
  show ∀ r ∈ toRows coreInventory, _
  rw [toRows_coreInventory]; decide

theorem CoreEngineMovesUnnamedSingletonImpl : Properties.CoreEngineMovesUnnamedSingletonImpl := by
  refine ⟨coreAfter, genuine_coreTransition, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, by decide⟩
  show ∀ r ∈ toRows coreInventory, _
  rw [toRows_coreInventory]; decide

/-! ## Certificates: (b), concrete runs -/

theorem CoreRowAdminMoveRevertsWitness : Properties.CoreRowAdminMoveRevertsWitness := by
  refine ⟨{ coreAfter with admin := upd coreAfter.admin 5 9 }, genuine_coreTransition, rfl, ?_,
    rfl, by decide, by decide, by decide, rfl, rfl, rfl, rfl⟩
  show coreRow ∈ toRows coreInventory
  rw [toRows_coreInventory]; simp

theorem CoreRowAdminMoveUncaughtWhenAnswerMatches :
    Properties.CoreRowAdminMoveUncaughtWhenAnswerMatches := by
  refine ⟨{ coreAfter with impl := upd coreAfter.impl 5 12, admin := upd coreAfter.admin 5 9 },
    genuine_coreTransition, rfl, ?_, rfl, by decide, by decide, by decide⟩
  show coreRow ∈ toRows coreInventory
  rw [toRows_coreInventory]; simp

/-! ## Certificates: (c) countermodels and (d) witness -/

theorem UnownedReplayRevertsAtV35 : Properties.UnownedReplayRevertsAtV35 := by
  refine ⟨{ coreAfter with paOwner := 7 }, genuine_coreTransition, rfl, by decide, ?_, ?_, rfl⟩
  · intro r _; rfl
  · show ApplyRows _ _ (toRows coreInventory) _
    rw [toRows_coreInventory]
    refine ⟨fun r _ => rfl, ApplyLoop.cons (ApplyRow.alreadyAtTarget ?_) ApplyLoop.nil, ?_⟩
    · decide
    · intro r hr
      rw [List.mem_singleton] at hr
      subst hr
      decide

theorem DefaultLegNeedsAdministeredRows : Properties.DefaultLegNeedsAdministeredRows := by
  refine ⟨genuine_coreTransition, rfl, fun _ _ => rfl, rfl, by decide, by decide, ?_⟩
  intro h
  have := h.verified coreRow
    (by show coreRow ∈ toRows coreInventory; rw [toRows_coreInventory]; simp)
  revert this; decide

theorem DefaultLegReinitMovesRowAdmin : Properties.DefaultLegReinitMovesRowAdmin := by
  refine ⟨{ coreAfter with admin := upd coreWorld.admin 5 9 }, genuine_coreTransitionInit, rfl, ?_,
    ?_, rfl, by decide, by decide, by decide, ?_, rfl, rfl⟩
  · intro r _; rfl
  · intro h
    have := congrFun (h coreRowInit coreWorld) 5
    revert this; decide
  · intro h
    have := congrArg (fun w : World => w.admin 5) h
    revert this; decide

theorem CoreLegWitness : Properties.CoreLegWitness := by
  refine ⟨{ coreWorld with impl := upd coreAfter.impl 5 11 }, genuine_coreTransitionInit, rfl, rfl,
    rfl, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, rfl, ?_, rfl, rfl, by decide, by decide,
    by decide, by decide, rfl⟩
  · show (toRows coreInventoryInit).Pairwise (fun a b => a.proxy ≠ b.proxy)
    rw [toRows_coreInventoryInit]; simp
  · intro r I q hq
    exact Contracts.ProxyUpgradeCurrent.upd_ne I r.implNew hq
  · show coreRowInit ∈ toRows coreInventoryInit
    rw [toRows_coreInventoryInit]; simp
  · intro h
    have := congrFun h 5
    revert this; decide

end Contracts.ProxyUpgradeExecutorV35.CoreLeg
