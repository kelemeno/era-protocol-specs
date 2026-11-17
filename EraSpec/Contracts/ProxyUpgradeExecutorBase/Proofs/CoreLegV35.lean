import EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.CoreLegV35
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsCurrent

/-!
# Proofs: the Core-domain leg at `d9f678900`

`applyL1Upgrade_eq_some` unfolds the leg into its checks; the zero-CTM branch of
`_domainHolders` turns the holder comparison into one on `keccakOwner` of the `ProxyAdmin`'s
owner. The row results read `requireRowsApplied` through `getProxyImplementation`. For the
default engine, `applyRowsW_spec` relates the world-level loop to `RowsCurrent.ApplyRows` row by
row, under the premises that the `ProxyAdmin` administers each row's proxy and that no
reinitializer writes an admin slot; the loop then changes nothing but the implementation mapping,
so the first premise survives every step. The countermodels are computations.
-/

namespace Contracts.ProxyUpgradeExecutorV35.CoreLeg

open Contracts.ProxyUpgradeCurrent (Address Row Impl upd toRows Domain ValidRows Config ApplyRows
  ApplyRow ApplyLoop RowCode RowsApplied ReinitFrames swap)

/-! ## Unfolding the leg -/

lemma toRowsChecked_eq_some {slots : List Row} {n : Nat} {rows : List Row} :
    toRowsChecked slots n = some rows ↔ slots.length = n ∧ toRows slots = rows := by
  unfold toRowsChecked
  by_cases h : slots.length = n
  · simp [h]
  · simp [h]

lemma postChecks_eq_some {X : Exec} {d : Domain} {ctm sn : Address} {slots : List Row}
    {W M W' : World} :
    postChecks X d ctm sn slots W M = some W' ↔
      M = W' ∧ M.owner = W.owner ∧ M.pendingOwner = W.pendingOwner ∧
      domainHolders X ctm sn M = domainHolders X ctm sn W ∧
      slots.length = inventoryLength d ∧ RowsAppliedW X M (toRows slots) := by
  unfold postChecks
  by_cases h1 : M.owner = W.owner ∧ M.pendingOwner = W.pendingOwner
  · rw [ite_eq_left h1]
    by_cases h2 : domainHolders X ctm sn M = domainHolders X ctm sn W
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

lemma applyProxyUpgradeTransition_eq_some {X : Exec} {E : Engines} {T : TransitionObj}
    {d : Domain} {ctm : Address} {W W' : World} :
    applyProxyUpgradeTransition X E T d ctm W = some W' ↔
      (X.hasCode T.addr = true ∧ T.manifest.domain = d ∧ X.hasCode T.manifest.engine = true) ∧
      E T.manifest.engine (context X T d ctm) T.manifest.proxyUpgrades W = some W' ∧
      W'.owner = W.owner ∧ W'.pendingOwner = W.pendingOwner ∧
      domainHolders X ctm (serverNotifier X ctm W) W' =
        domainHolders X ctm (serverNotifier X ctm W) W ∧
      T.manifest.proxyUpgrades.length = inventoryLength d ∧
      RowsAppliedW X W' (toRows T.manifest.proxyUpgrades) := by
  unfold applyProxyUpgradeTransition
  by_cases h : X.hasCode T.addr = true ∧ T.manifest.domain = d ∧ X.hasCode T.manifest.engine = true
  · rw [ite_eq_left h, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨M, hE, hP⟩
      obtain ⟨rfl, h1, h2, h3, h4, h5⟩ := postChecks_eq_some.mp hP
      exact ⟨h, hE, h1, h2, h3, h4, h5⟩
    · rintro ⟨-, hE, h1, h2, h3, h4, h5⟩
      exact ⟨W', hE, postChecks_eq_some.mpr ⟨rfl, h1, h2, h3, h4, h5⟩⟩
  · rw [ite_eq_right h]
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h', -⟩
    exact h h'

lemma applyL1Upgrade_eq_some {X : Exec} {E : Engines} {caller : Address} {T : TransitionObj}
    {W W' : World} :
    applyL1Upgrade X E caller T W = some W' ↔
      (caller = W.owner ∧ X.hasCode T.addr = true ∧ T.manifest.domain = .core ∧
        X.hasCode T.manifest.engine = true ∧
        E T.manifest.engine ⟨T.addr, T.manifest.engine, .core, X.pa, 0⟩ T.manifest.proxyUpgrades W
          = some W' ∧
        W'.owner = W.owner ∧ W'.pendingOwner = W.pendingOwner ∧
        X.keccakOwner W'.paOwner = X.keccakOwner W.paOwner ∧
        T.manifest.proxyUpgrades.length = L1_ECOSYSTEM_CONTRACT_COUNT ∧
        RowsAppliedW X W' (toRows T.manifest.proxyUpgrades)) := by
  unfold applyL1Upgrade
  by_cases hc : caller = W.owner
  · rw [ite_eq_left hc, applyProxyUpgradeTransition_eq_some]
    simp only [domainHolders, ↓reduceIte]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7, h8, h9⟩
      exact ⟨hc, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    · rintro ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      exact ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7, h8, h9⟩
  · rw [ite_eq_right hc]
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h', -⟩
    exact hc h'

/-! ## The row reads -/

lemma getProxyImplementation_admin {X : Exec} {W : World} {p : Address} (h : W.admin p = X.pa) :
    getProxyImplementation X W p = some (W.impl p) := by
  simp [getProxyImplementation, h]

lemma getProxyImplementation_moved {X : Exec} {W : World} {p : Address} (h : W.admin p ≠ X.pa) :
    getProxyImplementation X W p = X.implAnswer (W.impl p) p := by
  simp [getProxyImplementation, h]

/-! ## `RowsCurrent` relations, unfolded -/

lemma applyRow_iff {C : Config} {I J : Impl} {r : Row} :
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

lemma applyLoop_nil_iff {C : Config} {I K : Impl} : ApplyLoop C I [] K ↔ K = I := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact ApplyLoop.nil

lemma applyLoop_cons_iff {C : Config} {I K : Impl} {r : Row} {rs : List Row} :
    ApplyLoop C I (r :: rs) K ↔ ∃ J, ApplyRow C I r J ∧ ApplyLoop C J rs K := by
  constructor
  · intro h
    cases h with
    | cons h1 h2 => exact ⟨_, h1, h2⟩
  · rintro ⟨J, h1, h2⟩
    exact ApplyLoop.cons h1 h2

/-! ## The default engine is `RowsCurrent.ApplyRows` -/

/-- A world that differs from `W` only in the implementation mapping. -/
lemma world_impl_eta (W : World) : ({ W with impl := W.impl } : World) = W := rfl

lemma swapW_eq {X : Exec} (hK : ReinitKeepsAdmins X) (r : Row) (W : World) :
    swapW X r W = { W with impl := swap (rowsConfig X W) r W.impl } := by
  unfold swapW swap
  by_cases h : r.callInitializeUpgrade = true
  · rw [ite_eq_left h, ite_eq_left h, hK r W.admin]; rfl
  · rw [ite_eq_right h, ite_eq_right h]

lemma applyRowW_spec {X : Exec} {W W1 : World} {r : Row} (hK : ReinitKeepsAdmins X)
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

lemma applyLoopW_spec {X : Exec} (hK : ReinitKeepsAdmins X) :
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

lemma rowsAppliedW_iff {X : Exec} {W : World} {rows : List Row}
    (hadm : ∀ r ∈ rows, W.admin r.proxy = X.pa) :
    RowsAppliedW X W rows ↔ RowsApplied W.impl rows := by
  constructor
  · intro h r hr
    have := h r hr
    rw [getProxyImplementation_admin (hadm r hr)] at this
    exact Option.some.inj this
  · intro h r hr
    rw [getProxyImplementation_admin (hadm r hr), h r hr]

lemma applyRowsW_spec {X : Exec} {rows : List Row} {W W' : World} (hK : ReinitKeepsAdmins X)
    (hadm : ∀ r ∈ rows, W.admin r.proxy = X.pa) :
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

lemma defaultEngine_eq_some {X : Exec} {ctx : Context} {inv : List Row} {W W' : World} :
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
  intro X h s E caller T W
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

theorem CorePostCheckScopeIsRows : Properties.CorePostCheckScopeIsRows := by
  intro X E E' caller T W M M' hE hE' ho hp hpa hrows
  have hread : ∀ r ∈ toRows T.manifest.proxyUpgrades,
      getProxyImplementation X M' r.proxy = getProxyImplementation X M r.proxy := by
    intro r hr
    obtain ⟨hi, ha⟩ := hrows r hr
    unfold getProxyImplementation
    rw [hi, ha]
  have happ : RowsAppliedW X M' (toRows T.manifest.proxyUpgrades) ↔
      RowsAppliedW X M (toRows T.manifest.proxyUpgrades) :=
    ⟨fun h r hr => (hread r hr) ▸ h r hr, fun h r hr => (hread r hr).symm ▸ h r hr⟩
  rw [applyL1Upgrade_eq_some, applyL1Upgrade_eq_some]
  constructor
  · rintro ⟨h1, h2, h3, h4, -, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h3, h4, hE', ho.trans h6, hp.trans h7, by rw [hpa]; exact h8, h9,
      happ.mpr h10⟩
  · rintro ⟨h1, h2, h3, h4, -, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h3, h4, hE, ho ▸ h6, hp ▸ h7, by rw [← hpa]; exact h8, h9, happ.mp h10⟩

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

theorem DefaultCoreLegIsApplyRows : Properties.DefaultCoreLegIsApplyRows := by
  intro X E caller T W W' hE hadm hK
  rw [applyL1Upgrade_eq_some, hE, defaultEngine_eq_some, applyRowsW_spec hK hadm]
  simp only [inventoryLength]
  constructor
  · rintro ⟨h1, h2, h3, h4, ⟨h5, hl, hA, hW⟩, -, -, -, -, -⟩
    exact ⟨h1, h2, h3, h4, h5, hl, hA, hW⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    have hadm' : ∀ r ∈ toRows T.manifest.proxyUpgrades, W'.admin r.proxy = X.pa := by
      intro r hr; rw [h8]; exact hadm r hr
    refine ⟨h1, h2, h3, h4, ⟨h5, h6, h7, h8⟩, ?_, ?_, ?_, h6, ?_⟩
    · rw [h8]
    · rw [h8]
    · rw [h8]
    · exact (rowsAppliedW_iff hadm').mpr h7.verified

theorem DefaultCoreLegOnlyNamedEdges : Properties.DefaultCoreLegOnlyNamedEdges := by
  intro X E caller T W W' hE hadm hK hd hf h
  obtain ⟨-, -, -, -, -, -, hA, hW⟩ :=
    (DefaultCoreLegIsApplyRows X E caller T W W' hE hadm hK).mp h
  refine ⟨by rw [hW], by rw [hW], by rw [hW], by rw [hW], ?_⟩
  exact Contracts.ProxyUpgradeCurrent.OnlyNamedEdgesAcrossCall _ _ _ _ hd hf hA

theorem DefaultCoreLegNeedsOwnedAdmin : Properties.DefaultCoreLegNeedsOwnedAdmin := by
  intro X E caller T W hE ho
  cases hl : applyL1Upgrade X E caller T W with
  | none => rfl
  | some W' =>
    obtain ⟨-, -, -, -, h5, -⟩ := applyL1Upgrade_eq_some.mp hl
    rw [hE] at h5
    exact absurd (defaultEngine_eq_some.mp h5).1 ho

/-! ## Witness facts -/

lemma toRows_coreInventory : toRows coreInventory = [coreRow] := by decide

lemma genuine_coreTransition : Genuine coreTransition := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · show toRows coreInventory ≠ []
    rw [toRows_coreInventory]; simp
  · show ValidRows (toRows coreInventory)
    rw [toRows_coreInventory]
    exact ⟨by simp [coreRow], by simp [coreRow], by simp⟩

lemma toRows_coreInventoryInit : toRows coreInventoryInit = [coreRowInit] := by decide

lemma genuine_coreTransitionInit : Genuine coreTransitionInit := by
  refine ⟨by decide, ?_, ?_, by decide⟩
  · show toRows coreInventoryInit ≠ []
    rw [toRows_coreInventoryInit]; simp
  · show ValidRows (toRows coreInventoryInit)
    rw [toRows_coreInventoryInit]
    exact ⟨by simp [coreRowInit], by simp [coreRowInit], by simp⟩

/-! ## Certificates: what the checks do not cover -/

theorem CoreEngineMovesUnnamedSingletonAdmin : Properties.CoreEngineMovesUnnamedSingletonAdmin := by
  refine ⟨{ wAfter with admin := upd wWorld.admin 6 9 }, genuine_coreTransition, rfl, rfl, ?_,
    by decide, by decide, by decide, rfl, rfl⟩
  show ∀ r ∈ toRows coreInventory, r.proxy ≠ 6
  rw [toRows_coreInventory]; decide

theorem CoreEngineMovesUnnamedSingletonImpl : Properties.CoreEngineMovesUnnamedSingletonImpl := by
  refine ⟨{ wAfter with impl := upd wAfter.impl 7 13 }, genuine_coreTransition, rfl, ?_,
    rfl, by decide, by decide⟩
  show ∀ r ∈ toRows coreInventory, r.proxy ≠ 7 ∧ r.implNew ≠ 13
  rw [toRows_coreInventory]; decide

/-! ## Certificates: the checks are load-bearing -/

theorem CorePAOwnerMoveUnderCollisionPasses : Properties.CorePAOwnerMoveUnderCollisionPasses :=
  ⟨{ wAfter with paOwner := 9 }, genuine_coreTransition, rfl, rfl, rfl, by decide⟩

theorem CorePAOwnerCheckIsLoadBearing : Properties.CorePAOwnerCheckIsLoadBearing := by
  refine ⟨{ wAfter with paOwner := 9 }, rfl, rfl, rfl, ?_, by decide, rfl⟩
  rw [toRows_coreInventory]; decide

theorem CoreExecutorOwnerCheckIsLoadBearing : Properties.CoreExecutorOwnerCheckIsLoadBearing := by
  refine ⟨{ wAfter with owner := 9 }, rfl, by decide, rfl, rfl, ?_, rfl⟩
  rw [toRows_coreInventory]; decide

theorem CorePendingOwnerCheckIsLoadBearing : Properties.CorePendingOwnerCheckIsLoadBearing := by
  refine ⟨{ wAfter with pendingOwner := 9 }, rfl, rfl, by decide, rfl, ?_, rfl⟩
  rw [toRows_coreInventory]; decide

theorem CoreRowsCheckIsLoadBearing : Properties.CoreRowsCheckIsLoadBearing := by
  refine ⟨genuine_coreTransition, rfl, ?_, rfl⟩
  rw [toRows_coreInventory]; decide

/-! ## Certificates: (b) countermodel -/

theorem CoreRowAdminMoveUncaughtWhenAnswerMatches :
    Properties.CoreRowAdminMoveUncaughtWhenAnswerMatches := by
  refine ⟨{ wAfter with impl := upd wAfter.impl 5 12, admin := upd wWorld.admin 5 9 },
    genuine_coreTransition, rfl, ?_, rfl, by decide, by decide, rfl⟩
  show coreRow ∈ toRows coreInventory
  rw [toRows_coreInventory]; simp

/-! ## Certificates: (c) countermodel and (d) witness -/

theorem DefaultLegNeedsAdministeredRows : Properties.DefaultLegNeedsAdministeredRows := by
  refine ⟨genuine_coreTransition, rfl, by decide, by decide, ?_⟩
  intro h
  have := h.verified coreRow (by show coreRow ∈ toRows coreInventory; rw [toRows_coreInventory]; simp)
  revert this; decide

theorem DefaultLegReinitMovesRowAdmin : Properties.DefaultLegReinitMovesRowAdmin := by
  refine ⟨{ wAfter with admin := upd wWorld.admin 5 9 }, genuine_coreTransitionInit, rfl, ?_, ?_,
    rfl, rfl, rfl, by decide, ?_, rfl⟩
  · show ∀ r ∈ toRows coreInventoryInit, wWorld.admin r.proxy = wExecReinit.pa
    intro r _; rfl
  · intro h
    have := congrFun (h coreRowInit wWorld.admin) 5
    revert this; decide
  · intro h
    have := congrFun (congrArg World.admin h) 5
    revert this; decide

theorem UnownedReplayRevertsAtV35 : Properties.UnownedReplayRevertsAtV35 := by
  refine ⟨{ wAfter with paOwner := 7 }, genuine_coreTransition, by decide, ?_, ?_, rfl⟩
  · intro r _; rfl
  · show ApplyRows _ _ (toRows coreInventory) _
    rw [toRows_coreInventory]
    refine ⟨fun r _ => rfl, ApplyLoop.cons (ApplyRow.alreadyAtTarget ?_) ApplyLoop.nil, ?_⟩
    · decide
    · intro r hr
      rw [List.mem_singleton] at hr
      subst hr
      decide

theorem CoreLegWitness : Properties.CoreLegWitness := by
  refine ⟨wAfter, genuine_coreTransition, rfl, rfl, rfl, ?_, fun _ _ => rfl, ?_,
    fun _ _ _ _ => rfl, rfl,
    rfl, by decide, by decide, rfl, rfl, rfl⟩
  · show ∀ r ∈ toRows coreInventory, wWorld.admin r.proxy = wExec.pa
    intro r _; rfl
  · show (toRows coreInventory).Pairwise (fun a b => a.proxy ≠ b.proxy)
    rw [toRows_coreInventory]; simp

end Contracts.ProxyUpgradeExecutorV35.CoreLeg
