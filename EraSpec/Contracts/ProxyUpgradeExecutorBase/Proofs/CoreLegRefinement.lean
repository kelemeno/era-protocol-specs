import EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.CoreLegRefinement
import EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.CoreLegV35
import EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.DomainHoldersV35

/-!
# Proofs: the Core leg is the canonical leg in the Core domain

With no CTM, `DomainHoldersV35`'s holder preimage is the one-word list of the `ProxyAdmin`'s
owner, its CTM-admin check passes, and its rows check reads the embedded slots exactly as
`CoreLeg`'s does. The two legs then make the same checks on the same values;
`CoreLegIsDomainHoldersLeg` compares them case by case. The derived result instantiates the
`DomainHoldersV35` engine with the embedding of the `CoreLeg` engine's run.
-/

namespace Contracts.CoreLegRefinement

open Contracts.ProxyUpgradeExecutorV35

private lemma domainMap_eq_core {d : Contracts.ProxyUpgradeCurrent.Domain} :
    domainMap d = .core ↔ d = .core := by
  cases d <;> simp [domainMap]

private lemma toRows_map (l : List Contracts.ProxyUpgradeCurrent.Row) :
    DomainHoldersV35.toRows (l.map rowMap) = (Contracts.ProxyUpgradeCurrent.toRows l).map rowMap := by
  simp only [DomainHoldersV35.toRows, Contracts.ProxyUpgradeCurrent.toRows,
    Contracts.ProxyUpgradeCurrent.dropInertSlots, List.filter_map]
  rfl

private lemma preimage (X : CoreLeg.Exec) (H : DomainHoldersV35.Hash) (w : DomainHoldersV35.World) :
    DomainHoldersV35.holderPreimage (bindings X) H w = some [w.paOwner] := by
  simp [DomainHoldersV35.holderPreimage, bindings]

private lemma holders (X : CoreLeg.Exec) (w₀ : DomainHoldersV35.World) (W : CoreLeg.World) :
    DomainHoldersV35.domainHolders (bindings X) (env X).H (embed X w₀ W)
      = some (X.keccakOwner W.paOwner) := by
  simp [DomainHoldersV35.domainHolders, preimage, env, embed]

private lemma rowsApplied_iff (X : CoreLeg.Exec) (w₀ : DomainHoldersV35.World) (W : CoreLeg.World)
    (l : List Contracts.ProxyUpgradeCurrent.Row) :
    DomainHoldersV35.rowsApplied (bindings X) (embed X w₀ W) (l.map rowMap)
      ↔ CoreLeg.RowsAppliedW X W l := by
  simp only [DomainHoldersV35.rowsApplied, CoreLeg.RowsAppliedW, List.forall_mem_map,
    DomainHoldersV35.getProxyImplementation, CoreLeg.getProxyImplementation, bindings, embed, rowMap]
  refine forall₂_congr fun r _ => ?_
  by_cases h : W.admin r.proxy = X.pa
  · simp [h]
  · have h' : ¬ X.pa = W.admin r.proxy := fun e => h e.symm
    simp [h, h']

private lemma embed_execOwner (X : CoreLeg.Exec) (w₀ : DomainHoldersV35.World) (W : CoreLeg.World) :
    (embed X w₀ W).execOwner = W.owner := rfl

private lemma embed_execPendingOwner (X : CoreLeg.Exec) (w₀ : DomainHoldersV35.World)
    (W : CoreLeg.World) : (embed X w₀ W).execPendingOwner = W.pendingOwner := rfl

private lemma invLen_core (X : CoreLeg.Exec) :
    (env X).invLen .core = CoreLeg.inventoryLength .core := rfl

theorem CoreLegIsDomainHoldersLeg : Properties.CoreLegIsDomainHoldersLeg := by
  intro X E T W w₀ eng heng
  have hok : DomainHoldersV35.CtmAdminOk (bindings X) (embed X w₀ W) := Or.inl rfl
  by_cases hpre : X.hasCode T.addr = true ∧ T.manifest.domain = .core ∧
      X.hasCode T.manifest.engine = true
  swap
  · have hl : CoreLeg.applyProxyUpgradeTransition X E T .core 0 W = none := by
      simp only [CoreLeg.applyProxyUpgradeTransition]
      rw [ite_eq_right (fun h => hpre ⟨h.1, h.2.1, h.2.2.1⟩)]
    have hr : ¬ DomainHoldersV35.Prechecks (env X) (bindings X) T.addr (manifestMap T.manifest) := by
      rintro ⟨h1, h2, h3, -⟩
      exact hpre ⟨h1, domainMap_eq_core.1 h2, h3⟩
    simp [hl, DomainHoldersV35.leg, hr]
  obtain ⟨h1, h2, h3⟩ := hpre
  have hcore : CoreLeg.applyProxyUpgradeTransition X E T .core 0 W
      = (E T.manifest.engine (CoreLeg.context X T .core 0) T.manifest.proxyUpgrades W).bind
          (CoreLeg.postChecks X .core 0 T.manifest.proxyUpgrades (X.keccakOwner W.paOwner) W) := by
    simp [CoreLeg.applyProxyUpgradeTransition, h1, h2, h3, CoreLeg.domainHolders]
  rw [hcore]
  by_cases hlen : T.manifest.proxyUpgrades.length = CoreLeg.inventoryLength .core
  swap
  · have hr : ¬ DomainHoldersV35.Prechecks (env X) (bindings X) T.addr (manifestMap T.manifest) := by
      rintro ⟨-, -, -, h4⟩
      simp [manifestMap, invLen_core, bindings] at h4
      exact hlen h4
    have hl : (E T.manifest.engine (CoreLeg.context X T .core 0) T.manifest.proxyUpgrades W).bind
        (CoreLeg.postChecks X .core 0 T.manifest.proxyUpgrades (X.keccakOwner W.paOwner) W)
          = none := by
      rcases E T.manifest.engine (CoreLeg.context X T .core 0) T.manifest.proxyUpgrades W
        with _ | W'
      · rfl
      · simp [CoreLeg.postChecks, CoreLeg.toRowsChecked, hlen]
    simp [hl, DomainHoldersV35.leg, hr]
  have hp : DomainHoldersV35.Prechecks (env X) (bindings X) T.addr (manifestMap T.manifest) :=
    ⟨h1, by simp [manifestMap, h2, domainMap, bindings], h3,
      by simp [manifestMap, invLen_core, bindings, hlen]⟩
  simp only [DomainHoldersV35.leg, hp, hok, not_true_eq_false, ite_false, holders]
  have heng' : eng (bindings X).self
      (DomainHoldersV35.buildContext (bindings X) T.addr (manifestMap T.manifest))
      (manifestMap T.manifest).proxyUpgrades (embed X w₀ W)
      = (E T.manifest.engine (CoreLeg.context X T .core 0) T.manifest.proxyUpgrades W).map
          (embed X w₀) := heng
  rw [heng']
  rcases E T.manifest.engine (CoreLeg.context X T .core 0) T.manifest.proxyUpgrades W
    with _ | W'
  · rfl
  · simp only [Option.bind_some, Option.map_some, embed_execOwner, embed_execPendingOwner, holders,
      CoreLeg.postChecks, CoreLeg.domainHolders, CoreLeg.toRowsChecked, hlen, ite_true,
      Option.bind_some]
    by_cases ho : W'.owner = W.owner ∧ W'.pendingOwner = W.pendingOwner
    · have ho' : ¬ (W'.owner ≠ W.owner ∨ W'.pendingOwner ≠ W.pendingOwner) := by
        rintro (h | h)
        · exact h ho.1
        · exact h ho.2
      rw [ite_eq_left ho, ite_eq_right ho']
      by_cases hh : X.keccakOwner W'.paOwner = X.keccakOwner W.paOwner
      · simp only [hh, ite_true, ne_eq, not_true_eq_false, ite_false, manifestMap, toRows_map,
          rowsApplied_iff]
        by_cases hr : CoreLeg.RowsAppliedW X W' (Contracts.ProxyUpgradeCurrent.toRows
            T.manifest.proxyUpgrades)
        · simp [hr]
        · simp [hr]
      · simp [hh]
    · have ho' : W'.owner ≠ W.owner ∨ W'.pendingOwner ≠ W.pendingOwner := by
        by_contra hc
        push Not at hc
        exact ho hc
      rw [ite_eq_right ho, ite_eq_left ho']
      rfl

theorem CoreLegIsDomainHoldersLegSatisfiable :
    Properties.CoreLegIsDomainHoldersLegSatisfiable :=
  fun X E T W w₀ =>
    ⟨fun _ _ _ _ =>
      (E T.manifest.engine (CoreLeg.context X T .core 0) T.manifest.proxyUpgrades W).map
        (embed X w₀), rfl⟩

theorem CoreLegKeepsPAOwnerViaDomainHolders : Properties.CoreLegKeepsPAOwnerViaDomainHolders := by
  classical
  intro X E T W W' h
  let w₀ : DomainHoldersV35.World :=
    ⟨0, 0, 0, fun _ => ⟨0, 0⟩, fun _ => 0, fun _ => 0, fun _ => none, fun _ => none, 0, 0, fun _ => 0⟩
  let r := E T.manifest.engine (CoreLeg.context X T .core 0) T.manifest.proxyUpgrades W
  let eng : DomainHoldersV35.Engine := fun _ _ _ _ => r.map (embed X w₀)
  have hleg := CoreLegIsDomainHoldersLeg X E T W w₀ eng rfl
  rw [h, Option.map_some] at hleg
  rcases DomainHoldersV35.PassingLegKeepsHolderReads (env X) (bindings X) T.addr
      (manifestMap T.manifest) eng (embed X w₀ W) (embed X w₀ W') hleg.symm with ⟨hpa, -⟩ | hc
  · exact Or.inl hpa
  · right
    rcases hc with ⟨hne, -⟩ | ⟨p, p', hp, hp', hne, hH⟩
    · exact absurd rfl hne
    · rw [preimage] at hp hp'
      cases hp; cases hp'
      refine ⟨fun e => hne (by simp [embed, e]), ?_⟩
      simpa [env, embed] using hH.symm

end Contracts.CoreLegRefinement
