import EraSpec.Contracts.ChainTypeManager.Properties.ExecutorRowsUnvalidated
import EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorForward
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsUnvalidated

/-!
# Proofs: the executor's fixed entry points, for any transition object

The infrastructure step is `ProxyUpgradeCurrent.ApplyTransition`, so the row library's
`OnlyNamedEdgesAcrossTransitionAnyRows` gives the edge for any object. The other fixed entry
points leave the implementation mapping unchanged. The witness is one concrete step.
-/

namespace Contracts.ChainTypeManager

theorem FixedEntrypointsMoveProxiesOnlyAlongRowsAnyRows :
    Properties.FixedEntrypointsMoveProxiesOnlyAlongRowsAnyRows := by
  intro X s s' x hf h hnf
  show ∀ p, _
  intro p
  cases h with
  | @infra T J c' happ _ =>
      rcases ProxyUpgradeCurrent.OnlyNamedEdgesAcrossTransitionAnyRows X.rc .ctm T s.impl J hf
          happ p with h1 | ⟨r, hr, hp, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨T, r, rfl, hr, hp, h2, h3⟩
  | forward _ => exact absurd rfl (hnf _)
  | _ => exact Or.inl rfl

theorem ExecutorAnyRowsWitness : Properties.ExecutorAnyRowsWitness := by
  have happ : ProxyUpgradeCurrent.ApplyTransition wX.rc .ctm ProxyUpgradeCurrent.wDupTransition
      ProxyUpgradeCurrent.wImpl
      (ProxyUpgradeCurrent.swap ProxyUpgradeCurrent.wConfig ProxyUpgradeCurrent.rowB
        ProxyUpgradeCurrent.wImpl) :=
    ⟨trivial, rfl, ProxyUpgradeCurrent.applyRows_dup_wConfig⟩
  refine ⟨ProxyUpgradeCurrent.wConfig_frames,
    fun hg => ProxyUpgradeCurrent.not_distinct_BB2 hg.2.distinctProxies,
    ProxyUpgradeCurrent.not_distinct_BB2, (fun _ h => by cases h), ?_, _,
    XStep.infra happ (fun _ => rfl), rfl, by decide, by decide⟩
  intro r hr
  rcases ProxyUpgradeCurrent.mem_pair hr with rfl | rfl <;> decide

end Contracts.ChainTypeManager
