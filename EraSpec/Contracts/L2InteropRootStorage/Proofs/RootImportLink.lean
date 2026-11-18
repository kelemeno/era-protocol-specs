import EraSpec.Contracts.L2InteropRootStorage.Properties.RootImportLink
import EraSpec.Contracts.L2InteropRootStorage.Proofs.Storage

/-!
# Proofs: the storage's runs and `Contracts.RootImport`'s imported roots

`ImportsGrow` is `no_overwrite_at_c67894b9` read through `importWorldAtC67`.
-/

namespace Contracts.InteropRootStorage

theorem storage_runs_grow_imports_at_c67894b9
    (slRoot : Contracts.Atomicity.Chain → ℕ → Contracts.Timeout.SlRoot)
    (l1 : Contracts.RootImport.Dest → Contracts.Atomicity.Chain)
    (R R' : Contracts.RootImport.Dest → RootsAtC67) (h : ∀ d, ReachAtC67 (R d) (R' d)) :
    Contracts.RootImport.ImportsGrow (importWorldAtC67 slRoot l1 R) (importWorldAtC67 slRoot l1 R') := by
  refine ⟨rfl, rfl, ?_⟩
  intro d sl k himp
  show (R' d sl (Nat.toUInt256 k)).root ≠ 0
  rw [no_overwrite_at_c67894b9 (h d) himp]
  exact himp

theorem storage_runs_grow_imports_witness : Properties.StorageRunsGrowImportsWitness := by
  let S₁ := writeRoot empty 9 7 5 0xdd
  have h1 : Reach empty S₁ := reach_of_addRoot (addRoot_mk (by decide) (by decide) rfl)
  refine ⟨fun _ => empty.storedInteropRoots,
    fun d => if d = 5 then S₁.storedInteropRoots else empty.storedInteropRoots, ?_, ?_⟩
  · intro d
    by_cases hd : d = 5
    · simp only [hd, ite_true]
      exact reach_projects h1
    · simp only [hd, ite_false]
      exact ReachAtC67.refl
  · intro slRoot l1
    exact ⟨fun h => h (show (empty.storedInteropRoots 9 (Nat.toUInt256 7)).root = 0 by decide),
      show (S₁.storedInteropRoots 9 (Nat.toUInt256 7)).root ≠ 0 by decide⟩

theorem StorageRunsGrowImportsAtC67894b9 : Properties.StorageRunsGrowImportsAtC67894b9 :=
  storage_runs_grow_imports_at_c67894b9
theorem StorageRunsGrowImportsWitness : Properties.StorageRunsGrowImportsWitness :=
  storage_runs_grow_imports_witness

end Contracts.InteropRootStorage
