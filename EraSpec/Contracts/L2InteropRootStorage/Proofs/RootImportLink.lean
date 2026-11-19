import EraSpec.Contracts.L2InteropRootStorage.Properties.RootImportLink
import EraSpec.Contracts.L2InteropRootStorage.Proofs.Storage

/-!
# Proofs: the storage's runs and `Contracts.RootImport`'s imported roots

`ImportsGrow` is `no_overwrite` read through `importWorld`.
-/

namespace Contracts.InteropRootStorage

theorem storage_runs_grow_imports
    (slRoot : Contracts.Atomicity.Chain → ℕ → Contracts.Timeout.SlRoot)
    (l1 : Contracts.RootImport.Dest → Contracts.Atomicity.Chain)
    (S S' : Contracts.RootImport.Dest → State) (h : ∀ d, Reach (S d) (S' d)) :
    Contracts.RootImport.ImportsGrow (importWorld slRoot l1 S) (importWorld slRoot l1 S') := by
  refine ⟨rfl, rfl, ?_⟩
  intro d sl k himp
  show ((S' d).storedInteropRoots sl (Nat.toUInt256 k)).root ≠ 0
  rw [no_overwrite (h d) himp]
  exact himp

theorem storage_runs_grow_imports_run_witness : Properties.StorageRunsGrowImportsRunWitness := by
  let S₁ := writeRoot empty 9 7 5 0xdd
  have h1 : Reach empty S₁ := reach_of_addRoot (addRoot_mk (by decide) (by decide) rfl)
  refine ⟨fun _ => empty, fun d => if d = 5 then S₁ else empty, ?_, ?_⟩
  · intro d
    by_cases hd : d = 5
    · simp only [hd, ite_true]
      exact h1
    · simp only [hd, ite_false]
      exact Reach.refl
  · intro slRoot l1
    exact ⟨fun h => h (show (empty.storedInteropRoots 9 (Nat.toUInt256 7)).root = 0 by decide),
      show (S₁.storedInteropRoots 9 (Nat.toUInt256 7)).root ≠ 0 by decide⟩

theorem StorageRunsGrowImports : Properties.StorageRunsGrowImports := storage_runs_grow_imports
theorem StorageRunsGrowImportsRunWitness : Properties.StorageRunsGrowImportsRunWitness :=
  storage_runs_grow_imports_run_witness

end Contracts.InteropRootStorage
