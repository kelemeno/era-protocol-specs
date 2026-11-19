import EraSpec.Contracts.L2InteropRootStorage.Specs.RootImportLink

/-!
# Properties: the storage's runs and `Contracts.RootImport`'s imported roots

Statements about `EraSpec.Contracts.L2InteropRootStorage.Specs.RootImportLink`; proofs are in
`EraSpec.Contracts.L2InteropRootStorage.Proofs.RootImportLink`.  No hash premise.

* `StorageRunsGrowImports`: if every destination's storage moves by a run of the contract, the
  induced worlds are related by `Contracts.RootImport.ImportsGrow`, the premise of
  `Contracts.RootImport.Properties.FinalizableAtPersistsAsImportsGrow`.
* `StorageRunsGrowImportsRunWitness`: one destination imports a root along a run, so the later
  world has an import the earlier one lacks.
-/

namespace Contracts.InteropRootStorage

/-- **THE STORAGE'S RUNS ONLY ADD IMPORTS.**  For any settlement-layer roots and `L1_CHAIN_ID`s,
if each destination's storage `S d` reaches `S' d` by a run of the contract, then the world read
off `S'` is a later snapshot of the world read off `S` in the sense of
`Contracts.RootImport.ImportsGrow`: the same roots and configuration, and every import of the
first still an import of the second. -/
def Properties.StorageRunsGrowImports : Prop :=
  ∀ (slRoot : Contracts.Atomicity.Chain → ℕ → Contracts.Timeout.SlRoot)
    (l1 : Contracts.RootImport.Dest → Contracts.Atomicity.Chain)
    (S S' : Contracts.RootImport.Dest → State),
    (∀ d, Reach (S d) (S' d)) →
      Contracts.RootImport.ImportsGrow (importWorld slRoot l1 S) (importWorld slRoot l1 S')

/-- **A RUN THAT ADDS AN IMPORT.**  Destination 5 runs from fresh storage to a state holding a root
at `(9, 7)`, every other destination stays at fresh storage: the premise of
`StorageRunsGrowImports` holds, and the later world has destination 5's import of `(9, 7)`, which
the earlier one does not have. -/
def Properties.StorageRunsGrowImportsRunWitness : Prop :=
  ∃ (S S' : Contracts.RootImport.Dest → State),
    (∀ d, Reach (S d) (S' d)) ∧
    ∀ (slRoot : Contracts.Atomicity.Chain → ℕ → Contracts.Timeout.SlRoot)
      (l1 : Contracts.RootImport.Dest → Contracts.Atomicity.Chain),
      ¬ (importWorld slRoot l1 S).imported 5 9 7 ∧ (importWorld slRoot l1 S').imported 5 9 7

end Contracts.InteropRootStorage
