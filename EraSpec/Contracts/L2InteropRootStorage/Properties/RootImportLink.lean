import EraSpec.Contracts.L2InteropRootStorage.Specs.RootImportLink

/-!
# Properties: the storage's runs and `Contracts.RootImport`'s imported roots

Statements about `EraSpec.Contracts.L2InteropRootStorage.Specs.RootImportLink`; proofs are in
`EraSpec.Contracts.L2InteropRootStorage.Proofs.RootImportLink`.  No hash premise.

* `StorageRunsGrowImportsAtC67894b9`: if every destination's `c67894b9` storage moves by a run of
  that contract, the induced worlds are related by `Contracts.RootImport.ImportsGrow`, the premise
  of `Contracts.RootImport.Properties.FinalizableAtPersistsAsImportsGrow`.
* `StorageRunsGrowImportsWitness`: one destination imports a root along a run, so the later world
  has an import the earlier one lacks.
-/

namespace Contracts.InteropRootStorage

/-- **AT `c67894b9`, THE STORAGE'S RUNS ONLY ADD IMPORTS.**  For any settlement-layer roots and
`L1_CHAIN_ID`s, if each destination's storage `R d` reaches `R' d` by a run of the `c67894b9`
contract, then the world read off `R'` is a later snapshot of the world read off `R` in the sense
of `Contracts.RootImport.ImportsGrow`: the same roots and configuration, and every import of the
first still an import of the second. -/
def Properties.StorageRunsGrowImportsAtC67894b9 : Prop :=
  ∀ (slRoot : Contracts.Atomicity.Chain → ℕ → Contracts.Timeout.SlRoot)
    (l1 : Contracts.RootImport.Dest → Contracts.Atomicity.Chain)
    (R R' : Contracts.RootImport.Dest → RootsAtC67),
    (∀ d, ReachAtC67 (R d) (R' d)) →
      Contracts.RootImport.ImportsGrow (importWorldAtC67 slRoot l1 R) (importWorldAtC67 slRoot l1 R')

/-- **A RUN THAT ADDS AN IMPORT.**  Destination 5 runs from fresh storage to a state holding a root
at `(9, 7)`, every other destination stays at fresh storage: the premise of
`StorageRunsGrowImportsAtC67894b9` holds, and the later world has destination 5's import of
`(9, 7)`, which the earlier one does not have. -/
def Properties.StorageRunsGrowImportsWitness : Prop :=
  ∃ (R R' : Contracts.RootImport.Dest → RootsAtC67),
    (∀ d, ReachAtC67 (R d) (R' d)) ∧
    ∀ (slRoot : Contracts.Atomicity.Chain → ℕ → Contracts.Timeout.SlRoot)
      (l1 : Contracts.RootImport.Dest → Contracts.Atomicity.Chain),
      ¬ (importWorldAtC67 slRoot l1 R).imported 5 9 7 ∧ (importWorldAtC67 slRoot l1 R').imported 5 9 7

end Contracts.InteropRootStorage
