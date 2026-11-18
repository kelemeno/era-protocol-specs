import EraSpec.Contracts.L2InteropRootStorage.Specs.Storage
import EraSpec.Protocol.InteropAtomicity.Specs.RootImport

/-!
# Model link: the storage's runs and `Contracts.RootImport`'s imported roots

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.L2InteropRootStorage.Properties.RootImportLink`, proofs in
`EraSpec.Contracts.L2InteropRootStorage.Proofs.RootImportLink`.

`Contracts.RootImport` (`Protocol/InteropAtomicity/Specs/RootImport.lean`, pinned at `c67894b9`)
describes each destination's imports as a predicate `World.imported d sl k`, "destination `d`'s
`interopRoots(sl, k)` is nonzero", and relates two snapshots by `ImportsGrow`, which its docstring
justifies by `InteropRootAlreadyExists` and the absence of a removing entry point.  This file reads
that predicate off the `c67894b9` storage contract of `Specs/Storage.lean` (`RootsAtC67`), one
storage per destination, so that `ImportsGrow` can be derived from the contract's runs.

The settlement-layer roots (`slRoot`) and the destinations' `L1_CHAIN_ID`s (`l1`) are inputs: the
storage contract does not hold them.  `World` numbers blocks in `ℕ`; the storage key read for
block `k` is `Nat.toUInt256 k`, so blocks that agree modulo `2^256` read the same slot.
-/

namespace Contracts.InteropRootStorage

/-- The destination side of `Contracts.RootImport` whose imports are read off each destination's
`c67894b9` storage: `imported d sl k` holds when `R d` holds a nonzero root at
`(sl, Nat.toUInt256 k)`.  The settlement-layer roots and `L1_CHAIN_ID`s are given. -/
def importWorldAtC67 (slRoot : Contracts.Atomicity.Chain → ℕ → Contracts.Timeout.SlRoot)
    (l1 : Contracts.RootImport.Dest → Contracts.Atomicity.Chain)
    (R : Contracts.RootImport.Dest → RootsAtC67) : Contracts.RootImport.World where
  slRoot := slRoot
  imported := fun d sl k => (R d sl (Nat.toUInt256 k)).root ≠ 0
  l1 := l1

end Contracts.InteropRootStorage
