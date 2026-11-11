# FullMerkle

Source: `contracts/common/libraries/FullMerkle.sol` in the pinned era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| CachedHashInjectivity | [Specs/CachedHashInjectivity.lean](Specs/CachedHashInjectivity.lean) | [Properties/CachedHashInjectivity.lean](Properties/CachedHashInjectivity.lean) | [Proofs/CachedHashInjectivity.lean](Proofs/CachedHashInjectivity.lean) |
| CapacityInvariant | [Specs/CapacityInvariant.lean](Specs/CapacityInvariant.lean) | [Properties/CapacityInvariant.lean](Properties/CapacityInvariant.lean) | [Proofs/CapacityInvariant.lean](Proofs/CapacityInvariant.lean) |
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| TreeShape | [Specs/TreeShape.lean](Specs/TreeShape.lean) | [Properties/TreeShape.lean](Properties/TreeShape.lean) | [Proofs/TreeShape.lean](Proofs/TreeShape.lean) |

The model is mathematical and EVM-free, but it describes FullMerkle and belongs
here. Verification soundness and root binding/forgery results live under
`../Merkle/`. Correspondence with compiled push/growth behavior and real
leaf/padding domain separation must still be supplied by the implementation.
