# IndexedMerkleTree

Source: `contracts/common/libraries/IndexedMerkleTree.sol` in the pinned
era-contracts tree. This folder owns the library's abstract IMT theory even
though the proofs are mathematical and shared by other contracts.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| InsertGuard | [Specs/InsertGuard.lean](Specs/InsertGuard.lean) | [Properties/InsertGuard.lean](Properties/InsertGuard.lean) | [Proofs/InsertGuard.lean](Proofs/InsertGuard.lean) |
| ResetAndZero | [Specs/ResetAndZero.lean](Specs/ResetAndZero.lean) | [Properties/ResetAndZero.lean](Properties/ResetAndZero.lean) | [Proofs/ResetAndZero.lean](Proofs/ResetAndZero.lean) |
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |

The deployed wrapper's indexed storage/search model is
`../L2InteropCommitmentTree/Specs/Model.lean`, which projects into this abstract theory.
Hash-tree behavior and proof soundness live under `../FullMerkle/` and `../Merkle/`.
These results do not alone establish compiled storage/root correspondence,
authorized callers, or the wrapper's one-time initialization guard; see
`../../Refinement.lean`.
