# Merkle

Source: `contracts/common/libraries/Merkle.sol`, also supporting FullMerkle and
indexed-Merkle proof verification in the pinned era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| ProofSound | [Specs/ProofSound.lean](Specs/ProofSound.lean) | [Properties/ProofSound.lean](Properties/ProofSound.lean) | [Proofs/ProofSound.lean](Proofs/ProofSound.lean) |
| RootBinding | [Specs/RootBinding.lean](Specs/RootBinding.lean) | [Properties/RootBinding.lean](Properties/RootBinding.lean) | [Proofs/RootBinding.lean](Proofs/RootBinding.lean) |
| RootForgery | [Specs/RootForgery.lean](Specs/RootForgery.lean) | [Properties/RootForgery.lean](Properties/RootForgery.lean) | [Proofs/RootForgery.lean](Proofs/RootForgery.lean) |

The tree levels and walk definitions are in `../FullMerkle/Specs/Model.lean`; capacity,
padding, and cached-hash properties are alongside that model. A pure root theorem
does not alone prove that contract storage, proof indices, and hash inputs
represent those same leaves. See obligation O7 in `../../Refinement.lean`.
