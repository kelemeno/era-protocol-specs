# L2InteropCommitmentTree

Source: `contracts/atomic-interop/L2InteropCommitmentTree.sol`, using
`contracts/common/libraries/IndexedMerkleTree.sol` in the pinned era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |

The library's abstract list/order theory, insertion-guard countermodels, and
reset/sentinel properties live under `../IndexedMerkleTree/`. The wrapper model
projects into `../IndexedMerkleTree/Specs/Model.lean`; that shared use does not make the
library specification a Core module.

Root authentication and hash assumptions have separate proofs under `../Merkle/`
and `../FullMerkle/`. Caller authorization, compiled search, and dispatcher-to-model
correspondence remain implementation obligations in `../../Refinement.lean`.
