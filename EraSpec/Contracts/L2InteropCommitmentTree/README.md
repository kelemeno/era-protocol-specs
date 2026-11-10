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
| Reaches | [Specs/Reaches.lean](Specs/Reaches.lean) | [Properties/Reaches.lean](Properties/Reaches.lean) | [Proofs/Reaches.lean](Proofs/Reaches.lean) |
| HintSearch | [Specs/HintSearch.lean](Specs/HintSearch.lean) | [Properties/HintSearch.lean](Properties/HintSearch.lean) | [Proofs/HintSearch.lean](Proofs/HintSearch.lean) |
| TreeRoot | [Specs/TreeRoot.lean](Specs/TreeRoot.lean) | [Properties/TreeRoot.lean](Properties/TreeRoot.lean) | [Proofs/TreeRoot.lean](Proofs/TreeRoot.lean) |

The library's abstract list/order theory, insertion-guard countermodels, and
reset/sentinel properties live under `../IndexedMerkleTree/`. The wrapper model
projects into `../IndexedMerkleTree/Specs/Model.lean`; that shared use does not make the
library specification a Core module.

`Reaches` is the batch-sized step (any number of guarded inserts) and shows the
key set only grows. `HintSearch` proves the contract's insert flow yields
`InsertGuard`, that `leafCount` hops always suffice, and that the deployed
constant fuel can make an honest insert revert (a liveness caveat).
`TreeRoot` adds the root over the list state and the two verifiers as they
consume an attacker's proof: sound and complete under `HashAssumptions`, and a
countermodel on a real run showing `padNotLeaf` is load-bearing and **false at
the pinned commit** (the setup pads with `hashLeaf({0,0,0})`). The soundness
results take `HashAssumptions`, which `HashAssumptionsUnsatisfiable` shows no hash
meets, so they are vacuous as stated; the padding countermodels take no such
premise and stand.

Root authentication and hash assumptions have separate proofs under `../Merkle/`
and `../FullMerkle/`. Caller authorization, compiled search, and dispatcher-to-model
correspondence remain implementation obligations in `../../Refinement.lean`.
