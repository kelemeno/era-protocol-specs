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
| Verifier | [Specs/Verifier.lean](Specs/Verifier.lean) | [Properties/Verifier.lean](Properties/Verifier.lean) | [Proofs/Verifier.lean](Proofs/Verifier.lean) |
| PathCollision | [Specs/PathCollision.lean](Specs/PathCollision.lean) | [Properties/PathCollision.lean](Properties/PathCollision.lean) | [Proofs/PathCollision.lean](Proofs/PathCollision.lean) |

`Verifier` drops `ProofSound`'s two hypotheses (occupied index, path length equal to
the tree height), which `Merkle.calculateRootMemory` does not check: an accepted
walk pins the level-0 entry at any index (padding included), and under domain
separation the accepted path length is the tree height. All four non-padded results
(`AcceptPinsEntry`, `AcceptPinsEntryCases`, `AcceptForcesHeight`,
`AcceptPinsEntryAnyLength`) take a global pair-injectivity premise `hinj`, which no
`UInt256` hash satisfies (`Contracts.InteropCommitmentTree.not_nodeInj`), so they are
vacuous as stated. The honest-walk and padded-slot results take no such premise.

`PathCollision` is the repair: an accepted path opens the tree's entry, **or** the
theorem names the level at which the verifier hashed a pair different from the tree's
pair to the same value (`AcceptPinsEntryOrCollision`, no hash premise). The collision
is pinned to the instance, and `HonestWalkNoCollision` shows it is false on the honest
path, so the disjunction is not trivially true.

The tree levels and walk definitions are in `../FullMerkle/Specs/Model.lean`; capacity,
padding, and cached-hash properties are alongside that model. A pure root theorem
does not alone prove that contract storage, proof indices, and hash inputs
represent those same leaves. See obligation O7 in `../../Refinement.lean`.
