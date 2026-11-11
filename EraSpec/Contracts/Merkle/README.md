# Merkle

Source: `l1-contracts/contracts/common/libraries/Merkle.sol`, also supporting FullMerkle and
indexed-Merkle proof verification in the pinned era-contracts tree. This is the copy
`FullMerkle` and `IndexedMerkleTree` import; the pin's
`system-contracts/contracts/libraries/Merkle.sol` differs in layout and, unlike this copy,
rejects empty paths (this copy accepts them: `ZeroLengthPathAcceptsRoot`).

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
| RootForgeryPinned | [Specs/RootForgeryPinned.lean](Specs/RootForgeryPinned.lean) | [Properties/RootForgeryPinned.lean](Properties/RootForgeryPinned.lean) | [Proofs/RootForgeryPinned.lean](Proofs/RootForgeryPinned.lean) |

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
path, so the disjunction is not trivially true. `AcceptForcesHeightOrBreak` and
`AcceptPinsEntryAnyLengthOrBreak` (same module) repair two more of the four.

`RootForgeryPinned` (namespace `MerkleSpec.Pinned`) finishes the repair for this folder and
for `../FullMerkle/`: every result that took global pair-injectivity has a replacement with
no hash premise, mapped one-to-one in the Properties header (`RootForgery` ×9,
`RootBinding` ×3, `ProofSound` ×3, `Verifier` ×4, FullMerkle `Model` ×7,
`CachedHashInjectivity.rootOf_inj_of_h_inj_of_on`, `TreeShape.capacity_ok_root_commits`;
four map to existing `PathCollision` results).
- Two trees with equal roots agree at a committed index, or hash different pairs to the
  same value at a named level of that index's path (`RootPinsEntryOrCollision`,
  `TreeCollision`).
- Two walks of one length from the same index with equal results used the same leaf and
  the same climbed siblings, or collide at a named step (`WalkVsWalkOrCollision`,
  `WalkCollision`). From different indices no collision is needed
  (`WalkVsWalkNeedsSameIndex`).
- Without the equal-length premise, equal roots give equal lists, a `PaddingHit` (the
  longer list holds the padding constant at the shorter one's length), or a located
  collision (`RootCommitsListOrBreak`).

Each property has a `…Satisfiable` witness; where the conclusion is "sides equal, or a
collision", a collision-free witness must have equal sides. `PinnedFormsFire`,
`RootCommitsListCollisionFires` and `PaddingHitFires` give each replacement an instance
where its original conclusion fails and the collision holds. `EqualInstancesNeverCollide`
and `RootPinsEntryPinnedToPath` show the collisions are pinned to the instance.

The tree levels and walk definitions are in `../FullMerkle/Specs/Model.lean`; capacity,
padding, and cached-hash properties are alongside that model. A pure root theorem
does not alone prove that contract storage, proof indices, and hash inputs
represent those same leaves. `../FullMerkle/` topic `CachedNodes` proves it for a
statement-by-statement transcription of the library's storage; that compiled code
executes the transcription remains obligation O7 in `../../Refinement.lean`.
