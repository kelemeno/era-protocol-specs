# FullMerkle

Source: `contracts/common/libraries/FullMerkle.sol` in the pinned era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| CachedHashInjectivity | [Specs/CachedHashInjectivity.lean](Specs/CachedHashInjectivity.lean) | [Properties/CachedHashInjectivity.lean](Properties/CachedHashInjectivity.lean) | [Proofs/CachedHashInjectivity.lean](Proofs/CachedHashInjectivity.lean) |
| CachedNodes | [Specs/CachedNodes.lean](Specs/CachedNodes.lean) | [Properties/CachedNodes.lean](Properties/CachedNodes.lean) | [Proofs/CachedNodes.lean](Proofs/CachedNodes.lean) |
| CapacityInvariant | [Specs/CapacityInvariant.lean](Specs/CapacityInvariant.lean) | [Properties/CapacityInvariant.lean](Properties/CapacityInvariant.lean) | [Proofs/CapacityInvariant.lean](Proofs/CapacityInvariant.lean) |
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| TreeShape | [Specs/TreeShape.lean](Specs/TreeShape.lean) | [Properties/TreeShape.lean](Properties/TreeShape.lean) | [Proofs/TreeShape.lean](Proofs/TreeShape.lean) |

The model is mathematical and EVM-free, but it describes FullMerkle and belongs
here. Verification soundness and root binding/forgery results live under
`../Merkle/`.

`CachedNodes` transcribes the library's storage (`_height`, `_leafNumber`, `_nodes`,
`_zeros`) and `setup`, `pushNewLeaf`, `updateLeaf`, `root`, `merklePath` statement by
statement as pure functions (a revert is `none`). For every node hash and padding:
- `setup` establishes the invariant `Represents` (`_zeros[i]` is the zero cascade,
  `_nodes[i]` is `levels i`), and both writes keep it and return the new fold
  (`SetupRepresentsEmpty`, `PushNewLeafComputesRoot`, `UpdateLeafComputesRoot`);
  `pushNewLeaf` moves `(_leafNumber, _height)` by `CapacityInvariant.push`.
- `root()` is `rootOf` (`RootIsFold`), `merklePath(i)` is the honest sibling stream
  (`MerklePathIsHonest`), and the library's own path verifies against its own root
  (`ContractPathVerifies`). Out-of-range `updateLeaf`/`merklePath` revert
  (`UpdateLeafOutOfRangeReverts`, `MerklePathOutOfRangeReverts`).
- Every storage reachable from `setup` represents its leaves (`ReachableRepresents`,
  `ReachableRootIsFold`, `CallsReturnTheStoredRoot`). Witness: `ThreePushesWitness`.

No hash premise. Not covered: that compiled code executes the transcription; the
`uint256` wrap of `1 << _height` and `_leafNumber++` (more than 2^255 leaves); a second
`setup` on storage that is not fresh (the library has no guard; the commitment tree's
`IndexedMerkleTree.setup` supplies one); real leaf/padding domain separation. The lift to
the commitment tree is `../L2InteropCommitmentTree/` topic `CachedRoot`.

The `global-hinj` results of `Model`, `CachedHashInjectivity` and `TreeShape` are vacuous
(`ASSUMPTIONS.md`). Their pinned replacements, with no hash premise, are in
`../Merkle/Properties/RootForgeryPinned.lean`. `capacity_ok_root_commits` at the
commitment tree's own height is `../L2InteropCommitmentTree/` topic `PublishedRootCommits`.

Source findings, reported to the maintainer of this repo, not yet confirmed upstream:
- `merklePath` refuses empty slots (`FullMerkle.sol:111-114`), but `Merkle.calculateRoot`
  checks only `index < 2^pathLength` (`Merkle.sol:133-140`). With the commitment tree's
  padding `hashLeaf({0,0,0})` (`IndexedMerkleTree.sol:47-48`), the honest siblings of an
  empty slot are an accepted non-inclusion proof against the stored root
  (`Contracts.InteropCommitmentTree.CThreeLeafWitness`). This is the known padding
  forgery (`PaddingCollisionRefundsDeliveredLeg`); both verifiers classified it as a bug,
  high severity.
- NatSpec (both verifiers: documentation wrong, informational): `FullMerkle.sol:23` says
  capacity is set to `2**levels`, but `setup` (:29) takes no `levels` and `pushNewLeaf`
  grows `_height` (:45-52); the comment at :30 ("Store depth") matches no code at :31-32.
