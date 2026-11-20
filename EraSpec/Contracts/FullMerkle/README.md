# FullMerkle

Source: `l1-contracts/contracts/common/libraries/FullMerkle.sol` at era-contracts `draft/v0.35.0`
`b17415d20`. The tree is the abstract fold `levels`/`rootOf` (`Specs/Model.lean`); topic `CachedNodes`
transcribes the library's storage and functions statement by statement and proves they compute that
fold. Verification soundness and root binding are in `../Merkle/`.

## Headline guarantees

All three are about the transcription (`MODEL-FULLMERKLE` in `ASSUMPTIONS.md`): any node hash
(`Merkle.efficientHash`) and zero value, no hash premise. Scope: fewer than `2^255` leaves (the
`uint256` wraps of `1 << _height` and `_leafNumber++` are not modelled); that compiled code executes
the transcription is not proved.

- `Contracts.FullMerkle.Properties.ReachableRootIsFold`: on every storage reached from fresh storage
  by `setup(z0)` and successful `pushNewLeaf`/`updateLeaf` calls, `root()` is the fold of the leaves
  it holds at its `_height`. Premises: the storage is reached that way (a second `setup` on used
  storage is not).
- `Contracts.FullMerkle.Properties.ContractPathVerifies`: for an occupied index, `merklePath(i)` is a
  path of length `_height` with `i < 2^length`, and walking it from leaf `i` gives `root()`.
  Premises: the storage represents its leaves (every reachable one does, `ReachableRepresents`); the
  index is occupied.
- `Contracts.FullMerkle.Properties.MerklePathOutOfRangeReverts`: `merklePath(i)` reverts for every
  index at or above `_leafNumber`. Premises: none (any storage).

## Topics

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| CachedNodes | [Specs/CachedNodes.lean](Specs/CachedNodes.lean) | [Properties/CachedNodes.lean](Properties/CachedNodes.lean) | [Proofs/CachedNodes.lean](Proofs/CachedNodes.lean) |
| CapacityInvariant | [Specs/CapacityInvariant.lean](Specs/CapacityInvariant.lean) | [Properties/CapacityInvariant.lean](Properties/CapacityInvariant.lean) | [Proofs/CapacityInvariant.lean](Proofs/CapacityInvariant.lean) |
| TreeShape | [Specs/TreeShape.lean](Specs/TreeShape.lean) | [Properties/TreeShape.lean](Properties/TreeShape.lean) | [Proofs/TreeShape.lean](Proofs/TreeShape.lean) |
| TreeShapeStrong | [Specs/TreeShapeStrong.lean](Specs/TreeShapeStrong.lean) | [Properties/TreeShapeStrong.lean](Properties/TreeShapeStrong.lean) | [Proofs/TreeShapeStrong.lean](Proofs/TreeShapeStrong.lean) |
| CachedHashInjectivity | [Specs/CachedHashInjectivity.lean](Specs/CachedHashInjectivity.lean) | [Properties/CachedHashInjectivity.lean](Properties/CachedHashInjectivity.lean) | [Proofs/CachedHashInjectivity.lean](Proofs/CachedHashInjectivity.lean) |

- **Model.** The fold, the update walk and the append walk, with the frontier arithmetic.
- **CachedNodes.** `setup` establishes the invariant `Represents` (`_zeros[i]` is the zero cascade,
  `_nodes[i]` is `levels i`); `pushNewLeaf` and `updateLeaf` keep it and return the new fold, and
  `pushNewLeaf` moves `(_leafNumber, _height)` by `CapacityInvariant.push`; `root()` is the fold,
  `merklePath(i)` the honest sibling stream, and out-of-range `updateLeaf`/`merklePath` revert.
  Witness: `ThreePushesWitness`. The lift to the commitment tree is `../L2InteropCommitmentTree/`
  topic `CachedRoot`; `MessageRoot` imports it for the shared tree.
- **CapacityInvariant, TreeShape(Strong).** The growth rule keeps `leafCount ≤ 2^height`; without
  it, or with the padding constant as a real leaf, equal roots do not commit the leaves
  (`capacity_overflow_forges_root`, the padding results; TreeShapeStrong pins the padding case to
  padding extensions).
- The `global-hinj` results of Model, CachedHashInjectivity and TreeShape are vacuous
  (`ASSUMPTIONS.md`); their replacements with no hash premise are in
  `../Merkle/Properties/RootForgeryPinned.lean`.

The library's zero value is its padding, and nothing in it checks the NatSpec request (:25-26) that it
not be a possible leaf. At `b17415d20` the commitment tree pads with the dedicated
`IMT_EMPTY_LEAF_HASH`; the interop pin `c67894b9`'s padding `hashLeaf({0,0,0})` was a leaf hash, the H2
finding, recorded in `../IndexedMerkleTree/History/` and `../L2InteropCommitmentTree/` (History).
NatSpec note (documentation only): `FullMerkle.sol:23` says capacity is set to `2**levels`, but
`setup` (:29) takes no `levels` and `pushNewLeaf` grows `_height` (:45-52).
