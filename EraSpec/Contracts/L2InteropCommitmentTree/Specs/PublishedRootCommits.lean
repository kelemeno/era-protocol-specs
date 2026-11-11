import EraSpec.Contracts.L2InteropCommitmentTree.Specs.RunHeight
import EraSpec.Contracts.Merkle.Specs.RootForgeryPinned

/-!
# Model: what the published root commits, at the run's own height

No new definitions.  This topic combines two existing models:

* `RunHeight` — the commitment tree's list state with `FullMerkle`'s `(_leafNumber, _height)`
  carried step for step as `IndexedMerkleTree.setup` / `insert` move them
  (`FullMerkle.sol:41-52`), and the root `IndexedMerkleTree.root()` returns, modelled as the
  fold over the leaf hashes at the state's own `_height` (`HState.root`).
* `Merkle/Specs/RootForgeryPinned` — `TreeCollision`, the collision two trees with equal
  roots exhibit on an index's path.

`FullMerkle/Properties/TreeShape.lean`'s `capacity_ok_root_commits` says the root commits the
leaf list under the capacity bound and global pair-injectivity.  The first premise holds along
every run (`RunHeight.HReachesCapacity`); the second cannot hold (`CRYPTO-PAIR-INJ`).  The
properties of this topic state the commitment at the published root with neither premise.

Model boundary: as for `RunHeight` — the stored `_nodes[_height][0]` is assumed to be the
fold (obligation O7), and `pushNewLeaf` is assumed to implement `push`.
-/

namespace Contracts.InteropCommitmentTree

end Contracts.InteropCommitmentTree
