import EraSpec.Contracts.DynamicIncrementalMerkle.Specs.Model
import EraSpec.Contracts.PriorityTree.Specs.Library

/-!
# Bridge: the `PriorityTree` folder's transcription of the library is this folder's

`Contracts.PriorityTree.Library.PushTree` (`PriorityTree/Specs/Library.lean`) is a second
transcription of `DynamicIncrementalMerkle.Bytes32PushTree` and its `setup`, `push` and `root`
(`DynamicIncrementalMerkle.sol:40-44, 53-58, 93-137, 161-163` at era-contracts `draft/v0.35.0`
`b17415d20`), written for the priority tree. It differs from `Specs/Model.lean` in form only:

* its loop is a `foldl` over `List.range levels` on a record `Walk`, where `Model.pushLoop` is a
  structural recursion on the iterations left;
* it reads `1 << levels` as a `uint256` (`shl1`: `0` from 256 levels on) and reverts when
  `_nextLeafIndex++` overflows, where `Model` keeps `ℕ` and leaves both wraps out of scope;
* `root()` on empty `_sides` reads `0` where `Model.root` reverts (`none`).

`toDim` maps its storage to this folder's `PushTree` field by field. `../Properties/PriorityTreeBridge.lean`
states that, inside the `uint256` range (fewer than 256 levels, the counter below `2^256 - 1`), the
two `push`es agree on the new storage and the returned root, and that `setup` and `root` agree. So
every result of `Model` about `push` (for example `PushComputesRoot`, `RunRootIsFold`) applies to
the priority tree's `push` as transcribed in `PriorityTree`.
-/

namespace Contracts.DynamicIncrementalMerkle.PriorityTreeBridge

/-- The priority tree's `Bytes32PushTree` storage as this folder's `PushTree`. -/
def toDim (t : Contracts.PriorityTree.Library.PushTree) : PushTree :=
  ⟨t.nextLeafIndex, t.sides, t.zeros⟩

end Contracts.DynamicIncrementalMerkle.PriorityTreeBridge
