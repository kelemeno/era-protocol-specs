import EraSpec.Contracts.FullMerkle.Specs.TreeShape
import EraSpec.Contracts.Merkle.Specs.RootForgeryPinned

/-!
# Contract spec: the padding ambiguity of `FullMerkle`, within capacity and located

## Why this file exists

`AttackVectors.TreeShape.Properties.padding_ambiguity_forges_root` is meant to show that a real
leaf equal to the padding constant `z0` forges a root, and that the equal-length premise `hlen`
of root injectivity is indispensable even with the capacity premise in place.  Its statement is
only

    ∃ L₁ L₂ height, L₁.length ≠ L₂.length ∧ L₁ ≠ L₂ ∧ rootOf h z0 L₁ height = rootOf h z0 L₂ height

with no capacity bound and no link between the two lists.  It is also met by capacity overflow
with no padding involved: at height 0 the root is the head of the list, so `[a]` and `[a, a]`
share a root (attack (A) of the same file).  So it does not say what its docstring claims.

`TreeShape`'s positive results about padding are equations for an ODD-length list with ONE
appended `z0`: on level lists (`levelUp_trailing_padding`, `levels_trailing_padding`) and on the
root (`rootOf_trailing_padding`).  At the root, neither restriction is needed: an entry read with
the zero cascade as the default is the same in the tree over `L` and in the tree over `L`
followed by any number of `z0` leaves, at every level, so the two roots agree at every height for
every length of `L` (`MerkleSpec.Pinned.same_tree_of_getD_eq`).  For an even-length `L` the level-1
LIST does change (it gains the entry `h z0 z0`), but that entry is the level-1 zero, which is
exactly what the frontier would have read there anyway.

`../Properties/TreeShapeStrong.lean` states the ambiguity with both lists within capacity, the
second pinned to the first followed by padding leaves, and located: a `PaddingHit` and no
`TreeCollision` on any path, for every hash.  It also says for which lists it occurs: exactly the
lists below capacity.

## What the source does (era-contracts `c67894b9`)

`l1-contracts/contracts/common/libraries/FullMerkle.sol`: `setup(zero)` stores `zero` as
`_zeros[0]` (:29-35); `pushNewLeaf` grows `_zeros` by `efficientHash(topZero, topZero)` (:45-52);
`updateLeaf` reads an absent right sibling at level `i` as `_zeros[i]` (:82-85); `root()` is
`_nodes[_height][0]` (:99-101).  The NatSpec (:25-26) asks for a `zero` "not expected to be part
of the tree"; nothing in the library checks it.  `IndexedMerkleTree.setup` passes
`hashLeaf({0,0,0})` as `zero` and pushes the same hash as its sentinel leaf at index 0
(`IndexedMerkleTree.sol:47-50`).

## Model boundary

`rootOf h z0 L height` is the abstract fold (`Specs/Model.lean`); `CachedNodes` proves the
library's cached storage computes it.  The node hash `h` is arbitrary: nothing here depends on a
hash premise.
-/

namespace AttackVectors.TreeShapeStrong

open Clear MerkleSpec MerkleSpec.Pinned

end AttackVectors.TreeShapeStrong
