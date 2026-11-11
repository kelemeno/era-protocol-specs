import EraSpec.Contracts.Merkle.Specs.PathCollision

/-!
# Contract spec: collisions located between two trees, two walks, or two levels

## Why this file exists

Twenty-eight results about `Merkle.sol` / `FullMerkle.sol` trees take the premise

    hinj : ∀ a b c d, h a b = h c d → a = c ∧ b = d

(`ASSUMPTIONS.md`, "Results whose premises cannot hold": FullMerkle `Model` ×7,
`CachedHashInjectivity` ×1, `TreeShape` ×1; Merkle `ProofSound` ×3, `RootBinding` ×3,
`RootForgery` ×9, `Verifier` ×4).  No `UInt256 → UInt256 → UInt256` satisfies it
(`Contracts.InteropCommitmentTree.not_nodeInj`), so all of them are vacuous.

`PathCollision` repaired the WALK-versus-TREE comparison: an accepted path opens the
tree, or the verifier hashed a pair different from the tree's, to the same value, at a
named level of the submitted path.  The remaining results make three other comparisons,
and each extracts its own located collision:

* **tree versus tree** — two leaf lists whose roots are equal (`rootOf_inj_of_h_inj`,
  `no_false_inclusion`, `mem_of_rootOf_eq`, `capacity_ok_root_commits`, …).
  `TreeCollision h z0 L₁ L₂ height i`: at a level `l < height` on index `i`'s path, the
  two trees hash DIFFERENT pairs under `i`'s level-`l` node's parent to the SAME value.
* **walk versus walk** — two walks from the same index whose results are equal
  (`walkPure_inj`, `no_path_forgery`, `single_sibling_substitution`, …).
  `WalkCollision h s₁ s₂ lvl k j x y`: at a step `i < k`, the two walks hash different
  pairs to the same value.
* **level versus level** — two equal-width levels with the same parent level
  (`levelUp_inj`, `levels_inj`).  `LevelCollision h z L₁ L₂`: under some parent `m`, the
  two levels' child pairs differ and hash equal.

and one domain case that is not a collision at all:

* `PaddingHit z0 L₁ L₂` — two lists of DIFFERENT lengths, the longer holding the padding
  constant as a real leaf at the shorter one's frontier.  This is what the equal-length
  premise of `rootOf_inj_of_h_inj` was excluding (`TreeShape.padding_ambiguity_forges_root`)
  and what `FullMerkle.setup`'s NatSpec warns about.

Every colliding pair named here is read from the instance (the two leaf lists, or the two
walks' leaves, siblings and index) at a level or step bounded by the height, so none of
these predicates follows from the mere existence of collisions (`exists_pair_collision`).
The properties file checks each is false on the honest instance for every hash, and false
on a fixed instance even under a hash for which EVERY pair collides.

## What the source does (era-contracts `c67894b9`)

`l1-contracts/contracts/common/libraries/Merkle.sol`, the copy that `FullMerkle.sol:6` and
`IndexedMerkleTree.sol:17` import and whose `calculateRootMemory` `IndexedMerkleTree`'s
`verifyInclusion` / `verifyNonInclusion` call (`IndexedMerkleTree.sol:144`, `:170`).  Line
numbers below are that file's:

    function calculateRootMemory(                                     // :53-70
        bytes32[] memory _path, uint256 _index, bytes32 _itemHash     // :54-56
    ) internal pure returns (bytes32) {
        uint256 pathLength = _path.length;
        _validatePathLengthForSingleProof(_index, pathLength);       // :59
        bytes32 currentHash = _itemHash;
        for (uint256 i; i < pathLength; ++i) {                        // :62
            currentHash = (_index % 2 == 0)
                ? efficientHash(currentHash, _path[i])                // :64
                : efficientHash(_path[i], currentHash);               // :65
            _index /= 2;                                              // :66
        }
        return currentHash;
    }
    function efficientHash(bytes32 _lhs, bytes32 _rhs) … { … keccak256(0x00, 0x40) }  // :125-131
    function _validatePathLengthForSingleProof(uint256 _index, uint256 _pathLength) … {  // :133-140
        if (_pathLength >= 256) revert MerklePathOutOfBounds();
        if (_index >= (1 << _pathLength)) revert MerkleIndexOutOfBounds();
    }

The loop's iteration `i` hashes exactly `walkPair h sibs 0 j x i` (`walkPure` is the loop,
`walkStep` one iteration), with `h = efficientHash`.

The same pin also has `system-contracts/contracts/libraries/Merkle.sol`, used there only by a
test contract.  Its loop is the same, at other lines (validate `:52`, loop `:55` written
`i = i.uncheckedInc()`, branches `:57`/`:58`, `efficientHash` `:112-118`), and its
`_validatePathLengthForSingleProof` (`:120-130`) also reverts `MerklePathEmpty` on an empty
path (`:121-123`).  The l1-contracts copy accepts an empty path at index 0 and returns the
leaf; `walkPure` with `k = 0` models that copy.

`l1-contracts/contracts/common/libraries/FullMerkle.sol`:

    function setup(FullTree storage self, bytes32 zero) internal returns (bytes32) {   // :29
        self._zeros.push(zero);  self._nodes.push([zero]);  return zero;
    }
    // "IMPORTANT: The zero value should be carefully chosen since it will be stored in the
    //  tree representing empty leaves. It should be a value that is not expected to be part
    //  of the tree."                                                                     // :25-26
    function updateLeaf(…) … {
        …  currentHash = Merkle.efficientHash(currentHash,
               maxNodeNumber == _index ? self._zeros[i] : self._nodes[i][_index + 1]);   // :82-85
        …  currentHash = Merkle.efficientHash(self._nodes[i][_index - 1], currentHash);  // :87
        …  self._nodes[i + 1][_index] = currentHash;                                     // :91
    }
    function root(FullTree storage self) … { return self._nodes[self._height][0]; }      // :99-101

So the level-`l+1` node above index `m` is `efficientHash` of the level-`l` entries `2m`,
`2m+1`, the right one read as `_zeros[l]` at the frontier.  `treePair h z0 L l j` is that
pair under the parent of entry `j` (`../Specs/PathCollision.lean`), and `levels`/`rootOf`
(`../../FullMerkle/Specs/Model.lean`) is the whole fold.

## Model boundary

* As throughout `Merkle`/`FullMerkle`: the node hash is an abstract `h`, leaves and nodes
  are `UInt256`, indices and heights are `ℕ`.  That stored `_nodes` equal the `levels`
  fold is obligation O7 in `EraSpec.Refinement`, not proved here (backlog item A1).
* A located collision is a pair of 64-byte `efficientHash` preimages with equal digest.
  Turning that into a statement about keccak (that finding one is infeasible) is
  `CRYPTO-BINDING`, outside this package.  What is proved is the extraction: every
  failure of the binding property exhibits such a pair, at a named place.
-/

namespace MerkleSpec.Pinned

open Clear MerkleSpec MerkleSpec.Verifier

/-! ## Tree versus tree -/

/-- **Two trees collide on index `i`'s path.**  At some level `l < height`, the pair the
tree over `L₁` hashes under the parent of `i`'s level-`l` node (`treePair`, the frontier
read as `_zeros[l]`) differs from the pair the tree over `L₂` hashes there, and the two
hash to the same value.  Both pairs are determined by `(h, z0, L₁, L₂, i)` and `l`. -/
def TreeCollision (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height i : ℕ) : Prop :=
  ∃ l < height, treePair h z0 L₁ l (i / 2 ^ l) ≠ treePair h z0 L₂ l (i / 2 ^ l)
    ∧ h (treePair h z0 L₁ l (i / 2 ^ l)).1 (treePair h z0 L₁ l (i / 2 ^ l)).2
      = h (treePair h z0 L₂ l (i / 2 ^ l)).1 (treePair h z0 L₂ l (i / 2 ^ l)).2

/-- **The padding constant held as a real leaf, at the shorter list's frontier.**  One
list is longer, and its entry at the other's length — a position the shorter tree pads
with `z0` (`FullMerkle.sol:84`, `_zeros[0]`) — IS `z0`.  Determined by `(z0, L₁, L₂)`. -/
def PaddingHit (z0 : UInt256) (L₁ L₂ : List UInt256) : Prop :=
  (L₁.length < L₂.length ∧ L₂.getD L₁.length z0 = z0)
    ∨ (L₂.length < L₁.length ∧ L₁.getD L₂.length z0 = z0)

/-! ## Walk versus walk -/

/-- **Two walks from the same index collide.**  At some step `i < k`, the pair the walk
from `(lvl, j)` with leaf `x` and siblings `s₁` hashes (`walkPair`, one iteration of
`calculateRootMemory`'s loop, `l1-contracts/contracts/common/libraries/Merkle.sol:62-67`)
differs from the pair the walk with leaf `y` and siblings `s₂` hashes at the same step, and
the two hash to the same value.  Both pairs are determined by `(h, s₁, s₂, lvl, j, x, y)`
and `i`. -/
def WalkCollision (h : Hash) (s₁ s₂ : ℕ → UInt256) (lvl k j : ℕ) (x y : UInt256) : Prop :=
  ∃ i < k, walkPair h s₁ lvl j x i ≠ walkPair h s₂ lvl j y i
    ∧ h (walkPair h s₁ lvl j x i).1 (walkPair h s₁ lvl j x i).2
      = h (walkPair h s₂ lvl j y i).1 (walkPair h s₂ lvl j y i).2

/-! ## Level versus level -/

/-- The pair `levelUp h z` hashes into parent `m` of the level `L`: the entries `2m` and
`2m+1`, a lone left child padded with `z` (`FullMerkle.sol:84`). -/
def parentPair (z : UInt256) (L : List UInt256) (m : ℕ) : UInt256 × UInt256 :=
  (L.getD (2 * m) z, L.getD (2 * m + 1) z)

/-- **Two levels collide under `levelUp`.**  Under some parent `m` of the level (below
its width `(L₁.length + 1) / 2`), the two levels' child pairs differ and hash equal. -/
def LevelCollision (h : Hash) (z : UInt256) (L₁ L₂ : List UInt256) : Prop :=
  ∃ m < (L₁.length + 1) / 2, parentPair z L₁ m ≠ parentPair z L₂ m
    ∧ h (parentPair z L₁ m).1 (parentPair z L₁ m).2 = h (parentPair z L₂ m).1 (parentPair z L₂ m).2

/-! ## Toy hashes and a toy sibling stream, for the witnesses only

Neither hash is a model of `keccak`.  They are deliberately weak node hashes whose
collisions can be written down, so that the witnesses can show (a) a located collision
really fires when the vacuous original's conclusion fails, and (b) a located collision can
be FALSE on an instance even under a hash that collides. -/

/-- Every pair collides: `constHash a b = 0`.  The worst case for an unpinned
"some collision exists" conclusion, which is then trivially true. -/
def constHash : Hash := fun _ _ => 0

/-- Addition modulo `2^256`.  Collides on swapped pairs (`sumHash 1 0 = sumHash 0 1`). -/
def sumHash : Hash := fun a b => a + b

/-- A sibling stream that differs from `fun _ => 0` at level 0 and agrees with it at every
other level (a one-level sibling substitution). -/
def oneAtZero : ℕ → UInt256 := fun l => if l = 0 then 1 else 0

end MerkleSpec.Pinned
