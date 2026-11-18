import EraSpec.Contracts.Merkle.Specs.PathCollision
import EraSpec.Contracts.Merkle.Specs.RootForgeryPinned

/-!
# Contract spec: `Merkle.calculateRootPaths`, the range proof

Source: era-contracts `draft/v0.35.0` head `b17415d20`,
`l1-contracts/contracts/common/libraries/Merkle.sol`; the file is identical at `main`
`70096e2ea`. Line numbers below are of that file.

    function calculateRootPaths(                                              // :79
        bytes32[] memory _startPath, bytes32[] memory _endPath,
        uint256 _startIndex, bytes32[] memory _itemHashes
    ) internal pure returns (bytes32) {
        uint256 pathLength = _startPath.length;                               // :85
        if (pathLength != _endPath.length) revert MerklePathLengthMismatch(…); // :86-88
        if (pathLength >= 256) revert MerklePathOutOfBounds();                // :89-91
        uint256 levelLen = _itemHashes.length;                                // :92
        if (pathLength == 0 && (_startIndex != 0 || levelLen != 1))
            revert MerklePathEmpty();                                         // :94-96
        if (levelLen == 0) revert MerkleNothingToProve();                     // :97-99
        if (_startIndex + levelLen > (1 << pathLength))
            revert MerkleIndexOrHeightMismatch();                             // :100-102
        bytes32[] memory itemHashes = _itemHashes;                            // :103
        for (uint256 level; level < pathLength; ++level) {                    // :105
            uint256 parity = _startIndex % 2;                                 // :106
            uint256 nextLevelLen = levelLen / 2 + (parity | (levelLen % 2));  // :109
            for (uint256 i; i < nextLevelLen; ++i) {                          // :110
                bytes32 lhs = (i == 0 && parity == 1)
                    ? _startPath[level] : itemHashes[2 * i - parity];         // :111
                bytes32 rhs = (i == nextLevelLen - 1 && (levelLen - parity) % 2 == 1)
                    ? _endPath[level] : itemHashes[2 * i + 1 - parity];       // :112-114
                itemHashes[i] = efficientHash(lhs, rhs);                      // :115
            }
            levelLen = nextLevelLen;                                          // :117
            _startIndex /= 2;                                                 // :118
        }
        return itemHashes[0];                                                 // :121
    }

`efficientHash` (`:125-131`) is `keccak256` of the two words; here it is the abstract node
hash `h : MerkleSpec.Hash`, as throughout `Merkle`/`FullMerkle`.

The only production caller is `PriorityTree.processBatch`
(`state-transition/libraries/PriorityTree.sol:83-96`), with `_startIndex` the tree's
`unprocessedIndex` (`../../PriorityTree/Specs/SegmentBinding.lean`).

**This file is definitions only.** Statements are in `../Properties/RootPaths.lean`, proofs in
`../Proofs/RootPaths.lean`.

## The transcription

* `guard` is `:85-102`: the first failing check, in source order, or `none`. The checked
  addition `_startIndex + levelLen` (`:100`) has its own case (`Revert.addOverflow`, Panic
  `0x11`); `1 << pathLength` is `2 ^ pathLength`, since `pathLength < 256` by then.
* `lhsAt`/`rhsAt` are `:111`/`:112-114`, reading the array as it stands at that point of the
  inner loop. Solidity's `?:` evaluates only the chosen branch, so the `2 * i - parity` read is
  taken only when `i ≠ 0 ∨ parity ≠ 1`, and never underflows.
* `innerStep` is one iteration of `:110-116`, writing `itemHashes[i]` **in place**, into the
  array the later iterations read from. `levelLoop` is `:105-119`.
* `rootPathsMem` returns the root (`:121`) and the final contents of the item array. The
  assignment at `:103` copies a memory pointer, so these are also the final contents of the
  caller's `_itemHashes`. `rootPaths` keeps the root.
* Indices, lengths and `_startIndex` are `ℕ`. A read is `getD _ 0` and a write `List.set`:
  they agree with Solidity's bounds-checked `bytes32[] memory` accesses only in range.
  `Properties.RootPathsReadsInBounds` proves the index arithmetic: with `n ≥ 1` items every
  index the loop computes is below `levelLen ≤ n`, and the array keeps length `n`
  (`Properties.RootPathsFrame`). The loop counters cannot overflow (`level < 256`,
  `i < levelLen`).

## Reading aids (not source)

* `stepWin`/`win`: the same loop computed level by level into fresh lists. `win … ℓ` is
  what `itemHashes[0 .. levelLen)` holds at the start of level `ℓ`
  (`Properties.RootPathsInPlaceIsLevelByLevel`).
* `rangeSib … j`: for the item at absolute index `j`, the value the computation hashes next to
  `j`'s ancestor at each level: another computed value inside the range, or `_startPath[ℓ]` /
  `_endPath[ℓ]` at the range's two ends. Walking `j`'s item up this stream with
  `MerkleSpec.walkPure` (the single-leaf `calculateRoot` loop) gives the root
  (`Properties.RootPathsIsItemWalks`), so the range proof is `n` single-leaf proofs, and the
  existing single-leaf extractors (`PathCollision`, `HeightBreak`) apply to each item.
* `honestPath`/`treeSegment`: the sibling path a tree supplies for an index, and the level-0
  entries `[s, s + n)` of a tree read with the padding default.
-/

namespace MerkleSpec.RootPaths

open Clear MerkleSpec MerkleSpec.Verifier

/-- `2^256`: one past the largest `uint256`. -/
def wordLimit : ℕ := 2 ^ 256

/-- Why `calculateRootPaths` reverts: one constructor per check of `:85-102`, in source order. -/
inductive Revert where
  /-- `MerklePathLengthMismatch` (`:86-88`): the two paths differ in length. -/
  | pathLengthMismatch
  /-- `MerklePathOutOfBounds` (`:89-91`): the paths have 256 or more entries. -/
  | pathOutOfBounds
  /-- `MerklePathEmpty` (`:94-96`): empty paths with a start index other than 0 or other than
  one item. -/
  | pathEmpty
  /-- `MerkleNothingToProve` (`:97-99`): no items. -/
  | nothingToProve
  /-- The checked addition `_startIndex + levelLen` (`:100`) overflows: Panic `0x11`. -/
  | addOverflow
  /-- `MerkleIndexOrHeightMismatch` (`:100-102`): the range does not end at or below
  `2 ^ pathLength`. -/
  | indexOrHeightMismatch
  deriving DecidableEq

/-- **The checks (`:85-102`).** The first that fails, in source order, or `none` when all
pass. Arguments: `_startPath`, `_endPath`, `_startIndex`, `_itemHashes`. -/
def guard (sp ep : List UInt256) (s : ℕ) (items : List UInt256) : Option Revert :=
  if sp.length ≠ ep.length then some .pathLengthMismatch
  else if 256 ≤ sp.length then some .pathOutOfBounds
  else if sp.length = 0 ∧ (s ≠ 0 ∨ items.length ≠ 1) then some .pathEmpty
  else if items.length = 0 then some .nothingToProve
  else if wordLimit ≤ s + items.length then some .addOverflow
  else if 2 ^ sp.length < s + items.length then some .indexOrHeightMismatch
  else none

/-- `nextLevelLen` (`:109`): `levelLen / 2 + (parity | (levelLen % 2))`. -/
def nextLen (parity levelLen : ℕ) : ℕ := levelLen / 2 + (parity ||| levelLen % 2)

/-- `lhs` (`:111`): `_startPath[level]` for the first parent when the range starts on a right
child (`parity == 1`), otherwise `itemHashes[2 * i - parity]` of the array `arr`. -/
def lhsAt (sp arr : List UInt256) (level parity i : ℕ) : UInt256 :=
  if i = 0 ∧ parity = 1 then sp.getD level 0 else arr.getD (2 * i - parity) 0

/-- `rhs` (`:112-114`): `_endPath[level]` for the last parent when the range ends on a left
child (`(levelLen - parity) % 2 == 1`), otherwise `itemHashes[2 * i + 1 - parity]` of `arr`.
`nl` is `nextLevelLen`. -/
def rhsAt (ep arr : List UInt256) (level parity levelLen nl i : ℕ) : UInt256 :=
  if i = nl - 1 ∧ (levelLen - parity) % 2 = 1 then ep.getD level 0
  else arr.getD (2 * i + 1 - parity) 0

/-- **One iteration `i` of the inner loop (`:110-116`)**: `itemHashes[i] = efficientHash(lhs,
rhs)`, with `lhs` and `rhs` read from the array as it stands, and the result written into
that same array. -/
def innerStep (h : Hash) (sp ep : List UInt256) (level parity levelLen nl : ℕ)
    (arr : List UInt256) (i : ℕ) : List UInt256 :=
  arr.set i (h (lhsAt sp arr level parity i) (rhsAt ep arr level parity levelLen nl i))

/-- **The level loop (`:105-119`)**, with `k` levels still to run, starting at `level`, with
`_startIndex = s`, `levelLen` and the item array `arr`. One level: `parity = s % 2` (`:106`),
the inner loop for `i = 0, …, nextLevelLen - 1` (`:110-116`), then `levelLen = nextLevelLen`
(`:117`) and `_startIndex /= 2` (`:118`). Returns the final item array. -/
def levelLoop (h : Hash) (sp ep : List UInt256) :
    ℕ → ℕ → ℕ → ℕ → List UInt256 → List UInt256
  | 0, _, _, _, arr => arr
  | k + 1, level, s, levelLen, arr =>
      levelLoop h sp ep k (level + 1) (s / 2) (nextLen (s % 2) levelLen)
        ((List.range (nextLen (s % 2) levelLen)).foldl
          (innerStep h sp ep level (s % 2) levelLen (nextLen (s % 2) levelLen)) arr)

/-- The loop run from level 0 on the caller's array (`:103-119`), and `itemHashes[0]`
(`:121`). -/
def runLoop (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256) :
    UInt256 × List UInt256 :=
  ((levelLoop h sp ep sp.length 0 s items.length items).getD 0 0,
    levelLoop h sp ep sp.length 0 s items.length items)

/-- **`calculateRootPaths` (`:79-122`) with the memory it leaves behind.** `none` is a revert;
otherwise the returned root and the final contents of the item array, which, through the
pointer copy at `:103`, are the final contents of the caller's `_itemHashes`. -/
def rootPathsMem (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256) :
    Option (UInt256 × List UInt256) :=
  if guard sp ep s items = none then some (runLoop h sp ep s items) else none

/-- **`calculateRootPaths(_startPath, _endPath, _startIndex, _itemHashes)`**: the returned root,
`none` on a revert. -/
def rootPaths (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256) :
    Option UInt256 :=
  (rootPathsMem h sp ep s items).map Prod.fst

/-! ## The same loop, level by level into fresh lists (a reading aid) -/

/-- One level computed into a fresh list from the level below: `v` holds the values at
absolute positions `a, a + 1, …`, and entry `i` of the result is `efficientHash(lhs, rhs)`
with both read from `v`. -/
def stepWin (h : Hash) (sp ep : List UInt256) (level a : ℕ) (v : List UInt256) :
    List UInt256 :=
  (List.range (nextLen (a % 2) v.length)).map fun i =>
    h (lhsAt sp v level (a % 2) i)
      (rhsAt ep v level (a % 2) v.length (nextLen (a % 2) v.length) i)

/-- The values at the start of level `ℓ`, computed level by level (`a = s / 2^ℓ` is
`_startIndex` there). -/
def win (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256) : ℕ → List UInt256
  | 0 => items
  | ℓ + 1 => stepWin h sp ep ℓ (s / 2 ^ ℓ) (win h sp ep s items ℓ)

/-- `levelLen` at the start of level `ℓ` (`:92`, `:117`), for start index `s` and `n` items. -/
def lenAt (s n : ℕ) : ℕ → ℕ
  | 0 => n
  | ℓ + 1 => nextLen ((s / 2 ^ ℓ) % 2) (lenAt s n ℓ)

/-- At a level whose values `v` start at absolute index `a`, the value hashed next to absolute
index `jj`: its left neighbour (for odd `jj`), which is `_startPath[level]` when `jj` is the
first position; its right neighbour (for even `jj`), which is `_endPath[level]` when `jj` is
the last position. -/
def sibAt (sp ep v : List UInt256) (level a jj : ℕ) : UInt256 :=
  if jj % 2 = 1 then (if jj = a then sp.getD level 0 else v.getD (jj - 1 - a) 0)
  else (if jj + 1 = a + v.length then ep.getD level 0 else v.getD (jj + 1 - a) 0)

/-- **The sibling stream of the item at absolute index `j`** inside the range proof: at level
`ℓ`, `sibAt` for `j`'s level-`ℓ` ancestor `j / 2^ℓ` in the level-`ℓ` values. Determined by the
call's arguments `(h, _startPath, _endPath, _startIndex, _itemHashes)` and `j`. -/
def rangeSib (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256) (j : ℕ) :
    ℕ → UInt256 :=
  fun ℓ => sibAt sp ep (win h sp ep s items ℓ) ℓ (s / 2 ^ ℓ) (j / 2 ^ ℓ)

/-! ## Honest inputs -/

/-- The sibling path of index `j` in the tree over `L` at height `H`: entry `ℓ` is
`honestSibs h z0 L j ℓ`, the level-`ℓ` neighbour of `j`'s ancestor, a padding read giving that
level's zero (`MerkleSpec.Verifier.honestSibs`). -/
def honestPath (h : Hash) (z0 : UInt256) (L : List UInt256) (j H : ℕ) : List UInt256 :=
  (List.range H).map (honestSibs h z0 L j)

/-- The level-0 entries `[s, s + n)` of the tree over `L`, read with the padding value `z0`
beyond `L`. -/
def treeSegment (z0 : UInt256) (L : List UInt256) (s n : ℕ) : List UInt256 :=
  (List.range n).map fun i => L.getD (s + i) z0

/-! ## A variant, for one source remark only -/

/-- `guard` with the `MerklePathEmpty` check (`:94-96`) deleted. -/
def guardNoEmptyCheck (sp ep : List UInt256) (s : ℕ) (items : List UInt256) : Option Revert :=
  if sp.length ≠ ep.length then some .pathLengthMismatch
  else if 256 ≤ sp.length then some .pathOutOfBounds
  else if items.length = 0 then some .nothingToProve
  else if wordLimit ≤ s + items.length then some .addOverflow
  else if 2 ^ sp.length < s + items.length then some .indexOrHeightMismatch
  else none

/-- `calculateRootPaths` with the `MerklePathEmpty` check (`:94-96`) deleted. -/
def rootPathsNoEmptyCheck (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256) :
    Option UInt256 :=
  if guardNoEmptyCheck sp ep s items = none then some (runLoop h sp ep s items).1 else none

/-! ## A toy hash, for the witnesses only

Not a model of `keccak`. It is not symmetric, so a witness built with it does not owe its
outcome to a hash that ignores order or collides everywhere. -/

/-- `3a + b + 1` modulo `2^256`. -/
def rangeToyHash : Hash := fun a b => 3 * a + b + 1

end MerkleSpec.RootPaths
