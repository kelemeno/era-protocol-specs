import EraSpec.Contracts.Merkle.Specs.RootPaths

/-!
# Properties: `Merkle.calculateRootPaths` is complete, sound up to a located break, and in place

Statements about `../Specs/RootPaths.lean`, the transcription of `calculateRootPaths`
(`l1-contracts/contracts/common/libraries/Merkle.sol:79-122` at `b17415d20`). Proofs:
`../Proofs/RootPaths.lean`. No statement takes a hash premise: the general ones hold for every
node hash `h` (and, where a tree appears, every padding value `z0` and leaf list `L`); the
witnesses are concrete instances under the toy hashes `rangeToyHash` and `sumHash`.

* **Checks.** `RootPathsAcceptIff` (the exact set of accepted arguments),
  `RootPathsEmptyPathIsTheItem`, `RootPathsEmptyCheckOnlyChangesReason`.
* **In place.** `RootPathsReadsInBounds`, `RootPathsInPlaceIsLevelByLevel`, `RootPathsFrame`.
* **Completeness.** `RootPathsComplete`.
* **A range proof is one walk per item.** `RootPathsIsItemWalks`,
  `RootPathsWalkPairsAreLoopPairs`.
* **Soundness.** `RootPathsSoundOrCollision` (paths of the tree's height),
  `RootPathsSiblingsPinnedOrCollision`, `RootPathsAnyLengthOrBreak` (any path length). The breaks are the existing single-leaf
  extractors `MerkleSpec.Verifier.PathCollision` and `MerkleSpec.Verifier.HeightBreak`, applied
  to one item's walk (`rangeSib`), so each is determined by the call's arguments, the tree, and
  the item.
* **Non-triviality and witnesses.** `RootPathsHonestNoBreak`, `RootPathsHonestWitness`,
  `RootPathsCollisionFires`, `RootPathsWrongLengthFires`, `RootPathsClobbersItems`.
-/

namespace MerkleSpec.RootPaths

open Clear MerkleSpec MerkleSpec.Verifier MerkleSpec.Pinned

/-! ## The checks -/

/-- **(d) THE EXACT SET OF ACCEPTED ARGUMENTS.** The call returns (does not revert) exactly
when the two paths have the same length `P < 256`, there is at least one item, and the range
`[s, s + n)` ends at or below `2 ^ P`. -/
def Properties.RootPathsAcceptIff : Prop :=
  ∀ (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256),
    rootPaths h sp ep s items ≠ none ↔
      (sp.length = ep.length ∧ sp.length < 256 ∧ 0 < items.length
        ∧ s + items.length ≤ 2 ^ sp.length)

/-- **(d) THE EMPTY PATH.** An accepted call with an empty start path has an empty end path,
start index 0 and one item, and returns that item; and every such call is accepted. -/
def Properties.RootPathsEmptyPathIsTheItem : Prop :=
  (∀ (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256) (r : UInt256),
      rootPaths h sp ep s items = some r → sp = [] →
        ep = [] ∧ s = 0 ∧ items.length = 1 ∧ r = items.getD 0 0)
  ∧ ∀ (h : Hash) (x : UInt256), rootPaths h [] [] 0 [x] = some x

/-- **THE `MerklePathEmpty` CHECK (`:94-96`) CHANGES ONLY THE REVERT REASON.** Deleting it
leaves the result of every call unchanged: the checks `:97-102` already reject every input it
rejects. It does change which error a rejected call reverts with:
`MerklePathEmpty` instead of `MerkleIndexOrHeightMismatch` for one item at index 1, instead of
`MerkleNothingToProve` for no items. -/
def Properties.RootPathsEmptyCheckOnlyChangesReason : Prop :=
  (∀ (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256),
      rootPathsNoEmptyCheck h sp ep s items = rootPaths h sp ep s items)
  ∧ guard [] [] 1 [7] = some .pathEmpty
  ∧ guardNoEmptyCheck [] [] 1 [7] = some .indexOrHeightMismatch
  ∧ guard [] [] 0 [] = some .pathEmpty
  ∧ guardNoEmptyCheck [] [] 0 [] = some .nothingToProve

/-! ## In place -/

/-- **EVERY INDEX THE LOOP USES IS IN RANGE, AND NOTHING UNDERFLOWS.** For `n ≥ 1` items and
any start index `s`, at every level `ℓ` the level length `lenAt s n ℓ` (the `levelLen`
recursion of `:92`, `:109`, `:117`) is between
1 and `n`, `nextLevelLen` is at least 1, and for every iteration `i < nextLevelLen`: the write
index `i` is below
`levelLen`; the `lhs` read index `2 * i - parity`, when that read is taken, is below
`levelLen` and `2 * i ≥ parity`; the `rhs` read index `2 * i + 1 - parity`, when taken, is
below `levelLen`. So `levelLen - parity` and `nextLevelLen - 1` do not underflow either. The item array keeps its length `n` (`RootPathsFrame`), so these indices are
inside it: this is the arithmetic by which the transcription's `getD _ 0` reads and `List.set`
writes agree with Solidity's bounds-checked memory accesses. (`_startPath[level]` and
`_endPath[level]` are read for `level < pathLength`, the length of both paths after `:86-88`;
that is the loop bound, not part of this statement.) -/
def Properties.RootPathsReadsInBounds : Prop :=
  ∀ (s n ℓ : ℕ), 1 ≤ n →
    1 ≤ lenAt s n ℓ ∧ lenAt s n ℓ ≤ n ∧ 1 ≤ nextLen ((s / 2 ^ ℓ) % 2) (lenAt s n ℓ)
    ∧ ∀ i, i < nextLen ((s / 2 ^ ℓ) % 2) (lenAt s n ℓ) →
      i < lenAt s n ℓ
      ∧ (¬ (i = 0 ∧ (s / 2 ^ ℓ) % 2 = 1) →
          (s / 2 ^ ℓ) % 2 ≤ 2 * i ∧ 2 * i - (s / 2 ^ ℓ) % 2 < lenAt s n ℓ)
      ∧ (¬ (i = nextLen ((s / 2 ^ ℓ) % 2) (lenAt s n ℓ) - 1
              ∧ (lenAt s n ℓ - (s / 2 ^ ℓ) % 2) % 2 = 1) →
          2 * i + 1 - (s / 2 ^ ℓ) % 2 < lenAt s n ℓ)

/-- **IN PLACE IS THE SAME AS LEVEL BY LEVEL.** On every accepted call: after the first `ℓ`
levels of the in-place loop (`levelLoop … ℓ 0 …`, from the caller's array) the array has
`n` entries and its first `levelLen` entries are the level-`ℓ` values of the level-by-level
computation (`win`, each level a fresh list read only from the level below); `win … ℓ` has
`levelLen` (`lenAt`) entries; at the top it has exactly one; and the call returns it. -/
def Properties.RootPathsInPlaceIsLevelByLevel : Prop :=
  ∀ (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256),
    guard sp ep s items = none →
      (∀ ℓ, (levelLoop h sp ep ℓ 0 s items.length items).length = items.length
        ∧ ∀ j, j < (win h sp ep s items ℓ).length →
          (levelLoop h sp ep ℓ 0 s items.length items).getD j 0 = (win h sp ep s items ℓ).getD j 0)
      ∧ (∀ ℓ, (win h sp ep s items ℓ).length = lenAt s items.length ℓ)
      ∧ (win h sp ep s items sp.length).length = 1
      ∧ rootPaths h sp ep s items = some ((win h sp ep s items sp.length).getD 0 0)

/-- **(e) WHAT THE CALL LEAVES IN THE CALLER'S ARRAY.** On an accepted call returning `r` with
final item-array contents `mem`: the array keeps its length; its entry 0 is `r`; with empty
paths nothing is written; otherwise every entry at or after the first level's
`nextLevelLen` keeps its value (each level writes only below its `nextLevelLen`, and the
lengths only shrink). Entries below it are overwritten in general (`RootPathsClobbersItems`). -/
def Properties.RootPathsFrame : Prop :=
  ∀ (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256) (r : UInt256)
    (mem : List UInt256),
    rootPathsMem h sp ep s items = some (r, mem) →
      mem.length = items.length ∧ mem.getD 0 0 = r
      ∧ (sp = [] → mem = items)
      ∧ (sp ≠ [] → ∀ j, nextLen (s % 2) items.length ≤ j → mem.getD j 0 = items.getD j 0)

/-! ## Completeness -/

/-- **(a) COMPLETENESS.** For any leaf list `L`, padding `z0` and height `H < 256`, and any
nonempty range `[s, s + n)` ending at or below `2 ^ H`: the tree's sibling paths of the range's
first and last indices, with the tree's level-0 entries of the range as items (the padding
`z0` beyond `L`), are accepted, and the call returns the tree's root `rootOf h z0 L H`. -/
def Properties.RootPathsComplete : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (H s n : ℕ),
    1 ≤ n → s + n ≤ 2 ^ H → H < 256 →
      rootPaths h (honestPath h z0 L s H) (honestPath h z0 L (s + n - 1) H) s (treeSegment z0 L s n)
        = some (rootOf h z0 L H)

/-! ## A range proof is one walk per item -/

/-- **EACH ITEM'S OWN WALK REACHES THE RETURNED ROOT.** If the call returns `r`, then for every
item `i`: its absolute index `s + i` is below `2 ^ pathLength`, and walking the item up the
stream `rangeSib … (s + i)` for `pathLength` levels (the single-leaf loop of
`calculateRoot`, `Merkle.sol:36-41`, as `MerkleSpec.walkPure`) gives `r`. -/
def Properties.RootPathsIsItemWalks : Prop :=
  ∀ (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256) (r : UInt256),
    rootPaths h sp ep s items = some r →
      ∀ i, i < items.length →
        s + i < 2 ^ sp.length
        ∧ walkPure h (rangeSib h sp ep s items (s + i)) 0 sp.length (s + i) (items.getD i 0) = r

/-- **THE WALK HASHES THE LOOP'S OWN PAIRS.** On an accepted call, the pair item `i`'s walk
hashes at level `ℓ < pathLength` (`walkPair`) is the pair `(lhs, rhs)` that `lhsAt`/`rhsAt`
(`:111-114`) compute for iteration `m` of level `ℓ` from that level's values `win … ℓ`, with
`m` the index of the item's level-`(ℓ+1)` ancestor relative to the level's start; and
`m < nextLevelLen`, so the loop runs that iteration. With `RootPathsInPlaceIsLevelByLevel`
(the in-place array holds `win … ℓ` below `levelLen`), a `PathCollision` located on an item's
walk compares a pair the loop hashes at `:115` with the tree's pair. -/
def Properties.RootPathsWalkPairsAreLoopPairs : Prop :=
  ∀ (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256) (r : UInt256),
    rootPaths h sp ep s items = some r →
      ∀ i ℓ, i < items.length → ℓ < sp.length →
        (s + i) / 2 ^ (ℓ + 1) - s / 2 ^ (ℓ + 1)
            < nextLen ((s / 2 ^ ℓ) % 2) (win h sp ep s items ℓ).length
        ∧ walkPair h (rangeSib h sp ep s items (s + i)) 0 (s + i) (items.getD i 0) ℓ
          = (lhsAt sp (win h sp ep s items ℓ) ℓ ((s / 2 ^ ℓ) % 2)
                ((s + i) / 2 ^ (ℓ + 1) - s / 2 ^ (ℓ + 1)),
             rhsAt ep (win h sp ep s items ℓ) ℓ ((s / 2 ^ ℓ) % 2)
                (win h sp ep s items ℓ).length
                (nextLen ((s / 2 ^ ℓ) % 2) (win h sp ep s items ℓ).length)
                ((s + i) / 2 ^ (ℓ + 1) - s / 2 ^ (ℓ + 1)))

/-! ## Soundness -/

/-- **(b) SOUNDNESS AT THE TREE'S HEIGHT, OR A LOCATED COLLISION.** If the call returns the root
of the tree over `L` at height `pathLength`, then the items are the tree's level-0 entries
`[s, s + n)` (the padding `z0` at indices `≥ L.length`), or for some item `i` its walk
(`RootPathsIsItemWalks`) exhibits a `PathCollision`: at a named level the loop hashed a pair
different from the tree's pair at that position (`RootPathsWalkPairsAreLoopPairs`), with the
same hash. No hash premise. -/
def Properties.RootPathsSoundOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sp ep : List UInt256) (s : ℕ)
    (items : List UInt256),
    rootPaths h sp ep s items = some (rootOf h z0 L sp.length) →
      items = treeSegment z0 L s items.length
      ∨ ∃ i, i < items.length ∧
          PathCollision h z0 L (rangeSib h sp ep s items (s + i)) 0 sp.length (s + i)
            (items.getD i 0)

/-- **THE SIBLINGS EACH ITEM'S WALK USED ARE THE TREE'S, OR A LOCATED COLLISION.** Under the
premise of `RootPathsSoundOrCollision`, for every item `i`: at every level below the path length
the stream `rangeSib … (s + i)` holds the tree's sibling of the item's ancestor, or the item's
walk exhibits a `PathCollision`. At the levels where the range starts on a right child (resp.
ends on a left child), the stream of the first (resp. last) item reads `_startPath[ℓ]` (resp.
`_endPath[ℓ]`) (`sibAt`), so the path entries the loop reads are pinned the same way. -/
def Properties.RootPathsSiblingsPinnedOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sp ep : List UInt256) (s : ℕ)
    (items : List UInt256),
    rootPaths h sp ep s items = some (rootOf h z0 L sp.length) →
      ∀ i, i < items.length →
        (∀ ℓ, ℓ < sp.length → rangeSib h sp ep s items (s + i) ℓ
            = (levels h z0 L ℓ).getD (sibIdx ((s + i) / 2 ^ ℓ)) (zeros h z0 ℓ))
        ∨ PathCollision h z0 L (rangeSib h sp ep s items (s + i)) 0 sp.length (s + i)
            (items.getD i 0)

/-- **(c) ANY PATH LENGTH: SOUND, OR A LOCATED COLLISION, OR A LOCATED `HeightBreak`.**
`calculateRootPaths` does not know the tree's height (`processBatch` does not check it), so the
path length `pathLength` may differ from the height `H` of the tree whose root is returned.
Then: the length is `H` and the items are the tree's entries `[s, s + n)`; or the length is `H`
and some item's walk exhibits a `PathCollision`; or the length is not `H` and every item's
walk exhibits a `HeightBreak` (`MerkleSpec.Verifier.HeightBreak`: an interior node presented
as the item, a level-0 entry that is the node hash of the walk's own pair, or a collision on
the re-anchored or split walk). This mirrors `AcceptPinsEntryAnyLengthOrBreak`. -/
def Properties.RootPathsAnyLengthOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ) (sp ep : List UInt256) (s : ℕ)
    (items : List UInt256),
    rootPaths h sp ep s items = some (rootOf h z0 L H) →
      (sp.length = H ∧ items = treeSegment z0 L s items.length)
      ∨ (sp.length = H ∧ ∃ i, i < items.length ∧
          PathCollision h z0 L (rangeSib h sp ep s items (s + i)) 0 sp.length (s + i)
            (items.getD i 0))
      ∨ (sp.length ≠ H ∧ ∀ i, i < items.length →
          HeightBreak h z0 L (rangeSib h sp ep s items (s + i)) sp.length H (s + i)
            (items.getD i 0))

/-! ## Non-triviality and witnesses -/

/-- **ON AN HONEST PROOF NO BREAK IS LOCATED, FOR EVERY HASH.** Under the premises of
`RootPathsComplete`, no item's walk exhibits a `PathCollision` or a `HeightBreak` against the
tree the proof was taken from. So the break disjuncts of `RootPathsSoundOrCollision` and
`RootPathsAnyLengthOrBreak` are not tautologies. -/
def Properties.RootPathsHonestNoBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (H s n : ℕ),
    1 ≤ n → s + n ≤ 2 ^ H → H < 256 →
      ∀ i, i < n →
        ¬ PathCollision h z0 L
            (rangeSib h (honestPath h z0 L s H) (honestPath h z0 L (s + n - 1) H) s
              (treeSegment z0 L s n) (s + i)) 0 H (s + i) ((treeSegment z0 L s n).getD i 0)
        ∧ ¬ HeightBreak h z0 L
            (rangeSib h (honestPath h z0 L s H) (honestPath h z0 L (s + n - 1) H) s
              (treeSegment z0 L s n) (s + i)) H H (s + i) ((treeSegment z0 L s n).getD i 0)

/-- **A CONCRETE HONEST PROOF.** Tree `[10, 20]` with padding `7` at height 2 under
`rangeToyHash`, range `[1, 3)`: it starts on a right child and ends on a left child at level
0 (so the loop reads both paths there) and its last index is a padded slot (`L.length = 2`).
The premises of `RootPathsComplete` and `RootPathsHonestNoBreak` hold (`n = 2`, `1 + 2 ≤ 2^2`,
`2 < 256`). The call passes the checks (the premise of `RootPathsInPlaceIsLevelByLevel`),
returns the tree's root, which is `183` (the premises of `RootPathsIsItemWalks`,
`RootPathsWalkPairsAreLoopPairs`, `RootPathsSoundOrCollision`,
`RootPathsSiblingsPinnedOrCollision` and `RootPathsAnyLengthOrBreak`, with `H = 2` the path
length), the items are `[20, 7]`, and no item's walk exhibits a
`PathCollision`. (`n = 2` also meets the premise `1 ≤ n` of `RootPathsReadsInBounds`.) -/
def Properties.RootPathsHonestWitness : Prop :=
  1 ≤ 2 ∧ 1 + 2 ≤ 2 ^ 2 ∧ 2 < 256
    ∧ 1 % 2 = 1 ∧ (1 + 2 - 1) % 2 = 0 ∧ ([10, 20] : List UInt256).length < 1 + 2
    ∧ guard (honestPath rangeToyHash 7 [10, 20] 1 2) (honestPath rangeToyHash 7 [10, 20] 2 2) 1
        (treeSegment 7 [10, 20] 1 2) = none
    ∧ rootPaths rangeToyHash (honestPath rangeToyHash 7 [10, 20] 1 2)
        (honestPath rangeToyHash 7 [10, 20] 2 2) 1 (treeSegment 7 [10, 20] 1 2)
        = some (rootOf rangeToyHash 7 [10, 20] (honestPath rangeToyHash 7 [10, 20] 1 2).length)
    ∧ (honestPath rangeToyHash 7 [10, 20] 1 2).length = 2
    ∧ rootOf rangeToyHash 7 [10, 20] 2 = 183
    ∧ treeSegment 7 [10, 20] 1 2 = [20, 7]
    ∧ ∀ i, i < 2 → ¬ PathCollision rangeToyHash 7 [10, 20]
        (rangeSib rangeToyHash (honestPath rangeToyHash 7 [10, 20] 1 2)
          (honestPath rangeToyHash 7 [10, 20] 2 2) 1 (treeSegment 7 [10, 20] 1 2) (1 + i))
        0 2 (1 + i) ((treeSegment 7 [10, 20] 1 2).getD i 0)

/-- **A REORDERED RANGE IS ACCEPTED UNDER AN ORDER-BLIND HASH, AND IS LOCATED.** Under
`sumHash` (`a + b`, which ignores order), the items `[2, 1]` at index 0, with the honest paths
of the tree `[1, 2, 3, 4]` at height 2, return that tree's root, though the tree's entries
`[0, 2)` are `[1, 2]`. `RootPathsSoundOrCollision` locates it as a `PathCollision` on item 0's
walk: at level 0 that walk hashes `(2, 1)`, where the tree hashes `(1, 2)`. -/
def Properties.RootPathsCollisionFires : Prop :=
  rootPaths sumHash (honestPath sumHash 0 [1, 2, 3, 4] 0 2) (honestPath sumHash 0 [1, 2, 3, 4] 1 2)
      0 [2, 1] = some (rootOf sumHash 0 [1, 2, 3, 4] 2)
    ∧ ([2, 1] : List UInt256) ≠ treeSegment 0 [1, 2, 3, 4] 0 2
    ∧ PathCollision sumHash 0 [1, 2, 3, 4]
        (rangeSib sumHash (honestPath sumHash 0 [1, 2, 3, 4] 0 2)
          (honestPath sumHash 0 [1, 2, 3, 4] 1 2) 0 [2, 1] (0 + 0))
        0 2 (0 + 0) (([2, 1] : List UInt256).getD 0 0)
    ∧ walkPair sumHash
        (rangeSib sumHash (honestPath sumHash 0 [1, 2, 3, 4] 0 2)
          (honestPath sumHash 0 [1, 2, 3, 4] 1 2) 0 [2, 1] (0 + 0))
        0 (0 + 0) (([2, 1] : List UInt256).getD 0 0) 0 = (2, 1)
    ∧ treePair sumHash 0 [1, 2, 3, 4] 0 (0 + 0) = (1, 2)

/-- **WRONG PATH LENGTHS ARE ACCEPTED, AND ARE LOCATED.** Under `rangeToyHash`:
* too short: with empty paths, the single item `rootOf … [3, 4] 1` (the root of a height-1
  tree) is accepted and returns that root; the path length 0 is not 1, a `HeightBreak` holds,
  and the item is the node hash of the tree's top pair `(3, 4)` (its case `shortInteriorLeaf`);
* too long: with one-entry paths, the item `3` at index 0 returns `rangeToyHash 3 4`, the root
  of the height-0 tree whose only leaf is `rangeToyHash 3 4`; the path length 1 is not 0, a
  `HeightBreak` holds, and that leaf is the node hash of the walk's own pair `(3, 4)` (its case
  `longEntryIsNode`). -/
def Properties.RootPathsWrongLengthFires : Prop :=
  (rootPaths rangeToyHash [] [] 0 [rootOf rangeToyHash 7 [3, 4] 1]
        = some (rootOf rangeToyHash 7 [3, 4] 1)
    ∧ ([] : List UInt256).length ≠ 1
    ∧ HeightBreak rangeToyHash 7 [3, 4]
        (rangeSib rangeToyHash [] [] 0 [rootOf rangeToyHash 7 [3, 4] 1] (0 + 0)) 0 1 (0 + 0)
        (([rootOf rangeToyHash 7 [3, 4] 1] : List UInt256).getD 0 0)
    ∧ treePair rangeToyHash 7 [3, 4] 0 0 = (3, 4)
    ∧ rootOf rangeToyHash 7 [3, 4] 1 = rangeToyHash 3 4)
  ∧ (rootPaths rangeToyHash [9] [4] 0 [3] = some (rootOf rangeToyHash 7 [rangeToyHash 3 4] 0)
    ∧ ([9] : List UInt256).length ≠ 0
    ∧ HeightBreak rangeToyHash 7 [rangeToyHash 3 4] (rangeSib rangeToyHash [9] [4] 0 [3] (0 + 0))
        1 0 (0 + 0) (([3] : List UInt256).getD 0 0)
    ∧ walkPair rangeToyHash (rangeSib rangeToyHash [9] [4] 0 [3] (0 + 0)) 0 (0 + 0) 3 0 = (3, 4))

/-- **THE CALL OVERWRITES THE CALLER'S ITEMS.** Under `rangeToyHash`, items `[1, 2]` at index
0 with one-entry paths: the call returns `6` and leaves `[6, 2]` in the caller's array, which
is not `[1, 2]`. This meets the premise of `RootPathsFrame` with nonempty paths, and the first
level's `nextLevelLen` is 1: entry 0 changed, entry 1 did not. -/
def Properties.RootPathsClobbersItems : Prop :=
  rootPathsMem rangeToyHash [0] [0] 0 [1, 2] = some (6, [6, 2])
    ∧ ([6, 2] : List UInt256) ≠ [1, 2]
    ∧ nextLen (0 % 2) ([1, 2] : List UInt256).length = 1

end MerkleSpec.RootPaths
