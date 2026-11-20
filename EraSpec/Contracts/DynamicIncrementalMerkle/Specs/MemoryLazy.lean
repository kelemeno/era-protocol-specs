import EraSpec.Contracts.DynamicIncrementalMerkle.Specs.Model

/-!
# Model: `DynamicIncrementalMerkleMemory` and its lazy push

`DynamicIncrementalMerkleMemory` is the `memory` copy of the storage library (`Specs/Model.lean`):
its arrays are allocated once by `createTree(depth)` and their logical lengths are kept in two
counters.  It adds a **lazy push**, which returns right after the first saved side without
writing the root slot and sets `_needsRootRecalculation`, and `_recalculateRoot`, which `root()`
runs when that flag is set.  Its only caller at `b17415d20` is
`L2MessageRoot.getEmptyMultichainBatchRoot` (L2MessageRoot.sol:79-91), which runs
`createTree(1)` and `setup` and uses the value `setup` returns.

Source: `l1-contracts/contracts/common/libraries/DynamicIncrementalMerkleMemory.sol` at
era-contracts `draft/v0.35.0` `b17415d20` (identical at `d9f6789`).  It was first transcribed at
the interop pin `c67894b9`, where it is unchanged on `main` (`70096e2`): there `push` is declared
on one line and `push`/`pushLazy` name their returned index `index`, so every line from :150 on is
3 lines earlier; the code is otherwise the same.  `getEmptyMultichainBatchRoot` is
`L2MessageRoot.sol:79-91` at `b17415d20`.

    struct Bytes32PushTree { uint256 _nextLeafIndex; bytes32[] _sides; bytes32[] _zeros;
        uint256 _sidesLengthMemory; uint256 _zerosLengthMemory; bool _needsRootRecalculation;
        bytes32 _lastLeafValue; }

* `createTree(_treeDepth)` (:50-56) allocates `_sides` and `_zeros` as zero arrays of length
  `_treeDepth`, zeroes both logical lengths and clears the flag.  `_nextLeafIndex` and
  `_lastLeafValue` are not touched.
* `setup(zero)` (:65-73): `_nextLeafIndex = 0; _zeros[0] = zero; _zerosLengthMemory = 1;
  _sides[0] = bytes32(0); _sidesLengthMemory = 1; _lastLeafValue = bytes32(0); return bytes32(0);`.
* `_pushInner(leaf, isLazy)` (:79-140) is the storage `push` on the logical prefixes, plus
  `_lastLeafValue = leaf` (:92).  Growth writes at the logical lengths (:98-101).  In the loop, at
  the first left turn (`isLeft && !updatedSides`, :114) it saves the side and, **if lazy**, sets
  `_needsRootRecalculation = true` and returns `(leafIndex, bytes32(0))` at once (:117-122).
  Otherwise it ends with `_sides[levels] = currentLevelHash; _needsRootRecalculation = false;`
  (:137-138).  `push` (:149-154) is the eager call, `pushLazy` (:164-166) the lazy one.
* `_recalculateRoot()` (:194-223): `0` when empty; otherwise it walks from the last leaf
  `_nextLeafIndex - 1`, starting from `_sides[0]` if that index is even and from `_lastLeafValue`
  if odd, hashing with `_sides[i]` at a right child and `_zeros[i]` at a left one.
* `root()` (:228-237): if the flag is set, recalculate, store the result in the root slot and
  clear the flag; return the root slot.  It writes to the memory struct.
* `height()` (:242-244): `_sidesLengthMemory - 1`.

Not modelled: `extendUntilEnd()` (:172-188) and `index()` (:249-251).  No contract at `b17415d20` (or at the
interop pin) calls either.

## How the transcription treats the language

* **Memory accesses are checked.**  `a[i]` reads and writes revert (Panic 0x32) at
  `i ≥ a.length`, so they are `xs[i]?` and `mset`, and a revert is `none`.  The checked
  subtractions `_zerosLengthMemory - 1` and `_sidesLengthMemory - 1` revert at `0`.
* A struct declared `memory` without initializer has every word zero and every array empty
  (`MemPushTree.fresh`).
* The library's functions are `internal`, so the struct is passed by reference and the callee's
  writes are the caller's: each function returns the updated struct.
* Everything else is as in `Specs/Model.lean`: `bytes32` is `UInt256`, `efficientHash` is the
  abstract `h`, indices are `ℕ`, uint256 wrap is out of scope.
-/

namespace Contracts.DynamicIncrementalMerkle

open MerkleSpec

/-! ## State -/

/-- `DynamicIncrementalMerkleMemory.Bytes32PushTree` (DynamicIncrementalMerkleMemory.sol:39-47). -/
structure MemPushTree where
  /-- `_nextLeafIndex`. -/
  next : ℕ
  /-- `_sides`, the allocated array. -/
  sides : List UInt256
  /-- `_zeros`, the allocated array. -/
  zeros : List UInt256
  /-- `_sidesLengthMemory`: the logical length of `_sides`. -/
  sidesLen : ℕ
  /-- `_zerosLengthMemory`: the logical length of `_zeros`. -/
  zerosLen : ℕ
  /-- `_needsRootRecalculation`. -/
  needsRecalc : Bool
  /-- `_lastLeafValue`. -/
  lastLeaf : UInt256

/-- `Bytes32PushTree memory t;`: every field zero, both arrays empty. -/
def MemPushTree.fresh : MemPushTree := ⟨0, [], [], 0, 0, false, 0⟩

/-- A checked memory write `a[i] = v`: reverts at `i ≥ a.length`. -/
def mset (a : List UInt256) (i : ℕ) (v : UInt256) : Option (List UInt256) :=
  if i < a.length then some (a.set i v) else none

/-! ## `createTree`, `setup` (DynamicIncrementalMerkleMemory.sol:50-73) -/

/-- `createTree(_treeDepth)` (:50-56). -/
def createTree (T : MemPushTree) (depth : ℕ) : MemPushTree :=
  { T with sides := List.replicate depth 0, zeros := List.replicate depth 0, sidesLen := 0,
           zerosLen := 0, needsRecalc := false }

/-- `setup(zero)` (:65-73). -/
def msetup (T : MemPushTree) (zero : UInt256) : Option (MemPushTree × UInt256) :=
  (mset T.zeros 0 zero).bind fun zs => (mset T.sides 0 0).map fun sd =>
    ({ T with next := 0, zeros := zs, zerosLen := 1, sides := sd, sidesLen := 1, lastLeaf := 0 },
      0)

/-! ## `_pushInner`, `push`, `pushLazy` (DynamicIncrementalMerkleMemory.sol:79-163) -/

/-- How `_pushInner`'s loop ended: it ran all levels with this `currentLevelHash`, or it took
the lazy early return (:117-122). -/
inductive LoopEnd
  | done (cur : UInt256)
  | early

/-- `_pushInner`'s loop (:109-135), at level `i` with `k` iterations left; `zs` is `_zeros`, `sd`
is `_sides`, `upd` is `updatedSides`. -/
def mPushLoop (h : Hash) (lazy : Bool) (zs : List UInt256) :
    ℕ → ℕ → ℕ → UInt256 → Bool → List UInt256 → Option (LoopEnd × List UInt256)
  | 0, _, _, cur, _, sd => some (.done cur, sd)
  | k + 1, i, ci, cur, upd, sd =>
      if ci % 2 = 0 then
        if upd then
          (zs[i]?).bind fun zi => mPushLoop h lazy zs k (i + 1) (ci / 2) (h cur zi) true sd
        else
          -- `self._sides[i] = currentLevelHash; updatedSides = true;` (:115-116)
          (mset sd i cur).bind fun sd' =>
            -- `if (isLazy) { …; return (leafIndex, bytes32(0)); }` (:117-122)
            if lazy then some (.early, sd')
            else (zs[i]?).bind fun zi => mPushLoop h lazy zs k (i + 1) (ci / 2) (h cur zi) true sd'
      else
        (sd[i]?).bind fun si => mPushLoop h lazy zs k (i + 1) (ci / 2) (h si cur) upd sd

/-- The growth branch (:95-103), writing at the logical lengths: returns the tree and the new
`levels`. -/
def mGrow (h : Hash) (T : MemPushTree) : Option MemPushTree :=
  (T.zeros[T.zerosLen - 1]?).bind fun zero =>
    (mset T.zeros T.zerosLen (h zero zero)).bind fun zs =>
      (mset T.sides T.sidesLen 0).map fun sd =>
        { T with zeros := zs, zerosLen := T.zerosLen + 1, sides := sd, sidesLen := T.sidesLen + 1 }

/-- What `_pushInner` does after its loop, on the tree `T₂` after the growth branch: after the
lazy early return, set the flag and return `(leafIndex, bytes32(0))` (:117-122); otherwise
`self._sides[levels] = currentLevelHash; self._needsRootRecalculation = false;` and return the
root (:137-139). -/
def mPushFinish (T₂ : MemPushTree) (index levels : ℕ) :
    LoopEnd × List UInt256 → Option (MemPushTree × ℕ × UInt256)
  | (.early, sd) => some ({ T₂ with sides := sd, needsRecalc := true }, index, 0)
  | (.done cur, sd) =>
      (mset sd levels cur).map fun sd' => ({ T₂ with sides := sd', needsRecalc := false }, index, cur)

/-- `_pushInner(leaf, isLazy)` (:79-140): the new tree, `leafIndex` and `newRoot` (`bytes32(0)`
after a lazy early return). -/
def mPushInner (h : Hash) (T : MemPushTree) (leaf : UInt256) (lazy : Bool) :
    Option (MemPushTree × ℕ × UInt256) :=
  -- `uint256 levels = self._zerosLengthMemory - 1;` (:85)
  if T.zerosLen = 0 then none
  else
    -- `leafIndex = self._nextLeafIndex++;` (:89) and `self._lastLeafValue = leaf;` (:92)
    let index := T.next
    let T₁ : MemPushTree := { T with next := T.next + 1, lastLeaf := leaf }
    -- `if (leafIndex == 1 << levels) { … }` (:95-103)
    let T₂? := if index = 2 ^ (T.zerosLen - 1) then mGrow h T₁ else some T₁
    T₂?.bind fun T₂ =>
      (mPushLoop h lazy T₂.zeros (T₂.zerosLen - 1) 0 index leaf false T₂.sides).bind
        (mPushFinish T₂ index (T₂.zerosLen - 1))

/-- `push(leaf)` (:149-151). -/
def mPush (h : Hash) (T : MemPushTree) (leaf : UInt256) : Option (MemPushTree × ℕ × UInt256) :=
  mPushInner h T leaf false

/-- `pushLazy(leaf)` (:164-166): the new tree and `index`. -/
def mPushLazy (h : Hash) (T : MemPushTree) (leaf : UInt256) : Option (MemPushTree × ℕ) :=
  (mPushInner h T leaf true).map fun r => (r.1, r.2.1)

/-! ## `_recalculateRoot`, `root`, `height` (DynamicIncrementalMerkleMemory.sol:194-244) -/

/-- `_recalculateRoot`'s loop (:211-220), at level `i` with `k` iterations left. -/
def mRecalcLoop (h : Hash) (zs sd : List UInt256) : ℕ → ℕ → ℕ → UInt256 → Option UInt256
  | 0, _, _, cur => some cur
  | k + 1, i, ci, cur =>
      if ci % 2 = 0 then (zs[i]?).bind fun zi => mRecalcLoop h zs sd k (i + 1) (ci / 2) (h cur zi)
      else (sd[i]?).bind fun si => mRecalcLoop h zs sd k (i + 1) (ci / 2) (h si cur)

/-- `_recalculateRoot()` (:194-223). -/
def recalculateRoot (h : Hash) (T : MemPushTree) : Option UInt256 :=
  -- `uint256 levels = self._zerosLengthMemory - 1;` (:195)
  if T.zerosLen = 0 then none
  -- `if (leafCount == 0) return bytes32(0);` (:198-200)
  else if T.next = 0 then some 0
  else
    -- start from the last leaf: `_sides[0]` at an even index, `_lastLeafValue` at an odd one
    ((if (T.next - 1) % 2 = 0 then T.sides[0]? else some T.lastLeaf)).bind fun cur =>
      mRecalcLoop h T.zeros T.sides (T.zerosLen - 1) 0 (T.next - 1) cur

/-- `root()` (:228-237): the root, and the tree as `root()` leaves it (it writes the recalculated
root into the root slot and clears the flag). -/
def mRoot (h : Hash) (T : MemPushTree) : Option (MemPushTree × UInt256) :=
  if T.needsRecalc then
    (recalculateRoot h T).bind fun r =>
      if T.sidesLen = 0 then none
      else (mset T.sides (T.sidesLen - 1) r).map fun sd =>
        ({ T with sides := sd, needsRecalc := false }, r)
  else if T.sidesLen = 0 then none
  else (T.sides[T.sidesLen - 1]?).map fun r => (T, r)

/-- `height()` (:242-244). -/
def mHeight (T : MemPushTree) : Option ℕ :=
  if T.sidesLen = 0 then none else some (T.sidesLen - 1)

/-! ## What the memory tree holds -/

/-- The completed left node the LAST push read at level `i` when it arrived there as a right
child: entry `(|L| - 1) / 2^i - 1` of level `i`.  `_recalculateRoot` reads exactly these. -/
def prevNode (h : Hash) (z : UInt256) (L : List UInt256) (i : ℕ) : UInt256 :=
  (levels h z L i).getD ((L.length - 1) / 2 ^ i - 1) (zeros h z i)

/-- **The memory tree holds the tree over `L` at height `H`.**

* the logical lengths are `H + 1`, inside one allocation (`_sides` and `_zeros` as long as each
  other), and `_zeros[i] = zeros h z i` for `i ≤ H`;
* the sides invariant of the storage library (`frontierNode`), and the same for the previous
  count (`prevNode`), which is what `_recalculateRoot` needs;
* `_lastLeafValue` is the last leaf;
* unless the flag is set, the root slot `_sides[H]` holds `dimRoot h z L H`; when it is set, the
  tree is nonempty and not full (the push that fills it runs the loop to the end and clears the
  flag; along runs, `Properties.LazyFlagMeansNotFull`). -/
structure MemRepresents (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (T : MemPushTree) :
    Prop where
  next_eq : T.next = L.length
  capacity : L.length ≤ 2 ^ H
  sidesLen_eq : T.sidesLen = H + 1
  zerosLen_eq : T.zerosLen = H + 1
  alloc : T.zeros.length = T.sides.length
  fits : H + 1 ≤ T.sides.length
  zeros_eq : ∀ i, i ≤ H → T.zeros.getD i 0 = zeros h z i
  sides_eq : ∀ i, i < H → L.length / 2 ^ i % 2 = 1 → T.sides.getD i 0 = frontierNode h z L i
  prev_eq : ∀ i, i < H → (L.length - 1) / 2 ^ i % 2 = 1 → T.sides.getD i 0 = prevNode h z L i
  last_eq : L ≠ [] → T.lastLeaf = L.getD (L.length - 1) z
  top_eq : T.needsRecalc = false → T.sides.getD H 0 = dimRoot h z L H
  lazy_notFull : T.needsRecalc = true → L ≠ [] ∧ L.length < 2 ^ H

/-- One successful call on a memory tree, with the leaves as a ghost: an eager or a lazy push. -/
inductive MemStep (h : Hash) : List UInt256 × MemPushTree → List UInt256 × MemPushTree → Prop
  | push {L : List UInt256} {T T' : MemPushTree} {x : UInt256} {i : ℕ} {r : UInt256} :
      mPush h T x = some (T', i, r) → MemStep h (L, T) (L ++ [x], T')
  | pushLazy {L : List UInt256} {T T' : MemPushTree} {x : UInt256} {i : ℕ} :
      mPushLazy h T x = some (T', i) → MemStep h (L, T) (L ++ [x], T')

/-- **A memory tree after `createTree(depth)`, `setup(z)` and successful pushes**, eager or
lazy, in any order. -/
inductive MemRun (h : Hash) (z : UInt256) (depth : ℕ) : List UInt256 → MemPushTree → Prop
  | setup {T : MemPushTree} {r : UInt256} :
      msetup (createTree MemPushTree.fresh depth) z = some (T, r) → MemRun h z depth [] T
  | step {L L' : List UInt256} {T T' : MemPushTree} :
      MemRun h z depth L T → MemStep h (L, T) (L', T') → MemRun h z depth L' T'

/-! ## Runs of lazy pushes, for the witnesses -/

/-- `createTree(depth); setup(z);` then `pushLazy` each leaf in order; `none` if a call reverts. -/
def lazyRun (h : Hash) (z : UInt256) (depth : ℕ) (L : List UInt256) : Option MemPushTree :=
  (msetup (createTree MemPushTree.fresh depth) z).bind fun r =>
    L.foldl (fun o x => o.bind fun T => (mPushLazy h T x).map (·.1)) (some r.1)

end Contracts.DynamicIncrementalMerkle
