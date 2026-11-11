import EraSpec.Contracts.FullMerkle.Specs.Model

/-!
# Model: `DynamicIncrementalMerkle` (storage), transcribed

Every chain tree in the `MessageRoot` (`chainTree[chainId]`, MessageRootBase.sol:69, pushed at
:257-259, set up at :350) and the L1 priority tree (PriorityTree.sol:32, 54, 60) are
`DynamicIncrementalMerkle.Bytes32PushTree`s.  The repo so far took their root to be the
`FullMerkle`-shaped fold `rootOf h z leaves height` by definition (`Timeout.RootBacking`,
`EndBranch.Backing`, `LastBatchInRoot`).  The library departs from a fixed-height fold in four
ways, all visible below:

* **its height is dynamic and minimal**: the tree doubles exactly when it is full
  (`index == 1 << levels`, :102), so after `n ≥ 1` pushes its height is `⌈log₂ n⌉`;
* **its empty root is `bytes32(0)`** (`setup`, :56-57), not the zero cascade `rootOf h z [] 0 = z`;
* **its root after one leaf is that leaf** (height 0, no hashing);
* **it saves only the first left node of each push path** (`updatedSides`, :113-122), unlike
  the OpenZeppelin `MerkleTree` it forks, which saves every left node.

This file transcribes the storage struct and its seven functions as pure Lean functions.  The
statements are in `Properties/Model.lean`.

Source: `contracts/common/libraries/DynamicIncrementalMerkle.sol` at era-contracts `c67894b9`.

    struct Bytes32PushTree { uint256 _nextLeafIndex; bytes32[] _sides; bytes32[] _zeros; }

* `setup(zero)` (:53-58): `_nextLeafIndex = 0; _zeros.push(zero); _sides.push(bytes32(0));
  return bytes32(0);`.  There is no guard: a second `setup` pushes a second entry onto each array.
* `reset(zero)` (:66-69) is `clear(); setup(zero);` and returns its never-assigned named return
  `initialRoot`, i.e. `bytes32(0)`.  `clear()` (:74-84) zeroes `_nextLeafIndex` and pops both
  arrays empty.
* `push(leaf)` (:93-137): `levels = _zeros.length - 1`; `index = _nextLeafIndex++`.  If
  `index == 1 << levels` the tree grows (:102-108): it pushes `efficientHash(zero, zero)` with
  `zero = _zeros[levels]` onto `_zeros`, pushes `bytes32(0)` onto `_sides`, and increments `levels`.
  Then the loop (:111-133) walks up from the leaf: at a left child (`currentIndex % 2 == 0`) it
  saves the current node into `_sides[i]` **only if no side was saved yet on this path**
  (`isLeft && !updatedSides`, :119-122), and hashes with `_zeros[i]`; at a right child it hashes
  `_sides[i]` with the current node.  Finally `_sides[levels] = currentLevelHash` (:135): the top
  entry of `_sides` is the root.
* `extendUntilEnd(finalDepth)` (:143-156): with `currentZero = _zeros[_zeros.length - 1]`, it first
  writes `_sides[0] = currentZero` if the tree is empty (:145-147), then reads
  `currentSide = _sides[_sides.length - 1]` and, for `i` from `_sides.length` to `finalDepth - 1`,
  pushes `currentZero := h(currentZero, currentZero)` and `currentSide := h(currentSide, currentZero)`
  (the old `currentZero`) onto the two arrays.
* `root()` (:161-163) is `_sides[_sides.length - 1]`; `height()` (:168-170) is `_sides.length - 1`.

## How the transcription treats the language

* **Reverts are `none`.**  The checked subtraction `_zeros.length - 1` (:95, :144) and
  `_sides.length - 1` (:148, :162, :169) revert on an empty array, and so do the checked
  accesses `self._sides[0]` (:146) and `self._sides[self._sides.length - 1]` (:148).  The checked
  read `self._zeros[levels]` (:103) is always in range (`levels = _zeros.length - 1`), so it is a
  plain read here.
* **`Arrays.unsafeAccess`** (:120, :127-128, :135, :162) does no bounds check.  It is transcribed
  as `List.getD _ i 0` for a read and `List.set` for a write, which is exact whenever the index is
  below the array's length.  Every state reachable from fresh storage has `_sides` and `_zeros` of
  the same length (`setup`, growth and `extendUntilEnd` push one entry onto each), and on such a
  state every unsafe access of `push` and `root` is in range (`Represents.sides_length`).  On a
  state with `_sides` shorter than `_zeros`, which only direct struct writes can produce, the real
  code would touch storage slots past the end of `_sides`; that is outside the model.
* **Words.**  `bytes32` is `UInt256`; `Merkle.efficientHash(a, b)` is the abstract two-child hash
  `h : Hash`, as throughout `MerkleSpec`.  Indices and counters are `ℕ`.
* **Loops** are structural recursions on the number of iterations left.  `push`'s loop runs
  `levels` times and `extendUntilEnd`'s runs `finalDepth - _sides.length` times (zero if
  negative): neither body changes the bound.

## Model boundary

* `uint256` wrap is out of scope: `1 << levels` is `0` in the source once `levels ≥ 256`, and
  `_nextLeafIndex++` reverts at `2^256 - 1`; both need more than `2^255` leaves.  The loop counter
  `uint32 i` would overflow only past `2^32` levels.
* That compiled code executes these functions is the transcription's own correspondence
  obligation (`VM-STORAGE`, `SOL-ARITH`, `BUILD-PRESERVATION`).  It is not proved here.
-/

namespace Contracts.DynamicIncrementalMerkle

open MerkleSpec

/-! ## State -/

/-- `DynamicIncrementalMerkle.Bytes32PushTree` (DynamicIncrementalMerkle.sol:40-44). -/
structure PushTree where
  /-- `_nextLeafIndex`: the number of leaves pushed. -/
  next : ℕ
  /-- `_sides`: below the top, the saved left nodes; the top entry is the root. -/
  sides : List UInt256
  /-- `_zeros`: `_zeros[i]` is the hash of an empty subtree at level `i`. -/
  zeros : List UInt256

/-- Fresh storage: counter zero and both arrays empty. -/
def PushTree.empty : PushTree := ⟨0, [], []⟩

/-! ## `setup`, `clear`, `reset` (DynamicIncrementalMerkle.sol:53-84) -/

/-- `setup(zero)` (:53-58): `_nextLeafIndex = 0; _zeros.push(zero); _sides.push(bytes32(0));
return bytes32(0);`. -/
def setup (S : PushTree) (zero : UInt256) : PushTree × UInt256 :=
  ({ next := 0, sides := S.sides ++ [0], zeros := S.zeros ++ [zero] }, 0)

/-- `clear()` (:74-84): `_nextLeafIndex = 0`, then pop `_zeros` and `_sides` once per entry. -/
def clear (_S : PushTree) : PushTree := PushTree.empty

/-- `reset(zero)` (:66-69): `clear(self); setup(self, zero);`.  The named return `initialRoot`
is never assigned, so the call returns `bytes32(0)`. -/
def reset (S : PushTree) (zero : UInt256) : PushTree × UInt256 :=
  ((setup (clear S) zero).1, 0)

/-! ## `push` (DynamicIncrementalMerkle.sol:93-137) -/

/-- The growth branch (:102-108): `zero = _zeros[levels]` with `levels = _zeros.length - 1`,
then `_zeros.push(efficientHash(zero, zero))` and `_sides.push(bytes32(0))`. -/
def grow (h : Hash) (S : PushTree) : PushTree :=
  let zero := S.zeros.getD (S.zeros.length - 1) 0
  { S with zeros := S.zeros ++ [h zero zero], sides := S.sides ++ [0] }

/-- The loop of `push` (:111-133), at level `i` with `k` iterations left: `ci` is
`currentIndex`, `cur` is `currentLevelHash`, `upd` is `updatedSides`, `sd` is `_sides`, and `zs`
is `_zeros` (read only).

* Left child (`ci % 2 == 0`): if `guarded` and a side was already saved on this path, nothing is
  written; otherwise `_sides[i] = cur`.  Then `cur := h(cur, _zeros[i])` and `upd := true`.
* Right child: `cur := h(_sides[i], cur)`.

With `guarded = true` this is the fork's loop (`if (isLeft && !updatedSides)`, :119-122).  With
`guarded = false` it is OpenZeppelin's `MerkleTree._insert` loop (`if (isLeft)`), which the fork's
NatSpec (:21-22) names as its origin: it saves every left node on the path.  Returns the final
`currentLevelHash` and `_sides`. -/
def pushLoop (h : Hash) (guarded : Bool) (zs : List UInt256) :
    ℕ → ℕ → ℕ → UInt256 → Bool → List UInt256 → UInt256 × List UInt256
  | 0, _, _, cur, _, sd => (cur, sd)
  | k + 1, i, ci, cur, upd, sd =>
      if ci % 2 = 0 then
        pushLoop h guarded zs k (i + 1) (ci / 2) (h cur (zs.getD i 0)) true
          (if guarded && upd then sd else sd.set i cur)
      else
        pushLoop h guarded zs k (i + 1) (ci / 2) (h (sd.getD i 0) cur) upd sd

/-- `push` with the loop's guard switched: `guarded = true` is the deployed `push` (:93-137),
`guarded = false` the OpenZeppelin write policy with the fork's growth step.  Returns the new
storage, the leaf's `index` and the new root, or `none` when `_zeros.length - 1` underflows
(:95). -/
def pushWith (h : Hash) (guarded : Bool) (S : PushTree) (leaf : UInt256) :
    Option (PushTree × ℕ × UInt256) :=
  -- `uint256 levels = self._zeros.length - 1;` (:95)
  if S.zeros.length = 0 then none
  else
    -- `index = self._nextLeafIndex++;` (:99)
    let index := S.next
    -- `if (index == 1 << levels) { … }` (:102-108)
    let S₁ := if index = 2 ^ (S.zeros.length - 1) then grow h S else S
    let levels := S₁.zeros.length - 1
    -- the loop from `currentIndex = index`, `currentLevelHash = leaf`, `updatedSides = false`
    let r := pushLoop h guarded S₁.zeros levels 0 index leaf false S₁.sides
    -- `_sides[levels] = currentLevelHash; return (index, currentLevelHash);` (:135-136)
    some ({ next := index + 1, sides := r.2.set levels r.1, zeros := S₁.zeros }, index, r.1)

/-- **`push(leaf)`** (DynamicIncrementalMerkle.sol:93-137): the new storage, the leaf's index and
the new root. -/
def push (h : Hash) (S : PushTree) (leaf : UInt256) : Option (PushTree × ℕ × UInt256) :=
  pushWith h true S leaf

/-- The same `push` under OpenZeppelin's write policy (`if (isLeft)`), for comparison. -/
def ozPush (h : Hash) (S : PushTree) (leaf : UInt256) : Option (PushTree × ℕ × UInt256) :=
  pushWith h false S leaf

/-! ## `root`, `height` (DynamicIncrementalMerkle.sol:161-170) -/

/-- `root()` (:161-163): `_sides[_sides.length - 1]`; the subtraction reverts on an empty
`_sides`. -/
def root (S : PushTree) : Option UInt256 :=
  if S.sides.length = 0 then none else some (S.sides.getD (S.sides.length - 1) 0)

/-- `height()` (:168-170): `_sides.length - 1`. -/
def height (S : PushTree) : Option ℕ :=
  if S.sides.length = 0 then none else some (S.sides.length - 1)

/-! ## `extendUntilEnd` (DynamicIncrementalMerkle.sol:143-156) -/

/-- The loop of `extendUntilEnd` (:149-155), with `k` iterations left:
`currentSide = h(currentSide, currentZero); currentZero = h(currentZero, currentZero);` and
both pushed. -/
def extendLoop (h : Hash) : ℕ → UInt256 → UInt256 → PushTree → PushTree
  | 0, _, _, S => S
  | k + 1, side, zero, S =>
      extendLoop h k (h side zero) (h zero zero)
        { S with zeros := S.zeros ++ [h zero zero], sides := S.sides ++ [h side zero] }

/-- `extendUntilEnd(finalDepth)` (:143-156). -/
def extendUntilEnd (h : Hash) (S : PushTree) (finalDepth : ℕ) : Option PushTree :=
  -- `bytes32 currentZero = self._zeros[self._zeros.length - 1];` (:144)
  if S.zeros.length = 0 then none
  -- `self._sides[0] = …` (:146) and `self._sides[self._sides.length - 1]` (:148) revert on an
  -- empty `_sides`
  else if S.sides.length = 0 then none
  else
    let currentZero := S.zeros.getD (S.zeros.length - 1) 0
    -- `if (self._nextLeafIndex == 0) { self._sides[0] = currentZero; }` (:145-147)
    let sides₁ := if S.next = 0 then S.sides.set 0 currentZero else S.sides
    -- `bytes32 currentSide = self._sides[self._sides.length - 1];` (:148)
    let currentSide := sides₁.getD (sides₁.length - 1) 0
    -- `for (uint256 i = self._sides.length; i < finalDepth; ++i)` (:149)
    some (extendLoop h (finalDepth - sides₁.length) currentSide currentZero
      { S with sides := sides₁ })

/-! ## What the storage holds: the representation -/

/-- **The root the library reports for the tree over `L` at height `H`**: `bytes32(0)` for the
empty tree (`setup` stores it, :56), and the `FullMerkle`-shaped fold otherwise. -/
def dimRoot (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) : UInt256 :=
  if L = [] then 0 else rootOf h z L H

/-- The completed left node a push from `L.length` reads at level `i` when it arrives there as a
right child: entry `L.length / 2^i - 1` of level `i`.  Its subtree lies wholly below the next
index, so later pushes never change it. -/
def frontierNode (h : Hash) (z : UInt256) (L : List UInt256) (i : ℕ) : UInt256 :=
  (levels h z L i).getD (L.length / 2 ^ i - 1) (zeros h z i)

/-- **The sides invariant, without the root slot.**  `S` holds the tree over `L` at height `H`:

* `_nextLeafIndex` counts the leaves, and they fit the height;
* `_zeros[i] = zeros h z i` for `i ≤ H`, and `_sides` has `H + 1` entries;
* at every level `i < H` where the next push arrives as a right child (bit `i` of `L.length`
  set), `_sides[i]` is the completed left node `frontierNode h z L i`.

At the other levels `_sides[i]` is unconstrained: the fork leaves stale values there, and
OpenZeppelin's policy partial ones. -/
structure Frontier (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree) :
    Prop where
  next_eq : S.next = L.length
  capacity : L.length ≤ 2 ^ H
  zeros_eq : S.zeros = (List.range (H + 1)).map (zeros h z)
  sides_length : S.sides.length = H + 1
  sides_eq : ∀ i, i < H → L.length / 2 ^ i % 2 = 1 → S.sides.getD i 0 = frontierNode h z L i

/-- **`S` represents the tree over `L` at height `H`**: the sides invariant, and the root slot
`_sides[H]` holds `dimRoot h z L H` (`bytes32(0)` when empty). -/
structure Represents (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree) :
    Prop extends Frontier h z L H S where
  top_eq : S.sides.getD H 0 = dimRoot h z L H

/-- **After `extendUntilEnd`**: the sides invariant, with the root slot holding the fold
`rootOf h z L H` even when `L` is empty (`extendUntilEnd` writes the zero cascade there,
:145-147). -/
structure ExtendedRepresents (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ)
    (S : PushTree) : Prop extends Frontier h z L H S where
  top_eq : S.sides.getD H 0 = rootOf h z L H

/-- The height a push-only run reaches after `n` pushes: `⌈log₂ n⌉` (and `0` for `n ≤ 1`).
`Nat.clog 2 n` is the least `H` with `n ≤ 2^H`. -/
def dimHeight (n : ℕ) : ℕ := Nat.clog 2 n

/-! ## Runs of the library -/

/-- **Storage reached by `setup(z)` on fresh storage and then successful pushes**, with the
pushed leaves `L` in order as a ghost. -/
inductive Run (h : Hash) (z : UInt256) : List UInt256 → PushTree → Prop
  | setup : Run h z [] (setup PushTree.empty z).1
  | push {L : List UInt256} {S S' : PushTree} {x : UInt256} {i : ℕ} {r : UInt256} :
      Run h z L S → push h S x = some (S', i, r) → Run h z (L ++ [x]) S'

/-- Push the leaves `L` in order under the given write policy, or `none` if a call reverts. -/
def pushAllWith (h : Hash) (guarded : Bool) : PushTree → List UInt256 → Option PushTree
  | S, [] => some S
  | S, x :: xs => (pushWith h guarded S x).bind fun r => pushAllWith h guarded r.1 xs

/-- Push the leaves `L` in order with the deployed `push`, or `none` if a call reverts. -/
def pushAll (h : Hash) (S : PushTree) (L : List UInt256) : Option PushTree :=
  pushAllWith h true S L

/-! ## The zero value of the `MessageRoot` chain trees -/

/-- `CHAIN_TREE_EMPTY_ENTRY_HASH` (IMessageRoot.sol:9-11), the zero value every `MessageRoot`
chain tree is set up with (`chainTree[_chainId].setup(CHAIN_TREE_EMPTY_ENTRY_HASH)`,
MessageRootBase.sol:350).  The source comment (:8) says it is the hash of `new bytes(96)`. -/
def chainTreeEmptyEntryHash : UInt256 :=
  0x46700b4d40ac5c35af2c22dda2787a91eb567b06c924a8fb8ae9a05b20c08c21

/-! ## A misplaced guard, for the countermodel

The fork's guard is `isLeft && !updatedSides`.  Dropping `isLeft` from it (testing only
`!updatedSides`) saves the leaf into `_sides[0]` even when the leaf is a right child, before the
same iteration reads `_sides[0]` as its left sibling. -/

/-- `push`'s loop with the guard `if (!updatedSides)` in place of `if (isLeft && !updatedSides)`. -/
def misplacedLoop (h : Hash) (zs : List UInt256) :
    ℕ → ℕ → ℕ → UInt256 → Bool → List UInt256 → UInt256 × List UInt256
  | 0, _, _, cur, _, sd => (cur, sd)
  | k + 1, i, ci, cur, upd, sd =>
      let sd' := if upd then sd else sd.set i cur
      if ci % 2 = 0 then misplacedLoop h zs k (i + 1) (ci / 2) (h cur (zs.getD i 0)) true sd'
      else misplacedLoop h zs k (i + 1) (ci / 2) (h (sd'.getD i 0) cur) true sd'

/-- `push` with the misplaced guard. -/
def misplacedPush (h : Hash) (S : PushTree) (leaf : UInt256) :
    Option (PushTree × ℕ × UInt256) :=
  if S.zeros.length = 0 then none
  else
    let index := S.next
    let S₁ := if index = 2 ^ (S.zeros.length - 1) then grow h S else S
    let levels := S₁.zeros.length - 1
    let r := misplacedLoop h S₁.zeros levels 0 index leaf false S₁.sides
    some ({ next := index + 1, sides := r.2.set levels r.1, zeros := S₁.zeros }, index, r.1)

end Contracts.DynamicIncrementalMerkle
