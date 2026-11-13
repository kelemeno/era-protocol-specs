import EraSpec.Contracts.Merkle.Specs.PathCollision
import EraSpec.Contracts.Merkle.Specs.RootForgeryPinned

/-!
# Contract spec: `DynamicIncrementalMerkle` (the storage push tree)

Source: `l1-contracts/contracts/common/libraries/DynamicIncrementalMerkle.sol` at era-contracts
`d9f678900e1bc8286412b78f56d4a9f443983c29` (draft/v0.35.0). Line numbers below are of that file.

**Definitions only.** Statements are in `../Properties/Model.lean`, proofs in
`../Proofs/Model.lean`.

## State

`Bytes32PushTree` (`:40-44`) is `(_nextLeafIndex, _sides, _zeros)`: a counter and two storage
arrays. `Tree` transcribes it with the counter in `ℕ` and the arrays as lists.

## Operations, in source order

* `setup` (`:53-58`): `_nextLeafIndex = 0`, `_zeros.push(zero)`, `_sides.push(0)`, return `0`.
  It does **not** clear the arrays first and has no guard.
* `reset` (`:66-69`): `clear` then `setup`.
* `clear` (`:74-84`): counter to `0`, pop every entry of both arrays.
* `push` (`:93-137`): `levels = _zeros.length - 1` (checked: reverts on an empty tree),
  `index = _nextLeafIndex++` (checked: reverts at `2^256 - 1`); if `index == 1 << levels`
  the tree grows one level (`_zeros.push(h(z, z))`, `_sides.push(0)`); then the loop
  `pushLoop` rebuilds the branch, writing `_sides[i]` only at the FIRST level where the path
  is a left child (`updatedSides`); finally `_sides[levels] = root`.
* `extendUntilEnd` (`:143-156`): if the tree is empty, `_sides[0] = _zeros[last]`; then append
  levels `i = _sides.length, …, finalDepth - 1`, each new side `h(side, zero)` and each new zero
  `h(zero, zero)`.
* `root` (`:161-163`): `_sides[_sides.length - 1]` (checked subtraction).
* `height` (`:168-170`): `_sides.length - 1`.

`Merkle.efficientHash` (`Merkle.sol:125-131`) is the abstract `h : MerkleSpec.Hash`.

## Model boundary (`MODEL-DIM` in ASSUMPTIONS.md)

* `1 << levels` is the uint256 shift: `shl1 levels = 2^levels` for `levels < 256`, else `0`.
* `_nextLeafIndex` and `finalDepth` are `ℕ`; the `++` overflow revert is the `index = UINT_MAX`
  guard. The loop counter `uint32 i` overflows only at `2^32` levels, which needs
  `finalDepth ≥ 2^32`; it is not modelled.
* `Arrays.unsafeAccess` reads and writes are `getD _ 0` / `List.set`, which agree with storage
  only in bounds. `Properties.PushAccessInBounds` proves every such index is in bounds on every
  represented (hence every reachable) tree.
* A revert is `none`. The library is `internal`: who may call it is the consumer's business.
  `Reach` lets the consumer make every call in any order, except `setup` on a tree that is
  already set up (the source's "WARNING" at `:38`); `Properties.SecondSetupBreaksTheZeroCascade`
  shows what that call does.
-/

namespace Contracts.DynamicIncrementalMerkle

open Clear MerkleSpec

/-! ## State -/

/-- `Bytes32PushTree` (`DynamicIncrementalMerkle.sol:40-44`). -/
structure Tree where
  /-- `_nextLeafIndex` -/
  next : ℕ
  /-- `_sides` -/
  sides : List UInt256
  /-- `_zeros` -/
  zeros : List UInt256
deriving DecidableEq

/-- All-zero storage: what a never-touched `Bytes32PushTree` holds. -/
def blank : Tree := ⟨0, [], []⟩

/-- `type(uint256).max`: `_nextLeafIndex++` reverts when the counter already holds it. -/
def UINT_MAX : ℕ := 2 ^ 256 - 1

/-- `1 << levels` on `uint256`: zero once the shift reaches the word width. -/
def shl1 (levels : ℕ) : ℕ := if levels < 256 then 2 ^ levels else 0

/-! ## The library functions -/

/-- `setup` (`:53-58`). Pushes onto whatever arrays are there; returns `bytes32(0)`. -/
def setup (t : Tree) (zero : UInt256) : Tree × UInt256 :=
  (⟨0, t.sides ++ [0], t.zeros ++ [zero]⟩, 0)

/-- `clear` (`:74-84`): both pop loops run to empty. -/
def clear (_t : Tree) : Tree := ⟨0, [], []⟩

/-- `reset` (`:66-69`). -/
def reset (t : Tree) (zero : UInt256) : Tree × UInt256 := setup (clear t) zero

/-- The branch-rebuild loop of `push` (`:111-133`), from level `i` with `k` iterations left,
path index `idx`, accumulator `acc`, flag `updatedSides = upd` and side array `sd`.
Returns the final side array and the final accumulator. Per iteration, in source order:
`isLeft = idx % 2 == 0`; if `isLeft && !upd` write `_sides[i] = acc` and set the flag; then
`acc = h(isLeft ? acc : _sides[i], isLeft ? _zeros[i] : acc)`; `idx >>= 1`. -/
def pushLoop (h : Hash) (zs : List UInt256) :
    ℕ → ℕ → ℕ → UInt256 → Bool → List UInt256 → List UInt256 × UInt256
  | _, 0, _, acc, _, sd => (sd, acc)
  | i, k + 1, idx, acc, upd, sd =>
      let isLeft : Bool := decide (idx % 2 = 0)
      let write : Bool := isLeft && !upd
      let sd1 := if write then sd.set i acc else sd
      let upd1 := upd || write
      let acc1 := h (if isLeft then acc else sd1.getD i 0) (if isLeft then zs.getD i 0 else acc)
      pushLoop h zs (i + 1) k (idx / 2) acc1 upd1 sd1

/-- The growth block of `push` (`:102-108`): `(_zeros, _sides, levels)` after it. -/
def grow (h : Hash) (t : Tree) (levels index : ℕ) : List UInt256 × List UInt256 × ℕ :=
  if index = shl1 levels then
    (t.zeros ++ [h (t.zeros.getD levels 0) (t.zeros.getD levels 0)], t.sides ++ [0], levels + 1)
  else (t.zeros, t.sides, levels)

/-- `push` (`:93-137`). Returns the new tree, the leaf index and the new root. -/
def push (h : Hash) (t : Tree) (leaf : UInt256) : Option (Tree × ℕ × UInt256) :=
  if t.zeros.length = 0 then none            -- `_zeros.length - 1` underflows (`:95`)
  else if t.next = UINT_MAX then none        -- `_nextLeafIndex++` overflows (`:99`)
  else
    let g := grow h t (t.zeros.length - 1) t.next
    let r := pushLoop h g.1 0 g.2.2 t.next leaf false g.2.1
    some (⟨t.next + 1, r.1.set g.2.2 r.2, g.1⟩, t.next, r.2)

/-- The append loop of `extendUntilEnd` (`:149-155`), run `k` times from `(side, zero)`. -/
def extendSteps (h : Hash) : ℕ → UInt256 → UInt256 → List UInt256 → List UInt256 →
    List UInt256 × List UInt256
  | 0, _, _, zs, sd => (zs, sd)
  | k + 1, cs, cz, zs, sd =>
      extendSteps h k (h cs cz) (h cz cz) (zs ++ [h cz cz]) (sd ++ [h cs cz])

/-- `extendUntilEnd` (`:143-156`). The loop runs for `i` from `_sides.length` to
`finalDepth - 1`, i.e. `finalDepth - _sides.length` times. -/
def extendUntilEnd (h : Hash) (t : Tree) (finalDepth : ℕ) : Option Tree :=
  if t.zeros.length = 0 then none            -- `_zeros.length - 1` underflows (`:144`)
  else if t.sides.length = 0 then none       -- `_sides[0]` (`:146`) / `_sides.length - 1` (`:148`)
  else
    let cz := t.zeros.getD (t.zeros.length - 1) 0
    let sd := if t.next = 0 then t.sides.set 0 cz else t.sides
    let r := extendSteps h (finalDepth - sd.length) (sd.getD (sd.length - 1) 0) cz t.zeros sd
    some ⟨t.next, r.2, r.1⟩

/-- `root` (`:161-163`). -/
def root (t : Tree) : Option UInt256 :=
  if t.sides.length = 0 then none else some (t.sides.getD (t.sides.length - 1) 0)

/-- `height` (`:168-170`). -/
def height (t : Tree) : Option ℕ :=
  if t.sides.length = 0 then none else some (t.sides.length - 1)

/-! ## The representation relation -/

/-- The last complete left-child node at level `i` of the tree over `L`: among the
`L.length / 2^i` complete level-`i` nodes, the last one with an even index. This is what
`_sides[i]` holds once `2^i` leaves are in. -/
def frontierNode (h : Hash) (z0 : UInt256) (L : List UInt256) (i : ℕ) : UInt256 :=
  (levels h z0 L i).getD (2 * ((L.length / 2 ^ i - 1) / 2)) (zeros h z0 i)

/-- **The representation invariant.** The storage tree `t` of height `H` holds the leaf list
`L` with padding `z0`, in the sense of `MerkleSpec.rootOf` (`FullMerkle/Specs/Model.lean`):
* the counter is the number of leaves, which fits the `++` guard and the height;
* `_zeros[i]` is the level-`i` zero cascade of `z0`, for every `i ≤ H`;
* `_sides` and `_zeros` have `H + 1` entries;
* **frontier**: at every level `i < H` that holds a complete node, `_sides[i]` is the last
  complete left-child node (`frontierNode`);
* **root slot**: `_sides[H]` is the full-tree root of `L` at height `H`, except on a freshly
  set-up empty tree of height 0, where `setup` wrote `bytes32(0)`. -/
structure Repr (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ) (t : Tree) : Prop where
  next_eq : t.next = L.length
  next_le : L.length ≤ UINT_MAX
  cap : L.length ≤ 2 ^ H
  zeros_len : t.zeros.length = H + 1
  zeros_eq : ∀ i, i ≤ H → t.zeros.getD i 0 = zeros h z0 i
  sides_len : t.sides.length = H + 1
  frontier : ∀ i, i < H → 2 ^ i ≤ L.length → t.sides.getD i 0 = frontierNode h z0 L i
  rootSlot : t.sides.getD H 0 = rootOf h z0 L H ∨ (L = [] ∧ H = 0 ∧ t.sides.getD 0 0 = 0)

/-- The height `push` produces from height `H` with `n` leaves already in. -/
def pushHeight (n H : ℕ) : ℕ := if n = shl1 H then H + 1 else H

/-- The number of trailing one bits of `n`: the first loop level at which `n`'s path is a
left child, i.e. the only level whose `_sides` entry `push` writes inside the loop. -/
def lowZero (n : ℕ) : ℕ := if n % 2 = 0 then 0 else lowZero (n / 2) + 1
termination_by n
decreasing_by omega

/-! ## Runs -/

/-- **Every call sequence a consumer can make**, with a ghost: `none` for blank storage,
`some (z, L)` for a tree set up with padding `z` into which the leaves `L` were pushed since.
Only successful calls are steps (a revert is no step). The one call left out is `setup` on a
tree that is already set up. -/
inductive Reach (h : Hash) : Tree → Option (UInt256 × List UInt256) → Prop
  | blank : Reach h blank none
  | setup {t : Tree} (z : UInt256) : Reach h t none → Reach h (setup t z).1 (some (z, []))
  | clear {t : Tree} {g : Option (UInt256 × List UInt256)} : Reach h t g → Reach h (clear t) none
  | reset {t : Tree} {g : Option (UInt256 × List UInt256)} (z : UInt256) :
      Reach h t g → Reach h (reset t z).1 (some (z, []))
  | push {t t' : Tree} {z x r : UInt256} {L : List UInt256} {i : ℕ} :
      Reach h t (some (z, L)) → push h t x = some (t', i, r) → Reach h t' (some (z, L ++ [x]))
  | extend {t t' : Tree} {z : UInt256} {L : List UInt256} {d : ℕ} :
      Reach h t (some (z, L)) → extendUntilEnd h t d = some t' → Reach h t' (some (z, L))

/-- Runs that only push after `setup(z)` on blank storage (no `extendUntilEnd`, no `reset`):
what `MessageRootBase` and `PriorityTree` do with their trees. -/
inductive PushRun (h : Hash) (z : UInt256) : Tree → List UInt256 → Prop
  | setup : PushRun h z (setup blank z).1 []
  | push {t t' : Tree} {x r : UInt256} {L : List UInt256} {i : ℕ} :
      PushRun h z t L → push h t x = some (t', i, r) → PushRun h z t' (L ++ [x])

/-! ## Variants, for the countermodels only -/

/-- `push` with the growth block (`:102-108`) deleted. -/
def pushNoGrow (h : Hash) (t : Tree) (leaf : UInt256) : Option (Tree × ℕ × UInt256) :=
  if t.zeros.length = 0 then none
  else if t.next = UINT_MAX then none
  else
    let levels := t.zeros.length - 1
    let r := pushLoop h t.zeros 0 levels t.next leaf false t.sides
    some (⟨t.next + 1, r.1.set levels r.2, t.zeros⟩, t.next, r.2)

/-- `setup(z)`, `push(a)`, `push(b)` on blank storage with the growth block deleted;
returns `root()`. -/
def twoPushesNoGrow (h : Hash) (z a b : UInt256) : Option UInt256 := do
  let r₁ ← pushNoGrow h (setup blank z).1 a
  let r₂ ← pushNoGrow h r₁.1 b
  root r₂.1

/-! ## A concrete run, for the witnesses -/

/-- `setup(z)` then `push(a)`, `push(b)`, `push(c)` on blank storage, or `none` if a call
reverts. Both later pushes take the growth branch. -/
def threePushes (h : Hash) (z a b c : UInt256) : Option Tree := do
  let r₁ ← push h (setup blank z).1 a
  let r₂ ← push h r₁.1 b
  let r₃ ← push h r₂.1 c
  pure r₃.1

end Contracts.DynamicIncrementalMerkle
