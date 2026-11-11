import EraSpec.Contracts.FullMerkle.Specs.Model
import EraSpec.Contracts.FullMerkle.Specs.CapacityInvariant

/-!
# Model: `FullMerkle`'s cached-node algorithm, transcribed

`Specs/Model.lean` defines the tree abstractly: `levels h z0 leaves l` is the level-`l`
list and `rootOf h z0 leaves height` the root at a height.  The deployed library does
not evaluate that fold.  It keeps every level in storage (`_nodes`), keeps the
empty-subtree hashes in `_zeros`, and patches one root-to-leaf path per call.  Every
result about "the root `FullMerkle` publishes" so far took the fold as that root by
definition (`L2InteropCommitmentTree/Specs/TreeRoot.lean`, `RunHeight.lean`, and
obligation O7 in `EraSpec.Refinement`).

This file transcribes the library's storage and its five functions, statement by
statement, as pure Lean functions, so that the cached algorithm can be compared with the
fold.  The comparison is stated in `Properties/CachedNodes.lean`.

Source: `contracts/common/libraries/FullMerkle.sol` at era-contracts `c67894b9`.

    struct FullTree { uint256 _height; uint256 _leafNumber; bytes32[][] _nodes; bytes32[] _zeros; }

* `setup(zero)` (FullMerkle.sol:29-35) pushes `zero` onto `_zeros` and `[zero]` onto
  `_nodes`.
* `pushNewLeaf(leaf)` (:41-66) takes `index = _leafNumber++`.  When `index == 1 << _height`
  it grows the tree (:45-52): `_height += 1`, and it pushes `h(topZero, topZero)` onto
  `_zeros` and as a new one-entry level onto `_nodes`.  When `index != 0` it pads (:53-64):
  from level 0 upwards, while the old and the new last index of the level differ, it
  pushes `_zeros[i]` onto `_nodes[i]`.  Then it calls `updateLeaf(index, leaf)`.
* `updateLeaf(_index, x)` (:73-94) writes `_nodes[0][_index] = x` and walks up.  At each
  level it hashes with the right sibling `_nodes[i][_index + 1]` (even index), or with
  `_zeros[i]` when `_index` is the level's last node (`maxNodeNumber == _index`, :84), or
  with the left sibling `_nodes[i][_index - 1]` (odd index).  It stores each parent at
  `_nodes[i + 1][_index / 2]` and returns the last one.
* `root()` (:99-101) is `_nodes[_height][0]`.
* `merklePath(_index)` (:107-126) returns the siblings `updateLeaf` would read, one per
  level below `_height`.

## How the transcription treats the language

* **Reverts are `none`.**  A storage-array read or write at an index `≥ length` reverts
  (Panic 0x32), so `nodeAt`, `setNode`, `pushNode` and `zs[i]?` return `none` there.  The
  checked subtraction `self._leafNumber - 1` (:74) underflows on an empty tree, and that
  revert is transcribed too.  Explicit `revert`s (`MerkleWrongIndex`,
  `MerkleNothingToProve`) are `none`.  A call that returns `none` has no effect, as in
  `MODEL-COMMIT`.
* **Words.**  `bytes32` is `UInt256`.  `Merkle.efficientHash(a, b)`, the keccak of the
  64-byte concatenation, is the abstract two-child hash `h : Hash`, as throughout
  `MerkleSpec`.
* **Loops** are structural recursions on the number of iterations left.  `self._height`
  is re-read by every loop test, but no loop body writes it, so the count is fixed on
  entry.

## Model boundary

* `_height`, `_leafNumber` and all indices are `ℕ`.  In the source `1 << self._height`
  (:45) is a `uint256` shift, which is `0` once `_height ≥ 256`.  `self._leafNumber++`
  (:43) reverts at `2^256 - 1`.  Both need more than `2^255` leaves and are not modelled
  (as in `L2InteropCommitmentTree/Specs/RunHeight.lean`).  No other arithmetic step can
  wrap or underflow on the paths that reach it: the halvings; `_index + 1` and `i + 1`
  on values below `_leafNumber` and `_height`; and `_index - 1`, `newHeight - 1` and
  `index - 1`, each taken only when the value is positive.
* `Merkle.calculateRoot` also rejects a path of length `≥ 256` (Merkle.sol:133-140).  A
  path from `merklePath` has length `_height`, and `_height < 256` holds below `2^255`
  leaves, so that check is not modelled either.
* `setup` has no guard; called on storage that is not fresh it pushes a second zero.
  Runs here (`Reachable`) start with `setup` on `FullTree.empty`, the fresh storage;
  the other results assume `Represents`, which a second `setup` breaks.
  `IndexedMerkleTree.setup` guards the call with `_leafNumber != 0` and pushes a leaf
  straight after (IndexedMerkleTree.sol:42-51).
* That compiled code executes these functions is the transcription's own correspondence
  obligation (`VM-STORAGE`, `SOL-ARITH`, `BUILD-PRESERVATION`).  It is not proved here.
-/

namespace Contracts.FullMerkle

open MerkleSpec

/-! ## State -/

/-- `FullMerkle.FullTree` (FullMerkle.sol:14-19). -/
structure FullTree where
  /-- `_height`. -/
  height : ℕ
  /-- `_leafNumber`. -/
  leafNumber : ℕ
  /-- `_nodes`: `_nodes[i]` is the cached level `i`. -/
  nodes : List (List UInt256)
  /-- `_zeros`: `_zeros[i]` is the hash of an empty subtree at level `i`. -/
  zeros : List UInt256

/-- Fresh storage: both counters zero and both arrays empty. -/
def FullTree.empty : FullTree := ⟨0, 0, [], []⟩

/-! ## Storage-array access (out-of-bounds access reverts) -/

/-- `self._nodes[i][j]` read. -/
def nodeAt (N : List (List UInt256)) (i j : ℕ) : Option UInt256 :=
  N[i]?.bind fun row => row[j]?

/-- `self._nodes[i][j] = a`. -/
def setNode (N : List (List UInt256)) (i j : ℕ) (a : UInt256) : Option (List (List UInt256)) :=
  N[i]?.bind fun row => if j < row.length then some (N.set i (row.set j a)) else none

/-- `self._nodes[i].push(a)`. -/
def pushNode (N : List (List UInt256)) (i : ℕ) (a : UInt256) : Option (List (List UInt256)) :=
  N[i]?.map fun row => N.set i (row ++ [a])

/-! ## `setup` (FullMerkle.sol:29-35) -/

/-- `setup(zero)`: `_zeros.push(zero); _nodes.push([zero]); return zero;`. -/
def setup (S : FullTree) (zero : UInt256) : FullTree × UInt256 :=
  ({ S with zeros := S.zeros ++ [zero], nodes := S.nodes ++ [[zero]] }, zero)

/-! ## `updateLeaf` (FullMerkle.sol:73-94) -/

/-- The sibling read at level `i` for the node at index `idx`, shared by `updateLeaf`
(FullMerkle.sol:81-87) and `merklePath` (:117-121): for an even index, `_zeros[i]` if
`idx` is the level's last node (`maxNodeNumber == _index`) and `_nodes[i][idx + 1]`
otherwise; for an odd index, `_nodes[i][idx - 1]`. -/
def sibRead (zs : List UInt256) (N : List (List UInt256)) (i idx maxN : ℕ) : Option UInt256 :=
  if idx % 2 = 0 then (if maxN = idx then zs[i]? else nodeAt N i (idx + 1))
  else nodeAt N i (idx - 1)

/-- `updateLeaf`'s loop (FullMerkle.sol:80-92), at level `i` with `k` iterations left:
hash `currentHash` with the sibling (sibling on the right for an even index), halve
`_index` and `maxNodeNumber`, and store the parent at `_nodes[i + 1][_index]`.  Returns
the final `_nodes` and `currentHash`. -/
def updateLoop (h : Hash) (zs : List UInt256) :
    ℕ → ℕ → ℕ → ℕ → UInt256 → List (List UInt256) → Option (List (List UInt256) × UInt256)
  | 0, _, _, _, cur, N => some (N, cur)
  | k + 1, i, idx, maxN, cur, N => do
      let s ← sibRead zs N i idx maxN
      let cur' := if idx % 2 = 0 then h cur s else h s cur
      let N' ← setNode N (i + 1) (idx / 2) cur'
      updateLoop h zs k (i + 1) (idx / 2) (maxN / 2) cur' N'

/-- `updateLeaf(_index, _itemHash)`: the new storage and the returned hash. -/
def updateLeaf (h : Hash) (S : FullTree) (idx : ℕ) (x : UInt256) :
    Option (FullTree × UInt256) :=
  -- `uint256 maxNodeNumber = self._leafNumber - 1;` underflows on an empty tree (:74)
  if S.leafNumber = 0 then none
  -- `if (_index > maxNodeNumber) revert MerkleWrongIndex(...)` (:75-77)
  else if S.leafNumber - 1 < idx then none
  else do
    -- `self._nodes[0][_index] = _itemHash;` (:78)
    let N ← setNode S.nodes 0 idx x
    -- the loop, from `currentHash = _itemHash` (:79-92)
    let r ← updateLoop h S.zeros S.height 0 idx (S.leafNumber - 1) x N
    pure ({ S with nodes := r.1 }, r.2)

/-! ## `pushNewLeaf` (FullMerkle.sol:41-66) -/

/-- The growth branch (FullMerkle.sol:45-52): `newHeight = _height + 1`, then push
`efficientHash(topZero, topZero)` with `topZero = _zeros[newHeight - 1]` onto `_zeros`,
and as the one-entry level `[newZero]` onto `_nodes`. -/
def grow (h : Hash) (S : FullTree) : Option FullTree :=
  let newHeight := S.height + 1
  S.zeros[newHeight - 1]?.map fun topZero =>
    { S with height := newHeight,
             zeros := S.zeros ++ [h topZero topZero],
             nodes := S.nodes ++ [[h topZero topZero]] }

/-- The padding loop (FullMerkle.sol:56-63), at level `i` with `k` iterations left:
`break` when `oldMaxNodeNumber == maxNodeNumber`, otherwise
`_nodes[i].push(_zeros[i])` and halve both. -/
def padLoop (zs : List UInt256) :
    ℕ → ℕ → ℕ → ℕ → List (List UInt256) → Option (List (List UInt256))
  | 0, _, _, _, N => some N
  | k + 1, i, oldMax, maxN, N =>
      if oldMax = maxN then some N
      else do
        let z ← zs[i]?
        let N' ← pushNode N i z
        padLoop zs k (i + 1) (oldMax / 2) (maxN / 2) N'

/-- The padding block (FullMerkle.sol:53-64) for the new leaf's `index`: nothing when
`index == 0`, otherwise the loop from level 0 with `oldMaxNodeNumber = index - 1` and
`maxNodeNumber = index`, up to the (possibly grown) `_height`. -/
def pad (S : FullTree) (index : ℕ) : Option FullTree :=
  if index = 0 then some S
  else (padLoop S.zeros S.height 0 (index - 1) index S.nodes).map fun N => { S with nodes := N }

/-- `pushNewLeaf(_leaf)`: the new storage and the returned root. -/
def pushNewLeaf (h : Hash) (S : FullTree) (leaf : UInt256) : Option (FullTree × UInt256) := do
  -- `uint256 index = self._leafNumber++;` (:43)
  let index := S.leafNumber
  let S₁ : FullTree := { S with leafNumber := S.leafNumber + 1 }
  -- `if (index == 1 << self._height) { ... }` (:45-52)
  let S₂ ← if index = 2 ^ S₁.height then grow h S₁ else some S₁
  -- `if (index != 0) { ... }` (:53-64)
  let S₃ ← pad S₂ index
  -- `return updateLeaf(self, index, _leaf);` (:65)
  updateLeaf h S₃ index leaf

/-! ## `root` and `merklePath` (FullMerkle.sol:99-126) -/

/-- `root()`: `self._nodes[self._height][0]` (:99-101). -/
def root (S : FullTree) : Option UInt256 := nodeAt S.nodes S.height 0

/-- `merklePath`'s loop (FullMerkle.sol:116-124), at level `i` with `k` iterations left:
`proof[i]` is the sibling read, then `_index` and `maxNodeNumber` are halved. -/
def pathLoop (zs : List UInt256) (N : List (List UInt256)) :
    ℕ → ℕ → ℕ → ℕ → Option (List UInt256)
  | 0, _, _, _ => some []
  | k + 1, i, idx, maxN => do
      let s ← sibRead zs N i idx maxN
      let rest ← pathLoop zs N k (i + 1) (idx / 2) (maxN / 2)
      pure (s :: rest)

/-- `merklePath(_index)` (:107-126): the `_height` siblings of `_index`, bottom-up. -/
def merklePath (S : FullTree) (idx : ℕ) : Option (List UInt256) :=
  -- `if (self._leafNumber == 0) revert MerkleNothingToProve();` (:108-110)
  if S.leafNumber = 0 then none
  -- `if (_index > maxNodeNumber) revert MerkleWrongIndex(...)` (:111-114)
  else if S.leafNumber - 1 < idx then none
  else pathLoop S.zeros S.nodes S.height 0 idx (S.leafNumber - 1)

/-- The sibling stream `Merkle.calculateRoot(_path, _index, _itemHash)` reads from a path
`p` (Merkle.sol:27-44): `_path[i]` at level `i < _path.length`.  Levels at or above the
length are never read (`MerkleSpec.walkPure_congr_sibs`), so the default `0` is
immaterial. -/
def pathSibs (p : List UInt256) : ℕ → UInt256 := fun l => p.getD l 0

/-! ## What the storage holds: the representation -/

/-- The level-`l` list the storage caches for the tree over `leaves`: the abstract level
`levels h z0 leaves l`, except that an empty tree caches the single entry `zeros h z0 l`
(`setup` stores `[zero]` at level 0, and `grow` stores `[newZero]` at each new level). -/
def cachedLevel (h : Hash) (z0 : UInt256) (leaves : List UInt256) (l : ℕ) : List UInt256 :=
  if leaves = [] then [zeros h z0 l] else levels h z0 leaves l

/-- **`S` caches the tree over `leaves`.**  `_leafNumber` is the number of leaves, the
leaves fit the height, and each of the `_height + 1` entries of `_zeros` and `_nodes`
is what the fold says it is: `_zeros[i] = zeros h z0 i`, and `_nodes[i]` is the level-`i`
list `levels h z0 leaves i` (one zero for an empty tree). -/
structure Represents (h : Hash) (z0 : UInt256) (leaves : List UInt256) (S : FullTree) :
    Prop where
  leafNumber_eq : S.leafNumber = leaves.length
  capacity : leaves.length ≤ 2 ^ S.height
  zeros_eq : S.zeros = (List.range (S.height + 1)).map (zeros h z0)
  nodes_eq : S.nodes = (List.range (S.height + 1)).map (cachedLevel h z0 leaves)

/-- The leaves the storage holds: the first `_leafNumber` entries of `_nodes[0]`. -/
def leavesOf (S : FullTree) : List UInt256 := (S.nodes.headD []).take S.leafNumber

/-! ## Runs of the library -/

/-- One successful library call: `pushNewLeaf(x)` or `updateLeaf(i, x)`. -/
inductive Step (h : Hash) : FullTree → FullTree → Prop
  | push {S S' : FullTree} {x r : UInt256} : pushNewLeaf h S x = some (S', r) → Step h S S'
  | update {S S' : FullTree} {i : ℕ} {x r : UInt256} :
      updateLeaf h S i x = some (S', r) → Step h S S'

/-- Storage reachable from fresh storage by `setup(z0)` and then successful calls. -/
inductive Reachable (h : Hash) (z0 : UInt256) : FullTree → Prop
  | init : Reachable h z0 (setup FullTree.empty z0).1
  | step {S S' : FullTree} : Reachable h z0 S → Step h S S' → Reachable h z0 S'

/-! ## A concrete run, for the witnesses -/

/-- `setup(z0)` then `pushNewLeaf(a)`, `pushNewLeaf(b)`, `pushNewLeaf(c)` on fresh storage,
or `none` if any call reverts.  Both later pushes take the growth branch. -/
def threePushes (h : Hash) (z0 a b c : UInt256) : Option FullTree := do
  let r₁ ← pushNewLeaf h (setup FullTree.empty z0).1 a
  let r₂ ← pushNewLeaf h r₁.1 b
  let r₃ ← pushNewLeaf h r₂.1 c
  pure r₃.1

end Contracts.FullMerkle
