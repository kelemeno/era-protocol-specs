import EraSpec.Core.Word

/-!
# Model: the `PriorityTree` library and the tree it wraps

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`. Paths are
relative to `l1-contracts/contracts/`.

* `state-transition/libraries/PriorityTree.sol`, cited as `PT`.
* `common/libraries/DynamicIncrementalMerkle.sol`, cited as `DIM`: only the struct and the three
  functions `PriorityTree` calls (`setup`, `push`, `root`).

**This file is definitions only.** Statements are in
`EraSpec.Contracts.MailboxFacet.Properties.PriorityTree`, proofs in
`EraSpec.Contracts.MailboxFacet.Proofs.PriorityTree`.

## Conventions

* A `uint256` counter is a natural number. Each checked `+`, `*`, `++`, `+=` of the source
  reverts at `2^256`; the model writes that guard out (`checked`). A revert is `none`.
* `bytes32` values are `UInt256`. The node hash `Merkle.efficientHash` and the padding leaf
  `ZERO_LEAF_HASH = keccak256("")` (`PT:22`) are parameters; nothing is assumed about them.
* `Merkle.calculateRootPaths` (`PT:85-90`) is a parameter `RootPaths`: `none` is a revert of that
  call. Nothing is assumed about it.
* `Arrays.unsafeAccess` (`DIM:120-135`, `:162`) does no bounds check. The model reads a missing
  slot as `0` and drops a write to a missing slot. On every state reachable from `setup` or
  `initFromCommitment` the accesses are in bounds (`Properties.TreeShapeInvariant`), so the choice
  is not observable there.
* The loop counter of `DIM.push` is a `uint32` (`DIM:114`). Its overflow needs `2^32` levels and is
  not modelled.

## What is modelled

Every function of `PriorityTree`: the three views, `push`, `setup`, `getRoot`,
`isHistoricalRoot`, `processBatch`, `skipUntil`, `initFromCommitment`, `l1Reinit`,
`checkGWReinit`, `getCommitment`. `TreeLabel`/`TreeRun` are the tree transitions a deployed chain
performs after initialization: `push` (Mailbox), `processBatch` (Executor), and the two
re-initializations of `Migrator.forwardedBridgeMint` on an already deployed chain. `skipUntil` has
no caller at this commit and is not a label.

## What is not

That `DIM.push` computes the Merkle root of the pushed leaves: that is the
`DynamicIncrementalMerkle` library's own correctness, a different model. Nothing here depends on
it. `Merkle.calculateRootPaths`. The callers' own guards (Executor, Migrator).
-/

namespace Contracts.MailboxFacet

/-- `2^256`: one past the largest `uint256`. -/
def wordLimit : ℕ := 2 ^ 256

/-- The result of a checked `uint256` operation whose exact value is `n`: a revert (`none`) when
`n` does not fit. -/
def checked (n : ℕ) : Option ℕ := if n < wordLimit then some n else none

/-- `Merkle.efficientHash`: the hash of two `bytes32`. A parameter. -/
abbrev NodeHash := UInt256 → UInt256 → UInt256

/-! ## `DynamicIncrementalMerkle.Bytes32PushTree` -/

/-- `Bytes32PushTree` (`DIM:40-44`). -/
structure PushTree where
  /-- `_nextLeafIndex`. -/
  nextLeafIndex : ℕ
  /-- `_sides`. -/
  sides : List UInt256
  /-- `_zeros`. -/
  zeros : List UInt256

namespace PushTree

/-- `setup(zero)` (`DIM:53-58`): reset the counter, push `zero` onto `_zeros` and `0` onto
`_sides`, return `bytes32(0)`. The source does not clear the arrays first. -/
def setup (t : PushTree) (zero : UInt256) : PushTree × UInt256 :=
  ({ nextLeafIndex := 0, sides := t.sides ++ [0], zeros := t.zeros ++ [zero] }, 0)

/-- `root()` (`DIM:161-163`): the last entry of `_sides`. On empty `_sides` the source reverts
(`length - 1` underflows); the model reads `0` there. -/
def root (t : PushTree) : UInt256 := t.sides.getD (t.sides.length - 1) 0

/-- `1 << levels` on a `uint256` (`DIM:102`): `0` from 256 levels on. -/
def shl1 (levels : ℕ) : ℕ := if levels < 256 then 2 ^ levels else 0

/-- "Check if tree is full" (`DIM:102`): `index == 1 << levels`, with `levels = _zeros.length - 1`
(`DIM:95`). -/
def Grows (t : PushTree) : Prop := t.nextLeafIndex = shl1 (t.zeros.length - 1)

instance (t : PushTree) : Decidable t.Grows := by unfold Grows; infer_instance

/-- `_zeros` after the growth branch (`DIM:102-108`): one more level, `hash(zero, zero)` of the
last, when the tree is full. -/
def pushZeros (h : NodeHash) (t : PushTree) : List UInt256 :=
  if t.Grows then
    t.zeros ++ [h (t.zeros.getD (t.zeros.length - 1) 0) (t.zeros.getD (t.zeros.length - 1) 0)]
  else t.zeros

/-- `_sides` after the growth branch (`DIM:106`): one more `bytes32(0)` when the tree is full. -/
def pushSides (t : PushTree) : List UInt256 := if t.Grows then t.sides ++ [0] else t.sides

/-- The local state of the loop "Rebuild branch from leaf to root" (`DIM:111-133`). -/
structure Walk where
  /-- `currentIndex`. -/
  index : ℕ
  /-- `currentLevelHash`. -/
  hash : UInt256
  /-- `updatedSides`. -/
  updatedSides : Bool
  /-- `_sides` as written so far. -/
  sides : List UInt256

/-- One iteration at level `i` (`DIM:114-133`). A left child is saved to `_sides[i]` the first
time one is met, and hashed with the level's zero; a right child is hashed with `_sides[i]`. -/
def walkStep (h : NodeHash) (zeros : List UInt256) (w : Walk) (i : ℕ) : Walk :=
  if w.index % 2 = 0 then
    { index := w.index / 2
      hash := h w.hash (zeros.getD i 0)
      updatedSides := true
      sides := if w.updatedSides then w.sides else w.sides.set i w.hash }
  else
    { index := w.index / 2
      hash := h (w.sides.getD i 0) w.hash
      updatedSides := w.updatedSides
      sides := w.sides }

/-- The loop over levels `0 .. levels - 1`, where `levels` is `_zeros.length - 1` after the growth
branch. -/
def walk (h : NodeHash) (t : PushTree) (leaf : UInt256) : Walk :=
  (List.range ((pushZeros h t).length - 1)).foldl (walkStep h (pushZeros h t))
    ⟨t.nextLeafIndex, leaf, false, pushSides t⟩

/-- `push(leaf)` (`DIM:93-137`), returning the new tree and `newRoot`. Reverts: `_zeros.length - 1`
on an empty array (`DIM:95`), and `_nextLeafIndex++` at `2^256 - 1` (`DIM:99`). The last write is
`_sides[levels] = currentLevelHash` (`DIM:135`). -/
def push (h : NodeHash) (t : PushTree) (leaf : UInt256) : Option (PushTree × UInt256) :=
  if t.zeros.length = 0 then none
  else if wordLimit ≤ t.nextLeafIndex + 1 then none
  else
    some
      ({ nextLeafIndex := t.nextLeafIndex + 1
         sides := (walk h t leaf).sides.set ((pushZeros h t).length - 1) (walk h t leaf).hash
         zeros := pushZeros h t },
        (walk h t leaf).hash)

end PushTree

/-! ## `PriorityTree.Tree` -/

/-- `PriorityTree.Tree` (`PT:28-33`). -/
structure PTree where
  /-- `startIndex`: "priority tree started accepting priority ops from this index". -/
  startIndex : ℕ
  /-- `unprocessedIndex`, "relative to `startIndex`". -/
  unprocessedIndex : ℕ
  /-- `historicalRoots`. -/
  historicalRoots : UInt256 → Bool
  /-- `tree`. -/
  tree : PushTree

/-- `PriorityTreeCommitment` (`common/Config.sol:226-231`). -/
structure Commitment where
  nextLeafIndex : ℕ
  startIndex : ℕ
  unprocessedIndex : ℕ
  sides : List UInt256

/-- `PriorityOpsBatchInfo` (`PT:16-20`). -/
structure BatchInfo where
  leftPath : List UInt256
  rightPath : List UInt256
  itemHashes : List UInt256

/-- `Merkle.calculateRootPaths(leftPath, rightPath, startIndex, itemHashes)`: `none` is a revert.
A parameter. -/
abbrev RootPaths := List UInt256 → List UInt256 → ℕ → List UInt256 → Option UInt256

/-- The hash-like parameters of the tree. -/
structure TreeParams where
  /-- `Merkle.efficientHash`. -/
  node : NodeHash
  /-- `ZERO_LEAF_HASH = keccak256("")` (`PT:22`). -/
  zeroLeaf : UInt256
  /-- `Merkle.calculateRootPaths`. -/
  rootPaths : RootPaths

/-- `historicalRoots[r] = true`. -/
def markRoot (roots : UInt256 → Bool) (r : UInt256) : UInt256 → Bool :=
  fun x => if x = r then true else roots x

namespace PTree

/-- `getFirstUnprocessedPriorityTx` (`PT:37-39`). -/
def getFirstUnprocessedPriorityTx (t : PTree) : Option ℕ :=
  checked (t.startIndex + t.unprocessedIndex)

/-- `getTotalPriorityTxs` (`PT:42-44`). -/
def getTotalPriorityTxs (t : PTree) : Option ℕ := checked (t.startIndex + t.tree.nextLeafIndex)

/-- `getSize` (`PT:47-49`): the checked subtraction reverts when more is processed than pushed. -/
def getSize (t : PTree) : Option ℕ :=
  if t.unprocessedIndex ≤ t.tree.nextLeafIndex then
    some (t.tree.nextLeafIndex - t.unprocessedIndex)
  else none

/-- `push(hash)` (`PT:52-56`): push into the tree and record the new root as historical. -/
def push (P : TreeParams) (t : PTree) (hash : UInt256) : Option PTree :=
  match t.tree.push P.node hash with
  | none => none
  | some (tree, newRoot) =>
      some { t with tree := tree, historicalRoots := markRoot t.historicalRoots newRoot }

/-- `setup(startIndex)` (`PT:59-63`). -/
def setup (P : TreeParams) (t : PTree) (startIndex : ℕ) : PTree :=
  { t with
    tree := (t.tree.setup P.zeroLeaf).1
    historicalRoots := markRoot t.historicalRoots (t.tree.setup P.zeroLeaf).2
    startIndex := startIndex }

/-- `getRoot` (`PT:66-68`). -/
def getRoot (t : PTree) : UInt256 := t.tree.root

/-- `isHistoricalRoot` (`PT:72-74`). -/
def isHistoricalRoot (t : PTree) (r : UInt256) : Bool := t.historicalRoots r

/-- `processBatch` (`PT:83-96`). With no items it does nothing. Otherwise the root recomputed from
the items at positions `unprocessedIndex ..` must be a historical root, and `unprocessedIndex`
advances by the number of items (checked `+=`). -/
def processBatch (P : TreeParams) (t : PTree) (info : BatchInfo) : Option PTree :=
  if info.itemHashes.length = 0 then some t
  else
    match P.rootPaths info.leftPath info.rightPath t.unprocessedIndex info.itemHashes with
    | none => none
    | some expectedRoot =>
        if t.historicalRoots expectedRoot = false then none
        else
          match checked (t.unprocessedIndex + info.itemHashes.length) with
          | none => none
          | some u => some { t with unprocessedIndex := u }

/-- `skipUntil` (`PT:101-113`). No caller at this commit. -/
def skipUntil (t : PTree) (lastUnprocessed : ℕ) : PTree :=
  if t.startIndex > lastUnprocessed then t
  else if lastUnprocessed - t.startIndex ≤ t.unprocessedIndex then t
  else { t with unprocessedIndex := lastUnprocessed - t.startIndex }

/-- `_zeros` as `initFromCommitment` fills it (`PT:125-130`): `height` entries, the padding leaf
and its repeated self-hashes. -/
def zeroCascade (P : TreeParams) (height : ℕ) : List UInt256 :=
  List.iterate (fun z => P.node z z) P.zeroLeaf height

/-- `initFromCommitment` (`PT:116-132`): reverts on an empty `sides`; otherwise overwrites the
three counters, `_sides` and `_zeros`, and records the resulting root as historical. Earlier
historical roots stay. -/
def initFromCommitment (P : TreeParams) (t : PTree) (c : Commitment) : Option PTree :=
  if c.sides.length = 0 then none
  else
    some
      { startIndex := c.startIndex
        unprocessedIndex := c.unprocessedIndex
        tree :=
          { nextLeafIndex := c.nextLeafIndex, sides := c.sides,
            zeros := zeroCascade P c.sides.length }
        historicalRoots :=
          markRoot t.historicalRoots
            (PushTree.root
              { nextLeafIndex := c.nextLeafIndex, sides := c.sides,
                zeros := zeroCascade P c.sides.length }) }

/-- `l1Reinit` (`PT:135-147`): three guards in source order, then only `unprocessedIndex` is
written. -/
def l1Reinit (t : PTree) (c : Commitment) : Option PTree :=
  if t.startIndex ≠ c.startIndex then none
  else if t.unprocessedIndex > c.unprocessedIndex then none
  else if t.tree.nextLeafIndex < c.nextLeafIndex then none
  else some { t with unprocessedIndex := c.unprocessedIndex }

/-- `checkGWReinit` (`PT:150-160`): the three guards; `true` when none reverts. -/
def checkGWReinit (t : PTree) (c : Commitment) : Bool :=
  decide (t.startIndex = c.startIndex) && decide (t.unprocessedIndex ≤ c.unprocessedIndex)
    && decide (t.tree.nextLeafIndex ≤ c.nextLeafIndex)

/-- `getCommitment` (`PT:163-168`). -/
def getCommitment (t : PTree) : Commitment :=
  { nextLeafIndex := t.tree.nextLeafIndex, startIndex := t.startIndex,
    unprocessedIndex := t.unprocessedIndex, sides := t.tree.sides }

/-- The re-initialization of an already deployed chain on a settlement layer other than L1
(`state-transition/chain-deps/facets/Migrator.sol:284-289`): `checkGWReinit`, then
`initFromCommitment`. -/
def gwReinit (P : TreeParams) (t : PTree) (c : Commitment) : Option PTree :=
  if t.checkGWReinit c = true then t.initFromCommitment P c else none

end PTree

/-! ## The tree's transitions on a deployed chain -/

/-- One state-changing call into the chain's priority tree after its initialization. -/
inductive TreeLabel where
  /-- `push` from `MailboxFacet._writePriorityOpHash`
  (`state-transition/chain-deps/facets/Mailbox.sol:374`). -/
  | push (hash : UInt256)
  /-- `processBatch` from `Executor._executeOneBatch`
  (`state-transition/chain-deps/facets/Executor.sol:98`). -/
  | processBatch (info : BatchInfo)
  /-- `l1Reinit` from `Migrator.forwardedBridgeMint` on L1 (`Migrator.sol:283`). -/
  | l1Reinit (c : Commitment)
  /-- `checkGWReinit` and `initFromCommitment` from `Migrator.forwardedBridgeMint` off L1 on an
  already deployed chain (`Migrator.sol:288-289`). -/
  | gwReinit (c : Commitment)

/-- The tree after one call; `none` is a revert. -/
def PTree.apply (P : TreeParams) (t : PTree) : TreeLabel → Option PTree
  | .push hash => t.push P hash
  | .processBatch info => t.processBatch P info
  | .l1Reinit c => t.l1Reinit c
  | .gwReinit c => t.gwReinit P c

/-- A run of successful calls, in order. -/
inductive TreeRun (P : TreeParams) : PTree → List TreeLabel → PTree → Prop
  | nil (t : PTree) : TreeRun P t [] t
  | snoc {t u v : PTree} {ls : List TreeLabel} (l : TreeLabel) :
      TreeRun P t ls u → u.apply P l = some v → TreeRun P t (ls ++ [l]) v

/-- The shape `DynamicIncrementalMerkle` relies on: `_sides` and `_zeros` have the same nonzero
length, so `push` and `root` stay in bounds; and the tree's current root is recorded as
historical. -/
structure PTree.WellFormed (t : PTree) : Prop where
  sameLength : t.tree.sides.length = t.tree.zeros.length
  nonempty : 0 < t.tree.zeros.length
  rootHistorical : t.historicalRoots t.tree.root = true

/-- What the caller is trusted for at one call, where the library's own guards do not bound
`unprocessedIndex` by the number of pushed leaves.

* `processBatch`: the items are leaves that were pushed. `PT:77-82` states this reliance: the
  function "only checks that a certain segment of items is present in the tree", padding leaves
  included.
* `l1Reinit`, `gwReinit`: the commitment does not claim more processed than pushed. -/
def TreeLabel.Consistent (t : PTree) : TreeLabel → Prop
  | .push _ => True
  | .processBatch info => t.unprocessedIndex + info.itemHashes.length ≤ t.tree.nextLeafIndex
  | .l1Reinit c => c.unprocessedIndex ≤ c.nextLeafIndex
  | .gwReinit c => c.unprocessedIndex ≤ c.nextLeafIndex

/-- A run in which every call is `Consistent` with the tree it is made on. -/
inductive ConsistentRun (P : TreeParams) : PTree → List TreeLabel → PTree → Prop
  | nil (t : PTree) : ConsistentRun P t [] t
  | snoc {t u v : PTree} {ls : List TreeLabel} (l : TreeLabel) :
      ConsistentRun P t ls u → l.Consistent u → u.apply P l = some v →
      ConsistentRun P t (ls ++ [l]) v

/-! ## Witness data -/

/-- A node hash for the witnesses: addition. -/
def wNode : NodeHash := fun a b => a + b

/-- Witness parameters: `wNode`, padding leaf `7`, and a `calculateRootPaths` that returns `0`
(the root `setup` records) for every input. -/
def wParams : TreeParams := { node := wNode, zeroLeaf := 7, rootPaths := fun _ _ _ _ => some 0 }

/-- All-zero storage. -/
def emptyTree : PTree :=
  { startIndex := 0, unprocessedIndex := 0, historicalRoots := fun _ => false,
    tree := { nextLeafIndex := 0, sides := [], zeros := [] } }

/-- A fresh tree as `DiamondInit` leaves it (`state-transition/chain-deps/DiamondInit.sol:137`),
with start index `5`. -/
def wFresh : PTree := emptyTree.setup wParams 5

end Contracts.MailboxFacet
