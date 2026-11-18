import EraSpec.Contracts.Merkle.Specs.RootPaths

/-!
# Contract spec: `PriorityTree.processBatch` and the Executor's priority-operation step

Source: era-contracts `draft/v0.35.0` head `b17415d20`, under `l1-contracts/contracts/`:

* `state-transition/libraries/PriorityTree.sol` (`PT`), identical at `main` `70096e2ea`;
* `state-transition/chain-deps/facets/Executor.sol` (`Ex`); at `main` `70096e2ea` the lines
  cited as `Ex:92-98` below are `:89-95`;
* `common/libraries/Merkle.sol`, through `MerkleSpec.RootPaths.rootPathsMem`
  (`../../Merkle/Specs/RootPaths.lean`).

    function processBatch(Tree storage _tree, PriorityOpsBatchInfo memory _priorityOpsData) internal {  // PT:83
        if (_priorityOpsData.itemHashes.length > 0) {                                                  // PT:84
            bytes32 expectedRoot = Merkle.calculateRootPaths(
                _priorityOpsData.leftPath, _priorityOpsData.rightPath,
                _tree.unprocessedIndex, _priorityOpsData.itemHashes);                                  // PT:85-90
            if (!_tree.historicalRoots[expectedRoot]) revert NotHistoricalRoot(expectedRoot);          // PT:91-93
            _tree.unprocessedIndex += _priorityOpsData.itemHashes.length;                              // PT:94
        }
    }

and in `ExecutorFacet._executeOneBatch` (`Ex:86-114`):

    if (_priorityOpsData.itemHashes.length != _storedBatch.numberOfLayer1Txs) revert …;   // Ex:92-94
    bytes32 priorityOperationsHash = _rollingHash(_priorityOpsData.itemHashes);          // Ex:95
    bytes32 dependencyRootsRollingHash = _verifyDependencyInteropRoots(_dependencyRoots); // Ex:96
    _checkBatchData(_storedBatch, _executedBatchIdx, priorityOperationsHash, …);         // Ex:97
    s.priorityTree.processBatch(_priorityOpsData);                                       // Ex:98

`_rollingHash` (`Ex:48-55`) starts from `EMPTY_STRING_KECCAK` (`common/Config.sol:6`) and
folds `hash = keccak256(abi.encode(hash, item))` over the items; `_checkBatchData` compares the
result with the stored batch's `priorityOperationsHash` (`Ex:70-72`).

**This file is definitions only.** Statements are in `../Properties/SegmentBinding.lean`,
proofs in `../Proofs/SegmentBinding.lean`.

## The model

* `processBatch` transcribes `PT:83-96` on the two fields it touches: `unprocessedIndex` (a
  `uint256`, here `ℕ`, with the checked `+=` of `PT:94` as a revert at `2^256`) and the mapping
  `historicalRoots` (`roots : UInt256 → Bool`). It returns the new `unprocessedIndex` and the
  final contents of `itemHashes`: `calculateRootPaths` writes into the caller's array
  (`Merkle.sol:103`, `MerkleSpec.RootPaths.rootPathsMem`), and `PT:94` reads that array's length
  after the call.
* `executePriority` is the priority-operation part of `_executeOneBatch`: `Ex:92-95`, the
  comparison of `Ex:70-72`, and `Ex:98`. The other checks of `_checkBatchData` and
  `_verifyDependencyInteropRoots` only reject, and are omitted; so are the steps after
  `Ex:98`, which do not read `_priorityOpsData`. `keccak256(abi.encode(hash, item))` is an
  abstract `kpair`, `EMPTY_STRING_KECCAK` an abstract `e0`.
* `executePriorityHashAfter` is a variant with `Ex:95` moved after `Ex:98`, for one
  countermodel only.

## The historical roots, as a premise

`RootsAreLoggedPrefixRoots h z roots Q log` says: `log` is a finite list of trees `(m, H)`, each
the first `m ≤ Q.length` queued hashes of `Q` (padding `z`) at a height `H`; and every recorded
root is `bytes32(0)` or the root `MerkleSpec.rootOf h z (Q.take m) H` of a logged tree.
The breaks located below are against a logged tree, so they are pinned to the run's own trees.
Where the roots come from:

* `setup` (`PT:59-63`) records the value `DynamicIncrementalMerkle.setup` returns, which is
  `bytes32(0)` (`common/libraries/DynamicIncrementalMerkle.sol:53-58`), not the padded root of
  an empty tree. `PT:22` fixes the padding `z = ZERO_LEAF_HASH = keccak256("")`.
* `push` (`PT:52-56`) records each root `DynamicIncrementalMerkle.push` returns. That this root
  is `rootOf h z (Q.take m) H` for the `m` hashes pushed so far, at the least `H` with
  `m ≤ 2^H`, is `DynamicIncrementalMerkle`'s own correctness. It is **not proved in this
  package**; the unmerged branch `origin/cov2/merkle-libs` states it
  (`PushRunHeightIsMinimal`) without a finished proof. With it, a run of `setup` and pushes
  meets this premise with `log = [(m, least H with m ≤ 2^H) | m = 1, …, Q.length]`; `Q` is the
  list of pushed hashes, which only grows, so one premise on the final `Q` covers every root
  recorded along the run.
* `initFromCommitment` (`PT:116-132`, called from `Migrator.sol:289`, `:291`) records the root of
  a supplied commitment. The premise says nothing about such roots: a chain re-initialised that
  way is outside these results.
-/

namespace Contracts.PriorityTree.SegmentBinding

open Clear MerkleSpec MerkleSpec.Verifier MerkleSpec.RootPaths

/-- `PriorityOpsBatchInfo` (`PT:16-20`). -/
structure BatchInfo where
  /-- `leftPath`: the start path passed to `calculateRootPaths`. -/
  leftPath : List UInt256
  /-- `rightPath`: the end path. -/
  rightPath : List UInt256
  /-- `itemHashes`: the priority operations' hashes. -/
  itemHashes : List UInt256

/-- **`processBatch` (`PT:83-96`)** with `unprocessedIndex = u` and `historicalRoots = roots`.
`none` is a revert: of `calculateRootPaths`, `NotHistoricalRoot` (`PT:91-93`), or the checked
`+=` (`PT:94`). Otherwise the new `unprocessedIndex` and the final contents of `itemHashes`.
`PT:94` adds the length of the array as `calculateRootPaths` left it. -/
def processBatch (h : Hash) (roots : UInt256 → Bool) (u : ℕ) (info : BatchInfo) :
    Option (ℕ × List UInt256) :=
  if 0 < info.itemHashes.length then
    match rootPathsMem h info.leftPath info.rightPath u info.itemHashes with
    | none => none
    | some (r, mem) =>
      if roots r = true then
        (if u + mem.length < wordLimit then some (u + mem.length, mem) else none)
      else none
  else some (u, info.itemHashes)

/-- `_rollingHash` (`Ex:48-55`): `hash = keccak256(abi.encode(hash, item))` from
`EMPTY_STRING_KECCAK`, with `kpair` for the keccak of the encoded pair and `e0` for the start. -/
def rollingHash (kpair : UInt256 → UInt256 → UInt256) (e0 : UInt256) (items : List UInt256) :
    UInt256 :=
  items.foldl kpair e0

/-- **The priority-operation part of `_executeOneBatch`** with the stored batch's
`numberOfLayer1Txs = nL1` and `priorityOperationsHash = poh`: the count check (`Ex:92-94`), the
rolling hash of the submitted items (`Ex:95`) compared with `poh` (`Ex:97`, `Ex:70-72`), then
`processBatch` (`Ex:98`). -/
def executePriority (h : Hash) (kpair : UInt256 → UInt256 → UInt256) (e0 : UInt256)
    (roots : UInt256 → Bool) (u nL1 : ℕ) (poh : UInt256) (info : BatchInfo) :
    Option (ℕ × List UInt256) :=
  if info.itemHashes.length ≠ nL1 then none
  else if rollingHash kpair e0 info.itemHashes ≠ poh then none
  else processBatch h roots u info

/-- A variant with the rolling hash (`Ex:95`) computed after `processBatch` (`Ex:98`), from the
array that call leaves. For the countermodel `HashAfterCallRejectsHonestBatch` only. -/
def executePriorityHashAfter (h : Hash) (kpair : UInt256 → UInt256 → UInt256) (e0 : UInt256)
    (roots : UInt256 → Bool) (u nL1 : ℕ) (poh : UInt256) (info : BatchInfo) :
    Option (ℕ × List UInt256) :=
  if info.itemHashes.length ≠ nL1 then none
  else
    match processBatch h roots u info with
    | none => none
    | some (u', mem) => if rollingHash kpair e0 mem ≠ poh then none else some (u', mem)

/-! ## The historical roots and the queue -/

/-- **The recorded roots are `setup`'s and those of logged queue prefixes.** Every logged tree
`(m, H)` is the first `m ≤ Q.length` hashes of `Q` at a height `H`, and every root `r` with
`roots r = true` is `bytes32(0)` or the root (padding `z`) of a logged tree. See the module
docstring for which source paths establish it. -/
def RootsAreLoggedPrefixRoots (h : Hash) (z : UInt256) (roots : UInt256 → Bool)
    (Q : List UInt256) (log : List (ℕ × ℕ)) : Prop :=
  (∀ p ∈ log, p.1 ≤ Q.length)
  ∧ ∀ r, roots r = true → r = 0 ∨ ∃ p ∈ log, r = rootOf h z (Q.take p.1) p.2

/-- `items` are the queue entries `Q[u], …, Q[u + n - 1]`, all inside the queue. (The shape of
`SegmentOk` on the unmerged branch `origin/cov/executor`.) -/
def IsQueueSegment (Q : List UInt256) (u : ℕ) (items : List UInt256) : Prop :=
  u + items.length ≤ Q.length ∧ (Q.drop u).take items.length = items

instance (Q : List UInt256) (u : ℕ) (items : List UInt256) :
    Decidable (IsQueueSegment Q u items) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **A located break against one recorded tree.** For the batch `info` at start index `u`,
against the tree over `L` at height `H`: the paths have length `H` and some item's walk
exhibits a `PathCollision`, or the paths do not have length `H` and every item's walk exhibits
a `HeightBreak` (`MerkleSpec.RootPaths.Properties.RootPathsAnyLengthOrBreak`). -/
def TreeBreak (h : Hash) (z : UInt256) (L : List UInt256) (H u : ℕ) (info : BatchInfo) : Prop :=
  (info.leftPath.length = H ∧ ∃ i, i < info.itemHashes.length ∧
      PathCollision h z L (rangeSib h info.leftPath info.rightPath u info.itemHashes (u + i)) 0 H
        (u + i) (info.itemHashes.getD i 0))
  ∨ (info.leftPath.length ≠ H ∧ ∀ i, i < info.itemHashes.length →
      HeightBreak h z L (rangeSib h info.leftPath info.rightPath u info.itemHashes (u + i))
        info.leftPath.length H (u + i) (info.itemHashes.getD i 0))

/-- **A located break on one batch.** The batch's recomputed root is `bytes32(0)`, the root
`setup` records; or it is the root of a logged tree `(m, H)` (the first `m` queued hashes at
height `H`), and there is a `TreeBreak` against that tree. -/
def BatchBreak (h : Hash) (z : UInt256) (Q : List UInt256) (log : List (ℕ × ℕ)) (u : ℕ)
    (info : BatchInfo) : Prop :=
  rootPaths h info.leftPath info.rightPath u info.itemHashes = some 0
  ∨ ∃ p ∈ log,
      rootPaths h info.leftPath info.rightPath u info.itemHashes
          = some (rootOf h z (Q.take p.1) p.2)
      ∧ TreeBreak h z (Q.take p.1) p.2 u info

/-- **Successive successful `processBatch` calls**, each recorded with the `unprocessedIndex` it
started from: `ProcessRun h roots u₀ steps u₁` runs `steps` from `u₀` and ends at `u₁`.
`roots` is fixed; a run whose roots grow is covered by taking the final set
(`Properties.ProcessBatchMonotoneInRoots`). Only `processBatch` moves the index here: the
migration paths that set `unprocessedIndex` directly (`l1Reinit`, `PT:135-147`;
`initFromCommitment`, `PT:116-132`) are not steps of a run. -/
inductive ProcessRun (h : Hash) (roots : UInt256 → Bool) : ℕ → List (ℕ × BatchInfo) → ℕ → Prop
  | nil (u : ℕ) : ProcessRun h roots u [] u
  | cons {u u' u'' : ℕ} {info : BatchInfo} {mem : List UInt256} {rest : List (ℕ × BatchInfo)} :
      processBatch h roots u info = some (u', mem) → ProcessRun h roots u' rest u'' →
      ProcessRun h roots u ((u, info) :: rest) u''

/-- All item hashes of a run, in order. -/
def runItems (steps : List (ℕ × BatchInfo)) : List UInt256 :=
  steps.flatMap fun p => p.2.itemHashes

/-! ## A concrete queue, for the witnesses only -/

/-- The queue `[11, 12, 13]`. -/
def witnessQueue : List UInt256 := [11, 12, 13]

/-- The trees `(m, H)` = `(1, 0)`, `(2, 1)`, `(3, 2)`: each prefix of `witnessQueue` at the least
height that holds it. -/
def witnessLog : List (ℕ × ℕ) := [(1, 0), (2, 1), (3, 2)]

/-- `bytes32(0)` and the roots of the trees in `witnessLog`, padding `7`, under `rangeToyHash`
(`11`, `46` and `186`): roots of the shape `RootsAreLoggedPrefixRoots` allows. -/
def witnessRoots : UInt256 → Bool := fun r =>
  r == 0 || r == rootOf rangeToyHash 7 (witnessQueue.take 1) 0
    || r == rootOf rangeToyHash 7 (witnessQueue.take 2) 1
    || r == rootOf rangeToyHash 7 (witnessQueue.take 3) 2

end Contracts.PriorityTree.SegmentBinding
