import EraSpec.Contracts.PriorityTree.Specs.SegmentBinding

/-!
# Properties: a processed batch is the queue segment at `unprocessedIndex`, or a located break

Statements about `../Specs/SegmentBinding.lean` (`PriorityTree.processBatch` and the
priority-operation step of `ExecutorFacet._executeOneBatch` at `b17415d20`), built on
`MerkleSpec.RootPaths` (`../../Merkle/Properties/RootPaths.lean`). Proofs:
`../Proofs/SegmentBinding.lean`. No statement takes a hash premise.

* **Frame.** `ProcessBatchAdvancesByLength`, `ExecutePriorityHashesSubmittedItems`, and the
  countermodel `HashAfterCallRejectsHonestBatch`.
* **One batch.** `ProcessBatchSegmentOrBreak`, and with no item equal to the padding value
  `ProcessBatchQueueSegmentOrBreak`.
* **A run of batches.** `ProcessedRunIsQueueSegmentOrBreak` (headline),
  `ProcessBatchMonotoneInRoots`.
* **The breaks.** `SetupRootHitCases`, `HonestBatchNoTreeBreak`, `SegmentBindingWitness`, and
  the countermodels `PaddingItemsAdvancePastQueue`, `SetupRootAcceptsZeroItem`.
-/

namespace Contracts.PriorityTree.SegmentBinding

open Clear MerkleSpec MerkleSpec.Verifier MerkleSpec.RootPaths

/-! ## Frame -/

/-- **(e) `processBatch` ADVANCES BY THE NUMBER OF ITEMS.** A successful call sets
`unprocessedIndex` to `u + n` for the `n` submitted items, and leaves an array of length `n`:
`calculateRootPaths` overwrote entries of the array in place but not its length, which is all
`PT:94` reads afterwards. With at least one item, the call's recomputed root is a recorded root
and the array left behind is the one `calculateRootPaths` leaves. -/
def Properties.ProcessBatchAdvancesByLength : Prop :=
  ∀ (h : Hash) (roots : UInt256 → Bool) (u : ℕ) (info : BatchInfo) (u' : ℕ) (mem : List UInt256),
    processBatch h roots u info = some (u', mem) →
      u' = u + info.itemHashes.length ∧ mem.length = info.itemHashes.length
      ∧ (0 < info.itemHashes.length →
          ∃ r, rootPathsMem h info.leftPath info.rightPath u info.itemHashes = some (r, mem)
            ∧ roots r = true)

/-- **(e) THE EXECUTOR HASHES THE ITEMS AS SUBMITTED.** A successful priority-operation step
checked the count and the rolling hash of the submitted items (`Ex:92-95`, `Ex:70-72`) before
`processBatch` (`Ex:98`) overwrote them, and its result is that call's result. -/
def Properties.ExecutePriorityHashesSubmittedItems : Prop :=
  ∀ (h : Hash) (kpair : UInt256 → UInt256 → UInt256) (e0 : UInt256) (roots : UInt256 → Bool)
    (u nL1 : ℕ) (poh : UInt256) (info : BatchInfo) (u' : ℕ) (mem : List UInt256),
    executePriority h kpair e0 roots u nL1 poh info = some (u', mem) →
      info.itemHashes.length = nL1 ∧ rollingHash kpair e0 info.itemHashes = poh
      ∧ processBatch h roots u info = some (u', mem)

/-- **COUNTERMODEL: HASHING AFTER THE CALL READS THE OVERWRITTEN ITEMS.** Under `rangeToyHash`
with the rolling-hash pair function `sumHash` and start value `5`: the batch with items
`[1, 2]` and one-entry paths, at `unprocessedIndex = 0`, against the recorded root `6`, with
`numberOfLayer1Txs = 2` and the stored `priorityOperationsHash` equal to the rolling hash of
`[1, 2]`, passes the deployed order; with the rolling hash moved after `processBatch` it is
rejected, because `calculateRootPaths` left `[6, 2]` in the array. So the order `Ex:95` before
`Ex:98` is load-bearing. -/
def Properties.HashAfterCallRejectsHonestBatch : Prop :=
  executePriority rangeToyHash MerkleSpec.Pinned.sumHash 5 (fun r => r == 6) 0 2
      (rollingHash MerkleSpec.Pinned.sumHash 5 [1, 2]) ⟨[0], [0], [1, 2]⟩ = some (2, [6, 2])
    ∧ executePriorityHashAfter rangeToyHash MerkleSpec.Pinned.sumHash 5 (fun r => r == 6) 0 2
      (rollingHash MerkleSpec.Pinned.sumHash 5 [1, 2]) ⟨[0], [0], [1, 2]⟩ = none

/-! ## One batch -/

/-- **ONE BATCH: THE TREE'S ENTRIES AT `unprocessedIndex`, OR A LOCATED BREAK.** Under
`RootsAreLoggedPrefixRoots`, a successful `processBatch` with `n ≥ 1` items at
`unprocessedIndex = u` sets it to `u + n`, and its recomputed root is `bytes32(0)` (the root
`setup` records), or the root of a logged tree `(m, H)`, against which either the paths have
length `H` and the items are that tree's level-0 entries `[u, u + n)` (the padding `z` at
indices `≥ m`), or there is a `TreeBreak`. -/
def Properties.ProcessBatchSegmentOrBreak : Prop :=
  ∀ (h : Hash) (z : UInt256) (roots : UInt256 → Bool) (Q : List UInt256) (log : List (ℕ × ℕ))
    (u : ℕ) (info : BatchInfo) (u' : ℕ) (mem : List UInt256),
    RootsAreLoggedPrefixRoots h z roots Q log →
    processBatch h roots u info = some (u', mem) → 0 < info.itemHashes.length →
      u' = u + info.itemHashes.length
      ∧ (rootPaths h info.leftPath info.rightPath u info.itemHashes = some 0
        ∨ ∃ p ∈ log,
            rootPaths h info.leftPath info.rightPath u info.itemHashes
              = some (rootOf h z (Q.take p.1) p.2)
            ∧ ((info.leftPath.length = p.2
                  ∧ info.itemHashes = treeSegment z (Q.take p.1) u info.itemHashes.length)
              ∨ TreeBreak h z (Q.take p.1) p.2 u info))

/-- **ONE BATCH, NO PADDING ITEM: THE QUEUE SEGMENT AT `unprocessedIndex`, OR A LOCATED BREAK.**
If moreover no item is the padding value `z`, the batch's items are the queued hashes
`Q[u], …, Q[u + n - 1]`, all inside the queue (`IsQueueSegment`), or there is a `BatchBreak`:
the recomputed root is `bytes32(0)`, or a `TreeBreak` against a logged tree whose root it is. -/
def Properties.ProcessBatchQueueSegmentOrBreak : Prop :=
  ∀ (h : Hash) (z : UInt256) (roots : UInt256 → Bool) (Q : List UInt256) (log : List (ℕ × ℕ))
    (u : ℕ) (info : BatchInfo) (u' : ℕ) (mem : List UInt256),
    RootsAreLoggedPrefixRoots h z roots Q log →
    processBatch h roots u info = some (u', mem) → 0 < info.itemHashes.length →
    z ∉ info.itemHashes →
      u' = u + info.itemHashes.length
      ∧ (IsQueueSegment Q u info.itemHashes ∨ BatchBreak h z Q log u info)

/-! ## A run of batches -/

/-- **(Headline) NO SKIPPING OR REORDERING OF PRIORITY OPERATIONS, UP TO A LOCATED BREAK.** Under
`RootsAreLoggedPrefixRoots`, for a run of successful `processBatch` calls from
`unprocessedIndex = u₀ ≤ Q.length` to `u₁`, none of whose items is the padding value `z`:
`u₁ = u₀ + N` for the `N` items processed, and the items of all batches, in order, are the
queued hashes `Q[u₀], …, Q[u₀ + N - 1]` (`IsQueueSegment`), or some batch, at the index it
started from, has a `BatchBreak`. -/
def Properties.ProcessedRunIsQueueSegmentOrBreak : Prop :=
  ∀ (h : Hash) (z : UInt256) (roots : UInt256 → Bool) (Q : List UInt256) (log : List (ℕ × ℕ))
    (u₀ : ℕ) (steps : List (ℕ × BatchInfo)) (u₁ : ℕ),
    RootsAreLoggedPrefixRoots h z roots Q log →
    ProcessRun h roots u₀ steps u₁ → u₀ ≤ Q.length →
    (∀ p ∈ steps, z ∉ p.2.itemHashes) →
      u₁ = u₀ + (runItems steps).length
      ∧ (IsQueueSegment Q u₀ (runItems steps) ∨ ∃ p ∈ steps, BatchBreak h z Q log p.1 p.2)

/-- **MORE RECORDED ROOTS ONLY ADD SUCCESSES.** A `processBatch` call that succeeds against
`roots` succeeds, with the same result, against any `roots'` recording at least those roots. A
run whose recorded roots grow between its calls is therefore a `ProcessRun` against the final
roots. -/
def Properties.ProcessBatchMonotoneInRoots : Prop :=
  ∀ (h : Hash) (roots roots' : UInt256 → Bool) (u : ℕ) (info : BatchInfo) (x : ℕ × List UInt256),
    (∀ r, roots r = true → roots' r = true) →
    processBatch h roots u info = some x → processBatch h roots' u info = some x

/-! ## The breaks -/

/-- **WHAT HITTING THE SETUP ROOT TAKES.** If `calculateRootPaths` returns `bytes32(0)`, then
either the paths are empty, the start index is 0 and the single item is `bytes32(0)`; or the
paths are nonempty and the last pair item 0's walk hashes (`walkPair`, a pair the loop hashed:
`RootPathsWalkPairsAreLoopPairs`) hashes to 0. -/
def Properties.SetupRootHitCases : Prop :=
  ∀ (h : Hash) (sp ep : List UInt256) (u : ℕ) (items : List UInt256),
    rootPaths h sp ep u items = some 0 →
      (sp = [] ∧ u = 0 ∧ items = [0])
      ∨ (sp ≠ [] ∧
          h (walkPair h (rangeSib h sp ep u items (u + 0)) 0 (u + 0) (items.getD 0 0)
              (sp.length - 1)).1
            (walkPair h (rangeSib h sp ep u items (u + 0)) 0 (u + 0) (items.getD 0 0)
              (sp.length - 1)).2 = 0)

/-- **AN HONEST BATCH HAS NO TREE BREAK, FOR EVERY HASH.** The batch with the tree's own paths
for indices `u` and `u + n - 1` and the tree's entries `[u, u + n)` as items has no `TreeBreak`
against that tree at its height (premises of `MerkleSpec.RootPaths.Properties.RootPathsComplete`).
So the `TreeBreak` disjuncts above are not tautologies. -/
def Properties.HonestBatchNoTreeBreak : Prop :=
  ∀ (h : Hash) (z : UInt256) (L : List UInt256) (H u n : ℕ),
    1 ≤ n → u + n ≤ 2 ^ H → H < 256 →
      ¬ TreeBreak h z L H u ⟨honestPath h z L u H, honestPath h z L (u + n - 1) H, treeSegment z L u n⟩

/-- **A CONCRETE RUN MEETING EVERY PREMISE, WITH NO BREAK.** The queue `[11, 12, 13]`, the
roots `witnessRoots` and the log `witnessLog` meet `RootsAreLoggedPrefixRoots` (padding `7`,
`rangeToyHash`). The run processes `[11]` at index 0 with empty paths (against the one-leaf
root) and `[12, 13]` at index 1 with the honest paths of the three-leaf tree at height 2; the
second call leaves `[186, 47]` in the caller's array. The run starts at `0 ≤ Q.length`, no item
is `7`, it ends at index 3, its items are the whole queue, a `IsQueueSegment` at 0, and neither
batch has a `BatchBreak`. This meets every premise of `ProcessBatchSegmentOrBreak`,
`ProcessBatchQueueSegmentOrBreak` and `ProcessedRunIsQueueSegmentOrBreak` (both batches have
items), with the segment disjunct holding and the break disjunct false. -/
def Properties.SegmentBindingWitness : Prop :=
  RootsAreLoggedPrefixRoots rangeToyHash 7 witnessRoots witnessQueue witnessLog
  ∧ processBatch rangeToyHash witnessRoots 0 ⟨[], [], [11]⟩ = some (1, [11])
  ∧ processBatch rangeToyHash witnessRoots 1
      ⟨honestPath rangeToyHash 7 witnessQueue 1 2, honestPath rangeToyHash 7 witnessQueue 2 2,
        [12, 13]⟩ = some (3, [186, 47])
  ∧ ProcessRun rangeToyHash witnessRoots 0
      [(0, ⟨[], [], [11]⟩),
       (1, ⟨honestPath rangeToyHash 7 witnessQueue 1 2, honestPath rangeToyHash 7 witnessQueue 2 2,
          [12, 13]⟩)] 3
  ∧ 0 ≤ witnessQueue.length
  ∧ (7 : UInt256) ∉ ([11] : List UInt256) ∧ (7 : UInt256) ∉ ([12, 13] : List UInt256)
  ∧ runItems
      [(0, ⟨[], [], [11]⟩),
       (1, ⟨honestPath rangeToyHash 7 witnessQueue 1 2, honestPath rangeToyHash 7 witnessQueue 2 2,
          [12, 13]⟩)] = witnessQueue
  ∧ IsQueueSegment witnessQueue 0 witnessQueue
  ∧ ¬ BatchBreak rangeToyHash 7 witnessQueue witnessLog 0 ⟨[], [], [11]⟩
  ∧ ¬ BatchBreak rangeToyHash 7 witnessQueue witnessLog 1
      ⟨honestPath rangeToyHash 7 witnessQueue 1 2, honestPath rangeToyHash 7 witnessQueue 2 2,
        [12, 13]⟩

/-- **COUNTERMODEL: PADDING ITEMS ARE PROCESSED PAST THE QUEUE.** With the premise met
(`witnessRoots`, `witnessLog`), the batch `[7]` (the padding value) at index 3, with the honest
paths of the padded slot 3 of the three-leaf tree at height 2, is accepted and moves
`unprocessedIndex` to 4, past the 3 queued hashes: no `IsQueueSegment`, and no `BatchBreak`.
So the premise "no item is the padding value" of `ProcessBatchQueueSegmentOrBreak` is
load-bearing. (The NatSpec of `processBatch`, `PT:77-82`, leaves item validity to the proof that
binds the rolling hash.) -/
def Properties.PaddingItemsAdvancePastQueue : Prop :=
  RootsAreLoggedPrefixRoots rangeToyHash 7 witnessRoots witnessQueue witnessLog
  ∧ processBatch rangeToyHash witnessRoots 3
      ⟨honestPath rangeToyHash 7 witnessQueue 3 2, honestPath rangeToyHash 7 witnessQueue 3 2, [7]⟩
      = some (4, [186])
  ∧ witnessQueue.length < 4
  ∧ ¬ IsQueueSegment witnessQueue 3 [7]
  ∧ ¬ BatchBreak rangeToyHash 7 witnessQueue witnessLog 3
      ⟨honestPath rangeToyHash 7 witnessQueue 3 2, honestPath rangeToyHash 7 witnessQueue 3 2, [7]⟩

/-- **COUNTERMODEL: THE SETUP ROOT ACCEPTS THE ITEM `bytes32(0)`.** With the premise met, the
batch `[0]` with empty paths at index 0 is accepted against the recorded root `bytes32(0)`
(`PT:59-63`) and moves `unprocessedIndex` to 1, though the first queued hash is `11`: the
`bytes32(0)` case of `BatchBreak` is reached. -/
def Properties.SetupRootAcceptsZeroItem : Prop :=
  RootsAreLoggedPrefixRoots rangeToyHash 7 witnessRoots witnessQueue witnessLog
  ∧ processBatch rangeToyHash witnessRoots 0 ⟨[], [], [0]⟩ = some (1, [0])
  ∧ ¬ IsQueueSegment witnessQueue 0 [0]
  ∧ BatchBreak rangeToyHash 7 witnessQueue witnessLog 0 ⟨[], [], [0]⟩

end Contracts.PriorityTree.SegmentBinding
