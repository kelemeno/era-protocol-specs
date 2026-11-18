# PriorityTree

Source: `l1-contracts/contracts/state-transition/libraries/PriorityTree.sol` at era-contracts
`b17415d20` (`draft/v0.35.0`; unchanged at `main` `70096e2ea`), with the priority-operation step
of `state-transition/chain-deps/facets/Executor.sol` (`_executeOneBatch`, `:92-98` at
`b17415d20`, `:89-95` at `70096e2ea`). The Merkle check it relies on, `Merkle.calculateRootPaths`,
is modelled in [`../Merkle/`](../Merkle/README.md) topic `RootPaths`.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| SegmentBinding | [Specs/SegmentBinding.lean](Specs/SegmentBinding.lean) | [Properties/SegmentBinding.lean](Properties/SegmentBinding.lean) | [Proofs/SegmentBinding.lean](Proofs/SegmentBinding.lean) |

`SegmentBinding` models `processBatch` on `unprocessedIndex` and `historicalRoots`, and the
Executor's count check, rolling hash and call. No hash premise anywhere.

- `processBatch` advances `unprocessedIndex` by the number of items: `calculateRootPaths`
  overwrote the item array in place but kept its length, the only thing read afterwards
  (`ProcessBatchAdvancesByLength`). The Executor hashes the items before the call
  (`ExecutePriorityHashesSubmittedItems`); hashing after it would read the overwritten array
  and reject an honest batch (`HashAfterCallRejectsHonestBatch`).
- The premise `RootsAreLoggedPrefixRoots` (ASSUMPTIONS.md `PROTO-PRIORITY-ROOTS`): every recorded
  root is `bytes32(0)`, which `setup` records, or the padded root of a logged tree: a prefix of
  the pushed hashes at some height. On a run of `setup` and pushes it follows from the
  `DynamicIncrementalMerkle` push correctness (log: each prefix at the least height that holds
  it), which this package does not prove; roots that `initFromCommitment` records are not
  covered.
- Under it, a successful batch at `unprocessedIndex = u` with `n ≥ 1` items moves the index to
  `u + n`, and its root is `bytes32(0)` or a logged tree's root against which the items are the
  tree's entries `[u, u + n)` (padding beyond the prefix) or there is a `TreeBreak`: a
  `PathCollision` on an item's walk, or, when the path length is not the tree's height, a
  `HeightBreak` on every item's walk (`ProcessBatchSegmentOrBreak`). With no item equal to the
  padding value the items are the queue entries `Q[u], …, Q[u + n - 1]` or there is a
  `BatchBreak` (`ProcessBatchQueueSegmentOrBreak`).
- Headline: along a run of batches from `u₀ ≤ Q.length`, with no padding item, the index ends at
  `u₀ + N` and the `N` processed items, in order, are `Q[u₀], …, Q[u₀ + N - 1]`, or some batch has
  a `BatchBreak` at the index it started from (`ProcessedRunIsQueueSegmentOrBreak`). A run
  whose roots grow is covered by its final roots (`ProcessBatchMonotoneInRoots`). Only
  `processBatch` moves the index in a run: `l1Reinit` and `initFromCommitment`, which set it on
  migration, are not steps.
- The breaks: a `bytes32(0)` root needs a single item `bytes32(0)` at index 0 with empty paths,
  or a pair the loop hashed that hashes to 0 (`SetupRootHitCases`); an honest batch has no
  `TreeBreak` for any hash (`HonestBatchNoTreeBreak`); `SegmentBindingWitness` meets every
  premise with the segment case holding and no `BatchBreak`. Countermodels:
  `PaddingItemsAdvancePastQueue` (padding items move the index past the queue, with no break,
  so the no-padding premise is load-bearing) and `SetupRootAcceptsZeroItem` (the `bytes32(0)`
  case is reached).
