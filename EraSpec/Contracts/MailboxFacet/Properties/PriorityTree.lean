import EraSpec.Contracts.MailboxFacet.Specs.PriorityTree

/-!
# Properties: the priority tree is append-only and its processed prefix only grows

Statements about `EraSpec.Contracts.MailboxFacet.Specs.PriorityTree`. Proofs are in
`EraSpec.Contracts.MailboxFacet.Proofs.PriorityTree`. No statement has a hash premise: every one
holds for every node hash, padding leaf and `calculateRootPaths`.

* `TreeShapeInvariant`: `setup` and `initFromCommitment` establish `WellFormed`, every later call
  keeps it, so the tree's current root is always a recorded historical root.
* `PushAppendsOneLeaf`: what one `push` writes.
* `TreeRunMonotone` (headline): over any run of `push`, `processBatch`, `l1Reinit`, `gwReinit`,
  the start index is fixed, the leaf count and the processed count never decrease, and no
  historical root is ever forgotten.
* `LeafCountIsPushCount`: without `gwReinit` (so on L1), the leaf count grows by exactly the number
  of `push` calls.
* `HistoricalRootsWereRoots`: every historical root was already historical at the start or was the
  tree's root after some prefix of the run.
* `ProcessBatchChecksHistoricalRoot`: what a successful `processBatch` checked and wrote.
* `ConsistentRunKeepsSize`: if every caller is `Consistent`, at most the pushed leaves are
  processed, so `getSize` never reverts.
* `SizeNeedsConsistentCallers` (countermodel): the library's guards alone do not give that.
* `TreeRunWitness`: a concrete run.
-/

namespace Contracts.MailboxFacet

/-- **THE TREE KEEPS ITS SHAPE AND ITS ROOT IS HISTORICAL.** `setup` on storage whose two arrays
have equal length (fresh storage in particular), and every successful `initFromCommitment`, give a
`WellFormed` tree. Every successful `push`, `processBatch`, `l1Reinit` and `gwReinit` keeps
`WellFormed`, and so does every run of them. -/
def Properties.TreeShapeInvariant : Prop :=
  ∀ (P : TreeParams),
    (∀ (t : PTree) (startIndex : ℕ), t.tree.sides.length = t.tree.zeros.length →
        (t.setup P startIndex).WellFormed)
    ∧ (∀ (t t' : PTree) (c : Commitment), t.initFromCommitment P c = some t' → t'.WellFormed)
    ∧ (∀ (t t' : PTree) (ls : List TreeLabel), TreeRun P t ls t' → t.WellFormed → t'.WellFormed)

/-- **ONE PUSH, ONE LEAF.** A successful `push` on a `WellFormed` tree increments the leaf count
by exactly one, leaves `startIndex` and `unprocessedIndex` alone, keeps the old `_zeros` as a
prefix of the new, and adds exactly one historical root: the tree's new root. -/
def Properties.PushAppendsOneLeaf : Prop :=
  ∀ (P : TreeParams) (t t' : PTree) (hash : UInt256), t.WellFormed → t.push P hash = some t' →
    t'.tree.nextLeafIndex = t.tree.nextLeafIndex + 1
    ∧ t'.startIndex = t.startIndex ∧ t'.unprocessedIndex = t.unprocessedIndex
    ∧ t.tree.zeros <+: t'.tree.zeros
    ∧ t'.historicalRoots = markRoot t.historicalRoots t'.tree.root

/-- **HEADLINE: NOTHING IS EVER REMOVED.** Over any run of the tree's calls, in any order: the
start index does not change, the number of leaves never decreases, the number of processed
operations never decreases, and every historical root stays historical. -/
def Properties.TreeRunMonotone : Prop :=
  ∀ (P : TreeParams) (t t' : PTree) (ls : List TreeLabel), TreeRun P t ls t' →
    t'.startIndex = t.startIndex
    ∧ t.tree.nextLeafIndex ≤ t'.tree.nextLeafIndex
    ∧ t.unprocessedIndex ≤ t'.unprocessedIndex
    ∧ ∀ r, t.historicalRoots r = true → t'.historicalRoots r = true

/-- **ON L1 THE LEAF COUNT IS THE PUSH COUNT.** In a run with no `gwReinit` (L1 never
re-initializes the tree from a commitment), the leaf count grows by exactly the number of `push`
calls in the run. -/
def Properties.LeafCountIsPushCount : Prop :=
  ∀ (P : TreeParams) (t t' : PTree) (ls : List TreeLabel), TreeRun P t ls t' →
    (∀ c, TreeLabel.gwReinit c ∉ ls) →
    t'.tree.nextLeafIndex
      = t.tree.nextLeafIndex + (ls.filter (fun l => match l with | .push _ => true | _ => false)).length

/-- **A HISTORICAL ROOT WAS A ROOT.** From a `WellFormed` tree, every root recorded as historical
at the end of a run was either recorded at the start, or is the tree's root after some prefix of
the run. `processBatch` and the L1 migration check therefore accept only roots the tree has had. -/
def Properties.HistoricalRootsWereRoots : Prop :=
  ∀ (P : TreeParams) (t t' : PTree) (ls : List TreeLabel), TreeRun P t ls t' → t.WellFormed →
    ∀ r, t'.historicalRoots r = true →
      t.historicalRoots r = true
      ∨ ∃ (ls₁ ls₂ : List TreeLabel) (u : PTree),
          ls = ls₁ ++ ls₂ ∧ TreeRun P t ls₁ u ∧ u.tree.root = r

/-- **WHAT `processBatch` CHECKS.** A successful `processBatch` with at least one item recomputed
a root from the items at positions `unprocessedIndex ..`, found it among the historical roots, and
advanced `unprocessedIndex` by exactly the number of items. It writes nothing else. With no items
it changes nothing. -/
def Properties.ProcessBatchChecksHistoricalRoot : Prop :=
  ∀ (P : TreeParams) (t t' : PTree) (info : BatchInfo), t.processBatch P info = some t' →
    (info.itemHashes = [] → t' = t)
    ∧ (info.itemHashes ≠ [] →
        ∃ r, P.rootPaths info.leftPath info.rightPath t.unprocessedIndex info.itemHashes = some r
          ∧ t.historicalRoots r = true
          ∧ t' = { t with unprocessedIndex := t.unprocessedIndex + info.itemHashes.length })

/-- **WITH CONSISTENT CALLERS, PROCESSED NEVER EXCEEDS PUSHED.** If every call of a run is
`Consistent` and the run starts with at most the pushed leaves processed, it ends that way, so
`getSize` returns the difference and does not revert. -/
def Properties.ConsistentRunKeepsSize : Prop :=
  ∀ (P : TreeParams) (t t' : PTree) (ls : List TreeLabel), ConsistentRun P t ls t' →
    t.unprocessedIndex ≤ t.tree.nextLeafIndex →
    t'.unprocessedIndex ≤ t'.tree.nextLeafIndex
    ∧ t'.getSize = some (t'.tree.nextLeafIndex - t'.unprocessedIndex)

/-- **COUNTERMODEL: THE LIBRARY'S GUARDS DO NOT BOUND THE PROCESSED COUNT.** Both from the fresh
tree `wFresh`, which is `WellFormed` with nothing pushed and nothing processed.

* `l1Reinit` accepts a commitment claiming three processed operations and no leaves: all three
  guards pass. Afterwards `getSize` reverts.
* With the witness `calculateRootPaths` (nothing is assumed about that function), `processBatch`
  accepts one item that was never pushed. Afterwards `getSize` reverts.

So `Consistent` in `ConsistentRunKeepsSize` is needed at both calls. -/
def Properties.SizeNeedsConsistentCallers : Prop :=
  wFresh.WellFormed ∧ wFresh.unprocessedIndex = 0 ∧ wFresh.tree.nextLeafIndex = 0
  ∧ (∃ t', wFresh.l1Reinit ⟨0, 5, 3, []⟩ = some t' ∧ t'.unprocessedIndex = 3 ∧ t'.getSize = none)
  ∧ (∃ t', wFresh.processBatch wParams ⟨[], [], [9]⟩ = some t' ∧ t'.unprocessedIndex = 1
      ∧ t'.getSize = none)

/-- **A CONCRETE RUN.** From `wFresh` (start index `5`): three pushes, then a batch of two items,
then an `l1Reinit`. The run is `Consistent`. It ends with three leaves, two processed, total `8`,
first unprocessed `7`, size `1`; the tree has grown to three levels and its root is historical. -/
def Properties.TreeRunWitness : Prop :=
  ∃ t' : PTree,
    ConsistentRun wParams wFresh
      [.push 1, .push 2, .push 3, .processBatch ⟨[], [], [1, 2]⟩, .l1Reinit ⟨3, 5, 2, []⟩] t'
    ∧ t'.tree.nextLeafIndex = 3 ∧ t'.unprocessedIndex = 2
    ∧ t'.getTotalPriorityTxs = some 8 ∧ t'.getFirstUnprocessedPriorityTx = some 7
    ∧ t'.getSize = some 1 ∧ t'.tree.zeros.length = 3
    ∧ t'.historicalRoots t'.tree.root = true

end Contracts.MailboxFacet
