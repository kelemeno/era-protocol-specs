import EraSpec.Contracts.MessageRoot.Specs.Aggregation
import EraSpec.Contracts.AtomicInteropProof.Specs.LastBatchInRoot

/-!
# Properties: what a historical root aggregates

Statements about `EraSpec.Contracts.MessageRoot.Specs.Aggregation`. Proofs are in
`EraSpec.Contracts.MessageRoot.Proofs.Aggregation`. Every run starts at `_initialize` (`init`) and
interleaves the six steps of `Step` in any order; `r` is the timestamp rule of its blocks. No
statement takes a premise on the hashes. Caller checks are not modelled (Specs), so every
`∀`-statement over runs covers more runs than the callers allow.

## (a) The registry and the trees

A registered chain has its own shared-tree position (`ChainIndexInjective`,
`ChainIndexIsAPosition`), and the leaf at that position is `chainIdLeafHash` of the chain's current
tree root, `chainIdLeafHash(0, c)` while the chain has no leaf (`SharedLeafIsChainIdLeaf`,
`FreshChainLeafIsZeroRoot`). A chain tree holds recorded batches only, in strictly increasing
batch order, each with the timestamp the contract recorded for it (`ChainLeavesArePushedBatches`).
The source's stated invariant "for all batches starting from `currentChainBatchNumber + 1`, the
`chainBatchRoots` is 0" (:100) holds (`UnrecordedAboveCurrent`), a recorded batch root is never
rewritten (`BatchRootWriteOnce`), and an unregistered chain has no leaf and no recorded batch
(`UnregisteredChainHoldsNothing`).

## (b) The clock

Along every chain tree, timestamps and push blocks are non-decreasing (`LeavesOrdered`), so the
clock indexed by pushed position is monotone (`LeafTimeMonotone`), also as a `uint256` clock
(`LeafTimeMonotoneAsWord`). Monotone settlement times are what `Wf.timeOrdered`, `NoTheft`'s
`htmono` and `BurnMintBridge.History.Valid.monotone_time` take as premises.

## (c) A historical root is the snapshot of its block

In every reachable state, `historicalRoots[b]` counts exactly the leaves pushed in blocks up to
`b`: a chain's leaf at position `i` is counted iff it was pushed in a block `≤ b`, and every leaf
pushed in block `b` carries the root's timestamp (`HistoricalRootIsSnapshot`). The current block's
entry, once written, is the current shared root, counting every leaf (`LastWriteInBlockWins`).

## (d) Aggregation, discharged

Under either timestamp rule, every leaf that settled **strictly before** a historical root was
written is counted by it: for the root as it stood at any point of a run, possibly mid-block and
overwritten later in the same block, and for every later state of the run
(`AggregatesStrictFromMessageRoot`). Under strictly increasing timestamps the non-strict form
holds for the roots as they stand in a state (`AggregatesFromMessageRootStrictTs`).

## (e) The non-strict form needs both premises

Equal timestamps across two blocks (`EqualTimestampEscapesRoot`), or a root read mid-block even
with strictly increasing timestamps (`MidBlockReadEscapesRoot`), leave a leaf that settled exactly
at the root's timestamp outside the root: the non-strict form fails while the strict form holds.

## (g) Positions, not batch numbers

Indexed by pushed position, every leaf past a root's count settles no earlier than the root, for
every root and every later state (`PushedAfterLastIsLate`, the shape of
`LastBatchInRoot.OutsideRootLate`). Indexed by batch number, with the contract's own per-batch
timestamp `chainBatchRootTimestamp` as the clock, it fails: a record-only batch is outside the
root and carries timestamp 0 (`RecordOnlyGap`). A batch that is recorded and not pushed is never
pushed later, keeps timestamp 0 and keeps its root (`RecordOnlyBatchNotCitable`). A chain
registered at a nonzero start carries batch numbers that are not its positions
(`OnboardedChainPositionsAreNotBatchNumbers`).

## Witnesses

| Witness | Premises it meets |
|---|---|
| `AggregationWitness` | a reachable state under strict timestamps whose current block has an entry `e` (`LastWriteInBlockWins`, `HistoricalRootIsSnapshot`), a registered chain `c ≠ self` with a recorded batch and with leaves both inside `e` (one strictly before it) and, in a later state, outside it (`AggregatesStrictFromMessageRoot`, `PushedAfterLastIsLate`, `BatchRootWriteOnce`, (a), (b), `AggregatesFromMessageRootStrictTs`), with a `block.timestamp` that fits a word (`LeafTimeMonotoneAsWord`) |
| `AggregationRegistryWitness` | a registered chain `c ≠ self` with no leaf (`FreshChainLeafIsZeroRoot`), and an unregistered chain whose batch number was moved (`UnregisteredChainHoldsNothing`) |
| `RecordOnlyBatchNotCitableWitness` | `RecordOnlyBatchNotCitable`, with a nonempty tree that grows in the continuation |

The four existential statements of (e) and (g) are countermodels and need no witness.
-/

namespace Contracts.MessageRoot.Aggregation

open AttackVectors.LastBatchInRoot (OutsideRootLate)

/-! ## (a) The registry and the trees -/

/-- **ONE CHAIN PER SHARED-TREE POSITION.** Two registered chains with the same `chainIndex` are
the same chain. -/
def Properties.ChainIndexInjective : Prop :=
  ∀ (P : Params) (r : TsRule) (st : State), Reachable P r st →
    ∀ c c', st.Registered P c → st.Registered P c' → st.chainIndex c = st.chainIndex c' → c = c'

/-- A registered chain's index is a shared-tree position, and `chainIndexToId` inverts it. -/
def Properties.ChainIndexIsAPosition : Prop :=
  ∀ (P : Params) (r : TsRule) (st : State), Reachable P r st →
    st.shared.length = st.chainCount ∧ st.chainIndex P.self = 0 ∧
    ∀ c, st.Registered P c →
      st.chainIndex c < st.chainCount ∧ st.chainIndexToId (st.chainIndex c) = c

/-- **THE SHARED LEAF IS THE CHAIN-ID LEAF.** A registered chain's shared-tree leaf is
`chainIdLeafHash(chainRoot, c)` for its current chain-tree root (`chainRootVal`: `0` while the
tree is empty). -/
def Properties.SharedLeafIsChainIdLeaf : Prop :=
  ∀ (P : Params) (r : TsRule) (st : State), Reachable P r st → ∀ c, st.Registered P c →
    st.shared[st.chainIndex c]? = some (P.H.chainIdLeaf (chainRootVal P.H (st.leaves c)) c)

/-- **A FRESH CHAIN'S LEAF IS `chainIdLeafHash(0, c)`** (:352): while a registered chain has no
leaf, its shared-tree leaf commits to the zero word. -/
def Properties.FreshChainLeafIsZeroRoot : Prop :=
  ∀ (P : Params) (r : TsRule) (st : State), Reachable P r st → ∀ c, st.Registered P c →
    st.leaves c = [] → st.shared[st.chainIndex c]? = some (P.H.chainIdLeaf 0 c)

/-- **A CHAIN TREE HOLDS RECORDED BATCHES, EACH ONCE.** Batch numbers strictly increase along the
tree, and every leaf is a recorded batch (`chainBatchRoots`, nonzero) with its recorded timestamp
(`chainBatchRootTimestamp`), at or below `currentChainBatchNumber`. -/
def Properties.ChainLeavesArePushedBatches : Prop :=
  ∀ (P : Params) (r : TsRule) (st : State), Reachable P r st → ∀ c,
    (st.leaves c).Pairwise (fun l l' => l.batch < l'.batch)
      ∧ ∀ l ∈ st.leaves c, st.batchRoot c l.batch = l.root ∧ l.root ≠ 0
          ∧ st.batchTs c l.batch = l.ts ∧ l.batch ≤ st.current c

/-- **THE SOURCE'S OWN INVARIANT (:100).** No batch above `currentChainBatchNumber` is recorded. -/
def Properties.UnrecordedAboveCurrent : Prop :=
  ∀ (P : Params) (r : TsRule) (st : State), Reachable P r st →
    ∀ c b, st.current c < b → st.batchRoot c b = 0

/-- A recorded batch root is never rewritten, in any run from any state. -/
def Properties.BatchRootWriteOnce : Prop :=
  ∀ (P : Params) (r : TsRule) (st st' : State), Reach P r st st' →
    ∀ c b, st.batchRoot c b ≠ 0 → st'.batchRoot c b = st.batchRoot c b

/-- An unregistered chain has no leaf and no recorded batch. -/
def Properties.UnregisteredChainHoldsNothing : Prop :=
  ∀ (P : Params) (r : TsRule) (st : State), Reachable P r st → ∀ c, ¬ st.Registered P c →
    st.leaves c = [] ∧ ∀ b, st.batchRoot c b = 0

/-! ## (b) The clock -/

/-- **LEAVES ARE PUSHED IN TIME ORDER.** Along each chain tree, `l1Timestamp` and the push block
are non-decreasing, and no leaf is later than the current block. -/
def Properties.LeavesOrdered : Prop :=
  ∀ (P : Params) (r : TsRule) (st : State), Reachable P r st → ∀ c,
    (st.leaves c).Pairwise (fun l l' => l.ts ≤ l'.ts ∧ l.blk ≤ l'.blk)
      ∧ ∀ l ∈ st.leaves c, l.ts ≤ st.time ∧ l.blk ≤ st.block

/-- **THE CLOCK IS MONOTONE.** `leafTime c`, indexed by pushed position, is monotone. -/
def Properties.LeafTimeMonotone : Prop :=
  ∀ (P : Params) (r : TsRule) (st : State), Reachable P r st → ∀ c, Monotone (st.leafTime c)

/-- **…AS A `uint256` CLOCK TOO.** The form `NoTheft`'s `htmono : Monotone t` and
`BurnMintBridge.History.Valid.monotone_time` take (`t : ℕ → UInt256`), given that the current
`block.timestamp` plus one still fits a word. -/
def Properties.LeafTimeMonotoneAsWord : Prop :=
  ∀ (P : Params) (r : TsRule) (st : State), Reachable P r st → st.time + 1 < UInt256.size →
    ∀ c, Monotone (fun i => ((st.leafTime c i : ℕ) : UInt256))

/-! ## (c) A historical root is the snapshot of its block -/

/-- **`historicalRoots[b]` IS THE STATE AT THE END OF BLOCK `b` (SO FAR).** It was written in a
block `≤` the current one, at a timestamp `≤` the current one; it counts at most the leaves each
chain tree has; a leaf at position `i` is counted iff it was pushed in a block `≤ b`; and a leaf
pushed in block `b` carries the root's timestamp. -/
def Properties.HistoricalRootIsSnapshot : Prop :=
  ∀ (P : Params) (r : TsRule) (st : State), Reachable P r st → ∀ b e, st.hist b = some e →
    b ≤ st.block ∧ e.ts ≤ st.time ∧ ∀ c, e.count c ≤ (st.leaves c).length ∧
      ∀ i (hi : i < (st.leaves c).length),
        (i < e.count c ↔ ((st.leaves c)[i]).blk ≤ b)
          ∧ (((st.leaves c)[i]).blk = b → ((st.leaves c)[i]).ts = e.ts)

/-- **THE LAST WRITE IN THE BLOCK WINS.** The current block's entry, once written, is the current
shared root at the current timestamp, counting every leaf. -/
def Properties.LastWriteInBlockWins : Prop :=
  ∀ (P : Params) (r : TsRule) (st : State), Reachable P r st → ∀ e, st.hist st.block = some e →
    e.root = P.H.sharedRoot st.shared ∧ e.ts = st.time ∧ ∀ c, e.count c = (st.leaves c).length

/-! ## (d) Aggregation, discharged -/

/-- **STRICT AGGREGATION, FROM SOURCE.** Under either timestamp rule: take any historical root
`e` as it stood at some reachable state `st₁`, possibly mid-block and possibly overwritten later,
and any later state `st₂` of the run. Every leaf of `st₂` that settled strictly before `e`'s
timestamp is counted by `e`. -/
def Properties.AggregatesStrictFromMessageRoot : Prop :=
  ∀ (P : Params) (r : TsRule) (st₁ st₂ : State), Reachable P r st₁ → Reach P r st₁ st₂ →
    ∀ b e, st₁.hist b = some e → AggregatesStrictAt st₂ e

/-- **NON-STRICT AGGREGATION, UNDER STRICT TIMESTAMPS.** With strictly increasing block
timestamps, every root as it stands in a reachable state counts every leaf of that state that
settled at or before it. -/
def Properties.AggregatesFromMessageRootStrictTs : Prop :=
  ∀ (P : Params) (st : State), Reachable P .strict st →
    ∀ b e, st.hist b = some e → AggregatesAt st e

/-! ## (e) The non-strict form needs both premises -/

/-- **EQUAL TIMESTAMPS ACROSS BLOCKS ESCAPE THE ROOT.** Under non-decreasing timestamps, a leaf
pushed in a later block with the same timestamp is outside the earlier block's root: the
non-strict form fails for that root, the strict form holds. -/
def Properties.EqualTimestampEscapesRoot : Prop :=
  ∃ (P : Params) (st : State) (b : ℕ) (e : HistEntry), Reachable P .mono st ∧ st.hist b = some e
    ∧ AggregatesStrictAt st e ∧ ¬ AggregatesAt st e

/-- **A MID-BLOCK READ ESCAPES TOO.** Even with strictly increasing timestamps: a root as it
stood mid-block misses a leaf pushed later in the same block, which carries the root's own
timestamp. -/
def Properties.MidBlockReadEscapesRoot : Prop :=
  ∃ (P : Params) (st₁ st₂ : State) (b : ℕ) (e : HistEntry), Reachable P .strict st₁
    ∧ Reach P .strict st₁ st₂ ∧ st₂.block = st₁.block ∧ st₁.hist b = some e
    ∧ AggregatesStrictAt st₂ e ∧ ¬ AggregatesAt st₂ e

/-! ## (g) Positions, not batch numbers -/

/-- **A RECORD-ONLY BATCH BREAKS `OutsideRootLate` BY BATCH NUMBER.** Batches 0 and 1 of a chain
are pushed and counted by a root; batch 2 is then only recorded (`addChainBatchRoot`). With batch
numbers as the index and `chainBatchRootTimestamp` as the clock, batch 2 is outside the root yet
its time is `0`, before the root's: `LastBatchInRoot.OutsideRootLate` is false.

The run takes the record-only step after pushes. The pinned executor facet calls only
`addChainBatchRootV32` (`Executor.sol:154`), so on chain this order needs a chain whose executor
calls the record-only entry point after it has pushed (ASSUMPTIONS.md, `PROTO-CONTIGUOUS-PUSH`).
Record-only batches before the first push are the v31 path; they give the offset of
`OnboardedChainPositionsAreNotBatchNumbers` instead. -/
def Properties.RecordOnlyGap : Prop :=
  ∃ (P : Params) (st : State) (b : ℕ) (e : HistEntry) (c : ChainId), Reachable P .strict st
    ∧ st.hist b = some e ∧ st.batchRoot c 2 ≠ 0 ∧ (∀ l ∈ st.leaves c, l.batch ≠ 2)
    ∧ ¬ OutsideRootLate (st.BatchInFirst c (e.count c)) (st.batchTs c) e.ts

/-- **BY PUSHED POSITION, EVERYTHING OUTSIDE A ROOT IS LATE.** For any root as it stood at some
reachable state and any later state of the run, every position at or past the root's count
settles no earlier than the root: `OutsideRootLate` for the position-indexed clock. -/
def Properties.PushedAfterLastIsLate : Prop :=
  ∀ (P : Params) (r : TsRule) (st₁ st₂ : State), Reachable P r st₁ → Reach P r st₁ st₂ →
    ∀ b e, st₁.hist b = some e → ∀ c, OutsideRootLate (· < e.count c) (st₂.leafTime c) e.ts

/-- **A RECORD-ONLY BATCH IS NEVER PUSHED LATER.** If batch `b` of chain `c` is recorded in a
reachable state and is in none of `c`'s leaves, then in every later state of the run it is still
in none of `c`'s leaves, its recorded timestamp is `0`, and its recorded root is unchanged.
(At the source level the unchanged root is what `_getChainBatchRoot` serves for direct,
single-hop message verification, :436-445; that path is not modelled.) -/
def Properties.RecordOnlyBatchNotCitable : Prop :=
  ∀ (P : Params) (r : TsRule) (st₁ st₂ : State), Reachable P r st₁ → Reach P r st₁ st₂ →
    ∀ c b, st₁.batchRoot c b ≠ 0 → (∀ l ∈ st₁.leaves c, l.batch ≠ b) →
      (∀ l ∈ st₂.leaves c, l.batch ≠ b) ∧ st₂.batchTs c b = 0
        ∧ st₂.batchRoot c b = st₁.batchRoot c b

/-- **AN ONBOARDED CHAIN'S POSITIONS ARE NOT ITS BATCH NUMBERS.** A chain registered at start 5
(as `L1Bridgehub.sol:323` registers an existing chain at its executed-batch count) pushes its
batch 6 at position 0: a root counts one leaf of the chain, that leaf carries batch number 6, and
no leaf carries a batch number below 6. Reading the count as "batches `0 … count - 1`" names
batches that are in no tree. -/
def Properties.OnboardedChainPositionsAreNotBatchNumbers : Prop :=
  ∃ (P : Params) (st : State) (b : ℕ) (e : HistEntry) (c : ChainId) (l : Leaf),
    Reachable P .strict st ∧ st.hist b = some e ∧ e.count c = 1 ∧ (st.leaves c)[0]? = some l
      ∧ l.batch = 6 ∧ ∀ n < l.batch, ∀ l' ∈ st.leaves c, l'.batch ≠ n

/-! ## Witnesses -/

/-- **THE PREMISES OF (a)–(d) ARE MET NON-TRIVIALLY.** A run under strict timestamps reaching a
state `st₁` whose current block `b` has an entry `e`, with a registered chain `c ≠ self` that has
a recorded batch 1 and leaves counted by `e` (one settled strictly before `e`), and a later state
`st₂` with a leaf of `c` outside `e`, at a `block.timestamp` that fits a word. -/
def Properties.AggregationWitness : Prop :=
  ∃ (P : Params) (st₁ st₂ : State) (b : ℕ) (e : HistEntry) (c : ChainId),
    Reachable P .strict st₁ ∧ Reach P .strict st₁ st₂ ∧ st₁.hist b = some e ∧ b = st₁.block
      ∧ st₂.Registered P c ∧ c ≠ P.self ∧ st₁.batchRoot c 1 ≠ 0
      ∧ 0 < e.count c ∧ e.count c < (st₂.leaves c).length
      ∧ st₂.leafTime c 0 < e.ts ∧ st₂.time + 1 < UInt256.size

/-- **THE REGISTRY PREMISES ARE MET NON-TRIVIALLY.** A run under strict timestamps reaching a
state with a registered chain `c ≠ self` that has no leaf yet, and an unregistered chain `c'`
whose `currentChainBatchNumber` was moved by `setMigratingChainBatchNumber`, which has no
registration check (:178-183). Its deployed caller, the chain asset handler, calls it only for a
chain already deployed on the settlement layer (`ChainAssetHandlerBase.sol:363-386`), so the
second chain is a state of the model, not necessarily of the deployed system. -/
def Properties.AggregationRegistryWitness : Prop :=
  ∃ (P : Params) (st : State) (c c' : ChainId), Reachable P .strict st
    ∧ c ≠ P.self ∧ st.Registered P c ∧ st.leaves c = []
    ∧ ¬ st.Registered P c' ∧ st.current c' ≠ 0

/-- **`RecordOnlyBatchNotCitable`'S PREMISES, ON THE v31-TO-v32 PATH.** A chain registered at start
0 and never seeded (as for a chain `seedGenesisRoot` skips, :369-371) records its batch 1 with
`addChainBatchRoot`, then pushes batches 2 and 3 with `addChainBatchRootV32`. With `st₁` after
the first push and `st₂` after the second: batch 1 is recorded, is in none of the nonempty
tree's leaves at `st₁`, and the tree grows from `st₁` to `st₂`. -/
def Properties.RecordOnlyBatchNotCitableWitness : Prop :=
  ∃ (P : Params) (st₁ st₂ : State) (c : ChainId) (b : ℕ),
    Reachable P .strict st₁ ∧ Reach P .strict st₁ st₂ ∧ st₁.batchRoot c b ≠ 0
      ∧ (∀ l ∈ st₁.leaves c, l.batch ≠ b) ∧ st₁.leaves c ≠ []
      ∧ (st₁.leaves c).length < (st₂.leaves c).length

end Contracts.MessageRoot.Aggregation
