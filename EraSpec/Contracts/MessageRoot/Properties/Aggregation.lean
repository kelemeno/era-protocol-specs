import EraSpec.Contracts.MessageRoot.Specs.Aggregation
import EraSpec.Contracts.AtomicInteropProof.Specs.LastBatchInRoot

/-!
# Properties: what a historical root aggregates

Statements about `EraSpec.Contracts.MessageRoot.Specs.Aggregation`. Proofs are in
`EraSpec.Contracts.MessageRoot.Proofs.Aggregation`. Every run starts at `_initialize` (`init`) and
interleaves the six steps of `Step` in any order; `r` is the timestamp rule of its blocks.

## (a) The registry and the trees

A registered chain has its own shared-tree position (`ChainIndexInjective`,
`ChainIndexIsAPosition`), and the leaf at that position is `chainIdLeafHash` of the chain's current
tree root — `chainIdLeafHash(0, c)` while the chain has no leaf (`SharedLeafIsChainIdLeaf`,
`FreshChainLeafIsZeroRoot`). A chain tree holds recorded batches only, in strictly increasing
batch order, each with the timestamp the contract recorded for it (`ChainLeavesArePushedBatches`).
The source's stated invariant "for all batches starting from `currentChainBatchNumber + 1`, the
`chainBatchRoots` is 0" (:100) holds (`UnrecordedAboveCurrent`), and a recorded batch root is never
rewritten (`BatchRootWriteOnce`).

## (b) The clock

Along every chain tree, timestamps and blocks are non-decreasing (`LeavesOrdered`), so the clock
indexed by pushed position is monotone (`LeafTimeMonotone`), also as a `uint256` clock
(`LeafTimeMonotoneAsWord`). This is what `Wf.timeOrdered`, `NoTheft`'s `htmono` and
`BurnMintBridge.History.Valid.monotone_time` ask of the settlement layer.

## (c) A historical root is the snapshot of its block

`historicalRoots[b]` aggregates exactly the leaves pushed in blocks up to `b`: a chain's leaf at
position `i` is inside it iff it was pushed in a block `≤ b`, and the root's timestamp is the
push time of every leaf pushed in block `b` (`HistoricalRootIsSnapshot`). Within the current block
the last write wins: the current block's entry is always the current shared root
(`LastWriteInBlockWins`).

## (d) Aggregation, discharged

Under non-decreasing timestamps, every leaf that settled **strictly before** a historical root was
written is inside it — including a root read mid-block and overwritten later in the same block,
and for every later state of the run (`AggregatesStrictFromMessageRoot`). The non-strict form
holds under strictly increasing timestamps, for the roots as they stand
(`AggregatesFromMessageRootStrictTs`).

## (e) The non-strict form needs both

Equal timestamps across blocks (`EqualTimestampEscapesRoot`) or a mid-block read even with strict
timestamps (`MidBlockReadEscapesRoot`) put a leaf that settled exactly at the root's timestamp
outside the root: the non-strict form fails, the strict form holds.

## (g) Positions, not batch numbers

With the contract's own per-batch timestamp (`chainBatchRootTimestamp`) as the clock and batch
numbers as the index, `LastBatchInRoot.OutsideRootLate` is false: a record-only batch (the v31
entry point) is outside the root and carries timestamp 0 (`RecordOnlyGap`). Indexed by pushed
position it holds for every root (`PushedAfterLastIsLate`); a record-only batch is never pushed
later, keeps timestamp 0, and so is never inside any root (`RecordOnlyBatchNotCitable`). A chain
onboarded at a nonzero start carries batch numbers that are not its positions
(`OnboardedChainPositionsAreNotBatchNumbers`).

## Non-vacuity

`AggregationWitness`: a run under strict timestamps with two registered chains, a historical root
holding some of a chain's leaves (one settled strictly before the root) and missing a later one,
at a timestamp that fits a word. It meets every premise of (a)–(d), `LeafTimeMonotoneAsWord` and
`PushedAfterLastIsLate` non-trivially. `RecordOnlyGap` meets the premises of
`RecordOnlyBatchNotCitable`.
-/

namespace Contracts.MessageRoot

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

/-- **A FRESH CHAIN'S LEAF IS `chainIdLeafHash(0, c)`** (:352), not the hash of an empty tree's
root: while a registered chain has no leaf, its shared-tree leaf commits to the zero word. -/
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
`block.timestamp` plus one still fits a word (`block.timestamp` is a `uint256`). -/
def Properties.LeafTimeMonotoneAsWord : Prop :=
  ∀ (P : Params) (r : TsRule) (st : State), Reachable P r st → st.time + 1 < UInt256.size →
    ∀ c, Monotone (fun i => ((st.leafTime c i : ℕ) : UInt256))

/-! ## (c) A historical root is the snapshot of its block -/

/-- **`historicalRoots[b]` IS THE STATE AT THE END OF BLOCK `b` (SO FAR).** It was written in a
block `≤` the current one, at a timestamp `≤` the current one; it counts a prefix of every chain
tree; a leaf at position `i` is inside it iff the leaf was pushed in a block `≤ b`; and a leaf
pushed in block `b` carries the root's timestamp. So the write that survives is the block's last. -/
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
`e` as it stood at some point `st₁` of the run — possibly mid-block, possibly overwritten later —
and any later state `st₂`. Every leaf of `st₂` that settled strictly before `e`'s timestamp is
inside `e`. -/
def Properties.AggregatesStrictFromMessageRoot : Prop :=
  ∀ (P : Params) (r : TsRule) (st₁ st₂ : State), Reachable P r st₁ → Reach P r st₁ st₂ →
    ∀ b e, st₁.hist b = some e → AggregatesStrictAt st₂ e

/-- **NON-STRICT AGGREGATION, UNDER STRICT TIMESTAMPS.** With strictly increasing block
timestamps, every root as it stands aggregates every leaf that settled at or before it. -/
def Properties.AggregatesFromMessageRootStrictTs : Prop :=
  ∀ (P : Params) (st : State), Reachable P .strict st →
    ∀ b e, st.hist b = some e → AggregatesAt st e

/-! ## (e) The non-strict form needs both premises -/

/-- **EQUAL TIMESTAMPS ACROSS BLOCKS ESCAPE THE ROOT.** Under non-decreasing timestamps a leaf
pushed in a later block with the same timestamp is outside the earlier block's root: the
non-strict form fails, the strict form holds. -/
def Properties.EqualTimestampEscapesRoot : Prop :=
  ∃ (P : Params) (st : State) (b : ℕ) (e : HistEntry), Reachable P .mono st ∧ st.hist b = some e
    ∧ AggregatesStrictAt st e ∧ ¬ AggregatesAt st e

/-- **A MID-BLOCK READ ESCAPES TOO.** Even with strict timestamps: a root read mid-block misses a
leaf pushed later in the same block, which carries the root's own timestamp. -/
def Properties.MidBlockReadEscapesRoot : Prop :=
  ∃ (P : Params) (st₁ st₂ : State) (b : ℕ) (e : HistEntry), Reachable P .strict st₁
    ∧ Reach P .strict st₁ st₂ ∧ st₂.block = st₁.block ∧ st₁.hist b = some e
    ∧ AggregatesStrictAt st₂ e ∧ ¬ AggregatesAt st₂ e

/-! ## (g) Positions, not batch numbers -/

/-- **A RECORD-ONLY BATCH BREAKS `OutsideRootLate` BY BATCH NUMBER.** Batches 0 and 1 of a chain are
pushed and aggregated; batch 2 is only recorded (`addChainBatchRoot`, the v31 entry point). With
batch numbers as the index and `chainBatchRootTimestamp` as the clock, batch 2 is outside the
root yet its time is `0`, before the root's: `LastBatchInRoot.OutsideRootLate` is false. -/
def Properties.RecordOnlyGap : Prop :=
  ∃ (P : Params) (st : State) (b : ℕ) (e : HistEntry) (c : ChainId), Reachable P .strict st
    ∧ st.hist b = some e ∧ st.batchRoot c 2 ≠ 0 ∧ (∀ l ∈ st.leaves c, l.batch ≠ 2)
    ∧ ¬ OutsideRootLate (st.BatchInFirst c (e.count c)) (st.batchTs c) e.ts

/-- **BY PUSHED POSITION, EVERYTHING OUTSIDE A ROOT IS LATE.** The replacement: for any root as it
stood at some point of the run and any later state, every position past the root's count settles
no earlier than the root — exactly `OutsideRootLate` for the position-indexed clock. -/
def Properties.PushedAfterLastIsLate : Prop :=
  ∀ (P : Params) (r : TsRule) (st₁ st₂ : State), Reachable P r st₁ → Reach P r st₁ st₂ →
    ∀ b e, st₁.hist b = some e → ∀ c, OutsideRootLate (· < e.count c) (st₂.leafTime c) e.ts

/-- **A RECORD-ONLY BATCH IS NEVER CITABLE.** A batch recorded but not pushed is never pushed
later, so it is in no chain tree and in no historical root; its recorded timestamp stays `0`;
its recorded root never changes (so `_getChainBatchRoot` still serves it for direct, single-hop
message verification, :436-445). -/
def Properties.RecordOnlyBatchNotCitable : Prop :=
  ∀ (P : Params) (r : TsRule) (st₁ st₂ : State), Reachable P r st₁ → Reach P r st₁ st₂ →
    ∀ c b, st₁.batchRoot c b ≠ 0 → (∀ l ∈ st₁.leaves c, l.batch ≠ b) →
      (∀ l ∈ st₂.leaves c, l.batch ≠ b) ∧ st₂.batchTs c b = 0
        ∧ st₂.batchRoot c b = st₁.batchRoot c b

/-- **AN ONBOARDED CHAIN'S POSITIONS ARE NOT ITS BATCH NUMBERS.** A chain registered at a nonzero
start (`L1Bridgehub.sol:323`) pushes its first batch at position 0: the root holds one leaf of the
chain, carrying batch number 6, and batch 0 is in no leaf. Reading `upTo` as a batch number
counts batches `0 … 5` that are in no tree. -/
def Properties.OnboardedChainPositionsAreNotBatchNumbers : Prop :=
  ∃ (P : Params) (st : State) (b : ℕ) (e : HistEntry) (c : ChainId) (l : Leaf),
    Reachable P .strict st ∧ st.hist b = some e ∧ e.count c = 1 ∧ (st.leaves c)[0]? = some l
      ∧ l.batch = 6 ∧ ∀ n < l.batch, ∀ l' ∈ st.leaves c, l'.batch ≠ n

/-! ## Non-vacuity -/

/-- **THE PREMISES OF (a)–(d) ARE MET NON-TRIVIALLY.** A run under strict timestamps reaching a
state `st₁` with a registered chain `c ≠ self`, whose historical root `e` holds some of `c`'s leaves
(one settled strictly before `e`), and a later state `st₂` with a leaf of `c` outside `e`. -/
def Properties.AggregationWitness : Prop :=
  ∃ (P : Params) (st₁ st₂ : State) (b : ℕ) (e : HistEntry) (c : ChainId),
    Reachable P .strict st₁ ∧ Reach P .strict st₁ st₂ ∧ st₁.hist b = some e
      ∧ st₂.Registered P c ∧ c ≠ P.self ∧ 0 < e.count c ∧ e.count c < (st₂.leaves c).length
      ∧ st₂.leafTime c 0 < e.ts ∧ st₂.time + 1 < UInt256.size

end Contracts.MessageRoot
