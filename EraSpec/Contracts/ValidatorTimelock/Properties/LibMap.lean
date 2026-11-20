import EraSpec.Contracts.ValidatorTimelock.Specs.LibMap
import EraSpec.Core.Headline

/-!
# Properties: the packed commit timestamps

Statements about `EraSpec.Contracts.ValidatorTimelock.Specs.LibMap` (source `b17415d20`).
Proofs are in `EraSpec.Contracts.ValidatorTimelock.Proofs.LibMap`.

* **`set` then `get` is a point update** (`LibMapGetSet`): on word-valued storage, after
  `set(i, v)` with `v < 2^32`, `get(i)` is `v` and every other index, in the same slot or not,
  reads as before. `set` keeps storage word-valued (`LibMapSetKeepsWords`), and `get` is always
  below `2^32` (`LibMapGetFitsUint32`).
* **The commit loop writes exactly its range** (`RecordLoopWritesTheRange`): after
  `_recordBatchCommitment(c, lo, hi)` at time `now`, `get(j)` is `now % 2^32` for
  `lo ≤ j ≤ hi` and unchanged elsewhere.
* **The packed storage refines the model** (`PackedTimestampsRefine`,
  `PackedTimestampsRefineRuns`): all-zero storage represents fresh `committedAt`, and every
  successful call (or run) of `Specs.Model` keeps the representation when the packed storage
  takes `packedStep`. So `committedAt` in `Specs.Model` is what `getCommittedBatchTimestamp`
  and the execute check read, for the transcription here.
* `LibMapWitness` exercises a slot whose other values are all ones, and a commit range that
  spans two slots; `PackedTimestampsWitness` follows a commit through the refinement.
-/

namespace Contracts.ValidatorTimelock

/-- **`set` THEN `get` IS A POINT UPDATE.** On storage whose slots are 256-bit words, after
`set(i, v)` with `v` a `uint32`, `get(i)` returns `v` and `get(j)` for every `j ≠ i` returns
what it returned before. -/
def Properties.LibMapGetSet : Prop :=
  ∀ (m : Uint32Map) (i j v : ℕ), StorageWords m → v < 2 ^ 32 →
    libMapGet (libMapSet m i v) j = if j = i then v else libMapGet m j

/-- **`set` KEEPS STORAGE WORD-VALUED.** If every slot is below `2^256` before `set`, every
slot is below `2^256` after it, whatever the value written. -/
def Properties.LibMapSetKeepsWords : Prop :=
  ∀ (m : Uint32Map) (i v : ℕ), StorageWords m → StorageWords (libMapSet m i v)

/-- **`get` RETURNS A `uint32`.** -/
def Properties.LibMapGetFitsUint32 : Prop :=
  ∀ (m : Uint32Map) (i : ℕ), libMapGet m i < 2 ^ 32

/-- **THE COMMIT LOOP WRITES EXACTLY ITS RANGE.** On word-valued storage,
`_recordBatchCommitment(c, lo, hi)` at time `now` keeps storage word-valued, and afterwards
`get(j)` is `now % 2^32` for `lo ≤ j ≤ hi` and what it was before for every other `j`. -/
def Properties.RecordLoopWritesTheRange : Prop :=
  ∀ (m : Uint32Map) (lo hi now : ℕ), StorageWords m →
    StorageWords (recordBatchCommitment m lo hi now) ∧
    ∀ j, libMapGet (recordBatchCommitment m lo hi now) j =
      if lo ≤ j ∧ j ≤ hi then now % 2 ^ 32 else libMapGet m j

/-- **THE PACKED STORAGE REFINES THE MODEL.** All-zero packed storage represents fresh storage
(`Represents`), and if packed storage `M` represents state `s`, then after any successful call
`k` from `s` to `s'`, `packedStep k M` represents `s'`. -/
def Properties.PackedTimestampsRefine : Prop :=
  Represents (fun _ _ => 0) init ∧
  ∀ (M : PackedTimestamps) (k : Call) (s s' : State), Represents M s → step k s = some s' →
    Represents (packedStep k M) s'

/-- **ALONG RUNS.** If packed storage `M` represents `s`, then after any run of successful calls
from `s` to `s'`, the packed storage obtained by applying `packedStep` call by call represents
`s'`. -/
@[headline] def Properties.PackedTimestampsRefineRuns : Prop :=
  ∀ (M : PackedTimestamps) (s s' : State) (ks : List Call), Represents M s → Run s ks s' →
    Represents (packedRun ks M) s'

/-- **THE REFINEMENT ON A COMMIT.** From fresh storage and all-zero packed storage, after the
witness setup and `vtDelayCommit` (validator `3` commits batches `1 … 3` of chain `100` at time
`1000`), the packed storage represents the model's state, and its `get(2)` for chain `100`
reads `1000`, as the model's `committedAt` does. -/
@[witness] def Properties.PackedTimestampsWitness : Prop :=
  ∃ s : State, Run init (vtSetupCalls ++ [vtDelayCommit]) s ∧
    Represents (packedRun (vtSetupCalls ++ [vtDelayCommit]) (fun _ _ => 0)) s ∧
    libMapGet (packedRun (vtSetupCalls ++ [vtDelayCommit]) (fun _ _ => 0) vtChain) 2 = 1000 ∧
    s.committedAt vtChain 2 = 1000

/-- **THE TRANSCRIPTION ON A FULL SLOT.** `vtSlotMap` is word-valued, with every bit of slot
`0` set. After `set(3, 0x12345678)`, `get(3)` is `0x12345678`, its neighbours `get(2)` and
`get(4)` still read `0xFFFFFFFF`, and slot `0` has changed. A commit of indices `6 … 9` at time
`2^32 + 7` (two slots) makes `get(6)` to `get(9)` read `7`, while `get(5)` still reads
`0xFFFFFFFF` and `get(10)` reads `0`. -/
@[witness] def Properties.LibMapWitness : Prop :=
  StorageWords vtSlotMap ∧ (0x12345678 : ℕ) < 2 ^ 32 ∧
  libMapGet (libMapSet vtSlotMap 3 0x12345678) 3 = 0x12345678 ∧
  libMapGet (libMapSet vtSlotMap 3 0x12345678) 2 = 0xFFFFFFFF ∧
  libMapGet (libMapSet vtSlotMap 3 0x12345678) 4 = 0xFFFFFFFF ∧
  libMapSet vtSlotMap 3 0x12345678 0 ≠ vtSlotMap 0 ∧
  libMapGet (recordBatchCommitment vtSlotMap 6 9 (2 ^ 32 + 7)) 5 = 0xFFFFFFFF ∧
  (∀ j ∈ [6, 7, 8, 9], libMapGet (recordBatchCommitment vtSlotMap 6 9 (2 ^ 32 + 7)) j = 7) ∧
  libMapGet (recordBatchCommitment vtSlotMap 6 9 (2 ^ 32 + 7)) 10 = 0

end Contracts.ValidatorTimelock
