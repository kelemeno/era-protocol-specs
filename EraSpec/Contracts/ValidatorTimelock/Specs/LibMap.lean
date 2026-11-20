import EraSpec.Contracts.ValidatorTimelock.Specs.Model

/-!
# Model: the packed commit timestamps (`LibMap.Uint32Map`)

**Source commit.** era-contracts `draft/v0.35.0` at **`b17415d20`**:
`state-transition/libraries/LibMap.sol` (`LM`) and `state-transition/validators/ValidatorTimelock.sol` (`VT`).

**This file is definitions only.** The statements are in
`EraSpec.Contracts.ValidatorTimelock.Properties.LibMap` and are proved in
`EraSpec.Contracts.ValidatorTimelock.Proofs.LibMap`.

`committedBatchTimestamp[chain]` (`VT:88`) is a `LibMap.Uint32Map`: a mapping from a slot index
`k` to a 256-bit word holding the eight `uint32` values with indices `8k … 8k+7`, value number
`j` of the slot in bits `32j … 32j+31`.

* `get(i)` (`LM:19-33`): `uint32(map[i / 8] >> ((i & 7) * 32))`.
* `set(i, v)` (`LM:39-64`): with `w = map[i / 8]` and `o = (i & 7) * 32`,
  `map[i / 8] = (uint256(uint32(w >> o) ^ v) << o) ^ w`.
* The commit loop (`VT:296-303`): `ts = uint32(block.timestamp)`, then `set(i, ts)` for
  `i = _processBatchFrom, …, _processBatchTo`, in that order.

Both functions are `unchecked`. The only operation that can wrap is the shift left of `LM:62`,
transcribed with its `mod 2^256`; the others cannot exceed `2^256`. `uint32(x)` is
`x mod 2^32`, and the `uint32` XOR of `LM:58` of two values below `2^32` is below `2^32`.

## Modelling choices

* A storage word is a natural number. `StorageWords m` says every slot holds a value below
  `2^256`: true of EVM storage, and kept by `set` (`Properties.LibMap`).
* Indices are natural numbers; in the source they are `uint256`, and the loop's indices stay
  below `2^256` on the ranges `validRange` admits.
* Only `_recordBatchCommitment` (`VT:301`) writes `committedBatchTimestamp`; it is read at
  `VT:173` and `:334`. `packedStep` is this: a commit runs the loop on its chain's map, and no
  other entry point writes the packed storage.
-/

namespace Contracts.ValidatorTimelock

/-- `LibMap.Uint32Map`: slot index → the 256-bit word stored there. -/
abbrev Uint32Map := ℕ → ℕ

/-- Every slot holds a 256-bit word. -/
def StorageWords (m : Uint32Map) : Prop := ∀ k, m k < 2 ^ 256

/-- `LibMap.get` (`LM:19-33`). -/
def libMapGet (m : Uint32Map) (i : ℕ) : ℕ :=
  (m (i / 8) >>> ((i &&& 7) * 32)) % 2 ^ 32

/-- `LibMap.set` (`LM:39-64`). -/
def libMapSet (m : Uint32Map) (i v : ℕ) : Uint32Map :=
  let mapIndex := i / 8
  let mapValue := m mapIndex
  let bitOffset := (i &&& 7) * 32
  let oldValue := (mapValue >>> bitOffset) % 2 ^ 32
  let newValueXorOldValue := oldValue ^^^ v
  upd m mapIndex (((newValueXorOldValue <<< bitOffset) % 2 ^ 256) ^^^ mapValue)

/-- The loop of `_recordBatchCommitment` (`VT:300-302`) from index `i` for `n` iterations:
`set(i, ts)`, `set(i + 1, ts)`, …, in that order. -/
def recordLoop (ts : ℕ) : ℕ → ℕ → Uint32Map → Uint32Map
  | _, 0, m => m
  | i, n + 1, m => recordLoop ts (i + 1) n (libMapSet m i ts)

/-- `_recordBatchCommitment(c, lo, hi)` on chain `c`'s map (`VT:291-304`): `ts = uint32(now)`,
then `set(i, ts)` for `i = lo, …, hi` (no iteration when `lo > hi`). -/
def recordBatchCommitment (m : Uint32Map) (lo hi now : ℕ) : Uint32Map :=
  recordLoop (now % 2 ^ 32) lo (hi + 1 - lo) m

/-- The packed storage `committedBatchTimestamp`: each chain's `Uint32Map`. -/
abbrev PackedTimestamps := Address → Uint32Map

/-- The packed storage represents the model's `committedAt`: every slot holds a word, and every
`get` returns the model's value. -/
def Represents (M : PackedTimestamps) (s : State) : Prop :=
  ∀ c, StorageWords (M c) ∧ ∀ i, libMapGet (M c) i = s.committedAt c i

/-- What a call does to the packed storage: a commit runs the loop on its chain's map; nothing
else writes it. -/
def packedStep (k : Call) (M : PackedTimestamps) : PackedTimestamps :=
  match k.action with
  | .commitBatches c lo hi => upd M c (recordBatchCommitment (M c) lo hi k.env.now)
  | _ => M

/-- The packed storage after a sequence of calls, each applied with `packedStep`. -/
def packedRun (ks : List Call) (M : PackedTimestamps) : PackedTimestamps :=
  ks.foldl (fun M k => packedStep k M) M

/-! ## Witness data -/

/-- A map whose slot `0` has every bit set and whose other slots are zero. -/
def vtSlotMap : Uint32Map := fun k => if k = 0 then 2 ^ 256 - 1 else 0

end Contracts.ValidatorTimelock
