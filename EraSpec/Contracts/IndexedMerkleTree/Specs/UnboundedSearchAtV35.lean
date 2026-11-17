import EraSpec.Contracts.IndexedMerkleTree.Specs.Model

/-!
# Contract spec: the unbounded low-leaf walk of `IndexedMerkleTree.insert`, at draft/v0.35.0

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29` (`d9f6789`),
`l1-contracts/contracts/common/libraries/IndexedMerkleTree.sol`.  The file is byte-identical on
`main` at `3605e82`.  The walk became unbounded in `b8cc61203` (#2349), which also deleted
`MAX_LOW_INDEX_SEARCH_ATTEMPTS` from `l1-contracts/contracts/common/Config.sol`.

    function insert(IMT storage self, uint256 _value, uint256 _lowLeafIndex) ... {   // :65-69
        uint256 leafNumber = self.tree._leafNumber;                                 // :70
        if (leafNumber == 0) revert IMTNotInitialized();                            // :71-73
        if (_value == 0) revert IMTValueZero();                                     // :74-76
        if (self.valueToIndex[_value] != 0) revert IMTValueAlreadyExists(_value);   // :77-79
        if (_lowLeafIndex >= leafNumber) revert IMTLowLeafIndexOutOfBounds(...);    // :80-82
        uint256 lowLeafIndex = _lowLeafIndex;                                       // :84
        IMTLeaf memory lowLeaf = self.leaves[lowLeafIndex];                         // :85
        if (lowLeaf.value >= _value) revert IMTLowLeafValueTooLarge(...);           // :86-88
        while (lowLeaf.nextValue != 0 && lowLeaf.nextValue < _value) {              // :90
            lowLeafIndex = lowLeaf.nextIndex;                                       // :91
            lowLeaf = self.leaves[lowLeafIndex];                                    // :92
        }                                                                           // :93
        ... retarget leaves[lowLeafIndex] to {value, newIndex, _value}, append
            {_value, oldNextIndex, oldNextValue}, register valueToIndex ...         // :95-106
    }

The NatSpec (:59-62) says the walk is "deliberately unbounded", and
`protocol-docs/message-root.md:95` gives the reason: hints are computed against a snapshot, so a
griefer can land inserts between a pending insert's hint and its value, and any fixed hop bound
would turn that into a revert.  It claims that "a once-valid hint stays a valid starting point
forever", so the only residual failure is out-of-gas.  The regression test is
`test_regression_insertSucceedsWithArbitrarilyStaleLowLeafHint`
(`l1-contracts/test/foundry/l1/unit/concrete/common/libraries/IndexedMerkleTree.t.sol:172-189`):
fifty inserts land between the sentinel hint and the value.

At the pin (`c67894b9`, `IndexedMerkleTree.sol:85-92`) the same hop sat in a counted loop:

    for (uint256 attempts = 0; lowLeaf.nextValue != 0 && lowLeaf.nextValue < _value; ++attempts) {
        if (attempts == MAX_LOW_INDEX_SEARCH_ATTEMPTS) revert IMTLowLeafNextTooSmall(...);  // :86-88
        lowLeafIndex = lowLeaf.nextIndex;  lowLeaf = self.leaves[lowLeafIndex];             // :90-91
    }

with `MAX_LOW_INDEX_SEARCH_ATTEMPTS = 5` (`Config.sol:66` at the pin).  `BoundedWalkV35` models
that loop, for the contrast theorems only.

## What is modelled

Everything is over the abstract leaf set of `Specs/Model.lean` (a leaf is `⟨value, nextValue⟩`,
indices erased).  The guards and the writes are unchanged since the pin apart from a line shift,
so the writes are the existing `imtInsert`.  Only the loop is new.

* `WalkV35 s v n W W'` — the `while` loop entered at `W` exits at `W'` after exactly `n` hops.  A
  hop goes to a leaf of `s` whose key is the current `nextKey`.  The concrete loop follows
  `nextIndex`; that `leaves[nextIndex]` carries value `nextValue` is the commitment tree's
  `Valid.linkAgree` (`../../L2InteropCommitmentTree/Specs/Model.lean`), so every concrete walk is a
  `WalkV35` derivation.  Under `KeyInj` the hop target is unique and the relation is a function.
  The relation has no revert: a walk that never exits has no derivation, which is the out-of-gas
  case and outside the model.
* `InsertV35 s v W₀ s'` — a successful `insert(v, hint)` whose hint leaf is `W₀`.
* `RunV35 S` — a history of no-ops and successful v35 inserts.
* `StepV35` — a history step with the inserted value made explicit.  The `some v` steps are what
  `L2InteropCommitmentTree._reportLeaf` logs (`L2InteropCommitmentTree.sol:62`, `:71-76`).
* `gapKeysV35 s k v` — the keys strictly between the hint's key `k` and `v`: the walk's length.
* `BoundedWalkV35` — the pin's counted loop, with its `revert`.

## Model boundary

* Gas is not modelled.  The walk's length is (`Properties.WalkLengthIsGapV35`); what that costs
  is outside this package.
* The concrete lift (that the `Tree`-level `lowSearch` of `L2InteropCommitmentTree` with fuel at
  least `leafCount` is this walk) is not stated here; `lowSearch_of_fuel_ge` and
  `LowSearchTerminates` in `../../L2InteropCommitmentTree/Proofs/HintSearch.lean` are its pieces.
  This package keeps `IndexedMerkleTree` below `L2InteropCommitmentTree` in the import order.
* The dedup gate reads `valueToIndex[v] != 0`; at this level it is `v ∉ keys s`, as in
  `GuardedEvolution`.
-/

namespace IMTAbstract

open Clear

/-! ## The v35 walk -/

/-- **The v35 walk** (`IndexedMerkleTree.sol:90-93` at `d9f6789`), big-step: entered at the low leaf
`W`, the `while` loop exits at `W'` after exactly `n` hops.

* `exit` — the loop test `lowLeaf.nextValue != 0 && lowLeaf.nextValue < _value` (:90) is false.
* `hop` — the test is true, and the loop moves to `leaves[lowLeaf.nextIndex]` (:91-92), a leaf of
  `s` whose key is the current `nextKey`. -/
inductive WalkV35 (s : Finset AbsLeaf) (v : UInt256) : ℕ → AbsLeaf → AbsLeaf → Prop
  | exit {W : AbsLeaf} : (W.nextKey = 0 ∨ v ≤ W.nextKey) → WalkV35 s v 0 W W
  | hop {n : ℕ} {W L W' : AbsLeaf} : W.nextKey ≠ 0 → W.nextKey < v → L ∈ s → L.key = W.nextKey →
      WalkV35 s v n L W' → WalkV35 s v (n + 1) W W'

/-- The keys strictly between `k` (the hint's key) and the inserted value `v`: the gap the walk
crosses.  `Properties.WalkLengthIsGapV35` shows the walk takes exactly this many hops. -/
def gapKeysV35 (s : Finset AbsLeaf) (k v : UInt256) : Finset UInt256 :=
  (keys s).filter (fun x => k < x ∧ x < v)

/-! ## The v35 insert and its histories -/

/-- **The v35 `insert`** (`IndexedMerkleTree.sol:65-107` at `d9f6789`): `insert(v, hint)`, whose hint
leaf is `W₀`, succeeds and leaves `s'`.  The premises are the source's checks and the walk, in
source order:

* `IMTNotInitialized` (:71-73) is implied: the hint is a leaf, so the tree is not empty.
* `v ≠ 0` — `IMTValueZero` (:74-76).
* `v ∉ keys s` — `IMTValueAlreadyExists` (:77-79).  The source reads `valueToIndex[v] != 0`; that
  this is `v ∈ keys` on a valid tree is `Contracts.InteropCommitmentTree.dedup_gate_sound`.
* `W₀ ∈ s` — `IMTLowLeafIndexOutOfBounds` (:80-82): the hint index is occupied.
* `W₀.key < v` — `IMTLowLeafValueTooLarge` (:86-88).
* `WalkV35 s v n W₀ W` — the loop (:90-93) exits at `W` after `n` hops.  No bound on `n`.

The writes (:95-106) retarget `W` to `⟨W.key, v⟩` and append `⟨v, W.nextKey⟩`: `imtInsert s W v`. -/
inductive InsertV35 (s : Finset AbsLeaf) (v : UInt256) (W₀ : AbsLeaf) : Finset AbsLeaf → Prop
  | mk {n : ℕ} {W : AbsLeaf} : v ≠ 0 → v ∉ keys s → W₀ ∈ s → W₀.key < v →
      WalkV35 s v n W₀ W → InsertV35 s v W₀ (imtInsert s W v)

/-- **A v35 history.**  Each step leaves the leaf set unchanged (a call that does not write the
tree, or one that reverts), or is a successful v35 `insert` of some value through some hint. -/
def RunV35 (S : ℕ → Finset AbsLeaf) : Prop :=
  ∀ n, S (n + 1) = S n ∨ ∃ (v : UInt256) (W₀ : AbsLeaf), InsertV35 (S n) v W₀ (S (n + 1))

/-- One step of a history whose inserted values are known: `none` does not write the tree, and
`some v` is a successful v35 insert of `v` through some hint.  The `some` entries, in order, are
what `L2InteropCommitmentTree.insert` reports through `_reportLeaf`
(`l1-contracts/contracts/atomic-interop/L2InteropCommitmentTree.sol:62`, `:71-76` at `d9f6789`). -/
def StepV35 : Option UInt256 → Finset AbsLeaf → Finset AbsLeaf → Prop
  | none, s, s' => s' = s
  | some v, s, s' => ∃ W₀ : AbsLeaf, InsertV35 s v W₀ s'

/-! ## The pin's bounded walk, for contrast -/

/-- `MAX_LOW_INDEX_SEARCH_ATTEMPTS` at the pin (`l1-contracts/contracts/common/Config.sol:66` at
`c67894b9`).  It does not exist at `d9f6789`. -/
def pinSearchAttemptsV35 : ℕ := 5

/-- **The pin's counted loop** (`IndexedMerkleTree.sol:85-92` at `c67894b9`), for contrast:
`BoundedWalkV35 s v bound a W r` says the loop, at leaf `W` with `attempts = a`, ends with `r`:
`some W'` if it exits at `W'`, `none` if it reverts with `IMTLowLeafNextTooSmall` (:86-88).  The hop
is the one of `WalkV35`.  The loop starts at `attempts = 0`. -/
inductive BoundedWalkV35 (s : Finset AbsLeaf) (v : UInt256) (bound : ℕ) :
    ℕ → AbsLeaf → Option AbsLeaf → Prop
  | exit {a : ℕ} {W : AbsLeaf} : (W.nextKey = 0 ∨ v ≤ W.nextKey) →
      BoundedWalkV35 s v bound a W (some W)
  | revert {a : ℕ} {W : AbsLeaf} : W.nextKey ≠ 0 → W.nextKey < v → a = bound →
      BoundedWalkV35 s v bound a W none
  | hop {a : ℕ} {W L : AbsLeaf} {r : Option AbsLeaf} : W.nextKey ≠ 0 → W.nextKey < v → a ≠ bound →
      L ∈ s → L.key = W.nextKey → BoundedWalkV35 s v bound (a + 1) L r →
      BoundedWalkV35 s v bound a W r

/-! ## Witness states -/

/-- The chain after `k` appends, each value inserted after the current tail: `chainSetV35 0` is the
genesis `{⟨0, 0⟩}`, and `chainSetV35 k` is `{⟨0, 1⟩, ⟨1, 2⟩, …, ⟨k - 1, k⟩, ⟨k, 0⟩}`.
`chainSetV35 6` is the leaf set of the pin's `chainTree 6`
(`../../L2InteropCommitmentTree/Specs/HintSearch.lean`), on which
`HonestInsertRevertsAtDeployedFuel` makes the pin's insert of `7` from the sentinel revert. -/
def chainSetV35 : ℕ → Finset AbsLeaf
  | 0 => {⟨0, 0⟩}
  | k + 1 => imtInsert (chainSetV35 k) ⟨(k : UInt256), 0⟩ ((k + 1 : ℕ) : UInt256)

/-- The history that inserts `1, 2, …, 7` in order, each through the sentinel hint, and then does
nothing.  Its `k`-th insert walks `k - 1` hops; the seventh walks six, one more than the pin
allowed. -/
def chainRunV35 (n : ℕ) : Finset AbsLeaf := chainSetV35 (min n 7)

end IMTAbstract
