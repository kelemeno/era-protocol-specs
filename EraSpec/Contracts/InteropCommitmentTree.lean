import EraSpec.Core.IMT

/-!
# Model: `IndexedMerkleTree` / `L2InteropCommitmentTree`

The abstract state machine of the indexed Merkle tree, at the level of the
contract's OWN data — leaf indices, `nextIndex` links, and the `valueToIndex`
map — together with the projection that connects it to the order theory in
`EraSpec.Core.IMT`.

**This file is definitions only.**  State, invariant, operations, guards — each
transcribed from the Solidity and nothing else.  What is *true* of them is stated
in `EraSpec.Properties.InteropCommitmentTree` and proved in
`EraSpec.Proofs.InteropCommitmentTree`.  A reviewer checking that the model is
faithful reads this file against the source; a reviewer checking what is claimed
reads the properties file; nobody has to read the proofs.

## Why this layer exists

`EraSpec.Core.IMT` models the tree as a `Finset AbsLeaf`: a leaf is a
`(key, nextKey)` pair and the *indices* are erased.  That is the right level for
the security theorems (exclusivity, delivered-XOR-reclaimed), but it is NOT the
contract's state.  The deployed `IMT` struct is

    struct IMTLeaf { uint256 value; uint256 nextIndex; uint256 nextValue; }
    struct IMT { FullMerkle.FullTree tree;
                 mapping(uint256 => IMTLeaf) leaves;
                 mapping(uint256 => uint256) valueToIndex; }

so three things the `Finset` view cannot see are load-bearing on chain:

1. `nextIndex` — the physical link the search loop walks.  Nothing in the
   `Finset` model says it agrees with `nextValue`.
2. `valueToIndex` — the dedup gate reads *this*, not the key set.  The
   `Finset`-level theorems assume freshness (`v ∉ keys s`); the contract only
   checks `valueToIndex[v] == 0`.
3. The bounded search loop — the contract does not receive a correct low leaf, it
   *walks* to one from a caller-supplied hint, and reverts if the walk runs long.

This file models all three; the properties file discharges them into the
`Finset` layer, so the security corpus applies to a state machine that has the
contract's shape.

## Relationship to `contracts-formal-verification`

`Tree` here is the abstract target its compiled-code proofs refine to: its
storage-level results (`#39`–`#42`: the `keccak(i‖4)` slot accessor, the pointwise
write effect, the insert-effect bridge) establish that the compiled `insert`
implements `Tree.insert` on the keccak-derived storage.  See `EraSpec.Refinement`
for the obligations.

## Out of scope here

The `FullMerkle` hash tree and the root: `Tree` carries the *list* state only.
The hash side is `EraSpec.Contracts.TreeRoot`, which defines the root over this
state and the two proof verifiers.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-! ## State -/

/-- A leaf preimage: the mirror of Solidity's `IMTLeaf`.  Indices are `ℕ` rather
than `UInt256` deliberately — the contract's indices are bounded by `leafCount`,
so nothing is lost and the arithmetic stays cheap. -/
structure Leaf where
  value : UInt256
  nextIndex : ℕ
  nextValue : UInt256
deriving DecidableEq

/-- The contract's list state: how many leaves are occupied, the leaf at each
index, and the value→index map.  `leaf` and `valueToIndex` are total functions;
`leafCount` says which part is meaningful, exactly as the Solidity mappings
default to zero outside the occupied range. -/
structure Tree where
  leafCount : ℕ
  leaf : ℕ → Leaf
  valueToIndex : UInt256 → ℕ

/-- `_imt.tree._leafNumber != 0` — the contract's "initialized" flag. -/
def Initialized (T : Tree) : Prop := T.leafCount ≠ 0

/-- `setup()`: reserve index 0 for the `{0,0,0}` sentinel. -/
def setup : Tree where
  leafCount := 1
  leaf := fun _ => ⟨0, 0, 0⟩
  valueToIndex := fun _ => 0

/-! ## Projection to the order-theoretic model -/

/-- The `Finset AbsLeaf` view: forget the indices, keep `(value, nextValue)`. -/
def toAbs (T : Tree) : Finset AbsLeaf :=
  (Finset.range T.leafCount).image (fun i => ⟨(T.leaf i).value, (T.leaf i).nextValue⟩)

/-- The low leaf at index `low`, as the `Finset` layer sees it. -/
def lowAbs (T : Tree) (low : ℕ) : AbsLeaf :=
  ⟨(T.leaf low).value, (T.leaf low).nextValue⟩

/-! ## Structural validity — the invariants the `Finset` view cannot state -/

/-- The index-level invariants of a well-formed tree.

`absSound` delegates the ORDER theory to `EraSpec.Core.IMT` rather than
restating it; the other five fields are exactly the facts that are invisible
there.  Keeping the split explicit is the point: a reader can see that the
sortedness argument is inherited and the index bookkeeping is proved here. -/
structure Valid (T : Tree) : Prop where
  /-- Index 0 is the sentinel: its VALUE is zero.

  Only the value, not the whole leaf.  `setup` writes `{0,0,0}`, but the very
  first `insert` goes *through* the sentinel and retargets its links, so
  `leaf 0 = ⟨0,0,0⟩` is not an invariant — it is false after one insert.  The
  sentinel's role is to be the permanent bottom of the ordering, and that is a
  statement about its value alone. -/
  sentinel : (T.leaf 0).value = 0
  /-- The tree is initialized (index 0 is occupied). -/
  occupied : 0 < T.leafCount
  /-- Distinct occupied indices carry distinct values.  This is what makes the
  projection `toAbs` index-faithful, and the index-level form of `KeyInj`. -/
  idxInj : ∀ i < T.leafCount, ∀ j < T.leafCount, (T.leaf i).value = (T.leaf j).value → i = j
  /-- Every occupied non-sentinel leaf is registered in `valueToIndex`. -/
  vtiAgree : ∀ i, 0 < i → i < T.leafCount → T.valueToIndex (T.leaf i).value = i
  /-- Every registration resolves to an occupied leaf carrying that value. -/
  vtiSound : ∀ v : UInt256, T.valueToIndex v ≠ 0 →
    T.valueToIndex v < T.leafCount ∧ (T.leaf (T.valueToIndex v)).value = v
  /-- `nextIndex` really points at the leaf holding `nextValue`.  The physical
  link and the logical successor agree — the walk the search loop performs is
  the walk the order invariant talks about. -/
  linkAgree : ∀ i < T.leafCount, (T.leaf i).nextValue ≠ 0 →
    (T.leaf i).nextIndex < T.leafCount ∧
      (T.leaf ((T.leaf i).nextIndex)).value = (T.leaf i).nextValue
  /-- The order theory, inherited. -/
  absSound : SoundState (toAbs T)

/-! ## The bounded search loop

`insert` receives a low-leaf *hint* and walks the successor chain from it,
reverting after `MAX_LOW_INDEX_SEARCH_ATTEMPTS` hops.  `none` models the revert. -/

/-- The fuelled predecessor walk.  At each step, if the current leaf's successor
is still strictly below `v`, hop to it; the loop exits when it is not.  Running
out of fuel is a revert (`none`), matching `IMTLowLeafNextTooSmall`. -/
def lowSearch (T : Tree) (v : UInt256) : ℕ → ℕ → Option ℕ
  | 0, i => if (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v then none else some i
  | fuel + 1, i =>
      if (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
        then lowSearch T v fuel ((T.leaf i).nextIndex)
        else some i

/-! ## `insert` -/

/-- The guard `insert` enforces before writing, transcribed from the source.
Field-by-field: `IMTNotInitialized`, `IMTValueZero`, `IMTValueAlreadyExists`,
`IMTLowLeafIndexOutOfBounds`, `IMTLowLeafValueTooLarge`, and the loop exit.

`window` is the WEAK form the loop actually leaves behind — `v ≤ nextValue`, not
`v < nextValue`.  Writing the strict form here would be a spec that quietly
assumes the boundary case away; the boundary is closed by `fresh` instead, and
`AttackVectors.InsertGuard.weak_window_without_dedup_breaks_keyInj` is the
countermodel showing that is the only thing that closes it. -/
structure InsertGuard (T : Tree) (v : UInt256) (low : ℕ) : Prop where
  initialized : Initialized T
  nonzero : v ≠ 0
  fresh : T.valueToIndex v = 0
  inBounds : low < T.leafCount
  lowBelow : (T.leaf low).value < v
  window : (T.leaf low).nextValue = 0 ∨ v ≤ (T.leaf low).nextValue

/-- `insert(_value, _lowLeafIndex)`: retarget the low leaf at `low`, append the
new leaf at index `leafCount`, and register the value.  The write order mirrors
the source (low leaf updated, then the new leaf, then `valueToIndex`); the state
here is a function, so order is immaterial — that it is immaterial is itself part
of what the concrete repo's pointwise write-effect result (`#41`) establishes. -/
def insert (T : Tree) (v : UInt256) (low : ℕ) : Tree where
  leafCount := T.leafCount + 1
  leaf := fun i =>
    if i = low then { T.leaf low with nextIndex := T.leafCount, nextValue := v }
    else if i = T.leafCount then ⟨v, (T.leaf low).nextIndex, (T.leaf low).nextValue⟩
    else T.leaf i
  valueToIndex := fun w => if w = v then T.leafCount else T.valueToIndex w

/-! ## Contract runs -/

/-- A run of the contract: each step is either idle or a guarded `insert`. -/
def Run (R : ℕ → Tree) : Prop :=
  ∀ n, R (n + 1) = R n
    ∨ ∃ (v : UInt256) (low : ℕ), InsertGuard (R n) v low ∧ R (n + 1) = insert (R n) v low

end Contracts.InteropCommitmentTree
