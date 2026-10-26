import EraSpec.Contracts.L2InteropCommitmentTree.Specs.Model

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


/-!
# Contract spec: `IndexedMerkleTree` / `L2InteropCommitmentTree`

The abstract state machine of the indexed Merkle tree, at the level of the
contract's OWN data — leaf indices, `nextIndex` links, and the `valueToIndex`
map — together with the projection that connects it to the order theory in
`EraSpec.Contracts.IndexedMerkleTree.Specs.Model`.

## Why this layer exists

`EraSpec.Contracts.IndexedMerkleTree.Specs.Model` models the tree as a `Finset AbsLeaf`: a leaf is a
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
   checks `valueToIndex[v] == 0`.  `dedup_gate_sound` is the missing implication.
3. The bounded search loop — the contract does not receive a correct low leaf, it
   *walks* to one from a caller-supplied hint, and reverts if the walk runs long.

This file models all three and discharges them into the `Finset` layer, so the
security corpus applies to a state machine that has the contract's shape.

## Relationship to `contracts-formal-verification`

`Tree` here is the abstract target its compiled-code proofs refine to: its
storage-level results (`#39`–`#42`: the `keccak(i‖4)` slot accessor, the pointwise
write effect, the insert-effect bridge) establish that the compiled `insert`
implements `Tree.insert` on the keccak-derived storage.  This file is the other
half of that statement — that `Tree.insert` is correct as a protocol operation.
Neither half is useful alone; see `EraSpec.Refinement` for the obligations.

## Out of scope here, deliberately

The `FullMerkle` hash tree and the root.  `Tree` carries the *list* state only;
the hash side is `EraSpec.Contracts.FullMerkle.Specs.Model` plus the concrete repo's `updateWalk`
correspondence (`#31`/`#32`).  A root is an authentication device over this
state, and mixing the two obscures which invariant does which work.
-/

namespace Contracts.InteropCommitmentTree


open IMTAbstract


abbrev Properties.mem_toAbs {T : Tree} {X : AbsLeaf} :=
  X ∈ toAbs T ↔ ∃ i < T.leafCount, (T.leaf i).value = X.key ∧ (T.leaf i).nextValue = X.nextKey


/-! ## `setup` -/

abbrev Properties.toAbs_setup :=
  toAbs setup = ({⟨0, 0⟩} : Finset AbsLeaf)


/-- **`setup` ESTABLISHES A VALID STATE.**  From fresh storage the sentinel is
seeded, the maps are empty, and the projection is the genesis singleton — so
every order invariant holds by `IMTAbstract.genesis_soundState`. -/
abbrev Properties.setup_valid :=
  Valid setup


/-! ## The dedup gate

The contract's freshness check reads `valueToIndex`.  The `Finset` layer's
`guarded_insert_sound_step` wants `v ∉ keys`.  These are different statements
about different data; this is the implication between them. -/

/-- **THE STORAGE DEDUP GATE IMPLIES SET-LEVEL FRESHNESS.**  In a valid tree, a
nonzero value with `valueToIndex[v] == 0` is absent from the key set.

Note where each hypothesis is used: `v ≠ 0` rules out the SENTINEL, which is the
one occupied leaf deliberately left unregistered.  Without it the lemma is false
— `valueToIndex[0] = 0` while `0` *is* a key — and that is exactly why the
contract's `insert` rejects `_value == 0` separately from the dedup check.  Two
guards, two distinct jobs. -/
abbrev Properties.dedup_gate_sound {T : Tree} (hV : Valid T) {v : UInt256}
    (hv0 : v ≠ 0) (hgate : T.valueToIndex v = 0) :=
  v ∉ keys (toAbs T)


/-- The converse direction, for the caller that must *establish* the gate: a
registered value is a key.  Together with `dedup_gate_sound` this makes the gate
an exact test for membership among nonzero values. -/
abbrev Properties.registered_is_key {T : Tree} (hV : Valid T) {v : UInt256}
    (hreg : T.valueToIndex v ≠ 0) :=
  v ∈ keys (toAbs T)


/-- The gate is an exact membership test on nonzero values. -/
abbrev Properties.gate_iff_absent {T : Tree} (hV : Valid T) {v : UInt256} (hv0 : v ≠ 0) :=
  T.valueToIndex v = 0 ↔ v ∉ keys (toAbs T)


/-- **THE WALK EXITS IN THE WEAK WINDOW.**  Whenever the search returns an index,
that leaf satisfies the loop-exit condition `nextValue = 0 ∨ v ≤ nextValue` — the
WEAK window, which is all the contract establishes.  (Strictness comes from the
dedup gate; see `insert_sound_step`.) -/
abbrev Properties.lowSearch_window {T : Tree} {v : UInt256} :=
  ∀ (fuel i j : ℕ), lowSearch T v fuel i = some j →
        (T.leaf j).nextValue = 0 ∨ v ≤ (T.leaf j).nextValue


/-- **THE WALK STAYS IN BOUNDS AND STAYS BELOW `v`.**  Starting from an occupied
leaf whose value is below `v`, the returned leaf is occupied and its value is
still below `v`.  Both are needed by the insert guard, and both rest on
`linkAgree`: hopping to `nextIndex` is only sound because that index really
carries `nextValue`. -/
abbrev Properties.lowSearch_sound {T : Tree} (hV : Valid T) {v : UInt256} :=
  ∀ (fuel i j : ℕ), i < T.leafCount → (T.leaf i).value < v →
        lowSearch T v fuel i = some j →
        j < T.leafCount ∧ (T.leaf j).value < v


abbrev Properties.lowAbs_mem {T : Tree} {low : ℕ} (h : low < T.leafCount) :=
  lowAbs T low ∈ toAbs T


/-- **THE INDEXED INSERT PROJECTS TO `imtInsert`.**  This is the load-bearing
lemma of the file: the contract's three-write index manipulation and the
order theory's set operation are the same thing.

The proof needs `idxInj` — without distinct values at distinct indices, erasing
the low leaf from the projection could remove a *different* index's image too,
and the two sides would differ.  That is why `idxInj` is a `Valid` field rather
than a convenience. -/
abbrev Properties.insert_projects {T : Tree} (hV : Valid T) {v : UInt256} {low : ℕ}
    (hg : InsertGuard T v low) :=
  toAbs (insert T v low) = imtInsert (toAbs T) (lowAbs T low) v


/-! ### Field-wise computation of `insert` -/

abbrev Properties.insert_leafCount {T : Tree} {v : UInt256} {low : ℕ} :=
  (insert T v low).leafCount = T.leafCount + 1


abbrev Properties.insert_vti_self {T : Tree} {v : UInt256} {low : ℕ} :=
  (insert T v low).valueToIndex v = T.leafCount


abbrev Properties.insert_vti_other {T : Tree} {v w : UInt256} {low : ℕ} (h : w ≠ v) :=
  (insert T v low).valueToIndex w = T.valueToIndex w


abbrev Properties.insert_leaf_low {T : Tree} {v : UInt256} {low : ℕ} :=
  (insert T v low).leaf low
        = { T.leaf low with nextIndex := T.leafCount, nextValue := v }


abbrev Properties.insert_leaf_new {T : Tree} {v : UInt256} {low : ℕ} (h : low < T.leafCount) :=
  (insert T v low).leaf T.leafCount
        = ⟨v, (T.leaf low).nextIndex, (T.leaf low).nextValue⟩


abbrev Properties.insert_leaf_other {T : Tree} {v : UInt256} {low i : ℕ}
    (hlow : i ≠ low) (hnew : i ≠ T.leafCount) :=
  (insert T v low).leaf i = T.leaf i


/-- The dedup gate, in index form: no occupied leaf already carries `v`. -/
abbrev Properties.fresh_value {T : Tree} (hV : Valid T) {v : UInt256} {low : ℕ}
    (hg : InsertGuard T v low) :=
  ∀ i < T.leafCount, (T.leaf i).value ≠ v


/-! ## The insert is sound

`insert_sound_step` is the order-theoretic half, inherited wholesale.  Its two
hypotheses are exactly what this file's earlier results supply: the low leaf is a
member (`lowAbs_mem`, from the bounds check) and `v` is fresh (`dedup_gate_sound`,
from the storage gate). -/

/-- **THE CONTRACT'S GUARD PERFORMS A SOUND INSERT.**  The order invariants
survive and the key set grows by exactly `v`.

Everything order-theoretic here is `IMTAbstract.guarded_insert_sound_step`; what
this statement adds is that the contract's *actual* guard — a bounds check, a
zero check, a `valueToIndex` lookup and a loop exit — discharges that theorem's
premises.  In particular the WEAK window is enough, because `dedup_gate_sound`
turns the storage gate into the freshness hypothesis that closes the boundary. -/
abbrev Properties.insert_sound_step {T : Tree} (hV : Valid T) {v : UInt256} {low : ℕ}
    (hg : InsertGuard T v low) :=
  SoundState (toAbs (insert T v low))
        ∧ keys (toAbs (insert T v low)) = Insert.insert v (keys (toAbs T))


/-- **`insert` PRESERVES EVERY INVARIANT.**  The full inductive step: index
bookkeeping (this file) and order theory (inherited) both survive.

The `linkAgree` case for the appended leaf is the one with real content: the new
leaf inherits the low leaf's `nextIndex`, and showing that index still resolves
correctly needs `nextIndex ≠ low`, which follows from `WindowPos` — a leaf cannot
be its own successor because its value is strictly below its `nextValue`.  A
model that stored only `nextValue` could not even state this. -/
abbrev Properties.insert_preserves_valid {T : Tree} (hV : Valid T) {v : UInt256} {low : ℕ}
    (hg : InsertGuard T v low) :=
  Valid (insert T v low)


/-- Every state of a run from a valid start is valid. -/
abbrev Properties.run_valid {R : ℕ → Tree} (hR : Run R) (h0 : Valid (R 0)) :=
  ∀ n, Valid (R n)


/-- **A CONTRACT RUN IS A `GuardedEvolution`.**  Projecting a run index-wise
yields exactly the history shape `EraSpec.Contracts.IndexedMerkleTree.Specs.Model` reasons about, so every
security theorem there holds of real runs.

This is the statement that makes the contract spec worth having: the security
corpus is about `Finset AbsLeaf` histories, the contract is about indexed
storage, and this is the bridge. -/
abbrev Properties.run_isGuardedEvolution {R : ℕ → Tree} (hR : Run R) (h0 : Valid (R 0)) :=
  GuardedEvolution (fun n => toAbs (R n))


/-- **A RUN FROM `setup` INHERITS THE FULL SECURITY COROLLARY.**  Concretely: at
every step of every contract run started by `setup`, a nonzero commit value is
reclaimable exactly when it is absent — so a delivered leg can never be refunded
and an undelivered one always has a witness.

Stated here as the headline consequence for the deployed contract; the
mathematics is `IMTAbstract.guardedEvolution_reclaimable_iff_absent`. -/
abbrev Properties.genesis_run_reclaimable_iff_absent {R : ℕ → Tree}
    (hR : Run R) (h0 : R 0 = setup) (n : ℕ) (v : UInt256) (hv : v ≠ 0) :=
  (∃ W ∈ toAbs (R n), W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
        ↔ v ∉ keys (toAbs (R n))


end Contracts.InteropCommitmentTree
