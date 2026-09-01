import EraSpec.Core.IMT

/-!
# Contract spec: `IndexedMerkleTree` / `L2InteropCommitmentTree`

The abstract state machine of the indexed Merkle tree, at the level of the
contract's OWN data — leaf indices, `nextIndex` links, and the `valueToIndex`
map — together with the projection that connects it to the order theory in
`EraSpec.Core.IMT`.

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
the hash side is `EraSpec.Core.Merkle` plus the concrete repo's `updateWalk`
correspondence (`#31`/`#32`).  A root is an authentication device over this
state, and mixing the two obscures which invariant does which work.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-! ## State -/

/-- A leaf preimage: the mirror of Solidity's `IMTLeaf`.  Indices are `ℕ` rather
than `UInt256` deliberately — see the ℕ-vs-`UInt256` round-trip note in the
sibling repo's `AGENTS.md`; the contract's indices are bounded by `leafCount`, so
nothing is lost and the arithmetic stays cheap. -/
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

lemma mem_toAbs {T : Tree} {X : AbsLeaf} :
    X ∈ toAbs T ↔ ∃ i < T.leafCount, (T.leaf i).value = X.key ∧ (T.leaf i).nextValue = X.nextKey := by
  unfold toAbs
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, hEq⟩
    exact ⟨i, hi, by rw [← hEq], by rw [← hEq]⟩
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨i, hi, by cases X; simp_all⟩

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

/-! ## `setup` -/

@[simp] lemma toAbs_setup : toAbs setup = ({⟨0, 0⟩} : Finset AbsLeaf) := by
  unfold toAbs setup
  simp

/-- **`setup` ESTABLISHES A VALID STATE.**  From fresh storage the sentinel is
seeded, the maps are empty, and the projection is the genesis singleton — so
every order invariant holds by `IMTAbstract.genesis_soundState`. -/
theorem setup_valid : Valid setup := by
  refine ⟨by simp [setup], by norm_num [setup], ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj _
    simp only [setup] at hi hj
    omega
  · intro i hi hlt
    simp only [setup] at hlt
    omega
  · intro v hv
    simp only [setup] at hv
    exact absurd rfl hv
  · intro i hi h
    simp only [setup] at h
    exact absurd rfl h
  · rw [toAbs_setup]; exact genesis_soundState

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
theorem dedup_gate_sound {T : Tree} (hV : Valid T) {v : UInt256}
    (hv0 : v ≠ 0) (hgate : T.valueToIndex v = 0) : v ∉ keys (toAbs T) := by
  intro hmem
  unfold keys at hmem
  obtain ⟨X, hX, hXv⟩ := Finset.mem_image.mp hmem
  obtain ⟨i, hi, hival, _⟩ := mem_toAbs.mp hX
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · exact hv0 (by rw [← hXv, ← hival, hV.sentinel])
  · have := hV.vtiAgree i hipos hi
    rw [hival, hXv, hgate] at this
    omega

/-- The converse direction, for the caller that must *establish* the gate: a
registered value is a key.  Together with `dedup_gate_sound` this makes the gate
an exact test for membership among nonzero values. -/
theorem registered_is_key {T : Tree} (hV : Valid T) {v : UInt256}
    (hreg : T.valueToIndex v ≠ 0) : v ∈ keys (toAbs T) := by
  obtain ⟨hlt, hval⟩ := hV.vtiSound v hreg
  exact Finset.mem_image.mpr
    ⟨⟨v, (T.leaf (T.valueToIndex v)).nextValue⟩,
     mem_toAbs.mpr ⟨T.valueToIndex v, hlt, hval, rfl⟩, rfl⟩

/-- The gate is an exact membership test on nonzero values. -/
theorem gate_iff_absent {T : Tree} (hV : Valid T) {v : UInt256} (hv0 : v ≠ 0) :
    T.valueToIndex v = 0 ↔ v ∉ keys (toAbs T) := by
  constructor
  · exact dedup_gate_sound hV hv0
  · intro hnot
    by_contra hreg
    exact hnot (registered_is_key hV hreg)

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

/-- **THE WALK EXITS IN THE WEAK WINDOW.**  Whenever the search returns an index,
that leaf satisfies the loop-exit condition `nextValue = 0 ∨ v ≤ nextValue` — the
WEAK window, which is all the contract establishes.  (Strictness comes from the
dedup gate; see `insert_sound_step`.) -/
theorem lowSearch_window {T : Tree} {v : UInt256} :
    ∀ (fuel i j : ℕ), lowSearch T v fuel i = some j →
      (T.leaf j).nextValue = 0 ∨ v ≤ (T.leaf j).nextValue := by
  intro fuel
  induction fuel with
  | zero =>
    intro i j h
    unfold lowSearch at h
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [if_pos hc] at h; exact absurd h (by simp)
    · rw [if_neg hc] at h
      cases Option.some.inj h
      rcases not_and_or.mp hc with h1 | h2
      · exact Or.inl (by simpa using h1)
      · exact Or.inr (le_of_not_lt h2)
  | succ fuel ih =>
    intro i j h
    unfold lowSearch at h
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [if_pos hc] at h; exact ih _ _ h
    · rw [if_neg hc] at h
      cases Option.some.inj h
      rcases not_and_or.mp hc with h1 | h2
      · exact Or.inl (by simpa using h1)
      · exact Or.inr (le_of_not_lt h2)

/-- **THE WALK STAYS IN BOUNDS AND STAYS BELOW `v`.**  Starting from an occupied
leaf whose value is below `v`, the returned leaf is occupied and its value is
still below `v`.  Both are needed by the insert guard, and both rest on
`linkAgree`: hopping to `nextIndex` is only sound because that index really
carries `nextValue`. -/
theorem lowSearch_sound {T : Tree} (hV : Valid T) {v : UInt256} :
    ∀ (fuel i j : ℕ), i < T.leafCount → (T.leaf i).value < v →
      lowSearch T v fuel i = some j →
      j < T.leafCount ∧ (T.leaf j).value < v := by
  intro fuel
  induction fuel with
  | zero =>
    intro i j hi hlow h
    unfold lowSearch at h
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [if_pos hc] at h; exact absurd h (by simp)
    · rw [if_neg hc] at h
      cases Option.some.inj h
      exact ⟨hi, hlow⟩
  | succ fuel ih =>
    intro i j hi hlow h
    unfold lowSearch at h
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [if_pos hc] at h
      obtain ⟨hnz, hlt⟩ := hc
      obtain ⟨hbound, hval⟩ := hV.linkAgree i hi hnz
      exact ih _ _ hbound (by rw [hval]; exact hlt) h
    · rw [if_neg hc] at h
      cases Option.some.inj h
      exact ⟨hi, hlow⟩

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

/-- The low leaf, as the `Finset` layer sees it. -/
def lowAbs (T : Tree) (low : ℕ) : AbsLeaf :=
  ⟨(T.leaf low).value, (T.leaf low).nextValue⟩

lemma lowAbs_mem {T : Tree} {low : ℕ} (h : low < T.leafCount) :
    lowAbs T low ∈ toAbs T :=
  mem_toAbs.mpr ⟨low, h, rfl, rfl⟩

/-- **THE INDEXED INSERT PROJECTS TO `imtInsert`.**  This is the load-bearing
lemma of the file: the contract's three-write index manipulation and the
order theory's set operation are the same thing.

The proof needs `idxInj` — without distinct values at distinct indices, erasing
the low leaf from the projection could remove a *different* index's image too,
and the two sides would differ.  That is why `idxInj` is a `Valid` field rather
than a convenience. -/
theorem insert_projects {T : Tree} (hV : Valid T) {v : UInt256} {low : ℕ}
    (hg : InsertGuard T v low) :
    toAbs (insert T v low) = imtInsert (toAbs T) (lowAbs T low) v := by
  have hlowlt := hg.inBounds
  apply Finset.ext
  intro X
  rw [mem_toAbs]
  unfold imtInsert
  simp only [Finset.mem_insert, Finset.mem_erase, mem_toAbs, lowAbs]
  constructor
  · rintro ⟨i, hi, hval, hnext⟩
    simp only [insert] at hi hval hnext
    by_cases hilow : i = low
    · subst hilow
      simp only [if_pos rfl] at hval hnext
      left
      cases X; simp_all
    · by_cases hin : i = T.leafCount
      · subst hin
        rw [if_neg hilow, if_pos rfl] at hval hnext
        right; left
        cases X; simp_all
      · rw [if_neg hilow, if_neg hin] at hval hnext
        right; right
        refine ⟨?_, ⟨i, by omega, hval, hnext⟩⟩
        -- X ≠ the low leaf: else `idxInj` forces i = low
        intro hXlow
        apply hilow
        refine hV.idxInj i (by omega) low hlowlt ?_
        rw [hval, hXlow]
    -- (all three branches discharged above)
  · rintro (rfl | rfl | ⟨hXne, i, hi, hval, hnext⟩)
    · refine ⟨low, ?_, ?_, ?_⟩
      · simp only [insert]; omega
      · simp [insert]
      · simp [insert]
    · refine ⟨T.leafCount, ?_, ?_, ?_⟩
      · simp only [insert]; omega
      · simp only [insert]
        rw [if_neg (by omega : ¬ T.leafCount = low)]
        simp
      · simp only [insert]
        rw [if_neg (by omega : ¬ T.leafCount = low)]
        simp
    · refine ⟨i, by simp only [insert]; omega, ?_, ?_⟩
      · simp only [insert]
        rw [if_neg ?hne, if_neg (by omega : ¬ i = T.leafCount)]
        · exact hval
        case hne =>
          intro hil
          apply hXne
          subst hil
          cases X; simp_all
      · simp only [insert]
        rw [if_neg ?hne, if_neg (by omega : ¬ i = T.leafCount)]
        · exact hnext
        case hne =>
          intro hil
          apply hXne
          subst hil
          cases X; simp_all

/-! ### Field-wise computation of `insert` -/

@[simp] lemma insert_leafCount {T : Tree} {v : UInt256} {low : ℕ} :
    (insert T v low).leafCount = T.leafCount + 1 := rfl

@[simp] lemma insert_vti_self {T : Tree} {v : UInt256} {low : ℕ} :
    (insert T v low).valueToIndex v = T.leafCount := by simp [insert]

lemma insert_vti_other {T : Tree} {v w : UInt256} {low : ℕ} (h : w ≠ v) :
    (insert T v low).valueToIndex w = T.valueToIndex w := by simp [insert, h]

lemma insert_leaf_low {T : Tree} {v : UInt256} {low : ℕ} :
    (insert T v low).leaf low
      = { T.leaf low with nextIndex := T.leafCount, nextValue := v } := by
  simp [insert]

lemma insert_leaf_new {T : Tree} {v : UInt256} {low : ℕ} (h : low < T.leafCount) :
    (insert T v low).leaf T.leafCount
      = ⟨v, (T.leaf low).nextIndex, (T.leaf low).nextValue⟩ := by
  simp only [insert]
  rw [if_neg (by omega : ¬ T.leafCount = low)]
  simp

lemma insert_leaf_other {T : Tree} {v : UInt256} {low i : ℕ}
    (hlow : i ≠ low) (hnew : i ≠ T.leafCount) :
    (insert T v low).leaf i = T.leaf i := by
  simp only [insert]
  rw [if_neg hlow, if_neg hnew]

/-- The dedup gate, in index form: no occupied leaf already carries `v`. -/
lemma fresh_value {T : Tree} (hV : Valid T) {v : UInt256} {low : ℕ}
    (hg : InsertGuard T v low) : ∀ i < T.leafCount, (T.leaf i).value ≠ v := by
  intro i hi hEq
  refine dedup_gate_sound hV hg.nonzero hg.fresh (Finset.mem_image.mpr ?_)
  exact ⟨⟨v, (T.leaf i).nextValue⟩, mem_toAbs.mpr ⟨i, hi, hEq, rfl⟩, rfl⟩

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
theorem insert_sound_step {T : Tree} (hV : Valid T) {v : UInt256} {low : ℕ}
    (hg : InsertGuard T v low) :
    SoundState (toAbs (insert T v low))
      ∧ keys (toAbs (insert T v low)) = Insert.insert v (keys (toAbs T)) := by
  have hstep := guarded_insert_sound_step hV.absSound (lowAbs_mem hg.inBounds)
    hg.lowBelow hg.window (dedup_gate_sound hV hg.nonzero hg.fresh)
  rw [insert_projects hV hg]
  exact hstep

/-- **`insert` PRESERVES EVERY INVARIANT.**  The full inductive step: index
bookkeeping (this file) and order theory (inherited) both survive.

The `linkAgree` case for the appended leaf is the one with real content: the new
leaf inherits the low leaf's `nextIndex`, and showing that index still resolves
correctly needs `nextIndex ≠ low`, which follows from `WindowPos` — a leaf cannot
be its own successor because its value is strictly below its `nextValue`.  A
model that stored only `nextValue` could not even state this. -/
theorem insert_preserves_valid {T : Tree} (hV : Valid T) {v : UInt256} {low : ℕ}
    (hg : InsertGuard T v low) : Valid (insert T v low) := by
  have hlow := hg.inBounds
  have hfresh := fresh_value hV hg
  have hv0 := hg.nonzero
  refine ⟨?sent, ?occ, ?inj, ?vtiA, ?vtiS, ?link, (insert_sound_step hV hg).1⟩
  case sent =>
    by_cases h0 : (0 : ℕ) = low
    · rw [← h0] at hlow ⊢
      rw [insert_leaf_low]
      simpa using hV.sentinel
    · rw [insert_leaf_other h0 (by omega)]
      exact hV.sentinel
  case occ => simp only [insert_leafCount]; omega
  case inj =>
    intro i hi j hj hEq
    simp only [insert_leafCount] at hi hj
    -- values at old indices are unchanged; the new index carries the fresh `v`
    have hval : ∀ k, k < T.leafCount + 1 → ((insert T v low).leaf k).value
        = if k = T.leafCount then v else (T.leaf k).value := by
      intro k hk
      by_cases hkn : k = T.leafCount
      · subst hkn; rw [insert_leaf_new hlow]; simp
      · rw [if_neg hkn]
        by_cases hkl : k = low
        · subst hkl; rw [insert_leaf_low]
        · rw [insert_leaf_other hkl hkn]
    rw [hval i hi, hval j hj] at hEq
    by_cases hin : i = T.leafCount <;> by_cases hjn : j = T.leafCount
    · omega
    · rw [if_pos hin, if_neg hjn] at hEq
      exact absurd hEq.symm (hfresh j (by omega))
    · rw [if_neg hin, if_pos hjn] at hEq
      exact absurd hEq (hfresh i (by omega))
    · rw [if_neg hin, if_neg hjn] at hEq
      exact hV.idxInj i (by omega) j (by omega) hEq
  case vtiA =>
    intro i hipos hi
    simp only [insert_leafCount] at hi
    by_cases hin : i = T.leafCount
    · subst hin; rw [insert_leaf_new hlow]; simpa using insert_vti_self
    · have hlt : i < T.leafCount := by omega
      have hne : (T.leaf i).value ≠ v := hfresh i hlt
      by_cases hil : i = low
      · subst hil
        rw [insert_leaf_low]
        simpa [insert_vti_other hne] using hV.vtiAgree i hipos hlt
      · rw [insert_leaf_other hil hin, insert_vti_other hne]
        exact hV.vtiAgree i hipos hlt
  case vtiS =>
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      refine ⟨by rw [insert_vti_self, insert_leafCount]; omega, ?_⟩
      rw [insert_vti_self, insert_leaf_new hlow]
    · rw [insert_vti_other hwv] at hw ⊢
      obtain ⟨hlt, hval⟩ := hV.vtiSound w hw
      refine ⟨by simp only [insert_leafCount]; omega, ?_⟩
      by_cases hidl : T.valueToIndex w = low
      · rw [hidl, insert_leaf_low]; rw [hidl] at hval; exact hval
      · rw [insert_leaf_other hidl (by omega)]; exact hval
  case link =>
    intro i hi hnz
    simp only [insert_leafCount] at hi
    by_cases hil : i = low
    -- the retargeted low leaf now points at the appended leaf
    · subst hil
      rw [insert_leaf_low] at hnz ⊢
      refine ⟨by simp only [insert_leafCount]; omega, ?_⟩
      rw [insert_leaf_new hlow]
    · by_cases hin : i = T.leafCount
      -- the appended leaf inherits the low leaf's successor
      · subst hin
        rw [insert_leaf_new hlow] at hnz ⊢
        obtain ⟨hb, hv⟩ := hV.linkAgree low hlow (by simpa using hnz)
        -- a leaf is never its own successor: `WindowPos` puts its value strictly
        -- below its `nextValue`, so `nextIndex = low` would force `x < x`
        have hne : (T.leaf low).nextIndex ≠ low := by
          intro hEq
          rw [hEq] at hv
          rcases hV.absSound.2.2.2 (lowAbs T low) (lowAbs_mem hlow) with h0 | hlt
          · exact absurd (by simpa [lowAbs] using h0) (by simpa using hnz)
          · simp only [lowAbs] at hlt
            rw [hv] at hlt
            exact absurd hlt (lt_irrefl _)
        refine ⟨by simp only [insert_leafCount]; omega, ?_⟩
        rw [insert_leaf_other hne (by omega)]
        exact hv
      -- an untouched leaf: its successor may be the low leaf, whose value is unchanged
      · rw [insert_leaf_other hil hin] at hnz ⊢
        obtain ⟨hb, hv⟩ := hV.linkAgree i (by omega) hnz
        refine ⟨by simp only [insert_leafCount]; omega, ?_⟩
        by_cases hnl : (T.leaf i).nextIndex = low
        · rw [hnl, insert_leaf_low]; rw [hnl] at hv; exact hv
        · rw [insert_leaf_other hnl (by omega)]; exact hv

/-! ## Contract runs refine to `GuardedEvolution`

The whole point of the projection.  A run of the deployed contract — `setup`
followed by any sequence of guarded inserts — projects to a history that
`EraSpec.Core.IMT`'s analytic corpus applies to verbatim: `reclaimable_iff_absent`,
exactly-once delivery, `delivered_leg_available_forever`, and the
delivered-XOR-reclaimed capstone. -/

/-- A run of the contract: each step is either idle or a guarded `insert`. -/
def Run (R : ℕ → Tree) : Prop :=
  ∀ n, R (n + 1) = R n
    ∨ ∃ (v : UInt256) (low : ℕ), InsertGuard (R n) v low ∧ R (n + 1) = insert (R n) v low

/-- Every state of a run from a valid start is valid. -/
theorem run_valid {R : ℕ → Tree} (hR : Run R) (h0 : Valid (R 0)) : ∀ n, Valid (R n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rcases hR n with heq | ⟨v, low, hg, heq⟩
    · rw [heq]; exact ih
    · rw [heq]; exact insert_preserves_valid ih hg

/-- **A CONTRACT RUN IS A `GuardedEvolution`.**  Projecting a run index-wise
yields exactly the history shape `EraSpec.Core.IMT` reasons about, so every
security theorem there holds of real runs.

This is the statement that makes the contract spec worth having: the security
corpus is about `Finset AbsLeaf` histories, the contract is about indexed
storage, and this is the bridge. -/
theorem run_isGuardedEvolution {R : ℕ → Tree} (hR : Run R) (h0 : Valid (R 0)) :
    GuardedEvolution (fun n => toAbs (R n)) := by
  intro n
  rcases hR n with heq | ⟨v, low, hg, heq⟩
  · left
    show toAbs (R (n + 1)) = toAbs (R n)
    rw [heq]
  · right
    refine ⟨lowAbs (R n) low, v, lowAbs_mem hg.inBounds, hg.lowBelow, hg.window, ?_, ?_⟩
    · exact dedup_gate_sound (run_valid hR h0 n) hg.nonzero hg.fresh
    · show toAbs (R (n + 1)) = imtInsert (toAbs (R n)) (lowAbs (R n) low) v
      rw [heq]
      exact insert_projects (run_valid hR h0 n) hg

/-- **A RUN FROM `setup` INHERITS THE FULL SECURITY COROLLARY.**  Concretely: at
every step of every contract run started by `setup`, a nonzero commit value is
reclaimable exactly when it is absent — so a delivered leg can never be refunded
and an undelivered one always has a witness.

Stated here as the headline consequence for the deployed contract; the
mathematics is `IMTAbstract.guardedEvolution_reclaimable_iff_absent`. -/
theorem genesis_run_reclaimable_iff_absent {R : ℕ → Tree}
    (hR : Run R) (h0 : R 0 = setup) (n : ℕ) (v : UInt256) (hv : v ≠ 0) :
    (∃ W ∈ toAbs (R n), W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
      ↔ v ∉ keys (toAbs (R n)) := by
  have hvalid0 : Valid (R 0) := by rw [h0]; exact setup_valid
  have hgen : toAbs (R 0) = ({⟨0, 0⟩} : Finset AbsLeaf) := by rw [h0, toAbs_setup]
  exact guardedEvolution_reclaimable_iff_absent
    (run_isGuardedEvolution hR hvalid0) hgen hv

end Contracts.InteropCommitmentTree
