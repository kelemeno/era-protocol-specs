import EraSpec.Contracts.L2InteropCommitmentTree.Properties.Model
import EraSpec.Contracts.IndexedMerkleTree.Proofs.Model


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


lemma mem_toAbs {T : Tree} {X : AbsLeaf} :
    Properties.mem_toAbs (T := T) (X := X) := by
  unfold Properties.mem_toAbs
  exact
    by
      unfold toAbs
      simp only [Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨i, hi, hEq⟩
        exact ⟨i, hi, by rw [← hEq], by rw [← hEq]⟩
      · rintro ⟨i, hi, h1, h2⟩
        exact ⟨i, hi, by cases X; simp_all⟩


/-! ## `setup` -/

@[simp] lemma toAbs_setup :
    Properties.toAbs_setup := by
  unfold Properties.toAbs_setup
  exact
    by
      unfold toAbs setup
      simp


/-- **`setup` ESTABLISHES A VALID STATE.**  From fresh storage the sentinel is
seeded, the maps are empty, and the projection is the genesis singleton — so
every order invariant holds by `IMTAbstract.genesis_soundState`. -/
theorem setup_valid :
    Properties.setup_valid := by
  unfold Properties.setup_valid
  exact
    by
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
    (hv0 : v ≠ 0) (hgate : T.valueToIndex v = 0) :
    Properties.dedup_gate_sound (T := T) (hV := hV) (v := v) (hv0 := hv0) (hgate := hgate) := by
  unfold Properties.dedup_gate_sound
  exact
    by
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
    (hreg : T.valueToIndex v ≠ 0) :
    Properties.registered_is_key (T := T) (hV := hV) (v := v) (hreg := hreg) := by
  unfold Properties.registered_is_key
  exact
    by
      obtain ⟨hlt, hval⟩ := hV.vtiSound v hreg
      exact Finset.mem_image.mpr
        ⟨⟨v, (T.leaf (T.valueToIndex v)).nextValue⟩,
         mem_toAbs.mpr ⟨T.valueToIndex v, hlt, hval, rfl⟩, rfl⟩


/-- The gate is an exact membership test on nonzero values. -/
theorem gate_iff_absent {T : Tree} (hV : Valid T) {v : UInt256} (hv0 : v ≠ 0) :
    Properties.gate_iff_absent (T := T) (hV := hV) (v := v) (hv0 := hv0) := by
  unfold Properties.gate_iff_absent
  exact
    by
      constructor
      · exact dedup_gate_sound hV hv0
      · intro hnot
        by_contra hreg
        exact hnot (registered_is_key hV hreg)


/-- **THE WALK EXITS IN THE WEAK WINDOW.**  Whenever the search returns an index,
that leaf satisfies the loop-exit condition `nextValue = 0 ∨ v ≤ nextValue` — the
WEAK window, which is all the contract establishes.  (Strictness comes from the
dedup gate; see `insert_sound_step`.) -/
theorem lowSearch_window {T : Tree} {v : UInt256} :
    Properties.lowSearch_window (T := T) (v := v) := by
  unfold Properties.lowSearch_window
  exact
    by
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
    Properties.lowSearch_sound (T := T) (hV := hV) (v := v) := by
  unfold Properties.lowSearch_sound
  exact
    by
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


lemma lowAbs_mem {T : Tree} {low : ℕ} (h : low < T.leafCount) :
    Properties.lowAbs_mem (T := T) (low := low) (h := h) := by
  unfold Properties.lowAbs_mem
  exact
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
    Properties.insert_projects (T := T) (hV := hV) (v := v) (low := low) (hg := hg) := by
  unfold Properties.insert_projects
  exact
    by
      have hlowlt := hg.inBounds
      apply Finset.ext
      intro X
      have hmem : X ∈ toAbs (insert T v low) ↔
          ∃ i < (insert T v low).leafCount,
            ((insert T v low).leaf i).value = X.key ∧
              ((insert T v low).leaf i).nextValue = X.nextKey := mem_toAbs
      rw [hmem]
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
    Properties.insert_leafCount (T := T) (v := v) (low := low) := by
  unfold Properties.insert_leafCount
  exact
    rfl


@[simp] lemma insert_vti_self {T : Tree} {v : UInt256} {low : ℕ} :
    Properties.insert_vti_self (T := T) (v := v) (low := low) := by
  unfold Properties.insert_vti_self
  exact
    by simp [insert]


lemma insert_vti_other {T : Tree} {v w : UInt256} {low : ℕ} (h : w ≠ v) :
    Properties.insert_vti_other (T := T) (v := v) (w := w) (low := low) (h := h) := by
  unfold Properties.insert_vti_other
  exact
    by simp [insert, h]


lemma insert_leaf_low {T : Tree} {v : UInt256} {low : ℕ} :
    Properties.insert_leaf_low (T := T) (v := v) (low := low) := by
  unfold Properties.insert_leaf_low
  exact
    by
      simp [insert]


lemma insert_leaf_new {T : Tree} {v : UInt256} {low : ℕ} (h : low < T.leafCount) :
    Properties.insert_leaf_new (T := T) (v := v) (low := low) (h := h) := by
  unfold Properties.insert_leaf_new
  exact
    by
      simp only [insert]
      rw [if_neg (by omega : ¬ T.leafCount = low)]
      simp


lemma insert_leaf_other {T : Tree} {v : UInt256} {low i : ℕ}
    (hlow : i ≠ low) (hnew : i ≠ T.leafCount) :
    Properties.insert_leaf_other (T := T) (v := v) (low := low) (i := i) (hlow := hlow) (hnew := hnew) := by
  unfold Properties.insert_leaf_other
  exact
    by
      simp only [insert]
      rw [if_neg hlow, if_neg hnew]


/-- The dedup gate, in index form: no occupied leaf already carries `v`. -/
lemma fresh_value {T : Tree} (hV : Valid T) {v : UInt256} {low : ℕ}
    (hg : InsertGuard T v low) :
    Properties.fresh_value (T := T) (hV := hV) (v := v) (low := low) (hg := hg) := by
  unfold Properties.fresh_value
  exact
    by
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
    Properties.insert_sound_step (T := T) (hV := hV) (v := v) (low := low) (hg := hg) := by
  unfold Properties.insert_sound_step
  exact
    by
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
    (hg : InsertGuard T v low) :
    Properties.insert_preserves_valid (T := T) (hV := hV) (v := v) (low := low) (hg := hg) := by
  unfold Properties.insert_preserves_valid
  exact
    by
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


/-- Every state of a run from a valid start is valid. -/
theorem run_valid {R : ℕ → Tree} (hR : Run R) (h0 : Valid (R 0)) :
    Properties.run_valid (R := R) (hR := hR) (h0 := h0) := by
  unfold Properties.run_valid
  exact
    by
      intro n
      induction n with
      | zero => exact h0
      | succ n ih =>
        rcases hR n with heq | ⟨v, low, hg, heq⟩
        · rw [heq]; exact ih
        · rw [heq]; exact insert_preserves_valid ih hg


/-- **A CONTRACT RUN IS A `GuardedEvolution`.**  Projecting a run index-wise
yields exactly the history shape `EraSpec.Contracts.IndexedMerkleTree.Specs.Model` reasons about, so every
security theorem there holds of real runs.

This is the statement that makes the contract spec worth having: the security
corpus is about `Finset AbsLeaf` histories, the contract is about indexed
storage, and this is the bridge. -/
theorem run_isGuardedEvolution {R : ℕ → Tree} (hR : Run R) (h0 : Valid (R 0)) :
    Properties.run_isGuardedEvolution (R := R) (hR := hR) (h0 := h0) := by
  unfold Properties.run_isGuardedEvolution
  exact
    by
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
    Properties.genesis_run_reclaimable_iff_absent (R := R) (hR := hR) (h0 := h0) (n := n) (v := v) (hv := hv) := by
  unfold Properties.genesis_run_reclaimable_iff_absent
  exact
    by
      have hvalid0 : Valid (R 0) := by rw [h0]; exact setup_valid
      have hgen : toAbs (R 0) = ({⟨0, 0⟩} : Finset AbsLeaf) := by rw [h0, toAbs_setup]
      exact guardedEvolution_reclaimable_iff_absent
        (run_isGuardedEvolution hR hvalid0) hgen hv


end Contracts.InteropCommitmentTree
