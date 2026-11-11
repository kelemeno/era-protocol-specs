import EraSpec.Protocol.InteropAtomicity.Properties.DispatchLiveness
import EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLeg
import EraSpec.Contracts.InteropCenter.Proofs.Dispatch

/-!
# Proofs: an informed sender's atomic dispatch is enabled, unless a pinned clash

**(a)** One counting lemma does the work. In a valid tree, the loop condition at a leaf holds
iff some occupied leaf lies strictly between that leaf's value and `v` (`GapSound` for one
direction, `linkAgree` and `WindowPos` for the other), and a hop moves to the immediate
successor, so it removes exactly that successor from the set `hopsNeeded` counts (`GapSound` and
`idxInj`). Induction on the fuel then gives `SearchSucceedsIffHopsWithinFuel`; the exact-hint and
five-hop results are corollaries. An insert adds at most one leaf to the counted set, which gives
the stale-hint result.

**(b)** A closed form for `chainTree n` (`chainTree_leaf`, `chainTree_vti`), then the counted
set for hint `0` is the interval `(0, k + 2)`.

**(c)** The composed run projects step by step onto a deployed `Contracts.InteropCenter` run and
onto a `Contracts.AppendPath.Steps` run. A fresh nonzero commit value with the exact hint makes
the composed `append` succeed (`AppendPath`'s invariant gives the manager guard); a commit value
that is already a key is, by `Contracts.AppendPath.KeyPinsAppendedLegOrClash`, either a leg the
run appended (then the center's invariant ties it to a logged dispatch and the two are tied by a
salt or bundle-hash clash) or a `CommitClash` with one.
-/

namespace Contracts.DispatchLiveness

open IMTAbstract
open Contracts.InteropCommitmentTree (Tree Valid lowSearch InsertGuard maxLowIndexSearchAttempts
  chainTree Reaches Initialized toAbs setup lowAbs lowAbs_mem mem_toAbs dedup_gate_sound
  registered_is_key insert_preserves_valid reaches_valid setup_valid search_yields_guard
  insert_leafCount)
open Contracts.AppendPath (ChainState AppendSucceeds InsertSucceeds reseed)
open Contracts.InteropCenter (Params Dispatch FormedBy Validated bundleHash markSalt
  CrossSenderSaltClash BundleClash SaltClash Address Word wParams collidingParams)
open Contracts.AtomicFlowManager (LegState AppendGuard AuthorizeGuard ClaimGuard)
open Contracts.Atomicity (Chain CommitValue)
open Contracts.Refund (Obligation CommitClash)

/-! ## (a) The counted search -/

/-- The set `hopsNeeded` counts. -/
def aboveSet (T : Tree) (v : UInt256) (i : ℕ) : Finset ℕ :=
  (Finset.range T.leafCount).filter
    (fun k => (T.leaf i).value < (T.leaf k).value ∧ (T.leaf k).value < v)

lemma hopsNeeded_eq (T : Tree) (v : UInt256) (i : ℕ) :
    hopsNeeded T v i = (aboveSet T v i).card := rfl

lemma mem_aboveSet {T : Tree} {v : UInt256} {i k : ℕ} :
    k ∈ aboveSet T v i ↔
      k < T.leafCount ∧ (T.leaf i).value < (T.leaf k).value ∧ (T.leaf k).value < v := by
  simp [aboveSet, Finset.mem_filter, Finset.mem_range]

/-- `GapSound` at the index level: a leaf strictly above another bounds its `nextValue`. -/
lemma gap_index {T : Tree} (hV : Valid T) {i k : ℕ} (hi : i < T.leafCount)
    (hk : k < T.leafCount) (hlt : (T.leaf i).value < (T.leaf k).value) :
    (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue ≤ (T.leaf k).value :=
  hV.absSound.1 (lowAbs T i) (lowAbs_mem hi) (lowAbs T k) (lowAbs_mem hk) hlt

/-- `WindowPos` at the index level. -/
lemma window_index {T : Tree} (hV : Valid T) {i : ℕ} (hi : i < T.leafCount) :
    (T.leaf i).nextValue = 0 ∨ (T.leaf i).value < (T.leaf i).nextValue :=
  hV.absSound.2.2.2 (lowAbs T i) (lowAbs_mem hi)

/-- **THE LOOP CONDITION HOLDS IFF THE COUNTED SET IS NONEMPTY.** -/
lemma hop_iff_nonempty {T : Tree} (hV : Valid T) {v : UInt256} {i : ℕ} (hi : i < T.leafCount) :
    ((T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v) ↔ (aboveSet T v i).Nonempty := by
  constructor
  · rintro ⟨hnz, hlt⟩
    obtain ⟨hb, hval⟩ := hV.linkAgree i hi hnz
    have hpos : (T.leaf i).value < (T.leaf i).nextValue := by
      rcases window_index hV hi with h0 | h
      · exact absurd h0 hnz
      · exact h
    exact ⟨(T.leaf i).nextIndex, mem_aboveSet.mpr ⟨hb, by rw [hval]; exact hpos,
      by rw [hval]; exact hlt⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨hkb, hlo, hhi⟩ := mem_aboveSet.mp hk
    obtain ⟨hnz, hle⟩ := gap_index hV hi hkb hlo
    exact ⟨hnz, lt_of_le_of_lt hle hhi⟩

/-- **ONE HOP REMOVES EXACTLY THE SUCCESSOR.** -/
lemma aboveSet_hop {T : Tree} (hV : Valid T) {v : UInt256} {i : ℕ} (hi : i < T.leafCount)
    (hnz : (T.leaf i).nextValue ≠ 0) (hlt : (T.leaf i).nextValue < v) :
    (T.leaf i).nextIndex ∈ aboveSet T v i ∧
      aboveSet T v (T.leaf i).nextIndex = (aboveSet T v i).erase (T.leaf i).nextIndex := by
  obtain ⟨hb, hval⟩ := hV.linkAgree i hi hnz
  have hpos : (T.leaf i).value < (T.leaf i).nextValue := by
    rcases window_index hV hi with h0 | h
    · exact absurd h0 hnz
    · exact h
  set j := (T.leaf i).nextIndex with hj
  refine ⟨mem_aboveSet.mpr ⟨hb, by rw [hval]; exact hpos, by rw [hval]; exact hlt⟩, ?_⟩
  ext k
  rw [Finset.mem_erase, mem_aboveSet, mem_aboveSet]
  constructor
  · rintro ⟨hkb, hlo, hhi⟩
    refine ⟨?_, hkb, ?_, hhi⟩
    · rintro rfl; exact lt_irrefl _ hlo
    · rw [hval] at hlo; exact lt_trans hpos hlo
  · rintro ⟨hne, hkb, hlo, hhi⟩
    refine ⟨hkb, ?_, hhi⟩
    obtain ⟨_, hle⟩ := gap_index hV hi hkb hlo
    rw [← hval] at hle
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (hV.idxInj j hb k hkb h).symm hne

/-- **THE SEARCH SUCCEEDS IFF THE FUEL COVERS THE COUNT.** -/
theorem lowSearch_some_iff {T : Tree} (hV : Valid T) (v : UInt256) :
    ∀ (fuel i : ℕ), i < T.leafCount →
      ((∃ low, lowSearch T v fuel i = some low) ↔ (aboveSet T v i).card ≤ fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hi
    unfold lowSearch
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [ite_eq_left hc]
      have hne := (hop_iff_nonempty hV hi).mp hc
      simp only [reduceCtorEq, exists_false, nonpos_iff_eq_zero, Finset.card_eq_zero, false_iff]
      exact hne.ne_empty
    · rw [ite_eq_right hc]
      have he : ¬ (aboveSet T v i).Nonempty := fun h => hc ((hop_iff_nonempty hV hi).mpr h)
      rw [Finset.not_nonempty_iff_eq_empty] at he
      simp [he]
  | succ fuel ih =>
    intro i hi
    unfold lowSearch
    by_cases hc : (T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v
    · rw [ite_eq_left hc]
      obtain ⟨hmem, heq⟩ := aboveSet_hop hV hi hc.1 hc.2
      obtain ⟨hb, _⟩ := hV.linkAgree i hi hc.1
      rw [ih _ hb, heq, Finset.card_erase_of_mem hmem]
      have := Finset.card_pos.mpr ⟨_, hmem⟩
      omega
    · rw [ite_eq_right hc]
      have he : ¬ (aboveSet T v i).Nonempty := fun h => hc ((hop_iff_nonempty hV hi).mpr h)
      rw [Finset.not_nonempty_iff_eq_empty] at he
      simp [he]

theorem SearchSucceedsIffHopsWithinFuel : Properties.SearchSucceedsIffHopsWithinFuel :=
  fun _ hV v fuel _ hi => lowSearch_some_iff hV v fuel _ hi

/-- The exact hint stops the loop at once. -/
lemma ExactHint.not_hop {T : Tree} {v : UInt256} {i : ℕ} (h : ExactHint T v i) :
    ¬ ((T.leaf i).nextValue ≠ 0 ∧ (T.leaf i).nextValue < v) := by
  rintro ⟨hnz, hlt⟩
  rcases h.window with h0 | hle
  · exact hnz h0
  · exact absurd hlt (not_lt.mpr hle)

lemma exactHint_search {T : Tree} {v : UInt256} {i : ℕ} (h : ExactHint T v i) (fuel : ℕ) :
    lowSearch T v fuel i = some i :=
  Contracts.AppendPath.lowSearch_stop h.not_hop fuel

/-- The deployed insert flow passes with the exact hint as low leaf. -/
lemma exactHint_insertSucceeds {T : Tree} (hV : Valid T) {v : UInt256} {i : ℕ}
    (h : ExactHint T v i) (hv : v ≠ 0) (hfresh : T.valueToIndex v = 0) :
    InsertSucceeds T v i i :=
  ⟨hV.occupied.ne', hv, hfresh, h.inBounds, h.below, exactHint_search h _⟩

theorem ExactHintSucceeds : Properties.ExactHintSucceeds := by
  intro T v i h
  refine ⟨exactHint_search h, fun hV hv hfresh => ⟨exactHint_insertSucceeds hV h hv hfresh, ?_⟩⟩
  exact ⟨hV.occupied.ne', hv, hfresh, h.inBounds, h.below, h.window⟩

theorem ExactHintIffNoHops : Properties.ExactHintIffNoHops := by
  intro T hV v i hi hlow
  rw [hopsNeeded_eq, Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty,
    ← hop_iff_nonempty hV hi]
  constructor
  · exact ExactHint.not_hop
  · intro hc
    refine ⟨hi, hlow, ?_⟩
    rcases not_and_or.mp hc with h1 | h2
    · exact Or.inl (by simpa using h1)
    · exact Or.inr (not_lt.mp h2)

theorem ExactHintExistsAndIsUnique : Properties.ExactHintExistsAndIsUnique := by
  intro T hV v hv0 hfresh
  have hbelow : ∃ X ∈ toAbs T, X.key < v := by
    refine ⟨⟨(T.leaf 0).value, (T.leaf 0).nextValue⟩, mem_toAbs.mpr ⟨0, hV.occupied, rfl, rfl⟩, ?_⟩
    show (T.leaf 0).value < v
    rw [hV.sentinel]
    exact Fin.pos_iff_ne_zero.mpr hv0
  obtain ⟨W, hW, hWlt, hWwin⟩ :=
    gap_witness_exists hV.absSound.2.2.1 hV.absSound.2.2.2 hbelow hfresh
  obtain ⟨i, hi, hival, hinext⟩ := mem_toAbs.mp hW
  refine ⟨i, ⟨hi, by rw [hival]; exact hWlt, ?_⟩, ?_⟩
  · rw [hinext]
    rcases hWwin with h0 | hgt
    · exact Or.inl h0
    · exact Or.inr hgt.le
  · intro j hj
    have hexi : ExactHint T v i := ⟨hi, by rw [hival]; exact hWlt, by
      rw [hinext]
      rcases hWwin with h0 | hgt
      · exact Or.inl h0
      · exact Or.inr hgt.le⟩
    -- two exact hints carry the same value: neither can be strictly below the other
    have key : ∀ {a b : ℕ}, ExactHint T v a → ExactHint T v b →
        ¬ (T.leaf a).value < (T.leaf b).value := by
      intro a b ha hb hlt
      obtain ⟨hnz, hle⟩ := gap_index hV ha.inBounds hb.inBounds hlt
      exact ha.not_hop ⟨hnz, lt_of_le_of_lt hle hb.below⟩
    have hval : (T.leaf j).value = (T.leaf i).value := by
      rcases lt_trichotomy (T.leaf j).value (T.leaf i).value with h | h | h
      · exact absurd h (key hj hexi)
      · exact h
      · exact absurd h (key hexi hj)
    exact hV.idxInj j hj.inBounds i hi hval

theorem HintWithinFiveHopsSucceeds : Properties.HintWithinFiveHopsSucceeds := by
  intro T hV v hint hv0 hfresh hi hlow
  rw [hopsNeeded_eq, ← lowSearch_some_iff hV v _ hint hi]
  constructor
  · rintro ⟨low, hs⟩
    exact ⟨low, hs.search⟩
  · rintro ⟨low, hs⟩
    exact ⟨low, ⟨hV.occupied.ne', hv0, hfresh, hi, hlow, hs⟩⟩

/-- An insert adds at most one leaf to the counted set of an old hint. -/
lemma aboveSet_insert_subset {T : Tree} {w v : UInt256} {low hint : ℕ}
    (hhint : hint < T.leafCount) :
    aboveSet (Contracts.InteropCommitmentTree.insert T w low) v hint
      ⊆ Insert.insert T.leafCount (aboveSet T v hint) := by
  intro k hk
  obtain ⟨hkb, hlo, hhi⟩ := mem_aboveSet.mp hk
  rw [insert_leafCount] at hkb
  rcases Nat.lt_succ_iff_lt_or_eq.mp hkb with hkb | rfl
  · apply Finset.mem_insert_of_mem
    have hkv := Contracts.AppendPath.insert_value_of_ne (T := T) (v := w) (low := low)
      (i := k) hkb.ne
    have hhv := Contracts.AppendPath.insert_value_of_ne (T := T) (v := w) (low := low)
      (i := hint) hhint.ne
    rw [hkv, hhv] at hlo
    rw [hkv] at hhi
    exact mem_aboveSet.mpr ⟨hkb, hlo, hhi⟩
  · exact Finset.mem_insert_self _ _

lemma hopsNeeded_insert_le {T : Tree} {w v : UInt256} {low hint : ℕ}
    (hhint : hint < T.leafCount) :
    hopsNeeded (Contracts.InteropCommitmentTree.insert T w low) v hint
      ≤ hopsNeeded T v hint + 1 := by
  rw [hopsNeeded_eq, hopsNeeded_eq]
  exact (Finset.card_le_card (aboveSet_insert_subset hhint)).trans (Finset.card_insert_le _ _)

/-- Along `m` guarded inserts from a valid tree: validity, the hint's bounds and value, and at
most `m` more hops. -/
lemma reachesIn_hops {T : Tree} (hV : Valid T) {v : UInt256} {hint : ℕ}
    (hhint : hint < T.leafCount) :
    ∀ {m : ℕ} {U : Tree}, ReachesIn T m U →
      Valid U ∧ hint < U.leafCount ∧ (U.leaf hint).value = (T.leaf hint).value
        ∧ hopsNeeded U v hint ≤ hopsNeeded T v hint + m := by
  intro m U h
  induction h with
  | refl => exact ⟨hV, hhint, rfl, by omega⟩
  | @tail m U' _ w low hg ih =>
    obtain ⟨hVU, hb, hval, hhops⟩ := ih
    refine ⟨insert_preserves_valid hVU hg, ?_, ?_, ?_⟩
    · rw [insert_leafCount]; omega
    · rw [Contracts.AppendPath.insert_value_of_ne hb.ne]; exact hval
    · have := hopsNeeded_insert_le (w := w) (v := v) (low := low) hb
      omega

theorem StaleExactHintSurvivesFiveInserts : Properties.StaleExactHintSurvivesFiveInserts := by
  intro T U m v hint hV hex hR hm hv0 hfresh
  obtain ⟨hVU, hb, hval, hhops⟩ := reachesIn_hops hV hex.inBounds (v := v) hR
  have h0 : hopsNeeded T v hint = 0 :=
    (ExactHintIffNoHops T hV v hint hex.inBounds hex.below).mp hex
  have hlow : (U.leaf hint).value < v := by rw [hval]; exact hex.below
  exact (HintWithinFiveHopsSucceeds U hVU v hint hv0 hfresh hb hlow).mpr (by omega)

/-! ## (b) The honest chain of leaves -/

lemma natCast_val {a : ℕ} (ha : a < UInt256.size) : ((a : ℕ) : UInt256).val = a := by
  show (Fin.ofNat UInt256.size a).val = a
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt ha]

lemma natCast_lt {a b : ℕ} (ha : a < UInt256.size) (hb : b < UInt256.size) :
    ((a : ℕ) : UInt256) < ((b : ℕ) : UInt256) ↔ a < b := by
  rw [Fin.lt_def, natCast_val ha, natCast_val hb]

lemma natCast_inj {a b : ℕ} (ha : a < UInt256.size) (hb : b < UInt256.size) :
    ((a : ℕ) : UInt256) = ((b : ℕ) : UInt256) ↔ a = b := by
  rw [Fin.ext_iff, natCast_val ha, natCast_val hb]

lemma chainTree_leafCount : ∀ n, (chainTree n).leafCount = n + 1
  | 0 => rfl
  | n + 1 => by
    show (chainTree n).leafCount + 1 = n + 1 + 1
    rw [chainTree_leafCount n]

/-- **THE CLOSED FORM OF THE HONEST CHAIN.** Leaf `i < n` holds `i` and points at `i + 1`; leaf
`n` holds `n` and ends the list; the rest are the default `{0, 0, 0}`. -/
lemma chainTree_leaf (n i : ℕ) : (chainTree n).leaf i =
    if i < n then ⟨(i : UInt256), i + 1, ((i + 1 : ℕ) : UInt256)⟩
    else if i = n then ⟨(n : UInt256), 0, 0⟩ else ⟨0, 0, 0⟩ := by
  induction n generalizing i with
  | zero =>
    show setup.leaf i = _
    simp only [setup, Nat.not_lt_zero, ite_false]
    split_ifs with h
    · subst h; rfl
    · rfl
  | succ n ih =>
    show (Contracts.InteropCommitmentTree.insert (chainTree n) ((n + 1 : ℕ) : UInt256) n).leaf i
      = _
    simp only [Contracts.InteropCommitmentTree.insert, chainTree_leafCount]
    by_cases h1 : i = n
    · subst h1
      rw [ih]
      simp
    · by_cases h2 : i = n + 1
      · subst h2
        rw [ih]
        simp
      · have h3 : i < n + 1 ↔ i < n := by omega
        simp only [h1, h2, ite_false]
        rw [ih i]
        simp only [h1, h3, ite_false]

lemma chainTree_value {n i : ℕ} (hi : i ≤ n) : ((chainTree n).leaf i).value = (i : UInt256) := by
  rw [chainTree_leaf]
  rcases Nat.lt_or_eq_of_le hi with h | rfl
  · simp [h]
  · simp

lemma chainTree_nextValue_last (n : ℕ) : ((chainTree n).leaf n).nextValue = 0 := by
  rw [chainTree_leaf]
  simp

/-- No value outside `1, …, n` is registered. -/
lemma chainTree_vti (n : ℕ) (w : UInt256) (hw : ∀ j, 1 ≤ j → j ≤ n → w ≠ ((j : ℕ) : UInt256)) :
    (chainTree n).valueToIndex w = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (if w = ((n + 1 : ℕ) : UInt256) then (chainTree n).leafCount
      else (chainTree n).valueToIndex w) = 0
    rw [ite_eq_right (hw (n + 1) (by omega) le_rfl)]
    exact ih (fun j h1 h2 => hw j h1 (by omega))

/-- Each step of the honest chain is a guarded insert, below the word size. -/
lemma chainTree_guard {m : ℕ} (hm : m + 1 < UInt256.size) :
    InsertGuard (chainTree m) ((m + 1 : ℕ) : UInt256) m where
  initialized := by
    show (chainTree m).leafCount ≠ 0
    rw [chainTree_leafCount]; omega
  nonzero := by
    intro h
    have := congrArg Fin.val h
    rw [natCast_val hm] at this
    exact absurd this (by simp)
  fresh := chainTree_vti m _ (fun j h1 h2 heq => by
    rw [natCast_inj hm (by omega)] at heq; omega)
  inBounds := by rw [chainTree_leafCount]; omega
  lowBelow := by
    rw [chainTree_value le_rfl]
    exact (natCast_lt (by omega) hm).mpr (by omega)
  window := Or.inl (chainTree_nextValue_last m)

lemma chainTree_reaches : ∀ n, n < UInt256.size → Reaches setup (chainTree n)
  | 0, _ => .refl
  | n + 1, h => .tail (chainTree_reaches n (by omega)) (chainTree_guard h)

/-- The counted set for the sentinel hint is every non-sentinel leaf. -/
lemma chainTree_aboveSet (k : ℕ) (hk : k + 2 < UInt256.size) :
    aboveSet (chainTree (k + 1)) ((k + 2 : ℕ) : UInt256) 0 = (Finset.range (k + 2)).erase 0 := by
  have h0 : ((chainTree (k + 1)).leaf 0).value = ((0 : ℕ) : UInt256) := chainTree_value (by omega)
  ext j
  rw [mem_aboveSet, Finset.mem_erase, Finset.mem_range, chainTree_leafCount, h0]
  constructor
  · rintro ⟨hj, hlo, _⟩
    refine ⟨?_, hj⟩
    rintro rfl
    rw [h0] at hlo
    exact lt_irrefl _ hlo
  · rintro ⟨hne, hj⟩
    rw [chainTree_value (by omega)]
    refine ⟨hj, (natCast_lt (by omega) (by omega)).mpr (by omega),
      (natCast_lt (by omega) hk).mpr (by omega)⟩

theorem HopsNeededUnbounded : Properties.HopsNeededUnbounded := by
  intro k hk
  have hV : Valid (chainTree (k + 1)) :=
    reaches_valid (chainTree_reaches (k + 1) (by omega)) setup_valid
  have hhops : hopsNeeded (chainTree (k + 1)) ((k + 2 : ℕ) : UInt256) 0 = k + 1 := by
    rw [hopsNeeded_eq, chainTree_aboveSet k hk,
      Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
    omega
  have h0 : (0 : ℕ) < (chainTree (k + 1)).leafCount := by rw [chainTree_leafCount]; omega
  refine ⟨chainTree_reaches _ (by omega), chainTree_leafCount _, ?_, ?_, hhops, ?_, ?_⟩
  · rw [chainTree_value (by omega)]
    exact (natCast_lt (by omega) hk).mpr (by omega)
  · exact chainTree_vti _ _ (fun j h1 h2 heq => by
      rw [natCast_inj hk (by omega)] at heq; omega)
  · have hiff := lowSearch_some_iff hV ((k + 2 : ℕ) : UInt256) k 0 h0
    rw [← hopsNeeded_eq, hhops] at hiff
    cases hs : lowSearch (chainTree (k + 1)) ((k + 2 : ℕ) : UInt256) k 0 with
    | none => rfl
    | some low => exact absurd (hiff.mp ⟨low, hs⟩) (by omega)
  · refine ⟨by rw [chainTree_leafCount]; omega, ?_, Or.inl (chainTree_nextValue_last _)⟩
    rw [chainTree_value le_rfl]
    exact (natCast_lt (by omega) hk).mpr (by omega)

/-! ## (c) The composed send path -/

@[simp] lemma afterAtomic_chain (P : Params) (cv : CommitValue) (X : State) (d : Dispatch)
    (low : ℕ) :
    (X.afterAtomic P cv d low).chain = X.chain.appended cv d.atomicSend.flowId (bundleHash P d.bundle) low :=
  rfl

@[simp] lemma afterAtomic_log (P : Params) (cv : CommitValue) (X : State) (d : Dispatch)
    (low : ℕ) : (X.afterAtomic P cv d low).log = X.log ++ [d] := rfl

lemma appendLog_public {P : Params} (log : List Dispatch) {d : Dispatch}
    (hat : d.isAtomic = false) : appendLog P (log ++ [d]) = appendLog P log := by
  simp [appendLog, List.filter_append, hat]

lemma appendLog_atomic {P : Params} (log : List Dispatch) {d : Dispatch}
    (hat : d.isAtomic = true) : appendLog P (log ++ [d]) = legOf P d :: appendLog P log := by
  simp [appendLog, List.filter_append, hat]

lemma mem_appendLog {P : Params} {log : List Dispatch} {o : Obligation} :
    o ∈ appendLog P log ↔ ∃ d ∈ log, d.isAtomic = true ∧ legOf P d = o := by
  simp [appendLog, List.mem_reverse, List.mem_map, List.mem_filter, and_assoc]

lemma legOf_eq {P : Params} {d d' : Dispatch} :
    legOf P d' = legOf P d ↔
      d'.atomicSend.flowId = d.atomicSend.flowId ∧ bundleHash P d'.bundle = bundleHash P d.bundle := by
  simp [legOf]

/-- The center's view of one step: a deployed center step, or no change. -/
lemma step_center {P : Params} {cv : CommitValue} {Y Z : State} (hs : Step P cv Y Z) :
    Z.center = Y.center ∨
      Contracts.InteropCenter.Step Contracts.InteropCenter.deployed P Y.center Z.center := by
  cases hs with
  | sendPublic d hat hsalt hform =>
    right
    have heq : (Y.afterPublic d).center = Y.center.afterSend P d := by
      simp [State.center, State.afterPublic, Contracts.InteropCenter.State.afterSend, hat]
    rw [heq]
    refine Contracts.InteropCenter.Step.send d (fun _ => hsalt) hform ?_ ?_
    · intro h; rw [hat] at h; exact absurd h (by decide)
    · intro h; rw [hat] at h; exact absurd h (by decide)
  | sendAtomic d low hat hsalt hform hval happ =>
    right
    have heq : (Y.afterAtomic P cv d low).center = Y.center.afterSend P d := by
      simp [State.center, State.afterAtomic, Contracts.InteropCenter.State.afterSend, hat]
    rw [heq]
    exact Contracts.InteropCenter.Step.send d (fun _ => hsalt) hform
      (fun _ _ => hval) (fun _ => happ.legUnset)
  | authorize f hh hg => exact Or.inr (Contracts.InteropCenter.Step.authorize f hh hg)
  | claim f hh hg => exact Or.inr (Contracts.InteropCenter.Step.claim f hh hg)
  | initL2 _ => exact Or.inl rfl

/-- The center's view of a run is a deployed center run. -/
theorem reach_center {P : Params} {cv : CommitValue} {X : State} (h : Reach P cv genesis X) :
    Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P
      Contracts.InteropCenter.init X.center := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    rcases step_center hs with heq | hstep
    · rw [heq]; exact ih
    · exact .tail ih hstep

/-- The manager-and-tree view of one step: an `AppendPath` step, or no change. -/
lemma step_chain {P : Params} {cv : CommitValue} {Y Z : State} (hs : Step P cv Y Z)
    {s₀ : ChainState}
    (h : Contracts.AppendPath.Steps cv P.chainId s₀ Y.chain (appendLog P Y.log)) :
    Contracts.AppendPath.Steps cv P.chainId s₀ Z.chain (appendLog P Z.log) := by
  cases hs with
  | sendPublic d hat hsalt hform =>
    show Contracts.AppendPath.Steps cv P.chainId s₀ Y.chain (appendLog P (Y.log ++ [d]))
    rw [appendLog_public _ hat]
    exact h
  | sendAtomic d low hat hsalt hform hval happ =>
    rw [afterAtomic_chain, afterAtomic_log, appendLog_atomic _ hat]
    exact .append h happ
  | authorize f hh hg => exact .authorize h hg
  | claim f hh hg => exact .claim h hg
  | initL2 h0 => exact .initL2 h h0

/-- The manager-and-tree view of a run is an `AppendPath` run. -/
theorem reach_chain {P : Params} {cv : CommitValue} {X : State} (h : Reach P cv genesis X) :
    Contracts.AppendPath.Steps cv P.chainId Contracts.AppendPath.genesis X.chain
      (appendLog P X.log) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact step_chain hs ih

theorem DispatchRunProjectsToCenter : Properties.DispatchRunProjectsToCenter :=
  fun _ _ _ h => reach_center h

theorem DispatchRunProjectsToAppendPath : Properties.DispatchRunProjectsToAppendPath :=
  fun _ _ _ h => reach_chain h

/-- **TWO DISPATCHES WITH ONE LEG ARE TIED BY A PINNED CLASH.** On a deployed center run, a
logged dispatch `d'` and a dispatch `d` whose salt is unused, formed as `_sendBundle` forms it,
with equal bundle hashes: their bundles are equal through a cross-sender salt clash, or they are
two different bundles with one hash. -/
lemma shared_hash_clash {P : Params} {S : Contracts.InteropCenter.State}
    (hr : Contracts.InteropCenter.Reach Contracts.InteropCenter.deployed P
      Contracts.InteropCenter.init S)
    {d d' : Dispatch} (hd' : d' ∈ S.log) (hsalt : S.saltUsed d.sender d.salt = false)
    (hform : FormedBy P d) (hh : bundleHash P d'.bundle = bundleHash P d.bundle) :
    CrossSenderSaltClash P d d' ∨ BundleClash P d.bundle d'.bundle := by
  have hI := Contracts.InteropCenter.inv_reach hr
  have hused : S.saltUsed d'.sender d'.salt = true := (hI.salt _ _).mpr ⟨d', hd', rfl, rfl⟩
  by_cases hb : d.bundle = d'.bundle
  · left
    have hsalteq : d.salt = d'.salt := by simp [Contracts.InteropCenter.Dispatch.salt, hb]
    have hsender : d.sender ≠ d'.sender := by
      intro hs
      rw [hs, hsalteq, hused] at hsalt
      exact Bool.noConfusion hsalt
    refine ⟨hsalteq, hsender, ?_, ?_⟩
    · intro hpre
      exact hsender (Contracts.InteropCenter.saltPreimage_inj hpre).1
    · rw [← hform.salt, ← (hI.formed d' hd').salt, hb]
  · right
    exact ⟨hb, hh.symm⟩

theorem FreshDispatchPassesManagerGuardOrClash :
    Properties.FreshDispatchPassesManagerGuardOrClash := by
  intro P S hr d hsalt hform
  by_cases hu : S.manager.legState d.atomicSend.flowId (bundleHash P d.bundle) = .Unset
  · exact Or.inl hu
  · right
    obtain ⟨d', hd', hat', hf, hh⟩ :=
      (Contracts.InteropCenter.inv_reach hr).legs rfl _ _ hu
    exact ⟨d', hd', hat', hf, hh, shared_hash_clash hr hd' hsalt hform hh⟩

/-- **A KEY OF THE TREE IS EXPLAINED BY THE LOG.** On a reachable state, if the commit value of
`d`'s leg is a nonzero key, a `DispatchClash` holds for `d` (given an unused salt and a formed
bundle). -/
lemma key_gives_clash {P : Params} {cv : CommitValue} {X : State} (h : Reach P cv genesis X)
    {d : Dispatch} (hsalt : X.saltUsed d.sender d.salt = false) (hform : FormedBy P d)
    (hv0 : commitValueOf P cv d ≠ 0)
    (hkey : commitValueOf P cv d ∈ keys (toAbs X.chain.tree)) : DispatchClash P cv X.log d := by
  have hC := reach_chain h
  rcases (Contracts.AppendPath.KeyPinsAppendedLegOrClash cv P.chainId X.chain _ hC
    d.atomicSend.flowId (bundleHash P d.bundle) hv0 hkey).1 with hmem | ⟨o, ho, hcl⟩
  · obtain ⟨d', hd', hat', hleg⟩ := mem_appendLog.mp hmem
    refine ⟨d', hd', hat', Or.inl ⟨hleg, ?_⟩⟩
    have hh : bundleHash P d'.bundle = bundleHash P d.bundle := (legOf_eq.mp hleg).2
    exact shared_hash_clash (reach_center h) hd' hsalt hform hh
  · obtain ⟨d', hd', hat', rfl⟩ := mem_appendLog.mp ho
    exact ⟨d', hd', hat', Or.inr hcl⟩

/-- **A FRESH COMMIT VALUE PASSES THE MANAGER'S GUARD AND THE DEDUP GATE.** -/
lemma fresh_value_guards {P : Params} {cv : CommitValue} {X : State} (h : Reach P cv genesis X)
    {d : Dispatch} (hfresh : commitValueOf P cv d ∉ keys (toAbs X.chain.tree)) :
    AppendGuard X.chain.mgr d.atomicSend.flowId (bundleHash P d.bundle)
      ∧ X.chain.tree.valueToIndex (commitValueOf P cv d) = 0 := by
  have hI := Contracts.AppendPath.inv_of_steps (reach_chain h)
  refine ⟨?_, ?_⟩
  · show X.chain.mgr.legState _ _ = .Unset
    rw [hI.mgrUnset]
    intro hmem
    exact hfresh (hI.key_of_mem hmem)
  · by_contra hreg
    exact hfresh (registered_is_key hI.valid hreg)

theorem HonestDispatchEnabledOrClash : Properties.HonestDispatchEnabledOrClash := by
  intro P cv X h d hat hsalt hform hval hv0 hex
  have hV : Valid X.chain.tree := (Contracts.AppendPath.inv_of_steps (reach_chain h)).valid
  by_cases hkey : commitValueOf P cv d ∈ keys (toAbs X.chain.tree)
  · exact Or.inr (key_gives_clash h hsalt hform hv0 hkey)
  · left
    obtain ⟨hguard, hreg⟩ := fresh_value_guards h hkey
    exact Step.sendAtomic d _ hat hsalt hform hval
      ⟨hguard, exactHint_insertSucceeds hV hex hv0 hreg⟩

theorem DispatchWithinFiveHopsEnabledOrClash :
    Properties.DispatchWithinFiveHopsEnabledOrClash := by
  intro P cv X h d hat hsalt hform hval hv0 hb hlow hhops
  have hV : Valid X.chain.tree := (Contracts.AppendPath.inv_of_steps (reach_chain h)).valid
  by_cases hkey : commitValueOf P cv d ∈ keys (toAbs X.chain.tree)
  · exact Or.inr (key_gives_clash h hsalt hform hv0 hkey)
  · left
    obtain ⟨hguard, hreg⟩ := fresh_value_guards h hkey
    obtain ⟨low, hins⟩ :=
      (HintWithinFiveHopsSucceeds _ hV _ _ hv0 hreg hb hlow).mpr hhops
    exact ⟨low, Step.sendAtomic d low hat hsalt hform hval ⟨hguard, hins⟩⟩

theorem AtomicDispatchBlockedIffClash : Properties.AtomicDispatchBlockedIffClash := by
  intro P cv X h d hsalt hform hv0
  have hI := Contracts.AppendPath.inv_of_steps (reach_chain h)
  constructor
  · intro hblocked
    by_cases hkey : commitValueOf P cv d ∈ keys (toAbs X.chain.tree)
    · exact key_gives_clash h hsalt hform hv0 hkey
    · exfalso
      obtain ⟨hguard, hreg⟩ := fresh_value_guards h hkey
      obtain ⟨i, hex, -⟩ := ExactHintExistsAndIsUnique _ hI.valid _ hv0 hkey
      exact hblocked i ⟨i, hguard, exactHint_insertSucceeds hI.valid hex hv0 hreg⟩
  · rintro ⟨d', hd', hat', hcl⟩ i ⟨low, happ⟩
    rcases hcl with ⟨hleg, -⟩ | hcl
    · -- the leg is already committed, so the manager's guard fails
      have hstay := Contracts.InteropCenter.AppendedLegsStayCommitted _ P _ (reach_center h)
        d' hd' hat'
      obtain ⟨hf, hh⟩ := legOf_eq.mp hleg
      have hu : X.chain.mgr.legState d.atomicSend.flowId (bundleHash P d.bundle) = .Unset :=
        happ.legUnset
      exact hstay (by rw [hf, hh]; exact hu)
    · -- the commit value is already a key, so the dedup gate fails
      have hmem : legOf P d' ∈ appendLog P X.log := mem_appendLog.mpr ⟨d', hd', hat', rfl⟩
      have hk : commitValueOf P cv d ∈ keys (toAbs X.chain.tree) := by
        rw [show commitValueOf P cv d = Contracts.AppendPath.commitOf cv (legOf P d') from hcl.2]
        exact hI.key_of_mem hmem
      exact happ.treeInsert.not_key hI.valid hk

/-! ## Witnesses -/

/-- The tree after one append of the value `1` through the sentinel. -/
abbrev oneTree : Tree := Contracts.InteropCommitmentTree.insert setup 1 0

lemma atomicDispatch_formed (P : Params) (s : Address) (salt : Word) (hint : ℕ) :
    FormedBy P (atomicDispatch P s salt hint) :=
  ⟨rfl, rfl, List.Forall₂.cons (Contracts.InteropCenter.formsCall_direct s 0) List.Forall₂.nil⟩

lemma atomicDispatch_validated (P : Params) (s : Address) (salt : Word) (hint : ℕ) :
    Validated (atomicDispatch P s salt hint).bundle := by
  intro c hc
  simp only [atomicDispatch, Contracts.InteropCenter.wBundle, List.mem_singleton] at hc
  subst hc; rfl

lemma atomicDispatch_hash (s : Address) (salt : Word) (hint : ℕ) :
    bundleHash wParams (atomicDispatch wParams s salt hint).bundle = salt :=
  Contracts.InteropCenter.bundleHash_wParams _

/-- The first append of every witness run: the value `1` through the sentinel. -/
lemma first_append (cv : CommitValue) (f b : UInt256) (h1 : cv f b = 1) :
    AppendSucceeds cv Contracts.AppendPath.genesis f b 0 0 := by
  refine ⟨rfl, ?_⟩
  rw [h1]
  exact ⟨by unfold Initialized; decide, by decide, rfl, by decide, by decide, by decide⟩

lemma oneTree_exact_one : ExactHint oneTree 1 0 :=
  ⟨by decide, by decide, Or.inr (by decide)⟩

/-- The genesis step of a witness run, for any chain and dispatch whose commit value is `1`. -/
lemma first_step (P : Params) (cv : CommitValue) (d : Dispatch) (hat : d.isAtomic = true)
    (hform : FormedBy P d) (hval : Validated d.bundle) (hlow : d.atomicSend.lowNullifierIndex = 0)
    (h1 : commitValueOf P cv d = 1) :
    Reach P cv genesis (genesis.afterAtomic P cv d 0) := by
  refine .tail .refl (Step.sendAtomic d 0 hat rfl hform hval ?_)
  rw [hlow]
  exact first_append cv _ _ h1

lemma afterAtomic_genesis_tree (P : Params) (cv : CommitValue) (d : Dispatch)
    (h1 : commitValueOf P cv d = 1) :
    (genesis.afterAtomic P cv d 0).chain.tree = oneTree := by
  show Contracts.InteropCommitmentTree.insert setup (commitValueOf P cv d) 0 = oneTree
  rw [h1]

theorem HonestDispatchWitness : Properties.HonestDispatchWitness := by
  have hb1 := atomicDispatch_hash 1 1 0
  have hb2 : bundleHash wParams wNext.bundle = 2 := atomicDispatch_hash 2 2 1
  have hv1 : commitValueOf wParams bundleCv (atomicDispatch wParams 1 1 0) = 1 := hb1
  have hv2 : commitValueOf wParams bundleCv wNext = 2 := hb2
  have htree : wX1.chain.tree = oneTree := afterAtomic_genesis_tree _ _ _ hv1
  have hmgr : wX1.chain.mgr = Contracts.AtomicFlowManager.empty.set 7 1 .Committed := by
    show Contracts.AtomicFlowManager.empty.set 7 (bundleHash wParams _) .Committed = _
    rw [hb1]
  have hsalt : wX1.saltUsed wNext.sender wNext.salt = false := by decide
  have hex : ExactHint wX1.chain.tree (commitValueOf wParams bundleCv wNext)
      wNext.atomicSend.lowNullifierIndex := by
    rw [htree, hv2]
    exact ⟨by decide, by decide, Or.inl (by decide)⟩
  have hunset : AppendGuard wX1.chain.mgr wNext.atomicSend.flowId (bundleHash wParams wNext.bundle) := by
    show wX1.chain.mgr.legState 7 (bundleHash wParams wNext.bundle) = .Unset
    rw [hmgr, hb2]; decide
  refine ⟨first_step _ _ _ rfl (atomicDispatch_formed _ _ _ _) (atomicDispatch_validated _ _ _ _)
      rfl hv1, by simp [wX1], rfl, hsalt, atomicDispatch_formed _ _ _ _,
    atomicDispatch_validated _ _ _ _, by rw [hv2]; decide, hex, ?_, ?_, ?_⟩
  · refine Step.sendAtomic wNext 1 rfl hsalt (atomicDispatch_formed _ _ _ _)
      (atomicDispatch_validated _ _ _ _) ⟨hunset, ?_⟩
    show InsertSucceeds wX1.chain.tree (commitValueOf wParams bundleCv wNext) 1 1
    rw [htree, hv2]
    exact ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, by decide⟩
  · rintro ⟨d', hd', -, hcl⟩
    have hd'eq : d' = atomicDispatch wParams 1 1 0 := by simpa [wX1, genesis] using hd'
    subst hd'eq
    rcases hcl with ⟨hleg, -⟩ | ⟨-, hcv⟩
    · have hh := (legOf_eq.mp hleg).2
      rw [hb1, hb2] at hh
      exact absurd hh (by decide)
    · have : commitValueOf wParams bundleCv wNext
          = commitValueOf wParams bundleCv (atomicDispatch wParams 1 1 0) := hcv
      rw [hv1, hv2] at this
      exact absurd this (by decide)
  · refine ⟨1, hunset, ?_⟩
    show InsertSucceeds wX1.chain.tree (commitValueOf wParams bundleCv wNext) 0 1
    rw [htree, hv2]
    exact ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, by decide⟩

theorem CommitClashBlocksHonestDispatch : Properties.CommitClashBlocksHonestDispatch := by
  have hb1 := atomicDispatch_hash 1 1 0
  have hb2 := atomicDispatch_hash 2 2 0
  have hreach : Reach wParams constCv genesis
      (genesis.afterAtomic wParams constCv (atomicDispatch wParams 1 1 0) 0) :=
    first_step _ _ _ rfl (atomicDispatch_formed _ _ _ _) (atomicDispatch_validated _ _ _ _) rfl rfl
  have htree := afterAtomic_genesis_tree wParams constCv (atomicDispatch wParams 1 1 0) rfl
  have hsalt : (genesis.afterAtomic wParams constCv (atomicDispatch wParams 1 1 0) 0).saltUsed
      (atomicDispatch wParams 2 2 0).sender (atomicDispatch wParams 2 2 0).salt = false := by
    decide
  have hclash : DispatchClash wParams constCv
      (genesis.afterAtomic wParams constCv (atomicDispatch wParams 1 1 0) 0).log
      (atomicDispatch wParams 2 2 0) := by
    refine ⟨atomicDispatch wParams 1 1 0, by simp, rfl, Or.inr ⟨?_, by show (1 : UInt256) = 1; rfl⟩⟩
    show ((7 : UInt256), bundleHash wParams (atomicDispatch wParams 2 2 0).bundle)
      ≠ (7, bundleHash wParams (atomicDispatch wParams 1 1 0).bundle)
    rw [hb1, hb2]; decide
  refine ⟨_, atomicDispatch wParams 2 2 0, hreach, rfl, hsalt, atomicDispatch_formed _ _ _ _,
    atomicDispatch_validated _ _ _ _, by decide, ?_,
    (AtomicDispatchBlockedIffClash _ _ _ hreach _ hsalt (atomicDispatch_formed _ _ _ _)
      (by decide)).mpr hclash, hclash, ?_⟩
  · rw [htree]; exact oneTree_exact_one
  · intro d' hd' hleg
    have hd'eq : d' = atomicDispatch wParams 1 1 0 := by simpa [genesis] using hd'
    subst hd'eq
    have hh := (legOf_eq.mp hleg).2
    rw [hb1, hb2] at hh
    exact absurd hh (by decide)

/-- Under the constant keccak: sender `s`, salt `3`, one indirect call through `9`. -/
def sharingDispatch (s : Address) : Dispatch :=
  ⟨s, [Contracts.InteropCenter.wIndirect],
    Contracts.InteropCenter.wBundle collidingParams s 3 [⟨5, 9, 0, []⟩], ⟨7, 0, 100, true⟩⟩

lemma sharingDispatch_formed (s : Address) : FormedBy collidingParams (sharingDispatch s) :=
  ⟨rfl, rfl, List.Forall₂.cons (Contracts.InteropCenter.formsCall_indirect s) List.Forall₂.nil⟩

lemma sharingDispatch_validated (s : Address) : Validated (sharingDispatch s).bundle := by
  intro c hc
  simp only [sharingDispatch, Contracts.InteropCenter.wBundle, List.mem_singleton] at hc
  subst hc; rfl

theorem LegClashBlocksHonestDispatch : Properties.LegClashBlocksHonestDispatch := by
  refine ⟨?_, ?_⟩
  · have hreach : Reach collidingParams constCv genesis
        (genesis.afterAtomic collidingParams constCv (sharingDispatch 1) 0) :=
      first_step _ _ _ rfl (sharingDispatch_formed 1) (sharingDispatch_validated 1) rfl rfl
    have htree := afterAtomic_genesis_tree collidingParams constCv (sharingDispatch 1) rfl
    have hsalt : (genesis.afterAtomic collidingParams constCv (sharingDispatch 1) 0).saltUsed
        (sharingDispatch 2).sender (sharingDispatch 2).salt = false := by decide
    have hss : CrossSenderSaltClash collidingParams (sharingDispatch 2) (sharingDispatch 1) := by
      refine ⟨rfl, by decide, ?_, rfl⟩
      intro hpre
      exact absurd (Contracts.InteropCenter.saltPreimage_inj hpre).1 (by decide)
    have hclash : DispatchClash collidingParams constCv
        (genesis.afterAtomic collidingParams constCv (sharingDispatch 1) 0).log
        (sharingDispatch 2) :=
      ⟨sharingDispatch 1, by simp, rfl, Or.inl ⟨rfl, Or.inl hss⟩⟩
    refine ⟨_, sharingDispatch 2, hreach, rfl, hsalt, sharingDispatch_formed 2,
      sharingDispatch_validated 2, by decide, ?_,
      (AtomicDispatchBlockedIffClash _ _ _ hreach _ hsalt (sharingDispatch_formed 2)
        (by decide)).mpr hclash, ⟨sharingDispatch 1, by simp, rfl, rfl, hss⟩, ?_⟩
    · rw [htree]; exact oneTree_exact_one
    · intro d' hd' hcl
      have hd'eq : d' = sharingDispatch 1 := by simpa [genesis] using hd'
      subst hd'eq
      exact hcl.1 rfl
  · have hreach : Reach collidingParams constCv genesis
        (genesis.afterAtomic collidingParams constCv (atomicDispatch collidingParams 1 1 0) 0) :=
      first_step _ _ _ rfl (atomicDispatch_formed _ _ _ _) (atomicDispatch_validated _ _ _ _)
        rfl rfl
    have htree := afterAtomic_genesis_tree collidingParams constCv
      (atomicDispatch collidingParams 1 1 0) rfl
    have hsalt :
        (genesis.afterAtomic collidingParams constCv (atomicDispatch collidingParams 1 1 0) 0).saltUsed
          (atomicDispatch collidingParams 1 2 0).sender
          (atomicDispatch collidingParams 1 2 0).salt = false := by decide
    have hbc : BundleClash collidingParams (atomicDispatch collidingParams 1 2 0).bundle
        (atomicDispatch collidingParams 1 1 0).bundle := ⟨by decide, rfl⟩
    have hclash : DispatchClash collidingParams constCv
        (genesis.afterAtomic collidingParams constCv (atomicDispatch collidingParams 1 1 0) 0).log
        (atomicDispatch collidingParams 1 2 0) :=
      ⟨atomicDispatch collidingParams 1 1 0, by simp, rfl, Or.inl ⟨rfl, Or.inr hbc⟩⟩
    refine ⟨_, atomicDispatch collidingParams 1 2 0, hreach, rfl, hsalt,
      atomicDispatch_formed _ _ _ _, atomicDispatch_validated _ _ _ _, by decide, ?_,
      (AtomicDispatchBlockedIffClash _ _ _ hreach _ hsalt (atomicDispatch_formed _ _ _ _)
        (by decide)).mpr hclash,
      ⟨atomicDispatch collidingParams 1 1 0, by simp, rfl, rfl, hbc, fun h => h.2.1 rfl⟩, ?_⟩
    · rw [htree]; exact oneTree_exact_one
    · intro d' hd' hcl
      have hd'eq : d' = atomicDispatch collidingParams 1 1 0 := by simpa [genesis] using hd'
      subst hd'eq
      exact hcl.1 rfl

theorem StaleHintWitness : Properties.StaleHintWitness := by
  refine ⟨setup_valid, ⟨by decide, by decide, Or.inl rfl⟩,
    ReachesIn.tail ReachesIn.refl (Contracts.InteropCommitmentTree.setup_insertGuard (by decide)),
    by decide, ?_, by decide,
    ⟨1, by unfold Initialized; decide, by decide, by decide, by decide, by decide, by decide⟩⟩
  intro h
  rcases h.window with h0 | hle
  · exact absurd h0 (by decide)
  · exact absurd hle (by decide)

end Contracts.DispatchLiveness
