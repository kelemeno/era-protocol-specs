import EraSpec.Contracts.DynamicIncrementalMerkle.Properties.MemoryLazy
import EraSpec.Contracts.DynamicIncrementalMerkle.Proofs.Model

/-!
# Proofs: the memory tree, its lazy push, and the stale root after `extendUntilEnd`

Proofs of `EraSpec.Contracts.DynamicIncrementalMerkle.Properties.MemoryLazy`.

The memory loop is reduced to the storage loop of `Proofs/Model.lean`, run on the allocated
arrays themselves: every index the loop touches is below the logical length, hence below the
allocation, so each checked access succeeds and reads what `getD` reads (`mPushLoop_eager`).  The
lazy loop returns early right after the first saved side, which is also the storage loop's last
write (`pushLoop_after_save`), so it leaves the same `_sides` (`mPushLoop_lazy`).  An early return
happens only when the new count is not a power of two, so the flag never survives into a growth.

`_recalculateRoot` is the honest walk from the last leaf (`honest_walk_root`): at a right child it
reads the side the last push read, which is still in place (`pushLoop_odd_unchanged`, recorded as
`MemRepresents.prev_eq`), and at a left child the level zero, which is the honest sibling because
the last leaf has nothing to its right.

The countermodel `LazyExtendStaleRoot` is evaluated symbolically.
-/

namespace Contracts.DynamicIncrementalMerkle

open MerkleSpec MerkleSpec.Verifier

/-! ## Memory accesses in range -/

theorem mem_getElem?_eq {xs : List UInt256} {i : ℕ} (hi : i < xs.length) (d : UInt256) :
    xs[i]? = some (xs.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem mset_of_lt {xs : List UInt256} {i : ℕ} (hi : i < xs.length) (v : UInt256) :
    mset xs i v = some (xs.set i v) := by
  unfold mset; rw [ite_eq_left hi]

theorem mset_of_le {xs : List UInt256} {i : ℕ} (hi : xs.length ≤ i) (v : UInt256) :
    mset xs i v = none := by
  unfold mset; rw [ite_eq_right (by omega)]

/-! ## The memory loop is the storage loop on the allocated arrays -/

/-- **The eager memory loop is the fork's storage loop.** -/
theorem mPushLoop_eager (h : Hash) (zs : List UInt256) :
    ∀ (k i ci : ℕ) (cur : UInt256) (upd : Bool) (sd : List UInt256),
      i + k ≤ sd.length → i + k ≤ zs.length →
      mPushLoop h false zs k i ci cur upd sd
        = some (.done (pushLoop h true zs k i ci cur upd sd).1,
            (pushLoop h true zs k i ci cur upd sd).2) := by
  intro k
  induction k with
  | zero => intro i ci cur upd sd _ _; rfl
  | succ k ih =>
    intro i ci cur upd sd hsd hzs
    have hzi := mem_getElem?_eq (xs := zs) (i := i) (by omega) 0
    by_cases hpar : ci % 2 = 0
    · cases upd with
      | true =>
        have e1 : mPushLoop h false zs (k + 1) i ci cur true sd
            = mPushLoop h false zs k (i + 1) (ci / 2) (h cur (zs.getD i 0)) true sd := by
          rw [mPushLoop, ite_eq_left hpar, ite_eq_left rfl, hzi, Option.bind_some]
        have e2 : pushLoop h true zs (k + 1) i ci cur true sd
            = pushLoop h true zs k (i + 1) (ci / 2) (h cur (zs.getD i 0)) true sd := by
          rw [pushLoop, ite_eq_left hpar]; rfl
        rw [e1, e2]
        exact ih (i + 1) (ci / 2) _ true sd (by omega) (by omega)
      | false =>
        have hset := mset_of_lt (xs := sd) (i := i) (by omega) cur
        have e1 : mPushLoop h false zs (k + 1) i ci cur false sd
            = mPushLoop h false zs k (i + 1) (ci / 2) (h cur (zs.getD i 0)) true (sd.set i cur) := by
          rw [mPushLoop, ite_eq_left hpar, ite_eq_right (by decide), hset, Option.bind_some, ite_eq_right (by decide), hzi, Option.bind_some]
        have e2 : pushLoop h true zs (k + 1) i ci cur false sd
            = pushLoop h true zs k (i + 1) (ci / 2) (h cur (zs.getD i 0)) true (sd.set i cur) := by
          rw [pushLoop, ite_eq_left hpar]; rfl
        rw [e1, e2]
        exact ih (i + 1) (ci / 2) _ true (sd.set i cur) (by simp; omega) (by omega)
    · have hsi := mem_getElem?_eq (xs := sd) (i := i) (by omega) 0
      have e1 : mPushLoop h false zs (k + 1) i ci cur upd sd
          = mPushLoop h false zs k (i + 1) (ci / 2) (h (sd.getD i 0) cur) upd sd := by
        rw [mPushLoop, ite_eq_right hpar, hsi, Option.bind_some]
      have e2 : pushLoop h true zs (k + 1) i ci cur upd sd
          = pushLoop h true zs k (i + 1) (ci / 2) (h (sd.getD i 0) cur) upd sd := by
        rw [pushLoop, ite_eq_right hpar]
      rw [e1, e2]
      exact ih (i + 1) (ci / 2) _ upd sd (by omega) (by omega)

/-- **The lazy memory loop leaves the storage loop's `_sides`**, and either ends like it or takes
the early return, which it does only if some low bit of the index below the height is clear. -/
theorem mPushLoop_lazy (h : Hash) (zs : List UInt256) (n : ℕ) :
    ∀ (k i : ℕ) (cur : UInt256) (upd : Bool) (sd : List UInt256),
      i + k ≤ sd.length → i + k ≤ zs.length →
      (upd = false ↔ n % 2 ^ i = 2 ^ i - 1) →
      ∃ e, mPushLoop h true zs k i (n / 2 ^ i) cur upd sd
          = some (e, (pushLoop h true zs k i (n / 2 ^ i) cur upd sd).2)
        ∧ (e = .done (pushLoop h true zs k i (n / 2 ^ i) cur upd sd).1
            ∨ (e = .early ∧ ¬ n % 2 ^ (i + k) = 2 ^ (i + k) - 1)) := by
  intro k
  induction k with
  | zero => intro i cur upd sd _ _ _; exact ⟨_, rfl, Or.inl rfl⟩
  | succ k ih =>
    intro i cur upd sd hsd hzs hupd
    have hzi := mem_getElem?_eq (xs := zs) (i := i) (by omega) 0
    by_cases hpar : n / 2 ^ i % 2 = 0
    · cases upd with
      | true =>
        have e1 : mPushLoop h true zs (k + 1) i (n / 2 ^ i) cur true sd
            = mPushLoop h true zs k (i + 1) (n / 2 ^ (i + 1)) (h cur (zs.getD i 0)) true sd := by
          rw [mPushLoop, ite_eq_left hpar, ite_eq_left rfl, hzi, Option.bind_some, div_two_pow_succ']
        have e2 : pushLoop h true zs (k + 1) i (n / 2 ^ i) cur true sd
            = pushLoop h true zs k (i + 1) (n / 2 ^ (i + 1)) (h cur (zs.getD i 0)) true sd := by
          rw [pushLoop, ite_eq_left hpar, ← div_two_pow_succ']; rfl
        have hupd' : (true = false ↔ n % 2 ^ (i + 1) = 2 ^ (i + 1) - 1) := by
          rw [allOnes_succ]
          constructor
          · intro hc; cases hc
          · rintro ⟨_, hb⟩; omega
        obtain ⟨e, he, hcase⟩ := ih (i + 1) _ true sd (by omega) (by omega) hupd'
        rw [e1, e2, show i + (k + 1) = i + 1 + k by omega]
        exact ⟨e, he, hcase⟩
      | false =>
        have hall : n % 2 ^ i = 2 ^ i - 1 := hupd.mp rfl
        have hset := mset_of_lt (xs := sd) (i := i) (by omega) cur
        have e1 : mPushLoop h true zs (k + 1) i (n / 2 ^ i) cur false sd
            = some (.early, sd.set i cur) := by
          rw [mPushLoop, ite_eq_left hpar, ite_eq_right (by decide), hset, Option.bind_some, ite_eq_left rfl]
        have e2 : (pushLoop h true zs (k + 1) i (n / 2 ^ i) cur false sd).2 = sd.set i cur := by
          rw [pushLoop, ite_eq_left hpar]
          exact pushLoop_after_save h zs k (i + 1) _ _ _
        refine ⟨.early, by rw [e1, e2], Or.inr ⟨rfl, ?_⟩⟩
        have hnot : ¬ n % 2 ^ (i + 1) = 2 ^ (i + 1) - 1 := by
          rw [allOnes_succ]; rintro ⟨_, hb⟩; omega
        exact not_allOnes_mono (by omega) hnot
    · have hodd : n / 2 ^ i % 2 = 1 := by omega
      have hsi := mem_getElem?_eq (xs := sd) (i := i) (by omega) 0
      have e1 : mPushLoop h true zs (k + 1) i (n / 2 ^ i) cur upd sd
          = mPushLoop h true zs k (i + 1) (n / 2 ^ (i + 1)) (h (sd.getD i 0) cur) upd sd := by
        rw [mPushLoop, ite_eq_right hpar, hsi, Option.bind_some, div_two_pow_succ']
      have e2 : pushLoop h true zs (k + 1) i (n / 2 ^ i) cur upd sd
          = pushLoop h true zs k (i + 1) (n / 2 ^ (i + 1)) (h (sd.getD i 0) cur) upd sd := by
        rw [pushLoop, ite_eq_right hpar, ← div_two_pow_succ']
      have hupd' : (upd = false ↔ n % 2 ^ (i + 1) = 2 ^ (i + 1) - 1) := by
        rw [allOnes_succ, hupd]
        constructor
        · intro h'; exact ⟨h', hodd⟩
        · intro h'; exact h'.1
      obtain ⟨e, he, hcase⟩ := ih (i + 1) _ upd sd (by omega) (by omega) hupd'
      rw [e1, e2, show i + (k + 1) = i + 1 + k by omega]
      exact ⟨e, he, hcase⟩

/-! ## `_pushInner` -/

/-- The fields of `MemRepresents` for the tree after a push, given its new `_sides`. -/
private theorem memRep_after_push (h : Hash) (z : UInt256) (L : List UInt256) (x : UInt256)
    (H' : ℕ) (T₂ : MemPushTree) (sd₀ sd : List UInt256) (nr : Bool)
    (hnext : T₂.next = L.length + 1) (hlast : T₂.lastLeaf = x)
    (hzl : T₂.zerosLen = H' + 1) (hsl : T₂.sidesLen = H' + 1)
    (halloc : T₂.zeros.length = T₂.sides.length) (hfits : H' + 1 ≤ T₂.sides.length)
    (hz : ∀ l, l ≤ H' → T₂.zeros.getD l 0 = zeros h z l)
    (hold : ∀ l, l < H' → OldF h z L T₂.sides l) (hcap : L.length + 1 ≤ 2 ^ H')
    (hlen : sd.length = T₂.sides.length) (hbelow : ∀ l, l < H' → sd.getD l 0 = sd₀.getD l 0)
    (hnew : ∀ l, l < H' → NewF h z L x sd₀ l)
    (hodd : ∀ l, l < H' → L.length / 2 ^ l % 2 = 1 → sd₀.getD l 0 = T₂.sides.getD l 0)
    (htop : nr = false → sd.getD H' 0 = dimRoot h z (L ++ [x]) H')
    (hlazy : nr = true → L ++ [x] ≠ [] ∧ (L ++ [x]).length < 2 ^ H') :
    MemRepresents h z (L ++ [x]) H' { T₂ with sides := sd, needsRecalc := nr } := by
  have hlenx : (L ++ [x]).length = L.length + 1 := by simp
  refine { next_eq := by simp [hnext], capacity := by rw [hlenx]; exact hcap,
           sidesLen_eq := hsl, zerosLen_eq := hzl, alloc := by simp [halloc, hlen],
           fits := by simp [hlen]; exact hfits, zeros_eq := hz, sides_eq := ?_, prev_eq := ?_,
           last_eq := ?_, top_eq := htop, lazy_notFull := hlazy }
  · intro i hi hb
    simp only
    rw [hbelow i hi]
    exact hnew i hi (by rw [hlenx] at hb; exact hb)
  · intro i hi hb
    simp only
    rw [hlenx, Nat.add_sub_cancel] at hb
    have hpos : 0 < L.length / 2 ^ i := by
      rcases Nat.eq_zero_or_pos (L.length / 2 ^ i) with h0 | h0
      · rw [h0] at hb; simp at hb
      · exact h0
    rw [hbelow i hi, hodd i hi hb, hold i hi hb, frontierNode, prevNode, hlenx, Nat.add_sub_cancel,
      levels_append_left h z L x i (L.length / 2 ^ i - 1) (Nat.sub_lt hpos Nat.one_pos)]
  · intro _
    simp only
    rw [hlast, hlenx, Nat.add_sub_cancel, getD_append_right' (le_refl _), Nat.sub_self]
    rfl

/-- **The loop and what follows it, from the tree the loop starts on.**  `T₂` is the tree after
the growth branch, at height `H'`, with room for the new leaf.  Whether eager or lazy, the call
returns index `|L|`, the new tree represents `L ++ [x]` at `H'`, an eager call clears the flag,
and with the flag clear the returned value is the new fold. -/
theorem memFinish (h : Hash) (z : UInt256) (L : List UInt256) (x : UInt256) (H' : ℕ)
    (lazy : Bool) (T₂ : MemPushTree)
    (hnext : T₂.next = L.length + 1) (hlast : T₂.lastLeaf = x)
    (hzl : T₂.zerosLen = H' + 1) (hsl : T₂.sidesLen = H' + 1)
    (halloc : T₂.zeros.length = T₂.sides.length) (hfits : H' + 1 ≤ T₂.sides.length)
    (hz : ∀ l, l ≤ H' → T₂.zeros.getD l 0 = zeros h z l)
    (hold : ∀ l, l < H' → OldF h z L T₂.sides l) (hcap : L.length + 1 ≤ 2 ^ H') :
    ∃ (T' : MemPushTree) (r : UInt256),
      (mPushLoop h lazy T₂.zeros H' 0 L.length x false T₂.sides).bind
          (mPushFinish T₂ L.length H') = some (T', L.length, r)
      ∧ MemRepresents h z (L ++ [x]) H' T'
      ∧ (lazy = false → T'.needsRecalc = false)
      ∧ (T'.needsRecalc = false → r = rootOf h z (L ++ [x]) H') := by
  have hzs : ∀ l, l < H' → T₂.zeros.getD l 0 = zeros h z l := fun l hl => hz l (by omega)
  have hspec := pushLoop_spec h z L x H' true T₂.zeros hzs H' 0 x false T₂.sides
    (by omega) (by omega) (by rw [appendPath_zero])
    (by simp [Nat.mod_one]) (fun l hl => absurd hl (Nat.not_lt_zero l)) (fun l _ hl => hold l hl)
  rw [pow_zero, Nat.div_one] at hspec
  obtain ⟨hcur, hlen, hnew⟩ := hspec
  have hodd : ∀ l, l < H' → L.length / 2 ^ l % 2 = 1 →
      (pushLoop h true T₂.zeros H' 0 L.length x false T₂.sides).2.getD l 0
        = T₂.sides.getD l 0 := by
    intro l _ hb
    have := pushLoop_odd_unchanged h true T₂.zeros L.length H' 0 x false T₂.sides l (Or.inr (Or.inr hb))
    rwa [pow_zero, Nat.div_one] at this
  set r := pushLoop h true T₂.zeros H' 0 L.length x false T₂.sides with hr
  have hroot : r.1 = rootOf h z (L ++ [x]) H' := by rw [hcur, appendPath_top h z L x H' hcap]
  have hne : L ++ [x] ≠ [] := by simp
  -- the eager ending, shared by an eager call and a lazy one that ran to the end
  have hdone : (mPushFinish T₂ L.length H' (.done r.1, r.2))
      = some ({ T₂ with sides := r.2.set H' r.1, needsRecalc := false }, L.length, r.1) := by
    simp only [mPushFinish]
    rw [mset_of_lt (by rw [hlen]; omega)]
    rfl
  have hrep_done : MemRepresents h z (L ++ [x]) H'
      { T₂ with sides := r.2.set H' r.1, needsRecalc := false } :=
    memRep_after_push h z L x H' T₂ r.2 (r.2.set H' r.1) false hnext hlast hzl hsl halloc hfits hz
      hold hcap (by rw [List.length_set, hlen]) (fun l hl => getD_set_ne' (by omega) _ _) hnew hodd
      (fun _ => by rw [getD_set_self' (by rw [hlen]; omega), hroot, dimRoot, ite_eq_right hne])
      (fun hc => by cases hc)
  cases lazy with
  | false =>
    have hloop := mPushLoop_eager h T₂.zeros H' 0 L.length x false T₂.sides (by omega)
      (by omega)
    refine ⟨_, r.1, ?_, hrep_done, fun _ => rfl, fun _ => hroot⟩
    rw [hloop, Option.bind_some, hdone]
  | true =>
    have hloop := mPushLoop_lazy h T₂.zeros L.length H' 0 x false T₂.sides (by omega) (by omega)
      (by simp [Nat.mod_one])
    rw [pow_zero, Nat.div_one, Nat.zero_add] at hloop
    obtain ⟨e, he, hcase⟩ := hloop
    rcases hcase with hd | ⟨he', hnot⟩
    · refine ⟨_, r.1, ?_, hrep_done, (fun hc => by cases hc), fun _ => hroot⟩
      rw [he, hd, Option.bind_some, hdone]
    · have hlt : L.length + 1 < 2 ^ H' := by
        have hmod : L.length % 2 ^ H' = L.length := Nat.mod_eq_of_lt (by omega)
        rw [hmod] at hnot
        omega
      refine ⟨{ T₂ with sides := r.2, needsRecalc := true }, 0, ?_, ?_, (fun hc => by cases hc),
        (fun hc => by cases hc)⟩
      · rw [he, he', Option.bind_some]
        rfl
      · exact memRep_after_push h z L x H' T₂ r.2 r.2 true hnext hlast hzl hsl halloc hfits hz
          hold hcap hlen (fun _ _ => rfl) hnew hodd (fun hc => by cases hc)
          (fun _ => ⟨hne, by simpa using hlt⟩)

/-- `_pushInner` on a tree with nonzero `_zerosLengthMemory`, with the `let`s spelled out. -/
private theorem mPushInner_eq (h : Hash) (T : MemPushTree) (x : UInt256) (lazy : Bool)
    (hz : T.zerosLen ≠ 0) :
    mPushInner h T x lazy =
      (if T.next = 2 ^ (T.zerosLen - 1) then mGrow h { T with next := T.next + 1, lastLeaf := x }
        else some { T with next := T.next + 1, lastLeaf := x }).bind fun T₂ =>
        (mPushLoop h lazy T₂.zeros (T₂.zerosLen - 1) 0 T.next x false T₂.sides).bind
          (mPushFinish T₂ T.next (T₂.zerosLen - 1)) := by
  unfold mPushInner
  rw [ite_eq_right hz]

theorem mPushInner_spec (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (T : MemPushTree)
    (x : UInt256) (lazy : Bool) (hR : MemRepresents h z L H T) :
    (L.length = 2 ^ H ∧ T.sides.length ≤ H + 1 → mPushInner h T x lazy = none)
      ∧ (¬ (L.length = 2 ^ H ∧ T.sides.length ≤ H + 1) →
          ∃ (T' : MemPushTree) (r : UInt256), mPushInner h T x lazy = some (T', L.length, r)
            ∧ MemRepresents h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H) T'
            ∧ (lazy = false → T'.needsRecalc = false)
            ∧ (T'.needsRecalc = false →
                r = rootOf h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H))) := by
  have hz0 : T.zerosLen ≠ 0 := by rw [hR.zerosLen_eq]; omega
  have hfits := hR.fits
  have halloc := hR.alloc
  have hcond : (T.next = 2 ^ (T.zerosLen - 1)) ↔ L.length = 2 ^ H := by
    rw [hR.next_eq, hR.zerosLen_eq, Nat.add_sub_cancel]
  rw [mPushInner_eq h T x lazy hz0]
  by_cases hg : L.length = 2 ^ H
  · rw [ite_eq_left (hcond.mpr hg), ite_eq_left hg]
    have hzH : T.zeros[T.zerosLen - 1]? = some (zeros h z H) := by
      rw [hR.zerosLen_eq, Nat.add_sub_cancel, mem_getElem?_eq (by omega) 0, hR.zeros_eq H le_rfl]
    have hLne : L ≠ [] := by
      intro he; rw [he] at hg; have := Nat.two_pow_pos H; simp at hg; omega
    constructor
    · rintro ⟨_, hroom⟩
      have hnone : mGrow h { T with next := T.next + 1, lastLeaf := x } = none := by
        unfold mGrow
        dsimp only
        rw [hzH, Option.bind_some, hR.zerosLen_eq, mset_of_le (by omega), Option.bind_none]
      rw [hnone, Option.bind_none]
    · intro hroom
      have hroom' : H + 1 < T.sides.length := by omega
      have hgrow : mGrow h { T with next := T.next + 1, lastLeaf := x }
          = some { T with next := T.next + 1, lastLeaf := x,
                          zeros := T.zeros.set (H + 1) (h (zeros h z H) (zeros h z H)),
                          zerosLen := H + 1 + 1,
                          sides := T.sides.set (H + 1) 0, sidesLen := H + 1 + 1 } := by
        unfold mGrow
        dsimp only
        rw [hzH, Option.bind_some, hR.zerosLen_eq, mset_of_lt (by omega), Option.bind_some,
          hR.sidesLen_eq, mset_of_lt (by omega), Option.map_some]
      rw [hgrow, Option.bind_some, hR.next_eq]
      have hnr : T.needsRecalc = false := by
        cases hn : T.needsRecalc
        · rfl
        · have := (hR.lazy_notFull hn).2; omega
      obtain ⟨T', r, hfin, hrep, heager, hval⟩ := memFinish h z L x (H + 1) lazy
        { T with next := L.length + 1, lastLeaf := x,
                 zeros := T.zeros.set (H + 1) (h (zeros h z H) (zeros h z H)),
                 zerosLen := H + 1 + 1,
                 sides := T.sides.set (H + 1) 0, sidesLen := H + 1 + 1 }
        rfl rfl rfl rfl (by simp [halloc]) (by simp; omega)
        (by
          intro l hl
          dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hl) with hl' | hl'
          · rw [getD_set_ne' (by omega)]; exact hR.zeros_eq l (by omega)
          · subst hl'; rw [getD_set_self' (by omega)]; rfl)
        (by
          intro l hl hb
          dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | hl'
          · rw [hg, pow_div_pow_mod_two hl'] at hb; omega
          · subst hl'
            rw [getD_set_ne' (by omega), hR.top_eq hnr, dimRoot, ite_eq_right hLne, frontierNode,
              hg, Nat.div_self (Nat.two_pow_pos l), Nat.sub_self, rootOf_eq_getD_zero])
        (by rw [hg, pow_succ]; have := Nat.two_pow_pos H; omega)
      exact ⟨T', r, hfin, hrep, heager, hval⟩
  · rw [ite_eq_right (mt hcond.mp hg), ite_eq_right hg, Option.bind_some, hR.next_eq]
    constructor
    · rintro ⟨hc, _⟩; exact absurd hc hg
    · intro _
      have hzl : ({ T with next := L.length + 1, lastLeaf := x } : MemPushTree).zerosLen - 1 = H := by
        show T.zerosLen - 1 = H
        rw [hR.zerosLen_eq, Nat.add_sub_cancel]
      obtain ⟨T', r, hfin, hrep, heager, hval⟩ := memFinish h z L x H lazy
        { T with next := L.length + 1, lastLeaf := x } rfl rfl hR.zerosLen_eq hR.sidesLen_eq
        halloc hfits (fun l hl => hR.zeros_eq l hl) (fun l hl hb => hR.sides_eq l hl hb)
        (by have := hR.capacity; omega)
      refine ⟨T', r, ?_, hrep, heager, hval⟩
      rw [hzl]
      exact hfin

/-! ## `setup` -/

theorem mem_setup_represents_empty (h : Hash) (z : UInt256) (depth : ℕ) :
    (depth = 0 → msetup (createTree MemPushTree.fresh depth) z = none)
      ∧ (0 < depth → ∃ T, msetup (createTree MemPushTree.fresh depth) z = some (T, 0)
          ∧ MemRepresents h z [] 0 T) := by
  constructor
  · rintro rfl
    simp [msetup, createTree, mset, MemPushTree.fresh]
  · intro hd
    have hz := mset_of_lt (xs := List.replicate depth (0 : UInt256)) (i := 0) (by simpa using hd) z
    have hs := mset_of_lt (xs := List.replicate depth (0 : UInt256)) (i := 0) (by simpa using hd) 0
    refine ⟨{ next := 0, sides := (List.replicate depth 0).set 0 0,
              zeros := (List.replicate depth 0).set 0 z, sidesLen := 1, zerosLen := 1,
              needsRecalc := false, lastLeaf := 0 }, ?_, ?_⟩
    · unfold msetup createTree MemPushTree.fresh
      dsimp only
      rw [hz, Option.bind_some, hs, Option.map_some]
    · refine { next_eq := rfl, capacity := by simp, sidesLen_eq := rfl, zerosLen_eq := rfl,
               alloc := by simp, fits := by simp; omega, zeros_eq := ?_,
               sides_eq := fun i hi => absurd hi (Nat.not_lt_zero i),
               prev_eq := fun i hi => absurd hi (Nat.not_lt_zero i),
               last_eq := fun hne => absurd rfl hne, top_eq := ?_,
               lazy_notFull := fun hc => by cases hc }
      · intro i hi
        rw [Nat.le_zero.mp hi]
        dsimp only
        rw [getD_set_self' (by simpa using hd)]
        rfl
      · intro _
        dsimp only
        rw [getD_set_self' (by simpa using hd)]
        rfl

/-! ## `_recalculateRoot` and `root` -/

/-- The siblings `_recalculateRoot` reads for the leaf at index `m`: `_sides[l]` at a right child
and `_zeros[l]` at a left one. -/
def recalcSibs (zs sd : List UInt256) (m : ℕ) : ℕ → UInt256 :=
  fun l => if m / 2 ^ l % 2 = 1 then sd.getD l 0 else zs.getD l 0

/-- **`_recalculateRoot`'s loop is a walk** with `recalcSibs` as its sibling stream. -/
theorem mRecalcLoop_eq (h : Hash) (zs sd : List UInt256) (m : ℕ) :
    ∀ (k i : ℕ) (cur : UInt256), i + k ≤ zs.length → i + k ≤ sd.length →
      mRecalcLoop h zs sd k i (m / 2 ^ i) cur
        = some (walkPure h (recalcSibs zs sd m) i k (m / 2 ^ i) cur) := by
  intro k
  induction k with
  | zero => intro i cur _ _; rfl
  | succ k ih =>
    intro i cur hzs hsd
    rw [walkPure_succ]
    by_cases hpar : m / 2 ^ i % 2 = 0
    · have hs : recalcSibs zs sd m i = zs.getD i 0 := by
        unfold recalcSibs; rw [ite_eq_right (by omega)]
      rw [mRecalcLoop, ite_eq_left hpar, mem_getElem?_eq (by omega) 0, Option.bind_some,
        ite_eq_right (by omega), hs, div_two_pow_succ']
      exact ih (i + 1) _ (by omega) (by omega)
    · have hodd : m / 2 ^ i % 2 = 1 := by omega
      have hs : recalcSibs zs sd m i = sd.getD i 0 := by
        unfold recalcSibs; rw [ite_eq_left hodd]
      rw [mRecalcLoop, ite_eq_right hpar, mem_getElem?_eq (by omega) 0, Option.bind_some,
        ite_eq_left hodd, hs, div_two_pow_succ']
      exact ih (i + 1) _ (by omega) (by omega)

/-- **`_recalculateRoot` RECOMPUTES THE FOLD** on a flagged tree: the walk from the last leaf, with
the sides the last push read and the zeros on its right, is the honest walk. -/
theorem recalculateRoot_spec (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ)
    (T : MemPushTree) (hR : MemRepresents h z L H T) (hflag : T.needsRecalc = true) :
    recalculateRoot h T = some (rootOf h z L H) := by
  obtain ⟨hne, hlt⟩ := hR.lazy_notFull hflag
  have hn : L.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hne
  have hH : 0 < H := by
    rcases Nat.eq_zero_or_pos H with h0 | h0
    · rw [h0, pow_zero] at hlt; omega
    · exact h0
  have hzl := hR.zerosLen_eq
  have hfits := hR.fits
  have halloc := hR.alloc
  -- the walk starts from the last leaf
  have hstart : (if (T.next - 1) % 2 = 0 then T.sides[0]? else some T.lastLeaf)
      = some (L.getD (L.length - 1) z) := by
    rw [hR.next_eq]
    split_ifs with hev
    · rw [mem_getElem?_eq (by omega) 0]
      have hb : L.length / 2 ^ 0 % 2 = 1 := by rw [pow_zero, Nat.div_one]; omega
      rw [hR.sides_eq 0 hH hb, frontierNode, levels_zero, pow_zero, Nat.div_one, zeros_zero]
    · rw [hR.last_eq hne]
  unfold recalculateRoot
  rw [ite_eq_right (by omega), ite_eq_right (by rw [hR.next_eq]; exact hn), hstart, Option.bind_some,
    hzl, Nat.add_sub_cancel, hR.next_eq]
  have hloop := mRecalcLoop_eq h T.zeros T.sides (L.length - 1) H 0 (L.getD (L.length - 1) z)
    (by omega) (by omega)
  rw [pow_zero, Nat.div_one] at hloop
  rw [hloop]
  congr 1
  have hcongr := walkPure_congr_sibs h (recalcSibs T.zeros T.sides (L.length - 1))
    (honestSibs h z L (L.length - 1)) H 0 (L.length - 1) (L.getD (L.length - 1) z) (by
      intro l _ hl
      unfold recalcSibs honestSibs
      split_ifs with hb
      · rw [hR.prev_eq l (by omega) hb, prevNode, show sibIdx ((L.length - 1) / 2 ^ l)
            = (L.length - 1) / 2 ^ l - 1 from by simp [sibIdx, hb]]
      · have hb0 : (L.length - 1) / 2 ^ l % 2 = 0 := by omega
        rw [hR.zeros_eq l (by omega), show sibIdx ((L.length - 1) / 2 ^ l)
            = (L.length - 1) / 2 ^ l + 1 from by simp [sibIdx, hb0],
          getD_default _ _ _ (by rw [levels_length h z L hn l])])
  rw [hcongr]
  exact honest_walk_root h z L H (L.length - 1) (by omega)

theorem mRoot_spec (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (T : MemPushTree)
    (hR : MemRepresents h z L H T) :
    ∃ T', mRoot h T = some (T', dimRoot h z L H) ∧ MemRepresents h z L H T'
      ∧ T'.needsRecalc = false := by
  have hsl := hR.sidesLen_eq
  have hfits := hR.fits
  cases hflag : T.needsRecalc with
  | false =>
    refine ⟨T, ?_, hR, hflag⟩
    unfold mRoot
    rw [hflag, ite_eq_right (by decide), ite_eq_right (by omega), hsl, Nat.add_sub_cancel,
      mem_getElem?_eq (by omega) 0, Option.map_some, hR.top_eq hflag]
  | true =>
    have hne := (hR.lazy_notFull hflag).1
    have hrec := recalculateRoot_spec h z L H T hR hflag
    have hdim : dimRoot h z L H = rootOf h z L H := by rw [dimRoot, ite_eq_right hne]
    refine ⟨{ T with sides := T.sides.set H (rootOf h z L H), needsRecalc := false }, ?_, ?_, rfl⟩
    · unfold mRoot
      rw [hflag, ite_eq_left rfl, hrec, Option.bind_some, ite_eq_right (by omega), hsl,
        Nat.add_sub_cancel, mset_of_lt (by omega), Option.map_some, hdim]
    · refine { next_eq := hR.next_eq, capacity := hR.capacity, sidesLen_eq := hsl,
               zerosLen_eq := hR.zerosLen_eq, alloc := by simp [hR.alloc],
               fits := by simp; exact hfits, zeros_eq := hR.zeros_eq, sides_eq := ?_,
               prev_eq := ?_, last_eq := hR.last_eq, top_eq := ?_,
               lazy_notFull := fun hc => by cases hc }
      · intro i hi hb
        dsimp only
        rw [getD_set_ne' (by omega)]
        exact hR.sides_eq i hi hb
      · intro i hi hb
        dsimp only
        rw [getD_set_ne' (by omega)]
        exact hR.prev_eq i hi hb
      · intro _
        dsimp only
        rw [getD_set_self' (by omega), hdim]

/-! ## Runs -/

private lemma memStep_represents (h : Hash) (z : UInt256) (L L' : List UInt256)
    (T T' : MemPushTree) (hR : MemRepresents h z L (dimHeight L.length) T)
    (hstep : MemStep h (L, T) (L', T')) :
    MemRepresents h z L' (dimHeight L'.length) T' := by
  -- both kinds of step are `_pushInner` returning `T'`
  have hinner : ∃ (x : UInt256) (lazy : Bool) (i : ℕ) (r : UInt256), L' = L ++ [x]
      ∧ mPushInner h T x lazy = some (T', i, r) := by
    cases hstep with
    | push hp => exact ⟨_, false, _, _, rfl, hp⟩
    | pushLazy hp =>
      unfold mPushLazy at hp
      cases hq : mPushInner h T _ true with
      | none => rw [hq] at hp; cases hp
      | some q =>
        rw [hq, Option.map_some] at hp
        obtain ⟨hT, hi⟩ := Prod.mk.inj (Option.some.inj hp)
        exact ⟨_, true, q.2.1, q.2.2, rfl, by rw [hq, ← hT]⟩
  obtain ⟨x, lazy, i, r, rfl, hp⟩ := hinner
  obtain ⟨hnone, hsome⟩ := mPushInner_spec h z L _ T x lazy hR
  by_cases hroom : L.length = 2 ^ dimHeight L.length ∧ T.sides.length ≤ dimHeight L.length + 1
  · rw [hnone hroom] at hp; cases hp
  · obtain ⟨T'', r'', hp'', hR'', _, _⟩ := hsome hroom
    rw [hp''] at hp
    have hT : T'' = T' := (Prod.mk.inj (Option.some.inj hp)).1
    subst hT
    rw [List.length_append, List.length_singleton, dimHeight_succ]
    exact hR''

theorem memRun_represents (h : Hash) (z : UInt256) (depth : ℕ) (L : List UInt256)
    (T : MemPushTree) (hT : MemRun h z depth L T) : MemRepresents h z L (dimHeight L.length) T := by
  induction hT with
  | @setup T r hs =>
    obtain ⟨h0, hpos⟩ := mem_setup_represents_empty h z depth
    rcases Nat.eq_zero_or_pos depth with hd | hd
    · rw [h0 hd] at hs; cases hs
    · obtain ⟨T₀, hs₀, hR₀⟩ := hpos hd
      rw [hs₀] at hs
      have : T₀ = T := (Prod.mk.inj (Option.some.inj hs)).1
      subst this
      exact hR₀
  | step _ hstep ih => exact memStep_represents h z _ _ _ _ ih hstep

theorem lazy_root_recalculated (h : Hash) (z : UInt256) (depth : ℕ) (L : List UInt256)
    (T : MemPushTree) (hT : MemRun h z depth L T) :
    MemRepresents h z L (dimHeight L.length) T
      ∧ ∃ T', mRoot h T = some (T', dimRoot h z L (dimHeight L.length))
          ∧ T'.needsRecalc = false := by
  have hR := memRun_represents h z depth L T hT
  obtain ⟨T', hroot, _, hflag⟩ := mRoot_spec h z L _ T hR
  exact ⟨hR, T', hroot, hflag⟩

theorem lazy_flag_means_not_full (h : Hash) (z : UInt256) (depth : ℕ) (L : List UInt256)
    (T : MemPushTree) (hT : MemRun h z depth L T) (hflag : T.needsRecalc = true) :
    L ≠ [] ∧ L.length < 2 ^ dimHeight L.length :=
  (memRun_represents h z depth L T hT).lazy_notFull hflag

theorem memory_matches_storage (h : Hash) (z : UInt256) (depth : ℕ) (L : List UInt256)
    (T : MemPushTree) (S : PushTree) (hT : MemRun h z depth L T) (hS : Run h z L S) :
    (mRoot h T).map (·.2) = root S ∧ mHeight T = height S
      ∧ ∀ (x : UInt256) (T' : MemPushTree) (i : ℕ) (r : UInt256), mPush h T x = some (T', i, r) →
          ∃ S', push h S x = some (S', i, r) := by
  have hRm := memRun_represents h z depth L T hT
  have hRs := run_represents h z L S hS
  obtain ⟨T', hroot, _, _⟩ := mRoot_spec h z L _ T hRm
  obtain ⟨hsroot, hsheight⟩ := root_is_fold h z L _ S hRs
  refine ⟨by rw [hroot, hsroot]; rfl, ?_, ?_⟩
  · unfold mHeight
    rw [hsheight, hRm.sidesLen_eq, ite_eq_right (by omega), Nat.add_sub_cancel]
  · intro x T' i r hp
    obtain ⟨hnone, hsome⟩ := mPushInner_spec h z L _ T x false hRm
    by_cases hroom : L.length = 2 ^ dimHeight L.length ∧ T.sides.length ≤ dimHeight L.length + 1
    · unfold mPush at hp; rw [hnone hroom] at hp; cases hp
    · obtain ⟨T'', r'', hp'', _, heager, hval⟩ := hsome hroom
      unfold mPush at hp
      rw [hp''] at hp
      obtain ⟨_, hir⟩ := Prod.mk.inj (Option.some.inj hp)
      obtain ⟨hi, hr⟩ := Prod.mk.inj hir
      obtain ⟨S', hps, _⟩ := push_computes_root h z L _ S x hRs
      rw [← hi, ← hr, hval (heager rfl)]
      exact ⟨S', hps⟩

/-! ## The countermodel -/

private lemma foldl_none (h : Hash) (xs : List UInt256) (lazy : Bool) :
    xs.foldl (fun o x => o.bind fun T => (mPushInner h T x lazy).map (·.1)) none = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

/-- Folding `_pushInner` over a list from a run is a run. -/
private lemma foldl_run (h : Hash) (z : UInt256) (depth : ℕ) (lazy : Bool) :
    ∀ (xs L₀ : List UInt256) (T₀ T : MemPushTree), MemRun h z depth L₀ T₀ →
      xs.foldl (fun o x => o.bind fun T => (mPushInner h T x lazy).map (·.1)) (some T₀) = some T →
      MemRun h z depth (L₀ ++ xs) T := by
  intro xs
  induction xs with
  | nil =>
    intro L₀ T₀ T hT hf
    simp only [List.foldl_nil, Option.some.injEq] at hf
    subst hf
    simpa using hT
  | cons x xs ih =>
    intro L₀ T₀ T hT hf
    rw [List.foldl_cons, Option.bind_some] at hf
    cases hq : mPushInner h T₀ x lazy with
    | none => rw [hq, Option.map_none, foldl_none] at hf; cases hf
    | some q =>
      rw [hq, Option.map_some] at hf
      have hstep : MemStep h (L₀, T₀) (L₀ ++ [x], q.1) := by
        cases lazy with
        | false => exact MemStep.push (i := q.2.1) (r := q.2.2) hq
        | true =>
          exact MemStep.pushLazy (i := q.2.1) (by unfold mPushLazy; rw [hq, Option.map_some])
      have := ih (L₀ ++ [x]) q.1 T (MemRun.step hT hstep) hf
      simpa using this

private lemma lazyRun_eq (h : Hash) (z : UInt256) (depth : ℕ) (L : List UInt256) :
    lazyRun h z depth L = (msetup (createTree MemPushTree.fresh depth) z).bind fun r =>
      L.foldl (fun o x => o.bind fun T => (mPushInner h T x true).map (·.1)) (some r.1) := by
  unfold lazyRun mPushLazy
  congr 1
  funext r
  congr 1
  funext o x
  congr 1
  funext T
  cases mPushInner h T x true <;> rfl

theorem lazy_run_is_run (h : Hash) (z : UInt256) (depth : ℕ) (L : List UInt256) (T : MemPushTree)
    (hT : lazyRun h z depth L = some T) : MemRun h z depth L T := by
  rw [lazyRun_eq] at hT
  cases hs : msetup (createTree MemPushTree.fresh depth) z with
  | none => rw [hs, Option.bind_none] at hT; cases hT
  | some s =>
    rw [hs, Option.bind_some] at hT
    have := foldl_run h z depth true L [] s.1 T (MemRun.setup (r := s.2) (by rw [hs])) hT
    simpa using this

theorem lazy_extend_stale_root (h : Hash) (z a b c : UInt256) :
    ((lazyRun h z 3 [a, b, c]).bind (mExtendUntilEnd h)).map MemPushTree.needsRecalc = some false
      ∧ (((lazyRun h z 3 [a, b, c]).bind (mExtendUntilEnd h)).bind (mRoot h)).map (·.2) = some 0
      ∧ (((eagerRun h z 3 [a, b, c]).bind (mExtendUntilEnd h)).bind (mRoot h)).map (·.2)
          = some (h (h a b) (h c z))
      ∧ ((lazyRun h z 3 [a, b, c]).bind (mRoot h)).map (·.2) = some (h (h a b) (h c z)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [lazyRun, eagerRun, mPush, mPushLazy, mPushInner, mPushFinish, mGrow, mPushLoop, mset,
      msetup, createTree, MemPushTree.fresh, mExtendUntilEnd, mExtendLoop, mRoot, recalculateRoot,
      mRecalcLoop]

theorem lazy_extend_stale_root_is_wrong : ∃ (h : Hash) (z a b c : UInt256),
    (((lazyRun h z 3 [a, b, c]).bind (mExtendUntilEnd h)).bind (mRoot h)).map (·.2)
      ≠ some (rootOf h z [a, b, c] 2)
    ∧ (((eagerRun h z 3 [a, b, c]).bind (mExtendUntilEnd h)).bind (mRoot h)).map (·.2)
      = some (rootOf h z [a, b, c] 2) := by
  have hfold : ∀ (h : Hash) (z a b c : UInt256), rootOf h z [a, b, c] 2 = h (h a b) (h c z) := by
    intro h z a b c; simp [rootOf, levels, levelUp, zeros]
  refine ⟨fun _ _ => 1, 0, 0, 0, 0, ?_, ?_⟩
  · obtain ⟨_, hstale, _, _⟩ := lazy_extend_stale_root (fun _ _ => 1) 0 0 0 0
    rw [hstale, hfold]
    decide
  · obtain ⟨_, _, heager, _⟩ := lazy_extend_stale_root (fun _ _ => 1) 0 0 0 0
    rw [heager, hfold]

theorem lazy_run_witness (h : Hash) (z a b c : UInt256) : ∃ T : MemPushTree,
    lazyRun h z 3 [a, b, c] = some T ∧ MemRun h z 3 [a, b, c] T ∧ T.needsRecalc = true := by
  have hrun : lazyRun h z 3 [a, b, c]
      = some ⟨3, [c, h a b, 0], [z, h z z, h (h z z) (h z z)], 3, 3, true, c⟩ := by
    simp [lazyRun, mPushLazy, mPushInner, mPushFinish, mGrow, mPushLoop, mset, msetup, createTree,
      MemPushTree.fresh]
  exact ⟨_, hrun, lazy_run_is_run h z 3 _ _ hrun, rfl⟩

end Contracts.DynamicIncrementalMerkle

/-! ## Certificates -/

namespace Contracts.DynamicIncrementalMerkle

theorem LazyExtendStaleRoot : Properties.LazyExtendStaleRoot := lazy_extend_stale_root
theorem LazyExtendStaleRootIsWrong : Properties.LazyExtendStaleRootIsWrong :=
  lazy_extend_stale_root_is_wrong
theorem MemSetupRepresentsEmpty : Properties.MemSetupRepresentsEmpty := mem_setup_represents_empty
theorem MemPushComputesRoot : Properties.MemPushComputesRoot := mPushInner_spec
theorem MemRootIsFold : Properties.MemRootIsFold := mRoot_spec
theorem LazyRootRecalculated : Properties.LazyRootRecalculated := lazy_root_recalculated
theorem LazyFlagMeansNotFull : Properties.LazyFlagMeansNotFull := lazy_flag_means_not_full
theorem MemoryMatchesStorage : Properties.MemoryMatchesStorage := memory_matches_storage
theorem LazyRunWitness : Properties.LazyRunWitness := lazy_run_witness

end Contracts.DynamicIncrementalMerkle
