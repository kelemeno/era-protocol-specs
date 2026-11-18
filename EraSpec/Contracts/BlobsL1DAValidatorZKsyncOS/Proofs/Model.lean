import EraSpec.Contracts.BlobsL1DAValidatorZKsyncOS.Properties.Model
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashEncoding
import Mathlib.Tactic

/-!
# Proofs: `BlobsL1DAValidatorZKsyncOS`

Proofs of `../Properties/Model.lean`. The loop of `checkDA` is characterised once
(`checkLoop_eq_some_iff`); the acceptance, freshness and binding results read off that
characterisation. Freshness rests on the run invariant `RunInv`: every recorded block is at most
the current block, every nonzero record was written by a logged call at that block, and every logged
write is at most the hash's record.
-/

namespace Contracts.ZKsyncOSBlobsDA

open AttackVectors.BundleHashEncoding

/-! ## Words -/

theorem toB32_length (x : UInt256) : (toB32 x).length = 32 := length_toBytesBE 32 x.val

theorem toUInt256_val (x : UInt256) : Nat.toUInt256 x.val = x := by
  apply Fin.ext
  show x.val % UInt256.size = x.val
  exact Nat.mod_eq_of_lt x.isLt

theorem fromBytesBE_toB32 (x : UInt256) : fromBytesBE (toB32 x) = x.val :=
  fromBytesBE_toBytesBE (k := 32) (n := x.val) (by
    have h : (256 : ℕ) ^ 32 = UInt256.size := by rfl
    rw [h]; exact x.isLt)

theorem toB32_injective {x y : UInt256} (h : toB32 x = toB32 y) : x = y := by
  have := congrArg fromBytesBE h
  rw [fromBytesBE_toB32, fromBytesBE_toB32] at this
  exact Fin.ext this

/-- Reading a word written at the start. -/
theorem b32At_zero_toB32_append (x : UInt256) (tail : Bytes) : b32At (toB32 x ++ tail) 0 = x := by
  unfold b32At
  rw [List.drop_zero, List.take_left' (toB32_length x), fromBytesBE_toB32, toUInt256_val]

theorem b32At_zero_toB32 (x : UInt256) : b32At (toB32 x) 0 = x := by
  have := b32At_zero_toB32_append x []
  rwa [List.append_nil] at this

theorem b32At_append_right (pre b : Bytes) (off : ℕ) :
    b32At (pre ++ b) (pre.length + off) = b32At b off := by
  unfold b32At
  rw [← List.drop_drop, List.drop_left]

theorem encWords_cons (x : UInt256) (xs : List UInt256) :
    encWords (x :: xs) = toB32 x ++ encWords xs := by
  unfold encWords
  rw [List.map_cons, List.flatten_cons]

theorem encWords_nil : encWords [] = [] := rfl

theorem encWords_length (vs : List UInt256) : (encWords vs).length = 32 * vs.length := by
  induction vs with
  | nil => rfl
  | cons x xs ih =>
    rw [encWords_cons, List.length_append, toB32_length, ih, List.length_cons]
    ring

theorem encWords_injective : ∀ a b : List UInt256, encWords a = encWords b → a = b
  | [], [], _ => rfl
  | [], y :: ys, h => by
    have := congrArg List.length h
    rw [encWords_nil, encWords_length] at this
    simp at this
  | x :: xs, [], h => by
    have := congrArg List.length h
    rw [encWords_nil, encWords_length] at this
    simp at this
  | x :: xs, y :: ys, h => by
    rw [encWords_cons, encWords_cons] at h
    have h1 : toB32 x = toB32 y := by
      have := congrArg (List.take 32) h
      rwa [List.take_left' (toB32_length x), List.take_left' (toB32_length y)] at this
    have h2 : encWords xs = encWords ys := by
      have := congrArg (List.drop 32) h
      rwa [List.drop_left' (toB32_length x), List.drop_left' (toB32_length y)] at this
    rw [toB32_injective h1, encWords_injective xs ys h2]

/-! ## Writes -/

theorem publishLoop_apply (b : ℕ) :
    ∀ (vs : List UInt256) (m : UInt256 → ℕ) (v : UInt256),
      publishLoop b vs m v
        = if v ∈ vs.takeWhile (fun x => decide (x ≠ 0)) then b else m v
  | [], m, v => by simp [publishLoop]
  | x :: xs, m, v => by
    by_cases hx : x = 0
    · simp [publishLoop, hx]
    · have ih := publishLoop_apply b xs (Function.update m x b) v
      simp only [publishLoop, hx, ↓reduceIte] at ih ⊢
      rw [ih, List.takeWhile_cons_of_pos (by simpa using hx)]
      by_cases h1 : v ∈ xs.takeWhile (fun x => decide (x ≠ 0))
      · rw [ite_eq_left h1, ite_eq_left (List.mem_cons_of_mem _ h1)]
      · by_cases h2 : v = x
        · subst h2
          rw [ite_eq_right h1, ite_eq_left List.mem_cons_self, Function.update_self]
        · rw [ite_eq_right h1, ite_eq_right (fun h => (List.mem_cons.mp h).elim h2 h1),
            Function.update_of_ne h2]

theorem BlobsPublishWritesExactlyAttached : Properties.BlobsPublishWritesExactlyAttached := by
  intro env S v
  exact ⟨publishLoop_apply S.block env.blobs S.published v, rfl⟩

theorem takeWhile_of_all {l : List UInt256} (h : ∀ v ∈ l, v ≠ 0) :
    l.takeWhile (fun x => decide (x ≠ 0)) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.takeWhile_cons_of_pos (by simpa using h x (by simp))]
    rw [ih (fun v hv => h v (List.mem_cons_of_mem _ hv))]

theorem BlobsAttachedIsAllBlobs : Properties.BlobsAttachedIsAllBlobs := by
  intro env hwf
  exact takeWhile_of_all hwf

/-! ## The loop -/

theorem isBlobAvailable_eq_some_true_iff (S : VState) (v : UInt256) :
    isBlobAvailable S v = some true ↔ Available S v := by
  unfold isBlobAvailable isBlobAvailableWith Available
  by_cases h0 : S.published v = 0
  · simp [h0]
  · by_cases hlt : S.block < S.published v
    · simp [h0, hlt]
    · simp [h0, hlt]
      omega

theorem zeroCount_cons_zero (ws : List UInt256) : zeroCount (0 :: ws) = zeroCount ws + 1 := by
  unfold zeroCount
  simp

theorem zeroCount_cons_ne {w : UInt256} (hw : w ≠ 0) (ws : List UInt256) :
    zeroCount (w :: ws) = zeroCount ws := by
  unfold zeroCount
  simp [hw]

theorem resolveWords_cons_zero (bh : ℕ → UInt256) (j : ℕ) (ws : List UInt256) :
    resolveWords bh j (0 :: ws) = bh j :: resolveWords bh (j + 1) ws := by
  simp [resolveWords]

theorem resolveWords_cons_ne (bh : ℕ → UInt256) (j : ℕ) {w : UInt256} (hw : w ≠ 0)
    (ws : List UInt256) : resolveWords bh j (w :: ws) = w :: resolveWords bh j ws := by
  simp [resolveWords, hw]

/-- **THE LOOP, CHARACTERISED.** From index `j`, the loop over `ws` succeeds with `r` iff every
nonzero entry is available, the blob hashes `j … j + z - 1` are nonzero, and `r` is the resolved
list with final index `j + z`. -/
theorem checkLoop_eq_some_iff (env : TxEnv) (S : VState) :
    ∀ (ws : List UInt256) (j : ℕ) (r : List UInt256 × ℕ),
      checkLoopWith {} env S ws j = some r ↔
        (∀ w ∈ ws, w ≠ 0 → Available S w)
          ∧ (∀ i < zeroCount ws, env.blobhash (j + i) ≠ 0)
          ∧ r = (resolveWords env.blobhash j ws, j + zeroCount ws)
  | [], j, r => by
    simp only [checkLoopWith, Option.some.injEq, List.not_mem_nil, false_implies, implies_true,
      zeroCount, List.count_nil, Nat.not_lt_zero, resolveWords, Nat.add_zero, true_and]
    exact eq_comm
  | w :: ws, j, r => by
    by_cases hw : w = 0
    · subst hw
      have ih := checkLoop_eq_some_iff env S ws (j + 1)
      rw [zeroCount_cons_zero, resolveWords_cons_zero]
      simp only [checkLoopWith, ne_eq, not_true_eq_false, ite_false]
      by_cases hb : env.blobhash j = 0
      · simp only [hb, ite_true]
        constructor
        · intro h; cases h
        · rintro ⟨_, h2, _⟩
          exact absurd (by simpa using hb) (h2 0 (by omega))
      · simp only [hb, ite_false]
        constructor
        · intro h
          obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨h1, h2, h3⟩ := (ih r').mp hr'
          refine ⟨?_, ?_, ?_⟩
          · intro x hx hx0
            rcases List.mem_cons.mp hx with rfl | hx
            · exact absurd rfl hx0
            · exact h1 x hx hx0
          · intro i hi
            rcases i with _ | i
            · simpa using hb
            · have := h2 i (by omega)
              rwa [show j + 1 + i = j + (i + 1) by omega] at this
          · rw [h3]
            simp only [Prod.mk.injEq, true_and]
            omega
        · rintro ⟨h1, h2, rfl⟩
          have hr := (ih (resolveWords env.blobhash (j + 1) ws, j + 1 + zeroCount ws)).mpr
            ⟨fun x hx hx0 => h1 x (List.mem_cons_of_mem _ hx) hx0,
             fun i hi => by
               have := h2 (i + 1) (by omega)
               rwa [show j + (i + 1) = j + 1 + i by omega] at this,
             rfl⟩
          rw [hr, Option.map_some, show j + 1 + zeroCount ws = j + (zeroCount ws + 1) by omega]
    · have ih := checkLoop_eq_some_iff env S ws j
      rw [zeroCount_cons_ne hw, resolveWords_cons_ne _ _ hw]
      simp only [checkLoopWith, ne_eq, hw, not_false_eq_true, ite_true]
      by_cases ha : isBlobAvailable S w = some true
      · have ha' : isBlobAvailableWith {} S w = some true := ha
        simp only [ha', ite_true]
        constructor
        · intro h
          obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨h1, h2, h3⟩ := (ih r').mp hr'
          refine ⟨?_, h2, ?_⟩
          · intro x hx hx0
            rcases List.mem_cons.mp hx with rfl | hx
            · exact (isBlobAvailable_eq_some_true_iff S x).mp ha
            · exact h1 x hx hx0
          · rw [h3]
        · rintro ⟨h1, h2, rfl⟩
          have hr := (ih (resolveWords env.blobhash j ws, j + zeroCount ws)).mpr
            ⟨fun x hx hx0 => h1 x (List.mem_cons_of_mem _ hx) hx0, h2, rfl⟩
          rw [hr]
          rfl
      · have ha' : ¬ isBlobAvailableWith {} S w = some true := ha
        simp only [ha', ite_false]
        constructor
        · intro h; cases h
        · rintro ⟨h1, _, _⟩
          exact absurd ((isBlobAvailable_eq_some_true_iff S w).mpr (h1 w (by simp) hw)) ha

/-! ## Exact acceptance -/

/-- `checkDA` on an input with a whole number of entries, once the loop has succeeded. -/
theorem checkDA_of_loop {K : Bytes → UInt256} {env : TxEnv} {S : VState} {h : UInt256}
    {input : Bytes} (hlen : input.length % 32 = 0) {vs : List UInt256} {j : ℕ}
    (hl : checkLoopWith {} env S (inputWords input) 0 = some (vs, j)) :
    checkDA K env S h input
      = if env.blobhash j ≠ 0 then none
        else if K (encWords vs) ≠ h then none else some DAOutput.empty := by
  show checkDAWith {} K env S h input = _
  unfold checkDAWith
  have hlen' : ¬ input.length % BLOB_VERSIONED_HASH_SIZE ≠ 0 := by
    show ¬ input.length % 32 ≠ 0
    omega
  rw [ite_eq_right hlen', hl]
  simp only [true_and]

theorem checkDA_of_loop_none {K : Bytes → UInt256} {env : TxEnv} {S : VState} {h : UInt256}
    {input : Bytes} (hl : checkLoopWith {} env S (inputWords input) 0 = none) :
    checkDA K env S h input = none := by
  show checkDAWith {} K env S h input = _
  unfold checkDAWith
  by_cases hlen : input.length % BLOB_VERSIONED_HASH_SIZE ≠ 0
  · rw [ite_eq_left hlen]
  · rw [ite_eq_right hlen, hl]

theorem checkDA_of_len {K : Bytes → UInt256} {env : TxEnv} {S : VState} {h : UInt256}
    {input : Bytes} (hlen : input.length % 32 ≠ 0) : checkDA K env S h input = none := by
  show checkDAWith {} K env S h input = _
  unfold checkDAWith
  rw [ite_eq_left (show input.length % BLOB_VERSIONED_HASH_SIZE ≠ 0 from hlen)]

theorem BlobsCheckDAAcceptsIff : Properties.BlobsCheckDAAcceptsIff := by
  intro K env S h input out
  by_cases hlen : input.length % 32 ≠ 0
  · rw [checkDA_of_len hlen]
    constructor
    · intro h; cases h
    · rintro ⟨h1, _⟩; exact absurd h1 hlen
  · have hlen' : input.length % 32 = 0 := by omega
    have key := checkLoop_eq_some_iff env S (inputWords input) 0
    cases hl : checkLoopWith {} env S (inputWords input) 0 with
    | none =>
      rw [checkDA_of_loop_none hl]
      constructor
      · intro h; cases h
      · rintro ⟨_, h1, h2, _⟩
        have := (key (resolveWords env.blobhash 0 (inputWords input),
          0 + zeroCount (inputWords input))).mpr ⟨h1, by simpa using h2, rfl⟩
        rw [hl] at this
        cases this
    | some r =>
      obtain ⟨h1, h2, hr⟩ := (key r).mp hl
      subst hr
      rw [checkDA_of_loop hlen' hl]
      simp only [zero_add] at h2 ⊢
      unfold resolvedHashes
      by_cases he : env.blobhash (zeroCount (inputWords input)) = 0
      · rw [ite_eq_right (not_not.mpr he)]
        by_cases hk : K (encWords (resolveWords env.blobhash 0 (inputWords input))) = h
        · rw [ite_eq_right (not_not.mpr hk)]
          constructor
          · intro ho
            exact ⟨hlen', h1, h2, he, hk, (Option.some.inj ho).symm⟩
          · rintro ⟨_, _, _, _, _, ho⟩
            rw [ho]
        · rw [ite_eq_left hk]
          constructor
          · intro h; cases h
          · rintro ⟨_, _, _, _, hk', _⟩
            exact absurd hk' hk
      · rw [ite_eq_left he]
        constructor
        · intro h; cases h
        · rintro ⟨_, _, _, he', _⟩
          exact absurd he' he

/-! ## The resolved list -/

theorem getD_of_lt {l : List UInt256} {i : ℕ} (h : i < l.length) (d : UInt256) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD_of_ge {l : List UInt256} {i : ℕ} (h : l.length ≤ i) (d : UInt256) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem mem_iff_getD {l : List UInt256} {w : UInt256} :
    w ∈ l ↔ ∃ i < l.length, l.getD i 0 = w := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, getD_of_lt hi 0⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, (getD_of_lt hi 0).symm⟩

theorem resolveWords_length (bh : ℕ → UInt256) :
    ∀ (j : ℕ) (ws : List UInt256), (resolveWords bh j ws).length = ws.length
  | _, [] => rfl
  | j, w :: ws => by
    by_cases hw : w = 0
    · subst hw
      rw [resolveWords_cons_zero, List.length_cons, List.length_cons, resolveWords_length]
    · rw [resolveWords_cons_ne _ _ hw, List.length_cons, List.length_cons, resolveWords_length]

theorem resolveWords_getD_ne (bh : ℕ → UInt256) :
    ∀ (j : ℕ) (ws : List UInt256) (i : ℕ), ws.getD i 0 ≠ 0 →
      (resolveWords bh j ws).getD i 0 = ws.getD i 0
  | _, [], i, h => by simp at h
  | j, w :: ws, i, h => by
    by_cases hw : w = 0
    · subst hw
      rw [resolveWords_cons_zero]
      rcases i with _ | i
      · simp at h
      · rw [List.getD_cons_succ, List.getD_cons_succ] at *
        exact resolveWords_getD_ne bh (j + 1) ws i h
    · rw [resolveWords_cons_ne _ _ hw]
      rcases i with _ | i
      · rfl
      · rw [List.getD_cons_succ, List.getD_cons_succ] at *
        exact resolveWords_getD_ne bh j ws i h

theorem resolveWords_getD_zero (bh : ℕ → UInt256) :
    ∀ (j : ℕ) (ws : List UInt256) (i : ℕ), i < ws.length → ws.getD i 0 = 0 →
      ∃ c < zeroCount ws, (resolveWords bh j ws).getD i 0 = bh (j + c)
  | _, [], i, hi, _ => by simp at hi
  | j, w :: ws, i, hi, h => by
    by_cases hw : w = 0
    · subst hw
      rw [resolveWords_cons_zero, zeroCount_cons_zero]
      rcases i with _ | i
      · exact ⟨0, by omega, by simp⟩
      · rw [List.getD_cons_succ] at h ⊢
        obtain ⟨c, hc, he⟩ := resolveWords_getD_zero bh (j + 1) ws i
          (by simpa using hi) h
        exact ⟨c + 1, by omega, by rw [he]; congr 1; omega⟩
    · rw [resolveWords_cons_ne _ _ hw, zeroCount_cons_ne hw]
      rcases i with _ | i
      · simp at h; exact absurd h hw
      · rw [List.getD_cons_succ] at h ⊢
        exact resolveWords_getD_zero bh j ws i (by simpa using hi) h

theorem atZeroEntries_resolveWords (bh : ℕ → UInt256) :
    ∀ (j : ℕ) (ws : List UInt256),
      atZeroEntries ws (resolveWords bh j ws)
        = (List.range (zeroCount ws)).map (fun c => bh (j + c))
  | _, [] => rfl
  | j, w :: ws => by
    by_cases hw : w = 0
    · subst hw
      rw [resolveWords_cons_zero, zeroCount_cons_zero, List.range_succ_eq_map]
      simp only [atZeroEntries, ↓reduceIte, List.map_cons, List.map_map, Nat.add_zero]
      rw [atZeroEntries_resolveWords bh (j + 1) ws]
      congr 1
      apply List.map_congr_left
      intro c _
      simp only [Function.comp_apply, Nat.succ_eq_add_one]
      congr 1
      omega
    · rw [resolveWords_cons_ne _ _ hw, zeroCount_cons_ne hw]
      simp only [atZeroEntries, hw, ↓reduceIte]
      exact atZeroEntries_resolveWords bh j ws

theorem atZeroEntries_length :
    ∀ (ws vs : List UInt256), vs.length = ws.length → (atZeroEntries ws vs).length = zeroCount ws
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | w :: ws, v :: vs, h => by
    by_cases hw : w = 0
    · subst hw
      simp only [atZeroEntries, ↓reduceIte, List.length_cons, zeroCount_cons_zero]
      rw [atZeroEntries_length ws vs (by simpa using h)]
    · simp only [atZeroEntries, hw, ↓reduceIte, zeroCount_cons_ne hw]
      exact atZeroEntries_length ws vs (by simpa using h)

/-- **THE RESOLVED LIST IS UNIQUE**: a list that keeps every nonzero entry and holds `bh j, bh (j + 1),
…` at the zero entries is `resolveWords bh j ws`. -/
theorem eq_resolveWords_of (bh : ℕ → UInt256) :
    ∀ (j : ℕ) (ws vs : List UInt256), vs.length = ws.length →
      (∀ i < vs.length, ws.getD i 0 ≠ 0 → vs.getD i 0 = ws.getD i 0) →
      atZeroEntries ws vs = (List.range (zeroCount ws)).map (fun c => bh (j + c)) →
      vs = resolveWords bh j ws
  | _, [], vs, hl, _, _ => by
    have : vs = [] := by simpa using hl
    rw [this]; rfl
  | _, _ :: _, [], hl, _, _ => by simp at hl
  | j, w :: ws, v :: vs, hl, hne, hz => by
    by_cases hw : w = 0
    · subst hw
      rw [resolveWords_cons_zero]
      rw [zeroCount_cons_zero, List.range_succ_eq_map] at hz
      simp only [atZeroEntries, ↓reduceIte, List.map_cons, List.map_map, Nat.add_zero,
        List.cons.injEq] at hz
      obtain ⟨hv, hz⟩ := hz
      rw [hv, eq_resolveWords_of bh (j + 1) ws vs (by simpa using hl)
        (fun i hi h => by simpa using hne (i + 1) (by simp; omega) (by simpa using h))
        (by
          rw [hz]
          apply List.map_congr_left
          intro c _
          simp only [Function.comp_apply, Nat.succ_eq_add_one]
          congr 1
          omega)]
    · rw [resolveWords_cons_ne _ _ hw]
      have hv : v = w := by simpa using hne 0 (by simp) (by simpa using hw)
      rw [zeroCount_cons_ne hw] at hz
      simp only [atZeroEntries, hw, ↓reduceIte] at hz
      rw [hv, eq_resolveWords_of bh j ws vs (by simpa using hl)
        (fun i hi h => by simpa using hne (i + 1) (by simp; omega) (by simpa using h)) hz]

theorem blobhash_ne_zero_iff {env : TxEnv} (hwf : env.WellFormed) (i : ℕ) :
    env.blobhash i ≠ 0 ↔ i < env.blobs.length := by
  unfold TxEnv.blobhash
  constructor
  · intro h
    by_contra hge
    exact h (getD_of_ge (by omega) 0)
  · intro hi
    rw [getD_of_lt hi 0]
    exact hwf _ (List.getElem_mem hi)

theorem map_range_blobhash (env : TxEnv) :
    (List.range env.blobs.length).map (fun c => env.blobhash (0 + c)) = env.blobs := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Nat.zero_add]
    unfold TxEnv.blobhash
    rw [getD_of_lt h2 0]

/-- Under `WellFormed`, the blob-hash conditions of `BlobsCheckDAAcceptsIff` say that the number
of zero entries is the number of blobs. -/
theorem zeroCount_eq_of_wellFormed {env : TxEnv} (hwf : env.WellFormed) (z : ℕ) :
    ((∀ j < z, env.blobhash j ≠ 0) ∧ env.blobhash z = 0) ↔ z = env.blobs.length := by
  constructor
  · rintro ⟨h1, h2⟩
    have hz : ¬ z < env.blobs.length := fun hlt => (blobhash_ne_zero_iff hwf z).mpr hlt h2
    by_contra hne
    have hlt : env.blobs.length < z := by omega
    exact absurd ((blobhash_ne_zero_iff hwf _).mp (h1 _ hlt)) (lt_irrefl _)
  · rintro rfl
    refine ⟨fun j hj => (blobhash_ne_zero_iff hwf j).mpr hj, ?_⟩
    unfold TxEnv.blobhash
    exact getD_of_ge (le_refl _) 0

theorem BlobsCheckDAAcceptsIffWellFormed : Properties.BlobsCheckDAAcceptsIffWellFormed := by
  intro K env S h input out hwf
  rw [BlobsCheckDAAcceptsIff]
  set ws := inputWords input with hws
  constructor
  · rintro ⟨hlen, havail, hb, hz, hk, ho⟩
    have hzm := (zeroCount_eq_of_wellFormed hwf _).mp ⟨hb, hz⟩
    refine ⟨hlen, resolveWords env.blobhash 0 ws, resolveWords_length _ _ _, ?_, ?_, hk, ho⟩
    · intro i hi hne
      refine ⟨resolveWords_getD_ne _ _ _ _ hne, havail _ ?_ hne⟩
      rw [resolveWords_length] at hi
      exact mem_iff_getD.mpr ⟨i, hi, rfl⟩
    · rw [atZeroEntries_resolveWords, hzm, map_range_blobhash]
  · rintro ⟨hlen, vs, hl, hne, hzero, hk, ho⟩
    have hzm : zeroCount ws = env.blobs.length := by
      rw [← atZeroEntries_length ws vs hl, hzero]
    have hvs : vs = resolveWords env.blobhash 0 ws := by
      apply eq_resolveWords_of env.blobhash 0 ws vs hl (fun i hi h => (hne i hi h).1)
      rw [hzero, hzm, map_range_blobhash]
    obtain ⟨hb, hz⟩ := (zeroCount_eq_of_wellFormed hwf _).mpr hzm
    refine ⟨hlen, ?_, hb, hz, ?_, ho⟩
    · intro w hw hw0
      obtain ⟨i, hi, rfl⟩ := mem_iff_getD.mp hw
      exact (hne i (by rw [hl]; exact hi) hw0).2
    · unfold resolvedHashes
      rw [← hvs]
      exact hk

theorem BlobsAcceptedUsesEveryAttachedBlob : Properties.BlobsAcceptedUsesEveryAttachedBlob := by
  intro K env S h input out hwf hacc
  obtain ⟨_, _, hb, hz, _, _⟩ := (BlobsCheckDAAcceptsIff K env S h input out).mp hacc
  have hzm := (zeroCount_eq_of_wellFormed hwf _).mp ⟨hb, hz⟩
  refine ⟨hzm, ?_⟩
  unfold resolvedHashes
  rw [atZeroEntries_resolveWords, hzm, map_range_blobhash]

/-! ## Runs -/

/-- **THE RUN INVARIANT.** Every recorded block and every logged block is at most the current
block; a nonzero record was written by a logged call at exactly that block; every logged write of
a hash is at most its record. -/
structure RunInv (W : World) : Prop where
  pub_le : ∀ v, W.st.published v ≤ W.st.block
  log_le : ∀ e ∈ W.log, e.1 ≤ W.st.block
  pub_logged : ∀ v, W.st.published v ≠ 0 → ∃ e ∈ W.log, v ∈ e.2 ∧ e.1 = W.st.published v
  logged_le_pub : ∀ e ∈ W.log, ∀ v ∈ e.2, e.1 ≤ W.st.published v

theorem publishBlobs_published (env : TxEnv) (S : VState) (v : UInt256) :
    (publishBlobs env S).published v = if v ∈ attached env then S.block else S.published v :=
  publishLoop_apply S.block env.blobs S.published v

theorem runInv_fresh (b : ℕ) : RunInv (World.fresh b) where
  pub_le _ := Nat.zero_le _
  log_le _ he := by simp [World.fresh] at he
  pub_logged _ h := absurd rfl h
  logged_le_pub _ he := by simp [World.fresh] at he

theorem runInv_step {W W' : World} (hs : WStep W W') (hi : RunInv W) : RunInv W' := by
  cases hs with
  | publish env =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v
      show (publishBlobs env W.st).published v ≤ W.st.block
      rw [publishBlobs_published]
      split_ifs
      · exact le_refl _
      · exact hi.pub_le v
    · intro e he
      show e.1 ≤ W.st.block
      rcases List.mem_append.mp he with he | he
      · exact hi.log_le e he
      · rw [List.mem_singleton.mp he]
    · intro v hv
      change (publishBlobs env W.st).published v ≠ 0 at hv
      show ∃ e ∈ W.log ++ [(W.st.block, attached env)], v ∈ e.2
        ∧ e.1 = (publishBlobs env W.st).published v
      rw [publishBlobs_published] at hv ⊢
      by_cases hm : v ∈ attached env
      · rw [ite_eq_left hm]
        exact ⟨(W.st.block, attached env), by simp, hm, rfl⟩
      · rw [ite_eq_right hm] at hv ⊢
        obtain ⟨e, he, hve, hb⟩ := hi.pub_logged v hv
        exact ⟨e, List.mem_append_left _ he, hve, hb⟩
    · intro e he v hv
      show e.1 ≤ (publishBlobs env W.st).published v
      rw [publishBlobs_published]
      rcases List.mem_append.mp he with he | he
      · by_cases hm : v ∈ attached env
        · rw [ite_eq_left hm]; exact hi.log_le e he
        · rw [ite_eq_right hm]; exact hi.logged_le_pub e he v hv
      · rw [List.mem_singleton.mp he] at hv ⊢
        rw [ite_eq_left hv]
  | advance b hb =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v; exact le_trans (hi.pub_le v) hb
    · intro e he; exact le_trans (hi.log_le e he) hb
    · exact hi.pub_logged
    · exact hi.logged_le_pub

theorem runInv_of_reachable {W : World} (h : W.Reachable) : RunInv W := by
  obtain ⟨b, hr⟩ := h
  induction hr with
  | refl => exact runInv_fresh b
  | tail _ hs ih => exact runInv_step hs ih

theorem BlobsAvailabilityNeverPanics : Properties.BlobsAvailabilityNeverPanics := by
  intro W v hr
  have hi := runInv_of_reachable hr
  unfold isBlobAvailable isBlobAvailableWith
  by_cases h0 : W.st.published v = 0
  · rw [ite_eq_left h0]; exact Option.some_ne_none _
  · rw [ite_eq_right h0]
    have hlt : ¬ W.st.block < W.st.published v := not_lt.mpr (hi.pub_le v)
    simp only [Bool.true_eq_false, ↓reduceIte, hlt]
    exact Option.some_ne_none _

theorem BlobsAvailableIffLoggedInWindow : Properties.BlobsAvailableIffLoggedInWindow := by
  intro W v hr
  have hi := runInv_of_reachable hr
  unfold Available LoggedInWindow
  constructor
  · rintro ⟨h0, hle, hw⟩
    obtain ⟨e, he, hve, hb⟩ := hi.pub_logged v (by omega)
    exact ⟨e, he, hve, by omega, by omega, by omega⟩
  · rintro ⟨e, he, hve, h0, hle, hw⟩
    have h1 := hi.logged_le_pub e he v hve
    have h2 := hi.pub_le v
    exact ⟨by omega, h2, by omega⟩

theorem BlobsAcceptedHashesFresh : Properties.BlobsAcceptedHashesFresh := by
  intro K env W h input out hr hacc i hi
  obtain ⟨_, havail, hb, _, _, _⟩ := (BlobsCheckDAAcceptsIff K env W.st h input out).mp hacc
  refine ⟨fun hne => ⟨resolveWords_getD_ne _ _ _ _ hne, ?_⟩, fun hz => ?_⟩
  · exact (BlobsAvailableIffLoggedInWindow W _ hr).mp
      (havail _ (mem_iff_getD.mpr ⟨i, hi, rfl⟩) hne)
  · obtain ⟨c, hc, he⟩ := resolveWords_getD_zero env.blobhash 0 (inputWords input) i hi hz
    unfold resolvedHashes
    rw [he, Nat.zero_add]
    have hne := hb c hc
    refine ⟨?_, hne⟩
    unfold TxEnv.blobhash at hne ⊢
    have hlt : c < env.blobs.length := by
      by_contra hge
      exact hne (getD_of_ge (by omega) 0)
    rw [getD_of_lt hlt 0]
    exact List.getElem_mem hlt

/-! ## Pinned binding -/

theorem BlobsEncWordsInjective : Properties.BlobsEncWordsInjective := encWords_injective

theorem BlobsAcceptedBindsOrCollision : Properties.BlobsAcceptedBindsOrCollision := by
  intro K env S input vs out hacc
  obtain ⟨_, _, _, _, hk, _⟩ := (BlobsCheckDAAcceptsIff K env S _ input out).mp hacc
  by_cases he : resolvedHashes env input = vs
  · exact Or.inl he
  · exact Or.inr ⟨fun h => he (encWords_injective _ _ h), hk⟩

theorem BlobsTwoAcceptancesAgreeOrCollision : Properties.BlobsTwoAcceptancesAgreeOrCollision := by
  intro K env₁ env₂ S₁ S₂ h input₁ input₂ out₁ out₂ h₁ h₂
  obtain ⟨_, _, _, _, hk₁, _⟩ := (BlobsCheckDAAcceptsIff K env₁ S₁ h input₁ out₁).mp h₁
  obtain ⟨_, _, _, _, hk₂, _⟩ := (BlobsCheckDAAcceptsIff K env₂ S₂ h input₂ out₂).mp h₂
  by_cases he : resolvedHashes env₁ input₁ = resolvedHashes env₂ input₂
  · exact Or.inl he
  · exact Or.inr ⟨fun h => he (encWords_injective _ _ h), hk₁.trans hk₂.symm⟩

/-! ## Concrete inputs and worlds -/

theorem inputWords_one (a : UInt256) : inputWords (toB32 a) = [a] := by
  unfold inputWords
  rw [toB32_length]
  show (List.range 1).map (fun i => b32At (toB32 a) (32 * i)) = [a]
  rw [show List.range 1 = [0] from rfl, List.map_cons, List.map_nil, Nat.mul_zero,
    b32At_zero_toB32]

theorem inputWords_two (a b : UInt256) : inputWords (toB32 a ++ toB32 b) = [a, b] := by
  unfold inputWords
  rw [List.length_append, toB32_length, toB32_length]
  show (List.range 2).map (fun i => b32At (toB32 a ++ toB32 b) (32 * i)) = [a, b]
  have h1 : b32At (toB32 a ++ toB32 b) (32 * 1) = b := by
    have := b32At_append_right (toB32 a) (toB32 b) 0
    rw [toB32_length, Nat.add_zero, b32At_zero_toB32] at this
    exact this
  rw [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_cons, List.map_nil,
    Nat.mul_zero, b32At_zero_toB32_append, h1]

/-- Deploy at block 1, publish the hashes `pubs` there, move to block `b`. -/
def demoWorld (pubs : List UInt256) (b : ℕ) : World :=
  ⟨{ publishBlobs ⟨pubs⟩ (World.fresh 1).st with block := b }, [(1, attached ⟨pubs⟩)]⟩

theorem demoWorld_reachable (pubs : List UInt256) {b : ℕ} (hb : 1 ≤ b) :
    (demoWorld pubs b).Reachable :=
  ⟨1, Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single (WStep.publish (World.fresh 1) ⟨pubs⟩))
    (WStep.advance _ b hb)⟩

theorem demoWorld_published (pubs : List UInt256) (b : ℕ) (v : UInt256) :
    (demoWorld pubs b).st.published v = if v ∈ attached ⟨pubs⟩ then 1 else 0 :=
  publishBlobs_published ⟨pubs⟩ (World.fresh 1).st v

theorem demoWorld_available {pubs : List UInt256} {b : ℕ} {v : UInt256}
    (hv : v ∈ attached ⟨pubs⟩) (hb : 1 ≤ b) (hw : b - 1 ≤ BLOB_EXPIRATION_BLOCKS) :
    Available (demoWorld pubs b).st v := by
  unfold Available
  rw [demoWorld_published, ite_eq_left hv]
  exact ⟨Nat.one_pos, hb, hw⟩

/-! ## Countermodels -/

theorem BlobsExtraBlobCheckLoadBearing : Properties.BlobsExtraBlobCheckLoadBearing := by
  intro K S
  have hl : checkLoopWith {} ⟨[1]⟩ S (inputWords []) 0 = some ([], 0) := rfl
  refine ⟨fun v hv => by rw [List.mem_singleton.mp hv]; decide, ?_, by decide, ?_⟩
  · show checkDAWith _ K _ S _ [] = _
    unfold checkDAWith
    simp [inputWords, checkLoopWith, BLOB_VERSIONED_HASH_SIZE]
  · rw [checkDA_of_loop (by decide) hl]
    rw [ite_eq_left (by decide)]

theorem BlobsWindowCheckLoadBearing : Properties.BlobsWindowCheckLoadBearing := by
  intro K
  have hatt : attached ⟨[1]⟩ = [1] := by decide
  have hpub : (demoWorld [1] (2 + BLOB_EXPIRATION_BLOCKS)).st.published 1 = 1 := by
    rw [demoWorld_published, hatt, ite_eq_left (by simp)]
  refine ⟨demoWorld [1] (2 + BLOB_EXPIRATION_BLOCKS), demoWorld_reachable _ (by omega),
    by rw [demoWorld, hatt], rfl, ?_, ?_, ?_⟩
  · show checkDAWith { window := false } K ⟨[]⟩ _ _ (toB32 1) = _
    unfold checkDAWith
    rw [toB32_length, inputWords_one]
    have hav : isBlobAvailableWith { window := false } (demoWorld [1] (2 + BLOB_EXPIRATION_BLOCKS)).st 1
        = some true := by
      unfold isBlobAvailableWith
      rw [hpub]
      rfl
    simp [checkLoopWith, hav, TxEnv.blobhash, BLOB_VERSIONED_HASH_SIZE]
  · rintro ⟨e, he, hve, _, _, hw⟩
    have : e = (1, [1]) := by
      have := he
      simp only [demoWorld, hatt, List.mem_singleton] at this
      exact this
    subst this
    change 2 + BLOB_EXPIRATION_BLOCKS - 1 ≤ BLOB_EXPIRATION_BLOCKS at hw
    omega
  · apply checkDA_of_loop_none
    rw [inputWords_one]
    have hav : isBlobAvailableWith {} (demoWorld [1] (2 + BLOB_EXPIRATION_BLOCKS)).st 1
        = some false := by
      have hblk : (demoWorld [1] (2 + BLOB_EXPIRATION_BLOCKS)).st.block
          = 2 + BLOB_EXPIRATION_BLOCKS := rfl
      unfold isBlobAvailableWith
      rw [hpub, hblk]
      simp [BLOB_EXPIRATION_BLOCKS]
    simp [checkLoopWith, hav]

/-! ## Witnesses -/

theorem blobs_demo_accept (K : Bytes → UInt256) (pubs : List UInt256)
    (h7 : (7 : UInt256) ∈ attached ⟨pubs⟩) :
    checkDA K ⟨[9]⟩ (demoWorld pubs 10).st (K (encWords [7, 9])) (toB32 7 ++ toB32 0)
      = some DAOutput.empty := by
  rw [BlobsCheckDAAcceptsIff]
  have hres : resolvedHashes ⟨[9]⟩ (toB32 7 ++ toB32 0) = [7, 9] := by
    unfold resolvedHashes; rw [inputWords_two]; decide
  refine ⟨by simp [toB32_length], ?_, ?_, ?_, by rw [hres], rfl⟩
  · rw [inputWords_two]
    intro w hw hw0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact demoWorld_available h7 (by omega) (by simp [BLOB_EXPIRATION_BLOCKS])
    · exact absurd rfl hw0
  · rw [inputWords_two]; decide
  · rw [inputWords_two]; decide

theorem BlobsAcceptanceWitness : Properties.BlobsAcceptanceWitness := by
  intro K
  have hatt : attached ⟨[7]⟩ = [7] := by decide
  refine ⟨demoWorld [7] 10, demoWorld_reachable _ (by omega), by rw [demoWorld, hatt], rfl,
    fun v hv => by rw [List.mem_singleton.mp hv]; decide, by decide, inputWords_two 7 0, ?_,
    blobs_demo_accept K [7] (by rw [hatt]; simp),
    demoWorld_available (by rw [hatt]; simp) (by omega) (by simp [BLOB_EXPIRATION_BLOCKS]), ?_⟩
  · unfold resolvedHashes; rw [inputWords_two]; decide
  · refine ⟨(1, [7]), by rw [demoWorld, hatt]; simp, by simp, Nat.one_pos, by
      show 1 ≤ 10; omega, by show 10 - 1 ≤ BLOB_EXPIRATION_BLOCKS; simp [BLOB_EXPIRATION_BLOCKS]⟩

theorem BlobsBindingWitness : Properties.BlobsBindingWitness := by
  have hatt : attached ⟨[7]⟩ = [7] := by decide
  have h7 : (7 : UInt256) ∈ attached ⟨[7]⟩ := by rw [hatt]; simp
  have hres : resolvedHashes ⟨[9]⟩ (toB32 7 ++ toB32 0) = [7, 9] := by
    unfold resolvedHashes; rw [inputWords_two]; decide
  refine ⟨fun K => ⟨demoWorld [7] 10, demoWorld_reachable _ (by omega),
      blobs_demo_accept K [7] h7, hres, ?_⟩,
    ⟨demoWorld [7] 10, demoWorld_reachable _ (by omega),
      blobs_demo_accept (fun _ => 0) [7] h7, by rw [hres]; decide, ?_⟩⟩
  · rw [hres]
    rintro ⟨hne, _⟩
    exact hne rfl
  · rw [hres]
    refine ⟨fun h => ?_, rfl⟩
    have := congrArg List.length h
    rw [encWords_length, encWords_length] at this
    simp at this

theorem BlobsTwoInputsOneListWitness : Properties.BlobsTwoInputsOneListWitness := by
  intro K
  have hatt : attached ⟨[7, 9]⟩ = [7, 9] := by decide
  have h7 : (7 : UInt256) ∈ attached ⟨[7, 9]⟩ := by rw [hatt]; simp
  have h9 : (9 : UInt256) ∈ attached ⟨[7, 9]⟩ := by rw [hatt]; simp
  have hres1 : resolvedHashes ⟨[9]⟩ (toB32 7 ++ toB32 0) = [7, 9] := by
    unfold resolvedHashes; rw [inputWords_two]; decide
  have hres2 : resolvedHashes ⟨[]⟩ (toB32 7 ++ toB32 9) = [7, 9] := by
    unfold resolvedHashes; rw [inputWords_two]; decide
  refine ⟨demoWorld [7, 9] 10, demoWorld_reachable _ (by omega),
    blobs_demo_accept K [7, 9] h7, ?_, ?_, by rw [hres1, hres2]⟩
  · rw [BlobsCheckDAAcceptsIff]
    refine ⟨by simp [toB32_length], ?_, ?_, ?_, by rw [hres2], rfl⟩
    · rw [inputWords_two]
      intro w hw _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact demoWorld_available h7 (by omega) (by simp [BLOB_EXPIRATION_BLOCKS])
      · exact demoWorld_available h9 (by omega) (by simp [BLOB_EXPIRATION_BLOCKS])
    · rw [inputWords_two]; decide
    · rw [inputWords_two]; decide
  · intro h
    have := congrArg (List.drop 32) h
    rw [List.drop_left' (toB32_length 7), List.drop_left' (toB32_length 7)] at this
    exact absurd (toB32_injective this) (by decide)

end Contracts.ZKsyncOSBlobsDA
