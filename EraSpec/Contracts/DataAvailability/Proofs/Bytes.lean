import EraSpec.Contracts.DataAvailability.Specs.OtherValidators
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashEncoding

/-!
# Proofs: byte-level lemmas for the DA validators

Auxiliary lemmas only; no property of `Properties/` is stated here. They relate the readers
`b32At`/`byteAt` to `toB32`, to `List.take`/`List.drop`/`++`, and to the layout `l2Output`, and give
the inversion lemmas of the helpers in `Specs/Common.lean`.
-/

namespace Contracts.DataAvailability

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

theorem b32At_append_left {a : Bytes} (b : Bytes) {off : ℕ} (h : off + 32 ≤ a.length) :
    b32At (a ++ b) off = b32At a off := by
  unfold b32At
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by rw [List.length_drop]; omega)]

theorem b32At_take {x : Bytes} {L off : ℕ} (h : off + 32 ≤ L) :
    b32At (x.take L) off = b32At x off := by
  unfold b32At
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

theorem b32At_drop (x : Bytes) (a off : ℕ) : b32At (x.drop a) off = b32At x (a + off) := by
  unfold b32At
  rw [List.drop_drop]

theorem byteAt_take {x : Bytes} {L i : ℕ} (h : i < L) : byteAt (x.take L) i = byteAt x i := by
  unfold byteAt
  simp [List.getD_eq_getElem?_getD, h]

theorem byteAt_append_left {a : Bytes} (b : Bytes) {i : ℕ} (h : i < a.length) :
    byteAt (a ++ b) i = byteAt a i := by
  unfold byteAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem byteAt_lt (x : Bytes) (i : ℕ) : byteAt x i < 256 := UInt8.toNat_lt _

/-- If `l.drop n` starts with `a`, then `a` is the element at `n`, and the tail is `l.drop (n+1)`. -/
theorem drop_eq_cons {α : Type} {l : List α} {n : ℕ} {a : α} {t : List α} (h : l.drop n = a :: t) :
    l[n]? = some a ∧ l.drop (n + 1) = t ∧ l.length = n + 1 + t.length := by
  refine ⟨?_, ?_, ?_⟩
  · have := List.getElem?_drop (xs := l) (i := n) (j := 0)
    rw [h] at this
    simpa using this.symm
  · have : (l.drop n).drop 1 = t := by rw [h]; rfl
    rwa [List.drop_drop] at this
  · have := congrArg List.length h
    rw [List.length_drop, List.length_cons] at this
    omega

/-! ## Zero-padded arrays -/

theorem padTo_length {lin : List UInt256} {max : ℕ} (h : lin.length ≤ max) :
    (padTo lin max).length = max := by
  unfold padTo
  rw [List.length_append, List.length_replicate]
  omega

/-- Reading a zero-padded array with default zero is reading the unpadded array. -/
theorem padTo_getD (lin : List UInt256) (max i : ℕ) : (padTo lin max).getD i 0 = lin.getD i 0 := by
  unfold padTo
  by_cases hi : i < lin.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · have hi' : lin.length ≤ i := by omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right hi',
      List.getElem?_eq_none hi', List.getElem?_replicate]
    split <;> rfl

theorem wordsAt_length (src : Bytes) (n max : ℕ) : (wordsAt src n max).length = max := by
  unfold wordsAt
  rw [List.length_map, List.length_range]

theorem wordsAt_getD (src : Bytes) (n max i : ℕ) :
    (wordsAt src n max).getD i 0 = if i < n ∧ i < max then b32At src (32 * i) else 0 := by
  unfold wordsAt
  by_cases hi : i < max
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, hi]

/-- A cloned array equals the zero-padded list of the words it was cloned from. -/
theorem wordsAt_eq_padTo {src : Bytes} {lin : List UInt256} {max : ℕ} (hmax : lin.length ≤ max)
    (h : ∀ i, i < lin.length → b32At src (32 * i) = lin.getD i 0) :
    wordsAt src lin.length max = padTo lin max := by
  apply List.ext_getElem
  · rw [wordsAt_length, padTo_length hmax]
  · intro i h1 h2
    have e1 : (wordsAt src lin.length max)[i] = (wordsAt src lin.length max).getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]
    have e2 : (padTo lin max)[i] = (padTo lin max).getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
    rw [e1, e2, wordsAt_getD, padTo_getD]
    rw [wordsAt_length] at h1
    by_cases hi : i < lin.length
    · rw [ite_eq_left ⟨hi, h1⟩, h i hi]
    · rw [ite_eq_right (fun hc => hi hc.1), List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega)]
      rfl

/-! ## The layout of the L2 DA validator's output -/

theorem flatten_toB32_length (lin : List UInt256) :
    ((lin.map toB32).flatten).length = 32 * lin.length := by
  induction lin with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.flatten_cons, List.length_append, toB32_length, ih, List.length_cons]
    omega

theorem b32At_flatten : ∀ (lin : List UInt256) (i : ℕ), i < lin.length →
    b32At ((lin.map toB32).flatten) (32 * i) = lin.getD i 0
  | [], i, h => by simp at h
  | x :: xs, 0, _ => by
    rw [List.map_cons, List.flatten_cons]
    exact b32At_zero_toB32_append x _
  | x :: xs, i + 1, h => by
    rw [List.map_cons, List.flatten_cons]
    have e : 32 * (i + 1) = (toB32 x).length + 32 * i := by rw [toB32_length]; omega
    rw [e, b32At_append_right, b32At_flatten xs i (by simpa using h)]
    rfl

theorem l2Output_length (sd fp : UInt256) (lin : List UInt256) :
    (l2Output sd fp lin).length = BLOB_DATA_OFFSET + 32 * lin.length := by
  unfold l2Output BLOB_DATA_OFFSET
  simp only [List.length_append, toB32_length, flatten_toB32_length, List.length_cons,
    List.length_nil]

theorem l2Output_b32At_0 (sd fp : UInt256) (lin : List UInt256) :
    b32At (l2Output sd fp lin) 0 = sd := by
  unfold l2Output
  simp only [List.append_assoc]
  exact b32At_zero_toB32_append _ _

theorem l2Output_b32At_32 (sd fp : UInt256) (lin : List UInt256) :
    b32At (l2Output sd fp lin) 32 = fp := by
  unfold l2Output
  simp only [List.append_assoc]
  have := b32At_append_right (toB32 sd)
    (toB32 fp ++ ([UInt8.ofNat lin.length] ++ (lin.map toB32).flatten)) 0
  rw [toB32_length] at this
  rw [this]
  exact b32At_zero_toB32_append _ _

theorem l2Output_b32At_lin (sd fp : UInt256) (lin : List UInt256) {i : ℕ} (h : i < lin.length) :
    b32At (l2Output sd fp lin) (BLOB_DATA_OFFSET + 32 * i) = lin.getD i 0 := by
  unfold l2Output
  have hlen : (toB32 sd ++ toB32 fp ++ [UInt8.ofNat lin.length]).length = BLOB_DATA_OFFSET := by
    simp [toB32_length, BLOB_DATA_OFFSET]
  rw [← hlen, b32At_append_right]
  exact b32At_flatten lin i h

theorem l2Output_byteAt_64 (sd fp : UInt256) (lin : List UInt256) :
    byteAt (l2Output sd fp lin) 64 = lin.length % 256 := by
  unfold l2Output byteAt
  have hlen : (toB32 sd ++ toB32 fp).length = 64 := by simp [toB32_length]
  rw [List.append_assoc (toB32 sd ++ toB32 fp), List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), hlen]
  simp

end Contracts.DataAvailability
