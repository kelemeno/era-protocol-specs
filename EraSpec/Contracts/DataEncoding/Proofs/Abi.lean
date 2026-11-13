import EraSpec.Contracts.DataEncoding.Specs.Abi
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashEncoding
import Mathlib.Tactic

/-!
# Auxiliary lemmas for the ABI toolkit

Byte-list facts used by the `DataEncoding`, `AttributesDecoder` and `InteroperableAddress`
proofs: lengths of words, reading a word back, reading a `bytes` field back, and the
big-endian arithmetic of `fromBytesBE` on concatenations. No property statements live here.
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding

theorem toBytesBE_length (k n : ℕ) : (toBytesBE k n).length = k :=
  AttackVectors.BundleHashEncoding.length_toBytesBE k n

@[simp] theorem word_length (n : ℕ) : (word n).length = 32 := toBytesBE_length 32 n

@[simp] theorem be_length (k n : ℕ) : (be k n).length = k := toBytesBE_length k n

theorem fromBytesBE_toBytesBE' {k n : ℕ} (h : n < 256 ^ k) : fromBytesBE (toBytesBE k n) = n :=
  AttackVectors.BundleHashEncoding.fromBytesBE_toBytesBE h

theorem two_pow_256 : (2 : ℕ) ^ 256 = 256 ^ 32 := by norm_num

theorem fromBytesBE_word {n : ℕ} (h : n < 2 ^ 256) : fromBytesBE (word n) = n :=
  fromBytesBE_toBytesBE' (by rw [← two_pow_256]; exact h)

theorem toBytesBE_inj {k n m : ℕ} (hn : n < 256 ^ k) (hm : m < 256 ^ k)
    (h : toBytesBE k n = toBytesBE k m) : n = m := by
  rw [← fromBytesBE_toBytesBE' hn, ← fromBytesBE_toBytesBE' hm, h]

theorem word_inj {n m : ℕ} (hn : n < 2 ^ 256) (hm : m < 2 ^ 256) (h : word n = word m) : n = m := by
  rw [← fromBytesBE_word hn, ← fromBytesBE_word hm, h]

theorem fromBytesBE_append (l₁ l₂ : List UInt8) :
    fromBytesBE (l₁ ++ l₂) = fromBytesBE l₁ * 256 ^ l₂.length + fromBytesBE l₂ := by
  induction l₂ using List.reverseRecOn with
  | nil => simp [fromBytesBE]
  | append_singleton l x ih =>
    rw [← List.append_assoc, AttackVectors.BundleHashEncoding.fromBytesBE_append_singleton,
      AttackVectors.BundleHashEncoding.fromBytesBE_append_singleton, ih]
    simp only [List.length_append, List.length_singleton, pow_succ]
    ring

theorem fromBytesBE_lt (l : List UInt8) : fromBytesBE l < 256 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [fromBytesBE]
  | append_singleton l x ih =>
    rw [AttackVectors.BundleHashEncoding.fromBytesBE_append_singleton]
    have hx : x.toNat < 256 := x.toNat_lt
    simp only [List.length_append, List.length_singleton, pow_succ]
    nlinarith

theorem fromBytesBE_replicate_zero (k : ℕ) : fromBytesBE (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', AttackVectors.BundleHashEncoding.fromBytesBE_append_singleton, ih]
    rfl

/-! ## Reading words -/

theorem readWord_append (pre rest : List UInt8) (k : ℕ) :
    readWord (pre ++ rest) (pre.length + k) = readWord rest k := by
  simp [readWord, List.drop_append, List.drop_eq_nil_of_le]

theorem readWord_append' (pre rest : List UInt8) (o : ℕ) (ho : o = pre.length) :
    readWord (pre ++ rest) o = readWord rest 0 := by
  subst ho; simpa using readWord_append pre rest 0

theorem readWord_word {n : ℕ} (h : n < 2 ^ 256) (post : List UInt8) :
    readWord (word n ++ post) 0 = n := by
  simp only [readWord, List.drop_zero]
  rw [List.take_left' (word_length n)]
  exact fromBytesBE_word h

/-- The word at offset `pre.length` of `pre ++ word n ++ post` is `n`. -/
theorem readWord_at {n : ℕ} (h : n < 2 ^ 256) (pre post : List UInt8) (o : ℕ) (ho : o = pre.length) :
    readWord (pre ++ (word n ++ post)) o = n := by
  rw [readWord_append' pre _ o ho, readWord_word h]

theorem decAddr_at {n : ℕ} (h : n < 2 ^ 160) (pre post : List UInt8) (o : ℕ) (ho : o = pre.length) :
    decAddr (pre ++ (word n ++ post)) o = some n := by
  have h' : n < 2 ^ 256 := lt_trans h (by norm_num)
  simp only [decAddr, readWord_at h' pre post o ho, h, ↓reduceIte]

theorem decAddr_eq_some {d : List UInt8} {o r : ℕ} :
    decAddr d o = some r ↔ readWord d o < 2 ^ 160 ∧ r = readWord d o := by
  unfold decAddr
  by_cases h : readWord d o < 2 ^ 160
  · rw [if_pos h]; exact ⟨fun e => ⟨h, (Option.some.inj e).symm⟩, fun e => by rw [e.2]⟩
  · rw [if_neg h]; exact ⟨fun e => absurd e (by simp), fun e => absurd e.1 h⟩

/-! ## Reading `bytes` fields -/

/-- A `bytes` field is read back when its head word at `o` holds `off`, and at `off` the tuple has
the length word of `b`, then `b`, then anything. -/
theorem decBytes_of (d pre rest b : List UInt8) (o : ℕ)
    (hd : d = pre ++ (word b.length ++ (b ++ rest)))
    (ho : readWord d o = pre.length) (hoff : pre.length < 2 ^ 64) (hb : b.length < 2 ^ 64) :
    decBytes d o = some b := by
  have hb' : b.length < 2 ^ 256 := lt_trans hb (by norm_num)
  have hlenw : readWord d pre.length = b.length := by
    rw [hd]; exact readWord_at hb' pre _ _ rfl
  have hlen : d.length = pre.length + 32 + b.length + rest.length := by
    rw [hd]; simp; ring
  have hdrop : d.drop (pre.length + 32) = b ++ rest := by
    have : d = (pre ++ word b.length) ++ (b ++ rest) := by simp [hd]
    rw [this]; exact List.drop_left' (by simp)
  have h1 : ¬ (2 ^ 64 ≤ pre.length) := by omega
  have h2 : ¬ (d.length < pre.length + 32) := by omega
  have h3 : ¬ (2 ^ 64 ≤ b.length) := by omega
  have h4 : ¬ (d.length < pre.length + 32 + b.length) := by omega
  simp only [decBytes, ho, hlenw, hdrop, h1, h2, h3, h4, ↓reduceIte, List.take_left']

theorem pad32_eq (b : List UInt8) : ∃ z, pad32 b = b ++ z := ⟨_, rfl⟩

theorem pad32_length_ge (b : List UInt8) : b.length ≤ (pad32 b).length := by
  simp [pad32]

theorem bytesTail_eq (b : List UInt8) : ∃ z, bytesTail b = word b.length ++ (b ++ z) :=
  ⟨List.replicate ((32 - b.length % 32) % 32) 0, by simp [bytesTail, pad32]⟩


/-! ## Re-encoding what was read -/

theorem toBytesBE_fromBytesBE (l : List UInt8) : toBytesBE l.length (fromBytesBE l) = l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
    have hx : x.toNat < 256 := x.toNat_lt
    rw [AttackVectors.BundleHashEncoding.fromBytesBE_append_singleton]
    simp only [List.length_append, List.length_singleton, toBytesBE]
    have h1 : (fromBytesBE l * 256 + x.toNat) / 256 = fromBytesBE l := by omega
    have h2 : (fromBytesBE l * 256 + x.toNat) % 256 = x.toNat := by omega
    rw [h1, h2, ih]
    congr 2
    exact UInt8.ofNat_toNat

/-- The word read at `o` re-encodes to the 32 bytes at `o`, when they are in bounds. -/
theorem word_readWord (d : List UInt8) (o : ℕ) (h : o + 32 ≤ d.length) :
    word (readWord d o) = (d.drop o).take 32 := by
  have hl : ((d.drop o).take 32).length = 32 := by simp; omega
  have := toBytesBE_fromBytesBE ((d.drop o).take 32)
  rw [hl] at this
  exact this

theorem readWord_lt (d : List UInt8) (o : ℕ) : readWord d o < 2 ^ 256 := by
  rw [two_pow_256]
  calc readWord d o < 256 ^ ((d.drop o).take 32).length := fromBytesBE_lt _
    _ ≤ 256 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by simp)

/-- Splitting a byte string at a word boundary. -/
theorem split_word (d : List UInt8) (o : ℕ) :
    d.drop o = (d.drop o).take 32 ++ d.drop (o + 32) := by
  rw [← List.drop_drop]
  exact (List.take_append_drop 32 (d.drop o)).symm

/-! ## Words inside concatenations, for `simp` -/

theorem readWord_word_append_ge (n : ℕ) (rest : List UInt8) (o : ℕ) (h : 32 ≤ o) :
    readWord (word n ++ rest) o = readWord rest (o - 32) := by
  obtain ⟨k, rfl⟩ : ∃ k, o = 32 + k := ⟨o - 32, by omega⟩
  have := readWord_append (word n) rest k
  simp only [word_length] at this
  rw [this]; congr 1; omega

theorem readWord_word_append_zero {n : ℕ} (h : n < 2 ^ 256) (rest : List UInt8) :
    readWord (word n ++ rest) 0 = n := readWord_word h rest

theorem readWord_word_zero {n : ℕ} (h : n < 2 ^ 256) : readWord (word n) 0 = n := by
  simpa using readWord_word h []

theorem pad32_length_le (b : List UInt8) : (pad32 b).length ≤ b.length + 31 := by
  simp [pad32]; omega

theorem bytesTail_length_le (b : List UInt8) : (bytesTail b).length ≤ b.length + 63 := by
  have := pad32_length_le b
  simp [bytesTail]; omega

theorem bytesTail_length_ge (b : List UInt8) : b.length + 32 ≤ (bytesTail b).length := by
  have := pad32_length_ge b
  simp [bytesTail]; omega

end Contracts.DataEncoding
