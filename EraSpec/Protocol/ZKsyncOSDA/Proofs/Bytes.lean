import EraSpec.Protocol.ZKsyncOSDA.Specs.CommitterDA
import EraSpec.Contracts.BlobsL1DAValidatorZKsyncOS.Proofs.Model

/-!
# Proofs: byte-level lemmas for the DA validators' input layout

Auxiliary lemmas only; no property of `../Properties/` is stated here. They read words back from
`toB32`/`encWords`/`l2Output` layouts, and invert `processL2`: an input it accepts is
`l2Output sd fp lin ++ rest` for the words it parsed (`processL2_eq_some`), and an input of that
shape is parsed back to those words (`processL2_l2Output`). Parts follow an earlier draft DA
model's byte lemmas.
-/

namespace Contracts.ZKsyncOSCommitterDA

open AttackVectors.BundleHashEncoding
open Contracts.ZKsyncOSBlobsDA (Bytes toB32 b32At DAOutput TxEnv encWords toB32_length
  toUInt256_val fromBytesBE_toB32 toB32_injective b32At_zero_toB32_append b32At_zero_toB32
  b32At_append_right encWords_cons encWords_nil encWords_length encWords_injective)

/-! ## Big-endian words -/

theorem fromBytesBE_lt (l : List UInt8) : fromBytesBE l < 256 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [fromBytesBE]
  | append_singleton l x ih =>
    rw [fromBytesBE_append_singleton, List.length_append, List.length_singleton, pow_succ]
    have hx : x.toNat < 256 := UInt8.toNat_lt _
    nlinarith

theorem toBytesBE_fromBytesBE (l : List UInt8) : toBytesBE l.length (fromBytesBE l) = l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
    rw [fromBytesBE_append_singleton, List.length_append, List.length_singleton, toBytesBE]
    have hx : x.toNat < 256 := UInt8.toNat_lt _
    have h1 : (fromBytesBE l * 256 + x.toNat) / 256 = fromBytesBE l := by omega
    have h2 : (fromBytesBE l * 256 + x.toNat) % 256 = x.toNat := by omega
    rw [h1, h2, ih, UInt8.ofNat_toNat]

/-- **A WORD READ BACK.** The 32 bytes at `off` are the big-endian bytes of the word read there. -/
theorem toB32_b32At {x : Bytes} {off : ℕ} (h : off + 32 ≤ x.length) :
    toB32 (b32At x off) = (x.drop off).take 32 := by
  have hlen : ((x.drop off).take 32).length = 32 := by
    rw [List.length_take, List.length_drop]; omega
  have hlt : fromBytesBE ((x.drop off).take 32) < UInt256.size := by
    have := fromBytesBE_lt ((x.drop off).take 32)
    rw [hlen] at this
    exact this
  unfold toB32 b32At
  have hval : (Nat.toUInt256 (fromBytesBE ((x.drop off).take 32))).val
      = fromBytesBE ((x.drop off).take 32) := Nat.mod_eq_of_lt hlt
  rw [hval]
  have := toBytesBE_fromBytesBE ((x.drop off).take 32)
  rw [hlen] at this
  exact this

theorem toB32_zero : toB32 0 = List.replicate 32 0 := by decide

theorem b32At_eq_zero_slice {x : Bytes} {off : ℕ} (h : off + 32 ≤ x.length)
    (hz : b32At x off = 0) : (x.drop off).take 32 = toB32 0 := by
  rw [← toB32_b32At h, hz]

/-! ## Concatenated words -/

theorem encWords_append (a b : List UInt256) : encWords (a ++ b) = encWords a ++ encWords b := by
  unfold encWords
  rw [List.map_append, List.flatten_append]

theorem encWords_replicate_zero (n : ℕ) : encWords (List.replicate n 0) = List.replicate (32 * n) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, encWords_cons, ih, toB32_zero, show 32 * (n + 1) = 32 + 32 * n by ring,
      List.replicate_add]

/-- Reading entry `i` of a concatenation of words, followed by anything. -/
theorem b32At_encWords_append :
    ∀ (lin : List UInt256) (t : Bytes) (i : ℕ), i < lin.length →
      b32At (encWords lin ++ t) (32 * i) = lin.getD i 0
  | [], _, i, h => by simp at h
  | x :: xs, t, 0, _ => by
    rw [encWords_cons, List.append_assoc]
    exact b32At_zero_toB32_append x _
  | x :: xs, t, i + 1, h => by
    rw [encWords_cons, List.append_assoc]
    have e : 32 * (i + 1) = (toB32 x).length + 32 * i := by rw [toB32_length]; ring
    rw [e, b32At_append_right, b32At_encWords_append xs t i (by simpa using h)]
    rfl

/-- The first `n` words of `x`, concatenated, are its first `32 n` bytes. -/
theorem encWords_map_range {x : Bytes} :
    ∀ {n : ℕ}, 32 * n ≤ x.length →
      encWords ((List.range n).map (fun i => b32At x (32 * i))) = x.take (32 * n)
  | 0, _ => by simp [encWords_nil]
  | n + 1, h => by
    rw [List.range_succ, List.map_append, encWords_append, encWords_map_range (by omega),
      List.map_singleton, encWords_cons, encWords_nil, List.append_nil,
      toB32_b32At (by omega), show 32 * (n + 1) = 32 * n + 32 by ring, List.take_add]

/-- A zeroed `max`-word array whose first `n` words are read from `src`. -/
theorem wordsAt_eq (src : Bytes) {n max : ℕ} (hn : n ≤ max) :
    wordsAt src n max
      = (List.range n).map (fun i => b32At src (32 * i)) ++ List.replicate (max - n) 0 := by
  apply List.ext_getElem
  · simp [wordsAt]; omega
  · intro i h1 h2
    simp only [wordsAt, List.getElem_map, List.getElem_range]
    by_cases hi : i < n
    · rw [ite_eq_left hi, List.getElem_append_left (by simpa using hi)]
      simp
    · rw [ite_eq_right hi, List.getElem_append_right (by simp; omega)]
      simp

/-! ## The L2 output layout -/

theorem l2Output_assoc (sd fp : UInt256) (lin : List UInt256) :
    l2Output sd fp lin = toB32 sd ++ (toB32 fp ++ (UInt8.ofNat lin.length :: encWords lin)) := by
  unfold l2Output
  simp only [List.append_assoc, List.singleton_append]

theorem l2Output_length (sd fp : UInt256) (lin : List UInt256) :
    (l2Output sd fp lin).length = 65 + 32 * lin.length := by
  rw [l2Output_assoc]
  simp only [List.length_append, List.length_cons, toB32_length, encWords_length]
  ring

theorem byteAt_l2Output (sd fp : UInt256) {lin : List UInt256} (t : Bytes)
    (h : lin.length < 256) : byteAt (l2Output sd fp lin ++ t) 64 = lin.length := by
  unfold byteAt
  rw [l2Output_assoc, List.append_assoc, List.append_assoc]
  have e : (64 : ℕ) = (toB32 sd).length + ((toB32 fp).length + 0) := by
    rw [toB32_length, toB32_length]
  rw [e, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  simp only [List.cons_append, List.getElem?_cons_zero, Option.getD_some]
  simp only [UInt8.toNat_ofNat']
  omega

theorem l2PrefixLen_l2Output (sd fp : UInt256) {lin : List UInt256} (t : Bytes)
    (h : lin.length < 256) :
    l2PrefixLen (l2Output sd fp lin ++ t) = (l2Output sd fp lin).length := by
  unfold l2PrefixLen
  rw [byteAt_l2Output sd fp t h, l2Output_length]
  rfl

theorem l2Prefix_l2Output (sd fp : UInt256) {lin : List UInt256} (t : Bytes)
    (h : lin.length < 256) : l2Prefix (l2Output sd fp lin ++ t) = l2Output sd fp lin := by
  unfold l2Prefix
  rw [l2PrefixLen_l2Output sd fp t h, List.take_left' rfl]

theorem drop_l2PrefixLen_l2Output (sd fp : UInt256) {lin : List UInt256} (t : Bytes)
    (h : lin.length < 256) :
    (l2Output sd fp lin ++ t).drop (l2PrefixLen (l2Output sd fp lin ++ t)) = t := by
  rw [l2PrefixLen_l2Output sd fp t h, List.drop_left]

theorem b32At_l2Output_zero (sd fp : UInt256) (lin : List UInt256) (t : Bytes) :
    b32At (l2Output sd fp lin ++ t) 0 = sd := by
  rw [l2Output_assoc, List.append_assoc]
  exact b32At_zero_toB32_append sd _

theorem b32At_l2Output_32 (sd fp : UInt256) (lin : List UInt256) (t : Bytes) :
    b32At (l2Output sd fp lin ++ t) 32 = fp := by
  rw [l2Output_assoc, List.append_assoc]
  have e : (32 : ℕ) = (toB32 sd).length + 0 := by rw [toB32_length]
  rw [e, b32At_append_right, List.append_assoc]
  exact b32At_zero_toB32_append fp _

theorem drop_65_l2Output (sd fp : UInt256) (lin : List UInt256) (t : Bytes) :
    (l2Output sd fp lin ++ t).drop 65 = encWords lin ++ t := by
  rw [l2Output_assoc]
  simp only [List.append_assoc, List.cons_append]
  rw [show (65 : ℕ) = 32 + (32 + 1) by rfl, ← List.drop_drop, List.drop_left' (toB32_length sd),
    ← List.drop_drop, List.drop_left' (toB32_length fp)]
  rfl

theorem linearOf_l2Output (sd fp : UInt256) {lin : List UInt256} (t : Bytes) {max : ℕ}
    (hmax : lin.length ≤ max) :
    linearOf (l2Output sd fp lin ++ t) lin.length max
      = lin ++ List.replicate (max - lin.length) 0 := by
  unfold linearOf
  rw [show BLOB_DATA_OFFSET = 65 from rfl, drop_65_l2Output, wordsAt_eq _ hmax]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [b32At_encWords_append lin t i (by simpa using h1)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-- **PARSING THE L2 OUTPUT LAYOUT.** `processL2` reads `l2Output sd fp lin ++ t` back as
`(sd, fp, lin padded to max, lin.length, t)` when keccak of the prefix is the given hash. -/
theorem processL2_l2Output (keccak : Bytes → UInt256) (sd fp : UInt256) {lin : List UInt256}
    (t : Bytes) {max : ℕ} (hmax : lin.length ≤ max) (h256 : lin.length < 256) :
    processL2 keccak (keccak (l2Output sd fp lin)) max (l2Output sd fp lin ++ t)
      = some ⟨sd, fp, lin ++ List.replicate (max - lin.length) 0, lin.length, t⟩ := by
  unfold processL2
  have hlen : (l2Output sd fp lin ++ t).length = 65 + 32 * lin.length + t.length := by
    rw [List.length_append, l2Output_length]
  rw [byteAt_l2Output sd fp t h256, l2Prefix_l2Output sd fp t h256,
    l2PrefixLen_l2Output sd fp t h256, b32At_l2Output_zero, b32At_l2Output_32,
    linearOf_l2Output sd fp t hmax, List.drop_left]
  have h1 : ¬ (l2Output sd fp lin ++ t).length < BLOB_DATA_OFFSET := by
    rw [hlen]; show ¬ _ < 65; omega
  have h2 : ¬ max < lin.length := by omega
  have h3 : ¬ (l2Output sd fp lin ++ t).length < (l2Output sd fp lin).length := by
    rw [hlen, l2Output_length]; omega
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right (not_not.mpr rfl)]

/-- **INVERTING `processL2`.** An input it accepts is `l2Output sd fp lin ++ l1DaInput` for the
parsed words, with `keccak` of that prefix equal to the given hash. -/
theorem processL2_eq_some {keccak : Bytes → UInt256} {h : UInt256} {max : ℕ} {input : Bytes}
    {p : L2Parsed} (hp : processL2 keccak h max input = some p) :
    ∃ lin : List UInt256, lin.length = p.blobsProvided ∧ p.blobsProvided ≤ max
      ∧ input = l2Output p.stateDiffHash p.fullPubdataHash lin ++ p.l1DaInput
      ∧ l2Prefix input = l2Output p.stateDiffHash p.fullPubdataHash lin
      ∧ l2PrefixLen input = (l2Output p.stateDiffHash p.fullPubdataHash lin).length
      ∧ keccak (l2Output p.stateDiffHash p.fullPubdataHash lin) = h
      ∧ p.blobsLinearHashes = lin ++ List.replicate (max - lin.length) 0 := by
  unfold processL2 at hp
  split_ifs at hp with h1 h2 h3 h4
  cases hp
  set n := byteAt input 64 with hn
  have hL : 65 + 32 * n ≤ input.length := by
    have : ¬ input.length < l2PrefixLen input := h3
    unfold l2PrefixLen at this
    exact Nat.le_of_not_lt this
  have hn256 : n < 256 := UInt8.toNat_lt _
  set lin := (List.range n).map (fun i => b32At (input.drop 65) (32 * i)) with hlin
  have hlinlen : lin.length = n := by simp [hlin]
  have hpre : input.take (65 + 32 * n) = l2Output (b32At input 0) (b32At input 32) lin := by
    rw [l2Output_assoc, hlinlen]
    rw [show 65 + 32 * n = 32 + (32 + (1 + 32 * n)) by ring, List.take_add, List.take_add,
      List.take_add]
    have e1 : input.take 32 = toB32 (b32At input 0) := by
      rw [toB32_b32At (by omega), List.drop_zero]
    have e2 : (input.drop 32).take 32 = toB32 (b32At input 32) := by
      rw [toB32_b32At (by omega)]
    have e3 : ((input.drop 32).drop 32).take 1 = [UInt8.ofNat n] := by
      rw [List.drop_drop, show 32 + 32 = 64 by rfl, List.drop_eq_getElem_cons (by omega)]
      simp only [List.take_succ_cons, List.take_zero]
      congr 1
      rw [hn]
      unfold byteAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
        UInt8.ofNat_toNat]
    have e4 : (((input.drop 32).drop 32).drop 1).take (32 * n) = encWords lin := by
      rw [List.drop_drop, List.drop_drop, show 32 + 32 + 1 = 65 by rfl, hlin,
        encWords_map_range (by rw [List.length_drop]; omega)]
    rw [e1, e2, e3, e4]
    simp
  have hpl : l2PrefixLen input = 65 + 32 * n := rfl
  refine ⟨lin, hlinlen, by show n ≤ max; omega, ?_, ?_, ?_, ?_, ?_⟩
  · show input = l2Output (b32At input 0) (b32At input 32) lin ++ input.drop (l2PrefixLen input)
    rw [hpl, ← hpre, List.take_append_drop]
  · show input.take (l2PrefixLen input) = _
    rw [hpl, hpre]
  · rw [hpl, l2Output_length, hlinlen]
  · have : keccak (l2Prefix input) = h := not_not.mp h4
    rw [← this]
    show keccak (l2Output (b32At input 0) (b32At input 32) lin) = keccak (input.take (l2PrefixLen input))
    rw [hpl, hpre]
  · show linearOf input n max = lin ++ List.replicate (max - lin.length) 0
    unfold linearOf
    rw [wordsAt_eq _ (by omega), hlinlen]
    rfl

/-! ## Reading the l2 output layout back -/

theorem l2Output_fp_eq {sd fp sd' fp' : UInt256} {lin lin' : List UInt256}
    (h : l2Output sd fp lin = l2Output sd' fp' lin') : fp = fp' := by
  have := congrArg (fun x => b32At x 32) h
  have e1 := b32At_l2Output_32 sd fp lin []
  have e2 := b32At_l2Output_32 sd' fp' lin' []
  rw [List.append_nil] at e1 e2
  rw [e1, e2] at this
  exact this

end Contracts.ZKsyncOSCommitterDA
