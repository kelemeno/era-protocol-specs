import EraSpec.Contracts.DataEncoding.Properties.TransferData
import EraSpec.Contracts.DataEncoding.Proofs.Abi

/-!
# Proofs: `DataEncoding` transfer data round-trips, injectivity and canonicity
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding

private theorem lt256_of_lt160 {n : ℕ} (h : n < 2 ^ 160) : n < 2 ^ 256 :=
  lt_trans h (by norm_num)

private theorem lt256_of_lt64 {n : ℕ} (h : n < 2 ^ 64) : n < 2 ^ 256 :=
  lt_trans h (by norm_num)

/-! ## Burn data -/

/-- Both burn decoders read the canonical encoding back, whatever follows it (the source decoder
then still rejects any trailing bytes by its length check). -/
theorem burnNoCheck_encode_append {a r t : ℕ} (ha : a < 2 ^ 256) (hr : r < 2 ^ 160)
    (ht : t < 2 ^ 160) (rest : List UInt8) :
    decodeBridgeBurnDataNoLengthCheck (encodeBridgeBurnData a r t ++ rest) = some (a, r, t) := by
  have h1 : decAddr (encodeBridgeBurnData a r t ++ rest) 32 = some r := by
    have : encodeBridgeBurnData a r t ++ rest = word a ++ (word r ++ (word t ++ rest)) := by
      simp [encodeBridgeBurnData]
    rw [this]; exact decAddr_at hr _ _ _ (by simp)
  have h2 : decAddr (encodeBridgeBurnData a r t ++ rest) 64 = some t := by
    have : encodeBridgeBurnData a r t ++ rest = (word a ++ word r) ++ (word t ++ rest) := by
      simp [encodeBridgeBurnData]
    rw [this]; exact decAddr_at ht _ _ _ (by simp)
  have h0 : readWord (encodeBridgeBurnData a r t ++ rest) 0 = a := by
    simp only [encodeBridgeBurnData, List.append_assoc]; exact readWord_word ha _
  have hl : ¬ (encodeBridgeBurnData a r t ++ rest).length < 96 := by
    simp [encodeBridgeBurnData]; omega
  unfold decodeBridgeBurnDataNoLengthCheck
  rw [if_neg hl]
  simp [h1, h2, h0]

theorem BurnDataRoundTrip : Properties.BurnDataRoundTrip := by
  intro a r t ha hr ht
  have h := burnNoCheck_encode_append ha hr ht []
  rw [List.append_nil] at h
  have hl : (encodeBridgeBurnData a r t).length = 96 := by simp [encodeBridgeBurnData]
  simp only [decodeBridgeBurnDataNoLengthCheck, hl] at h
  simpa [decodeBridgeBurnData, hl] using h

theorem BurnDataEncodeInjective : Properties.BurnDataEncodeInjective := by
  intro a r t a' r' t' ha hr ht ha' hr' ht' h
  have h1 := BurnDataRoundTrip a r t ha hr ht
  rw [h, BurnDataRoundTrip a' r' t' ha' hr' ht'] at h1
  exact (Option.some.inj h1).symm

theorem BurnDataCanonical : Properties.BurnDataCanonical := by
  intro d a r t h
  unfold decodeBridgeBurnData at h
  by_cases hl : d.length ≠ 96
  · rw [if_pos hl] at h; exact absurd h (by simp)
  · have hl' : d.length = 96 := not_not.mp hl
    rw [if_neg hl] at h
    cases hr : decAddr d 32 with
    | none => simp [hr] at h
    | some r' =>
    cases ht : decAddr d 64 with
    | none => simp [hr, ht] at h
    | some t' =>
    simp only [hr, ht, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨h32, rfl⟩ := decAddr_eq_some.mp hr
    obtain ⟨h64, rfl⟩ := decAddr_eq_some.mp ht
    refine ⟨?_, readWord_lt d 0, h32, h64⟩
    unfold encodeBridgeBurnData
    rw [word_readWord d 0 (by omega), word_readWord d 32 (by omega), word_readWord d 64 (by omega)]
    have e1 := split_word d 0
    have e2 := split_word d 32
    have e3 : d.drop 64 = (d.drop 64).take 32 := by
      rw [List.take_of_length_le]; simp; omega
    simp only [List.drop_zero, zero_add] at e1
    calc d = (d.drop 0).take 32 ++ ((d.drop 32).take 32 ++ (d.drop 64).take 32) := by
          simp only [List.drop_zero]
          conv_lhs => rw [e1, e2, e3]
      _ = _ := rfl

theorem BurnLengthCheckLoadBearing : Properties.BurnLengthCheckLoadBearing := by
  have h0 : (0 : ℕ) < 2 ^ 256 := by norm_num
  have h0' : (0 : ℕ) < 2 ^ 160 := by norm_num
  refine ⟨encodeBridgeBurnData 0 0 0, encodeBridgeBurnData 0 0 0 ++ [0], ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg List.length h
    simp at this
  · have := burnNoCheck_encode_append h0 h0' h0' []
    rw [List.append_nil] at this
    rw [this]; rfl
  · have := burnNoCheck_encode_append h0 h0' h0' []
    rw [List.append_nil] at this
    rw [this, burnNoCheck_encode_append h0 h0' h0' [0]]
  · simp [decodeBridgeBurnData, encodeBridgeBurnData]

/-! ## Mint data -/

theorem mint_encode_append {c r t a : ℕ} {m : List UInt8} (hc : c < 2 ^ 160) (hr : r < 2 ^ 160)
    (ht : t < 2 ^ 160) (ha : a < 2 ^ 256) (hm : m.length < 2 ^ 64) (rest : List UInt8) :
    decodeBridgeMintData (encodeBridgeMintData c r t a m ++ rest) = some (c, r, t, a, m) := by
  set d := encodeBridgeMintData c r t a m ++ rest with hd
  have hc0 : decAddr d 0 = some c := by
    have : d = [] ++ (word c ++ (word r ++ (word t ++ (word a ++ (word 160 ++ bytesTail m))) ++ rest)) := by
      simp [hd, encodeBridgeMintData]
    rw [this]; exact decAddr_at hc _ _ _ rfl
  have hr0 : decAddr d 32 = some r := by
    have : d = word c ++ (word r ++ ((word t ++ (word a ++ (word 160 ++ bytesTail m))) ++ rest)) := by
      simp [hd, encodeBridgeMintData]
    rw [this]; exact decAddr_at hr _ _ _ (by simp)
  have ht0 : decAddr d 64 = some t := by
    have : d = (word c ++ word r) ++ (word t ++ ((word a ++ (word 160 ++ bytesTail m)) ++ rest)) := by
      simp [hd, encodeBridgeMintData]
    rw [this]; exact decAddr_at ht _ _ _ (by simp)
  have ha0 : readWord d 96 = a := by
    have : d = (word c ++ word r ++ word t) ++ (word a ++ ((word 160 ++ bytesTail m) ++ rest)) := by
      simp [hd, encodeBridgeMintData]
    rw [this]; exact readWord_at ha _ _ _ (by simp)
  have hoff : readWord d 128 = 160 := by
    have : d = (word c ++ word r ++ word t ++ word a) ++ (word 160 ++ (bytesTail m ++ rest)) := by
      simp [hd, encodeBridgeMintData]
    rw [this]; exact readWord_at (by norm_num) _ _ _ (by simp)
  have hm0 : decBytes d 128 = some m := by
    apply decBytes_of d (word c ++ word r ++ word t ++ word a ++ word 160)
      (List.replicate ((32 - m.length % 32) % 32) 0 ++ rest) m 128
    · simp [hd, encodeBridgeMintData, bytesTail, pad32]
    · rw [hoff]; simp
    · simp
    · exact hm
  have hl : ¬ d.length < 160 := by simp [hd, encodeBridgeMintData]; omega
  simp [decodeBridgeMintData, hl, hc0, hr0, ht0, ha0, hm0]

theorem MintDataRoundTrip : Properties.MintDataRoundTrip := by
  intro c r t a m hc hr ht ha hm
  simpa using mint_encode_append hc hr ht ha hm []

theorem MintDataEncodeInjective : Properties.MintDataEncodeInjective := by
  intro c r t a c' r' t' a' m m' hc hr ht ha hm hc' hr' ht' ha' hm' h
  have h1 := MintDataRoundTrip c r t a m hc hr ht ha hm
  rw [h, MintDataRoundTrip c' r' t' a' m' hc' hr' ht' ha' hm'] at h1
  exact (Option.some.inj h1).symm

theorem MintDecodeNotCanonical : Properties.MintDecodeNotCanonical := by
  refine ⟨encodeBridgeMintData 0 0 0 0 [] ++ [0], 0, 0, 0, 0, [], ?_, ?_⟩
  · exact mint_encode_append (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _
  · intro h
    have := congrArg List.length h
    simp at this

/-! ## Deposit data -/

theorem DepositDataRoundTrip : Properties.DepositDataRoundTrip := by
  intro id td hid htd
  set X := word id ++ (word 64 ++ bytesTail td) with hX
  have hdrop : (encodeDepositData id td).drop 1 = X := by simp [encodeDepositData, hX]
  have hXl : 64 ≤ X.length := by simp [hX]; omega
  have hl : ¬ (encodeDepositData id td).length < 33 := by simp [encodeDepositData]
  have hh : (encodeDepositData id td).head? = some NEW_ENCODING_VERSION := rfl
  have hid0 : readWord X 0 = id := by rw [hX]; exact readWord_word hid _
  have hoff : readWord X 32 = 64 := by
    rw [hX]; exact readWord_at (by norm_num) (word id) _ 32 (by simp)
  have hb : decBytes X 32 = some td := by
    apply decBytes_of X (word id ++ word 64) (List.replicate ((32 - td.length % 32) % 32) 0) td 32
    · simp [hX, bytesTail, pad32]
    · rw [hoff]; simp
    · simp
    · exact htd
  simp [decodeDepositData, hl, hh, hdrop, not_lt.mpr hXl, hb, hid0]

theorem DepositDataEncodeInjective : Properties.DepositDataEncodeInjective := by
  intro id id' td td' hid htd hid' htd' h
  have h1 := DepositDataRoundTrip id td hid htd
  rw [h, DepositDataRoundTrip id' td' hid' htd'] at h1
  exact (Option.some.inj h1).symm

/-! ## Token data -/

theorem TokenDataRoundTrip : Properties.TokenDataRoundTrip := by
  intro c n s k hc hn hs hk
  have tn := bytesTail_length_le n
  have ts := bytesTail_length_le s
  have tn' := bytesTail_length_ge n
  set o2 := 128 + (bytesTail n).length with ho2
  set o3 := 128 + (bytesTail n).length + (bytesTail s).length with ho3
  set X := word c ++ (word 128 ++ (word o2 ++ (word o3 ++
      (bytesTail n ++ (bytesTail s ++ bytesTail k))))) with hX
  have hdrop : (encodeTokenData c n s k).drop 1 = X := by simp [encodeTokenData, hX, ho2, ho3]
  have hXl : 128 ≤ X.length := by simp [hX]; omega
  have hl : ¬ (encodeTokenData c n s k).length = 0 := by simp [encodeTokenData]
  have hh : (encodeTokenData c n s k).head? = some NEW_ENCODING_VERSION := rfl
  have hc0 : readWord X 0 = c := by rw [hX]; exact readWord_word hc _
  have ho2lt : o2 < 2 ^ 64 := by omega
  have ho3lt : o3 < 2 ^ 64 := by omega
  have r32 : readWord X 32 = 128 := by
    rw [hX]; exact readWord_at (by norm_num) (word c) _ 32 (by simp)
  have r64 : readWord X 64 = o2 := by
    have : X = (word c ++ word 128) ++ (word o2 ++ (word o3 ++
      (bytesTail n ++ (bytesTail s ++ bytesTail k)))) := by simp [hX]
    rw [this]; exact readWord_at (lt256_of_lt64 ho2lt) _ _ 64 (by simp)
  have r96 : readWord X 96 = o3 := by
    have : X = (word c ++ word 128 ++ word o2) ++ (word o3 ++
      (bytesTail n ++ (bytesTail s ++ bytesTail k))) := by simp [hX]
    rw [this]; exact readWord_at (lt256_of_lt64 ho3lt) _ _ 96 (by simp)
  have bn : decBytes X 32 = some n := by
    apply decBytes_of X (word c ++ word 128 ++ word o2 ++ word o3)
      (List.replicate ((32 - n.length % 32) % 32) 0 ++ (bytesTail s ++ bytesTail k)) n 32
    · simp [hX, bytesTail, pad32]
    · rw [r32]; simp
    · simp
    · omega
  have bs : decBytes X 64 = some s := by
    apply decBytes_of X (word c ++ word 128 ++ word o2 ++ word o3 ++ bytesTail n)
      (List.replicate ((32 - s.length % 32) % 32) 0 ++ bytesTail k) s 64
    · simp [hX, bytesTail, pad32]
    · rw [r64]; simp [ho2]; omega
    · simp; omega
    · omega
  have bk : decBytes X 96 = some k := by
    apply decBytes_of X (word c ++ word 128 ++ word o2 ++ word o3 ++ bytesTail n ++ bytesTail s)
      (List.replicate ((32 - k.length % 32) % 32) 0) k 96
    · simp [hX, bytesTail, pad32]
    · rw [r96]; simp [ho3]; omega
    · simp; omega
    · omega
  simp [decodeTokenData, hl, hh, hdrop, not_lt.mpr hXl, bn, bs, bk, hc0]

theorem TokenDataEncodeInjective : Properties.TokenDataEncodeInjective := by
  intro c c' n s k n' s' k' hc hc' hn hs hk hn' hs' hk' h
  have h1 := TokenDataRoundTrip c n s k hc hn hs hk
  rw [h, TokenDataRoundTrip c' n' s' k' hc' hn' hs' hk'] at h1
  exact (Option.some.inj h1).symm

/-! ## Finalize-deposit messages -/

theorem FinalizeRoundTrip : Properties.FinalizeRoundTrip := by
  intro sel c id td hsel hc hid
  have hl : ¬ (encodeFinalizeDepositData sel c id td).length < 68 := by
    simp [encodeFinalizeDepositData]; omega
  have h4 : (encodeFinalizeDepositData sel c id td).take 4 = be 4 sel := by
    simp [encodeFinalizeDepositData]
  have hsel' : fromBytesBE (be 4 sel) = sel := fromBytesBE_toBytesBE' (by
    have : (256 : ℕ) ^ 4 = 2 ^ 32 := by norm_num
    rw [this]; exact hsel)
  have hc4 : readWord (encodeFinalizeDepositData sel c id td) 4 = c := by
    exact readWord_at hc (be 4 sel) _ 4 (by simp)
  have hid36 : readWord (encodeFinalizeDepositData sel c id td) 36 = id := by
    have : encodeFinalizeDepositData sel c id td = (be 4 sel ++ word c) ++ (word id ++ td) := by
      simp [encodeFinalizeDepositData]
    rw [this]; exact readWord_at hid _ _ 36 (by simp)
  have hdrop : (encodeFinalizeDepositData sel c id td).drop 68 = td := by
    have : encodeFinalizeDepositData sel c id td = (be 4 sel ++ word c ++ word id) ++ td := by
      simp [encodeFinalizeDepositData]
    rw [this]; exact List.drop_left' (by simp)
  simp [decodeFinalizeDepositData, hl, h4, hsel', hc4, hid36, hdrop]

theorem FinalizeEncodeInjective : Properties.FinalizeEncodeInjective := by
  intro sel c id sel' c' id' td td' hsel hc hid hsel' hc' hid' h
  have h1 := FinalizeRoundTrip sel c id td hsel hc hid
  rw [h, FinalizeRoundTrip sel' c' id' td' hsel' hc' hid'] at h1
  exact (Option.some.inj h1).symm

theorem FinalizeCanonical : Properties.FinalizeCanonical := by
  intro d
  refine ⟨fun h => by simp [decodeFinalizeDepositData, h], fun h => ?_⟩
  refine ⟨fromBytesBE (d.take 4), readWord d 4, readWord d 36, d.drop 68, ?_, ?_,
    readWord_lt d 4, readWord_lt d 36, ?_⟩
  · simp [decodeFinalizeDepositData, not_lt.mpr h]
  · have := fromBytesBE_lt (d.take 4)
    have h4 : (d.take 4).length = 4 := by simp; omega
    rw [h4] at this
    have : (256 : ℕ) ^ 4 = 2 ^ 32 := by norm_num
    omega
  · unfold encodeFinalizeDepositData
    have h4 : (d.take 4).length = 4 := by simp; omega
    have hbe : be 4 (fromBytesBE (d.take 4)) = d.take 4 := by
      have := toBytesBE_fromBytesBE (d.take 4); rw [h4] at this; exact this
    rw [hbe, word_readWord d 4 (by omega), word_readWord d 36 (by omega)]
    have e1 : d.drop 4 = (d.drop 4).take 32 ++ d.drop 36 := split_word d 4
    have e2 : d.drop 36 = (d.drop 36).take 32 ++ d.drop 68 := split_word d 36
    calc _ = d.take 4 ++ d.drop 4 := by rw [← e2, ← e1]
      _ = d := List.take_append_drop 4 d

end Contracts.DataEncoding
