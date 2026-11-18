import EraSpec.Contracts.DataEncoding.Properties.TxDataHash
import EraSpec.Contracts.DataEncoding.Proofs.AssetId

/-!
# Proofs: the deposit record hash, the legacy format, and the burn data

The lengths are arithmetic on `pad32` (`txData_pad32_length`). Injectivity drops the version
byte, splits the four heads with `List.append_inj`, reads the length word back (this is where
the bound `len < 2^256` is used), and takes that many bytes of the padded tail. The burn-data
results go through one equation for an accepted input (`txData_decode_of`) and the converse
round trip `toBytesBE 32 (fromBytesBE l) = l` for 32-byte `l` (`txData_toBytesBE_fromBytesBE`).
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding (toBytesBE fromBytesBE word pad32 HashCollision word_length
  length_toBytesBE fromBytesBE_toBytesBE fromBytesBE_append_singleton uint256_val_lt toUInt256_val)

/-! ## Byte-level facts -/

theorem txData_pad32_length (d : List UInt8) : (pad32 d).length = 32 * ((d.length + 31) / 32) := by
  simp only [pad32, List.length_append, List.length_replicate]
  omega

/-- Writing back the number a byte string reads as gives the byte string. -/
theorem txData_toBytesBE_fromBytesBE : ∀ (k : ℕ) (l : List UInt8), l.length = k →
    toBytesBE k (fromBytesBE l) = l
  | 0, l, h => by
      rw [List.length_eq_zero_iff] at h
      subst h
      rfl
  | k + 1, l, h => by
      obtain ⟨l', x, rfl⟩ : ∃ l' x, l = l' ++ [x] := by
        rcases List.eq_nil_or_concat l with h0 | ⟨l', x, hx⟩
        · subst h0; simp at h
        · exact ⟨l', x, by simpa using hx⟩
      have hl' : l'.length = k := by simpa using h
      rw [toBytesBE, fromBytesBE_append_singleton]
      have hx : x.toNat < 256 := x.toNat_lt
      have hdiv : (fromBytesBE l' * 256 + x.toNat) / 256 = fromBytesBE l' := by omega
      have hmod : (fromBytesBE l' * 256 + x.toNat) % 256 = x.toNat := by omega
      rw [hdiv, hmod, txData_toBytesBE_fromBytesBE k l' hl']
      simp

theorem txData_fromBytesBE_lt (l : List UInt8) : fromBytesBE l < 256 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [fromBytesBE]
  | append_singleton l x ih =>
    rw [fromBytesBE_append_singleton]
    have hx := x.toNat_lt
    simp only [List.length_append, List.length_singleton, pow_succ]
    nlinarith

theorem txData_fromBytesBE_lt_word {l : List UInt8} (h : l.length = 32) :
    fromBytesBE l < 256 ^ 32 := by
  have := txData_fromBytesBE_lt l
  rwa [h] at this

/-- A 32-byte string is the `uint256` head of the number it reads as. -/
theorem txData_encWord_fromBytesBE {l : List UInt8} (h : l.length = 32) :
    encWord (Nat.toUInt256 (fromBytesBE l)) = l := by
  have hlt := txData_fromBytesBE_lt_word h
  have hval : (Nat.toUInt256 (fromBytesBE l)).val = fromBytesBE l := by
    rw [Fin.val_ofNat]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_eq hlt (by norm_num [UInt256.size]))
  rw [encWord, hval]
  exact txData_toBytesBE_fromBytesBE 32 l h

/-- A 32-byte string whose number fits 160 bits is the address head of that address. -/
theorem txData_encAddr_fromBytesBE {l : List UInt8} (h : l.length = 32)
    (hr : fromBytesBE l < 2 ^ 160) : encAddr ⟨fromBytesBE l, hr⟩ = l := by
  rw [encAddr_eq_encWord]
  exact txData_toBytesBE_fromBytesBE 32 l h

theorem txData_fromBytesBE_encAddr (t : Addr) : fromBytesBE (encAddr t) = t.val := by
  rw [encAddr_eq_encWord, encWord]
  exact fromBytesBE_toBytesBE (lt_of_lt_of_le t.isLt (by norm_num))

theorem txData_fromBytesBE_encWord (w : UInt256) : fromBytesBE (encWord w) = w.val :=
  fromBytesBE_toBytesBE (uint256_val_lt w)

/-! ## Lengths -/

theorem txDataPreimage_length (s : Addr) (a : UInt256) (d : List UInt8) :
    (txDataPreimage s a d).length = 129 + 32 * ((d.length + 31) / 32) := by
  simp only [txDataPreimage, txDataAbiEncoding, List.length_cons, List.length_append,
    encAddr_length, encWord_length, word_length, txData_pad32_length]
  omega

theorem legacyTxDataPreimage_length (account token : Addr) (amount : UInt256) :
    (legacyTxDataPreimage account token amount).length = 96 := by
  simp [legacyTxDataPreimage, encAddr_length, encWord_length]

theorem txDataPreimage_head (s : Addr) (a : UInt256) (d : List UInt8) :
    (txDataPreimage s a d).head? = some 0x01 := rfl

theorem legacyTxDataPreimage_head (account token : Addr) (amount : UInt256) :
    (legacyTxDataPreimage account token amount).head? = some 0x00 := by
  simp [legacyTxDataPreimage, encAddr]

/-! ## Injectivity -/

theorem txDataPreimage_inj {s s' : Addr} {a a' : UInt256} {d d' : List UInt8}
    (hd : d.length < 2 ^ 256) (hd' : d'.length < 2 ^ 256)
    (h : txDataPreimage s a d = txDataPreimage s' a' d') : s = s' ∧ a = a' ∧ d = d' := by
  have h0 : txDataAbiEncoding s a d = txDataAbiEncoding s' a' d' := (List.cons.inj h).2
  unfold txDataAbiEncoding at h0
  obtain ⟨h128, hpad⟩ := List.append_inj h0 (by simp [encAddr_length, encWord_length])
  obtain ⟨h96, hlen⟩ := List.append_inj h128 (by simp [encAddr_length, encWord_length])
  obtain ⟨h64, -⟩ := List.append_inj h96 (by simp [encAddr_length, encWord_length])
  obtain ⟨hs, ha⟩ := List.append_inj h64 (by rw [encAddr_length, encAddr_length])
  have hl : d.length = d'.length := by
    have := congrArg fromBytesBE hlen
    rwa [fromBytesBE_toBytesBE (lt_of_lt_of_eq hd (by norm_num)),
      fromBytesBE_toBytesBE (lt_of_lt_of_eq hd' (by norm_num))] at this
  refine ⟨encAddr_inj hs, encWord_inj ha, ?_⟩
  have := congrArg (List.take d.length) hpad
  rwa [pad32, pad32, List.take_left' rfl, hl, List.take_left' rfl] at this

theorem legacyTxDataPreimage_inj {account account' token token' : Addr} {amount amount' : UInt256}
    (h : legacyTxDataPreimage account token amount = legacyTxDataPreimage account' token' amount') :
    account = account' ∧ token = token' ∧ amount = amount' := by
  obtain ⟨h1, h2, h3⟩ := assetId_three_heads (encAddr_length _) (encAddr_length _)
    (encAddr_length _) (encAddr_length _) h
  exact ⟨encAddr_inj h1, encAddr_inj h2, encWord_inj h3⟩

theorem txData_new_ne_legacy (s : Addr) (a : UInt256) (d : List UInt8) (account token : Addr)
    (amount : UInt256) :
    (txDataPreimage s a d).length ≠ (legacyTxDataPreimage account token amount).length
    ∧ (txDataPreimage s a d).head? ≠ (legacyTxDataPreimage account token amount).head?
    ∧ txDataPreimage s a d ≠ legacyTxDataPreimage account token amount := by
  have hlen : (txDataPreimage s a d).length ≠ (legacyTxDataPreimage account token amount).length := by
    rw [txDataPreimage_length, legacyTxDataPreimage_length]
    omega
  refine ⟨hlen, ?_, fun h => hlen (congrArg List.length h)⟩
  rw [txDataPreimage_head, legacyTxDataPreimage_head]
  decide

/-! ## The burn data -/

theorem encodeNtvBurnData_length (b : NativeTokenVaultBase.BurnData) :
    (encodeNtvBurnData b).length = 96 := by
  simp [encodeNtvBurnData, encWord_length, encAddr_length]

/-- The decoder on an accepted input. -/
theorem txData_decode_of {data : List UInt8} (hl : data.length = 96)
    (hr : fromBytesBE ((data.drop 32).take 32) < 2 ^ 160)
    (ht : fromBytesBE ((data.drop 64).take 32) < 2 ^ 160) :
    decodeNtvBurnData data
      = some ⟨Nat.toUInt256 (fromBytesBE (data.take 32)), ⟨_, hr⟩, ⟨_, ht⟩⟩ := by
  unfold decodeNtvBurnData
  rw [ite_eq_left hl, dite_eq_left hr, dite_eq_left ht]

theorem txData_burn_words (b : NativeTokenVaultBase.BurnData) :
    (encodeNtvBurnData b).take 32 = encWord b.amount
    ∧ ((encodeNtvBurnData b).drop 32).take 32 = encAddr b.receiver
    ∧ ((encodeNtvBurnData b).drop 64).take 32 = encAddr b.tokenHint := by
  have h64 : (encWord b.amount ++ encAddr b.receiver).length = 64 := by
    simp [encWord_length, encAddr_length]
  refine ⟨?_, ?_, ?_⟩
  · rw [encodeNtvBurnData, List.append_assoc, List.take_left' (encWord_length _)]
  · rw [encodeNtvBurnData, List.append_assoc, List.drop_left' (encWord_length _),
      List.take_left' (encAddr_length _)]
  · rw [encodeNtvBurnData, List.drop_left' h64, List.take_of_length_le
      (le_of_eq (encAddr_length _))]

theorem decodeNtvBurnData_encode (b : NativeTokenVaultBase.BurnData) :
    decodeNtvBurnData (encodeNtvBurnData b) = some b := by
  obtain ⟨w1, w2, w3⟩ := txData_burn_words b
  have hr : fromBytesBE (((encodeNtvBurnData b).drop 32).take 32) < 2 ^ 160 := by
    rw [w2, txData_fromBytesBE_encAddr]; exact b.receiver.isLt
  have ht : fromBytesBE (((encodeNtvBurnData b).drop 64).take 32) < 2 ^ 160 := by
    rw [w3, txData_fromBytesBE_encAddr]; exact b.tokenHint.isLt
  rw [txData_decode_of (encodeNtvBurnData_length b) hr ht]
  obtain ⟨amt, r, t⟩ := b
  simp only [Option.some.injEq, NativeTokenVaultBase.BurnData.mk.injEq]
  refine ⟨?_, Fin.ext ?_, Fin.ext ?_⟩
  · simp only [w1, txData_fromBytesBE_encWord]
    exact toUInt256_val amt
  · simp only [w2, txData_fromBytesBE_encAddr]
  · simp only [w3, txData_fromBytesBE_encAddr]

theorem encode_of_decodeNtvBurnData {data : List UInt8} {b : NativeTokenVaultBase.BurnData}
    (h : decodeNtvBurnData data = some b) : data = encodeNtvBurnData b := by
  unfold decodeNtvBurnData at h
  split_ifs at h with hl hr ht
  cases h
  have h1 : (data.take 32).length = 32 := by simp [hl]
  have h2 : ((data.drop 32).take 32).length = 32 := by simp [hl]
  have h3 : (data.drop 64).length = 32 := by simp [hl]
  have h3' : (data.drop 64).take 32 = data.drop 64 := List.take_of_length_le (le_of_eq h3)
  have hsplit : data = data.take 32 ++ ((data.drop 32).take 32 ++ data.drop 64) := by
    rw [show (64 : ℕ) = 32 + 32 from rfl, ← List.drop_drop, List.take_append_drop,
      List.take_append_drop]
  rw [encodeNtvBurnData]
  simp only
  rw [txData_encWord_fromBytesBE h1, txData_encAddr_fromBytesBE h2,
    txData_encAddr_fromBytesBE (by rw [h3']; exact h3), h3', List.append_assoc, ← hsplit]

theorem decodeNtvBurnData_eq_some_iff (data : List UInt8) (b : NativeTokenVaultBase.BurnData) :
    decodeNtvBurnData data = some b ↔ data = encodeNtvBurnData b := by
  constructor
  · exact encode_of_decodeNtvBurnData
  · intro h
    rw [h]
    exact decodeNtvBurnData_encode b

theorem decodeNtvBurnData_ne_none_iff (data : List UInt8) :
    decodeNtvBurnData data ≠ none ↔
      data.length = 96 ∧ fromBytesBE ((data.drop 32).take 32) < 2 ^ 160
        ∧ fromBytesBE ((data.drop 64).take 32) < 2 ^ 160 := by
  unfold decodeNtvBurnData
  split_ifs with hl hr ht
  · exact ⟨fun _ => ⟨hl, hr, ht⟩, fun _ => Option.some_ne_none _⟩
  · exact ⟨fun h => absurd rfl h, fun h => absurd h.2.2 ht⟩
  · exact ⟨fun h => absurd rfl h, fun h => absurd h.2.1 hr⟩
  · exact ⟨fun h => absurd rfl h, fun h => absurd h.1 hl⟩

/-! ## Witnesses

The recorded deposit of the two hash-level witnesses: sender `1`, asset id `1`, and NTV burn
data of amount `5` to receiver `2` with no token hint. The claim changes only the amount, to
`6`. The legacy record names the same sender, token `3` and the recorded amount. -/

/-- The burn data of the recorded deposit. -/
def txDataRecordedBurn : NativeTokenVaultBase.BurnData := ⟨5, 2, 0⟩

/-- The burn data of a claim that changes only the amount. -/
def txDataClaimedBurn : NativeTokenVaultBase.BurnData := ⟨6, 2, 0⟩

/-- The stand-in keccak of `TxDataHashWitness`: the recorded deposit's preimage goes to `1`, every
other byte string to `2`. It is not a hash. -/
def txDataSeparatingKeccak : Keccak := fun x =>
  if x = txDataPreimage 1 1 (encodeNtvBurnData txDataRecordedBurn) then 1 else 2

/-- Different burn data encode to different bytes (the decoder inverts the encoder). -/
theorem txData_encode_ne {b b' : NativeTokenVaultBase.BurnData} (h : b.amount ≠ b'.amount) :
    encodeNtvBurnData b ≠ encodeNtvBurnData b' := by
  intro he
  have hd := congrArg decodeNtvBurnData he
  rw [decodeNtvBurnData_encode, decodeNtvBurnData_encode] at hd
  exact h (congrArg NativeTokenVaultBase.BurnData.amount (Option.some.inj hd))

theorem txData_claimed_ne_recorded :
    encodeNtvBurnData txDataClaimedBurn ≠ encodeNtvBurnData txDataRecordedBurn :=
  txData_encode_ne (by decide)

/-- The claim's record preimage is not the recorded one. -/
theorem txData_claim_preimage_ne :
    txDataPreimage 1 1 (encodeNtvBurnData txDataClaimedBurn)
      ≠ txDataPreimage 1 1 (encodeNtvBurnData txDataRecordedBurn) := by
  intro h
  have hlen : ∀ b : NativeTokenVaultBase.BurnData, (encodeNtvBurnData b).length < 2 ^ 256 := by
    intro b; rw [encodeNtvBurnData_length]; norm_num
  exact txData_claimed_ne_recorded (txDataPreimage_inj (hlen _) (hlen _) h).2.2

/-! ## Certificates -/

theorem TxDataPreimageLength : Properties.TxDataPreimageLength := txDataPreimage_length

theorem TxDataPreimageLengthShape : Properties.TxDataPreimageLengthShape := by
  intro s a d
  rw [txDataPreimage_length]
  omega

theorem TxDataPreimageAtLeast161IffNonempty : Properties.TxDataPreimageAtLeast161IffNonempty := by
  intro s a d
  rw [txDataPreimage_length, List.ne_nil_iff_length_pos]
  omega

theorem TxDataPreimageMinimumIs129 : Properties.TxDataPreimageMinimumIs129 := by
  intro s a
  rw [txDataPreimage_length]
  rfl

theorem LegacyPreimageLength : Properties.LegacyPreimageLength := legacyTxDataPreimage_length

theorem TxDataFirstBytes : Properties.TxDataFirstBytes :=
  ⟨txDataPreimage_head, legacyTxDataPreimage_head⟩

theorem NewPreimageInjective : Properties.NewPreimageInjective :=
  fun _ _ _ _ _ _ hd hd' h => txDataPreimage_inj hd hd' h

theorem LegacyPreimageInjective : Properties.LegacyPreimageInjective :=
  fun _ _ _ _ _ _ h => legacyTxDataPreimage_inj h

theorem NewNeverLegacy : Properties.NewNeverLegacy := txData_new_ne_legacy

theorem TxDataHashBindsOrCollision : Properties.TxDataHashBindsOrCollision := by
  intro keccak s s' a a' d d' hd hd' h
  by_cases hpre : txDataPreimage s a d = txDataPreimage s' a' d'
  · exact Or.inl (txDataPreimage_inj hd hd' hpre)
  · exact Or.inr ⟨hpre, h⟩

theorem NewHashMatchesLegacyOnlyByCollision : Properties.NewHashMatchesLegacyOnlyByCollision :=
  fun _ s a d account token amount h => ⟨(txData_new_ne_legacy s a d account token amount).2.2, h⟩

theorem TxDataHashZeroIsPreimageEvent : Properties.TxDataHashZeroIsPreimageEvent :=
  fun _ _ _ _ => Iff.rfl

theorem TxDataHashWitness : Properties.TxDataHashWitness := by
  have hrec : txDataSeparatingKeccak (txDataPreimage 1 1 (encodeNtvBurnData txDataRecordedBurn))
      = 1 := ite_eq_left rfl
  have hclaim : txDataSeparatingKeccak (txDataPreimage 1 1 (encodeNtvBurnData txDataClaimedBurn))
      = 2 := ite_eq_right txData_claim_preimage_ne
  have hleg : txDataSeparatingKeccak (legacyTxDataPreimage 1 3 txDataRecordedBurn.amount) = 2 :=
    ite_eq_right fun h => (txData_new_ne_legacy 1 1 _ 1 3 _).2.2 h.symm
  have h12 : (1 : UInt256) ≠ 2 := by decide
  have h21 : (2 : UInt256) ≠ 1 := by decide
  refine ⟨txDataSeparatingKeccak, 1, 1, txDataRecordedBurn, txDataClaimedBurn, 3,
    by decide, by decide, by decide, by decide, by decide, by decide, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show txDataSeparatingKeccak _ ≠ txDataSeparatingKeccak _
    rw [hclaim, hrec]; exact h21
  · rintro ⟨-, h⟩
    rw [hclaim, hrec] at h; exact h21 h
  · show txDataSeparatingKeccak _ ≠ txDataSeparatingKeccak _
    rw [hrec, hleg]; exact h12
  · rintro ⟨-, h⟩
    rw [hrec, hleg] at h; exact h12 h
  · show ¬ txDataSeparatingKeccak _ = 0
    rw [hrec]; decide
  · show ¬ txDataSeparatingKeccak _ = 0
    rw [hclaim]; decide

theorem TxDataHashCollisionDisjunctNeeded : Properties.TxDataHashCollisionDisjunctNeeded := by
  have hlen : ∀ b : NativeTokenVaultBase.BurnData, (encodeNtvBurnData b).length < 2 ^ 256 := by
    intro b; rw [encodeNtvBurnData_length]; norm_num
  exact ⟨fun _ => 1, 1, 1, txDataRecordedBurn, txDataClaimedBurn, 3, by decide, by decide,
    by decide, by decide, by decide, by decide, rfl, rfl, hlen _, hlen _,
    txData_claimed_ne_recorded, rfl, rfl, by decide⟩

theorem BurnDataDecodeIffEncode : Properties.BurnDataDecodeIffEncode :=
  decodeNtvBurnData_eq_some_iff

theorem BurnDataLength : Properties.BurnDataLength := by
  refine ⟨encodeNtvBurnData_length, fun data hl => ?_, decodeNtvBurnData_encode⟩
  by_contra hne
  exact hl ((decodeNtvBurnData_ne_none_iff data).mp hne).1

theorem BurnDataAcceptsIff : Properties.BurnDataAcceptsIff := decodeNtvBurnData_ne_none_iff

theorem TwoFieldBurnDataRejected : Properties.TwoFieldBurnDataRejected := by
  intro amount receiver
  by_contra hne
  have := ((decodeNtvBurnData_ne_none_iff _).mp hne).1
  simp [encWord_length, encAddr_length] at this

theorem BurnDataLengthNotSufficient : Properties.BurnDataLengthNotSufficient := by
  have hw : ((encWord 0 ++ word (2 ^ 160) ++ encWord 0).drop 32).take 32 = word (2 ^ 160) := by
    rw [List.append_assoc, List.drop_left' (encWord_length _), List.take_left' (word_length _)]
  have hv : fromBytesBE (word (2 ^ 160)) = 2 ^ 160 := fromBytesBE_toBytesBE (by norm_num)
  refine ⟨encWord 0 ++ word (2 ^ 160) ++ encWord 0, ?_, ?_, ?_⟩
  · rw [List.length_append, List.length_append, encWord_length, word_length]
  · rw [hw, hv]
  · by_contra hne
    have h := ((decodeNtvBurnData_ne_none_iff _).mp hne).2.1
    rw [hw, hv] at h
    exact lt_irrefl _ h

theorem NtvClaimNamesRecordedDepositOrCollision :
    Properties.NtvClaimNamesRecordedDepositOrCollision := by
  intro keccak s s' a a' b b' d' hdec heq
  have hd' : d'.length < 2 ^ 256 := by
    rw [encode_of_decodeNtvBurnData hdec, encodeNtvBurnData_length]; norm_num
  have hb : (encodeNtvBurnData b).length < 2 ^ 256 := by
    rw [encodeNtvBurnData_length]; norm_num
  rcases TxDataHashBindsOrCollision keccak s' s a' a d' (encodeNtvBurnData b) hd' hb heq with
    ⟨h1, h2, h3⟩ | hc
  · refine Or.inl ⟨h1, h2, ?_⟩
    have hdb : decodeNtvBurnData d' = some b := by rw [h3]; exact decodeNtvBurnData_encode b
    rw [hdec] at hdb
    exact Option.some.inj hdb
  · exact Or.inr hc

theorem NtvClaimNamesRecordedDepositOrCollisionWitness :
    Properties.NtvClaimNamesRecordedDepositOrCollisionWitness := by
  have hrec : txDataSeparatingKeccak (txDataPreimage 1 1 (encodeNtvBurnData txDataRecordedBurn))
      = 1 := ite_eq_left rfl
  refine ⟨1, 1, txDataRecordedBurn, txDataClaimedBurn, by decide, by decide, by decide, by decide,
    by decide, rfl, rfl, ⟨txDataSeparatingKeccak, ?_, decodeNtvBurnData_encode _, rfl⟩,
    ⟨fun _ => 1, by decide, decodeNtvBurnData_encode _, rfl, txData_claim_preimage_ne, rfl⟩⟩
  show txDataSeparatingKeccak _ ≠ 0
  rw [hrec]; decide

/-! ## Model validation

Byte positions on concrete arguments: the version byte, the address head's left padding, the
offset word `0x60`, the length word, and the padding of a one-byte transfer data. -/

set_option maxRecDepth 8000

example : (txDataPreimage l2NtvAddr 7 [0xaa]).length = 161 := by decide
example : (txDataPreimage l2NtvAddr 7 [0xaa])[0]! = 0x01 := by decide    -- NEW_ENCODING_VERSION
example : (txDataPreimage l2NtvAddr 7 [0xaa])[1]! = 0x00 := by decide    -- address left padding
example : (txDataPreimage l2NtvAddr 7 [0xaa])[32]! = 0x04 := by decide   -- sender's low byte
example : (txDataPreimage l2NtvAddr 7 [0xaa])[64]! = 0x07 := by decide   -- asset id's low byte
example : (txDataPreimage l2NtvAddr 7 [0xaa])[96]! = 0x60 := by decide   -- offset of the bytes
example : (txDataPreimage l2NtvAddr 7 [0xaa])[128]! = 0x01 := by decide  -- length word
example : (txDataPreimage l2NtvAddr 7 [0xaa])[129]! = 0xaa := by decide  -- the data
example : (txDataPreimage l2NtvAddr 7 [0xaa])[130]! = 0x00 := by decide  -- right padding
example : (legacyTxDataPreimage l2NtvAddr l2NtvAddr 5).length = 96 := by decide

end Contracts.DataEncoding
