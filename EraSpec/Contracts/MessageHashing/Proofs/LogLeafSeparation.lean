import EraSpec.Contracts.MessageHashing.Properties.LogLeafSeparation
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashEncoding

/-!
# Proofs: a status log's leaf preimage differs from every other log's

Everything reduces to one fact, `logPre_chunks`: the preimage is a concatenation of fixed-width
chunks, so equal preimages have equal chunks. Well-formedness then turns the transaction-number and
sender chunks back into the numbers.
-/

namespace Contracts.MessageHashing

open AttackVectors.BundleHashEncoding (HashCollision toBytesBE word fromBytesBE)

/-! ## Bytes -/

lemma logLeaf_toBytesBE_length (k n : ℕ) : (toBytesBE k n).length = k :=
  AttackVectors.BundleHashEncoding.length_toBytesBE k n

lemma logLeaf_toBytesBE_inj {k a a' : ℕ} (ha : a < 256 ^ k) (ha' : a' < 256 ^ k)
    (h : toBytesBE k a = toBytesBE k a') : a = a' := by
  have e := congrArg fromBytesBE h
  have e1 : fromBytesBE (toBytesBE k a) = a :=
    AttackVectors.BundleHashEncoding.fromBytesBE_toBytesBE ha
  have e2 : fromBytesBE (toBytesBE k a') = a' :=
    AttackVectors.BundleHashEncoding.fromBytesBE_toBytesBE ha'
  rw [e1, e2] at e
  exact e

lemma logLeaf_word_lt (a : UInt256) : a.val < 256 ^ 32 :=
  lt_of_lt_of_eq a.isLt (by decide)

lemma logLeaf_w32_length (a : UInt256) : (w32 a).length = 32 := logLeaf_toBytesBE_length 32 a.val

lemma logLeaf_w32_inj {a b : UInt256} (h : w32 a = w32 b) : a = b :=
  Fin.ext (logLeaf_toBytesBE_inj (logLeaf_word_lt a) (logLeaf_word_lt b) h)

lemma logLeaf_boolByte_inj {b b' : Bool} (h : boolByte b = boolByte b') : b = b' := by
  cases b <;> cases b' <;> simp_all [boolByte]

lemma logPre_length (log : L2Log) : (logPre log).length = 88 := by
  simp [logPre]

lemma nodePre_length (a b : UInt256) : (nodePre a b).length = 64 := by
  simp [nodePre]

/-- **EQUAL PREIMAGES HAVE EQUAL CHUNKS**, for every two logs, well-formed or not. -/
lemma logPre_chunks {log log' : L2Log} (h : logPre log = logPre log') :
    log.l2ShardId = log'.l2ShardId ∧ log.isService = log'.isService
      ∧ toBytesBE 2 log.txNumberInBatch = toBytesBE 2 log'.txNumberInBatch
      ∧ toBytesBE 20 log.sender = toBytesBE 20 log'.sender
      ∧ log.key = log'.key ∧ log.value = log'.value := by
  simp only [logPre, List.singleton_append, List.cons.injEq] at h
  obtain ⟨h0, h1, h2⟩ := h
  obtain ⟨hT, h3⟩ := List.append_inj h2 (by rw [logLeaf_toBytesBE_length, logLeaf_toBytesBE_length])
  obtain ⟨hA, h4⟩ := List.append_inj h3 (by rw [logLeaf_toBytesBE_length, logLeaf_toBytesBE_length])
  obtain ⟨hK, hV⟩ := List.append_inj h4 (by rw [logLeaf_w32_length, logLeaf_w32_length])
  exact ⟨h0, logLeaf_boolByte_inj h1, hT, hA, logLeaf_w32_inj hK, logLeaf_w32_inj hV⟩

/-- The preimage determines a well-formed log. -/
theorem logPre_inj {log log' : L2Log} (hw : LogWellFormed log) (hw' : LogWellFormed log')
    (h : logPre log = logPre log') : log = log' := by
  obtain ⟨h0, h1, hT, hA, hK, hV⟩ := logPre_chunks h
  have ht := logLeaf_toBytesBE_inj hw.1 hw'.1 hT
  have ha := logLeaf_toBytesBE_inj hw.2 hw'.2 hA
  cases log
  cases log'
  simp_all

lemma logLeaf_bootloader_lt : BOOTLOADER_ADDRESS < 256 ^ 20 := by
  unfold BOOTLOADER_ADDRESS; norm_num

lemma logLeaf_messenger_lt : MESSENGER_ADDRESS < 256 ^ 20 := by
  unfold MESSENGER_ADDRESS; norm_num

lemma logLeaf_bootloader_ne_messenger : BOOTLOADER_ADDRESS ≠ MESSENGER_ADDRESS := by
  unfold BOOTLOADER_ADDRESS MESSENGER_ADDRESS; norm_num

lemma statusLog_wellFormed {t : ℕ} (tx : UInt256) (s : TxStatus) (ht : t < 256 ^ 2) :
    LogWellFormed (statusLog t tx s) :=
  ⟨ht, logLeaf_bootloader_lt⟩

lemma logLeaf_toWord_inj {s s' : TxStatus} (h : s.toWord = s'.toWord) : s = s' := by
  cases s <;> cases s' <;> first | rfl | exact absurd h (by decide)

/-! ## (a) -/

theorem LeafAndNodePreimageLengths : Properties.LeafAndNodePreimageLengths :=
  ⟨logPre_length, nodePre_length⟩

theorem LogPreimageInjective : Properties.LogPreimageInjective :=
  fun _ _ hw hw' h => logPre_inj hw hw' h

theorem LogPreimageInjectiveWitness : Properties.LogPreimageInjectiveWitness := by
  refine ⟨⟨statusLog 7 5 .success, statusLog 7 5 .success,
    statusLog_wellFormed 5 .success (by norm_num), statusLog_wellFormed 5 .success (by norm_num),
    rfl, by decide, by decide, rfl⟩, ?_⟩
  refine ⟨⟨0, true, 0, 0, 0, 0⟩, ⟨0, true, 256 ^ 2, 0, 0, 0⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg L2Log.txNumberInBatch h
    simp at this
  · simp only [logPre]
    rw [show toBytesBE 2 (256 ^ 2) = toBytesBE 2 0 from by decide]
  · exact ⟨by norm_num, by norm_num⟩
  · intro h
    exact absurd h.1 (by norm_num)

/-! ## (b) -/

theorem StatusPreimageFailureNeSuccess : Properties.StatusPreimageFailureNeSuccess := by
  intro t t' tx tx' h
  obtain ⟨-, -, -, -, -, hV⟩ := logPre_chunks h
  exact (by decide : (0 : UInt256) ≠ 1) hV

theorem StatusPreimageInjective : Properties.StatusPreimageInjective := by
  intro t t' tx tx' s s' ht ht' h
  obtain ⟨-, -, hT, -, hK, hV⟩ := logPre_chunks h
  exact ⟨logLeaf_toBytesBE_inj ht ht' hT, hK, logLeaf_toWord_inj hV⟩

theorem StatusPreimageInjectiveWitness : Properties.StatusPreimageInjectiveWitness := by
  refine ⟨⟨7, 7, 5, 5, .success, .success, by norm_num, by norm_num, rfl, by decide, by decide⟩, ?_⟩
  intro tx s
  simp only [logPre, statusLog]
  rw [show toBytesBE 2 (256 ^ 2) = toBytesBE 2 0 from by decide]

/-- No status preimage is the preimage of a well-formed-sender log with another sender. -/
lemma statusPre_ne_of_sender {log : L2Log} (hs : log.sender < 256 ^ 20)
    (hne : log.sender ≠ BOOTLOADER_ADDRESS) (t : ℕ) (tx : UInt256) (s : TxStatus) :
    logPre log ≠ logPre (statusLog t tx s) := by
  intro h
  obtain ⟨-, -, -, hA, -, -⟩ := logPre_chunks h
  exact hne (logLeaf_toBytesBE_inj hs logLeaf_bootloader_lt hA)

theorem StatusPreimageNeMessagePreimage : Properties.StatusPreimageNeMessagePreimage := by
  intro keccak t tx s m h
  exact statusPre_ne_of_sender (log := messageLog keccak m) logLeaf_messenger_lt
    (Ne.symm logLeaf_bootloader_ne_messenger) t tx s h.symm

theorem StatusPreimageNeDefault : Properties.StatusPreimageNeDefault := by
  refine ⟨?_, by decide⟩
  intro t tx s h
  have e := congrArg (fun l : List UInt8 => l[1]?) h
  simp [logPre, statusLog, logDefaultPre, boolByte] at e

theorem OtherSenderPreimageNeStatusPreimage : Properties.OtherSenderPreimageNeStatusPreimage :=
  fun _ hw hne t tx s => statusPre_ne_of_sender hw.2 hne t tx s

theorem OtherSenderPreimageWitness : Properties.OtherSenderPreimageWitness := by
  intro keccak
  refine ⟨⟨3, 0x1234, [1, 2, 3]⟩, ⟨by norm_num, by norm_num⟩, by decide, by decide,
    ⟨by simp [messageLog], logLeaf_messenger_lt⟩, Ne.symm logLeaf_bootloader_ne_messenger⟩

/-! ## (c) -/

theorem LeafHashPinsLogOrCollision : Properties.LeafHashPinsLogOrCollision := by
  intro keccak log log' hw hw' h
  by_cases he : log = log'
  · exact Or.inl he
  · exact Or.inr ⟨fun hp => he (logPre_inj hw hw' hp), h⟩

theorem FailureLeafOfOtherLogIsCollision : Properties.FailureLeafOfOtherLogIsCollision := by
  intro keccak t tx log ht hw hne h
  exact ⟨fun hp => hne (logPre_inj hw (statusLog_wellFormed tx .failure ht) hp), h⟩

theorem FailureLeafOfSuccessLogIsCollision : Properties.FailureLeafOfSuccessLogIsCollision := by
  intro keccak t t' tx tx' h
  exact ⟨fun hp => StatusPreimageFailureNeSuccess t t' tx tx' hp.symm, h⟩

theorem StatusLeafOfMessageIsCollision : Properties.StatusLeafOfMessageIsCollision := by
  intro keccak t tx s m h
  exact ⟨fun hp => StatusPreimageNeMessagePreimage keccak t tx s m hp.symm, h⟩

lemma logLeaf_toUInt256_inj {a b : ℕ} (ha : a < 256 ^ 20) (hb : b < 256 ^ 20)
    (h : Nat.toUInt256 a = Nat.toUInt256 b) : a = b := by
  have e := congrArg Fin.val h
  have hsz : (256 : ℕ) ^ 20 < UInt256.size := by decide
  simp only [Fin.val_ofNat] at e
  rwa [Nat.mod_eq_of_lt (lt_trans ha hsz), Nat.mod_eq_of_lt (lt_trans hb hsz)] at e

theorem MessageLeafPinsMessageOrCollision : Properties.MessageLeafPinsMessageOrCollision := by
  intro keccak m m' hw hw' h
  by_cases hp : logPre (messageLog keccak m) = logPre (messageLog keccak m')
  · obtain ⟨-, -, hT, -, hK, hV⟩ := logPre_chunks hp
    have ht := logLeaf_toBytesBE_inj hw.1 hw'.1 hT
    have ha := logLeaf_toUInt256_inj hw.2 hw'.2 hK
    by_cases hd : m.data = m'.data
    · left
      cases m
      cases m'
      simp_all
    · exact Or.inr (Or.inr ⟨hd, hV⟩)
  · exact Or.inr (Or.inl ⟨hp, h⟩)

/-! ## Witnesses -/

lemma lengthKeccak_logLeaf (log : L2Log) : logLeaf lengthKeccak log = Nat.toUInt256 88 := by
  simp only [logLeaf, lengthKeccak, logPre_length]

lemma pointKeccak_no_collision {p q : List UInt8} : ¬ HashCollision (pointKeccak p) q p := by
  rintro ⟨hne, heq⟩
  simp [pointKeccak, hne] at heq

theorem StatusLeafCollisionWitness : Properties.StatusLeafCollisionWitness := by
  unfold Properties.StatusLeafCollisionWitness
  refine ⟨⟨by norm_num, statusLog_wellFormed 5 .success (by norm_num), by decide,
      by rw [lengthKeccak_logLeaf, lengthKeccak_logLeaf]⟩,
    ⟨⟨by norm_num, by norm_num⟩, by rw [messageLeaf, lengthKeccak_logLeaf, lengthKeccak_logLeaf]⟩,
    pointKeccak_no_collision, pointKeccak_no_collision⟩

theorem LeafPinningWitness : Properties.LeafPinningWitness := by
  unfold Properties.LeafPinningWitness
  refine ⟨⟨statusLog_wellFormed 5 .success (by norm_num), statusLog_wellFormed 6 .success
      (by norm_num), by rw [lengthKeccak_logLeaf, lengthKeccak_logLeaf], by decide, ?_, ?_⟩,
    ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
      by rw [messageLeaf, messageLeaf, lengthKeccak_logLeaf, lengthKeccak_logLeaf], by decide,
      ⟨?_, ?_⟩, ?_⟩,
    ⟨⟨by norm_num, by norm_num⟩, by rw [messageLeaf, messageLeaf, lengthKeccak_logLeaf,
      lengthKeccak_logLeaf], by decide, ?_, ?_⟩⟩
  · intro hp
    obtain ⟨-, -, hT, -, -, -⟩ := logPre_chunks hp
    exact absurd (logLeaf_toBytesBE_inj (by simp [statusLog]) (by simp [statusLog]) hT)
      (by simp [statusLog])
  · simp only [lengthKeccak, logPre_length]
  · intro hp
    obtain ⟨-, -, -, -, hK, -⟩ := logPre_chunks hp
    exact absurd (logLeaf_toUInt256_inj (by norm_num) (by norm_num) hK) (by norm_num)
  · simp only [lengthKeccak, logPre_length]
  · rintro ⟨hne, -⟩
    exact hne rfl
  · rintro ⟨hne, -⟩
    apply hne
    simp [messageLog, lengthKeccak]
  · exact ⟨by decide, rfl⟩

end Contracts.MessageHashing
