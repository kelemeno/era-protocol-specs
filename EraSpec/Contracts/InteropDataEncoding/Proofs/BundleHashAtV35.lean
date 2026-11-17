import EraSpec.Contracts.InteropDataEncoding.Properties.BundleHashAtV35
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashPinned
import EraSpec.Contracts.InteropCenter.Proofs.Dispatch

/-!
# Proofs at draft/v0.35.0: distinct sends give distinct bundle hashes, or a named collision

The argument is the pin's case split, one layer shorter. If the two bundle hashes are equal, either
the two byte strings differ, which is a collision on them, or they are equal. Equal bytes carry
equal salt slots, so keccak agrees on two packed preimages, which differ by `packed_addr_salt_inj`.
Across chains, equal bytes also carry equal source slots, so they name the same chain: the bundle's
own `sourceChainId` word does what the pin's outer chain-id word (`chain_eq_of_abiEncode_eq`) did.

For `sendMessage` bytes the salt word is not needed: equal bytes have equal tails after the 256-byte
head, the tail splits into the call and the attributes (the attributes' length does not depend on the
sender), and the call's `from` word and the attributes' salt bytes read back the sender and the salt.

The pin relation uses `abiEncode_right_inj` (`InteropCenter/Proofs/Dispatch.lean`) in one direction
and the source slot in the other.

The chain-reference facts use Mathlib's `Nat.log` bounds. The comparison with an independent ABI
encoder rewrites the chain references and then lets the kernel compare the byte lists
(`decide +kernel`, no `native_decide`).
-/

namespace AttackVectors.BundleHashEncoding.AtV35

open AttackVectors.BundleHashEncoding

/-! ## Byte-level facts -/

theorem bundleEncoding_split_src_v35 (version : UInt8) (src dst base salt oc oa : ℕ)
    (tail : List UInt8) :
    bundleEncoding version src dst base salt oc oa tail
      = (word 0x20 ++ bytes1Word version)
          ++ (word src ++ (word dst ++ (word base ++ (word salt ++ (word oc ++ (word oa ++ tail)))))) := by
  simp [bundleEncoding, List.append_assoc]

theorem bundleEncoding_split_dst_v35 (version : UInt8) (src dst base salt oc oa : ℕ)
    (tail : List UInt8) :
    bundleEncoding version src dst base salt oc oa tail
      = (word 0x20 ++ bytes1Word version ++ word src)
          ++ (word dst ++ (word base ++ (word salt ++ (word oc ++ (word oa ++ tail))))) := by
  simp [bundleEncoding, List.append_assoc]

theorem bundleEncoding_split_tail_v35 (version : UInt8) (src dst base salt oc oa : ℕ)
    (tail : List UInt8) :
    bundleEncoding version src dst base salt oc oa tail
      = (word 0x20 ++ bytes1Word version ++ word src ++ word dst ++ word base ++ word salt ++ word oc
          ++ word oa) ++ tail := by
  simp [bundleEncoding, List.append_assoc]

theorem bundleSourceSlotV35_bundleEncoding (version : UInt8) (src dst base salt oc oa : ℕ)
    (tail : List UInt8) :
    bundleSourceSlotV35 (bundleEncoding version src dst base salt oc oa tail) = word src := by
  have hpre : (word 0x20 ++ bytes1Word version).length = 64 := by
    simp [bytes1Word, length_toBytesBE]
  rw [bundleSourceSlotV35, bundleEncoding_split_src_v35, List.drop_left' hpre]
  exact List.take_left' (word_length src)

theorem bundleDestSlotV35_bundleEncoding (version : UInt8) (src dst base salt oc oa : ℕ)
    (tail : List UInt8) :
    bundleDestSlotV35 (bundleEncoding version src dst base salt oc oa tail) = word dst := by
  have hpre : (word 0x20 ++ bytes1Word version ++ word src).length = 96 := by
    simp [bytes1Word, length_toBytesBE]
  rw [bundleDestSlotV35, bundleEncoding_split_dst_v35, List.drop_left' hpre]
  exact List.take_left' (word_length dst)

/-- The dynamic tail starts right after the 256-byte head (the outer offset word and seven fields). -/
theorem bundleEncoding_drop256_v35 (version : UInt8) (src dst base salt oc oa : ℕ)
    (tail : List UInt8) :
    (bundleEncoding version src dst base salt oc oa tail).drop 256 = tail := by
  have hpre : (word 0x20 ++ bytes1Word version ++ word src ++ word dst ++ word base ++ word salt
      ++ word oc ++ word oa).length = 256 := by
    simp [bytes1Word, length_toBytesBE]
  rw [bundleEncoding_split_tail_v35, List.drop_left' hpre]

theorem bundleEncoding_length_ne52_v35 (version : UInt8) (src dst base salt oc oa : ℕ)
    (tail : List UInt8) : (bundleEncoding version src dst base salt oc oa tail).length ≠ 52 := by
  have := bundleEncoding_length version src dst base salt oc oa tail
  omega

/-- A word below `2^256` is recovered from its bytes. -/
theorem word_inj_of_lt_v35 {c c' : ℕ} (hc : c < 256 ^ 32) (hc' : c' < 256 ^ 32)
    (h : word c = word c') : c = c' := by
  have h2 := congrArg fromBytesBE h
  rwa [fromBytesBE_toBytesBE hc, fromBytesBE_toBytesBE hc'] at h2

theorem pad32_of_mod32_v35 {B : List UInt8} (h : B.length % 32 = 0) : pad32 B = B := by
  simp [pad32, h]

theorem pad32_length_v35 (b : List UInt8) :
    (pad32 b).length = b.length + (32 - b.length % 32) % 32 := by
  simp [pad32]

theorem pad32_length_mod32_v35 (b : List UInt8) : (pad32 b).length % 32 = 0 := by
  rw [pad32_length_v35]
  omega

/-! ## The `sendMessage` bytes -/

theorem formatEvmV1V35_length (c addr : ℕ) :
    (formatEvmV1V35 c addr).length = 26 + (toChainReferenceV35 c).length := by
  simp [formatEvmV1V35, length_toBytesBE]
  omega

theorem bundleAttributesEncodingV35_length (u : List UInt8) {s : List UInt8} (hs : s.length = 32) :
    (bundleAttributesEncodingV35 u s).length = 192 + (pad32 u).length := by
  simp [bundleAttributesEncodingV35, length_toBytesBE, hs]
  omega

/-- The call's `from` is its fourth head word. -/
theorem directCall_from_v35 (toAddr fromAddr value : ℕ) (data : List UInt8) :
    ((directCallEncodingV35 toAddr fromAddr value data).drop 96).take 32 = word fromAddr := by
  have hsplit : directCallEncodingV35 toAddr fromAddr value data
      = (bytes1Word 1 ++ word 0 ++ word toAddr)
          ++ (word fromAddr ++ (word value ++ (word 192 ++ (word data.length ++ pad32 data)))) := by
    simp [directCallEncodingV35, List.append_assoc]
  have hpre : (bytes1Word 1 ++ word 0 ++ word toAddr).length = 96 := by
    simp [bytes1Word, length_toBytesBE]
  rw [hsplit, List.drop_left' hpre]
  exact List.take_left' (word_length fromAddr)

/-- The attributes' user salt is their fourth head word, written as its own 32 bytes. -/
theorem bundleAttributes_salt_v35 (u : List UInt8) {s : List UInt8} (hs : s.length = 32) :
    ((bundleAttributesEncodingV35 u s).drop 96).take 32 = s := by
  have hsplit : bundleAttributesEncodingV35 u s
      = (word 128 ++ word 160 ++ word 0) ++ (s ++ (word 0 ++ (word u.length ++ pad32 u))) := by
    simp [bundleAttributesEncodingV35, List.append_assoc]
  have hpre : (word 128 ++ word 160 ++ word 0).length = 96 := by
    simp [length_toBytesBE]
  rw [hsplit, List.drop_left' hpre]
  exact List.take_left' hs

theorem sendMessageBytes_source_v35 (keccak : List UInt8 → UInt256) (c d base a recipient value : ℕ)
    (s payload : List UInt8) :
    bundleSourceSlotV35 (sendMessageBytesV35 keccak c d base a recipient value s payload) = word c :=
  bundleSourceSlotV35_bundleEncoding ..

theorem sendMessageBytes_dest_v35 (keccak : List UInt8 → UInt256) (c d base a recipient value : ℕ)
    (s payload : List UInt8) :
    bundleDestSlotV35 (sendMessageBytesV35 keccak c d base a recipient value s payload) = word d :=
  bundleDestSlotV35_bundleEncoding ..

theorem sendMessageBytes_salt_v35 (keccak : List UInt8 → UInt256) (c d base a recipient value : ℕ)
    (s payload : List UInt8) :
    bundleSaltSlot (sendMessageBytesV35 keccak c d base a recipient value s payload)
      = word (keccak (packedSalt a s)).val :=
  bundleSaltSlot_bundleEncoding ..

theorem sendMessageBytes_length_v35 (keccak : List UInt8 → UInt256) (c d base a recipient value : ℕ)
    {s : List UInt8} (payload : List UInt8) (hs : s.length = 32) :
    (sendMessageBytesV35 keccak c d base a recipient value s payload).length
      = 736 + (pad32 payload).length + (pad32 (formatEvmV1V35 c a)).length := by
  simp [sendMessageBytesV35, bundleEncoding, directCallEncodingV35, bundleAttributesEncodingV35,
    bytes1Word, length_toBytesBE, hs]
  omega

theorem sendMessageBytes_length_mod32_v35 (keccak : List UInt8 → UInt256)
    (c d base a recipient value : ℕ) {s : List UInt8} (payload : List UInt8) (hs : s.length = 32) :
    (sendMessageBytesV35 keccak c d base a recipient value s payload).length % 32 = 0 := by
  rw [sendMessageBytes_length_v35 keccak c d base a recipient value payload hs]
  have h1 := pad32_length_mod32_v35 payload
  have h2 := pad32_length_mod32_v35 (formatEvmV1V35 c a)
  omega

theorem sendMessageBytes_length_ne52_v35 (keccak : List UInt8 → UInt256)
    (c d base a recipient value : ℕ) (s payload : List UInt8) :
    (sendMessageBytesV35 keccak c d base a recipient value s payload).length ≠ 52 :=
  bundleEncoding_length_ne52_v35 _ _ _ _ _ _ _ _

/-- **THE BYTES OF A `sendMessage` BUNDLE DETERMINE ITS CHAIN, SENDER AND SALT.** -/
theorem sendMessageBytes_determine_v35 {keccak : List UInt8 → UInt256}
    {c c' d d' base base' a a' recipient recipient' value value' : ℕ}
    {s s' payload payload' : List UInt8}
    (hc : c < 256 ^ 32) (hc' : c' < 256 ^ 32) (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20)
    (hs : s.length = 32) (hs' : s'.length = 32)
    (h : sendMessageBytesV35 keccak c d base a recipient value s payload
      = sendMessageBytesV35 keccak c' d' base' a' recipient' value' s' payload') :
    c = c' ∧ a = a' ∧ s = s' := by
  -- one source slot, so one chain
  have hcc : c = c' := by
    have hslot := congrArg bundleSourceSlotV35 h
    rw [sendMessageBytes_source_v35, sendMessageBytes_source_v35] at hslot
    exact word_inj_of_lt_v35 hc hc' hslot
  subst hcc
  -- the tails after the head, and after the array's length and offset words
  have htail := congrArg (List.drop 256) h
  simp only [sendMessageBytesV35, bundleEncoding_drop256_v35] at htail
  have h64 : (word 1 ++ word 32).length = 64 := by simp [length_toBytesBE]
  have hbody : directCallEncodingV35 recipient a value payload
        ++ bundleAttributesEncodingV35 (formatEvmV1V35 c a) s
      = directCallEncodingV35 recipient' a' value' payload'
        ++ bundleAttributesEncodingV35 (formatEvmV1V35 c a') s' := by
    have hassoc : ∀ x : List UInt8, word 1 ++ (word 32 ++ x) = (word 1 ++ word 32) ++ x :=
      fun x => (List.append_assoc _ _ _).symm
    have h2 := congrArg (List.drop 64) htail
    rwa [hassoc, hassoc, List.drop_left' h64, List.drop_left' h64] at h2
  -- the attributes have one length whatever the sender, so the split point is the same
  have hlen : (bundleAttributesEncodingV35 (formatEvmV1V35 c a) s).length
      = (bundleAttributesEncodingV35 (formatEvmV1V35 c a') s').length := by
    rw [bundleAttributesEncodingV35_length _ hs, bundleAttributesEncodingV35_length _ hs',
      pad32_length_v35, pad32_length_v35, formatEvmV1V35_length, formatEvmV1V35_length]
  obtain ⟨hcall, hattrs⟩ := List.append_inj' hbody hlen
  have haa : a = a' := by
    have h3 := congrArg (fun l => (l.drop 96).take 32) hcall
    simp only [directCall_from_v35] at h3
    exact word_inj_of_lt_v35 (lt_trans ha (by norm_num)) (lt_trans ha' (by norm_num)) h3
  have hss : s = s' := by
    have h4 := congrArg (fun l => (l.drop 96).take 32) hattrs
    simpa only [bundleAttributes_salt_v35 _ hs, bundleAttributes_salt_v35 _ hs'] using h4
  exact ⟨rfl, haa, hss⟩

/-- `sendMessageBytesV35` reads `keccak` only at the sender's packed salt preimage. -/
theorem sendMessageBytes_congr_v35 {k k' : List UInt8 → UInt256} {a : ℕ} {s : List UInt8}
    (h : k (packedSalt a s) = k' (packedSalt a s)) (c d base recipient value : ℕ)
    (payload : List UInt8) :
    sendMessageBytesV35 k c d base a recipient value s payload
      = sendMessageBytesV35 k' c d base a recipient value s payload := by
  unfold sendMessageBytesV35
  rw [h]

/-! ## Chain references -/

theorem toChainReferenceV35_324 : toChainReferenceV35 324 = [0x01, 0x44] := by
  have hlog : Nat.log 256 324 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  rw [toChainReferenceV35, hlog]
  decide

theorem toChainReferenceV35_326 : toChainReferenceV35 326 = [0x01, 0x46] := by
  have hlog : Nat.log 256 326 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  rw [toChainReferenceV35, hlog]
  decide

theorem toChainReferenceV35_70000 : toChainReferenceV35 70000 = [0x01, 0x11, 0x70] := by
  have hlog : Nat.log 256 70000 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  rw [toChainReferenceV35, hlog]
  decide

/-! ## Model validation against an independent ABI encoder

The word lists in `Properties.SendMessageBytesMatchAbiEncoderV35` are `cast abi-encode` output. The
chain references are rewritten first (`Nat.log` is not evaluated by the kernel), then the kernel
compares the two byte lists. -/

theorem sendMessageBytes_matches_abi_encoder_v35 :
    sendMessageBytesV35 (fun _ => 7) 324 325 1 1 0x1234 0 (word 0) [0xde, 0xad, 0xbe, 0xef]
      = [0x20, 0x100000000000000000000000000000000000000000000000000000000000000, 0x144, 0x145,
          0x1, 0x7, 0xe0, 0x220, 0x1, 0x20,
          0x100000000000000000000000000000000000000000000000000000000000000, 0x0, 0x1234, 0x1,
          0x0, 0xc0, 0x4, 0xdeadbeef00000000000000000000000000000000000000000000000000000000,
          0x80, 0xa0, 0x0, 0x0, 0x0, 0x1c,
          0x1000002014414000000000000000000000000000000000000000100000000].flatMap word := by
  rw [sendMessageBytesV35, formatEvmV1V35, toChainReferenceV35_324]
  decide +kernel

theorem noCallBytes_matches_abi_encoder_v35 :
    noCallBytesV35 (fun _ => 7) 324 325 1 1 (word 0) (formatEvmV1V35 324 7)
      = [0x20, 0x100000000000000000000000000000000000000000000000000000000000000, 0x144, 0x145,
          0x1, 0x7, 0xe0, 0x100, 0x0, 0x80, 0xa0, 0x0, 0x0, 0x0, 0x1c,
          0x1000002014414000000000000000000000000000000000000000700000000].flatMap word := by
  rw [noCallBytesV35, formatEvmV1V35, toChainReferenceV35_324]
  decide +kernel

theorem sendMessageBytes_matches_abi_encoder_wide_v35 :
    sendMessageBytesV35 (fun _ => 9) 70000 325 5 0xabcdef 0x1234 77 (word 3)
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
          26, 27, 28, 29, 30, 31, 32, 33]
      = [0x20, 0x100000000000000000000000000000000000000000000000000000000000000, 0x11170, 0x145,
          0x5, 0x9, 0xe0, 0x240, 0x1, 0x20,
          0x100000000000000000000000000000000000000000000000000000000000000, 0x0, 0x1234,
          0xabcdef, 0x4d, 0xc0, 0x21,
          0x102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20,
          0x2100000000000000000000000000000000000000000000000000000000000000, 0x80, 0xa0, 0x0, 0x3,
          0x0, 0x1d, 0x1000003011170140000000000000000000000000000000000abcdef000000].flatMap word := by
  rw [sendMessageBytesV35, formatEvmV1V35, toChainReferenceV35_70000]
  decide +kernel

theorem toChainReferenceV35_length (c : ℕ) :
    (toChainReferenceV35 c).length = Nat.log 256 c + 1 :=
  length_toBytesBE _ _

theorem toChainReferenceV35_minimal {c : ℕ} (hc : c < 256 ^ 32) :
    fromBytesBE (toChainReferenceV35 c) = c
      ∧ (toChainReferenceV35 c).length ≤ 32
      ∧ (c ≠ 0 → 256 ^ ((toChainReferenceV35 c).length - 1) ≤ c) := by
  rw [toChainReferenceV35_length]
  refine ⟨fromBytesBE_toBytesBE (Nat.lt_pow_succ_log_self (by norm_num) c), ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos c with h0 | hpos
    · subst h0
      simp
    · have := Nat.log_lt_of_lt_pow (Nat.pos_iff_ne_zero.mp hpos) hc
      omega
  · intro h0
    simpa using Nat.pow_log_le_self 256 h0

/-! ## The keccak layer -/

theorem sends_distinct_bundle_hashes_or_keccak_collision_v35 (keccak : List UInt8 → UInt256)
    {a a' : ℕ} {s s' B B' : List UInt8}
    (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20) (hs : s.length = 32) (hs' : s'.length = 32)
    (hB : bundleSaltSlot B = word (keccak (packedSalt a s)).val)
    (hB' : bundleSaltSlot B' = word (keccak (packedSalt a' s')).val)
    (hne : ¬ (a = a' ∧ s = s')) :
    bundleHashV35 keccak B ≠ bundleHashV35 keccak B'
      ∨ HashCollision keccak B B'
      ∨ HashCollision keccak (packedSalt a s) (packedSalt a' s') := by
  by_cases hh : bundleHashV35 keccak B = bundleHashV35 keccak B'
  · by_cases hBB : B = B'
    · -- one byte string carries one salt slot
      refine Or.inr (Or.inr ⟨packedSalt_ne ha ha' hs hs' hne, ?_⟩)
      rw [← hBB, hB] at hB'
      exact word_val_inj hB'
    · exact Or.inr (Or.inl ⟨hBB, hh⟩)
  · exact Or.inl hh

theorem sends_distinct_bundle_hashes_on_v35 (keccak : List UInt8 → UInt256)
    {a a' : ℕ} {s s' B B' : List UInt8}
    (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20) (hs : s.length = 32) (hs' : s'.length = 32)
    (hB : bundleSaltSlot B = word (keccak (packedSalt a s)).val)
    (hB' : bundleSaltSlot B' = word (keccak (packedSalt a' s')).val)
    (hne : ¬ (a = a' ∧ s = s'))
    (hbytes : Set.InjOn keccak {B, B'})
    (hsalt : Set.InjOn keccak {packedSalt a s, packedSalt a' s'}) :
    bundleHashV35 keccak B ≠ bundleHashV35 keccak B' := by
  rcases sends_distinct_bundle_hashes_or_keccak_collision_v35 keccak ha ha' hs hs' hB hB' hne
    with h | h | h
  · exact h
  · exact absurd h ((injOn_pair_iff_no_collision _ _ _).mp hbytes)
  · exact absurd h ((injOn_pair_iff_no_collision _ _ _).mp hsalt)

theorem sends_distinct_bundle_hashes_across_chains_or_keccak_collision_v35
    (keccak : List UInt8 → UInt256) {c c' a a' : ℕ} {s s' B B' : List UInt8}
    (hc : c < 256 ^ 32) (hc' : c' < 256 ^ 32)
    (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20) (hs : s.length = 32) (hs' : s'.length = 32)
    (hsrc : bundleSourceSlotV35 B = word c) (hsrc' : bundleSourceSlotV35 B' = word c')
    (hB : bundleSaltSlot B = word (keccak (packedSalt a s)).val)
    (hB' : bundleSaltSlot B' = word (keccak (packedSalt a' s')).val)
    (hne : ¬ (c = c' ∧ a = a' ∧ s = s')) :
    bundleHashV35 keccak B ≠ bundleHashV35 keccak B'
      ∨ HashCollision keccak B B'
      ∨ HashCollision keccak (packedSalt a s) (packedSalt a' s') := by
  by_cases hBB : B = B'
  · -- one byte string, so one source slot: one chain, and the one-chain case applies
    have hcc : c = c' := by
      rw [← hBB, hsrc] at hsrc'
      exact word_inj_of_lt_v35 hc hc' hsrc'
    rcases sends_distinct_bundle_hashes_or_keccak_collision_v35 keccak ha ha' hs hs' hB hB'
      (fun h => hne ⟨hcc, h⟩) with h | h | h
    · exact Or.inl h
    · exact absurd hBB h.1
    · exact Or.inr (Or.inr h)
  · by_cases hh : bundleHashV35 keccak B = bundleHashV35 keccak B'
    · exact Or.inr (Or.inl ⟨hBB, hh⟩)
    · exact Or.inl hh

theorem source_and_destination_agree_or_collision_v35 (keccak : List UInt8 → UInt256)
    (B x : List UInt8) (h : bundleHashV35 keccak x = bundleHashV35 keccak B) :
    x = B ∨ HashCollision keccak x B := by
  by_cases hx : x = B
  · exact Or.inl hx
  · exact Or.inr ⟨hx, h⟩

/-! ## `sendMessage` bundles -/

theorem sendMessages_distinct_bundle_hashes_or_bytes_collision_v35 (keccak : List UInt8 → UInt256)
    {c c' d d' base base' a a' recipient recipient' value value' : ℕ}
    {s s' payload payload' : List UInt8}
    (hc : c < 256 ^ 32) (hc' : c' < 256 ^ 32) (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20)
    (hs : s.length = 32) (hs' : s'.length = 32) (hne : ¬ (c = c' ∧ a = a' ∧ s = s')) :
    bundleHashV35 keccak (sendMessageBytesV35 keccak c d base a recipient value s payload)
        ≠ bundleHashV35 keccak (sendMessageBytesV35 keccak c' d' base' a' recipient' value' s' payload')
      ∨ HashCollision keccak (sendMessageBytesV35 keccak c d base a recipient value s payload)
          (sendMessageBytesV35 keccak c' d' base' a' recipient' value' s' payload') := by
  by_cases hh : bundleHashV35 keccak (sendMessageBytesV35 keccak c d base a recipient value s payload)
      = bundleHashV35 keccak (sendMessageBytesV35 keccak c' d' base' a' recipient' value' s' payload')
  · exact Or.inr ⟨fun hBB => hne (sendMessageBytes_determine_v35 hc hc' ha ha' hs hs' hBB), hh⟩
  · exact Or.inl hh

theorem sendMessages_distinct_bundle_hashes_on_v35 (keccak : List UInt8 → UInt256)
    {c c' d d' base base' a a' recipient recipient' value value' : ℕ}
    {s s' payload payload' : List UInt8}
    (hc : c < 256 ^ 32) (hc' : c' < 256 ^ 32) (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20)
    (hs : s.length = 32) (hs' : s'.length = 32) (hne : ¬ (c = c' ∧ a = a' ∧ s = s'))
    (hinj : Set.InjOn keccak {sendMessageBytesV35 keccak c d base a recipient value s payload,
      sendMessageBytesV35 keccak c' d' base' a' recipient' value' s' payload'}) :
    bundleHashV35 keccak (sendMessageBytesV35 keccak c d base a recipient value s payload)
      ≠ bundleHashV35 keccak (sendMessageBytesV35 keccak c' d' base' a' recipient' value' s' payload') := by
  rcases sendMessages_distinct_bundle_hashes_or_bytes_collision_v35 keccak hc hc' ha ha' hs hs' hne
    (d := d) (d' := d') (base := base) (base' := base') (recipient := recipient)
    (recipient' := recipient') (value := value) (value' := value') (payload := payload)
    (payload' := payload') with h | h
  · exact h
  · exact absurd h ((injOn_pair_iff_no_collision _ _ _).mp hinj)

/-! ## The pin relation -/

theorem pin_preimage_drops_to_v35_preimage (c : ℕ) {B : List UInt8} (h : B.length % 32 = 0) :
    (pinPreimageV35 c B).drop 96 = B := by
  rw [pinPreimageV35, abiEncode_drop96, pad32_of_mod32_v35 h]

theorem pin_and_v35_preimages_coincide {c c' : ℕ} {B B' : List UInt8}
    (hc : c < 256 ^ 32) (hc' : c' < 256 ^ 32)
    (hsrc : bundleSourceSlotV35 B = word c) (hsrc' : bundleSourceSlotV35 B' = word c') :
    pinPreimageV35 c B = pinPreimageV35 c' B' ↔ B = B' := by
  constructor
  · intro h
    exact Contracts.InteropCenter.abiEncode_right_inj h
  · intro hBB
    have hcc : c = c' := by
      rw [← hBB, hsrc] at hsrc'
      exact word_inj_of_lt_v35 hc hc' hsrc'
    rw [hcc, hBB]

/-! ## Witnesses and countermodels

Senders `1` and `2` with the zero user salt, on chain `324` (and `326` for the cross-chain cases).
The bundle bytes are `sendMessageBytesV35`: destination `325`, base-token asset id `1`, one direct
call to `0x1234` with value `0` and payload `0xdeadbeef`, and the sender's default unbundler. -/

/-- The witnesses' payload. -/
abbrev witnessPayloadV35 : List UInt8 := [0xde, 0xad, 0xbe, 0xef]

/-- A stand-in for keccak, used only in witnesses. On a 52-byte input (a packed salt preimage) it
returns the sender; on anything else (bundle bytes) it returns the salt word in the salt slot. -/
def toyKeccakV35 (x : List UInt8) : UInt256 :=
  if x.length = 52 then Nat.toUInt256 (fromBytesBE (x.take 20))
  else Nat.toUInt256 (fromBytesBE (bundleSaltSlot x))

/-- A stand-in that separates packed preimages by sender and bundle bytes by their source slot. -/
def sourceKeccakV35 (x : List UInt8) : UInt256 :=
  if x.length = 52 then Nat.toUInt256 (fromBytesBE (x.take 20))
  else Nat.toUInt256 (fromBytesBE (bundleSourceSlotV35 x))

/-- A stand-in that gives the named packed preimage `p` the value `1`, every other 52-byte input `2`,
the named bytes `B` the value `3`, and every other input `4`. -/
def separatingKeccakV35 (p B x : List UInt8) : UInt256 :=
  if x.length = 52 then (if x = p then 1 else 2) else (if x = B then 3 else 4)

/-- A collision's hash equation, read as an equation of `bundleHashV35`. Stated separately so that
elaboration does not unfold a concrete stand-in keccak on long byte strings. -/
theorem hashCollision_hashEq_v35 {keccak : List UInt8 → UInt256} {x y : List UInt8}
    (h : HashCollision keccak x y) : bundleHashV35 keccak x = bundleHashV35 keccak y := by
  unfold bundleHashV35
  exact h.2

theorem toyKeccakV35_bundleEncoding (version : UInt8) (c d base oc oa : ℕ) (x : UInt256)
    (tail : List UInt8) : toyKeccakV35 (bundleEncoding version c d base x.val oc oa tail) = x := by
  rw [toyKeccakV35, ite_eq_right (bundleEncoding_length_ne52_v35 _ _ _ _ _ _ _ _), bundleSaltSlot_bundleEncoding,
    fromBytesBE_toBytesBE (uint256_val_lt x), toUInt256_val]

theorem toyKeccakV35_sendMessage (k : List UInt8 → UInt256) (c d base a recipient value : ℕ)
    (s payload : List UInt8) :
    toyKeccakV35 (sendMessageBytesV35 k c d base a recipient value s payload) = k (packedSalt a s) :=
  toyKeccakV35_bundleEncoding ..

theorem toyKeccakV35_packedSalt {a : ℕ} {s : List UInt8} (ha : a < 256 ^ 20)
    (hs : s.length = 32) : toyKeccakV35 (packedSalt a s) = Nat.toUInt256 a := by
  rw [toyKeccakV35, ite_eq_left (packedSalt_length hs), packedSalt,
    List.take_left' (length_toBytesBE 20 a), fromBytesBE_toBytesBE ha]

theorem sourceKeccakV35_bundleEncoding (version : UInt8) {c : ℕ} (hc : c < 256 ^ 32)
    (d base σ oc oa : ℕ) (tail : List UInt8) :
    sourceKeccakV35 (bundleEncoding version c d base σ oc oa tail) = Nat.toUInt256 c := by
  rw [sourceKeccakV35, ite_eq_right (bundleEncoding_length_ne52_v35 _ _ _ _ _ _ _ _),
    bundleSourceSlotV35_bundleEncoding, fromBytesBE_toBytesBE hc]

theorem sourceKeccakV35_sendMessage (k : List UInt8 → UInt256) {c : ℕ} (hc : c < 256 ^ 32)
    (d base a recipient value : ℕ) (s payload : List UInt8) :
    sourceKeccakV35 (sendMessageBytesV35 k c d base a recipient value s payload)
      = Nat.toUInt256 c :=
  sourceKeccakV35_bundleEncoding _ hc ..

theorem senderKeccak_bundleEncoding_v35 (version : UInt8) (c d base σ oc oa : ℕ)
    (tail : List UInt8) : senderKeccak (bundleEncoding version c d base σ oc oa tail) = 0 := by
  rw [senderKeccak, ite_eq_right (bundleEncoding_length_ne52_v35 _ _ _ _ _ _ _ _)]

theorem senderKeccak_sendMessage_v35 (k : List UInt8 → UInt256) (c d base a recipient value : ℕ)
    (s payload : List UInt8) :
    senderKeccak (sendMessageBytesV35 k c d base a recipient value s payload) = 0 :=
  senderKeccak_bundleEncoding_v35 ..

theorem toyKeccakV35_one : toyKeccakV35 (packedSalt 1 (word 0)) = 1 :=
  toyKeccakV35_packedSalt (by norm_num) (word_length 0)

theorem toyKeccakV35_two : toyKeccakV35 (packedSalt 2 (word 0)) = 2 :=
  toyKeccakV35_packedSalt (by norm_num) (word_length 0)

theorem senderKeccak_one_v35 : senderKeccak (packedSalt 1 (word 0)) = 1 :=
  senderKeccak_packedSalt (by norm_num) (word_length 0)

theorem senderKeccak_two_v35 : senderKeccak (packedSalt 2 (word 0)) = 2 :=
  senderKeccak_packedSalt (by norm_num) (word_length 0)

theorem toyKeccakV35_no_salt_collision :
    ¬ HashCollision toyKeccakV35 (packedSalt 1 (word 0)) (packedSalt 2 (word 0)) := by
  rintro ⟨-, h⟩
  rw [toyKeccakV35_one, toyKeccakV35_two] at h
  exact uint256_one_ne_two h

theorem senderKeccak_no_salt_collision_v35 :
    ¬ HashCollision senderKeccak (packedSalt 1 (word 0)) (packedSalt 2 (word 0)) := by
  rintro ⟨-, h⟩
  rw [senderKeccak_one_v35, senderKeccak_two_v35] at h
  exact uint256_one_ne_two h

/-- The two senders' `sendMessage` bytes on chain `324` get bundle hashes `1` and `2` under
`toyKeccakV35`. -/
theorem toyKeccakV35_bundle_hashes_differ :
    bundleHashV35 toyKeccakV35
        (sendMessageBytesV35 toyKeccakV35 324 325 1 1 0x1234 0 (word 0) witnessPayloadV35)
      ≠ bundleHashV35 toyKeccakV35
        (sendMessageBytesV35 toyKeccakV35 324 325 1 2 0x1234 0 (word 0) witnessPayloadV35) := by
  rw [bundleHashV35, bundleHashV35, toyKeccakV35_sendMessage, toyKeccakV35_sendMessage,
    toyKeccakV35_one, toyKeccakV35_two]
  exact uint256_one_ne_two

theorem toyKeccakV35_no_bytes_collision :
    ¬ HashCollision toyKeccakV35
      (sendMessageBytesV35 toyKeccakV35 324 325 1 1 0x1234 0 (word 0) witnessPayloadV35)
      (sendMessageBytesV35 toyKeccakV35 324 325 1 2 0x1234 0 (word 0) witnessPayloadV35) :=
  fun h => toyKeccakV35_bundle_hashes_differ (hashCollision_hashEq_v35 h)

theorem sends_distinct_bundle_hashes_witness_v35 :
    ∃ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B B' : List UInt8),
      a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
      ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
      ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
      ∧ ¬ (a = a' ∧ s = s')
      ∧ B = sendMessageBytesV35 keccak 324 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef]
      ∧ B' = sendMessageBytesV35 keccak 324 325 1 a' 0x1234 0 s' [0xde, 0xad, 0xbe, 0xef]
      ∧ Set.InjOn keccak {B, B'}
      ∧ Set.InjOn keccak {packedSalt a s, packedSalt a' s'}
      ∧ ¬ HashCollision keccak B B'
      ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a' s')
      ∧ bundleHashV35 keccak B ≠ bundleHashV35 keccak B' :=
  ⟨toyKeccakV35, 1, 2, word 0, word 0,
    sendMessageBytesV35 toyKeccakV35 324 325 1 1 0x1234 0 (word 0) witnessPayloadV35,
    sendMessageBytesV35 toyKeccakV35 324 325 1 2 0x1234 0 (word 0) witnessPayloadV35,
    pre_bounds.1, pre_bounds.2.1, pre_bounds.2.2, pre_bounds.2.2,
    sendMessageBytes_salt_v35 .., sendMessageBytes_salt_v35 .., pre_distinct, rfl, rfl,
    (injOn_pair_iff_no_collision _ _ _).mpr toyKeccakV35_no_bytes_collision,
    (injOn_pair_iff_no_collision _ _ _).mpr toyKeccakV35_no_salt_collision,
    toyKeccakV35_no_bytes_collision, toyKeccakV35_no_salt_collision,
    toyKeccakV35_bundle_hashes_differ⟩

theorem sends_across_chains_witness_v35 :
    ∃ (keccak : List UInt8 → UInt256) (c c' a : ℕ) (s B B' : List UInt8),
      c < 256 ^ 32 ∧ c' < 256 ^ 32 ∧ a < 256 ^ 20 ∧ s.length = 32
      ∧ bundleSourceSlotV35 B = word c ∧ bundleSourceSlotV35 B' = word c'
      ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
      ∧ bundleSaltSlot B' = word (keccak (packedSalt a s)).val
      ∧ c ≠ c'
      ∧ B = sendMessageBytesV35 keccak c 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef]
      ∧ B' = sendMessageBytesV35 keccak c' 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef]
      ∧ ¬ HashCollision keccak B B'
      ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a s)
      ∧ bundleHashV35 keccak B ≠ bundleHashV35 keccak B' := by
  -- one sender and one salt on chains 324 and 326: the bundle hashes are the two chain ids
  have hne : bundleHashV35 sourceKeccakV35
        (sendMessageBytesV35 sourceKeccakV35 324 325 1 1 0x1234 0 (word 0) witnessPayloadV35)
      ≠ bundleHashV35 sourceKeccakV35
        (sendMessageBytesV35 sourceKeccakV35 326 325 1 1 0x1234 0 (word 0) witnessPayloadV35) := by
    rw [bundleHashV35, bundleHashV35, sourceKeccakV35_sendMessage _ (by norm_num),
      sourceKeccakV35_sendMessage _ (by norm_num)]
    decide
  exact ⟨sourceKeccakV35, 324, 326, 1, word 0,
    sendMessageBytesV35 sourceKeccakV35 324 325 1 1 0x1234 0 (word 0) witnessPayloadV35,
    sendMessageBytesV35 sourceKeccakV35 326 325 1 1 0x1234 0 (word 0) witnessPayloadV35,
    by norm_num, by norm_num, pre_bounds.1, pre_bounds.2.2,
    sendMessageBytes_source_v35 .., sendMessageBytes_source_v35 ..,
    sendMessageBytes_salt_v35 .., sendMessageBytes_salt_v35 .., by norm_num, rfl, rfl,
    fun h => hne (hashCollision_hashEq_v35 h), fun h => h.1 rfl, hne⟩

theorem sendMessages_witness_v35 :
    ∃ (keccak : List UInt8 → UInt256) (c a a' : ℕ) (s s' : List UInt8),
      c < 256 ^ 32 ∧ a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
      ∧ ¬ (c = c ∧ a = a' ∧ s = s')
      ∧ Set.InjOn keccak {sendMessageBytesV35 keccak c 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef],
          sendMessageBytesV35 keccak c 325 1 a' 0x1234 0 s' [0xde, 0xad, 0xbe, 0xef]}
      ∧ ¬ HashCollision keccak
          (sendMessageBytesV35 keccak c 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef])
          (sendMessageBytesV35 keccak c 325 1 a' 0x1234 0 s' [0xde, 0xad, 0xbe, 0xef])
      ∧ bundleHashV35 keccak
          (sendMessageBytesV35 keccak c 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef])
        ≠ bundleHashV35 keccak
          (sendMessageBytesV35 keccak c 325 1 a' 0x1234 0 s' [0xde, 0xad, 0xbe, 0xef]) :=
  ⟨toyKeccakV35, 324, 1, 2, word 0, word 0, by norm_num, pre_bounds.1, pre_bounds.2.1,
    pre_bounds.2.2, pre_bounds.2.2, fun h => pre_distinct h.2,
    (injOn_pair_iff_no_collision _ _ _).mpr toyKeccakV35_no_bytes_collision,
    toyKeccakV35_no_bytes_collision, toyKeccakV35_bundle_hashes_differ⟩

/-- The keccak of `SendsCollisionNotTautologyV35`: it gives the first send's packed preimage `1`,
and the first send's bytes (built with any keccak that does so) `3`. -/
def notTautologyKeccakV35 (c a : ℕ) (s : List UInt8) : List UInt8 → UInt256 :=
  separatingKeccakV35 (packedSalt a s)
    (sendMessageBytesV35 (separatingKeccakV35 (packedSalt a s) []) c 325 1 a 0x1234 0 s
      witnessPayloadV35)

theorem sends_collision_not_tautology_v35 {c c' a a' : ℕ} {s s' : List UInt8}
    (hs : s.length = 32) (hs' : s'.length = 32) :
    ∃ keccak : List UInt8 → UInt256,
      ¬ HashCollision keccak
          (sendMessageBytesV35 keccak c 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef])
          (sendMessageBytesV35 keccak c' 325 1 a' 0x1234 0 s' [0xde, 0xad, 0xbe, 0xef])
      ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a' s') := by
  classical
  set k₀ : List UInt8 → UInt256 := separatingKeccakV35 (packedSalt a s) [] with hk₀
  set B₀ := sendMessageBytesV35 k₀ c 325 1 a 0x1234 0 s witnessPayloadV35 with hB₀
  set keccak : List UInt8 → UInt256 := separatingKeccakV35 (packedSalt a s) B₀ with hkeccak
  -- on 52-byte inputs `keccak` and `k₀` agree
  have hk52 : ∀ x : List UInt8, x.length = 52 → keccak x = k₀ x := by
    intro x hx
    simp only [hkeccak, hk₀, separatingKeccakV35, ite_eq_left hx]
  have hB : sendMessageBytesV35 keccak c 325 1 a 0x1234 0 s witnessPayloadV35 = B₀ :=
    sendMessageBytes_congr_v35 (hk52 _ (packedSalt_length hs)) ..
  refine ⟨keccak, ?_, ?_⟩
  · rintro ⟨hne, heq⟩
    rw [hB] at hne heq
    have h3 : keccak B₀ = 3 := by
      rw [hkeccak, separatingKeccakV35, ite_eq_right (sendMessageBytes_length_ne52_v35 _ _ _ _ _ _ _ _ _),
        ite_eq_left rfl]
    have h4 : keccak (sendMessageBytesV35 keccak c' 325 1 a' 0x1234 0 s' witnessPayloadV35) = 4 := by
      rw [hkeccak, separatingKeccakV35, ite_eq_right (sendMessageBytes_length_ne52_v35 _ _ _ _ _ _ _ _ _),
        ite_eq_right (Ne.symm hne)]
    rw [h3, h4] at heq
    exact absurd heq (by decide)
  · rintro ⟨hne, heq⟩
    rw [hk52 _ (packedSalt_length hs), hk52 _ (packedSalt_length hs')] at heq
    rw [hk₀, separatingKeccakV35, separatingKeccakV35, ite_eq_left (packedSalt_length hs), ite_eq_left rfl,
      ite_eq_left (packedSalt_length hs'), ite_eq_right (Ne.symm hne)] at heq
    exact absurd heq (by decide)

theorem salt_collision_disjunct_needed_v35 :
    ∃ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B B' : List UInt8),
      a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
      ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
      ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
      ∧ ¬ (a = a' ∧ s = s')
      ∧ B = noCallBytesV35 keccak 324 325 1 a s (formatEvmV1V35 324 7)
      ∧ B' = noCallBytesV35 keccak 324 325 1 a' s' (formatEvmV1V35 324 7)
      ∧ bundleHashV35 keccak B = bundleHashV35 keccak B'
      ∧ ¬ HashCollision keccak B B'
      ∧ HashCollision keccak (packedSalt a s) (packedSalt a' s') := by
  -- every input hashes to `0`; both senders set unbundler `formatEvmV1(324, 7)` and send no call,
  -- so the two byte strings are the same
  have hBB : noCallBytesV35 (fun _ => 0) 324 325 1 1 (word 0) (formatEvmV1V35 324 7)
      = noCallBytesV35 (fun _ => 0) 324 325 1 2 (word 0) (formatEvmV1V35 324 7) := rfl
  exact ⟨fun _ => 0, 1, 2, word 0, word 0,
    noCallBytesV35 (fun _ => 0) 324 325 1 1 (word 0) (formatEvmV1V35 324 7),
    noCallBytesV35 (fun _ => 0) 324 325 1 2 (word 0) (formatEvmV1V35 324 7),
    pre_bounds.1, pre_bounds.2.1, pre_bounds.2.2, pre_bounds.2.2,
    bundleSaltSlot_bundleEncoding .., bundleSaltSlot_bundleEncoding .., pre_distinct, rfl, rfl,
    by rw [hBB], fun h => h.1 hBB, pre₁_ne_pre₂, rfl⟩

theorem preimage_collision_disjunct_needed_v35 :
    ∃ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B B' : List UInt8),
      a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
      ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
      ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
      ∧ ¬ (a = a' ∧ s = s')
      ∧ B = sendMessageBytesV35 keccak 324 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef]
      ∧ B' = sendMessageBytesV35 keccak 324 325 1 a' 0x1234 0 s' [0xde, 0xad, 0xbe, 0xef]
      ∧ bundleHashV35 keccak B = bundleHashV35 keccak B'
      ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a' s')
      ∧ HashCollision keccak B B' := by
  have hBB : sendMessageBytesV35 senderKeccak 324 325 1 1 0x1234 0 (word 0) witnessPayloadV35
      ≠ sendMessageBytesV35 senderKeccak 324 325 1 2 0x1234 0 (word 0) witnessPayloadV35 := by
    intro h
    have h2 := (sendMessageBytes_determine_v35 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (word_length 0) (word_length 0) h).2.1
    omega
  refine ⟨senderKeccak, 1, 2, word 0, word 0,
    sendMessageBytesV35 senderKeccak 324 325 1 1 0x1234 0 (word 0) witnessPayloadV35,
    sendMessageBytesV35 senderKeccak 324 325 1 2 0x1234 0 (word 0) witnessPayloadV35,
    pre_bounds.1, pre_bounds.2.1, pre_bounds.2.2, pre_bounds.2.2,
    sendMessageBytes_salt_v35 .., sendMessageBytes_salt_v35 .., pre_distinct, rfl, rfl, ?_,
    senderKeccak_no_salt_collision_v35, hBB, ?_⟩
  · rw [bundleHashV35, bundleHashV35, senderKeccak_sendMessage_v35, senderKeccak_sendMessage_v35]
  · rw [senderKeccak_sendMessage_v35, senderKeccak_sendMessage_v35]

theorem across_chains_preimage_disjunct_needed_v35 :
    ∃ (keccak : List UInt8 → UInt256) (c c' a : ℕ) (s B B' : List UInt8),
      c < 256 ^ 32 ∧ c' < 256 ^ 32 ∧ a < 256 ^ 20 ∧ s.length = 32
      ∧ bundleSourceSlotV35 B = word c ∧ bundleSourceSlotV35 B' = word c'
      ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
      ∧ bundleSaltSlot B' = word (keccak (packedSalt a s)).val
      ∧ c ≠ c'
      ∧ B = sendMessageBytesV35 keccak c 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef]
      ∧ B' = sendMessageBytesV35 keccak c' 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef]
      ∧ bundleHashV35 keccak B = bundleHashV35 keccak B'
      ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a s)
      ∧ HashCollision keccak B B' := by
  have hBB : sendMessageBytesV35 senderKeccak 324 325 1 1 0x1234 0 (word 0) witnessPayloadV35
      ≠ sendMessageBytesV35 senderKeccak 326 325 1 1 0x1234 0 (word 0) witnessPayloadV35 := by
    intro h
    have h2 := (sendMessageBytes_determine_v35 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (word_length 0) (word_length 0) h).1
    omega
  refine ⟨senderKeccak, 324, 326, 1, word 0,
    sendMessageBytesV35 senderKeccak 324 325 1 1 0x1234 0 (word 0) witnessPayloadV35,
    sendMessageBytesV35 senderKeccak 326 325 1 1 0x1234 0 (word 0) witnessPayloadV35,
    by norm_num, by norm_num, pre_bounds.1, pre_bounds.2.2,
    sendMessageBytes_source_v35 .., sendMessageBytes_source_v35 ..,
    sendMessageBytes_salt_v35 .., sendMessageBytes_salt_v35 .., by norm_num, rfl, rfl, ?_,
    fun h => h.1 rfl, hBB, ?_⟩
  · rw [bundleHashV35, bundleHashV35, senderKeccak_sendMessage_v35, senderKeccak_sendMessage_v35]
  · rw [senderKeccak_sendMessage_v35, senderKeccak_sendMessage_v35]

theorem source_and_destination_collision_not_tautology_v35 (B x : List UInt8) :
    ∃ keccak : List UInt8 → UInt256, ¬ HashCollision keccak x B := by
  classical
  refine ⟨fun y => if y = x then 1 else 0, ?_⟩
  rintro ⟨hne, h⟩
  have hB : ¬ B = x := fun e => hne e.symm
  beta_reduce at h
  rw [ite_eq_left rfl, ite_eq_right hB] at h
  exact absurd h (by decide)

theorem source_and_destination_collision_needed_v35 :
    ∃ (keccak : List UInt8 → UInt256) (B x : List UInt8),
      B = sendMessageBytesV35 keccak 324 325 1 1 0x1234 0 (word 0) [0xde, 0xad, 0xbe, 0xef]
      ∧ x = sendMessageBytesV35 keccak 324 325 1 2 0x1234 0 (word 0) [0xde, 0xad, 0xbe, 0xef]
      ∧ bundleHashV35 keccak x = bundleHashV35 keccak B ∧ x ≠ B := by
  have hBB : sendMessageBytesV35 senderKeccak 324 325 1 2 0x1234 0 (word 0) witnessPayloadV35
      ≠ sendMessageBytesV35 senderKeccak 324 325 1 1 0x1234 0 (word 0) witnessPayloadV35 := by
    intro h
    have h2 := (sendMessageBytes_determine_v35 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (word_length 0) (word_length 0) h).2.1
    omega
  refine ⟨senderKeccak,
    sendMessageBytesV35 senderKeccak 324 325 1 1 0x1234 0 (word 0) witnessPayloadV35,
    sendMessageBytesV35 senderKeccak 324 325 1 2 0x1234 0 (word 0) witnessPayloadV35,
    rfl, rfl, ?_, hBB⟩
  rw [bundleHashV35, bundleHashV35, senderKeccak_sendMessage_v35, senderKeccak_sendMessage_v35]

theorem pin_relation_witness_v35 :
    ∃ (keccak : List UInt8 → UInt256) (c c' : ℕ) (B B' : List UInt8),
      c < 256 ^ 32 ∧ c' < 256 ^ 32 ∧ c ≠ c'
      ∧ B = sendMessageBytesV35 keccak c 325 1 1 0x1234 0 (word 0) [0xde, 0xad, 0xbe, 0xef]
      ∧ B' = sendMessageBytesV35 keccak c' 325 1 1 0x1234 0 (word 0) [0xde, 0xad, 0xbe, 0xef]
      ∧ B.length % 32 = 0 ∧ B'.length % 32 = 0
      ∧ bundleSourceSlotV35 B = word c ∧ bundleSourceSlotV35 B' = word c'
      ∧ pinPreimageV35 c B ≠ pinPreimageV35 c' B' ∧ B ≠ B' := by
  have hc : (324 : ℕ) < 256 ^ 32 := by norm_num
  have hc' : (326 : ℕ) < 256 ^ 32 := by norm_num
  refine ⟨senderKeccak, 324, 326,
    sendMessageBytesV35 senderKeccak 324 325 1 1 0x1234 0 (word 0) witnessPayloadV35,
    sendMessageBytesV35 senderKeccak 326 325 1 1 0x1234 0 (word 0) witnessPayloadV35,
    hc, hc', by norm_num, rfl, rfl,
    sendMessageBytes_length_mod32_v35 _ _ _ _ _ _ _ _ (word_length 0),
    sendMessageBytes_length_mod32_v35 _ _ _ _ _ _ _ _ (word_length 0),
    sendMessageBytes_source_v35 .., sendMessageBytes_source_v35 .., ?_, ?_⟩
  · intro h
    have := chain_eq_of_abiEncode_eq hc hc' h
    omega
  · intro h
    have := (sendMessageBytes_determine_v35 hc hc' (by norm_num) (by norm_num) (word_length 0)
      (word_length 0) h).1
    omega

theorem pin_separates_unsourced_bytes_v35 :
    ∃ (keccak : List UInt8 → UInt256) (c c' : ℕ) (B : List UInt8),
      c < 256 ^ 32 ∧ c' < 256 ^ 32 ∧ c ≠ c'
      ∧ B = sendMessageBytesV35 keccak c 325 1 1 0x1234 0 (word 0) [0xde, 0xad, 0xbe, 0xef]
      ∧ bundleSourceSlotV35 B ≠ word c'
      ∧ pinPreimageV35 c B ≠ pinPreimageV35 c' B := by
  have hc : (324 : ℕ) < 256 ^ 32 := by norm_num
  have hc' : (326 : ℕ) < 256 ^ 32 := by norm_num
  refine ⟨senderKeccak, 324, 326,
    sendMessageBytesV35 senderKeccak 324 325 1 1 0x1234 0 (word 0) witnessPayloadV35,
    hc, hc', by norm_num, rfl, ?_, ?_⟩
  · rw [sendMessageBytes_source_v35]
    intro h
    have := word_inj_of_lt_v35 hc hc' h
    omega
  · intro h
    have := chain_eq_of_abiEncode_eq hc hc' h
    omega

end AttackVectors.BundleHashEncoding.AtV35

/-! ## Certificates -/

namespace AttackVectors.BundleHashEncoding.AtV35

open AttackVectors.BundleHashEncoding

theorem PreimageCarriesSourceDestinationSaltV35 :
    Properties.PreimageCarriesSourceDestinationSaltV35 :=
  fun v src dst base salt oc oa tail =>
    ⟨bundleSourceSlotV35_bundleEncoding v src dst base salt oc oa tail,
      bundleDestSlotV35_bundleEncoding v src dst base salt oc oa tail,
      bundleSaltSlot_bundleEncoding v src dst base salt oc oa tail⟩

theorem ToChainReferenceMinimalBytesV35 : Properties.ToChainReferenceMinimalBytesV35 :=
  ⟨fun _ hc => toChainReferenceV35_minimal hc, toChainReferenceV35_324, toChainReferenceV35_326⟩

theorem SendMessageBytesMatchAbiEncoderV35 : Properties.SendMessageBytesMatchAbiEncoderV35 :=
  ⟨sendMessageBytes_matches_abi_encoder_v35, noCallBytes_matches_abi_encoder_v35,
    sendMessageBytes_matches_abi_encoder_wide_v35⟩

theorem SendMessageBytesSlotsV35 : Properties.SendMessageBytesSlotsV35 :=
  fun keccak c d base a recipient value _ payload hs =>
    ⟨sendMessageBytes_source_v35 .., sendMessageBytes_dest_v35 .., sendMessageBytes_salt_v35 ..,
      sendMessageBytes_length_mod32_v35 keccak c d base a recipient value payload hs⟩

theorem SendsDistinctBundleHashesOrKeccakCollisionV35 :
    Properties.SendsDistinctBundleHashesOrKeccakCollisionV35 :=
  fun keccak _ _ _ _ _ _ ha ha' hs hs' hB hB' hne =>
    sends_distinct_bundle_hashes_or_keccak_collision_v35 keccak ha ha' hs hs' hB hB' hne

theorem SendsDistinctBundleHashesOnV35 : Properties.SendsDistinctBundleHashesOnV35 :=
  fun keccak _ _ _ _ _ _ ha ha' hs hs' hB hB' hne hbytes hsalt =>
    sends_distinct_bundle_hashes_on_v35 keccak ha ha' hs hs' hB hB' hne hbytes hsalt

theorem SendsDistinctBundleHashesAcrossChainsOrKeccakCollisionV35 :
    Properties.SendsDistinctBundleHashesAcrossChainsOrKeccakCollisionV35 :=
  fun keccak _ _ _ _ _ _ _ _ hc hc' ha ha' hs hs' hsrc hsrc' hB hB' hne =>
    sends_distinct_bundle_hashes_across_chains_or_keccak_collision_v35 keccak hc hc' ha ha' hs hs'
      hsrc hsrc' hB hB' hne

theorem SourceAndDestinationAgreeOrCollisionV35 :
    Properties.SourceAndDestinationAgreeOrCollisionV35 :=
  source_and_destination_agree_or_collision_v35

theorem SendMessageBytesDetermineChainSenderSaltV35 :
    Properties.SendMessageBytesDetermineChainSenderSaltV35 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hc' ha ha' hs hs' h =>
    sendMessageBytes_determine_v35 hc hc' ha ha' hs hs' h

theorem SendMessagesDistinctBundleHashesOrBytesCollisionV35 :
    Properties.SendMessagesDistinctBundleHashesOrBytesCollisionV35 :=
  fun keccak _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hc' ha ha' hs hs' hne =>
    sendMessages_distinct_bundle_hashes_or_bytes_collision_v35 keccak hc hc' ha ha' hs hs' hne

theorem SendMessagesDistinctBundleHashesOnV35 :
    Properties.SendMessagesDistinctBundleHashesOnV35 :=
  fun keccak _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hc' ha ha' hs hs' hne hinj =>
    sendMessages_distinct_bundle_hashes_on_v35 keccak hc hc' ha ha' hs hs' hne hinj

theorem PinPreimageDropsToV35PreimageV35 : Properties.PinPreimageDropsToV35PreimageV35 :=
  fun c _ h => pin_preimage_drops_to_v35_preimage c h

theorem PinAndV35PreimagesCoincideOnSourcedBytesV35 :
    Properties.PinAndV35PreimagesCoincideOnSourcedBytesV35 :=
  fun _ _ _ _ hc hc' hsrc hsrc' => pin_and_v35_preimages_coincide hc hc' hsrc hsrc'

theorem SendsDistinctBundleHashesWitnessV35 : Properties.SendsDistinctBundleHashesWitnessV35 :=
  sends_distinct_bundle_hashes_witness_v35

theorem SendsAcrossChainsWitnessV35 : Properties.SendsAcrossChainsWitnessV35 :=
  sends_across_chains_witness_v35

theorem SendMessagesWitnessV35 : Properties.SendMessagesWitnessV35 :=
  sendMessages_witness_v35

theorem SendsCollisionNotTautologyV35 : Properties.SendsCollisionNotTautologyV35 :=
  fun _ _ _ _ _ _ _ _ _ _ hs hs' _ => sends_collision_not_tautology_v35 hs hs'

theorem SaltCollisionDisjunctNeededV35 : Properties.SaltCollisionDisjunctNeededV35 :=
  salt_collision_disjunct_needed_v35

theorem PreimageCollisionDisjunctNeededV35 : Properties.PreimageCollisionDisjunctNeededV35 :=
  preimage_collision_disjunct_needed_v35

theorem AcrossChainsPreimageDisjunctNeededV35 :
    Properties.AcrossChainsPreimageDisjunctNeededV35 :=
  across_chains_preimage_disjunct_needed_v35

theorem SourceAndDestinationCollisionNotTautologyV35 :
    Properties.SourceAndDestinationCollisionNotTautologyV35 :=
  source_and_destination_collision_not_tautology_v35

theorem SourceAndDestinationCollisionNeededV35 :
    Properties.SourceAndDestinationCollisionNeededV35 :=
  source_and_destination_collision_needed_v35

theorem PinRelationWitnessV35 : Properties.PinRelationWitnessV35 :=
  pin_relation_witness_v35

theorem PinSeparatesUnsourcedBytesV35 : Properties.PinSeparatesUnsourcedBytesV35 :=
  pin_separates_unsourced_bytes_v35

end AttackVectors.BundleHashEncoding.AtV35
