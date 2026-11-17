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

The pin relation uses `abiEncode_right_inj` (`InteropCenter/Proofs/Dispatch.lean`) in one direction
and the source slot in the other.
-/

namespace AttackVectors.BundleHashEncoding.AtV35

open AttackVectors.BundleHashEncoding

/-! ## Byte-level facts -/

theorem bundleEncoding_split_v35 (version : UInt8) (src dst base salt oc oa : ℕ)
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

theorem bundleSourceSlot_bundleEncoding (version : UInt8) (src dst base salt oc oa : ℕ)
    (tail : List UInt8) :
    bundleSourceSlot (bundleEncoding version src dst base salt oc oa tail) = word src := by
  have hpre : (word 0x20 ++ bytes1Word version).length = 64 := by
    simp [bytes1Word, length_toBytesBE]
  rw [bundleSourceSlot, bundleEncoding_split_v35, List.drop_left' hpre]
  exact List.take_left' (word_length src)

theorem bundleDestSlot_bundleEncoding (version : UInt8) (src dst base salt oc oa : ℕ)
    (tail : List UInt8) :
    bundleDestSlot (bundleEncoding version src dst base salt oc oa tail) = word dst := by
  have hpre : (word 0x20 ++ bytes1Word version ++ word src).length = 96 := by
    simp [bytes1Word, length_toBytesBE]
  rw [bundleDestSlot, bundleEncoding_split_dst_v35, List.drop_left' hpre]
  exact List.take_left' (word_length dst)

/-- A word below `2^256` is recovered from its bytes. -/
theorem word_inj_of_lt {c c' : ℕ} (hc : c < 256 ^ 32) (hc' : c' < 256 ^ 32)
    (h : word c = word c') : c = c' := by
  have h2 := congrArg fromBytesBE h
  rwa [fromBytesBE_toBytesBE hc, fromBytesBE_toBytesBE hc'] at h2

theorem pad32_of_mod32 {B : List UInt8} (h : B.length % 32 = 0) : pad32 B = B := by
  simp [pad32, h]

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
    (hsrc : bundleSourceSlot B = word c) (hsrc' : bundleSourceSlot B' = word c')
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
      exact word_inj_of_lt hc hc' hsrc'
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

/-! ## The pin relation -/

theorem pin_preimage_drops_to_v35_preimage (c : ℕ) {B : List UInt8} (h : B.length % 32 = 0) :
    (pinPreimage c B).drop 96 = B := by
  rw [pinPreimage, abiEncode_drop96, pad32_of_mod32 h]

theorem pin_and_v35_preimages_coincide {c c' : ℕ} {B B' : List UInt8}
    (hc : c < 256 ^ 32) (hc' : c' < 256 ^ 32)
    (hsrc : bundleSourceSlot B = word c) (hsrc' : bundleSourceSlot B' = word c') :
    pinPreimage c B = pinPreimage c' B' ↔ B = B' := by
  constructor
  · intro h
    exact Contracts.InteropCenter.abiEncode_right_inj h
  · intro hBB
    have hcc : c = c' := by
      rw [← hBB, hsrc] at hsrc'
      exact word_inj_of_lt hc hc' hsrc'
    rw [hcc, hBB]

/-! ## Witnesses and countermodels

Senders `1` and `2` with the zero user salt, on chain `324` (and `326` for the cross-chain cases).
The bundle bytes are `bundleEncoding` layouts with version `0x01` (`Messaging.sol:6`), destination
`325`, base-token asset id `1`, the canonical offsets of a bundle with no calls, and the canonical
attribute tail whose unbundler is the sender's default `formatEvmV1(chainid, sender)`. -/

/-- The witnesses' bundle bytes from source chain `c`, with derived salt word `σ` and unbundler `u`. -/
def witnessBundleV35 (c σ : ℕ) (u : List UInt8) : List UInt8 :=
  bundleEncoding 1 c 325 1 σ 224 256 (bundleTailV35 u 0)

/-- A stand-in for keccak, used only in witnesses. On a 52-byte input (a packed salt preimage) it
returns the sender; on anything else (bundle bytes) it returns the salt word in the salt slot. -/
def toyKeccakV35 (x : List UInt8) : UInt256 :=
  if x.length = 52 then Nat.toUInt256 (fromBytesBE (x.take 20))
  else Nat.toUInt256 (fromBytesBE (bundleSaltSlot x))

/-- A stand-in that separates packed preimages by sender and bundle bytes by their source slot. -/
def sourceKeccakV35 (x : List UInt8) : UInt256 :=
  if x.length = 52 then Nat.toUInt256 (fromBytesBE (x.take 20))
  else Nat.toUInt256 (fromBytesBE (bundleSourceSlot x))

/-- A collision's hash equation, read as an equation of `bundleHashV35`. Stated separately so that
elaboration does not unfold a concrete stand-in keccak on long byte strings. -/
theorem HashCollision.hashEq {keccak : List UInt8 → UInt256} {x y : List UInt8}
    (h : HashCollision keccak x y) : bundleHashV35 keccak x = bundleHashV35 keccak y := by
  unfold bundleHashV35
  exact h.2

theorem witnessBundleV35_length_ne (c σ : ℕ) (u : List UInt8) :
    (witnessBundleV35 c σ u).length ≠ 52 := by
  have := bundleEncoding_length 1 c 325 1 σ 224 256 (bundleTailV35 u 0)
  unfold witnessBundleV35
  omega

theorem slot_witnessBundleV35 (c : ℕ) (x : UInt256) (u : List UInt8) :
    bundleSaltSlot (witnessBundleV35 c x.val u) = word x.val :=
  bundleSaltSlot_bundleEncoding ..

theorem source_witnessBundleV35 (c σ : ℕ) (u : List UInt8) :
    bundleSourceSlot (witnessBundleV35 c σ u) = word c :=
  bundleSourceSlot_bundleEncoding ..

theorem toyKeccakV35_witnessBundle (c : ℕ) (x : UInt256) (u : List UInt8) :
    toyKeccakV35 (witnessBundleV35 c x.val u) = x := by
  rw [toyKeccakV35, ite_eq_right (witnessBundleV35_length_ne c _ u), slot_witnessBundleV35,
    fromBytesBE_toBytesBE (uint256_val_lt x), toUInt256_val]

theorem toyKeccakV35_packedSalt {a : ℕ} {s : List UInt8} (ha : a < 256 ^ 20)
    (hs : s.length = 32) : toyKeccakV35 (packedSalt a s) = Nat.toUInt256 a := by
  rw [toyKeccakV35, ite_eq_left (packedSalt_length hs), packedSalt,
    List.take_left' (length_toBytesBE 20 a), fromBytesBE_toBytesBE ha]

theorem sourceKeccakV35_witnessBundle {c : ℕ} (hc : c < 256 ^ 32) (σ : ℕ) (u : List UInt8) :
    sourceKeccakV35 (witnessBundleV35 c σ u) = Nat.toUInt256 c := by
  rw [sourceKeccakV35, ite_eq_right (witnessBundleV35_length_ne c σ u), source_witnessBundleV35,
    fromBytesBE_toBytesBE hc]

theorem sourceKeccakV35_packedSalt {a : ℕ} {s : List UInt8} (ha : a < 256 ^ 20)
    (hs : s.length = 32) : sourceKeccakV35 (packedSalt a s) = Nat.toUInt256 a := by
  rw [sourceKeccakV35, ite_eq_left (packedSalt_length hs), packedSalt,
    List.take_left' (length_toBytesBE 20 a), fromBytesBE_toBytesBE ha]

theorem senderKeccak_witnessBundleV35 (c σ : ℕ) (u : List UInt8) :
    senderKeccak (witnessBundleV35 c σ u) = 0 := by
  rw [senderKeccak, ite_eq_right (witnessBundleV35_length_ne c σ u)]

theorem toyKeccakV35_pre₁ : toyKeccakV35 pre₁ = 1 :=
  toyKeccakV35_packedSalt (by norm_num) (word_length 0)

theorem toyKeccakV35_pre₂ : toyKeccakV35 pre₂ = 2 :=
  toyKeccakV35_packedSalt (by norm_num) (word_length 0)

theorem toyKeccakV35_no_salt_collision : ¬ HashCollision toyKeccakV35 pre₁ pre₂ := by
  rintro ⟨-, h⟩
  rw [toyKeccakV35_pre₁, toyKeccakV35_pre₂] at h
  exact uint256_one_ne_two h

/-- The two witness bundles on chain `324` get bundle hashes `1` and `2` under `toyKeccakV35`. -/
theorem toyKeccakV35_bundle_hashes_differ :
    bundleHashV35 toyKeccakV35
        (witnessBundleV35 324 (toyKeccakV35 pre₁).val (formatEvmV1 chainRef324 1))
      ≠ bundleHashV35 toyKeccakV35
        (witnessBundleV35 324 (toyKeccakV35 pre₂).val (formatEvmV1 chainRef324 2)) := by
  rw [bundleHashV35, bundleHashV35, toyKeccakV35_witnessBundle, toyKeccakV35_witnessBundle,
    toyKeccakV35_pre₁, toyKeccakV35_pre₂]
  exact uint256_one_ne_two

theorem sends_distinct_bundle_hashes_witness_v35 :
    ∃ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B B' : List UInt8),
      a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
      ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
      ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
      ∧ ¬ (a = a' ∧ s = s')
      ∧ B = bundleEncoding 1 324 325 1 (keccak (packedSalt a s)).val 224 256
          (bundleTailV35 (formatEvmV1 chainRef324 a) 0)
      ∧ B' = bundleEncoding 1 324 325 1 (keccak (packedSalt a' s')).val 224 256
          (bundleTailV35 (formatEvmV1 chainRef324 a') 0)
      ∧ Set.InjOn keccak {B, B'}
      ∧ Set.InjOn keccak {packedSalt a s, packedSalt a' s'}
      ∧ ¬ HashCollision keccak B B'
      ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a' s')
      ∧ bundleHashV35 keccak B ≠ bundleHashV35 keccak B' := by
  have hbytes : ¬ HashCollision toyKeccakV35
      (witnessBundleV35 324 (toyKeccakV35 pre₁).val (formatEvmV1 chainRef324 1))
      (witnessBundleV35 324 (toyKeccakV35 pre₂).val (formatEvmV1 chainRef324 2)) :=
    fun h => toyKeccakV35_bundle_hashes_differ h.hashEq
  exact ⟨toyKeccakV35, 1, 2, word 0, word 0,
    witnessBundleV35 324 (toyKeccakV35 pre₁).val (formatEvmV1 chainRef324 1),
    witnessBundleV35 324 (toyKeccakV35 pre₂).val (formatEvmV1 chainRef324 2),
    pre_bounds.1, pre_bounds.2.1, pre_bounds.2.2, pre_bounds.2.2,
    slot_witnessBundleV35 _ _ _, slot_witnessBundleV35 _ _ _, pre_distinct, rfl, rfl,
    (injOn_pair_iff_no_collision _ _ _).mpr hbytes,
    (injOn_pair_iff_no_collision _ _ _).mpr toyKeccakV35_no_salt_collision,
    hbytes, toyKeccakV35_no_salt_collision, toyKeccakV35_bundle_hashes_differ⟩

theorem sends_across_chains_witness_v35 :
    ∃ (keccak : List UInt8 → UInt256) (c c' a : ℕ) (s B B' : List UInt8),
      c < 256 ^ 32 ∧ c' < 256 ^ 32 ∧ a < 256 ^ 20 ∧ s.length = 32
      ∧ bundleSourceSlot B = word c ∧ bundleSourceSlot B' = word c'
      ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
      ∧ bundleSaltSlot B' = word (keccak (packedSalt a s)).val
      ∧ c ≠ c'
      ∧ B = bundleEncoding 1 c 325 1 (keccak (packedSalt a s)).val 224 256
          (bundleTailV35 (formatEvmV1 chainRef324 a) 0)
      ∧ B' = bundleEncoding 1 c' 325 1 (keccak (packedSalt a s)).val 224 256
          (bundleTailV35 (formatEvmV1 chainRef326 a) 0)
      ∧ ¬ HashCollision keccak B B'
      ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a s)
      ∧ bundleHashV35 keccak B ≠ bundleHashV35 keccak B' := by
  -- one sender and one salt on chains 324 and 326: the bundle hashes are the two chain ids
  have hne : bundleHashV35 sourceKeccakV35
        (witnessBundleV35 324 (sourceKeccakV35 pre₁).val (formatEvmV1 chainRef324 1))
      ≠ bundleHashV35 sourceKeccakV35
        (witnessBundleV35 326 (sourceKeccakV35 pre₁).val (formatEvmV1 chainRef326 1)) := by
    rw [bundleHashV35, bundleHashV35, sourceKeccakV35_witnessBundle (by norm_num),
      sourceKeccakV35_witnessBundle (by norm_num)]
    decide
  exact ⟨sourceKeccakV35, 324, 326, 1, word 0,
    witnessBundleV35 324 (sourceKeccakV35 pre₁).val (formatEvmV1 chainRef324 1),
    witnessBundleV35 326 (sourceKeccakV35 pre₁).val (formatEvmV1 chainRef326 1),
    by norm_num, by norm_num, pre_bounds.1, pre_bounds.2.2,
    source_witnessBundleV35 _ _ _, source_witnessBundleV35 _ _ _,
    slot_witnessBundleV35 _ _ _, slot_witnessBundleV35 _ _ _, by norm_num, rfl, rfl,
    fun h => hne h.hashEq, fun h => h.1 rfl, hne⟩

theorem salt_collision_disjunct_needed_v35 :
    ∃ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B B' : List UInt8),
      a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
      ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
      ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
      ∧ ¬ (a = a' ∧ s = s')
      ∧ bundleHashV35 keccak B = bundleHashV35 keccak B'
      ∧ ¬ HashCollision keccak B B'
      ∧ HashCollision keccak (packedSalt a s) (packedSalt a' s') :=
  -- every input hashes to `0`; both senders set unbundler `7` explicitly, so the bytes coincide
  ⟨fun _ => 0, 1, 2, word 0, word 0,
    witnessBundleV35 324 (0 : UInt256).val (formatEvmV1 chainRef324 7),
    witnessBundleV35 324 (0 : UInt256).val (formatEvmV1 chainRef324 7),
    pre_bounds.1, pre_bounds.2.1, pre_bounds.2.2, pre_bounds.2.2,
    slot_witnessBundleV35 _ _ _, slot_witnessBundleV35 _ _ _, pre_distinct, rfl,
    fun h => h.1 rfl, pre₁_ne_pre₂, rfl⟩

theorem preimage_collision_disjunct_needed_v35 :
    ∃ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B B' : List UInt8),
      a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
      ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
      ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
      ∧ ¬ (a = a' ∧ s = s')
      ∧ bundleHashV35 keccak B = bundleHashV35 keccak B'
      ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a' s')
      ∧ HashCollision keccak B B' := by
  have h1 : senderKeccak pre₁ = 1 := senderKeccak_packedSalt (by norm_num) (word_length 0)
  have h2 : senderKeccak pre₂ = 2 := senderKeccak_packedSalt (by norm_num) (word_length 0)
  have hsalt : ¬ HashCollision senderKeccak pre₁ pre₂ := by
    rintro ⟨-, h⟩
    rw [h1, h2] at h
    exact uint256_one_ne_two h
  have hBB : witnessBundleV35 324 (senderKeccak pre₁).val (formatEvmV1 chainRef324 1)
      ≠ witnessBundleV35 324 (senderKeccak pre₂).val (formatEvmV1 chainRef324 2) := by
    intro h
    have := congrArg bundleSaltSlot h
    rw [slot_witnessBundleV35, slot_witnessBundleV35] at this
    exact uint256_one_ne_two (by rw [← h1, ← h2]; exact word_val_inj this)
  refine ⟨senderKeccak, 1, 2, word 0, word 0,
    witnessBundleV35 324 (senderKeccak pre₁).val (formatEvmV1 chainRef324 1),
    witnessBundleV35 324 (senderKeccak pre₂).val (formatEvmV1 chainRef324 2),
    pre_bounds.1, pre_bounds.2.1, pre_bounds.2.2, pre_bounds.2.2,
    slot_witnessBundleV35 _ _ _, slot_witnessBundleV35 _ _ _, pre_distinct, ?_, hsalt, hBB, ?_⟩
  · rw [bundleHashV35, bundleHashV35, senderKeccak_witnessBundleV35, senderKeccak_witnessBundleV35]
  · rw [senderKeccak_witnessBundleV35, senderKeccak_witnessBundleV35]

theorem across_chains_preimage_disjunct_needed_v35 :
    ∃ (keccak : List UInt8 → UInt256) (c c' a : ℕ) (s B B' : List UInt8),
      c < 256 ^ 32 ∧ c' < 256 ^ 32 ∧ a < 256 ^ 20 ∧ s.length = 32
      ∧ bundleSourceSlot B = word c ∧ bundleSourceSlot B' = word c'
      ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
      ∧ bundleSaltSlot B' = word (keccak (packedSalt a s)).val
      ∧ c ≠ c'
      ∧ bundleHashV35 keccak B = bundleHashV35 keccak B'
      ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a s)
      ∧ HashCollision keccak B B' := by
  have hBB : witnessBundleV35 324 (senderKeccak pre₁).val (formatEvmV1 chainRef324 1)
      ≠ witnessBundleV35 326 (senderKeccak pre₁).val (formatEvmV1 chainRef326 1) := by
    intro h
    have := congrArg bundleSourceSlot h
    rw [source_witnessBundleV35, source_witnessBundleV35] at this
    have := word_inj_of_lt (by norm_num) (by norm_num) this
    omega
  refine ⟨senderKeccak, 324, 326, 1, word 0,
    witnessBundleV35 324 (senderKeccak pre₁).val (formatEvmV1 chainRef324 1),
    witnessBundleV35 326 (senderKeccak pre₁).val (formatEvmV1 chainRef326 1),
    by norm_num, by norm_num, pre_bounds.1, pre_bounds.2.2,
    source_witnessBundleV35 _ _ _, source_witnessBundleV35 _ _ _,
    slot_witnessBundleV35 _ _ _, slot_witnessBundleV35 _ _ _, by norm_num, ?_,
    fun h => h.1 rfl, hBB, ?_⟩
  · rw [bundleHashV35, bundleHashV35, senderKeccak_witnessBundleV35, senderKeccak_witnessBundleV35]
  · rw [senderKeccak_witnessBundleV35, senderKeccak_witnessBundleV35]

theorem source_and_destination_collision_not_tautology_v35 (B x : List UInt8) :
    ∃ keccak : List UInt8 → UInt256, ¬ HashCollision keccak x B := by
  classical
  refine ⟨fun y => if y = x then 1 else 0, ?_⟩
  rintro ⟨hne, h⟩
  have h' : (1 : UInt256) = 0 := by
    have hB : ¬ B = x := fun e => hne e.symm
    simp [hB] at h
  exact absurd h' (by decide)

theorem source_and_destination_collision_needed_v35 :
    ∃ (keccak : List UInt8 → UInt256) (B x : List UInt8),
      bundleHashV35 keccak x = bundleHashV35 keccak B ∧ x ≠ B :=
  ⟨fun _ => 0, [], [0], rfl, by simp⟩

end AttackVectors.BundleHashEncoding.AtV35

/-! ## Certificates -/

namespace AttackVectors.BundleHashEncoding.AtV35

open AttackVectors.BundleHashEncoding

theorem PreimageCarriesSourceDestinationSaltV35 :
    Properties.PreimageCarriesSourceDestinationSaltV35 :=
  fun v src dst base salt oc oa tail =>
    ⟨bundleSourceSlot_bundleEncoding v src dst base salt oc oa tail,
      bundleDestSlot_bundleEncoding v src dst base salt oc oa tail,
      bundleSaltSlot_bundleEncoding v src dst base salt oc oa tail⟩

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

theorem PinPreimageDropsToV35PreimageV35 : Properties.PinPreimageDropsToV35PreimageV35 :=
  fun c _ h => pin_preimage_drops_to_v35_preimage c h

theorem PinAndV35PreimagesCoincideOnSourcedBytesV35 :
    Properties.PinAndV35PreimagesCoincideOnSourcedBytesV35 :=
  fun _ _ _ _ hc hc' hsrc hsrc' => pin_and_v35_preimages_coincide hc hc' hsrc hsrc'

theorem SendsDistinctBundleHashesWitnessV35 : Properties.SendsDistinctBundleHashesWitnessV35 :=
  sends_distinct_bundle_hashes_witness_v35

theorem SendsAcrossChainsWitnessV35 : Properties.SendsAcrossChainsWitnessV35 :=
  sends_across_chains_witness_v35

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

end AttackVectors.BundleHashEncoding.AtV35
