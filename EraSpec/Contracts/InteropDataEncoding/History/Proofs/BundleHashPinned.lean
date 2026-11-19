import EraSpec.Contracts.InteropDataEncoding.History.Properties.BundleHashPinned
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashPinned

/-!
# History proofs: the keccak layer of `BundleHashPinned` at the interop pin `c67894b9`

**A record of an older commit, not a claim about era-contracts `b17415d20`.** The salt slot of the
bundle bytes is a fixed slot of the pin's keccak preimage `abi.encode(chainId, B)`
(`preimageSaltSlot_abiEncode`), so equal preimages carry equal salts. Across chains, equal
preimages also have equal leading words, so they name the same chain (`chain_eq_of_abiEncode_eq`).
The witnesses reuse the shared witness bundles of `Proofs/BundleHashPinned.lean`, with a stand-in
keccak `pinToyKeccak` that reads the salt from the pin's preimage.
-/

namespace AttackVectors.BundleHashEncoding.History

/-- **THE PREIMAGE'S SALT SLOT IS THE BUNDLE'S SALT SLOT**, for any bytes with a full slot. -/
theorem preimageSaltSlot_abiEncode (c : ℕ) {B : List UInt8} (hB : 192 ≤ B.length) :
    preimageSaltSlot (abiEncode c B) = bundleSaltSlot B := by
  unfold preimageSaltSlot bundleSaltSlot
  rw [show (256 : ℕ) = 96 + 160 from rfl, ← List.drop_drop, abiEncode_drop96, pad32,
    List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem preimageSaltSlot_bundleEncoding (c : ℕ) (version : UInt8) (src dst base salt oc oa : ℕ)
    (tail : List UInt8) :
    preimageSaltSlot (abiEncode c (bundleEncoding version src dst base salt oc oa tail))
      = word salt := by
  rw [preimageSaltSlot_abiEncode c (le_trans (by norm_num) (bundleEncoding_length ..)),
    bundleSaltSlot_bundleEncoding]

theorem sends_distinct_bundle_hashes_or_keccak_collision (keccak : List UInt8 → UInt256)
    (c c' : ℕ) {a a' : ℕ} {s s' B B' : List UInt8}
    (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20) (hs : s.length = 32) (hs' : s'.length = 32)
    (hB : bundleSaltSlot B = word (keccak (packedSalt a s)).val)
    (hB' : bundleSaltSlot B' = word (keccak (packedSalt a' s')).val)
    (hne : ¬ (a = a' ∧ s = s')) :
    bundleHashOfBytes keccak c B ≠ bundleHashOfBytes keccak c' B'
      ∨ HashCollision keccak (abiEncode c B) (abiEncode c' B')
      ∨ HashCollision keccak (packedSalt a s) (packedSalt a' s') := by
  by_cases hh : bundleHashOfBytes keccak c B = bundleHashOfBytes keccak c' B'
  · by_cases hE : abiEncode c B = abiEncode c' B'
    · refine Or.inr (Or.inr ⟨packedSalt_ne ha ha' hs hs' hne, ?_⟩)
      -- equal preimages carry equal salt slots
      have hslot : bundleSaltSlot B = bundleSaltSlot B' := by
        rw [← preimageSaltSlot_abiEncode c (length_of_saltSlot hB (word_length _)),
          ← preimageSaltSlot_abiEncode c' (length_of_saltSlot hB' (word_length _)), hE]
      rw [hB, hB'] at hslot
      exact word_val_inj hslot
    · exact Or.inr (Or.inl ⟨hE, hh⟩)
  · exact Or.inl hh

theorem sends_distinct_bundle_hashes_on (keccak : List UInt8 → UInt256)
    (c c' : ℕ) {a a' : ℕ} {s s' B B' : List UInt8}
    (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20) (hs : s.length = 32) (hs' : s'.length = 32)
    (hB : bundleSaltSlot B = word (keccak (packedSalt a s)).val)
    (hB' : bundleSaltSlot B' = word (keccak (packedSalt a' s')).val)
    (hne : ¬ (a = a' ∧ s = s'))
    (hpre : Set.InjOn keccak {abiEncode c B, abiEncode c' B'})
    (hsalt : Set.InjOn keccak {packedSalt a s, packedSalt a' s'}) :
    bundleHashOfBytes keccak c B ≠ bundleHashOfBytes keccak c' B' := by
  rcases sends_distinct_bundle_hashes_or_keccak_collision keccak c c' ha ha' hs hs' hB hB' hne
    with h | h | h
  · exact h
  · exact absurd h ((injOn_pair_iff_no_collision _ _ _).mp hpre)
  · exact absurd h ((injOn_pair_iff_no_collision _ _ _).mp hsalt)

theorem sends_distinct_bundle_hashes_across_chains_or_keccak_collision
    (keccak : List UInt8 → UInt256) {c c' a a' : ℕ} {s s' B B' : List UInt8}
    (hc : c < 256 ^ 32) (hc' : c' < 256 ^ 32)
    (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20) (hs : s.length = 32) (hs' : s'.length = 32)
    (hB : bundleSaltSlot B = word (keccak (packedSalt a s)).val)
    (hB' : bundleSaltSlot B' = word (keccak (packedSalt a' s')).val)
    (hne : ¬ (c = c' ∧ a = a' ∧ s = s')) :
    bundleHashOfBytes keccak c B ≠ bundleHashOfBytes keccak c' B'
      ∨ HashCollision keccak (abiEncode c B) (abiEncode c' B')
      ∨ HashCollision keccak (packedSalt a s) (packedSalt a' s') := by
  by_cases hE : abiEncode c B = abiEncode c' B'
  · -- one preimage, so one chain: the `(sender, salt)` pairs differ and the one-chain case applies
    have hcc := chain_eq_of_abiEncode_eq hc hc' hE
    rcases sends_distinct_bundle_hashes_or_keccak_collision keccak c c' ha ha' hs hs' hB hB'
      (fun h => hne ⟨hcc, h⟩) with h | h | h
    · exact Or.inl h
    · exact absurd hE h.1
    · exact Or.inr (Or.inr h)
  · by_cases hh : bundleHashOfBytes keccak c B = bundleHashOfBytes keccak c' B'
    · exact Or.inr (Or.inl ⟨hE, hh⟩)
    · exact Or.inl hh

/-- The pin's stand-in for keccak, used only in witnesses. It is not a hash: it reads back exactly what the
argument compares. On a 52-byte input (a packed salt preimage) it returns the sender, and on
anything else (a bundle-hash preimage) it returns the salt word in the preimage's salt slot. -/
def pinToyKeccak (x : List UInt8) : UInt256 :=
  if x.length = 52 then Nat.toUInt256 (fromBytesBE (x.take 20))
  else Nat.toUInt256 (fromBytesBE (preimageSaltSlot x))

/-- A stand-in that separates packed preimages by sender and bundle-hash preimages by their leading
word, the chain id. -/
def chainKeccak (x : List UInt8) : UInt256 :=
  if x.length = 52 then Nat.toUInt256 (fromBytesBE (x.take 20))
  else Nat.toUInt256 (fromBytesBE (x.take 32))

theorem pinToyKeccak_packedSalt {a : ℕ} {s : List UInt8} (ha : a < 256 ^ 20)
    (hs : s.length = 32) : pinToyKeccak (packedSalt a s) = Nat.toUInt256 a := by
  rw [pinToyKeccak, ite_eq_left (packedSalt_length hs), packedSalt,
    List.take_left' (length_toBytesBE 20 a), fromBytesBE_toBytesBE ha]

theorem pinToyKeccak_pre₁ : pinToyKeccak pre₁ = 1 :=
  pinToyKeccak_packedSalt (by norm_num) (word_length 0)
theorem pinToyKeccak_pre₂ : pinToyKeccak pre₂ = 2 :=
  pinToyKeccak_packedSalt (by norm_num) (word_length 0)

theorem pinToyKeccak_no_salt_collision : ¬ HashCollision pinToyKeccak pre₁ pre₂ := by
  rintro ⟨-, h⟩
  rw [pinToyKeccak_pre₁, pinToyKeccak_pre₂] at h
  exact uint256_one_ne_two h

theorem pinToyKeccak_abiEncode_witnessBundle (c c₀ : ℕ) (x : UInt256) :
    pinToyKeccak (abiEncode c (witnessBundle c₀ x.val)) = x := by
  rw [pinToyKeccak, ite_eq_right (abiEncode_length_ne c _), preimageSaltSlot_abiEncode c
    (witnessBundle_length _ _)]
  exact saltOfBytes_witnessBundle c₀ x

theorem chainKeccak_abiEncode {c : ℕ} (hc : c < 256 ^ 32) (B : List UInt8) :
    chainKeccak (abiEncode c B) = Nat.toUInt256 c := by
  rw [chainKeccak, ite_eq_right (abiEncode_length_ne c _), abiEncode_take32,
    fromBytesBE_toBytesBE hc]

theorem pinToyKeccak_bundle_hashes_differ :
    bundleHashOfBytes pinToyKeccak 324 (witnessBundle 324 (pinToyKeccak pre₁).val)
      ≠ bundleHashOfBytes pinToyKeccak 324 (witnessBundle 324 (pinToyKeccak pre₂).val) := by
  rw [bundleHashOfBytes, bundleHashOfBytes, pinToyKeccak_abiEncode_witnessBundle,
    pinToyKeccak_abiEncode_witnessBundle, pinToyKeccak_pre₁, pinToyKeccak_pre₂]
  exact uint256_one_ne_two

theorem sends_distinct_bundle_hashes_witness :
    ∃ (keccak : List UInt8 → UInt256) (c a a' : ℕ) (s s' B B' : List UInt8),
      a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
      ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
      ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
      ∧ ¬ (a = a' ∧ s = s')
      ∧ (∃ (v : UInt8) (dst base oc oa : ℕ) (tail : List UInt8),
          B = bundleEncoding v c dst base (keccak (packedSalt a s)).val oc oa tail
          ∧ B' = bundleEncoding v c dst base (keccak (packedSalt a' s')).val oc oa tail)
      ∧ Set.InjOn keccak {abiEncode c B, abiEncode c B'}
      ∧ Set.InjOn keccak {packedSalt a s, packedSalt a' s'}
      ∧ ¬ HashCollision keccak (abiEncode c B) (abiEncode c B')
      ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a' s')
      ∧ bundleHashOfBytes keccak c B ≠ bundleHashOfBytes keccak c B' := by
  have hpre : ¬ HashCollision pinToyKeccak (abiEncode 324 (witnessBundle 324 (pinToyKeccak pre₁).val))
      (abiEncode 324 (witnessBundle 324 (pinToyKeccak pre₂).val)) :=
    fun h => pinToyKeccak_bundle_hashes_differ h.2
  exact ⟨pinToyKeccak, 324, 1, 2, word 0, word 0,
    witnessBundle 324 (pinToyKeccak pre₁).val, witnessBundle 324 (pinToyKeccak pre₂).val,
    pre_bounds.1, pre_bounds.2.1, pre_bounds.2.2, pre_bounds.2.2,
    slot_witnessBundle _ _, slot_witnessBundle _ _, pre_distinct,
    ⟨1, 325, 0, 224, 256, witnessTail, rfl, rfl⟩,
    (injOn_pair_iff_no_collision _ _ _).mpr hpre,
    (injOn_pair_iff_no_collision _ _ _).mpr pinToyKeccak_no_salt_collision,
    hpre, pinToyKeccak_no_salt_collision, pinToyKeccak_bundle_hashes_differ⟩

theorem sends_across_chains_witness :
    ∃ (keccak : List UInt8 → UInt256) (c c' a : ℕ) (s B B' : List UInt8),
      c < 256 ^ 32 ∧ c' < 256 ^ 32 ∧ a < 256 ^ 20 ∧ s.length = 32
      ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
      ∧ bundleSaltSlot B' = word (keccak (packedSalt a s)).val
      ∧ c ≠ c'
      ∧ (∃ (v : UInt8) (dst base oc oa : ℕ) (tail : List UInt8),
          B = bundleEncoding v c dst base (keccak (packedSalt a s)).val oc oa tail
          ∧ B' = bundleEncoding v c' dst base (keccak (packedSalt a s)).val oc oa tail)
      ∧ ¬ HashCollision keccak (abiEncode c B) (abiEncode c' B')
      ∧ bundleHashOfBytes keccak c B ≠ bundleHashOfBytes keccak c' B' := by
  -- one sender and one salt on chains 324 and 326: the bundle hashes are the two chain ids
  have hne : bundleHashOfBytes chainKeccak 324 (witnessBundle 324 (chainKeccak pre₁).val)
      ≠ bundleHashOfBytes chainKeccak 326 (witnessBundle 326 (chainKeccak pre₁).val) := by
    rw [bundleHashOfBytes, bundleHashOfBytes, chainKeccak_abiEncode (by norm_num),
      chainKeccak_abiEncode (by norm_num)]
    decide
  exact ⟨chainKeccak, 324, 326, 1, word 0,
    witnessBundle 324 (chainKeccak pre₁).val, witnessBundle 326 (chainKeccak pre₁).val,
    by norm_num, by norm_num, pre_bounds.1, pre_bounds.2.2,
    slot_witnessBundle _ _, slot_witnessBundle _ _, by norm_num,
    ⟨1, 325, 0, 224, 256, witnessTail, rfl, rfl⟩, fun h => hne h.2, hne⟩

theorem preimage_collision_disjunct_needed :
    ∃ (keccak : List UInt8 → UInt256) (c a a' : ℕ) (s s' B B' : List UInt8),
      a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
      ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
      ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
      ∧ ¬ (a = a' ∧ s = s')
      ∧ bundleHashOfBytes keccak c B = bundleHashOfBytes keccak c B'
      ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a' s') := by
  have hsalt : ¬ HashCollision senderKeccak pre₁ pre₂ := by
    rintro ⟨-, h⟩
    rw [senderKeccak_packedSalt (by norm_num) (word_length 0),
      senderKeccak_packedSalt (by norm_num) (word_length 0)] at h
    exact uint256_one_ne_two h
  exact ⟨senderKeccak, 324, 1, 2, word 0, word 0,
    witnessBundle 324 (senderKeccak pre₁).val, witnessBundle 324 (senderKeccak pre₂).val,
    pre_bounds.1, pre_bounds.2.1, pre_bounds.2.2, pre_bounds.2.2,
    slot_witnessBundle _ _, slot_witnessBundle _ _, pre_distinct,
    by rw [bundleHashOfBytes, bundleHashOfBytes, senderKeccak_abiEncode, senderKeccak_abiEncode],
    hsalt⟩



end AttackVectors.BundleHashEncoding.History

/-! ## Certificates -/

namespace AttackVectors.BundleHashEncoding.History

theorem PreimageCarriesSalt : Properties.PreimageCarriesSalt :=
  preimageSaltSlot_bundleEncoding

theorem SendsDistinctBundleHashesOrKeccakCollision :
    Properties.SendsDistinctBundleHashesOrKeccakCollision :=
  fun keccak c c' _ _ _ _ _ _ ha ha' hs hs' hB hB' hne =>
    sends_distinct_bundle_hashes_or_keccak_collision keccak c c' ha ha' hs hs' hB hB' hne

theorem SendsDistinctBundleHashesOn : Properties.SendsDistinctBundleHashesOn :=
  fun keccak c c' _ _ _ _ _ _ ha ha' hs hs' hB hB' hne hpre hsalt =>
    sends_distinct_bundle_hashes_on keccak c c' ha ha' hs hs' hB hB' hne hpre hsalt

theorem SendsDistinctBundleHashesAcrossChainsOrKeccakCollision :
    Properties.SendsDistinctBundleHashesAcrossChainsOrKeccakCollision :=
  fun keccak _ _ _ _ _ _ _ _ hc hc' ha ha' hs hs' hB hB' hne =>
    sends_distinct_bundle_hashes_across_chains_or_keccak_collision keccak hc hc' ha ha' hs hs'
      hB hB' hne

theorem SendsAcrossChainsWitness : Properties.SendsAcrossChainsWitness :=
  sends_across_chains_witness

theorem SendsDistinctBundleHashesWitness : Properties.SendsDistinctBundleHashesWitness :=
  sends_distinct_bundle_hashes_witness

theorem PreimageCollisionDisjunctNeeded : Properties.PreimageCollisionDisjunctNeeded :=
  preimage_collision_disjunct_needed



end AttackVectors.BundleHashEncoding.History
