import EraSpec.Contracts.InteropDataEncoding.Properties.BundleHashPinned
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashEncoding

/-!
# Proofs: distinct sends give distinct bundle hashes, or a collision on named inputs

The argument is one case split. If the two bundle hashes are equal, either the two hashed inputs
differ, which is a collision on those named inputs, or they are equal. Equal inputs carry equal salt
fields. For the bytes, this is because the salt slot of `B` is a fixed slot of the keccak preimage
(`preimageSaltSlot_abiEncode`). Equal salt fields mean the salt hash agrees on two packed preimages,
and these differ by `packed_addr_salt_inj`. Across chains, equal preimages also have equal leading
words, so they name the same chain (`chain_eq_of_abiEncode_eq`).

The counting facts for the register use `Fintype.card_le_of_injective` on an explicit injection of
`Fin 2 × UInt256` into the packed preimages: two senders, every salt word.
-/

namespace AttackVectors.BundleHashEncoding

universe u v

/-! ## Byte-level facts -/

theorem word_length (n : ℕ) : (word n).length = 32 := length_toBytesBE 32 n

theorem packedSalt_length {a : ℕ} {s : List UInt8} (hs : s.length = 32) :
    (packedSalt a s).length = 52 := by
  simp [packedSalt, hs]

/-- Distinct well-formed `(sender, salt)` pairs give distinct packed preimages. -/
theorem packedSalt_ne {a a' : ℕ} {s s' : List UInt8} (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20)
    (hs : s.length = 32) (hs' : s'.length = 32) (hne : ¬ (a = a' ∧ s = s')) :
    packedSalt a s ≠ packedSalt a' s' :=
  fun h => hne (packed_addr_salt_inj ha ha' hs hs' h)

theorem uint256_val_lt (x : UInt256) : x.val < 256 ^ 32 :=
  lt_of_lt_of_eq x.isLt (by norm_num [UInt256.size])

/-- A `bytes32` value is recovered from its word. -/
theorem word_val_inj {x y : UInt256} (h : word x.val = word y.val) : x = y := by
  have := congrArg fromBytesBE h
  rw [fromBytesBE_toBytesBE (uint256_val_lt x), fromBytesBE_toBytesBE (uint256_val_lt y)] at this
  exact Fin.ext this

theorem toUInt256_val (x : UInt256) : Nat.toUInt256 x.val = x :=
  Fin.ext (Nat.mod_eq_of_lt x.isLt)

/-- A salt slot that holds a full word means the bytes reach past byte 192. -/
theorem length_of_saltSlot {B w : List UInt8} (h : bundleSaltSlot B = w) (hw : w.length = 32) :
    192 ≤ B.length := by
  have := congrArg List.length h
  simp only [bundleSaltSlot, List.length_take, List.length_drop, hw] at this
  omega

/-- The bundle bytes start at byte 96 of `abi.encode(chainId, B)`, padded. -/
theorem abiEncode_drop96 (c : ℕ) (B : List UInt8) : (abiEncode c B).drop 96 = pad32 B := by
  rw [abiEncode, ← List.append_assoc, ← List.append_assoc]
  exact List.drop_left' (by simp)

/-- The chain id is the leading word of `abi.encode(chainId, B)`. -/
theorem abiEncode_take32 (c : ℕ) (B : List UInt8) : (abiEncode c B).take 32 = word c := by
  rw [abiEncode]
  exact List.take_left' (word_length c)

/-- **THE PREIMAGE'S SALT SLOT IS THE BUNDLE'S SALT SLOT**, for any bytes with a full slot. -/
theorem preimageSaltSlot_abiEncode (c : ℕ) {B : List UInt8} (hB : 192 ≤ B.length) :
    preimageSaltSlot (abiEncode c B) = bundleSaltSlot B := by
  unfold preimageSaltSlot bundleSaltSlot
  rw [show (256 : ℕ) = 96 + 160 from rfl, ← List.drop_drop, abiEncode_drop96, pad32,
    List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

/-- Equal keccak preimages name the same chain, below the `uint256` bound. -/
theorem chain_eq_of_abiEncode_eq {c c' : ℕ} {B B' : List UInt8} (hc : c < 256 ^ 32)
    (hc' : c' < 256 ^ 32) (hE : abiEncode c B = abiEncode c' B') : c = c' := by
  have h := congrArg (List.take 32) hE
  rw [abiEncode_take32, abiEncode_take32] at h
  have h2 := congrArg fromBytesBE h
  rwa [fromBytesBE_toBytesBE hc, fromBytesBE_toBytesBE hc'] at h2

theorem bundleEncoding_split (version : UInt8) (src dst base salt oc oa : ℕ) (tail : List UInt8) :
    bundleEncoding version src dst base salt oc oa tail
      = (word 0x20 ++ bytes1Word version ++ word src ++ word dst ++ word base)
          ++ (word salt ++ (word oc ++ (word oa ++ tail))) := by
  simp [bundleEncoding, List.append_assoc]

theorem bundleSaltSlot_bundleEncoding (version : UInt8) (src dst base salt oc oa : ℕ)
    (tail : List UInt8) :
    bundleSaltSlot (bundleEncoding version src dst base salt oc oa tail) = word salt := by
  have hpre : (word 0x20 ++ bytes1Word version ++ word src ++ word dst ++ word base).length = 160 := by
    simp [bytes1Word, length_toBytesBE]
  rw [bundleSaltSlot, bundleEncoding_split, List.drop_left' hpre]
  exact List.take_left' (word_length salt)

theorem bundleEncoding_length (version : UInt8) (src dst base salt oc oa : ℕ) (tail : List UInt8) :
    256 ≤ (bundleEncoding version src dst base salt oc oa tail).length := by
  simp [bundleEncoding, bytes1Word]
  omega

theorem preimageSaltSlot_bundleEncoding (c : ℕ) (version : UInt8) (src dst base salt oc oa : ℕ)
    (tail : List UInt8) :
    preimageSaltSlot (abiEncode c (bundleEncoding version src dst base salt oc oa tail))
      = word salt := by
  rw [preimageSaltSlot_abiEncode c (le_trans (by norm_num) (bundleEncoding_length ..)),
    bundleSaltSlot_bundleEncoding]

/-! ## The register -/

theorem salt_hash_not_injOn_packed (saltHash : List UInt8 → UInt256) :
    ¬ Set.InjOn saltHash packedPreimages := by
  intro hinj
  let g : Fin 2 × UInt256 → List UInt8 := fun p => packedSalt p.1.val (word p.2.val)
  have hsmall : ∀ i : Fin 2, i.val < 256 ^ 20 := fun i => lt_of_lt_of_le i.isLt (by norm_num)
  have hg_mem : ∀ p, g p ∈ packedPreimages := fun p =>
    ⟨p.1.val, word p.2.val, hsmall p.1, word_length _, rfl⟩
  have hg_inj : Function.Injective g := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    obtain ⟨hij, hxy⟩ := packed_addr_salt_inj (hsmall i) (hsmall j) (word_length _)
      (word_length _) h
    exact Prod.ext (Fin.ext hij) (word_val_inj hxy)
  have hf : Function.Injective (saltHash ∘ g) := fun p q h =>
    hg_inj (hinj (hg_mem p) (hg_mem q) h)
  have hc := Fintype.card_le_of_injective _ hf
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  have hpos : 0 < UInt256.size := by decide
  omega

theorem salt_hash_inj_unsatisfiable (saltHash : List UInt8 → UInt256) :
    ¬ Function.Injective saltHash :=
  fun hinj => salt_hash_not_injOn_packed saltHash fun _ _ _ _ h => hinj h

theorem injOn_pair_iff_no_collision {α : Type u} {β : Type v} (f : α → β) (x y : α) :
    Set.InjOn f {x, y} ↔ ¬ HashCollision f x y := by
  rw [Set.injOn_pair, HashCollision, not_and', not_not]

/-! ## The abstract layer -/

theorem distinct_sends_distinct_bundles_or_salt_collision {Bundle : Type u} {Hash : Type v}
    (saltHash : List UInt8 → Hash) (saltField : Bundle → Hash)
    {a a' : ℕ} {s s' : List UInt8} {b b' : Bundle}
    (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20) (hs : s.length = 32) (hs' : s'.length = 32)
    (hb : saltField b = saltHash (packedSalt a s))
    (hb' : saltField b' = saltHash (packedSalt a' s'))
    (hne : ¬ (a = a' ∧ s = s')) :
    b ≠ b' ∨ HashCollision saltHash (packedSalt a s) (packedSalt a' s') := by
  rcases eq_or_ne b b' with rfl | hbb
  · exact .inr ⟨packedSalt_ne ha ha' hs hs' hne, hb.symm.trans hb'⟩
  · exact .inl hbb

theorem distinct_sends_distinct_hashes_or_collision {Bundle : Type u} {Hash : Type v}
    (saltHash : List UInt8 → Hash) (bundleHashOf : Bundle → Hash) (saltField : Bundle → Hash)
    {a a' : ℕ} {s s' : List UInt8} {b b' : Bundle}
    (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20) (hs : s.length = 32) (hs' : s'.length = 32)
    (hb : saltField b = saltHash (packedSalt a s))
    (hb' : saltField b' = saltHash (packedSalt a' s'))
    (hne : ¬ (a = a' ∧ s = s')) :
    bundleHashOf b ≠ bundleHashOf b'
      ∨ HashCollision bundleHashOf b b'
      ∨ HashCollision saltHash (packedSalt a s) (packedSalt a' s') := by
  by_cases hh : bundleHashOf b = bundleHashOf b'
  · exact .inr ((distinct_sends_distinct_bundles_or_salt_collision saltHash saltField ha ha' hs hs'
      hb hb' hne).imp (⟨·, hh⟩) id)
  · exact .inl hh

theorem distinct_sends_distinct_hashes_on {Bundle : Type u} {Hash : Type v}
    (saltHash : List UInt8 → Hash) (bundleHashOf : Bundle → Hash) (saltField : Bundle → Hash)
    {a a' : ℕ} {s s' : List UInt8} {b b' : Bundle}
    (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20) (hs : s.length = 32) (hs' : s'.length = 32)
    (hb : saltField b = saltHash (packedSalt a s))
    (hb' : saltField b' = saltHash (packedSalt a' s'))
    (hne : ¬ (a = a' ∧ s = s'))
    (hsalt : Set.InjOn saltHash {packedSalt a s, packedSalt a' s'})
    (hbundle : Set.InjOn bundleHashOf {b, b'}) :
    bundleHashOf b ≠ bundleHashOf b' := by
  rcases distinct_sends_distinct_hashes_or_collision saltHash bundleHashOf saltField ha ha' hs hs'
    hb hb' hne with h | h | h
  · exact h
  · exact absurd h ((injOn_pair_iff_no_collision _ _ _).mp hbundle)
  · exact absurd h ((injOn_pair_iff_no_collision _ _ _).mp hsalt)

/-! ## The keccak layer -/

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

/-! ## Witnesses and countermodels

The instances use two senders, `1` and `2`, with the zero user salt, on chain `324` (and `326` for the
cross-chain witness). The bundle bytes are `bundleEncoding` layouts with version `0x01`
(`Messaging.sol:6`), destination `325` and the canonical offsets and tail of a bundle with no calls. -/

/-- The salt word stored in bundle bytes, read back as a `bytes32`. -/
def saltOfBytes (B : List UInt8) : UInt256 := Nat.toUInt256 (fromBytesBE (bundleSaltSlot B))

/-- A stand-in for keccak, used only in witnesses. It is not a hash: it reads back exactly what the
argument compares. On a 52-byte input (a packed salt preimage) it returns the sender, and on
anything else (a bundle-hash preimage) it returns the salt word in the preimage's salt slot. -/
def toyKeccak (x : List UInt8) : UInt256 :=
  if x.length = 52 then Nat.toUInt256 (fromBytesBE (x.take 20))
  else Nat.toUInt256 (fromBytesBE (preimageSaltSlot x))

/-- A stand-in that separates packed preimages by sender and maps every other input to `0`. -/
def senderKeccak (x : List UInt8) : UInt256 :=
  if x.length = 52 then Nat.toUInt256 (fromBytesBE (x.take 20)) else 0

/-- A stand-in that separates packed preimages by sender and bundle-hash preimages by their leading
word, the chain id. -/
def chainKeccak (x : List UInt8) : UInt256 :=
  if x.length = 52 then Nat.toUInt256 (fromBytesBE (x.take 20))
  else Nat.toUInt256 (fromBytesBE (x.take 32))

/-- The tail of the canonical encoding of an empty `calls` array and a `BundleAttributes` with
empty execution and unbundler addresses, `useFixedFee = false` and user salt `0`. -/
def witnessTail : List UInt8 :=
  word 0 ++ (word 128 ++ (word 160 ++ (word 0 ++ (word 0 ++ (word 0 ++ word 0)))))

/-- The witnesses' bundle bytes from source chain `c`, carrying derived salt word `σ`. -/
def witnessBundle (c σ : ℕ) : List UInt8 := bundleEncoding 1 c 325 0 σ 224 256 witnessTail

theorem witnessBundle_length (c σ : ℕ) : 192 ≤ (witnessBundle c σ).length :=
  le_trans (by norm_num) (bundleEncoding_length ..)

theorem saltOfBytes_witnessBundle (c : ℕ) (x : UInt256) :
    saltOfBytes (witnessBundle c x.val) = x := by
  rw [saltOfBytes, witnessBundle, bundleSaltSlot_bundleEncoding,
    fromBytesBE_toBytesBE (uint256_val_lt x), toUInt256_val]

theorem toyKeccak_packedSalt {a : ℕ} {s : List UInt8} (ha : a < 256 ^ 20) (hs : s.length = 32) :
    toyKeccak (packedSalt a s) = Nat.toUInt256 a := by
  rw [toyKeccak, ite_eq_left (packedSalt_length hs), packedSalt,
    List.take_left' (length_toBytesBE 20 a), fromBytesBE_toBytesBE ha]

theorem senderKeccak_packedSalt {a : ℕ} {s : List UInt8} (ha : a < 256 ^ 20)
    (hs : s.length = 32) : senderKeccak (packedSalt a s) = Nat.toUInt256 a := by
  rw [senderKeccak, ite_eq_left (packedSalt_length hs), packedSalt,
    List.take_left' (length_toBytesBE 20 a), fromBytesBE_toBytesBE ha]

theorem abiEncode_length_ne (c : ℕ) (B : List UInt8) : (abiEncode c B).length ≠ 52 := by
  simp [abiEncode]
  omega

theorem toyKeccak_abiEncode_witnessBundle (c c₀ : ℕ) (x : UInt256) :
    toyKeccak (abiEncode c (witnessBundle c₀ x.val)) = x := by
  rw [toyKeccak, ite_eq_right (abiEncode_length_ne c _), preimageSaltSlot_abiEncode c
    (witnessBundle_length _ _)]
  exact saltOfBytes_witnessBundle c₀ x

theorem senderKeccak_abiEncode (c : ℕ) (B : List UInt8) : senderKeccak (abiEncode c B) = 0 := by
  rw [senderKeccak, ite_eq_right (abiEncode_length_ne c _)]

theorem chainKeccak_abiEncode {c : ℕ} (hc : c < 256 ^ 32) (B : List UInt8) :
    chainKeccak (abiEncode c B) = Nat.toUInt256 c := by
  rw [chainKeccak, ite_eq_right (abiEncode_length_ne c _), abiEncode_take32,
    fromBytesBE_toBytesBE hc]

theorem slot_witnessBundle (c : ℕ) (x : UInt256) :
    bundleSaltSlot (witnessBundle c x.val) = word x.val :=
  bundleSaltSlot_bundleEncoding ..

/-- The two packed preimages of the witnesses. -/
abbrev pre₁ : List UInt8 := packedSalt 1 (word 0)
abbrev pre₂ : List UInt8 := packedSalt 2 (word 0)

theorem pre_bounds : (1 : ℕ) < 256 ^ 20 ∧ (2 : ℕ) < 256 ^ 20 ∧ (word 0).length = 32 :=
  ⟨by norm_num, by norm_num, word_length 0⟩

theorem pre_distinct : ¬ ((1 : ℕ) = 2 ∧ word 0 = word 0) := by
  simp

theorem pre₁_ne_pre₂ : pre₁ ≠ pre₂ :=
  packedSalt_ne pre_bounds.1 pre_bounds.2.1 pre_bounds.2.2 pre_bounds.2.2 pre_distinct

theorem toyKeccak_pre₁ : toyKeccak pre₁ = 1 := toyKeccak_packedSalt (by norm_num) (word_length 0)
theorem toyKeccak_pre₂ : toyKeccak pre₂ = 2 := toyKeccak_packedSalt (by norm_num) (word_length 0)

theorem uint256_one_ne_two : (1 : UInt256) ≠ 2 := by decide

theorem toyKeccak_no_salt_collision : ¬ HashCollision toyKeccak pre₁ pre₂ := by
  rintro ⟨-, h⟩
  rw [toyKeccak_pre₁, toyKeccak_pre₂] at h
  exact uint256_one_ne_two h

/-- The two witness bundles on chain `324` get bundle hashes `1` and `2` under `toyKeccak`. -/
theorem toyKeccak_bundle_hashes_differ :
    bundleHashOfBytes toyKeccak 324 (witnessBundle 324 (toyKeccak pre₁).val)
      ≠ bundleHashOfBytes toyKeccak 324 (witnessBundle 324 (toyKeccak pre₂).val) := by
  rw [bundleHashOfBytes, bundleHashOfBytes, toyKeccak_abiEncode_witnessBundle,
    toyKeccak_abiEncode_witnessBundle, toyKeccak_pre₁, toyKeccak_pre₂]
  exact uint256_one_ne_two

theorem distinct_sends_distinct_hashes_on_satisfiable :
    ∃ (saltHash : List UInt8 → UInt256) (bundleHashOf saltField : List UInt8 → UInt256)
      (a a' : ℕ) (s s' : List UInt8) (b b' : List UInt8),
      a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
      ∧ saltField b = saltHash (packedSalt a s) ∧ saltField b' = saltHash (packedSalt a' s')
      ∧ ¬ (a = a' ∧ s = s')
      ∧ Set.InjOn saltHash {packedSalt a s, packedSalt a' s'} ∧ Set.InjOn bundleHashOf {b, b'}
      ∧ ¬ HashCollision bundleHashOf b b'
      ∧ ¬ HashCollision saltHash (packedSalt a s) (packedSalt a' s')
      ∧ bundleHashOf b ≠ bundleHashOf b' := by
  have hbundle : ¬ HashCollision (bundleHashOfBytes toyKeccak 324)
      (witnessBundle 324 (toyKeccak pre₁).val) (witnessBundle 324 (toyKeccak pre₂).val) :=
    fun h => toyKeccak_bundle_hashes_differ h.2
  exact ⟨toyKeccak, bundleHashOfBytes toyKeccak 324, saltOfBytes, 1, 2, word 0, word 0,
    witnessBundle 324 (toyKeccak pre₁).val, witnessBundle 324 (toyKeccak pre₂).val,
    pre_bounds.1, pre_bounds.2.1, pre_bounds.2.2, pre_bounds.2.2,
    saltOfBytes_witnessBundle _ _, saltOfBytes_witnessBundle _ _, pre_distinct,
    (injOn_pair_iff_no_collision _ _ _).mpr toyKeccak_no_salt_collision,
    (injOn_pair_iff_no_collision _ _ _).mpr hbundle,
    hbundle, toyKeccak_no_salt_collision, toyKeccak_bundle_hashes_differ⟩

theorem distinct_sends_collision_not_tautology {a a' : ℕ} {s s' : List UInt8}
    (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20) (hs : s.length = 32) (hs' : s'.length = 32)
    (hne : ¬ (a = a' ∧ s = s')) :
    ∃ (saltHash : List UInt8 → UInt256) (bundleHashOf saltField : List UInt8 → UInt256)
      (b b' : List UInt8),
      saltField b = saltHash (packedSalt a s) ∧ saltField b' = saltHash (packedSalt a' s')
      ∧ ¬ HashCollision bundleHashOf b b'
      ∧ ¬ HashCollision saltHash (packedSalt a s) (packedSalt a' s') := by
  classical
  -- the salt hash separating exactly the two named preimages
  let saltHash : List UInt8 → UInt256 := fun p => if p = packedSalt a s then 1 else 2
  have hpre : packedSalt a' s' ≠ packedSalt a s := (packedSalt_ne ha ha' hs hs' hne).symm
  have h₁ : saltHash (packedSalt a s) = 1 := ite_eq_left rfl
  have h₂ : saltHash (packedSalt a' s') = 2 := ite_eq_right hpre
  refine ⟨saltHash, bundleHashOfBytes toyKeccak 324, saltOfBytes,
    witnessBundle 324 (saltHash (packedSalt a s)).val,
    witnessBundle 324 (saltHash (packedSalt a' s')).val,
    saltOfBytes_witnessBundle _ _, saltOfBytes_witnessBundle _ _, ?_, ?_⟩
  · rintro ⟨-, h⟩
    rw [bundleHashOfBytes, bundleHashOfBytes, toyKeccak_abiEncode_witnessBundle,
      toyKeccak_abiEncode_witnessBundle, h₁, h₂] at h
    exact uint256_one_ne_two h
  · rintro ⟨-, h⟩
    rw [h₁, h₂] at h
    exact uint256_one_ne_two h

theorem salt_collision_disjunct_needed :
    ∃ (saltHash : List UInt8 → UInt256) (bundleHashOf saltField : List UInt8 → UInt256)
      (a a' : ℕ) (s s' : List UInt8) (b b' : List UInt8),
      a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
      ∧ saltField b = saltHash (packedSalt a s) ∧ saltField b' = saltHash (packedSalt a' s')
      ∧ ¬ (a = a' ∧ s = s')
      ∧ bundleHashOf b = bundleHashOf b'
      ∧ ¬ HashCollision bundleHashOf b b' :=
  -- every salt hashes to `0`, so both sends build the same bundle
  ⟨fun _ => 0, bundleHashOfBytes toyKeccak 324, saltOfBytes, 1, 2, word 0, word 0,
    witnessBundle 324 (0 : UInt256).val, witnessBundle 324 (0 : UInt256).val,
    pre_bounds.1, pre_bounds.2.1, pre_bounds.2.2, pre_bounds.2.2,
    saltOfBytes_witnessBundle _ _, saltOfBytes_witnessBundle _ _, pre_distinct, rfl,
    fun h => h.1 rfl⟩

theorem bundle_collision_disjunct_needed :
    ∃ (saltHash : List UInt8 → UInt256) (bundleHashOf saltField : List UInt8 → UInt256)
      (a a' : ℕ) (s s' : List UInt8) (b b' : List UInt8),
      a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
      ∧ saltField b = saltHash (packedSalt a s) ∧ saltField b' = saltHash (packedSalt a' s')
      ∧ ¬ (a = a' ∧ s = s')
      ∧ bundleHashOf b = bundleHashOf b'
      ∧ ¬ HashCollision saltHash (packedSalt a s) (packedSalt a' s') :=
  -- the salts are separated (sender 1 ↦ 1, sender 2 ↦ 2), every bundle hashes to `0`
  ⟨toyKeccak, fun _ => 0, saltOfBytes, 1, 2, word 0, word 0,
    witnessBundle 324 (toyKeccak pre₁).val, witnessBundle 324 (toyKeccak pre₂).val,
    pre_bounds.1, pre_bounds.2.1, pre_bounds.2.2, pre_bounds.2.2,
    saltOfBytes_witnessBundle _ _, saltOfBytes_witnessBundle _ _, pre_distinct, rfl,
    toyKeccak_no_salt_collision⟩

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
  have hpre : ¬ HashCollision toyKeccak (abiEncode 324 (witnessBundle 324 (toyKeccak pre₁).val))
      (abiEncode 324 (witnessBundle 324 (toyKeccak pre₂).val)) :=
    fun h => toyKeccak_bundle_hashes_differ h.2
  exact ⟨toyKeccak, 324, 1, 2, word 0, word 0,
    witnessBundle 324 (toyKeccak pre₁).val, witnessBundle 324 (toyKeccak pre₂).val,
    pre_bounds.1, pre_bounds.2.1, pre_bounds.2.2, pre_bounds.2.2,
    slot_witnessBundle _ _, slot_witnessBundle _ _, pre_distinct,
    ⟨1, 325, 0, 224, 256, witnessTail, rfl, rfl⟩,
    (injOn_pair_iff_no_collision _ _ _).mpr hpre,
    (injOn_pair_iff_no_collision _ _ _).mpr toyKeccak_no_salt_collision,
    hpre, toyKeccak_no_salt_collision, toyKeccak_bundle_hashes_differ⟩

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

theorem salt_collision_makes_bundles_identical :
    ∃ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B : List UInt8),
      a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
      ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
      ∧ bundleSaltSlot B = word (keccak (packedSalt a' s')).val
      ∧ ¬ (a = a' ∧ s = s')
      ∧ HashCollision keccak (packedSalt a s) (packedSalt a' s') :=
  ⟨fun _ => 0, 1, 2, word 0, word 0, witnessBundle 324 (0 : UInt256).val,
    pre_bounds.1, pre_bounds.2.1, pre_bounds.2.2, pre_bounds.2.2,
    slot_witnessBundle _ _, slot_witnessBundle _ _, pre_distinct, pre₁_ne_pre₂, rfl⟩

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

end AttackVectors.BundleHashEncoding

/-! ## Certificates -/

namespace AttackVectors.BundleHashEncoding

universe u v

theorem SaltHashInjUnsatisfiable : Properties.SaltHashInjUnsatisfiable :=
  salt_hash_inj_unsatisfiable

theorem SaltHashNotInjOnPackedPreimages : Properties.SaltHashNotInjOnPackedPreimages :=
  salt_hash_not_injOn_packed

theorem BundleHashInjUnsatisfiable : Properties.BundleHashInjUnsatisfiable.{u} :=
  fun _ _ f => not_injective_infinite_finite f

theorem InjOnPairIffNoCollision : Properties.InjOnPairIffNoCollision.{u, v} :=
  injOn_pair_iff_no_collision

theorem DistinctSendsDistinctBundlesOrSaltCollision :
    Properties.DistinctSendsDistinctBundlesOrSaltCollision.{u, v} :=
  fun saltHash saltField _ _ _ _ _ _ ha ha' hs hs' hb hb' hne =>
    distinct_sends_distinct_bundles_or_salt_collision saltHash saltField ha ha' hs hs' hb hb' hne

theorem DistinctSendsDistinctHashesOrCollision :
    Properties.DistinctSendsDistinctHashesOrCollision.{u, v} :=
  fun saltHash bundleHashOf saltField _ _ _ _ _ _ ha ha' hs hs' hb hb' hne =>
    distinct_sends_distinct_hashes_or_collision saltHash bundleHashOf saltField ha ha' hs hs' hb
      hb' hne

theorem DistinctSendsDistinctHashesOn : Properties.DistinctSendsDistinctHashesOn.{u, v} :=
  fun saltHash bundleHashOf saltField _ _ _ _ _ _ ha ha' hs hs' hb hb' hne hsalt hbundle =>
    distinct_sends_distinct_hashes_on saltHash bundleHashOf saltField ha ha' hs hs' hb hb' hne
      hsalt hbundle

theorem DistinctSendsDistinctHashesOnSatisfiable :
    Properties.DistinctSendsDistinctHashesOnSatisfiable :=
  distinct_sends_distinct_hashes_on_satisfiable

theorem DistinctSendsCollisionNotTautology : Properties.DistinctSendsCollisionNotTautology :=
  fun _ _ _ _ ha ha' hs hs' hne => distinct_sends_collision_not_tautology ha ha' hs hs' hne

theorem SaltCollisionDisjunctNeeded : Properties.SaltCollisionDisjunctNeeded :=
  salt_collision_disjunct_needed

theorem BundleCollisionDisjunctNeeded : Properties.BundleCollisionDisjunctNeeded :=
  bundle_collision_disjunct_needed

theorem SaltSlotOfBundleEncoding : Properties.SaltSlotOfBundleEncoding :=
  bundleSaltSlot_bundleEncoding

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

theorem SaltCollisionMakesBundlesIdentical : Properties.SaltCollisionMakesBundlesIdentical :=
  salt_collision_makes_bundles_identical

theorem PreimageCollisionDisjunctNeeded : Properties.PreimageCollisionDisjunctNeeded :=
  preimage_collision_disjunct_needed

end AttackVectors.BundleHashEncoding
