import EraSpec.Contracts.Merkle.Properties.DomainSeparation
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashPinned
import EraSpec.Contracts.Merkle.Proofs.PathCollision
import EraSpec.Contracts.Merkle.Proofs.RootForgeryPinned
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastLeaf
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.TreeRoot

/-!
# Proofs: every Merkle domain premise is a keccak collision on two named byte strings

Proofs of `../Properties/DomainSeparation.lean`.

The byte-level facts are two kinds of argument. Lengths: every encoder is a concatenation of
fixed-width blocks (`length_toBytesBE`). Content: two concatenations of 32-byte words are equal iff
their words are (`List.append_inj`), and a word below `2^256` is recovered from its bytes
(`fromBytesBE_toBytesBE`). Every reduction to keccak is then the same two steps: unfold the
abstract hash into keccak of a named preimage, and show the two named preimages differ (by length,
or by a word) so that equal hashes are a `HashCollision`. The composed results reuse the
abstract-hash theorems of `PathCollision`, `LastLeaf` and `TreeRoot` and translate their located
breaks.
-/

namespace MerkleSpec.DomainSeparation

open AttackVectors.BundleHashEncoding (HashCollision toBytesBE word fromBytesBE length_toBytesBE
  fromBytesBE_toBytesBE word_length uint256_val_lt word_val_inj toUInt256_val)
open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf MerkleSpec.Pinned
open Contracts.InteropCommitmentTree (Leaf Tree LeafHash leafHashes TreeRootBreak InclusionAccepted
  NonInclusionAccepted Valid root setup threeLeafTree)

/-! ## Byte toolkit -/

theorem w32_length (x : UInt256) : (w32 x).length = 32 := word_length x.val

theorem toBytesBE_zero : ∀ k, toBytesBE k 0 = List.replicate k 0
  | 0 => rfl
  | k + 1 => by
    rw [toBytesBE, Nat.zero_div, toBytesBE_zero k, List.replicate_succ']
    rfl

theorem word_zero : word 0 = List.replicate 32 0 := toBytesBE_zero 32

theorem w32_zero : w32 0 = List.replicate 32 0 := toBytesBE_zero 32

/-- A word below `2^256` is recovered from its 32 bytes. -/
theorem word_inj {a b : ℕ} (ha : a < 256 ^ 32) (hb : b < 256 ^ 32) (h : word a = word b) :
    a = b := by
  have := congrArg fromBytesBE h
  rwa [fromBytesBE_toBytesBE ha, fromBytesBE_toBytesBE hb] at this

theorem w32_inj {x y : UInt256} (h : w32 x = w32 y) : x = y := word_val_inj h

/-- The word of `a < 2^256` is 32 zero bytes iff `a = 0`. -/
theorem word_eq_zeros_iff {a : ℕ} (ha : a < 256 ^ 32) : word a = List.replicate 32 0 ↔ a = 0 := by
  constructor
  · intro h
    rw [← word_zero] at h
    exact word_inj ha (by norm_num) h
  · rintro rfl
    exact word_zero

/-- Two concatenations of three blocks, the first two of 32 bytes, are equal iff the blocks are. -/
theorem three_words_eq {a b c a' b' c' : List UInt8} (ha : a.length = 32) (ha' : a'.length = 32)
    (hb : b.length = 32) (hb' : b'.length = 32) (h : a ++ b ++ c = a' ++ b' ++ c') :
    a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [ha, ha', hb, hb'])
  obtain ⟨h3, h4⟩ := List.append_inj h1 (by simp [ha, ha'])
  exact ⟨h3, h4, h2⟩

/-- Multiplying by `256^j` shifts the big-endian bytes left by `j` zero bytes. -/
theorem toBytesBE_mul_pow (k n : ℕ) :
    ∀ j, toBytesBE (k + j) (n * 256 ^ j) = toBytesBE k n ++ List.replicate j 0
  | 0 => by simp
  | j + 1 => by
    rw [show k + (j + 1) = (k + j) + 1 from by omega, toBytesBE]
    have h1 : n * 256 ^ (j + 1) / 256 = n * 256 ^ j := by
      rw [pow_succ, ← mul_assoc, Nat.mul_div_cancel _ (by norm_num)]
    have h2 : n * 256 ^ (j + 1) % 256 = 0 := by
      rw [pow_succ, ← mul_assoc]
      exact Nat.mul_mod_left _ _
    rw [h1, h2, toBytesBE_mul_pow k n j, List.replicate_succ', List.append_assoc]
    rfl

theorem emptyPre_split :
    emptyPre = List.replicate 32 0 ++ List.replicate 32 0 ++ List.replicate 32 0 := by
  rw [List.replicate_append_replicate, List.replicate_append_replicate]
  rfl

theorem pinPaddingPre_eq : pinPaddingPre = emptyPre := by
  rw [emptyPre_split, pinPaddingPre, imtPre]
  exact congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) w32_zero (toBytesBE_zero 32)) w32_zero

theorem imtPre_zero : imtPre ⟨0, 0, 0⟩ = emptyPre := pinPaddingPre_eq

theorem zero_leafBounded : LeafBounded ⟨0, 0, 0⟩ := by
  show (0 : ℕ) < 256 ^ 32
  norm_num

/-! ## (a) Lengths -/

theorem nodePre_length (a b : UInt256) : (nodePre a b).length = 64 := by
  simp [nodePre]

theorem pairPre_length (p : UInt256 × UInt256) : (pairPre p).length = 64 := nodePre_length _ _

theorem logPre_length (log : L2Log) : (logPre log).length = 88 := by
  simp [logPre, length_toBytesBE]

theorem chainIdPre_length (padC r c : UInt256) : (chainIdPre padC r c).length = 96 := by
  simp [chainIdPre]

theorem imtPre_length (ℓ : Leaf) : (imtPre ℓ).length = 96 := by
  simp [imtPre, length_toBytesBE]

theorem commitPre_length (tag : ℕ) (f s : UInt256) : (commitPre tag f s).length = 96 := by
  simp [commitPre, length_toBytesBE]

theorem batchPre_length (padB r n t : UInt256) : (batchPre padB r n t).length = 128 := by
  simp [batchPre]

theorem emptyPre_length : emptyPre.length = 96 := by simp [emptyPre]

theorem logDefaultPre_length : logDefaultPre.length = 88 := by simp [logDefaultPre]

theorem imtEmptyLeafPre_length : imtEmptyLeafPre.length = 34 := rfl

theorem preimage_lengths : Properties.PreimageLengths :=
  ⟨nodePre_length, logPre_length, logDefaultPre_length, chainIdPre_length, imtPre_length,
    emptyPre_length, commitPre_length, batchPre_length, rfl, imtEmptyLeafPre_length⟩

theorem ne_of_length_ne {x y : List UInt8} (h : x.length ≠ y.length) : x ≠ y :=
  fun e => h (congrArg List.length e)

theorem cross_length_eq_is_collision (keccak : Keccak) (x y : List UInt8)
    (hlen : x.length ≠ y.length) (heq : keccak x = keccak y) : HashCollision keccak x y :=
  ⟨ne_of_length_ne hlen, heq⟩

/-- Below `2^256`, the word of a natural number determines it. -/
theorem toUInt256_inj {a b : ℕ} (ha : a < 256 ^ 32) (hb : b < 256 ^ 32)
    (h : Nat.toUInt256 a = Nat.toUInt256 b) : a = b := by
  have h' := congrArg Fin.val h
  have hsz : (256 : ℕ) ^ 32 = UInt256.size := by norm_num [UInt256.size]
  rw [hsz] at ha hb
  have e1 : (Nat.toUInt256 a).val = a := Nat.mod_eq_of_lt ha
  have e2 : (Nat.toUInt256 b).val = b := Nat.mod_eq_of_lt hb
  rw [e1, e2] at h'
  exact h'

theorem lengthKeccak_eq_iff {x y : List UInt8} (hx : x.length < 256 ^ 32) (hy : y.length < 256 ^ 32) :
    lengthKeccak x = lengthKeccak y ↔ x.length = y.length := by
  constructor
  · exact toUInt256_inj hx hy
  · intro h
    unfold lengthKeccak
    rw [h]

theorem cross_length_eq_is_collision_witness : Properties.CrossLengthEqIsCollisionWitness := by
  refine ⟨⟨constKeccak, [], [0], by simp, rfl⟩, ?_⟩
  rintro x y hx hy hne ⟨-, heq⟩
  exact hne ((lengthKeccak_eq_iff hx hy).mp heq)

/-! ## (b) The 96-byte family -/

theorem imtPre_inj {ℓ ℓ' : Leaf} (hℓ : LeafBounded ℓ) (hℓ' : LeafBounded ℓ')
    (h : imtPre ℓ = imtPre ℓ') : ℓ = ℓ' := by
  obtain ⟨h1, h2, h3⟩ :=
    three_words_eq (w32_length _) (w32_length _) (word_length _) (word_length _) h
  have e1 := w32_inj h1
  have e2 := word_inj hℓ hℓ' h2
  have e3 := w32_inj h3
  cases ℓ
  cases ℓ'
  simp only at e1 e2 e3
  subst e1 e2 e3
  rfl

theorem imtPre_eq_emptyPre_iff {ℓ : Leaf} (hℓ : LeafBounded ℓ) :
    imtPre ℓ = emptyPre ↔ ℓ = ⟨0, 0, 0⟩ := by
  constructor
  · intro h
    rw [← imtPre_zero] at h
    exact imtPre_inj hℓ zero_leafBounded h
  · rintro rfl
    exact imtPre_zero

theorem chainIdPre_ne_emptyPre {padC r c : UInt256} (hpad : padC ≠ 0) :
    chainIdPre padC r c ≠ emptyPre := by
  intro h
  rw [emptyPre_split] at h
  obtain ⟨h1, -, -⟩ := three_words_eq (w32_length _) (by simp) (w32_length _) (by simp) h
  rw [← w32_zero] at h1
  exact hpad (w32_inj h1)

theorem imtPre_ne_chainIdPre {ℓ : Leaf} {padC r c : UInt256} (hv : ℓ.value ≠ padC) :
    imtPre ℓ ≠ chainIdPre padC r c := by
  intro h
  obtain ⟨h1, -, -⟩ :=
    three_words_eq (w32_length _) (w32_length _) (word_length _) (w32_length _) h
  exact hv (w32_inj h1)

theorem imtPre_eq_chainIdPre_iff {ℓ : Leaf} {padC r c : UInt256} (hℓ : LeafBounded ℓ) :
    imtPre ℓ = chainIdPre padC r c ↔ ℓ = ⟨padC, r.val, c⟩ := by
  constructor
  · intro h
    have hb : LeafBounded ⟨padC, r.val, c⟩ := uint256_val_lt r
    exact imtPre_inj hℓ hb h
  · rintro rfl
    rfl

theorem chainIdLeafPaddingPre_length : chainIdLeafPaddingPre.length = 18 := rfl

theorem commit_leaf_not_chain_id_leaf_or_collision :
    Properties.CommitLeafNotChainIdLeafOrCollision := by
  intro keccak tag f b ni nv r c h
  obtain ⟨h1, -, -⟩ :=
    three_words_eq (w32_length _) (w32_length _) (word_length _) (w32_length _) h
  exact ⟨ne_of_length_ne (by rw [commitPre_length, chainIdLeafPaddingPre_length]; decide),
    w32_inj h1⟩

theorem commitPre_eq_words (tag : ℕ) (f s : UInt256) :
    commitPre tag f s = word (tag * 256 ^ 28) ++ w32 f ++ w32 s := by
  rw [commitPre, show word (tag * 256 ^ 28) = toBytesBE (4 + 28) (tag * 256 ^ 28) from rfl,
    toBytesBE_mul_pow]

theorem tagWord_lt {tag : ℕ} (ht : tag < 256 ^ 4) : tag * 256 ^ 28 < 256 ^ 32 := by
  calc tag * 256 ^ 28 < 256 ^ 4 * 256 ^ 28 := Nat.mul_lt_mul_of_pos_right ht (by positivity)
    _ = 256 ^ 32 := by norm_num

theorem commitPre_ne_emptyPre {tag : ℕ} {f s : UInt256} (ht : tag < 256 ^ 4) (hne : tag ≠ 0) :
    commitPre tag f s ≠ emptyPre := by
  intro h
  rw [commitPre_eq_words, emptyPre_split] at h
  obtain ⟨h1, -, -⟩ := three_words_eq (word_length _) (by simp) (w32_length _) (by simp) h
  have := (word_eq_zeros_iff (tagWord_lt ht)).mp h1
  rcases Nat.mul_eq_zero.mp this with h0 | h0
  · exact hne h0
  · exact absurd h0 (by positivity)

theorem commitPre_ne_imtPre {tag : ℕ} {f s : UInt256} {ℓ : Leaf} (ht : tag < 256 ^ 4)
    (hv : ℓ.value.val ≠ tag * 256 ^ 28) : commitPre tag f s ≠ imtPre ℓ := by
  intro h
  rw [commitPre_eq_words] at h
  obtain ⟨h1, -, -⟩ :=
    three_words_eq (word_length _) (w32_length _) (w32_length _) (word_length _) h
  exact hv (word_inj (tagWord_lt ht) (uint256_val_lt _) h1).symm

theorem commitPre_ne_chainIdPre {tag : ℕ} {f s padC r c : UInt256} (ht : tag < 256 ^ 4)
    (hv : padC.val ≠ tag * 256 ^ 28) : commitPre tag f s ≠ chainIdPre padC r c := by
  intro h
  rw [commitPre_eq_words] at h
  obtain ⟨h1, -, -⟩ :=
    three_words_eq (word_length _) (w32_length _) (w32_length _) (w32_length _) h
  exact hv (word_inj (tagWord_lt ht) (uint256_val_lt _) h1).symm

/-- `firstWordKeccak` reads back the first word. -/
theorem firstWordKeccak_word {a : ℕ} (ha : a < 256 ^ 32) (rest : List UInt8) :
    firstWordKeccak (word a ++ rest) = Nat.toUInt256 a := by
  rw [firstWordKeccak, List.take_left' (word_length a), fromBytesBE_toBytesBE ha]

theorem firstWordKeccak_w32 (x : UInt256) (rest : List UInt8) :
    firstWordKeccak (w32 x ++ rest) = x := by
  rw [firstWordKeccak_word (uint256_val_lt x), toUInt256_val]

theorem firstWordKeccak_emptyPre : firstWordKeccak emptyPre = 0 := by
  rw [emptyPre_split, List.append_assoc, ← word_zero, firstWordKeccak_word (by norm_num)]
  rfl

theorem firstWordKeccak_chainIdPre (padC r c : UInt256) :
    firstWordKeccak (chainIdPre padC r c) = padC := by
  rw [chainIdPre, List.append_assoc, firstWordKeccak_w32]

theorem firstWordKeccak_imtPre (ℓ : Leaf) : firstWordKeccak (imtPre ℓ) = ℓ.value := by
  rw [imtPre, List.append_assoc, firstWordKeccak_w32]

theorem firstWordKeccak_commitPre {tag : ℕ} (ht : tag < 256 ^ 4) (f s : UInt256) :
    firstWordKeccak (commitPre tag f s) = Nat.toUInt256 (tag * 256 ^ 28) := by
  rw [commitPre_eq_words, List.append_assoc, firstWordKeccak_word (tagWord_lt ht)]

theorem ninety_six_byte_family_witness : Properties.NinetySixByteFamilyWitness := by
  refine ⟨1, 1, ⟨2, 0, 0⟩, by decide, by norm_num, by norm_num, by
    show (0 : ℕ) < 256 ^ 32; norm_num, by decide, ?_, ?_, ?_⟩
  · show (2 : ℕ) ≠ 1 * 256 ^ 28
    norm_num
  · show (1 : ℕ) ≠ 1 * 256 ^ 28
    norm_num
  intro r c f s
  have ht : (1 : ℕ) < 256 ^ 4 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rintro ⟨-, h⟩
  · rw [firstWordKeccak_chainIdPre, firstWordKeccak_emptyPre] at h
    exact absurd h (by decide)
  · rw [firstWordKeccak_imtPre, firstWordKeccak_chainIdPre] at h
    exact absurd h (by decide)
  · rw [firstWordKeccak_commitPre ht, firstWordKeccak_emptyPre] at h
    exact absurd h (by decide)
  · rw [firstWordKeccak_commitPre ht, firstWordKeccak_imtPre] at h
    exact absurd h (by decide)
  · rw [firstWordKeccak_commitPre ht, firstWordKeccak_chainIdPre] at h
    exact absurd h (by decide)

theorem imtPadding_eq (keccak : Keccak) : imtPadding keccak = emptyEntryHash keccak := by
  show keccak (imtPre ⟨0, 0, 0⟩) = keccak emptyPre
  rw [imtPre_zero]

theorem setup_root_zero (keccak : Keccak) :
    root (efficientHash keccak) (imtPadding keccak) (hashLeaf keccak) setup 0
      = emptyEntryHash keccak := by
  rw [← imtPadding_eq]
  rfl

theorem empty_constants_coincide : Properties.EmptyConstantsCoincide := by
  refine ⟨rfl, rfl, fun keccak => ⟨imtPadding_eq keccak, setup_root_zero keccak⟩, ?_⟩
  intro keccak hdoc
  have he : emptyEntryHash keccak = CHAIN_TREE_EMPTY_ENTRY_HASH := hdoc
  exact ⟨he, (imtPadding_eq keccak).trans he, (setup_root_zero keccak).trans he⟩

theorem keccak_of_empty_is_documented_satisfiable :
    Properties.KeccakOfEmptyIsDocumentedSatisfiable :=
  ⟨fun _ => 0x46700b4d40ac5c35af2c22dda2787a91eb567b06c924a8fb8ae9a05b20c08c21, rfl⟩

theorem log_default_is_zero_log : Properties.LogDefaultIsZeroLog := by
  unfold Properties.LogDefaultIsZeroLog
  decide

/-! ## (e) The node-collision lift -/

theorem nodePre_inj {a b c d : UInt256} (h : nodePre a b = nodePre c d) : a = c ∧ b = d := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  exact ⟨w32_inj h1, w32_inj h2⟩

theorem pairPre_inj {p q : UInt256 × UInt256} (h : pairPre p = pairPre q) : p = q := by
  obtain ⟨h1, h2⟩ := nodePre_inj h
  exact Prod.ext h1 h2

/-- The node hash is keccak of the pair's node preimage. -/
theorem efficientHash_pair (keccak : Keccak) (p : UInt256 × UInt256) :
    efficientHash keccak p.1 p.2 = keccak (pairPre p) := rfl

theorem pair_collision_iff (keccak : Keccak) (p q : UInt256 × UInt256) :
    (p ≠ q ∧ efficientHash keccak p.1 p.2 = efficientHash keccak q.1 q.2)
      ↔ HashCollision keccak (pairPre p) (pairPre q) := by
  constructor
  · rintro ⟨hne, heq⟩
    exact ⟨fun h => hne (pairPre_inj h), heq⟩
  · rintro ⟨hne, heq⟩
    exact ⟨fun h => hne (by rw [h]), heq⟩

theorem pathCollision_iff (keccak : Keccak) (z0 : UInt256) (L : List UInt256)
    (sibs : ℕ → UInt256) (lvl k j : ℕ) (x : UInt256) :
    PathCollision (efficientHash keccak) z0 L sibs lvl k j x
      ↔ PathKeccakCollision keccak z0 L sibs lvl k j x :=
  exists_congr fun _ => and_congr_right fun _ => pair_collision_iff keccak _ _

theorem levelCollision_iff (keccak : Keccak) (z : UInt256) (L₁ L₂ : List UInt256) :
    LevelCollision (efficientHash keccak) z L₁ L₂
      ↔ ∃ m < (L₁.length + 1) / 2,
          HashCollision keccak (pairPre (parentPair z L₁ m)) (pairPre (parentPair z L₂ m)) :=
  exists_congr fun _ => and_congr_right fun _ => pair_collision_iff keccak _ _

theorem treeCollision_iff (keccak : Keccak) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (height i : ℕ) :
    TreeCollision (efficientHash keccak) z0 L₁ L₂ height i
      ↔ ∃ l < height,
          HashCollision keccak (pairPre (treePair (efficientHash keccak) z0 L₁ l (i / 2 ^ l)))
            (pairPre (treePair (efficientHash keccak) z0 L₂ l (i / 2 ^ l))) :=
  exists_congr fun _ => and_congr_right fun _ => pair_collision_iff keccak _ _

theorem walkCollision_iff (keccak : Keccak) (s₁ s₂ : ℕ → UInt256) (lvl k j : ℕ)
    (x y : UInt256) :
    WalkCollision (efficientHash keccak) s₁ s₂ lvl k j x y
      ↔ ∃ i < k,
          HashCollision keccak (pairPre (walkPair (efficientHash keccak) s₁ lvl j x i))
            (pairPre (walkPair (efficientHash keccak) s₂ lvl j y i)) :=
  exists_congr fun _ => and_congr_right fun _ => pair_collision_iff keccak _ _

theorem node_collision_lift : Properties.NodeCollisionLift := fun keccak =>
  ⟨pathCollision_iff keccak, fun _ _ _ _ => pair_collision_iff keccak _ _,
    levelCollision_iff keccak⟩

theorem tree_and_walk_collision_lift : Properties.TreeAndWalkCollisionLift := fun keccak =>
  ⟨treeCollision_iff keccak, walkCollision_iff keccak⟩

theorem node_collision_lift_witness : Properties.NodeCollisionLiftWitness := by
  intro keccak
  refine ⟨fun z0 L height j hc => ?_, fun z L ⟨_, _, hne, _⟩ => hne rfl⟩
  exact honest_walk_no_collision (efficientHash keccak) z0 L height j
    ((pathCollision_iff keccak _ _ _ _ _ _ _).mpr hc)

/-! ## Trees over keccak of named preimages -/

theorem leafList_length (keccak : Keccak) (pre : ℕ → List UInt8) (n : ℕ) :
    (leafList keccak pre n).length = n := by
  simp [leafList]

theorem leafList_getD (keccak : Keccak) (pre : ℕ → List UInt8) (n : ℕ) (zPre : List UInt8)
    (m : ℕ) : (leafList keccak pre n).getD m (keccak zPre) = keccak (entryPre pre n zPre m) := by
  unfold entryPre
  split_ifs with hm
  · simp [leafList, List.getElem?_range hm]
  · exact getD_default _ _ _ (by rw [leafList_length]; omega)

theorem mem_leafList {keccak : Keccak} {pre : ℕ → List UInt8} {n : ℕ} {y : UInt256} :
    y ∈ leafList keccak pre n ↔ ∃ m < n, keccak (pre m) = y := by
  simp [leafList, List.mem_map, List.mem_range]

theorem entryPre_length_ne {pre : ℕ → List UInt8} {n : ℕ} {zPre xPre : List UInt8}
    (hD : LeafDomain pre n zPre xPre) (m : ℕ) : (entryPre pre n zPre m).length ≠ 64 := by
  unfold entryPre
  split_ifs with hm
  · exact hD.1 m hm
  · exact hD.2.1

/-- A 64-byte node preimage differs from any preimage that is not 64 bytes long. -/
theorem ne_pairPre_of_length_ne {x : List UInt8} (hx : x.length ≠ 64) (p : UInt256 × UInt256) :
    x ≠ pairPre p := ne_of_length_ne (by rw [pairPre_length]; exact hx)

/-! ## (d) The leaf/node and entry/empty premises -/

theorem accept_forces_height_hypotheses_up_to_collision :
    Properties.AcceptForcesHeightHypothesesUpToCollision := by
  intro keccak pre n zPre xPre hD
  refine ⟨?_, ?_, ?_⟩
  · intro y hy a b hab
    obtain ⟨m, hm, rfl⟩ := mem_leafList.mp hy
    exact ⟨m, hm, rfl, ne_pairPre_of_length_ne (hD.1 m hm) (a, b), hab⟩
  · intro a b hab
    exact ⟨ne_pairPre_of_length_ne hD.2.1 (a, b), hab⟩
  · intro a b hab
    exact ⟨ne_pairPre_of_length_ne hD.2.2 (a, b), hab⟩

theorem tree_leaf_domains : Properties.TreeLeafDomains := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro logs n log
    refine ⟨fun m _ => ?_, ?_, ?_⟩
    · show (logPre (logs m)).length ≠ 64
      rw [logPre_length]; decide
    · rw [logDefaultPre_length]; decide
    · rw [logPre_length]; decide
  · intro padB B n b
    refine ⟨fun m _ => ?_, ?_, ?_⟩
    · show (batchPre padB _ _ _).length ≠ 64
      rw [batchPre_length]; decide
    · rw [emptyPre_length]; decide
    · rw [batchPre_length]; decide
  · intro padC C n c
    refine ⟨fun m _ => ?_, ?_, ?_⟩
    · show (chainIdPre padC _ _).length ≠ 64
      rw [chainIdPre_length]; decide
    · rw [emptyPre_length]; decide
    · rw [chainIdPre_length]; decide
  · intro T ℓ
    refine ⟨fun m _ => ?_, ?_, ?_⟩
    · show (imtPre (T.leaf m)).length ≠ 64
      rw [imtPre_length]; decide
    · rw [pinPaddingPre, imtPre_length]; decide
    · rw [imtPre_length]; decide
  · intro T ℓ
    refine ⟨fun m _ => ?_, ?_, ?_⟩
    · show (imtPre (T.leaf m)).length ≠ 64
      rw [imtPre_length]; decide
    · rw [imtEmptyLeafPre_length]; decide
    · rw [imtPre_length]; decide

theorem tree_entry_domains : Properties.TreeEntryDomains := by
  refine ⟨?_, ?_, ?_⟩
  · intro padB B n m _
    exact ne_of_length_ne (by
      show (batchPre padB _ _ _).length ≠ emptyPre.length
      rw [batchPre_length, emptyPre_length]; decide)
  · intro padC C n hpad m _
    exact chainIdPre_ne_emptyPre hpad
  · intro T m _
    exact ne_of_length_ne (by
      show (imtPre (T.leaf m)).length ≠ imtEmptyLeafPre.length
      rw [imtPre_length, imtEmptyLeafPre_length]; decide)

theorem entries_not_empty_or_collision : Properties.EntriesNotEmptyOrCollision := by
  intro keccak pre n zPre hE
  by_cases h : ∃ m < n, keccak (pre m) = keccak zPre
  · obtain ⟨m, hm, heq⟩ := h
    exact Or.inr ⟨m, hm, hE m hm, heq⟩
  · left
    intro m hm heq
    rw [leafList_length] at hm
    rw [leafList_getD, entryPre, ite_eq_left hm] at heq
    exact h ⟨m, hm, heq⟩

theorem chain_tree_entries_not_empty_or_collision :
    Properties.ChainTreeEntriesNotEmptyOrCollision :=
  fun keccak padB B n =>
    entries_not_empty_or_collision keccak (chainTreePre padB B) n emptyPre
      (tree_entry_domains.1 padB B n)

theorem lengthKeccak_of_length {x : List UInt8} {n : ℕ} (h : x.length = n) :
    lengthKeccak x = Nat.toUInt256 n := by
  unfold lengthKeccak
  rw [h]

theorem lengthKeccak_node (a b : UInt256) :
    efficientHash lengthKeccak a b = Nat.toUInt256 64 :=
  lengthKeccak_of_length (nodePre_length a b)

theorem tree_domains_witness : Properties.TreeDomainsWitness := by
  intro padB B n b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy a c
    obtain ⟨m, _, rfl⟩ := mem_leafList.mp hy
    simp only [chainTreePre]
    rw [lengthKeccak_node, lengthKeccak_of_length (batchPre_length _ _ _ _)]
    decide
  · intro a c
    rw [lengthKeccak_node, lengthKeccak_of_length emptyPre_length]
    decide
  · intro a c
    rw [lengthKeccak_node, lengthKeccak_of_length (batchPre_length _ _ _ _)]
    decide
  · intro m hm heq
    rw [leafList_length] at hm
    rw [leafList_getD, entryPre, ite_eq_left hm] at heq
    simp only [chainTreePre] at heq
    rw [lengthKeccak_of_length (batchPre_length _ _ _ _),
      lengthKeccak_of_length emptyPre_length] at heq
    exact absurd heq (by decide)

theorem heightBreak_keccak {keccak : Keccak} {pre : ℕ → List UInt8} {n : ℕ}
    {zPre xPre : List UInt8} {sibs : ℕ → UInt256} {k height j : ℕ}
    (hD : LeafDomain pre n zPre xPre)
    (hb : HeightBreak (efficientHash keccak) (keccak zPre) (leafList keccak pre n) sibs k height j
      (keccak xPre)) :
    HeightKeccakBreak keccak pre n zPre sibs k height j xPre := by
  cases hb with
  | shortInteriorLeaf hk hx =>
    exact .leafIsNode hk ⟨ne_pairPre_of_length_ne hD.2.2 _, hx⟩
  | shortCollision hk hpc =>
    exact .shortCollision hk ((pathCollision_iff ..).mp hpc)
  | longEntryIsNode hk he =>
    refine .entryIsNode hk ⟨ne_pairPre_of_length_ne (entryPre_length_ne hD _) _, ?_⟩
    rw [← leafList_getD keccak pre n zPre]
    exact he
  | longCollision hk hpc =>
    exact .longCollision hk ((pathCollision_iff ..).mp hpc)

theorem height_break_is_keccak_collision : Properties.HeightBreakIsKeccakCollision :=
  fun _ _ _ _ _ _ _ _ _ hD hb => heightBreak_keccak hD hb

theorem accept_forces_height_or_keccak_break : Properties.AcceptForcesHeightOrKeccakBreak := by
  intro keccak pre n zPre xPre sibs k height j hD hj haccept
  exact (accept_forces_height_or_break _ _ _ sibs k height j _ hj haccept).imp_right
    (heightBreak_keccak hD)

theorem accept_opens_preimage_or_keccak_break : Properties.AcceptOpensPreimageOrKeccakBreak := by
  intro keccak pre n zPre xPre sibs k height j hD hj haccept
  rcases accept_pins_entry_any_length_or_break (efficientHash keccak) (keccak zPre)
      (leafList keccak pre n) sibs k height j (keccak xPre) hj haccept with
    ⟨hk, hget⟩ | ⟨hk, hc⟩ | hb
  · rw [leafList_getD] at hget
    by_cases he : entryPre pre n zPre j = xPre
    · exact Or.inl ⟨hk, he⟩
    · exact Or.inr (Or.inl ⟨hk, he, hget⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hk, (pathCollision_iff ..).mp hc⟩))
  · exact Or.inr (Or.inr (Or.inr (heightBreak_keccak hD hb)))

theorem honest_proof_no_keccak_break : Properties.HonestProofNoKeccakBreak := by
  intro keccak pre n zPre height j hjn hj
  have hget : (leafList keccak pre n).getD j (keccak zPre) = keccak (pre j) := by
    rw [leafList_getD, entryPre, ite_eq_left hjn]
  have he : entryPre pre n zPre j = pre j := by rw [entryPre, ite_eq_left hjn]
  refine ⟨?_, he, ?_, ?_, ?_⟩
  · have := honest_walk_root (efficientHash keccak) (keccak zPre) (leafList keccak pre n)
      height j hj
    rw [hget] at this
    exact this
  · rintro ⟨hne, -⟩
    exact hne he
  · intro hc
    apply honest_walk_no_collision (efficientHash keccak) (keccak zPre) (leafList keccak pre n)
      height j
    rw [hget]
    exact (pathCollision_iff ..).mpr hc
  · intro hb
    cases hb <;> omega

theorem four_words_eq {a b c d a' b' c' d' : List UInt8} (ha : a.length = 32)
    (ha' : a'.length = 32) (hb : b.length = 32) (hb' : b'.length = 32) (hc : c.length = 32)
    (hc' : c'.length = 32) (h : a ++ b ++ c ++ d = a' ++ b' ++ c' ++ d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [ha, ha', hb, hb', hc, hc'])
  obtain ⟨h3, h4, h5⟩ := three_words_eq ha ha' hb hb' h1
  exact ⟨h3, h4, h5, h2⟩

theorem batchPre_fields_inj {padB : UInt256} {b b' : BatchLeaf}
    (h : batchPre padB b.batchRoot b.batchNumber b.l1Timestamp
      = batchPre padB b'.batchRoot b'.batchNumber b'.l1Timestamp) : b = b' := by
  obtain ⟨-, h2, h3, h4⟩ := four_words_eq (w32_length _) (w32_length _) (w32_length _)
    (w32_length _) (w32_length _) (w32_length _) h
  have e2 := w32_inj h2
  have e3 := w32_inj h3
  have e4 := w32_inj h4
  cases b
  cases b'
  simp only at e2 e3 e4
  subst e2 e3 e4
  rfl

theorem chainIdPre_fields_inj {padC : UInt256} {c c' : ChainIdLeaf}
    (h : chainIdPre padC c.chainIdRoot c.chainId = chainIdPre padC c'.chainIdRoot c'.chainId) :
    c = c' := by
  obtain ⟨-, h2, h3⟩ :=
    three_words_eq (w32_length _) (w32_length _) (w32_length _) (w32_length _) h
  have e2 := w32_inj h2
  have e3 := w32_inj h3
  cases c
  cases c'
  simp only at e2 e3
  subst e2 e3
  rfl

theorem batch_and_chain_id_preimages_injective :
    Properties.BatchAndChainIdPreimagesInjective :=
  ⟨fun _ _ _ h => batchPre_fields_inj h, fun _ _ _ h => chainIdPre_fields_inj h⟩

theorem accept_opens_occupied_preimage_or_keccak_break :
    Properties.AcceptOpensOccupiedPreimageOrKeccakBreak := by
  intro keccak pre n zPre xPre sibs k height j hD hxz hj haccept
  rcases accept_opens_preimage_or_keccak_break keccak pre n zPre xPre sibs k height j hD hj
      haccept with ⟨hk, he⟩ | h | h | h
  · by_cases hjn : j < n
    · rw [entryPre, ite_eq_left hjn] at he
      exact Or.inl ⟨hk, hjn, he⟩
    · rw [entryPre, ite_eq_right hjn] at he
      exact absurd he.symm hxz
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem chain_tree_proof_opens_batch_or_keccak_break :
    Properties.ChainTreeProofOpensBatchOrKeccakBreak := by
  intro keccak padB B n b sibs k height j hj haccept
  have hxz : batchPre padB b.batchRoot b.batchNumber b.l1Timestamp ≠ emptyPre :=
    ne_of_length_ne (by rw [batchPre_length, emptyPre_length]; decide)
  rcases accept_opens_occupied_preimage_or_keccak_break keccak (chainTreePre padB B) n emptyPre _
      sibs k height j (tree_leaf_domains.2.1 padB B n b) hxz hj haccept with
    ⟨hk, hjn, he⟩ | h | h | h
  · exact Or.inl ⟨hk, hjn, batchPre_fields_inj (b := B j) (b' := b) he⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem shared_tree_proof_opens_chain_or_keccak_break :
    Properties.SharedTreeProofOpensChainOrKeccakBreak := by
  intro keccak padC C n c sibs k height j hpad hj haccept
  rcases accept_opens_occupied_preimage_or_keccak_break keccak (sharedTreePre padC C) n emptyPre _
      sibs k height j (tree_leaf_domains.2.2.1 padC C n c) (chainIdPre_ne_emptyPre hpad) hj
      haccept with
    ⟨hk, hjn, he⟩ | h | h | h
  · exact Or.inl ⟨hk, hjn, chainIdPre_fields_inj (c := C j) (c' := c) he⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem tree_proof_opens_witness : Properties.TreeProofOpensWitness := by
  intro keccak padB B C
  obtain ⟨hacc₁, -, hnc₁, hnp₁, -⟩ := honest_proof_no_keccak_break keccak (chainTreePre padB B) 2
    emptyPre 1 1 (by norm_num) (by norm_num)
  obtain ⟨hacc₂, -, hnc₂, hnp₂, -⟩ := honest_proof_no_keccak_break keccak (sharedTreePre 1 C) 2
    emptyPre 1 1 (by norm_num) (by norm_num)
  exact ⟨⟨hacc₁, hnc₁, hnp₁⟩, ⟨by decide, hacc₂, hnc₂, hnp₂⟩⟩

theorem pinnedBreak_keccak {keccak : Keccak} {pre : ℕ → List UInt8} {n : ℕ} {zPre : List UInt8}
    {j : ℕ} (hE : EntryDomain pre n zPre)
    (hb : PinnedBreak (efficientHash keccak) (keccak zPre) (leafList keccak pre n) j) :
    PinnedKeccakBreak keccak pre n zPre j := by
  cases hb with
  | nodeCollision l m hj hm hne heq =>
    rw [leafList_length] at hj
    exact .nodeCollision l m hj hm ((pair_collision_iff keccak _ _).mp ⟨hne, heq⟩)
  | entryIsEmpty hj he =>
    rw [leafList_length] at hj
    rw [leafList_getD, entryPre, ite_eq_left hj] at he
    exact .entryIsEmpty hj ⟨hE _ hj, he⟩

theorem pinned_break_is_keccak_collision : Properties.PinnedBreakIsKeccakCollision :=
  fun _ _ _ _ _ hE hb => pinnedBreak_keccak hE hb

theorem accepted_last_leaf_or_keccak_break : Properties.AcceptedLastLeafOrKeccakBreak := by
  intro keccak pre n zPre sibs height j x hE hcap hj haccept hzero
  have hlen := leafList_length keccak pre n
  rcases accepted_last_leaf_or_pinned_break (efficientHash keccak) (keccak zPre)
      (leafList keccak pre n) sibs height j x (by rw [hlen]; exact hcap) (by rw [hlen]; exact hj)
      haccept hzero with h1 | h1 | h1
  · rw [hlen] at h1
    exact Or.inl h1
  · exact Or.inr (Or.inl (pinnedBreak_keccak hE h1))
  · exact Or.inr (Or.inr ((pathCollision_iff ..).mp h1))

theorem accepted_last_batch_or_keccak_break : Properties.AcceptedLastBatchOrKeccakBreak := by
  intro keccak padB B n sibs height j x hcap hj haccept hzero
  exact accepted_last_leaf_or_keccak_break keccak (chainTreePre padB B) n emptyPre sibs height j x
    (tree_entry_domains.1 padB B n) hcap hj haccept hzero

theorem accept_opens_preimage_witness : Properties.AcceptOpensPreimageWitness := by
  intro keccak
  let B : ℕ → BatchLeaf := fun _ => ⟨0, 0, 0⟩
  obtain ⟨hacc, he, hnc, hnp, hnh⟩ :=
    honest_proof_no_keccak_break keccak (chainTreePre 0 B) 2 emptyPre 1 1 (by norm_num)
      (by norm_num)
  exact ⟨chainTreePre 0 B, 2, emptyPre, chainTreePre 0 B 1, _, 1, 1, 1,
    (tree_leaf_domains.2.1 0 B 2 ⟨0, 0, 0⟩), by norm_num, by norm_num, hacc, ⟨rfl, he⟩, hnc,
    hnp, hnh⟩

/-- `m · 2^(l+1)` is even, so it is never `1`. -/
theorem mul_two_pow_succ_ne_one (l m : ℕ) : m * 2 ^ (l + 1) ≠ 1 := by
  have h2 : 2 ∣ m * 2 ^ (l + 1) := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) m
  omega

theorem accepted_last_batch_witness : Properties.AcceptedLastBatchWitness := by
  refine ⟨fun keccak padB B => ?_, fun padB B => ?_⟩
  · have hget : (leafList keccak (chainTreePre padB B) 2).getD 1 (emptyEntryHash keccak)
        = keccak (chainTreePre padB B 1) := by
      rw [emptyEntryHash, leafList_getD, entryPre, ite_eq_left (by norm_num)]
    refine ⟨by norm_num, by norm_num, ?_, ?_, ⟨1, by norm_num, by norm_num⟩⟩
    · have := honest_walk_root (efficientHash keccak) (emptyEntryHash keccak)
        (leafList keccak (chainTreePre padB B) 2) 2 1 (by norm_num)
      rw [hget] at this
      exact this
    · intro l hl hpar
      interval_cases l
      · norm_num at hpar
      · rfl
  · have hget : (leafList lengthKeccak (chainTreePre padB B) 2).getD 0 (emptyEntryHash lengthKeccak)
        = lengthKeccak (chainTreePre padB B 0) := by
      rw [emptyEntryHash, leafList_getD, entryPre, ite_eq_left (by norm_num)]
    refine ⟨?_, ?_⟩
    · have := honest_walk_root (efficientHash lengthKeccak) (emptyEntryHash lengthKeccak)
        (leafList lengthKeccak (chainTreePre padB B) 2) 1 0 (by norm_num)
      rw [hget] at this
      exact this
    · rintro (h | h | h)
      · omega
      · cases h with
        | nodeCollision l m _ hm _ => exact mul_two_pow_succ_ne_one l m hm
        | entryIsEmpty _ hc =>
          have := hc.2
          simp only [chainTreePre] at this
          rw [lengthKeccak_of_length (batchPre_length _ _ _ _),
            lengthKeccak_of_length emptyPre_length] at this
          exact absurd this (by decide)
      · apply honest_walk_no_collision (efficientHash lengthKeccak) (emptyEntryHash lengthKeccak)
          (leafList lengthKeccak (chainTreePre padB B) 2) 1 0
        rw [hget]
        exact (pathCollision_iff ..).mpr h

/-! ## (c) The IMT: `HashAssumptions` at the pin, and the root check down to keccak -/

theorem hash_assumptions_fields_up_to_collision : Properties.HashAssumptionsFieldsUpToCollision := by
  intro keccak
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b c d h
    by_cases he : nodePre a b = nodePre c d
    · exact Or.inl (nodePre_inj he)
    · exact Or.inr ⟨he, h⟩
  · intro ℓ ℓ' hℓ hℓ' h
    by_cases he : imtPre ℓ = imtPre ℓ'
    · exact Or.inl (imtPre_inj hℓ hℓ' he)
    · exact Or.inr ⟨he, h⟩
  · intro ℓ a b h
    exact ⟨ne_pairPre_of_length_ne (by rw [imtPre_length]; decide) (a, b), h⟩
  · intro ℓ hℓ
    constructor
    · intro h
      by_cases hz : ℓ = ⟨0, 0, 0⟩
      · exact Or.inl hz
      · refine Or.inr ⟨fun he => hz ((imtPre_eq_emptyPre_iff hℓ).mp he), ?_⟩
        rw [← imtPre_zero]
        exact h
    · rintro (rfl | ⟨-, h⟩)
      · rfl
      · show keccak (imtPre ℓ) = keccak (imtPre ⟨0, 0, 0⟩)
        rw [imtPre_zero]
        exact h
  · intro a b h
    refine ⟨ne_pairPre_of_length_ne (by rw [emptyPre_length]; decide) (a, b), ?_⟩
    rw [← imtPre_zero]
    exact h

theorem constKeccak_apply (x : List UInt8) : constKeccak x = 0 := rfl

theorem commit_leaf_not_chain_id_leaf_witness : Properties.CommitLeafNotChainIdLeafWitness := by
  refine ⟨⟨constKeccak, 0, 0, 0, 0, 0, 0, 0, ?_⟩, ?_⟩
  · simp only [constKeccak_apply]
    rfl
  · intro tag f b hc
    have := hc.2
    rw [lengthKeccak_of_length (commitPre_length _ _ _),
      lengthKeccak_of_length chainIdLeafPaddingPre_length] at this
    exact absurd this (by decide)

theorem hash_assumptions_fields_witness : Properties.HashAssumptionsFieldsWitness := by
  refine ⟨fun _ _ _ => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [hashLeaf, efficientHash, constKeccak_apply]
  · simp only [imtPadding, hashLeaf, efficientHash, constKeccak_apply]
  · intro ℓ a b
    refine ⟨?_, ?_⟩
    · show lengthKeccak (imtPre ℓ) ≠ lengthKeccak (nodePre a b)
      rw [lengthKeccak_of_length (imtPre_length ℓ), lengthKeccak_of_length (nodePre_length a b)]
      decide
    · show lengthKeccak (imtPre ⟨0, 0, 0⟩) ≠ lengthKeccak (nodePre a b)
      rw [lengthKeccak_of_length (imtPre_length _), lengthKeccak_of_length (nodePre_length a b)]
      decide
  · intro keccak
    exact ⟨rfl, fun hc => hc.1 imtPre_zero⟩
  · intro ℓ _ hv
    refine ⟨?_, ?_⟩
    · show firstWordKeccak (imtPre ℓ) ≠ firstWordKeccak (imtPre ⟨0, 0, 0⟩)
      rw [firstWordKeccak_imtPre, firstWordKeccak_imtPre]
      exact hv
    · rintro ⟨-, h⟩
      rw [firstWordKeccak_imtPre, firstWordKeccak_emptyPre] at h
      exact hv h

/-- The IMT's leaf-hash list is the keccak tree over the stored leaves' preimages. -/
theorem leafHashes_hashLeaf (keccak : Keccak) (T : Tree) :
    leafHashes (hashLeaf keccak) T = leafList keccak (imtLeafPre T) T.leafCount := rfl

theorem imt_leafDomain {zPre : List UInt8} (hz : zPre.length ≠ 64) (T : Tree) (ℓ : Leaf) :
    LeafDomain (imtLeafPre T) T.leafCount zPre (imtPre ℓ) := by
  refine ⟨fun m _ => ?_, hz, ?_⟩
  · show (imtPre (T.leaf m)).length ≠ 64
    rw [imtPre_length]; decide
  · rw [imtPre_length]; decide

theorem treeRootBreak_keccak {keccak : Keccak} {zPre : List UInt8} {T : Tree} {height : ℕ}
    {sibs : ℕ → UInt256} {k idx : ℕ} {ℓ : Leaf} (hz : zPre.length ≠ 64) (hT : TreeBounded T)
    (hℓ : LeafBounded ℓ)
    (hb : TreeRootBreak (efficientHash keccak) (keccak zPre) (hashLeaf keccak) T height sibs k idx ℓ) :
    (T.leafCount ≤ idx ∧ imtPre ℓ = zPre) ∨ ImtKeccakBreak keccak zPre T height sibs k idx ℓ := by
  cases hb with
  | wrongLength hh =>
    rw [leafHashes_hashLeaf] at hh
    exact Or.inr (.wrongLength (heightBreak_keccak (imt_leafDomain hz T ℓ) hh))
  | pathCollision hk hc =>
    rw [leafHashes_hashLeaf] at hc
    exact Or.inr (.pathCollision hk ((pathCollision_iff ..).mp hc))
  | leafCollision hidx hne heq =>
    exact Or.inr (.leafCollision hidx ⟨fun he => hne (imtPre_inj (hT _ hidx) hℓ he), heq⟩)
  | paddingHit hle heq =>
    by_cases he : imtPre ℓ = zPre
    · exact Or.inl ⟨hle, he⟩
    · exact Or.inr (.paddingCollision hle ⟨he, heq⟩)

theorem tree_root_break_is_keccak_collision : Properties.TreeRootBreakIsKeccakCollision :=
  fun _ _ _ _ _ _ _ _ hz hT hℓ hb => treeRootBreak_keccak hz hT hℓ hb

theorem pinPaddingPre_length_ne : pinPaddingPre.length ≠ 64 := by
  rw [pinPaddingPre, imtPre_length]; decide

theorem tree_root_break_is_keccak_collision_at_pin :
    Properties.TreeRootBreakIsKeccakCollisionAtPin := by
  intro keccak T height sibs k idx ℓ hT hℓ hb
  rcases treeRootBreak_keccak (zPre := pinPaddingPre) pinPaddingPre_length_ne hT hℓ hb with
    ⟨hle, he⟩ | hk
  · exact Or.inl ⟨hle, imtPre_inj hℓ zero_leafBounded he⟩
  · exact Or.inr hk

theorem proofs_exclusive_or_keccak_break_at_pin : Properties.ProofsExclusiveOrKeccakBreakAtPin := by
  intro keccak T hV hT height v ℓ₁ ℓ₂ i₁ i₂ s₁ s₂ k₁ k₂ hℓ₁ hℓ₂ hI hN
  rcases Contracts.InteropCommitmentTree.proofs_exclusive_or_break hV hI hN with hb | hb
  · rcases tree_root_break_is_keccak_collision_at_pin keccak T height s₁ k₁ i₁ ℓ₁ hT hℓ₁ hb with
      ⟨_, hz⟩ | hk
    · exfalso
      apply hN.nonzero
      rw [← hI.valueMatch, hz]
    · exact Or.inr (Or.inl hk)
  · rcases tree_root_break_is_keccak_collision_at_pin keccak T height s₂ k₂ i₂ ℓ₂ hT hℓ₂ hb with
      h | hk
    · exact Or.inl h
    · exact Or.inr (Or.inr hk)

theorem proofs_exclusive_or_keccak_break : Properties.ProofsExclusiveOrKeccakBreak := by
  intro keccak zPre hz64 hz96 T hV hT height v ℓ₁ ℓ₂ i₁ i₂ s₁ s₂ k₁ k₂ hℓ₁ hℓ₂ hI hN
  have hno : ∀ ℓ : Leaf, imtPre ℓ ≠ zPre := fun ℓ he => hz96 (by rw [← he, imtPre_length])
  rcases Contracts.InteropCommitmentTree.proofs_exclusive_or_break hV hI hN with hb | hb
  · rcases treeRootBreak_keccak hz64 hT hℓ₁ hb with ⟨_, he⟩ | hk
    · exact absurd he (hno ℓ₁)
    · exact Or.inl hk
  · rcases treeRootBreak_keccak hz64 hT hℓ₂ hb with ⟨_, he⟩ | hk
    · exact absurd he (hno ℓ₂)
    · exact Or.inr hk

/-- A valid tree holds the value `0`: the sentinel. -/
theorem zero_mem_keys_of_valid {T : Tree} (hV : Valid T) :
    (0 : UInt256) ∈ IMTAbstract.keys (Contracts.InteropCommitmentTree.toAbs T) :=
  Finset.mem_image.mpr ⟨⟨(T.leaf 0).value, (T.leaf 0).nextValue⟩,
    Contracts.InteropCommitmentTree.mem_toAbs.mpr ⟨0, hV.occupied, rfl, rfl⟩, hV.sentinel⟩

theorem inclusion_sound_or_keccak_break_at_pin : Properties.InclusionSoundOrKeccakBreakAtPin := by
  intro keccak T hV hT height v ℓ idx sibs k hℓ hI
  rcases Contracts.InteropCommitmentTree.inclusion_sound_or_break hI with hmem | hb
  · exact Or.inl hmem
  · rcases tree_root_break_is_keccak_collision_at_pin keccak T height sibs k idx ℓ hT hℓ hb with
      ⟨_, hz⟩ | hk
    · left
      have hv : v = 0 := by rw [← hI.valueMatch, hz]
      rw [hv]
      exact zero_mem_keys_of_valid hV
    · exact Or.inr hk

theorem non_inclusion_sound_or_keccak_break_at_pin :
    Properties.NonInclusionSoundOrKeccakBreakAtPin := by
  intro keccak T height v ℓ idx sibs k hT hℓ hN
  rcases Contracts.InteropCommitmentTree.non_inclusion_sound_or_break hN with hW | hb
  · exact Or.inl hW
  · rcases tree_root_break_is_keccak_collision_at_pin keccak T height sibs k idx ℓ hT hℓ hb with
      h | hk
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr hk)

theorem non_inclusion_sound_or_keccak_break : Properties.NonInclusionSoundOrKeccakBreak := by
  intro keccak zPre hz64 hz96 T height v ℓ idx sibs k hT hℓ hN
  rcases Contracts.InteropCommitmentTree.non_inclusion_sound_or_break hN with hW | hb
  · exact Or.inl hW
  · rcases treeRootBreak_keccak hz64 hT hℓ hb with ⟨_, he⟩ | hk
    · exact absurd (by rw [← he, imtPre_length]) hz96
    · exact Or.inr hk

theorem upg_padding_length_ok : Properties.UpgPaddingLengthOk := by
  unfold Properties.UpgPaddingLengthOk
  rw [imtEmptyLeafPre_length]
  decide

theorem imt_keccak_break_not_tautology : Properties.ImtKeccakBreakNotTautology := by
  intro keccak zPre T height i hi hk
  cases hk with
  | wrongLength hh => cases hh <;> omega
  | pathCollision _ hc =>
    apply honest_walk_no_collision (efficientHash keccak) (keccak zPre)
      (leafList keccak (imtLeafPre T) T.leafCount) height i
    rw [leafList_getD, entryPre, ite_eq_left hi]
    exact (pathCollision_iff ..).mpr hc
  | leafCollision _ hc => exact hc.1 rfl
  | paddingCollision hle _ => omega

theorem non_inclusion_sound_witness : Properties.NonInclusionSoundWitness := by
  intro keccak zPre
  have hset : TreeBounded setup := fun _ _ => zero_leafBounded
  refine ⟨hset, zero_leafBounded, ⟨by decide, by decide, Or.inl rfl, ⟨by norm_num, rfl⟩⟩, ?_, ?_⟩
  · exact imt_keccak_break_not_tautology keccak zPre setup 0 0 (by decide)
  · exact ⟨⟨0, 0⟩, by simp, by decide, Or.inl rfl⟩

theorem threeLeafTree_bounded (a b : UInt256) : TreeBounded (threeLeafTree a b) := by
  intro i hi
  have hcount : (threeLeafTree a b).leafCount = 3 := rfl
  rw [hcount] at hi
  show ((threeLeafTree a b).leaf i).nextIndex < 256 ^ 32
  interval_cases i <;>
    simp [threeLeafTree, Contracts.InteropCommitmentTree.insert, setup]

theorem padding_forgery_is_the_only_keccak_free_break :
    Properties.PaddingForgeryIsTheOnlyKeccakFreeBreak := by
  intro keccak a b ha hab
  obtain ⟨hV, hI, hN⟩ := Contracts.InteropCommitmentTree.proofs_exclusive_or_break_satisfiable
    (efficientHash keccak) (hashLeaf keccak) a b ha hab
  obtain ⟨_, hbreak⟩ := Contracts.InteropCommitmentTree.padding_countermodel_locates_padding_hit
    (efficientHash keccak) (hashLeaf keccak) a b
  have hT := threeLeafTree_bounded a b
  have hcount : (threeLeafTree a b).leafCount = 3 := rfl
  refine ⟨hV, hT, hT 1 (by rw [hcount]; norm_num), zero_leafBounded, hI, hN, hbreak, ?_, ?_⟩
  · exact imt_keccak_break_not_tautology keccak pinPaddingPre (threeLeafTree a b) 2 1
      (by rw [hcount]; norm_num)
  · intro hk
    cases hk with
    | wrongLength hh => cases hh <;> omega
    | pathCollision _ hc =>
      apply honest_walk_no_collision (efficientHash keccak) (imtPadding keccak)
        (leafHashes (hashLeaf keccak) (threeLeafTree a b)) 2 3
      rw [getD_default _ _ _ (by rw [Contracts.InteropCommitmentTree.leafHashes_length, hcount])]
      exact (pathCollision_iff ..).mpr hc
    | leafCollision hidx _ =>
      rw [hcount] at hidx
      omega
    | paddingCollision _ hc => exact hc.1 rfl

theorem proofs_exclusive_or_keccak_break_satisfiable :
    Properties.ProofsExclusiveOrKeccakBreakSatisfiable := by
  obtain ⟨hV, -, -⟩ := Contracts.InteropCommitmentTree.proofs_exclusive_or_break_satisfiable
    (efficientHash constKeccak) (hashLeaf constKeccak) 1 2 (by decide) (by decide)
  refine ⟨constKeccak, imtEmptyLeafPre, threeLeafTree 1 2, 2, 1, (threeLeafTree 1 2).leaf 1,
    ⟨0, 0, 0⟩, 1, 3, fun _ => 0, fun _ => 0, 2, 2, upg_padding_length_ok.1,
    upg_padding_length_ok.2, hV, threeLeafTree_bounded 1 2, threeLeafTree_bounded 1 2 1 (by decide),
    zero_leafBounded, ?_, ?_⟩
  · exact ⟨Contracts.InteropCommitmentTree.threeLeafTree_leaf_one_value 1 2, ⟨by norm_num, rfl⟩⟩
  · exact ⟨by decide, by decide, Or.inl rfl, ⟨by norm_num, rfl⟩⟩

theorem imt_keccak_break_fires : Properties.ImtKeccakBreakFires := by
  have hb5 : LeafBounded ⟨5, 0, 0⟩ := by
    show (0 : ℕ) < 256 ^ 32
    norm_num
  have hne : (⟨0, 0, 0⟩ : Leaf) ≠ ⟨5, 0, 0⟩ := by decide
  have hset : TreeBounded setup := fun _ _ => zero_leafBounded
  refine ⟨constKeccak, imtEmptyLeafPre, 1, fun _ => 0, 1, 0, ⟨5, 0, 0⟩, upg_padding_length_ok.1,
    hset, hb5, ⟨rfl, ⟨by norm_num, rfl⟩⟩, hne.symm, ?_, ?_, ?_⟩
  · exact .leafCollision (by decide) hne rfl
  · rintro ⟨hle, -⟩
    exact absurd hle (by decide)
  · exact .leafCollision (by decide)
      ⟨fun he => hne (imtPre_inj zero_leafBounded hb5 he), rfl⟩

end MerkleSpec.DomainSeparation

/-! ## Certificates -/

namespace MerkleSpec.DomainSeparation

/-! ### (a) Lengths -/

theorem PreimageLengths : Properties.PreimageLengths := preimage_lengths

theorem CrossLengthEqIsCollision : Properties.CrossLengthEqIsCollision :=
  cross_length_eq_is_collision

theorem CrossLengthEqIsCollisionWitness : Properties.CrossLengthEqIsCollisionWitness :=
  cross_length_eq_is_collision_witness

/-! ### (b) The 96-byte family -/

theorem PinPaddingIsEmptyPre : Properties.PinPaddingIsEmptyPre := pinPaddingPre_eq

theorem ImtPreEqEmptyPreIff : Properties.ImtPreEqEmptyPreIff :=
  fun _ hℓ => imtPre_eq_emptyPre_iff hℓ

theorem ChainIdPreNeEmptyPre : Properties.ChainIdPreNeEmptyPre :=
  fun _ _ _ hpad => chainIdPre_ne_emptyPre hpad

theorem ImtPreNeChainIdPreUnlessPadding : Properties.ImtPreNeChainIdPreUnlessPadding :=
  fun _ _ _ _ hv => imtPre_ne_chainIdPre hv

theorem ImtPreEqChainIdPreIff : Properties.ImtPreEqChainIdPreIff :=
  fun _ _ _ _ hℓ => imtPre_eq_chainIdPre_iff hℓ

theorem CommitLeafNotChainIdLeafOrCollision : Properties.CommitLeafNotChainIdLeafOrCollision :=
  commit_leaf_not_chain_id_leaf_or_collision

theorem CommitLeafNotChainIdLeafWitness : Properties.CommitLeafNotChainIdLeafWitness :=
  commit_leaf_not_chain_id_leaf_witness

theorem CommitPreIsThreeWords : Properties.CommitPreIsThreeWords := commitPre_eq_words

theorem CommitPreNeEmptyPre : Properties.CommitPreNeEmptyPre :=
  fun _ _ _ ht hne => commitPre_ne_emptyPre ht hne

theorem CommitPreNeImtPreUnlessTag : Properties.CommitPreNeImtPreUnlessTag :=
  fun _ _ _ _ ht hv => commitPre_ne_imtPre ht hv

theorem CommitPreNeChainIdPreUnlessTag : Properties.CommitPreNeChainIdPreUnlessTag :=
  fun _ _ _ _ _ _ ht hv => commitPre_ne_chainIdPre ht hv

theorem NinetySixByteFamilyWitness : Properties.NinetySixByteFamilyWitness :=
  ninety_six_byte_family_witness

theorem EmptyConstantsCoincide : Properties.EmptyConstantsCoincide := empty_constants_coincide

theorem KeccakOfEmptyIsDocumentedSatisfiable : Properties.KeccakOfEmptyIsDocumentedSatisfiable :=
  keccak_of_empty_is_documented_satisfiable

theorem LogDefaultIsZeroLog : Properties.LogDefaultIsZeroLog := log_default_is_zero_log

/-! ### (c) The IMT -/

theorem HashAssumptionsFieldsUpToCollision : Properties.HashAssumptionsFieldsUpToCollision :=
  hash_assumptions_fields_up_to_collision

theorem HashAssumptionsFieldsWitness : Properties.HashAssumptionsFieldsWitness :=
  hash_assumptions_fields_witness

theorem TreeRootBreakIsKeccakCollision : Properties.TreeRootBreakIsKeccakCollision :=
  tree_root_break_is_keccak_collision

theorem TreeRootBreakIsKeccakCollisionAtPin : Properties.TreeRootBreakIsKeccakCollisionAtPin :=
  tree_root_break_is_keccak_collision_at_pin

theorem ProofsExclusiveOrKeccakBreakAtPin : Properties.ProofsExclusiveOrKeccakBreakAtPin :=
  proofs_exclusive_or_keccak_break_at_pin

theorem ProofsExclusiveOrKeccakBreak : Properties.ProofsExclusiveOrKeccakBreak :=
  proofs_exclusive_or_keccak_break

theorem InclusionSoundOrKeccakBreakAtPin : Properties.InclusionSoundOrKeccakBreakAtPin :=
  inclusion_sound_or_keccak_break_at_pin

theorem NonInclusionSoundOrKeccakBreakAtPin : Properties.NonInclusionSoundOrKeccakBreakAtPin :=
  non_inclusion_sound_or_keccak_break_at_pin

theorem NonInclusionSoundOrKeccakBreak : Properties.NonInclusionSoundOrKeccakBreak :=
  non_inclusion_sound_or_keccak_break

theorem NonInclusionSoundWitness : Properties.NonInclusionSoundWitness :=
  non_inclusion_sound_witness

theorem UpgPaddingLengthOk : Properties.UpgPaddingLengthOk := upg_padding_length_ok

theorem PaddingForgeryIsTheOnlyKeccakFreeBreak :
    Properties.PaddingForgeryIsTheOnlyKeccakFreeBreak :=
  padding_forgery_is_the_only_keccak_free_break

theorem ProofsExclusiveOrKeccakBreakSatisfiable :
    Properties.ProofsExclusiveOrKeccakBreakSatisfiable :=
  proofs_exclusive_or_keccak_break_satisfiable

theorem ImtKeccakBreakNotTautology : Properties.ImtKeccakBreakNotTautology :=
  imt_keccak_break_not_tautology

theorem ImtKeccakBreakFires : Properties.ImtKeccakBreakFires := imt_keccak_break_fires

/-! ### (d) The other trees -/

theorem AcceptForcesHeightHypothesesUpToCollision :
    Properties.AcceptForcesHeightHypothesesUpToCollision :=
  accept_forces_height_hypotheses_up_to_collision

theorem TreeLeafDomains : Properties.TreeLeafDomains := tree_leaf_domains

theorem TreeEntryDomains : Properties.TreeEntryDomains := tree_entry_domains

theorem EntriesNotEmptyOrCollision : Properties.EntriesNotEmptyOrCollision :=
  entries_not_empty_or_collision

theorem ChainTreeEntriesNotEmptyOrCollision : Properties.ChainTreeEntriesNotEmptyOrCollision :=
  chain_tree_entries_not_empty_or_collision

theorem TreeDomainsWitness : Properties.TreeDomainsWitness := tree_domains_witness

theorem HeightBreakIsKeccakCollision : Properties.HeightBreakIsKeccakCollision :=
  height_break_is_keccak_collision

theorem AcceptForcesHeightOrKeccakBreak : Properties.AcceptForcesHeightOrKeccakBreak :=
  accept_forces_height_or_keccak_break

theorem AcceptOpensPreimageOrKeccakBreak : Properties.AcceptOpensPreimageOrKeccakBreak :=
  accept_opens_preimage_or_keccak_break

theorem HonestProofNoKeccakBreak : Properties.HonestProofNoKeccakBreak :=
  honest_proof_no_keccak_break

theorem AcceptOpensPreimageWitness : Properties.AcceptOpensPreimageWitness :=
  accept_opens_preimage_witness

theorem AcceptOpensOccupiedPreimageOrKeccakBreak :
    Properties.AcceptOpensOccupiedPreimageOrKeccakBreak :=
  accept_opens_occupied_preimage_or_keccak_break

theorem ChainTreeProofOpensBatchOrKeccakBreak : Properties.ChainTreeProofOpensBatchOrKeccakBreak :=
  chain_tree_proof_opens_batch_or_keccak_break

theorem SharedTreeProofOpensChainOrKeccakBreak :
    Properties.SharedTreeProofOpensChainOrKeccakBreak :=
  shared_tree_proof_opens_chain_or_keccak_break

theorem TreeProofOpensWitness : Properties.TreeProofOpensWitness := tree_proof_opens_witness

theorem BatchAndChainIdPreimagesInjective : Properties.BatchAndChainIdPreimagesInjective :=
  batch_and_chain_id_preimages_injective

theorem PinnedBreakIsKeccakCollision : Properties.PinnedBreakIsKeccakCollision :=
  pinned_break_is_keccak_collision

theorem AcceptedLastLeafOrKeccakBreak : Properties.AcceptedLastLeafOrKeccakBreak :=
  accepted_last_leaf_or_keccak_break

theorem AcceptedLastBatchOrKeccakBreak : Properties.AcceptedLastBatchOrKeccakBreak :=
  accepted_last_batch_or_keccak_break

theorem AcceptedLastBatchWitness : Properties.AcceptedLastBatchWitness :=
  accepted_last_batch_witness

/-! ### (e) The node-collision lift -/

theorem PairCollisionIsKeccakCollision : Properties.PairCollisionIsKeccakCollision :=
  pair_collision_iff

theorem NodeCollisionLift : Properties.NodeCollisionLift := node_collision_lift

theorem TreeAndWalkCollisionLift : Properties.TreeAndWalkCollisionLift :=
  tree_and_walk_collision_lift

theorem NodeCollisionLiftWitness : Properties.NodeCollisionLiftWitness :=
  node_collision_lift_witness

end MerkleSpec.DomainSeparation
