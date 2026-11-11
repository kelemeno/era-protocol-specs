import EraSpec.Contracts.L2InteropCommitmentTree.Properties.PaddingAtHead
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.CachedRoot
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashPinned

/-!
# Proofs: at `main`, an accepted absence proof means absent, or a named keccak collision

Proofs of `EraSpec.Contracts.L2InteropCommitmentTree.Properties.PaddingAtHead`.

The `FullMerkle` and `TreeRoot` content is padding-generic and is reused as it stands:
`cInsert_caches` (any padding), `accept_pins_entry_any_length_or_break` (an accepted walk pins
the level-0 entry, or a located `PathCollision` / `HeightBreak`).  What this file adds:

* the byte-level facts: the three keccak preimages have different lengths, a node preimage
  determines its pair, and a leaf preimage determines the leaf's `value` and `nextValue`;
* the reading of `PathCollision`, `HeightBreak` and `TreeRootBreak` at `main`'s hashes as keccak
  collisions;
* the setup with an independent padding constant, and the runs from it;
* the headline: from an accepted path, either the opened leaf has the presented leaf's `value`
  and `nextValue` (so the gap argument applies), or a `KeccakBreakAtHead`;
* the pin's three-leaf countermodel at `main`, and a toy keccak on which the forged proof is
  accepted with the pin's padding and rejected with `main`'s.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier AttackVectors.CapacityInvariant
open AttackVectors.BundleHashEncoding (word HashCollision word_length word_val_inj uint256_val_lt
  toUInt256_val fromBytesBE fromBytesBE_toBytesBE)

/-! ## The byte strings -/

theorem imtEmptyLeafTag_is_the_literal :
    imtEmptyLeafTag = "zkSync:IndexedMerkleTree:emptyLeaf".toList.map (fun c => c.toNat.toUInt8)
      ∧ (∀ c ∈ "zkSync:IndexedMerkleTree:emptyLeaf".toList, c.toNat < 128)
      ∧ imtEmptyLeafTag.length = 34 :=
  ⟨by decide, by decide, rfl⟩

lemma imtLeafPreimage_length (ℓ : Leaf) : (imtLeafPreimage ℓ).length = 96 := by
  simp [imtLeafPreimage]

lemma imtNodePreimage_length (a b : UInt256) : (imtNodePreimage a b).length = 64 := by
  simp [imtNodePreimage]

lemma imtPairPreimage_length (p : UInt256 × UInt256) : (imtPairPreimage p).length = 64 :=
  imtNodePreimage_length p.1 p.2

lemma imtEmptyLeafTag_length : imtEmptyLeafTag.length = 34 := rfl

lemma imtLeafPreimage_ne_node (ℓ : Leaf) (a b : UInt256) : imtLeafPreimage ℓ ≠ imtNodePreimage a b := by
  intro h
  have := congrArg List.length h
  rw [imtLeafPreimage_length, imtNodePreimage_length] at this
  omega

lemma imtLeafPreimage_ne_pair (ℓ : Leaf) (p : UInt256 × UInt256) :
    imtLeafPreimage ℓ ≠ imtPairPreimage p :=
  imtLeafPreimage_ne_node ℓ p.1 p.2

lemma imtLeafPreimage_ne_tag (ℓ : Leaf) : imtLeafPreimage ℓ ≠ imtEmptyLeafTag := by
  intro h
  have := congrArg List.length h
  rw [imtLeafPreimage_length, imtEmptyLeafTag_length] at this
  omega

lemma imtNodePreimage_ne_tag (a b : UInt256) : imtNodePreimage a b ≠ imtEmptyLeafTag := by
  intro h
  have := congrArg List.length h
  rw [imtNodePreimage_length, imtEmptyLeafTag_length] at this
  omega

lemma imtEmptyLeafTag_ne_pair (p : UInt256 × UInt256) : imtEmptyLeafTag ≠ imtPairPreimage p :=
  fun h => imtNodePreimage_ne_tag p.1 p.2 h.symm

theorem imt_preimages_domain_separated :
    (∀ ℓ : Leaf, (imtLeafPreimage ℓ).length = 96)
      ∧ (∀ a b : UInt256, (imtNodePreimage a b).length = 64)
      ∧ (∀ (ℓ : Leaf) (a b : UInt256),
          imtLeafPreimage ℓ ≠ imtNodePreimage a b ∧ imtLeafPreimage ℓ ≠ imtEmptyLeafTag
            ∧ imtNodePreimage a b ≠ imtEmptyLeafTag) :=
  ⟨imtLeafPreimage_length, imtNodePreimage_length,
    fun ℓ a b => ⟨imtLeafPreimage_ne_node ℓ a b, imtLeafPreimage_ne_tag ℓ, imtNodePreimage_ne_tag a b⟩⟩

lemma imtNodePreimage_inj {a b c d : UInt256} (h : imtNodePreimage a b = imtNodePreimage c d) :
    a = c ∧ b = d := by
  have := List.append_inj h (by rw [word_length, word_length])
  exact ⟨word_val_inj this.1, word_val_inj this.2⟩

lemma imtPairPreimage_inj {p q : UInt256 × UInt256} (h : imtPairPreimage p = imtPairPreimage q) :
    p = q := by
  obtain ⟨h1, h2⟩ := imtNodePreimage_inj h
  exact Prod.ext h1 h2

lemma imtLeafPreimage_fields {ℓ₁ ℓ₂ : Leaf} (h : imtLeafPreimage ℓ₁ = imtLeafPreimage ℓ₂) :
    ℓ₁.value = ℓ₂.value ∧ ℓ₁.nextValue = ℓ₂.nextValue ∧ word ℓ₁.nextIndex = word ℓ₂.nextIndex := by
  have h1 := List.append_inj h (by rw [word_length, word_length])
  have h2 := List.append_inj h1.2 (by rw [word_length, word_length])
  exact ⟨word_val_inj h1.1, word_val_inj h2.2, h2.1⟩

lemma imtLeafPreimage_inj {ℓ₁ ℓ₂ : Leaf} (h₁ : ℓ₁.nextIndex < 2 ^ 256) (h₂ : ℓ₂.nextIndex < 2 ^ 256)
    (h : imtLeafPreimage ℓ₁ = imtLeafPreimage ℓ₂) : ℓ₁ = ℓ₂ := by
  obtain ⟨hv, hn, hi⟩ := imtLeafPreimage_fields h
  have e : (2 : ℕ) ^ 256 = 256 ^ 32 := by norm_num
  have hi' := congrArg fromBytesBE hi
  rw [fromBytesBE_toBytesBE (by rw [← e]; exact h₁), fromBytesBE_toBytesBE (by rw [← e]; exact h₂)]
    at hi'
  cases ℓ₁
  cases ℓ₂
  simp only at hv hn hi'
  rw [hv, hn, hi']

theorem imt_preimages_determine_their_inputs :
    (∀ a b c d : UInt256, imtNodePreimage a b = imtNodePreimage c d → a = c ∧ b = d)
      ∧ (∀ ℓ₁ ℓ₂ : Leaf, imtLeafPreimage ℓ₁ = imtLeafPreimage ℓ₂ →
          ℓ₁.value = ℓ₂.value ∧ ℓ₁.nextValue = ℓ₂.nextValue
            ∧ (ℓ₁.nextIndex < 2 ^ 256 → ℓ₂.nextIndex < 2 ^ 256 → ℓ₁ = ℓ₂)) :=
  ⟨fun _ _ _ _ h => imtNodePreimage_inj h,
    fun _ _ h => ⟨(imtLeafPreimage_fields h).1, (imtLeafPreimage_fields h).2.1,
      fun h₁ h₂ => imtLeafPreimage_inj h₁ h₂ h⟩⟩

/-! ## `TreeRoot`'s located break, read at `main`'s hashes -/

theorem pathCollision_at_head_iff_keccak (keccak : List UInt8 → UInt256) (z0 : UInt256)
    (L : List UInt256) (sibs : ℕ → UInt256) (lvl k j : ℕ) (x : UInt256) :
    PathCollision (imtNodeHash keccak) z0 L sibs lvl k j x
      ↔ PathKeccakCollision keccak z0 L sibs lvl k j x := by
  constructor
  · rintro ⟨i, hi, hne, heq⟩
    exact ⟨i, hi, fun h => hne (imtPairPreimage_inj h), heq⟩
  · rintro ⟨i, hi, hne, heq⟩
    exact ⟨i, hi, fun h => hne (by rw [h]), heq⟩

theorem heightBreak_at_head_iff_keccak (keccak : List UInt8 → UInt256) (T : Tree) (height : ℕ)
    (sibs : ℕ → UInt256) (k j : ℕ) (ℓ : Leaf) :
    HeightBreak (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtLevel0 keccak T) sibs k height
        j (imtHashLeaf keccak ℓ)
      ↔ LengthKeccakBreak keccak T height sibs k j ℓ := by
  constructor
  · intro hb
    cases hb with
    | shortInteriorLeaf hk he =>
      exact LengthKeccakBreak.shortLeafIsNode hk ⟨imtLeafPreimage_ne_pair _ _, he⟩
    | shortCollision hk hc =>
      exact LengthKeccakBreak.shortCollision hk ((pathCollision_at_head_iff_keccak ..).1 hc)
    | longEntryIsNode hk he =>
      by_cases hm : j / 2 ^ (k - height) < T.leafCount
      · rw [imtLevel0, leafHashes_getD hm] at he
        exact LengthKeccakBreak.longLeafIsNode hk hm ⟨imtLeafPreimage_ne_pair _ _, he⟩
      · rw [imtLevel0, getD_default _ _ _ (by rw [leafHashes_length]; omega)] at he
        exact LengthKeccakBreak.longEmptyLeafIsNode hk (by omega) ⟨imtEmptyLeafTag_ne_pair _, he⟩
    | longCollision hk hc =>
      exact LengthKeccakBreak.longCollision hk ((pathCollision_at_head_iff_keccak ..).1 hc)
  · intro hb
    cases hb with
    | shortLeafIsNode hk hc => exact HeightBreak.shortInteriorLeaf hk hc.2
    | shortCollision hk hc =>
      exact HeightBreak.shortCollision hk ((pathCollision_at_head_iff_keccak ..).2 hc)
    | longLeafIsNode hk hm hc =>
      refine HeightBreak.longEntryIsNode hk ?_
      rw [imtLevel0, leafHashes_getD hm]
      exact hc.2
    | longEmptyLeafIsNode hk hm hc =>
      refine HeightBreak.longEntryIsNode hk ?_
      rw [imtLevel0, getD_default _ _ _ (by rw [leafHashes_length]; omega)]
      exact hc.2
    | longCollision hk hc =>
      exact HeightBreak.longCollision hk ((pathCollision_at_head_iff_keccak ..).2 hc)

theorem keccakBreakAtHead_is_treeRootBreak (keccak : List UInt8 → UInt256) (T : Tree)
    (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf)
    (hb : KeccakBreakAtHead keccak T height sibs k idx ℓ) :
    TreeRootBreak (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtHashLeaf keccak) T height
      sibs k idx ℓ := by
  cases hb with
  | emptyLeaf _ hidx hc => exact TreeRootBreak.paddingHit hidx hc.2
  | leaf _ hidx hc => exact TreeRootBreak.leafCollision hidx (fun he => hc.1 (by rw [he])) hc.2
  | node hk hc => exact TreeRootBreak.pathCollision hk ((pathCollision_at_head_iff_keccak ..).2 hc)
  | length hl => exact TreeRootBreak.wrongLength ((heightBreak_at_head_iff_keccak ..).2 hl)

theorem paddingHit_at_head_iff_emptyLeaf_collision (keccak : List UInt8 → UInt256) (T : Tree)
    (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf) :
    TreeRootBreakAt (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtHashLeaf keccak) T height
        sibs k idx ℓ .paddingHit
      ↔ T.leafCount ≤ idx ∧ HashCollision keccak (imtLeafPreimage ℓ) imtEmptyLeafTag := by
  show T.leafCount ≤ idx ∧ keccak (imtLeafPreimage ℓ) = keccak imtEmptyLeafTag ↔ _
  exact ⟨fun ⟨hidx, he⟩ => ⟨hidx, imtLeafPreimage_ne_tag ℓ, he⟩, fun ⟨hidx, _, he⟩ => ⟨hidx, he⟩⟩

theorem paddingHit_at_pin_needs_no_collision (keccak : List UInt8 → UInt256) (T : Tree)
    (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ) (hidx : T.leafCount ≤ idx) :
    zeroLeafHash (imtHashLeaf keccak) = keccak (imtLeafPreimage ⟨0, 0, 0⟩)
      ∧ TreeRootBreakAt (imtNodeHash keccak) (zeroLeafHash (imtHashLeaf keccak))
          (imtHashLeaf keccak) T height sibs k idx ⟨0, 0, 0⟩ .paddingHit :=
  ⟨rfl, hidx, rfl⟩

theorem treeRootBreak_at_head_is_keccak_collision (keccak : List UInt8 → UInt256) (T : Tree)
    (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf) (hℓ : ℓ.nextIndex < 2 ^ 256)
    (hT : ∀ i < T.leafCount, (T.leaf i).nextIndex < 2 ^ 256)
    (hb : TreeRootBreak (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtHashLeaf keccak) T
      height sibs k idx ℓ) :
    (T.leafCount ≤ idx ∧ HashCollision keccak (imtLeafPreimage ℓ) imtEmptyLeafTag)
      ∨ (idx < T.leafCount ∧ HashCollision keccak (imtLeafPreimage (T.leaf idx)) (imtLeafPreimage ℓ))
      ∨ (k = height ∧ PathKeccakCollision keccak (imtEmptyLeafHash keccak) (imtLevel0 keccak T) sibs
          0 k idx (imtHashLeaf keccak ℓ))
      ∨ LengthKeccakBreak keccak T height sibs k idx ℓ := by
  cases hb with
  | wrongLength hh => exact Or.inr (Or.inr (Or.inr ((heightBreak_at_head_iff_keccak ..).1 hh)))
  | pathCollision hk hc =>
    exact Or.inr (Or.inr (Or.inl ⟨hk, (pathCollision_at_head_iff_keccak ..).1 hc⟩))
  | leafCollision hidx hne he =>
    exact Or.inr (Or.inl ⟨hidx, fun hp => hne (imtLeafPreimage_inj (hT idx hidx) hℓ hp), he⟩)
  | paddingHit hidx he => exact Or.inl ⟨hidx, imtLeafPreimage_ne_tag ℓ, he⟩

/-! ## With the tree's own siblings, one collision anywhere suffices -/

theorem honest_siblings_accept_exactly (h : Hash) (z0 : UInt256) (L : List UInt256)
    (height j : ℕ) (x : UInt256) (hj : j < 2 ^ height) :
    walkPure h (honestSibs h z0 L j) 0 height j x = rootOf h z0 L height
      ↔ L.getD j z0 = x ∨ PathCollision h z0 L (honestSibs h z0 L j) 0 height j x := by
  constructor
  · exact accept_pins_entry_or_collision h z0 L _ height j x hj
  · rintro (he | ⟨i, hi, _, heq⟩)
    · rw [← he]
      exact honest_walk_root h z0 L height j hj
    · obtain ⟨m, rfl⟩ : ∃ m, height = (i + 1) + m := ⟨height - (i + 1), by omega⟩
      rw [walkPure_add h _ (i + 1) m 0 j x, walkPure_succ_eq_walkPair h _ i 0 j x, heq,
        hash_treePair h z0 L (0 + i) (j / 2 ^ i)]
      have e1 : j / 2 ^ i / 2 = j / 2 ^ (i + 1) := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ]
      simp only [Nat.zero_add]
      rw [e1]
      have hsibs : ∀ l, i + 1 ≤ l → l < (i + 1) + m →
          honestSibs h z0 L j l
            = (levels h z0 L l).getD (sibIdx (j / 2 ^ (i + 1) / 2 ^ (l - (i + 1)))) (zeros h z0 l) := by
        intro l hl1 _
        have hidx : j / 2 ^ (i + 1) / 2 ^ (l - (i + 1)) = j / 2 ^ l := by
          rw [Nat.div_div_eq_div_mul, ← pow_add, show i + 1 + (l - (i + 1)) = l from by omega]
        rw [hidx]
        rfl
      rw [walkPure_levels_all h z0 (honestSibs h z0 L j) L m (i + 1) (j / 2 ^ (i + 1)) hsibs]
      have e2 : j / 2 ^ (i + 1) / 2 ^ m = 0 := by
        rw [Nat.div_div_eq_div_mul, ← pow_add]
        exact Nat.div_eq_of_lt hj
      rw [e2, getD_zero_headD, ← rootOf_def]

/-! ## The model: `setup` with an independent padding constant -/

lemma leafHashes_setup_pad (hl : LeafHash) : leafHashes hl setup = [] ++ [hl ⟨0, 0, 0⟩] := rfl

theorem cSetupPad_caches (h : Hash) (hl : LeafHash) (ze : UInt256) :
    ∃ S : CState, cSetupPad h hl ze = some S ∧ S.tree = setup ∧ S.toH = hSetup
      ∧ FullMerkle.Represents h ze (leafHashes hl S.tree) S.fm
      ∧ S.root = some (hl ⟨0, 0, 0⟩) := by
  have hR₀ := (FullMerkle.setup_represents_empty h ze).1
  obtain ⟨F, hp, hR, hd⟩ :=
    FullMerkle.pushNewLeaf_computes_root h ze [] _ (hl ⟨0, 0, 0⟩) hR₀
  have hF0 : F.height = 0 := congrArg TreeDims.height hd
  refine ⟨⟨setup, F⟩, ?_, rfl, ?_, ?_, ?_⟩
  · simp [cSetupPad, hp]
  · show (⟨setup, ⟨F.leafNumber, F.height⟩⟩ : HState) = ⟨setup, setupDims⟩
    rw [hd]
    rfl
  · rw [leafHashes_setup_pad]
    exact hR
  · show FullMerkle.root F = some (hl ⟨0, 0, 0⟩)
    rw [FullMerkle.root_is_fold h ze _ F hR, hF0]
    rfl

private lemma cReachesPad_caches {h : Hash} {hl : LeafHash} {ze : UInt256} {S : CState}
    (hS : CReachesPad h hl ze S) :
    HReaches hSetup S.toH ∧ FullMerkle.Represents h ze (leafHashes hl S.tree) S.fm := by
  induction hS with
  | init hs =>
    obtain ⟨S₀, hs₀, _, hH, hR, _⟩ := cSetupPad_caches h hl ze
    rw [hs] at hs₀
    cases hs₀
    exact ⟨hH ▸ HReaches.refl, hR⟩
  | @insert S S' v low r _ hg hins ih =>
    obtain ⟨hH, hR⟩ := ih
    obtain ⟨S'', r'', hins', _, htoH, hR'', _⟩ := cInsert_caches h ze hl S v low hR hg.inBounds
    rw [hins] at hins'
    obtain ⟨hS', _⟩ := Prod.mk.inj (Option.some.inj hins')
    subst hS'
    exact ⟨htoH ▸ HReaches.tail hH hg, hR''⟩

/-- `root()` of a state whose storage caches its leaf hashes is the published root of its
view. -/
private lemma root_eq_published_pad {h : Hash} {z0 : UInt256} {hl : LeafHash} {S : CState}
    (hR : FullMerkle.Represents h z0 (leafHashes hl S.tree) S.fm) :
    S.root = some (S.toH.root h z0 hl) := by
  rw [CState.root, FullMerkle.root_is_fold h z0 _ S.fm hR]
  rfl

theorem cReachesPad_root_is_published (h : Hash) (hl : LeafHash) (ze : UInt256) (S : CState)
    (hS : CReachesPad h hl ze S) :
    HReaches hSetup S.toH
      ∧ FullMerkle.Represents h ze (leafHashes hl S.tree) S.fm
      ∧ S.root = some (S.toH.root h ze hl) :=
  ⟨(cReachesPad_caches hS).1, (cReachesPad_caches hS).2, root_eq_published_pad (cReachesPad_caches hS).2⟩

theorem cRunPad_reaches (h : Hash) (hl : LeafHash) (ze : UInt256) (R : ℕ → CState)
    (hR : CRun h hl R) (h0 : cSetupPad h hl ze = some (R 0)) (n : ℕ) : CReachesPad h hl ze (R n) := by
  induction n with
  | zero => exact CReachesPad.init h0
  | succ n ih =>
    rcases hR n with heq | ⟨v, low, r, hg, hins⟩
    · rw [heq]
      exact ih
    · exact CReachesPad.insert ih hg hins

theorem pin_setup_is_pad_at_zeroLeafHash (h : Hash) (hl : LeafHash) :
    cSetup h hl = cSetupPad h hl (zeroLeafHash hl)
      ∧ ∀ S : CState, CReaches h hl S ↔ CReachesPad h hl (zeroLeafHash hl) S := by
  refine ⟨rfl, fun S => ⟨fun hS => ?_, fun hS => ?_⟩⟩
  · induction hS with
    | init h0 => exact CReachesPad.init h0
    | insert _ hg hins ih => exact CReachesPad.insert ih hg hins
  · induction hS with
    | init h0 => exact CReaches.init h0
    | insert _ hg hins ih => exact CReaches.insert ih hg hins

theorem cReachesPad_views_are_hReaches (h : Hash) (hl : LeafHash) (ze : UInt256) (U : HState) :
    (∃ S : CState, CReachesPad h hl ze S ∧ S.toH = U) ↔ HReaches hSetup U := by
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact (cReachesPad_caches hS).1
  · intro hU
    induction hU with
    | refl =>
      obtain ⟨C, hC, _, hH, _, _⟩ := cSetupPad_caches h hl ze
      exact ⟨C, CReachesPad.init hC, hH⟩
    | @tail U _ v low hg ih =>
      obtain ⟨C, hC, hCU⟩ := ih
      have hg' : InsertGuard C.tree v low := by
        have : C.tree = U.tree := congrArg HState.tree hCU
        rw [this]
        exact hg
      obtain ⟨C', r, hins, _, htoH, _, _⟩ :=
        cInsert_caches h ze hl C v low (cReachesPad_caches hC).2 hg'.inBounds
      exact ⟨C', CReachesPad.insert hC hg' hins, by rw [htoH, hCU]⟩

/-! ## The headline -/

/-- **The core.**  An accepted path at `main`'s hashes against the root of `T` (any tree, any
height) opens, at the right length, an occupied index whose stored leaf has the presented
leaf's `value` and `nextValue`; or it carries a `KeccakBreakAtHead`. -/
theorem paddingAtHead_accepted_path (keccak : List UInt8 → UInt256) (T : Tree) (height : ℕ)
    (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf)
    (hp : PathAccepts (imtNodeHash keccak)
      (root (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtHashLeaf keccak) T height) sibs k idx
      (imtHashLeaf keccak ℓ)) :
    (k = height ∧ idx < T.leafCount ∧ (T.leaf idx).value = ℓ.value
        ∧ (T.leaf idx).nextValue = ℓ.nextValue)
      ∨ KeccakBreakAtHead keccak T height sibs k idx ℓ := by
  rcases accept_pins_entry_any_length_or_break (imtNodeHash keccak) (imtEmptyLeafHash keccak)
      (leafHashes (imtHashLeaf keccak) T) sibs k height idx (imtHashLeaf keccak ℓ)
      hp.inBounds hp.recompute with ⟨hk, hget⟩ | ⟨hk, hc⟩ | hb
  · by_cases hidx : idx < T.leafCount
    · rw [leafHashes_getD hidx] at hget
      by_cases hpre : imtLeafPreimage (T.leaf idx) = imtLeafPreimage ℓ
      · obtain ⟨hv, hn, _⟩ := imtLeafPreimage_fields hpre
        exact Or.inl ⟨hk, hidx, hv, hn⟩
      · exact Or.inr (KeccakBreakAtHead.leaf hk hidx ⟨hpre, hget⟩)
    · rw [getD_default _ _ _ (by rw [leafHashes_length]; omega)] at hget
      exact Or.inr (KeccakBreakAtHead.emptyLeaf hk (by omega) ⟨imtLeafPreimage_ne_tag ℓ, hget.symm⟩)
  · exact Or.inr (KeccakBreakAtHead.node hk ((pathCollision_at_head_iff_keccak ..).1 hc))
  · exact Or.inr (KeccakBreakAtHead.length ((heightBreak_at_head_iff_keccak ..).1 hb))

/-- An accepted non-inclusion proof against the root of a `Valid` tree, at `main`'s hashes. -/
theorem paddingAtHead_non_inclusion (keccak : List UInt8 → UInt256) {T : Tree} (hV : Valid T)
    {height : ℕ} {v : UInt256} {ℓ : Leaf} {idx : ℕ} {sibs : ℕ → UInt256} {k : ℕ}
    (hN : NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak)
      (root (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtHashLeaf keccak) T height) v ℓ idx
      sibs k) :
    v ∉ keys (toAbs T) ∨ KeccakBreakAtHead keccak T height sibs k idx ℓ := by
  rcases paddingAtHead_accepted_path keccak T height sibs k idx ℓ hN.path with ⟨_, hidx, hv, hn⟩ | hb
  · left
    intro hmem
    exact present_not_reclaimable hV.absSound.1 hmem
      ⟨⟨ℓ.value, ℓ.nextValue⟩, mem_toAbs.mpr ⟨idx, hidx, hv, hn⟩, hN.lowBelow, hN.window⟩
  · exact Or.inr hb

/-- An accepted inclusion proof against the root of any tree, at `main`'s hashes. -/
theorem paddingAtHead_inclusion (keccak : List UInt8 → UInt256) {T : Tree} {height : ℕ} {v : UInt256}
    {ℓ : Leaf} {idx : ℕ} {sibs : ℕ → UInt256} {k : ℕ}
    (hI : InclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak)
      (root (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtHashLeaf keccak) T height) v ℓ idx
      sibs k) :
    v ∈ keys (toAbs T) ∨ KeccakBreakAtHead keccak T height sibs k idx ℓ := by
  rcases paddingAtHead_accepted_path keccak T height sibs k idx ℓ hI.path with ⟨_, hidx, hv, _⟩ | hb
  · exact Or.inl (mem_keys_iff_index.mpr ⟨idx, hidx, hv.trans hI.valueMatch⟩)
  · exact Or.inr hb

/-- A reached state at `main`: its tree is `Valid`, and `root()` is the fold at its own height. -/
private lemma reached_at_head {keccak : List UInt8 → UInt256} {S : CState}
    (hS : CReachesAtHead keccak S) :
    Valid S.tree ∧ S.root = some (root (imtNodeHash keccak) (imtEmptyLeafHash keccak)
      (imtHashLeaf keccak) S.tree S.fm.height) := by
  obtain ⟨hH, _, hroot⟩ := cReachesPad_root_is_published _ _ _ S hS
  exact ⟨reaches_valid (hReaches_projects hH) setup_valid, hroot⟩

theorem non_inclusion_at_head_is_absent_or_keccak_collision (keccak : List UInt8 → UInt256)
    (S : CState) (hS : CReachesAtHead keccak S) :
    ∃ R : UInt256, S.root = some R ∧
      ∀ (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
        NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) R v ℓ idx sibs k →
          v ∉ keys (toAbs S.tree) ∨ KeccakBreakAtHead keccak S.tree S.fm.height sibs k idx ℓ := by
  obtain ⟨hV, hroot⟩ := reached_at_head hS
  exact ⟨_, hroot, fun _ _ _ _ _ hN => paddingAtHead_non_inclusion keccak hV hN⟩

theorem inclusion_at_head_is_present_or_keccak_collision (keccak : List UInt8 → UInt256)
    (S : CState) (hS : CReachesAtHead keccak S) :
    ∃ R : UInt256, S.root = some R ∧
      ∀ (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
        InclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) R v ℓ idx sibs k →
          v ∈ keys (toAbs S.tree) ∨ KeccakBreakAtHead keccak S.tree S.fm.height sibs k idx ℓ := by
  obtain ⟨_, hroot⟩ := reached_at_head hS
  exact ⟨_, hroot, fun _ _ _ _ _ hI => paddingAtHead_inclusion keccak hI⟩

theorem proofs_exclusive_at_head_or_keccak_collision (keccak : List UInt8 → UInt256)
    (S : CState) (hS : CReachesAtHead keccak S) :
    ∃ R : UInt256, S.root = some R ∧
      ∀ (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
        InclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) R v ℓ₁ i₁ s₁ k₁ →
        NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) R v ℓ₂ i₂ s₂ k₂ →
          KeccakBreakAtHead keccak S.tree S.fm.height s₁ k₁ i₁ ℓ₁
            ∨ KeccakBreakAtHead keccak S.tree S.fm.height s₂ k₂ i₂ ℓ₂ := by
  obtain ⟨hV, hroot⟩ := reached_at_head hS
  refine ⟨_, hroot, fun v ℓ₁ ℓ₂ i₁ i₂ s₁ s₂ k₁ k₂ hI hN => ?_⟩
  rcases paddingAtHead_inclusion keccak hI with hmem | hb₁
  · rcases paddingAtHead_non_inclusion keccak hV hN with hnot | hb₂
    · exact absurd hmem hnot
    · exact Or.inr hb₂
  · exact Or.inl hb₁

/-! ## Anti-vacuity: honest proofs, and the contract's own paths -/

theorem honest_proof_no_keccak_break_at_head (keccak : List UInt8 → UInt256) (T : Tree)
    (height i : ℕ) (hi : i < T.leafCount) :
    ¬ KeccakBreakAtHead keccak T height
        (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtLevel0 keccak T) i)
        height i (T.leaf i) :=
  fun hb => honest_proof_no_break _ _ _ T height i hi
    (keccakBreakAtHead_is_treeRootBreak keccak T height _ height i (T.leaf i) hb)

/-- The contract's path for leaf `i`: `merklePath(i)` on storage caching `leafHashes`. -/
private lemma contract_path_pad {h : Hash} {z0 : UInt256} {hl : LeafHash} {S : CState}
    (hR : FullMerkle.Represents h z0 (leafHashes hl S.tree) S.fm) {i : ℕ}
    (hi : i < S.tree.leafCount) :
    S.merklePath i
      = some ((List.range S.fm.height).map (honestSibs h z0 (leafHashes hl S.tree) i)) :=
  FullMerkle.merklePath_is_honest h z0 _ S.fm i hR (by rw [leafHashes_length]; exact hi)

/-- An accepted path at height `H` over the honest stream is accepted over the contract's
returned path, which has length `H`. -/
private lemma pathAccepts_contract_pad {h : Hash} {z0 : UInt256} {L : List UInt256} {R : UInt256}
    {H i : ℕ} {x : UInt256} (hA : PathAccepts h R (honestSibs h z0 L i) H i x) :
    PathAccepts h R (FullMerkle.pathSibs ((List.range H).map (honestSibs h z0 L i)))
      ((List.range H).map (honestSibs h z0 L i)).length i x := by
  rw [List.length_map, List.length_range]
  refine ⟨hA.inBounds, ?_⟩
  rw [walkPure_congr_sibs h _ (honestSibs h z0 L i) H 0 i x
    (fun l _ hl => FullMerkle.pathSibs_honest h z0 L H i l (by omega))]
  exact hA.recompute

/-- No located break on the contract's own path (`CachedRoot`'s argument, for any padding). -/
private lemma contract_path_no_break_pad (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree)
    (H i : ℕ) (hi : i < T.leafCount) :
    ¬ TreeRootBreak h z0 hl T H
        (FullMerkle.pathSibs ((List.range H).map (honestSibs h z0 (leafHashes hl T) i)))
        ((List.range H).map (honestSibs h z0 (leafHashes hl T) i)).length i (T.leaf i) := by
  rw [List.length_map, List.length_range]
  intro hb
  cases hb with
  | wrongLength hh => exact heightBreak_not_tautology.1 _ _ _ _ _ _ _ hh
  | pathCollision _ hc =>
    obtain ⟨j, hj, hne, _⟩ := hc
    apply hne
    refine walkPair_honest h z0 (leafHashes hl T) _ j 0 i (hl (T.leaf i)) ?_ ?_
    · intro l _ hl'
      rw [FullMerkle.pathSibs_honest h z0 _ H i l (by omega), Nat.sub_zero]
      rfl
    · rw [levels_zero, zeros_zero, leafHashes_getD hi]
  | leafCollision _ hne _ => exact hne rfl
  | paddingHit hle _ => omega

theorem contract_proofs_at_stored_root_at_head (keccak : List UInt8 → UInt256) (S : CState)
    (hS : CReachesAtHead keccak S) :
    ∃ R : UInt256, S.root = some R
      ∧ (∀ v : UInt256, v ∈ keys (toAbs S.tree) →
          ∃ i < S.tree.leafCount, (S.tree.leaf i).value = v
            ∧ ∃ p : List UInt256, S.merklePath i = some p ∧ p.length = S.fm.height
              ∧ InclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) R v (S.tree.leaf i) i
                  (FullMerkle.pathSibs p) p.length
              ∧ ¬ KeccakBreakAtHead keccak S.tree S.fm.height (FullMerkle.pathSibs p) p.length i
                  (S.tree.leaf i))
      ∧ (∀ v : UInt256, v ≠ 0 → v ∉ keys (toAbs S.tree) →
          ∃ i < S.tree.leafCount,
            ∃ p : List UInt256, S.merklePath i = some p ∧ p.length = S.fm.height
              ∧ NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) R v (S.tree.leaf i) i
                  (FullMerkle.pathSibs p) p.length
              ∧ ¬ KeccakBreakAtHead keccak S.tree S.fm.height (FullMerkle.pathSibs p) p.length i
                  (S.tree.leaf i)) := by
  obtain ⟨hH, hR, hroot⟩ := cReachesPad_root_is_published _ _ _ S hS
  obtain ⟨c1, c2, _⟩ := proofs_exclusive_or_break_at_own_height (imtNodeHash keccak)
    (imtEmptyLeafHash keccak) (imtHashLeaf keccak) S.toH hH
  refine ⟨_, hroot, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, hi, hval, hI, _⟩ := c1 v hv
    refine ⟨i, hi, hval, _, contract_path_pad hR hi, by rw [List.length_map, List.length_range],
      ⟨hI.valueMatch, pathAccepts_contract_pad hI.path⟩, fun hb => ?_⟩
    exact contract_path_no_break_pad _ _ _ S.tree S.fm.height i hi
      (keccakBreakAtHead_is_treeRootBreak keccak _ _ _ _ _ _ hb)
  · intro v hv0 habs
    obtain ⟨i, hi, hN, _⟩ := c2 v hv0 habs
    refine ⟨i, hi, _, contract_path_pad hR hi, by rw [List.length_map, List.length_range],
      ⟨hN.nonzero, hN.lowBelow, hN.window, pathAccepts_contract_pad hN.path⟩, fun hb => ?_⟩
    exact contract_path_no_break_pad _ _ _ S.tree S.fm.height i hi
      (keccakBreakAtHead_is_treeRootBreak keccak _ _ _ _ _ _ hb)

/-! ## The three-leaf run, with any padding constant -/

theorem paddingAtHead_three_leaf_run (h : Hash) (hl : LeafHash) (ze a b : UInt256) (ha : 0 < a)
    (hab : a < b) :
    ∃ (S₀ S₁ S₂ : CState) (r₁ r₂ : UInt256),
      cSetupPad h hl ze = some S₀ ∧ cInsert h hl S₀ a 0 = some (S₁, r₁)
      ∧ cInsert h hl S₁ b 1 = some (S₂, r₂)
      ∧ CReachesPad h hl ze S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.toH = hThree a b
      ∧ S₂.fm.height = 2 ∧ S₂.root = some r₂ ∧ r₂ = root h ze hl (threeLeafTree a b) 2
      ∧ S₂.merklePath 3 = none
      ∧ ∃ R : ℕ → CState, CRun h hl R ∧ R 0 = S₀ ∧ R 1 = S₁ ∧ ∀ n, 2 ≤ n → R n = S₂ := by
  obtain ⟨hg₁, hg₂⟩ := threeLeafTree_guards ha hab
  obtain ⟨S₀, hs₀, htree₀, hH₀, hR₀, _⟩ := cSetupPad_caches h hl ze
  have hc₀ : CReachesPad h hl ze S₀ := CReachesPad.init hs₀
  rw [← htree₀] at hg₁
  obtain ⟨S₁, r₁, hins₁, htree₁', htoH₁, hR₁, _⟩ := cInsert_caches h ze hl S₀ a 0 hR₀ hg₁.inBounds
  have hc₁ : CReachesPad h hl ze S₁ := CReachesPad.insert hc₀ hg₁ hins₁
  have htree₁ : S₁.tree = insert setup a 0 := by rw [htree₁', htree₀]
  rw [← htree₁] at hg₂
  obtain ⟨S₂, r₂, hins₂, _, htoH₂, hR₂, hr₂⟩ := cInsert_caches h ze hl S₁ b 1 hR₁ hg₂.inBounds
  have hc₂ : CReachesPad h hl ze S₂ := CReachesPad.insert hc₁ hg₂ hins₂
  have hview : S₂.toH = hThree a b := by rw [htoH₂, htoH₁, hH₀]; rfl
  have htree₂ : S₂.tree = threeLeafTree a b := congrArg HState.tree hview
  have hheight₂ : S₂.fm.height = 2 := congrArg HState.height hview
  refine ⟨S₀, S₁, S₂, r₁, r₂, hs₀, hins₁, hins₂, hc₂, htree₂, hview, hheight₂, ?_, ?_, ?_, ?_⟩
  · rw [root_eq_published_pad hR₂, hr₂]
    rfl
  · rw [hr₂, htree₂, hheight₂]
  · show FullMerkle.merklePath S₂.fm 3 = none
    refine FullMerkle.merklePath_out_of_range_reverts S₂.fm 3 ?_
    rw [hR₂.leafNumber_eq, leafHashes_length, htree₂]
    show 3 ≤ 3
    omega
  · refine ⟨fun n => if n = 0 then S₀ else if n = 1 then S₁ else S₂, ?_, rfl, rfl, ?_⟩
    · intro n
      match n with
      | 0 => exact Or.inr ⟨a, 0, r₁, hg₁, hins₁⟩
      | 1 => exact Or.inr ⟨b, 1, r₂, hg₂, hins₂⟩
      | n + 2 => exact Or.inl (by simp)
    · intro n hn
      simp only [show n ≠ 0 from by omega, show n ≠ 1 from by omega, ite_false]

/-! ## The pin's countermodel, at `main` -/

lemma threeLeafTree_leafCount (a b : UInt256) : (threeLeafTree a b).leafCount = 3 := rfl

lemma threeLeafTree_leaf_zero (a b : UInt256) : (threeLeafTree a b).leaf 0 = ⟨0, 1, a⟩ := rfl

/-- The pin's forged instance against `main`'s root of `threeLeafTree a b` at height 2: accepted
exactly when keccak collides on `abi.encode(0,0,0)` and the tag, or on a node pair of its path. -/
lemma paddingAtHead_pin_instance_iff (keccak : List UInt8 → UInt256) {a b : UInt256} (ha : 0 < a) :
    NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak)
        (root (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtHashLeaf keccak) (threeLeafTree a b) 2)
        a ⟨0, 0, 0⟩ 3
        (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
          (imtLevel0 keccak (threeLeafTree a b)) 3) 2
      ↔ HashCollision keccak (imtLeafPreimage ⟨0, 0, 0⟩) imtEmptyLeafTag
        ∨ PathKeccakCollision keccak (imtEmptyLeafHash keccak)
            (imtLevel0 keccak (threeLeafTree a b))
            (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
              (imtLevel0 keccak (threeLeafTree a b)) 3) 0 2 3 (imtHashLeaf keccak ⟨0, 0, 0⟩) := by
  have hlen : (imtLevel0 keccak (threeLeafTree a b)).length ≤ 3 := by
    rw [imtLevel0, leafHashes_length, threeLeafTree_leafCount]
  have hacc := honest_siblings_accept_exactly (imtNodeHash keccak) (imtEmptyLeafHash keccak)
    (imtLevel0 keccak (threeLeafTree a b)) 2 3 (imtHashLeaf keccak ⟨0, 0, 0⟩) (by norm_num)
  rw [getD_default _ _ _ hlen] at hacc
  constructor
  · intro hN
    rcases hacc.1 hN.path.recompute with he | hc
    · exact Or.inl ⟨imtLeafPreimage_ne_tag _, he.symm⟩
    · exact Or.inr ((pathCollision_at_head_iff_keccak ..).1 hc)
  · intro hcase
    refine ⟨(ne_of_lt ha).symm, ha, Or.inl rfl, ⟨by norm_num, hacc.2 ?_⟩⟩
    rcases hcase with hc | hc
    · exact Or.inl hc.2.symm
    · exact Or.inr ((pathCollision_at_head_iff_keccak ..).2 hc)

theorem pin_forgery_at_head_needs_keccak_collision (keccak : List UInt8 → UInt256) (a b : UInt256)
    (ha : 0 < a) (hab : a < b) :
    ∃ (S₂ : CState) (r₂ : UInt256),
      CReachesAtHead keccak S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.fm.height = 2
      ∧ S₂.root = some r₂ ∧ a ∈ keys (toAbs S₂.tree)
      ∧ (∀ (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ), 3 ≤ idx →
          NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a ⟨0, 0, 0⟩ idx sibs k →
            (k = 2 ∧ HashCollision keccak (imtLeafPreimage ⟨0, 0, 0⟩) imtEmptyLeafTag)
            ∨ (k = 2 ∧ PathKeccakCollision keccak (imtEmptyLeafHash keccak)
                (imtLevel0 keccak (threeLeafTree a b)) sibs 0 k idx (imtHashLeaf keccak ⟨0, 0, 0⟩))
            ∨ LengthKeccakBreak keccak (threeLeafTree a b) 2 sibs k idx ⟨0, 0, 0⟩)
      ∧ (NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a ⟨0, 0, 0⟩ 3
            (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
              (imtLevel0 keccak (threeLeafTree a b)) 3) 2
          ↔ HashCollision keccak (imtLeafPreimage ⟨0, 0, 0⟩) imtEmptyLeafTag
            ∨ PathKeccakCollision keccak (imtEmptyLeafHash keccak)
                (imtLevel0 keccak (threeLeafTree a b))
                (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
                  (imtLevel0 keccak (threeLeafTree a b)) 3) 0 2 3 (imtHashLeaf keccak ⟨0, 0, 0⟩)) := by
  obtain ⟨_, _, S₂, _, r₂, _, _, _, hc₂, htree₂, _, hheight₂, hroot₂, hr₂, _⟩ :=
    paddingAtHead_three_leaf_run (imtNodeHash keccak) (imtHashLeaf keccak) (imtEmptyLeafHash keccak)
      a b ha hab
  have hmem : a ∈ keys (toAbs (threeLeafTree a b)) :=
    (padding_collision_refunds_delivered_leg (imtNodeHash keccak) (imtHashLeaf keccak) ha hab).2.1
  refine ⟨S₂, r₂, hc₂, htree₂, hheight₂, hroot₂, by rw [htree₂]; exact hmem, ?_, ?_⟩
  · intro idx sibs k hidx hN
    rw [hr₂] at hN
    rcases paddingAtHead_accepted_path keccak (threeLeafTree a b) 2 sibs k idx ⟨0, 0, 0⟩ hN.path with
      ⟨_, hlt, _, _⟩ | hb
    · rw [threeLeafTree_leafCount] at hlt
      omega
    · cases hb with
      | emptyLeaf hk _ hc => exact Or.inl ⟨hk, hc⟩
      | leaf _ hlt _ =>
        rw [threeLeafTree_leafCount] at hlt
        omega
      | node hk hc => exact Or.inr (Or.inl ⟨hk, hc⟩)
      | length hl => exact Or.inr (Or.inr hl)
  · rw [hr₂]
    exact paddingAtHead_pin_instance_iff keccak ha

theorem pin_forgery_at_head_fires_on_collision :
    (∃ keccak : List UInt8 → UInt256,
        HashCollision keccak (imtLeafPreimage ⟨0, 0, 0⟩) imtEmptyLeafTag)
      ∧ ∀ (keccak : List UInt8 → UInt256),
          HashCollision keccak (imtLeafPreimage ⟨0, 0, 0⟩) imtEmptyLeafTag →
        ∀ a b : UInt256, 0 < a → a < b →
          ∃ (S₂ : CState) (r₂ : UInt256),
            CReachesAtHead keccak S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.root = some r₂
            ∧ a ∈ keys (toAbs S₂.tree)
            ∧ InclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a
                ((threeLeafTree a b).leaf 1) 1
                (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
                  (imtLevel0 keccak (threeLeafTree a b)) 1) 2
            ∧ NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a ⟨0, 0, 0⟩ 3
                (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
                  (imtLevel0 keccak (threeLeafTree a b)) 3) 2
            ∧ KeccakBreakAtHead keccak S₂.tree S₂.fm.height
                (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
                  (imtLevel0 keccak (threeLeafTree a b)) 3) 2 3 ⟨0, 0, 0⟩ := by
  refine ⟨⟨fun _ => 0, imtLeafPreimage_ne_tag _, rfl⟩, ?_⟩
  intro keccak hc a b ha hab
  obtain ⟨_, _, S₂, _, r₂, _, _, _, hc₂, htree₂, _, hheight₂, hroot₂, hr₂, _⟩ :=
    paddingAtHead_three_leaf_run (imtNodeHash keccak) (imtHashLeaf keccak) (imtEmptyLeafHash keccak)
      a b ha hab
  have hmem : a ∈ keys (toAbs (threeLeafTree a b)) :=
    (padding_collision_refunds_delivered_leg (imtNodeHash keccak) (imtHashLeaf keccak) ha hab).2.1
  have hI := inclusion_complete (h := imtNodeHash keccak) (z0 := imtEmptyLeafHash keccak)
    (hl := imtHashLeaf keccak) (T := threeLeafTree a b) (height := 2)
    (by rw [threeLeafTree_leafCount]; norm_num) (i := 1) (by rw [threeLeafTree_leafCount]; norm_num)
  rw [threeLeafTree_leaf_one_value] at hI
  refine ⟨S₂, r₂, hc₂, htree₂, hroot₂, by rw [htree₂]; exact hmem, by rw [hr₂]; exact hI,
    by rw [hr₂]; exact (paddingAtHead_pin_instance_iff keccak ha).2 (Or.inl hc), ?_⟩
  rw [htree₂, hheight₂]
  exact KeccakBreakAtHead.emptyLeaf rfl (by rw [threeLeafTree_leafCount]) hc

/-! ### Two more firing witnesses: the node case alone, and the leaf case -/

/-- A walk of positive length under a constant node hash is that constant. -/
lemma paddingAtHead_walkPure_const {h : Hash} {c : UInt256} (hc : ∀ a b, h a b = c)
    (sibs : ℕ → UInt256) (lvl k idx : ℕ) (x : UInt256) : walkPure h sibs lvl (k + 1) idx x = c := by
  obtain ⟨a, b, e⟩ := walkPure_succ_is_node h sibs k lvl idx x
  rw [e, hc]

/-- A root of positive height under a constant node hash is that constant. -/
lemma paddingAtHead_rootOf_const {h : Hash} {c : UInt256} (hc : ∀ a b, h a b = c) (z0 : UInt256)
    (L : List UInt256) (l : ℕ) : rootOf h z0 L (l + 1) = c := by
  obtain ⟨a, b, e⟩ := levels_succ_is_node h z0 L l 0
  rw [rootOf_def, ← getD_zero_headD, e, hc]

/-- A stand-in for keccak, used only in a witness.  It is not a hash.  It maps every 64-byte
input (a node pair) to `0`, the 34-byte tag to `1`, and everything else, every leaf preimage
among them, to `2`.  So the padding constant and `hashLeaf` never collide, while every two node
pairs do. -/
def paddingAtHeadNodeToyKeccak (x : List UInt8) : UInt256 :=
  if x.length = 64 then 0 else if x.length = 34 then 1 else 2

lemma paddingAtHeadNodeToyKeccak_node (a b : UInt256) :
    imtNodeHash paddingAtHeadNodeToyKeccak a b = 0 := by
  show paddingAtHeadNodeToyKeccak (imtNodePreimage a b) = 0
  rw [paddingAtHeadNodeToyKeccak, imtNodePreimage_length]
  rfl

lemma paddingAtHeadNodeToyKeccak_leaf (ℓ : Leaf) : imtHashLeaf paddingAtHeadNodeToyKeccak ℓ = 2 := by
  show paddingAtHeadNodeToyKeccak (imtLeafPreimage ℓ) = 2
  rw [paddingAtHeadNodeToyKeccak, imtLeafPreimage_length]
  rfl

lemma paddingAtHeadNodeToyKeccak_tag : imtEmptyLeafHash paddingAtHeadNodeToyKeccak = 1 := by
  show paddingAtHeadNodeToyKeccak imtEmptyLeafTag = 1
  rw [paddingAtHeadNodeToyKeccak, imtEmptyLeafTag_length]
  rfl

theorem node_collision_at_head_fires :
    ∃ keccak : List UInt8 → UInt256,
      ¬ HashCollision keccak (imtLeafPreimage ⟨0, 0, 0⟩) imtEmptyLeafTag
      ∧ ∀ a b : UInt256, 0 < a → a < b →
        ∃ (S₂ : CState) (r₂ : UInt256),
          CReachesAtHead keccak S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.root = some r₂
          ∧ a ∈ keys (toAbs S₂.tree)
          ∧ NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a ⟨0, 0, 0⟩ 3
              (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
                (imtLevel0 keccak (threeLeafTree a b)) 3) 2
          ∧ PathKeccakCollision keccak (imtEmptyLeafHash keccak)
              (imtLevel0 keccak (threeLeafTree a b))
              (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
                (imtLevel0 keccak (threeLeafTree a b)) 3) 0 2 3 (imtHashLeaf keccak ⟨0, 0, 0⟩) := by
  have hnoPad : ¬ HashCollision paddingAtHeadNodeToyKeccak (imtLeafPreimage ⟨0, 0, 0⟩)
      imtEmptyLeafTag := by
    rintro ⟨_, he⟩
    have h21 : (2 : UInt256) = 1 := by
      have := he
      rw [show paddingAtHeadNodeToyKeccak (imtLeafPreimage ⟨0, 0, 0⟩)
          = imtHashLeaf paddingAtHeadNodeToyKeccak ⟨0, 0, 0⟩ from rfl,
        show paddingAtHeadNodeToyKeccak imtEmptyLeafTag
          = imtEmptyLeafHash paddingAtHeadNodeToyKeccak from rfl,
        paddingAtHeadNodeToyKeccak_leaf, paddingAtHeadNodeToyKeccak_tag] at this
      exact this
    exact absurd h21 (by decide)
  refine ⟨paddingAtHeadNodeToyKeccak, hnoPad, ?_⟩
  intro a b ha hab
  obtain ⟨_, _, S₂, _, r₂, _, _, _, hc₂, htree₂, _, _, hroot₂, hr₂, _⟩ :=
    paddingAtHead_three_leaf_run (imtNodeHash paddingAtHeadNodeToyKeccak)
      (imtHashLeaf paddingAtHeadNodeToyKeccak) (imtEmptyLeafHash paddingAtHeadNodeToyKeccak) a b ha hab
  have hmem : a ∈ keys (toAbs (threeLeafTree a b)) :=
    (padding_collision_refunds_delivered_leg (imtNodeHash paddingAtHeadNodeToyKeccak)
      (imtHashLeaf paddingAtHeadNodeToyKeccak) ha hab).2.1
  have hN : NonInclusionAccepted (imtNodeHash paddingAtHeadNodeToyKeccak)
      (imtHashLeaf paddingAtHeadNodeToyKeccak)
      (root (imtNodeHash paddingAtHeadNodeToyKeccak) (imtEmptyLeafHash paddingAtHeadNodeToyKeccak)
        (imtHashLeaf paddingAtHeadNodeToyKeccak) (threeLeafTree a b) 2) a ⟨0, 0, 0⟩ 3
      (honestSibs (imtNodeHash paddingAtHeadNodeToyKeccak)
        (imtEmptyLeafHash paddingAtHeadNodeToyKeccak)
        (imtLevel0 paddingAtHeadNodeToyKeccak (threeLeafTree a b)) 3) 2 := by
    refine ⟨(ne_of_lt ha).symm, ha, Or.inl rfl, ⟨by norm_num, ?_⟩⟩
    show walkPure (imtNodeHash paddingAtHeadNodeToyKeccak) _ 0 (1 + 1) 3 _
      = rootOf (imtNodeHash paddingAtHeadNodeToyKeccak) _ _ (1 + 1)
    rw [paddingAtHead_walkPure_const paddingAtHeadNodeToyKeccak_node,
      paddingAtHead_rootOf_const paddingAtHeadNodeToyKeccak_node]
  refine ⟨S₂, r₂, hc₂, htree₂, hroot₂, by rw [htree₂]; exact hmem, by rw [hr₂]; exact hN, ?_⟩
  rcases (paddingAtHead_pin_instance_iff paddingAtHeadNodeToyKeccak ha).1 hN with hc | hc
  · exact absurd hc hnoPad
  · exact hc

theorem leaf_collision_at_head_fires :
    (∀ a : UInt256, 0 < a → ∃ keccak : List UInt8 → UInt256,
        HashCollision keccak (imtLeafPreimage ⟨0, 1, a⟩) (imtLeafPreimage ⟨0, 1, 0⟩))
      ∧ ∀ (keccak : List UInt8 → UInt256) (a b : UInt256), 0 < a → a < b →
        HashCollision keccak (imtLeafPreimage ⟨0, 1, a⟩) (imtLeafPreimage ⟨0, 1, 0⟩) →
          ∃ (S₂ : CState) (r₂ : UInt256),
            CReachesAtHead keccak S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.root = some r₂
            ∧ a ∈ keys (toAbs S₂.tree) ∧ S₂.tree.leaf 0 = ⟨0, 1, a⟩
            ∧ NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a ⟨0, 1, 0⟩ 0
                (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
                  (imtLevel0 keccak (threeLeafTree a b)) 0) 2
            ∧ KeccakBreakAtHead keccak S₂.tree S₂.fm.height
                (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
                  (imtLevel0 keccak (threeLeafTree a b)) 0) 2 0 ⟨0, 1, 0⟩ := by
  refine ⟨fun a ha => ⟨fun _ => 0, fun he => ?_, rfl⟩, ?_⟩
  · have := (imtLeafPreimage_fields he).2.1
    exact absurd this (ne_of_lt ha).symm
  · intro keccak a b ha hab hc
    obtain ⟨_, _, S₂, _, r₂, _, _, _, hc₂, htree₂, _, hheight₂, hroot₂, hr₂, _⟩ :=
      paddingAtHead_three_leaf_run (imtNodeHash keccak) (imtHashLeaf keccak)
        (imtEmptyLeafHash keccak) a b ha hab
    have hmem : a ∈ keys (toAbs (threeLeafTree a b)) :=
      (padding_collision_refunds_delivered_leg (imtNodeHash keccak) (imtHashLeaf keccak) ha hab).2.1
    have h0 : 0 < (threeLeafTree a b).leafCount := by rw [threeLeafTree_leafCount]; norm_num
    have e : imtHashLeaf keccak ⟨0, 1, 0⟩
        = (imtLevel0 keccak (threeLeafTree a b)).getD 0 (imtEmptyLeafHash keccak) := by
      rw [imtLevel0, leafHashes_getD h0, threeLeafTree_leaf_zero]
      exact hc.2.symm
    have hN : NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak)
        (root (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtHashLeaf keccak) (threeLeafTree a b) 2)
        a ⟨0, 1, 0⟩ 0
        (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
          (imtLevel0 keccak (threeLeafTree a b)) 0) 2 := by
      refine ⟨(ne_of_lt ha).symm, ha, Or.inl rfl, ⟨by norm_num, ?_⟩⟩
      rw [e]
      exact honest_walk_root _ _ _ 2 0 (by norm_num)
    refine ⟨S₂, r₂, hc₂, htree₂, hroot₂, by rw [htree₂]; exact hmem,
      by rw [htree₂]; exact threeLeafTree_leaf_zero a b, by rw [hr₂]; exact hN, ?_⟩
    rw [htree₂, hheight₂]
    refine KeccakBreakAtHead.leaf rfl h0 ?_
    rw [threeLeafTree_leaf_zero]
    exact hc

/-! ## A toy keccak: the same forged proof, accepted at the pin and rejected at `main` -/

/-- A stand-in for keccak, used only in a witness.  It is not a hash.  On a 64-byte input (a node
pair) it returns the right-hand word, on a 34-byte input (the tag) `1`, and on every other input,
every leaf preimage among them, `0`.  So `hashLeaf` is constantly `0` and the padding constant is
`1`: they never collide. -/
def paddingAtHeadToyKeccak (x : List UInt8) : UInt256 :=
  if x.length = 64 then Nat.toUInt256 (fromBytesBE (x.drop 32)) else if x.length = 34 then 1 else 0

lemma paddingAtHeadToyKeccak_node (a b : UInt256) :
    imtNodeHash paddingAtHeadToyKeccak a b = b := by
  show paddingAtHeadToyKeccak (imtNodePreimage a b) = b
  rw [paddingAtHeadToyKeccak, ite_eq_left (imtNodePreimage_length a b), imtNodePreimage,
    List.drop_left' (word_length a.val), fromBytesBE_toBytesBE (uint256_val_lt b), toUInt256_val]

lemma paddingAtHeadToyKeccak_leaf (ℓ : Leaf) : imtHashLeaf paddingAtHeadToyKeccak ℓ = 0 := by
  show paddingAtHeadToyKeccak (imtLeafPreimage ℓ) = 0
  rw [paddingAtHeadToyKeccak, imtLeafPreimage_length]
  rfl

lemma paddingAtHeadToyKeccak_tag : imtEmptyLeafHash paddingAtHeadToyKeccak = 1 := by
  show paddingAtHeadToyKeccak imtEmptyLeafTag = 1
  rw [paddingAtHeadToyKeccak, imtEmptyLeafTag_length]
  rfl

/-- Under the toy hash, slot 3 is a right child at both levels, so a length-2 walk from it
returns its accumulator, whatever the siblings. -/
lemma paddingAtHeadToyKeccak_walk (sibs : ℕ → UInt256) (y : UInt256) :
    walkPure (imtNodeHash paddingAtHeadToyKeccak) sibs 0 2 3 y = y := by
  show walkPure (imtNodeHash paddingAtHeadToyKeccak) sibs 0 (0 + 1 + 1) 3 y = y
  rw [walkPure_succ, walkPure_succ, walkPure_zero]
  simp [paddingAtHeadToyKeccak_node]

theorem pin_forgery_accepted_at_pin_rejected_at_head :
    ∃ keccak : List UInt8 → UInt256,
      ¬ HashCollision keccak (imtLeafPreimage ⟨0, 0, 0⟩) imtEmptyLeafTag
      ∧ ∀ a b : UInt256, 0 < a → a < b →
        (∃ (S₂ : CState) (r₂ : UInt256),
            CReaches (imtNodeHash keccak) (imtHashLeaf keccak) S₂ ∧ S₂.tree = threeLeafTree a b
            ∧ S₂.root = some r₂ ∧ a ∈ keys (toAbs S₂.tree)
            ∧ NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a ⟨0, 0, 0⟩ 3
                (honestSibs (imtNodeHash keccak) (zeroLeafHash (imtHashLeaf keccak))
                  (imtLevel0 keccak (threeLeafTree a b)) 3) 2)
        ∧ (∃ (S₂ : CState) (r₂ : UInt256),
            CReachesAtHead keccak S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.root = some r₂
            ∧ ∀ sibs : ℕ → UInt256,
                ¬ NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a ⟨0, 0, 0⟩ 3
                    sibs 2) := by
  refine ⟨paddingAtHeadToyKeccak, ?_, ?_⟩
  · rintro ⟨_, he⟩
    have h01 : (0 : UInt256) = 1 := by
      have := he
      rw [show paddingAtHeadToyKeccak (imtLeafPreimage ⟨0, 0, 0⟩)
          = imtHashLeaf paddingAtHeadToyKeccak ⟨0, 0, 0⟩ from rfl,
        show paddingAtHeadToyKeccak imtEmptyLeafTag = imtEmptyLeafHash paddingAtHeadToyKeccak from rfl,
        paddingAtHeadToyKeccak_leaf, paddingAtHeadToyKeccak_tag] at this
      exact this
    exact absurd h01 (by decide)
  · intro a b ha hab
    have hmem : a ∈ keys (toAbs (threeLeafTree a b)) :=
      (padding_collision_refunds_delivered_leg (imtNodeHash paddingAtHeadToyKeccak)
        (imtHashLeaf paddingAtHeadToyKeccak) ha hab).2.1
    refine ⟨?_, ?_⟩
    · obtain ⟨_, _, S₂, _, r₂, _, _, _, hc₂, htree₂, _, _, _, hroot₂, _, _, hN, _⟩ :=
        cThreeLeaf_witness (imtNodeHash paddingAtHeadToyKeccak) (imtHashLeaf paddingAtHeadToyKeccak)
          a b ha hab
      refine ⟨S₂, r₂, hc₂, htree₂, hroot₂, by rw [htree₂]; exact hmem, ?_⟩
      rw [htree₂] at hN
      exact hN
    · obtain ⟨_, _, S₂, _, r₂, _, _, _, hc₂, htree₂, _, _, hroot₂, hr₂, _⟩ :=
        paddingAtHead_three_leaf_run (imtNodeHash paddingAtHeadToyKeccak)
          (imtHashLeaf paddingAtHeadToyKeccak) (imtEmptyLeafHash paddingAtHeadToyKeccak) a b ha hab
      refine ⟨S₂, r₂, hc₂, htree₂, hroot₂, fun sibs hN => ?_⟩
      have hlen : (imtLevel0 paddingAtHeadToyKeccak (threeLeafTree a b)).length ≤ 3 := by
        rw [imtLevel0, leafHashes_length, threeLeafTree_leafCount]
      -- the root at height 2 is the padding constant: the honest slot-3 walk returns it
      have hroot : r₂ = 1 := by
        rw [hr₂, ← paddingAtHeadToyKeccak_tag]
        have := padded_slot_verifies (imtNodeHash paddingAtHeadToyKeccak)
          (imtEmptyLeafHash paddingAtHeadToyKeccak)
          (imtLevel0 paddingAtHeadToyKeccak (threeLeafTree a b)) 2 3 hlen (by norm_num)
        rw [paddingAtHeadToyKeccak_walk] at this
        exact this.symm
      have hwalk := hN.path.recompute
      rw [paddingAtHeadToyKeccak_walk, paddingAtHeadToyKeccak_leaf, hroot] at hwalk
      exact absurd hwalk (by decide)

/-! ## Out-of-range indices -/

theorem out_of_range_index_at_head (keccak : List UInt8 → UInt256) (S : CState)
    (hS : CReachesAtHead keccak S) :
    ∃ R : UInt256, S.root = some R
      ∧ (∀ idx : ℕ, S.tree.leafCount ≤ idx → idx < 2 ^ S.fm.height →
          PathAccepts (imtNodeHash keccak) R
            (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtLevel0 keccak S.tree) idx)
            S.fm.height idx (imtEmptyLeafHash keccak))
      ∧ (∀ (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf), S.tree.leafCount ≤ idx →
          PathAccepts (imtNodeHash keccak) R sibs k idx (imtHashLeaf keccak ℓ) →
            (k = S.fm.height ∧ idx < 2 ^ S.fm.height
                ∧ HashCollision keccak (imtLeafPreimage ℓ) imtEmptyLeafTag)
            ∨ (k = S.fm.height ∧ PathKeccakCollision keccak (imtEmptyLeafHash keccak)
                (imtLevel0 keccak S.tree) sibs 0 k idx (imtHashLeaf keccak ℓ))
            ∨ LengthKeccakBreak keccak S.tree S.fm.height sibs k idx ℓ)
      ∧ (∀ (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf), 2 ^ S.fm.height ≤ idx →
          PathAccepts (imtNodeHash keccak) R sibs k idx (imtHashLeaf keccak ℓ) →
            S.fm.height < k ∧ LengthKeccakBreak keccak S.tree S.fm.height sibs k idx ℓ) := by
  obtain ⟨hH, _, hroot⟩ := cReachesPad_root_is_published _ _ _ S hS
  have hcap : S.tree.leafCount ≤ 2 ^ S.fm.height := hReaches_capacity hH
  have cases : ∀ (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf), S.tree.leafCount ≤ idx →
      PathAccepts (imtNodeHash keccak) (S.toH.root (imtNodeHash keccak) (imtEmptyLeafHash keccak)
        (imtHashLeaf keccak)) sibs k idx (imtHashLeaf keccak ℓ) →
        (k = S.fm.height ∧ idx < 2 ^ S.fm.height
            ∧ HashCollision keccak (imtLeafPreimage ℓ) imtEmptyLeafTag)
        ∨ (k = S.fm.height ∧ PathKeccakCollision keccak (imtEmptyLeafHash keccak)
            (imtLevel0 keccak S.tree) sibs 0 k idx (imtHashLeaf keccak ℓ))
        ∨ LengthKeccakBreak keccak S.tree S.fm.height sibs k idx ℓ := by
    intro sibs k idx ℓ hle hp
    rcases accept_pins_entry_any_length_or_break (imtNodeHash keccak) (imtEmptyLeafHash keccak)
        (imtLevel0 keccak S.tree) sibs k S.fm.height idx (imtHashLeaf keccak ℓ)
        hp.inBounds hp.recompute with ⟨hk, hget⟩ | ⟨hk, hc⟩ | hb
    · rw [imtLevel0, getD_default _ _ _ (by rw [leafHashes_length]; exact hle)] at hget
      exact Or.inl ⟨hk, by rw [← hk]; exact hp.inBounds, imtLeafPreimage_ne_tag ℓ, hget.symm⟩
    · exact Or.inr (Or.inl ⟨hk, (pathCollision_at_head_iff_keccak ..).1 hc⟩)
    · exact Or.inr (Or.inr ((heightBreak_at_head_iff_keccak ..).1 hb))
  refine ⟨_, hroot, ?_, cases, ?_⟩
  · intro idx hle hlt
    exact ⟨hlt, padded_slot_verifies (imtNodeHash keccak) (imtEmptyLeafHash keccak)
      (imtLevel0 keccak S.tree) S.fm.height idx (by rw [imtLevel0, leafHashes_length]; exact hle) hlt⟩
  · intro sibs k idx ℓ hle hp
    have hk : S.fm.height < k := by
      by_contra hcon
      have h1 : idx < 2 ^ k := hp.inBounds
      have h2 : 2 ^ k ≤ 2 ^ S.fm.height := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    refine ⟨hk, ?_⟩
    rcases cases sibs k idx ℓ (le_trans hcap hle) hp with ⟨hk', _⟩ | ⟨hk', _⟩ | hb
    · omega
    · omega
    · exact hb

theorem out_of_range_index_at_head_witness :
    ∃ keccak : List UInt8 → UInt256, ∀ a b : UInt256, 0 < a → a < b →
      ∃ (S₂ : CState) (r₂ : UInt256),
        CReachesAtHead keccak S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.fm.height = 2
        ∧ S₂.root = some r₂
        ∧ PathAccepts (imtNodeHash keccak) r₂ (fun _ => 0) 2 3 (imtHashLeaf keccak ⟨0, 0, 0⟩)
        ∧ PathAccepts (imtNodeHash keccak) r₂ (fun _ => 0) 3 4 (imtHashLeaf keccak ⟨0, 0, 0⟩) := by
  have hc : ∀ a b : UInt256, imtNodeHash (fun _ => (0 : UInt256)) a b = 0 := fun _ _ => rfl
  refine ⟨fun _ => 0, fun a b ha hab => ?_⟩
  obtain ⟨_, _, S₂, _, r₂, _, _, _, hc₂, htree₂, _, hheight₂, hroot₂, hr₂, _⟩ :=
    paddingAtHead_three_leaf_run (imtNodeHash fun _ => 0) (imtHashLeaf fun _ => 0)
      (imtEmptyLeafHash fun _ => 0) a b ha hab
  refine ⟨S₂, r₂, hc₂, htree₂, hheight₂, hroot₂, ⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩⟩
  · rw [hr₂]
    show walkPure (imtNodeHash fun _ => 0) _ 0 (1 + 1) 3 _ = rootOf (imtNodeHash fun _ => 0) _ _ (1 + 1)
    rw [paddingAtHead_walkPure_const hc, paddingAtHead_rootOf_const hc]
  · rw [hr₂]
    show walkPure (imtNodeHash fun _ => 0) _ 0 (2 + 1) 4 _ = rootOf (imtNodeHash fun _ => 0) _ _ (1 + 1)
    rw [paddingAtHead_walkPure_const hc, paddingAtHead_rootOf_const hc]

theorem paddingAtHead_break_premises_satisfiable :
    ∃ (keccak : List UInt8 → UInt256) (sibs : ℕ → UInt256),
      (⟨0, 0, 0⟩ : Leaf).nextIndex < 2 ^ 256
      ∧ (∀ i < setup.leafCount, (setup.leaf i).nextIndex < 2 ^ 256)
      ∧ KeccakBreakAtHead keccak setup 1 sibs 1 1 ⟨0, 0, 0⟩
      ∧ TreeRootBreak (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtHashLeaf keccak) setup 1
          sibs 1 1 ⟨0, 0, 0⟩ := by
  have hb : KeccakBreakAtHead (fun _ => 0) setup 1 (fun _ => 0) 1 1 ⟨0, 0, 0⟩ :=
    KeccakBreakAtHead.emptyLeaf rfl (le_refl 1) ⟨imtLeafPreimage_ne_tag _, rfl⟩
  exact ⟨fun _ => 0, fun _ => 0, by norm_num, fun _ _ => by show (0 : ℕ) < 2 ^ 256; positivity, hb,
    keccakBreakAtHead_is_treeRootBreak _ _ _ _ _ _ _ hb⟩

/-! ## The headline's premises are satisfiable -/

theorem nonInclusion_at_head_witness (keccak : List UInt8 → UInt256) (a b v : UInt256) (ha : 0 < a)
    (hab : a < b) (hv0 : v ≠ 0) (hva : v ≠ a) (hvb : v ≠ b) :
    ∃ (S₂ : CState) (r₂ : UInt256), CReachesAtHead keccak S₂ ∧ S₂.tree = threeLeafTree a b
      ∧ S₂.root = some r₂ ∧ v ∉ keys (toAbs S₂.tree) ∧ a ∈ keys (toAbs S₂.tree)
      ∧ (∃ (i : ℕ) (p : List UInt256), S₂.merklePath i = some p
          ∧ NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ v (S₂.tree.leaf i) i
              (FullMerkle.pathSibs p) p.length
          ∧ ¬ KeccakBreakAtHead keccak S₂.tree S₂.fm.height (FullMerkle.pathSibs p) p.length i
              (S₂.tree.leaf i))
      ∧ (∃ (i : ℕ) (p : List UInt256), S₂.merklePath i = some p
          ∧ InclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a (S₂.tree.leaf i) i
              (FullMerkle.pathSibs p) p.length
          ∧ ¬ KeccakBreakAtHead keccak S₂.tree S₂.fm.height (FullMerkle.pathSibs p) p.length i
              (S₂.tree.leaf i)) := by
  obtain ⟨_, _, S₂, _, r₂, _, _, _, hc₂, htree₂, _, _, hroot₂, _, _⟩ :=
    paddingAtHead_three_leaf_run (imtNodeHash keccak) (imtHashLeaf keccak) (imtEmptyLeafHash keccak)
      a b ha hab
  obtain ⟨R, hR, c1, c2⟩ := contract_proofs_at_stored_root_at_head keccak S₂ hc₂
  have hRr : R = r₂ := Option.some.inj (hR.symm.trans hroot₂)
  subst hRr
  have hmem : a ∈ keys (toAbs S₂.tree) := by
    rw [htree₂]
    exact (padding_collision_refunds_delivered_leg (imtNodeHash keccak) (imtHashLeaf keccak) ha
      hab).2.1
  have hnot : v ∉ keys (toAbs S₂.tree) := by
    rw [htree₂]
    intro hv
    obtain ⟨i, hi, hval⟩ := mem_keys_iff_index.mp hv
    rw [threeLeafTree_leafCount] at hi
    interval_cases i
    · exact hv0 (by simpa [threeLeafTree, insert, setup] using hval.symm)
    · exact hva (by simpa [threeLeafTree, insert, setup] using hval.symm)
    · exact hvb (by simpa [threeLeafTree, insert, setup] using hval.symm)
  obtain ⟨i, _, p, hp, _, hN, hnb⟩ := c2 v hv0 hnot
  obtain ⟨j, _, _, q, hq, _, hI, hnb'⟩ := c1 a hmem
  exact ⟨S₂, R, hc₂, htree₂, hR, hnot, hmem, ⟨i, p, hp, hN, hnb⟩, ⟨j, q, hq, hI, hnb'⟩⟩

end Contracts.InteropCommitmentTree

/-! ## Certificates -/

namespace Contracts.InteropCommitmentTree

theorem ImtEmptyLeafTagIsTheLiteral : Properties.ImtEmptyLeafTagIsTheLiteral :=
  imtEmptyLeafTag_is_the_literal
theorem ImtPreimagesDomainSeparated : Properties.ImtPreimagesDomainSeparated :=
  imt_preimages_domain_separated
theorem ImtPreimagesDetermineTheirInputs : Properties.ImtPreimagesDetermineTheirInputs :=
  imt_preimages_determine_their_inputs
theorem PinSetupIsPadAtZeroLeafHash : Properties.PinSetupIsPadAtZeroLeafHash :=
  pin_setup_is_pad_at_zeroLeafHash
theorem CSetupPadCaches : Properties.CSetupPadCaches := cSetupPad_caches
theorem CReachesPadRootIsPublished : Properties.CReachesPadRootIsPublished :=
  cReachesPad_root_is_published
theorem CRunPadReaches : Properties.CRunPadReaches := cRunPad_reaches
theorem CReachesPadViewsAreHReaches : Properties.CReachesPadViewsAreHReaches :=
  cReachesPad_views_are_hReaches
theorem NonInclusionAtHeadIsAbsentOrKeccakCollision :
    Properties.NonInclusionAtHeadIsAbsentOrKeccakCollision :=
  non_inclusion_at_head_is_absent_or_keccak_collision
theorem InclusionAtHeadIsPresentOrKeccakCollision :
    Properties.InclusionAtHeadIsPresentOrKeccakCollision :=
  inclusion_at_head_is_present_or_keccak_collision
theorem ProofsExclusiveAtHeadOrKeccakCollision :
    Properties.ProofsExclusiveAtHeadOrKeccakCollision :=
  proofs_exclusive_at_head_or_keccak_collision
theorem KeccakBreakAtHeadIsTreeRootBreak : Properties.KeccakBreakAtHeadIsTreeRootBreak :=
  keccakBreakAtHead_is_treeRootBreak
theorem PathCollisionAtHeadIffKeccak : Properties.PathCollisionAtHeadIffKeccak :=
  pathCollision_at_head_iff_keccak
theorem HeightBreakAtHeadIffKeccak : Properties.HeightBreakAtHeadIffKeccak :=
  heightBreak_at_head_iff_keccak
theorem PaddingHitAtHeadIffEmptyLeafCollision : Properties.PaddingHitAtHeadIffEmptyLeafCollision :=
  paddingHit_at_head_iff_emptyLeaf_collision
theorem PaddingHitAtPinNeedsNoCollision : Properties.PaddingHitAtPinNeedsNoCollision :=
  paddingHit_at_pin_needs_no_collision
theorem TreeRootBreakAtHeadIsKeccakCollision : Properties.TreeRootBreakAtHeadIsKeccakCollision :=
  treeRootBreak_at_head_is_keccak_collision
theorem HonestSiblingsAcceptExactly : Properties.HonestSiblingsAcceptExactly :=
  honest_siblings_accept_exactly
theorem PaddingAtHeadThreeLeafRun : Properties.PaddingAtHeadThreeLeafRun :=
  paddingAtHead_three_leaf_run
theorem PinForgeryAtHeadNeedsKeccakCollision : Properties.PinForgeryAtHeadNeedsKeccakCollision :=
  pin_forgery_at_head_needs_keccak_collision
theorem PinForgeryAtHeadFiresOnCollision : Properties.PinForgeryAtHeadFiresOnCollision :=
  pin_forgery_at_head_fires_on_collision
theorem NodeCollisionAtHeadFires : Properties.NodeCollisionAtHeadFires :=
  node_collision_at_head_fires
theorem LeafCollisionAtHeadFires : Properties.LeafCollisionAtHeadFires :=
  leaf_collision_at_head_fires
theorem OutOfRangeIndexAtHeadWitness : Properties.OutOfRangeIndexAtHeadWitness :=
  out_of_range_index_at_head_witness
theorem PaddingAtHeadBreakPremisesSatisfiable : Properties.PaddingAtHeadBreakPremisesSatisfiable :=
  paddingAtHead_break_premises_satisfiable
theorem PinForgeryAcceptedAtPinRejectedAtHead : Properties.PinForgeryAcceptedAtPinRejectedAtHead :=
  pin_forgery_accepted_at_pin_rejected_at_head
theorem OutOfRangeIndexAtHead : Properties.OutOfRangeIndexAtHead := out_of_range_index_at_head
theorem HonestProofNoKeccakBreakAtHead : Properties.HonestProofNoKeccakBreakAtHead :=
  honest_proof_no_keccak_break_at_head
theorem ContractProofsAtStoredRootAtHead : Properties.ContractProofsAtStoredRootAtHead :=
  contract_proofs_at_stored_root_at_head
theorem NonInclusionAtHeadWitness : Properties.NonInclusionAtHeadWitness :=
  nonInclusion_at_head_witness

end Contracts.InteropCommitmentTree
