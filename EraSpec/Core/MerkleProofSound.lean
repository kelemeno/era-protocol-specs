import EraSpec.Core.Merkle

/- EXTRACTED from contracts-formal-verification (`specs/specs/MerkleProofSound.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  MERKLE PROOF SOUNDNESS — WITHOUT ASSUMING THE SIBLINGS ARE HONEST.

  Every walk result in the corpus so far is conditioned on `hsibs`: that the sibling stream holds the
  tree's own level nodes.  For a BUILDER that is fine — it fetches them.  For a VERIFIER it is
  exactly wrong: the path array is part of the Merkle proof, so an attacker chooses it.  A statement
  that assumes honest siblings says nothing about forged proofs.

  `RootForgery`'s header records an honest limitation: pair-injectivity pins the leaf against a FIXED
  sibling stream and pins ONE free sibling level, but "with two or more sibling levels free, an
  adversary could in principle pick a compensating pair".  That is true of walk-vs-WALK, where both
  sides are free.  It is NOT true of walk-vs-TREE-ROOT, and this file proves the difference.

  Peel the top level: the walk's last combine is `h u s`, the tree's root is `h` of two level-nodes,
  so pair-injectivity forces BOTH the accumulator and the sibling to be the tree's. Recurse.  Hence a
  walk that reaches the tree's root must have used the tree's own siblings at every level, and its
  leaf must be the tree's leaf at that index.  Nothing beyond `hinj` is needed — the extra strength
  comes from comparing against a root that is itself built by the level structure.

  This is the exact converse of `MerkleSpec.walkPure_levels`, and it is what makes root binding a
  statement about ATTACKER-SUPPLIED proofs.  Axiom-free.
-/

namespace Clear.MerkleProofSound

open Clear MerkleSpec

/-- Defaults are irrelevant in range (`MerkleSpec`'s copy is private). -/
private theorem getD_congr' : ∀ (L : List UInt256) (n : ℕ) (d₁ d₂ : UInt256),
    n < L.length → L.getD n d₁ = L.getD n d₂
  | [], _, _, _, hn => absurd hn (by simp)
  | _ :: _, 0, _, _, _ => rfl
  | _ :: t, n + 1, d₁, d₂, hn =>
    getD_congr' t n d₁ d₂ (by simp only [List.length_cons] at hn; omega)

private lemma div_div_pow (j k : ℕ) : j / 2 / 2 ^ k = j / 2 ^ (k + 1) := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ']

/-- **MERKLE PROOF SOUNDNESS.**  If a walk from index `j` with leaf value `x` and an ARBITRARY
sibling stream reaches the tree's level-`(lvl+k)` node above `j`, then

* `x` is the tree's own entry at `j`, and
* the sibling stream agreed with the tree's siblings at every level climbed.

So a forged proof cannot be accepted: pair-injectivity alone forces an accepted path to be the honest
one.  The exact converse of `MerkleSpec.walkPure_levels`. -/
theorem walk_pins_leaf_and_sibs (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L : List UInt256) (sibs : ℕ → UInt256) :
    ∀ (k lvl j : ℕ) (x : UInt256),
      j < (levels h z0 L lvl).length →
      walkPure h sibs lvl k j x
        = (levels h z0 L (lvl + k)).getD (j / 2 ^ k) (zeros h z0 (lvl + k)) →
      (levels h z0 L lvl).getD j (zeros h z0 lvl) = x
        ∧ ∀ l, lvl ≤ l → l < lvl + k →
            sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ (l - lvl))) (zeros h z0 l) := by
  intro k
  induction k with
  | zero =>
    intro lvl j x hj hw
    refine ⟨?_, fun l _ h2 => absurd h2 (by omega)⟩
    rw [walkPure_zero] at hw
    simpa using hw.symm
  | succ k ih =>
    intro lvl j x hj hw
    have hlen1 : j / 2 < (levels h z0 L (lvl + 1)).length := by
      rw [levels_succ, levelUp_length]; omega
    -- the walk's tail, re-indexed for the inductive hypothesis
    have harg : walkPure h sibs (lvl + 1) k (j / 2)
        (if j % 2 = 1 then h (sibs lvl) x else h x (sibs lvl))
        = (levels h z0 L ((lvl + 1) + k)).getD (j / 2 / 2 ^ k)
            (zeros h z0 ((lvl + 1) + k)) := by
      rw [walkPure_succ] at hw
      rw [show (lvl + 1) + k = lvl + (k + 1) from by omega, div_div_pow]
      exact hw
    obtain ⟨hIH, hsIH⟩ := ih (lvl + 1) (j / 2) _ hlen1 harg
    -- the parent entry combines the two children
    have hup : (levels h z0 L (lvl + 1)).getD (j / 2) (zeros h z0 (lvl + 1))
        = h ((levels h z0 L lvl).getD (2 * (j / 2)) (zeros h z0 (lvl + 1)))
            ((levels h z0 L lvl).getD (2 * (j / 2) + 1) (zeros h z0 lvl)) := by
      rw [levels_succ]
      exact levelUp_getD h (zeros h z0 lvl) (zeros h z0 (lvl + 1)) _ (j / 2) (by omega)
    rw [hup] at hIH
    -- the levels above are handled by the inductive hypothesis, re-indexed
    have habove : ∀ l, lvl + 1 ≤ l → l < lvl + (k + 1) →
        sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ (l - lvl))) (zeros h z0 l) := by
      intro l h1 h2
      have := hsIH l h1 (by omega)
      rw [show l - (lvl + 1) = (l - lvl) - 1 from by omega] at this
      rw [show j / 2 / 2 ^ (l - lvl - 1) = j / 2 ^ ((l - lvl - 1) + 1) from div_div_pow _ _,
          show (l - lvl - 1) + 1 = l - lvl from by omega] at this
      exact this
    by_cases hpar : j % 2 = 1
    · -- odd index: the walk's sibling is the LEFT child, the accumulator the right
      rw [if_pos hpar] at hIH
      rw [show 2 * (j / 2) = j - 1 from by omega,
          show j - 1 + 1 = j from by omega] at hIH
      obtain ⟨hs, hx⟩ := hinj _ _ _ _ hIH.symm
      refine ⟨hx.symm, ?_⟩
      intro l h1 h2
      rcases Nat.eq_or_lt_of_le h1 with heq | h1'
      · rw [← heq, show lvl - lvl = 0 from by omega, pow_zero, Nat.div_one,
            show sibIdx j = j - 1 from by simp [sibIdx, hpar]]
        exact hs.trans (getD_congr' _ (j - 1) _ _ (by omega))
      · exact habove l (by omega) h2
    · -- even index: the accumulator is the LEFT child, the walk's sibling the right
      rw [if_neg hpar] at hIH
      rw [show 2 * (j / 2) = j from by omega] at hIH
      obtain ⟨hx, hs⟩ := hinj _ _ _ _ hIH.symm
      refine ⟨(getD_congr' _ j (zeros h z0 lvl) (zeros h z0 (lvl + 1)) hj).trans hx.symm, ?_⟩
      intro l h1 h2
      rcases Nat.eq_or_lt_of_le h1 with heq | h1'
      · rw [← heq, show lvl - lvl = 0 from by omega, pow_zero, Nat.div_one,
            show sibIdx j = j + 1 from by simp [sibIdx, hpar]]
        exact hs
      · exact habove l (by omega) h2

/-- **FORGED PROOFS ARE REJECTED.**  Contrapositive at the leaf: if the tree's entry at `j` is not
`x`, no sibling stream whatsoever makes the walk reach the tree's node above `j`.

This is the statement a verifier's soundness rests on, and unlike `RootForgery`'s results it leaves
the attacker free to choose EVERY sibling. -/
theorem no_forged_walk (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L : List UInt256) (k lvl j : ℕ) (x : UInt256)
    (hj : j < (levels h z0 L lvl).length)
    (hne : (levels h z0 L lvl).getD j (zeros h z0 lvl) ≠ x) :
    ∀ sibs : ℕ → UInt256,
      walkPure h sibs lvl k j x
        ≠ (levels h z0 L (lvl + k)).getD (j / 2 ^ k) (zeros h z0 (lvl + k)) :=
  fun sibs hw => hne (walk_pins_leaf_and_sibs h z0 hinj L sibs k lvl j x hj hw).1

/-- **ROOT FORM.**  At `lvl = 0` and `k = height`, with the tree within capacity, the level-`height`
node above any index is the ROOT — so an accepted walk against a published root pins the leaf, for
arbitrary attacker-chosen siblings. -/
theorem walk_accept_pins_leaf_free_sibs (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ) (x : UInt256)
    (hj : j < L.length) (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height)
    (haccept : walkPure h sibs 0 height j x = rootOf h z0 L height) :
    L.getD j (zeros h z0 0) = x
      ∧ ∀ l, l < height → sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ l)) (zeros h z0 l) := by
  have hsingle : levels h z0 L height = [rootOf h z0 L height] :=
    levels_height_singleton h z0 L height hne hcap
  have hjq : j / 2 ^ height = 0 := Nat.div_eq_of_lt (by omega)
  have hroot : (levels h z0 L (0 + height)).getD (j / 2 ^ height) (zeros h z0 (0 + height))
      = rootOf h z0 L height := by
    rw [show (0 : ℕ) + height = height from by omega, hsingle, hjq]
    rfl
  obtain ⟨hx, hs⟩ := walk_pins_leaf_and_sibs h z0 hinj L sibs height 0 j x
    (by rw [levels_zero]; exact hj) (by rw [hroot]; exact haccept)
  refine ⟨?_, fun l hl => ?_⟩
  · rw [levels_zero] at hx; exact hx
  · have := hs l (by omega) (by omega)
    rw [show l - 0 = l from by omega] at this
    exact this

end Clear.MerkleProofSound
