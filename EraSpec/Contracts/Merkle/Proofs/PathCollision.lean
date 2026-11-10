import EraSpec.Contracts.Merkle.Properties.PathCollision
import EraSpec.Contracts.Merkle.Proofs.Verifier

/-! # Proofs: the positional-collision extractor (see `../Specs/PathCollision.lean`) -/

namespace MerkleSpec.Verifier

open Clear MerkleSpec

private lemma div_div_pow' (j k : ℕ) : j / 2 / 2 ^ k = j / 2 ^ (k + 1) := by
  rw [Nat.div_div_eq_div_mul, show 2 * 2 ^ k = (2 : ℕ) ^ (k + 1) from by ring]

lemma walkStep_hash (h : Hash) (sibs : ℕ → UInt256) (lvl j : ℕ) (x : UInt256) :
    h (walkStep sibs lvl j x).1 (walkStep sibs lvl j x).2
      = if j % 2 = 1 then h (sibs lvl) x else h x (sibs lvl) := by
  unfold walkStep; split <;> rfl

lemma walkPair_succ (h : Hash) (sibs : ℕ → UInt256) (lvl j : ℕ) (x : UInt256) (i : ℕ) :
    walkPair h sibs lvl j x (i + 1)
      = walkPair h sibs (lvl + 1) (j / 2) (h (walkStep sibs lvl j x).1 (walkStep sibs lvl j x).2) i :=
  rfl

lemma treePair_shift (h : Hash) (z0 : UInt256) (L : List UInt256) (lvl j i : ℕ) :
    treePair h z0 L (lvl + (i + 1)) (j / 2 ^ (i + 1)) = treePair h z0 L (lvl + 1 + i) (j / 2 / 2 ^ i) := by
  rw [div_div_pow', show lvl + (i + 1) = lvl + 1 + i from by omega]

/-- The level-`l` parent equation, phrased with `treePair`. -/
lemma hash_treePair (h : Hash) (z0 : UInt256) (L : List UInt256) (lvl j : ℕ) :
    h (treePair h z0 L lvl j).1 (treePair h z0 L lvl j).2
      = (levels h z0 L (lvl + 1)).getD (j / 2) (zeros h z0 (lvl + 1)) :=
  (levels_succ_getD h z0 L lvl (j / 2)).symm

theorem walk_pins_or_collision (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) :
    ∀ (k lvl j : ℕ) (x : UInt256),
      walkPure h sibs lvl k j x
          = (levels h z0 L (lvl + k)).getD (j / 2 ^ k) (zeros h z0 (lvl + k)) →
        ((levels h z0 L lvl).getD j (zeros h z0 lvl) = x
          ∧ ∀ l, lvl ≤ l → l < lvl + k →
              sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ (l - lvl))) (zeros h z0 l))
        ∨ PathCollision h z0 L sibs lvl k j x := by
  intro k
  induction k with
  | zero =>
    intro lvl j x hw
    left
    refine ⟨?_, fun l _ h2 => absurd h2 (by omega)⟩
    have e : walkPure h sibs lvl 0 j x = x := rfl
    rw [e] at hw
    simpa using hw.symm
  | succ k ih =>
    intro lvl j x hw
    have harg : walkPure h sibs (lvl + 1) k (j / 2)
        (h (walkStep sibs lvl j x).1 (walkStep sibs lvl j x).2)
        = (levels h z0 L ((lvl + 1) + k)).getD (j / 2 / 2 ^ k) (zeros h z0 ((lvl + 1) + k)) := by
      have e : walkPure h sibs lvl (k + 1) j x = walkPure h sibs (lvl + 1) k (j / 2)
          (if j % 2 = 1 then h (sibs lvl) x else h x (sibs lvl)) := rfl
      rw [e, ← walkStep_hash] at hw
      rw [show (lvl + 1) + k = lvl + (k + 1) from by omega, div_div_pow']
      exact hw
    rcases ih (lvl + 1) (j / 2) _ harg with ⟨hIH, hsIH⟩ | ⟨i, hi, hne, heq⟩
    · rw [← hash_treePair] at hIH
      by_cases hpe : walkStep sibs lvl j x = treePair h z0 L lvl j
      · left
        have habove : ∀ l, lvl + 1 ≤ l → l < lvl + (k + 1) →
            sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ (l - lvl))) (zeros h z0 l) := by
          intro l h1 h2
          have := hsIH l h1 (by omega)
          rw [show l - (lvl + 1) = (l - lvl) - 1 from by omega, div_div_pow',
            show (l - lvl - 1) + 1 = l - lvl from by omega] at this
          exact this
        simp only [walkStep, treePair] at hpe
        by_cases hpar : j % 2 = 1
        · rw [if_pos hpar] at hpe
          simp only [Prod.mk.injEq] at hpe
          obtain ⟨hs, hx⟩ := hpe
          rw [show 2 * (j / 2) = j - 1 from by omega] at hs hx
          rw [show j - 1 + 1 = j from by omega] at hx
          refine ⟨hx.symm, ?_⟩
          intro l h1 h2
          rcases Nat.eq_or_lt_of_le h1 with he | h1'
          · rw [← he, show lvl - lvl = 0 from by omega, pow_zero, Nat.div_one,
              show sibIdx j = j - 1 from by simp [sibIdx, hpar]]
            exact hs
          · exact habove l (by omega) h2
        · rw [if_neg hpar] at hpe
          simp only [Prod.mk.injEq] at hpe
          obtain ⟨hx, hs⟩ := hpe
          rw [show 2 * (j / 2) = j from by omega] at hs hx
          refine ⟨hx.symm, ?_⟩
          intro l h1 h2
          rcases Nat.eq_or_lt_of_le h1 with he | h1'
          · rw [← he, show lvl - lvl = 0 from by omega, pow_zero, Nat.div_one,
              show sibIdx j = j + 1 from by simp [sibIdx, hpar]]
            exact hs
          · exact habove l (by omega) h2
      · right
        refine ⟨0, by omega, ?_, ?_⟩
        · simpa [walkPair] using hpe
        · simp only [walkPair, Nat.add_zero, pow_zero, Nat.div_one]
          exact hIH.symm
    · right
      refine ⟨i + 1, by omega, ?_, ?_⟩
      · rw [walkPair_succ, treePair_shift]; exact hne
      · rw [walkPair_succ, treePair_shift]; exact heq

theorem accept_pins_entry_or_collision (h : Hash) (z0 : UInt256) (L : List UInt256)
    (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256) (hj : j < 2 ^ k)
    (haccept : walkPure h sibs 0 k j x = rootOf h z0 L k) :
    L.getD j z0 = x ∨ PathCollision h z0 L sibs 0 k j x := by
  have hroot : (levels h z0 L (0 + k)).getD (j / 2 ^ k) (zeros h z0 (0 + k)) = rootOf h z0 L k := by
    rw [Nat.zero_add, Nat.div_eq_of_lt hj, rootOf_def, getD_zero_headD]
  rcases walk_pins_or_collision h z0 L sibs k 0 j x (by rw [hroot]; exact haccept) with ⟨he, _⟩ | hc
  · left; simpa using he
  · right; exact hc

/-- One honest step hashes exactly the tree's pair. -/
lemma walkStep_honest (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256)
    (lvl j : ℕ) (x : UInt256)
    (hs : sibs lvl = (levels h z0 L lvl).getD (sibIdx j) (zeros h z0 lvl))
    (hx : x = (levels h z0 L lvl).getD j (zeros h z0 lvl)) :
    walkStep sibs lvl j x = treePair h z0 L lvl j := by
  unfold walkStep treePair
  by_cases hpar : j % 2 = 1
  · rw [if_pos hpar, hs, hx, show sibIdx j = j - 1 from by simp [sibIdx, hpar],
      show 2 * (j / 2) = j - 1 from by omega, show j - 1 + 1 = j from by omega]
  · rw [if_neg hpar, hs, hx, show sibIdx j = j + 1 from by simp [sibIdx, hpar],
      show 2 * (j / 2) = j from by omega]

theorem walkPair_honest (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) :
    ∀ (i lvl j : ℕ) (x : UInt256),
      (∀ l, lvl ≤ l → l ≤ lvl + i →
        sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ (l - lvl))) (zeros h z0 l)) →
      x = (levels h z0 L lvl).getD j (zeros h z0 lvl) →
      walkPair h sibs lvl j x i = treePair h z0 L (lvl + i) (j / 2 ^ i) := by
  have h0 : ∀ (lvl j : ℕ) (x : UInt256),
      (∀ l, lvl ≤ l → l ≤ lvl →
        sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ (l - lvl))) (zeros h z0 l)) →
      x = (levels h z0 L lvl).getD j (zeros h z0 lvl) →
      walkStep sibs lvl j x = treePair h z0 L lvl j := by
    intro lvl j x hs hx
    have hsl := hs lvl le_rfl le_rfl
    rw [show lvl - lvl = 0 from by omega, pow_zero, Nat.div_one] at hsl
    exact walkStep_honest h z0 L sibs lvl j x hsl hx
  intro i
  induction i with
  | zero =>
    intro lvl j x hs hx
    simp only [walkPair, Nat.add_zero, pow_zero, Nat.div_one]
    exact h0 lvl j x (fun l h1 h2 => hs l h1 (by omega)) hx
  | succ i ih =>
    intro lvl j x hs hx
    have hstep := h0 lvl j x (fun l h1 h2 => hs l h1 (by omega)) hx
    rw [walkPair_succ, treePair_shift, hstep, hash_treePair h z0 L lvl j]
    refine ih (lvl + 1) (j / 2) _ ?_ rfl
    intro l h1 h2
    have := hs l (by omega) (by omega)
    rw [show l - lvl = (l - (lvl + 1)) + 1 from by omega, ← div_div_pow'] at this
    exact this

theorem honest_walk_no_collision (h : Hash) (z0 : UInt256) (L : List UInt256) (height j : ℕ) :
    ¬ PathCollision h z0 L (honestSibs h z0 L j) 0 height j (L.getD j z0) := by
  rintro ⟨i, _, hne, _⟩
  apply hne
  refine walkPair_honest h z0 L _ i 0 j _ ?_ (by simp)
  intro l _ _
  simp [honestSibs]

/-- Pigeonhole: every `UInt256 → UInt256 → UInt256` has a collision.  This is why a bare
"…or some collision exists" conclusion says nothing. -/
theorem exists_pair_collision (f : UInt256 → UInt256 → UInt256) :
    ∃ a b c d : UInt256, (a, b) ≠ (c, d) ∧ f a b = f c d := by
  by_contra hno
  push_neg at hno
  have hf : Function.Injective (fun p : UInt256 × UInt256 => f p.1 p.2) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ he
    by_contra hne
    exact hno a b c d hne he
  have hc := Fintype.card_le_of_injective _ hf
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  have hpos : 1 < UInt256.size := by decide
  nlinarith

/-! ## Certificates -/

theorem WalkPinsOrCollision : Properties.WalkPinsOrCollision :=
  fun h z0 L sibs k lvl j x hw => walk_pins_or_collision h z0 L sibs k lvl j x hw
theorem AcceptPinsEntryOrCollision : Properties.AcceptPinsEntryOrCollision :=
  accept_pins_entry_or_collision
theorem HonestWalkNoCollision : Properties.HonestWalkNoCollision := honest_walk_no_collision

end MerkleSpec.Verifier
