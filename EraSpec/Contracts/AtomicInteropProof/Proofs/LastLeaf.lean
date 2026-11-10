import EraSpec.Contracts.AtomicInteropProof.Properties.LastLeaf
import EraSpec.Contracts.Merkle.Proofs.Verifier
import EraSpec.Contracts.Merkle.Proofs.PathCollision

/-! # Proofs: the last-leaf check (see `../Specs/LastLeaf.lean`) -/

namespace MerkleSpec.LastLeaf

open Clear MerkleSpec MerkleSpec.Verifier


/-- Assuming both idealizations, a break is impossible. -/
theorem not_hashBreak {h : Hash} {z0 : UInt256} {L : List UInt256}
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (hsep : EntriesNotEmpty z0 L) : ¬ HashBreak h z0 L := by
  intro hb
  cases hb with
  | nodeCollision a b c d hne heq =>
    rcases hne with hac | hbd
    · exact hac (hinj a b c d heq).1
    · exact hbd (hinj a b c d heq).2
  | entryIsEmpty m hm heq => exact hsep m hm heq

/-! ## A zero node over an occupied subtree -/

/-- **A ZERO NODE CANNOT SIT OVER AN OCCUPIED LEAF.**  If the level-`l` node at `m`
reads as `zeros l` while the first leaf under it is occupied, peel the zero cascade:
either some node's children are not both zeros — a collision — or an occupied entry
is the empty constant.

No injectivity assumed. -/
theorem zero_subtree_or_break (h : Hash) (z0 : UInt256) (L : List UInt256) :
    ∀ (l m : ℕ), m * 2 ^ l < L.length →
      (levels h z0 L l).getD m (zeros h z0 l) = zeros h z0 l → HashBreak h z0 L := by
  intro l
  induction l with
  | zero =>
    intro m hm heq
    refine HashBreak.entryIsEmpty m (by simpa using hm) ?_
    simpa using heq
  | succ l ih =>
    intro m hm heq
    rw [levels_succ_getD, zeros_succ] at heq
    by_cases hA : (levels h z0 L l).getD (2 * m) (zeros h z0 l) = zeros h z0 l
    · by_cases hB : (levels h z0 L l).getD (2 * m + 1) (zeros h z0 l) = zeros h z0 l
      · refine ih (2 * m) ?_ hA
        have : 2 * m * 2 ^ l = m * 2 ^ (l + 1) := by rw [pow_succ]; ring
        rw [this]
        exact hm
      · exact HashBreak.nodeCollision _ _ _ _ (Or.inr hB) heq
    · exact HashBreak.nodeCollision _ _ _ _ (Or.inl hA) heq

/-! ## Where the path first goes left -/

private lemma div_pow_succ (N l : ℕ) : N / 2 ^ (l + 1) = N / 2 / 2 ^ l := by
  rw [Nat.div_div_eq_div_mul, mul_comm, ← pow_succ]

/-- **THE FIRST LEFT TURN SITS EXACTLY ABOVE `j + 1`.**  Below it every step went
right, so `j`'s low bits are all ones and the right sibling's subtree begins at
`j + 1`. -/
theorem exists_left_level : ∀ (height N : ℕ), N + 1 < 2 ^ height →
    ∃ l < height, N / 2 ^ l % 2 = 0 ∧ (N / 2 ^ l + 1) * 2 ^ l = N + 1 := by
  intro height
  induction height with
  | zero =>
    intro N hN
    rw [pow_zero] at hN
    omega
  | succ height ih =>
    intro N hN
    by_cases hpar : N % 2 = 0
    · exact ⟨0, by omega, by simpa using hpar, by simp⟩
    · have hN2 : N / 2 + 1 < 2 ^ height := by
        rw [pow_succ] at hN
        omega
      obtain ⟨l, hl, hev, heq⟩ := ih (N / 2) hN2
      refine ⟨l + 1, by omega, ?_, ?_⟩
      · rw [div_pow_succ]
        exact hev
      · rw [div_pow_succ, pow_succ, ← mul_assoc, heq]
        omega

/-! ## The theorem -/

/-- **THE CHECK IDENTIFIES THE LAST LEAF, OR BREAKS THE HASH.**  Stated over the
tree's own siblings, with no injectivity: if every left-child sibling on `j`'s path
is the empty-subtree hash, then `j` is the last occupied leaf — or a break is
exhibited. -/
theorem last_leaf_or_break (h : Hash) (z0 : UInt256) (L : List UInt256)
    (sibs : ℕ → UInt256) (height j : ℕ)
    (hcap : L.length ≤ 2 ^ height) (hj : j < L.length)
    (honest : ∀ l < height, sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ l)) (zeros h z0 l))
    (hzero : ∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l) :
    j + 1 = L.length ∨ HashBreak h z0 L := by
  by_cases hlast : j + 1 = L.length
  · exact Or.inl hlast
  · refine Or.inr ?_
    have hnext : j + 1 < L.length := by omega
    obtain ⟨l, hl, hev, heq⟩ := exists_left_level height j (lt_of_lt_of_le hnext hcap)
    have hsib : (levels h z0 L l).getD (j / 2 ^ l + 1) (zeros h z0 l) = zeros h z0 l := by
      have h1 := honest l hl
      rw [hzero l hl hev, show sibIdx (j / 2 ^ l) = j / 2 ^ l + 1 from by simp [sibIdx, hev]] at h1
      exact h1.symm
    exact zero_subtree_or_break h z0 L l (j / 2 ^ l + 1) (by rw [heq]; exact hnext) hsib

/-- **AND THE SAME FOR AN AUTHENTICATED PATH.**  When the path recomputes the tree's
own root, its siblings *are* the tree's (`MerkleSpec.Verifier.walk_pins`), so the
check's conclusion holds for the proof as submitted. -/
theorem accepted_last_leaf_or_break (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ) (x : UInt256)
    (hcap : L.length ≤ 2 ^ height) (hj : j < L.length)
    (haccept : walkPure h sibs 0 height j x = rootOf h z0 L height)
    (hzero : ∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l) :
    j + 1 = L.length ∨ HashBreak h z0 L := by
  refine last_leaf_or_break h z0 L sibs height j hcap hj ?_ hzero
  have hjcap : j < 2 ^ height := lt_of_lt_of_le hj hcap
  have hroot : (levels h z0 L (0 + height)).getD (j / 2 ^ height) (zeros h z0 (0 + height))
      = rootOf h z0 L height := by
    rw [Nat.zero_add, Nat.div_eq_of_lt hjcap, rootOf_def, getD_zero_headD]
  have hpin := (walk_pins h z0 hinj L sibs height 0 j x (by rw [hroot]; exact haccept)).2
  intro l hl
  have := hpin l (by omega) (by omega)
  rwa [Nat.sub_zero] at this

/-! ## Certificates -/

theorem NotHashBreak : Properties.NotHashBreak := @not_hashBreak
theorem LastLeafOrBreak : Properties.LastLeafOrBreak := last_leaf_or_break
theorem AcceptedLastLeafOrBreak : Properties.AcceptedLastLeafOrBreak := accepted_last_leaf_or_break


theorem HashBreakAlways : Properties.HashBreakAlways := by
  intro h z0 L
  obtain ⟨a, b, c, d, hne, he⟩ := MerkleSpec.Verifier.exists_pair_collision h
  refine .nodeCollision a b c d ?_ he
  by_contra hcd
  push_neg at hcd
  exact hne (by rw [hcd.1, hcd.2])

end MerkleSpec.LastLeaf
