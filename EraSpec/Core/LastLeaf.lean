import EraSpec.Core.MerkleVerifier

/-!
# The last-leaf proof, and what breaking it would cost

`_verifyLastBatchInRoot` establishes that a batch leaf is the **last** leaf of its
chain's batch tree inside an aggregated root, and it does so with a shape argument
rather than a count:

    /// @dev Verifies that the proven batch leaf is the LAST leaf of the source chain's batch tree
    /// inside the aggregated root: on every level of the batch-leaf Merkle path where the current
    /// node is a left child (mask bit 0), the right sibling must be the empty-subtree hash for that
    /// level (`zeros[0] = CHAIN_TREE_EMPTY_ENTRY_HASH`, `zeros[i+1] = keccak(zeros[i] || zeros[i])`).
    /// A non-last leaf necessarily has a populated right subtree on some level, whose hash cannot
    /// collide with the zero cascade.

This file proves that, in the form the comment's last sentence suggests: not "assume
the hash is injective, therefore the leaf is last", but **the leaf is last, or you
have produced a concrete collision**.  `HashBreak` is that alternative, and it has
exactly two constructors because there are exactly two ways out — a genuine node
collision, or a real entry that equals the empty-entry constant.

## The argument

Let `j` be the proven leaf and suppose leaf `j+1` is also occupied.  Walk up from
`j` to the first level `l` where the path goes left.  Below that level every step
went right, so `j`'s low `l` bits are all ones and the right sibling's subtree
*starts exactly at* `j+1` (`exists_left_level`).  The check says that sibling is
`zeros l`.  But its subtree contains an occupied leaf, and peeling
`zeros (l+1) = h (zeros l) (zeros l)` down that subtree either hits a node whose two
children are not both zeros — a collision — or bottoms out at an occupied level-0
entry equal to `z0` (`zero_subtree_or_break`).

Nothing in either lemma assumes injectivity.  Injectivity enters only where the
path has to be pinned to the tree's own siblings, which is
`MerkleSpec.Verifier.walk_pins`, and `not_hashBreak` is the corollary that closes
the disjunction when one is willing to assume both idealizations.
-/

namespace MerkleSpec.LastLeaf

open Clear MerkleSpec MerkleSpec.Verifier

/-- What a failure of the last-leaf argument exhibits.

`nodeCollision` is a genuine keccak collision on a 64-byte node preimage.
`entryIsEmpty` is a domain-separation failure: an occupied leaf of the chain tree
equal to `CHAIN_TREE_EMPTY_ENTRY_HASH`, the constant the empty positions carry. -/
inductive HashBreak (h : Hash) (z0 : UInt256) (L : List UInt256) : Prop
  | nodeCollision (a b c d : UInt256) : (a ≠ c ∨ b ≠ d) → h a b = h c d → HashBreak h z0 L
  | entryIsEmpty (m : ℕ) : m < L.length → L.getD m z0 = z0 → HashBreak h z0 L

/-- The chain tree's domain separation: no occupied entry is the empty-entry
constant.  With this and node injectivity there is no way out — see
`not_hashBreak`. -/
def EntriesNotEmpty (z0 : UInt256) (L : List UInt256) : Prop :=
  ∀ m < L.length, L.getD m z0 ≠ z0

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

end MerkleSpec.LastLeaf
