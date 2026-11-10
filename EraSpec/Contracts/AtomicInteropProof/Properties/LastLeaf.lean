import EraSpec.Contracts.AtomicInteropProof.Specs.LastLeaf

/-!
# Properties: the last-leaf check identifies the last leaf, or breaks the hash

`_verifyLastBatchInRoot` requires every left-child sibling on the proven leaf's
path to be the empty-subtree hash.  The statements below do not assume hash
injectivity: the conclusion is "the leaf is last, **or** a `HashBreak` is
exhibited".  Proofs: `../Proofs/LastLeaf.lean`.
-/

namespace MerkleSpec.LastLeaf

open Clear MerkleSpec MerkleSpec.Verifier

/-- Assuming both idealizations — node pair injectivity and no occupied entry equal
to the empty-entry constant — a `HashBreak` is impossible. -/
def Properties.NotHashBreak : Prop :=
  ∀ {h : Hash} {z0 : UInt256} {L : List UInt256},
    (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) → EntriesNotEmpty z0 L →
    ¬ HashBreak h z0 L

/-- **THE CHECK IDENTIFIES THE LAST LEAF, OR BREAKS THE HASH.**  Over the tree's own
siblings, with no injectivity: if every left-child sibling on `j`'s path is the
empty-subtree hash, then `j` is the last occupied leaf, or a break is exhibited. -/
def Properties.LastLeafOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ),
    L.length ≤ 2 ^ height → j < L.length →
    (∀ l < height, sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ l)) (zeros h z0 l)) →
    (∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l) →
    j + 1 = L.length ∨ HashBreak h z0 L

/-- **AND THE SAME FOR AN AUTHENTICATED PATH.**  When the submitted path recomputes the
tree's own root, its siblings are the tree's (`MerkleSpec.Verifier.walk_pins`; this
step uses pair injectivity), so the check's conclusion holds for the proof as
submitted. -/
def Properties.AcceptedLastLeafOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256), (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) →
    ∀ (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ) (x : UInt256),
      L.length ≤ 2 ^ height → j < L.length →
      walkPure h sibs 0 height j x = rootOf h z0 L height →
      (∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l) →
      j + 1 = L.length ∨ HashBreak h z0 L

end MerkleSpec.LastLeaf
