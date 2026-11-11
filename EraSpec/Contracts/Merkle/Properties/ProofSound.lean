import EraSpec.Contracts.Merkle.Specs.ProofSound

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


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


/-- **MERKLE PROOF SOUNDNESS.**  If a walk from index `j` with leaf value `x` and an ARBITRARY
sibling stream reaches the tree's level-`(lvl+k)` node above `j`, then

* `x` is the tree's own entry at `j`, and
* the sibling stream agreed with the tree's siblings at every level climbed.

So a forged proof cannot be accepted: pair-injectivity alone forces an accepted path to be the honest
one.  The exact converse of `MerkleSpec.walkPure_levels`. -/
abbrev Properties.walk_pins_leaf_and_sibs (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L : List UInt256) (sibs : ℕ → UInt256) :=
  ∀ (k lvl j : ℕ) (x : UInt256),
        j < (levels h z0 L lvl).length →
        walkPure h sibs lvl k j x
          = (levels h z0 L (lvl + k)).getD (j / 2 ^ k) (zeros h z0 (lvl + k)) →
        (levels h z0 L lvl).getD j (zeros h z0 lvl) = x
          ∧ ∀ l, lvl ≤ l → l < lvl + k →
              sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ (l - lvl))) (zeros h z0 l)


/-- **FORGED PROOFS ARE REJECTED.**  Contrapositive at the leaf: if the tree's entry at `j` is not
`x`, no sibling stream whatsoever makes the walk reach the tree's node above `j`.

This is the statement a verifier's soundness rests on, and unlike `RootForgery`'s results it leaves
the attacker free to choose EVERY sibling. -/
abbrev Properties.no_forged_walk (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L : List UInt256) (k lvl j : ℕ) (x : UInt256)
    (hj : j < (levels h z0 L lvl).length)
    (hne : (levels h z0 L lvl).getD j (zeros h z0 lvl) ≠ x) :=
  ∀ sibs : ℕ → UInt256,
        walkPure h sibs lvl k j x
          ≠ (levels h z0 L (lvl + k)).getD (j / 2 ^ k) (zeros h z0 (lvl + k))


/-- **ROOT FORM.**  At `lvl = 0` and `k = height`, with the tree within capacity, the level-`height`
node above any index is the ROOT — so an accepted walk against a published root pins the leaf, for
arbitrary attacker-chosen siblings. -/
abbrev Properties.walk_accept_pins_leaf_free_sibs (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L : List UInt256) (sibs : ℕ → UInt256) (height j : ℕ) (x : UInt256)
    (hj : j < L.length) (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height)
    (haccept : walkPure h sibs 0 height j x = rootOf h z0 L height) :=
  L.getD j (zeros h z0 0) = x
        ∧ ∀ l, l < height → sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ l)) (zeros h z0 l)


end Clear.MerkleProofSound
