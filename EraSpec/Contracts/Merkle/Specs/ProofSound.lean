import EraSpec.Contracts.FullMerkle.Specs.Model


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


end Clear.MerkleProofSound
