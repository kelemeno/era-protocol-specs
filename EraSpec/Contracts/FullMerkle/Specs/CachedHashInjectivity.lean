import EraSpec.Contracts.FullMerkle.Specs.Model


/- EXTRACTED from contracts-formal-verification (`specs/specs/MerkleCachedInj.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  M-D, RESTRICTED TO THE PAIRS THE TREE ACTUALLY HASHES.

  `MerkleSpec.rootOf_inj_of_h_inj` asks for node-hash pair-injectivity at ALL arguments:

      hinj : ∀ a b c d, h a b = h c d → a = c ∧ b = d

  `specs/CachedHashInj.lean` derived pair-injectivity for the deployed hash `hashOf SF`, but only
  ON CACHED PAIRS — necessarily, since an uncached pair hashes to `0` and injectivity fails
  vacuously off the cache.  So M-D could not be instantiated with the contract's own hash: the
  last instance of the over-strength that forced four weakenings in `FoldWalkBridge` and the
  restricted form of `root_binding`.

  This file removes it.  `levelUp` hashes exactly the ADJACENT PAIRS of a level (plus
  `(last, zero)` when the level has odd length), so the pairs M-D's induction touches are
  enumerable: `levelPairs`.  Restricting injectivity to a predicate `P` holding on those pairs is
  then enough, and a "cached in SF" predicate is such a `P` — with a pair count linear in the tree
  size rather than universal.

  The unrestricted theorems are derived from the restricted ones as the `P := True` instances, so
  this is a generalization rather than a parallel development.  Axiom-free.
-/

namespace Clear.MerkleCachedInj


open Clear MerkleSpec


/-- The pairs `levelUp` hashes at one level: adjacent pairs, and `(last, z)` if odd-length. -/
def levelPairs (z : UInt256) : List UInt256 → List (UInt256 × UInt256)
  | [] => []
  | [a] => [(a, z)]
  | a :: b :: rest => (a, b) :: levelPairs z rest


/-- Every pair a level's `levelUp` hashes satisfies `P` — the restriction hypothesis, named. -/
def PairsOK (P : UInt256 → UInt256 → Prop) (z : UInt256) (L : List UInt256) : Prop :=
  ∀ p ∈ levelPairs z L, P p.1 p.2


end Clear.MerkleCachedInj
