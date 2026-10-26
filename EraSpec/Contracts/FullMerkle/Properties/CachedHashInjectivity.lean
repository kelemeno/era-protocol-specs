import EraSpec.Contracts.FullMerkle.Specs.CachedHashInjectivity

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


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


abbrev Properties.levelPairs_nil (z : UInt256) :=
  levelPairs z [] = []


abbrev Properties.levelPairs_single (z a : UInt256) :=
  levelPairs z [a] = [(a, z)]


abbrev Properties.levelPairs_cons₂ (z a b : UInt256) (rest : List UInt256) :=
  levelPairs z (a :: b :: rest) = (a, b) :: levelPairs z rest


/-- **`levelUp` IS INJECTIVE ON `P`-PAIRS.**  As `MerkleSpec.levelUp_inj`, but the node hash need
only be injective on pairs satisfying `P`, and `P` need only hold on the pairs the two levels
actually contribute. -/
abbrev Properties.levelUp_inj_on (h : Hash) (z : UInt256) {P : UInt256 → UInt256 → Prop}
    (hinj : ∀ a b c d : UInt256, P a b → P c d → h a b = h c d → a = c ∧ b = d) :=
  ∀ L₁ L₂ : List UInt256, L₁.length = L₂.length →
        PairsOK P z L₁ → PairsOK P z L₂ →
        levelUp h z L₁ = levelUp h z L₂ → L₁ = L₂


/-- **Equal level-`l` lists force equal leaves, on `P`-pairs.**  The restriction is needed at
every level below `l`, for both lists — which is exactly the set of pairs the tree hashes. -/
abbrev Properties.levels_inj_on (h : Hash) (z0 : UInt256) {P : UInt256 → UInt256 → Prop}
    (hinj : ∀ a b c d : UInt256, P a b → P c d → h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (hlen : L₁.length = L₂.length) :=
  ∀ l, (∀ l' < l, PairsOK P (zeros h z0 l') (levels h z0 L₁ l')) →
        (∀ l' < l, PairsOK P (zeros h z0 l') (levels h z0 L₂ l')) →
        levels h z0 L₁ l = levels h z0 L₂ l → L₁ = L₂


/-- **M-D ON CACHED PAIRS.**  For a non-full tree, the recomputed root pins the whole leaf list —
with node-hash injectivity required only on the pairs the tree's own levels hash.

This is the form the deployed hash can instantiate: `CachedHashInj.hashOf_pair_inj` supplies
`hinj` for `P := "cached in SF"`, and the pair obligation is linear in the tree size. -/
abbrev Properties.rootOf_inj_on (h : Hash) (z0 : UInt256) {P : UInt256 → UInt256 → Prop}
    (hinj : ∀ a b c d : UInt256, P a b → P c d → h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hne : L₁.length ≠ 0)
    (hcap : L₁.length ≤ 2 ^ height)
    (hp₁ : ∀ l < height, PairsOK P (zeros h z0 l) (levels h z0 L₁ l))
    (hp₂ : ∀ l < height, PairsOK P (zeros h z0 l) (levels h z0 L₂ l))
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :=
  L₁ = L₂


/-- The unrestricted M-D is the `P := True` instance — recorded so the restriction is visibly a
generalization of `MerkleSpec.rootOf_inj_of_h_inj`, not a parallel result. -/
abbrev Properties.rootOf_inj_of_h_inj_of_on (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hne : L₁.length ≠ 0)
    (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :=
  L₁ = L₂


/-- **Entry-level corollary, restricted.**  Equal roots force equal entries at every index —
the form `AttackVectors.RootBinding.getD_of_rootOf_eq` supplies to root binding, now on
`P`-restricted injectivity. -/
abbrev Properties.getD_of_rootOf_eq_on (h : Hash) (z0 : UInt256) {P : UInt256 → UInt256 → Prop}
    (hinj : ∀ a b c d : UInt256, P a b → P c d → h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hne : L₁.length ≠ 0)
    (hcap : L₁.length ≤ 2 ^ height)
    (hp₁ : ∀ l < height, PairsOK P (zeros h z0 l) (levels h z0 L₁ l))
    (hp₂ : ∀ l < height, PairsOK P (zeros h z0 l) (levels h z0 L₂ l))
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height)
    (i : ℕ) (dflt : UInt256) :=
  L₁.getD i dflt = L₂.getD i dflt


end Clear.MerkleCachedInj
