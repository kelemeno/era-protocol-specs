import EraSpec.Contracts.FullMerkle.Specs.Model


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/RootForgery.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  ROOT-FORGERY / FALSE-INCLUSION ATTACK VECTORS — the adversarial reading of
  the pure Merkle layer (`specs/MerkleSpec.lean`).

  Everything here is parameterized over an abstract two-child node hash `h`
  together with the PAIR-INJECTIVITY HYPOTHESIS

      hinj : ∀ a b c d, h a b = h c d → a = c ∧ b = d

  which is the abstract stand-in for keccak collision-resistance.  It is a
  HYPOTHESIS of every theorem below — never an axiom, never a `sorry`.  It is
  discharged downstream where `h` is instantiated from the keccak cache (R6).

  Attack vectors covered:

  (a) FALSE INCLUSION (Merkle path soundness).  An attacker publishes a root
      and then claims a leaf value at some index that differs from the honest
      one.  `no_false_inclusion` — equal-width, non-empty, in-capacity leaf
      lists with the SAME root agree at EVERY index; `root_ne_of_leaf_ne` is
      the contrapositive a verifier uses (differ anywhere ⟹ roots differ).
      Engine: `MerkleSpec.rootOf_inj_of_h_inj` (M-D), repackaged pointwise —
      which is the shape an inclusion-proof verifier actually needs.

  (b) PATH FORGERY.  An attacker presents two DIFFERENT leaf values at the
      same index with the SAME sibling path and reaches the same root.
      `no_path_forgery` / `path_forgery_changes_walk` rule this out for the
      walk itself (`MerkleSpec.walkPure_inj`), and `walk_accept_pins_leaf`
      is the composite: combining `MerkleSpec.walkPure_update_orig` (the walk
      IS the whole-tree recomputation of `leaves.set idx x`) with walk
      injectivity, a verifier that accepts a walk against a published root
      simultaneously (i) learns that the published root is the recomputed root
      of the updated tree and (ii) pins the leaf at `idx` uniquely.

  (c) SIBLING SUBSTITUTION.  `walk_congr_sibs_on_climbed` — the walk reads the
      sibling stream only on the levels it climbs, so tampering OUTSIDE
      `[lvl, lvl+k)` is a no-op (nothing is gained, nothing is broken).
      `leaf_substitution_changes_walk` — changing ONLY the leaf, keeping the
      siblings fixed, always changes the walk result.
      `single_sibling_substitution` — changing EXACTLY ONE sibling level (all
      other levels held fixed) also cannot preserve the walk result.

      *** SCOPE, CORRECTED ***  The limitation below is real but narrower than
      it reads, and `specs/MerkleProofSound.lean` now proves the missing part.
      Against ANOTHER WALK — both sides free — `hinj` alone indeed does not
      forbid a compensating multi-level sibling change. Against a TREE ROOT it
      does: peeling the top combine forces the accumulator AND the sibling to be
      the tree's, level by level, so an accepted walk must have used the honest
      siblings (`walk_pins_leaf_and_sibs`). The claim below should be read as
      being about walk-vs-walk only.

      *** HONEST LIMITATION (walk-vs-walk) ***  We do NOT claim, and it is NOT
      provable from `hinj` alone, that an arbitrary change to the sibling stream
      cannot preserve another WALK's value.  With two or more sibling levels free, an adversary
      could in principle pick a compensating pair of sibling values whose
      combines happen to coincide: pair-injectivity constrains each `h`-node
      individually, but it says nothing that forbids a different (leaf,
      sibling-stream) pair from hashing up to the same value once BOTH the
      accumulator and the siblings are allowed to move.  Ruling that out needs
      genuinely more than `hinj` (e.g. that the walk's sibling reads are
      themselves bound to committed storage — the atlas/storage-binding layer,
      not this pure layer).  Only the leaf-injectivity direction, and the
      one-free-sibling-level direction, are established here.

  (d) APPEND FORGERY.  An attacker appends a different leaf at the frontier
      and claims the honest root.  `no_append_forgery` is the `rootOf` form
      (`MerkleSpec.rootOf_append_inj`); `no_append_forgery_walk` is the form
      about the WALK the contract actually performs, obtained by pushing the
      honest root through `MerkleSpec.rootOf_append` (M-B).

  Auxiliary lemma proved here (not available in `MerkleSpec`):
  `walkPure_add`, the split of a `k₁ + k₂`-step walk into two walks; used only
  by `single_sibling_substitution`.

  No new axioms, no `sorry`.  Pure list/arithmetic reasoning on top of
  `MerkleSpec`; no EVM semantics.
-/

namespace AttackVectors.RootForgery


open Clear

open MerkleSpec


end AttackVectors.RootForgery
