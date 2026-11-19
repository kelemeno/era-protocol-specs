import EraSpec.Contracts.L2InteropCommitmentTree.History.Specs.PaddingForgeryPinned
import EraSpec.Protocol.Spec

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false

/-!
# History properties: the padding forgery at the interop pin `c67894b9`

**The record of an older commit, not a claim about `b17415d20`** (see the Specs module).  Each
statement sets the padding constant to the pin's `hashLeaf({0,0,0})` (`zeroLeafHash hl`, or
`hl ⟨0, 0, 0⟩`) and shows a forged non-inclusion proof accepted against the published or stored
root, for every node and leaf hash.  Proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.History.Proofs.PaddingForgeryPinned`.

These were `Contracts.InteropCommitmentTree.Properties.<name>` (TreeRoot, RunHeight, CachedRoot)
before round-9 consolidation; `handoff/2026-11-19/renames/imt.json` maps the names.
-/

namespace Contracts.InteropCommitmentTree.History

open IMTAbstract MerkleSpec MerkleSpec.Verifier AttackVectors.CapacityInvariant
open Contracts.InteropCommitmentTree Contracts.Protocol

/-- Without padding separation, every empty slot is a universal low leaf: in any
tree with an empty slot below capacity, the honest sibling path for that slot is
accepted by `verifyNonInclusion` with `{0,0,0}` as the low leaf, for EVERY
nonzero value.  No hash assumption is used — the proof is honest. -/
def Properties.PaddingCollisionForgesAbsence : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (T : Tree) (height : ℕ), T.leafCount < 2 ^ height →
    ∀ v : UInt256, 0 < v →
      NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl T height) v ⟨0, 0, 0⟩ T.leafCount
        (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl T) T.leafCount) height

/-- The padding collision refunds a delivered leg.  A real run from `setup` (two
guarded inserts, so the tree is `Valid`) has `a` delivered, and yet — with
`hashLeaf({0,0,0})` as the padding constant — `verifyNonInclusion` accepts an
absence proof for `a` against the tree's own root at its own height.  This is
the double spend the `IMT_EMPTY_LEAF_HASH` fix removes. -/
def Properties.PaddingCollisionRefundsDeliveredLeg : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    Valid (threeLeafTree a b)
      ∧ a ∈ keys (toAbs (threeLeafTree a b))
      ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2) a ⟨0, 0, 0⟩ 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2

/-- **THE BREAK FIRES WHERE THE BUG IS.**  On that instance the honest inclusion
proof locates no break, and the forged absence proof's break is `paddingHit`. -/
def Properties.PaddingCountermodelLocatesPaddingHit : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256),
    ¬ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2
        (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 1) 2 1
        ((threeLeafTree a b).leaf 1)
      ∧ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2
        (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2 3 ⟨0, 0, 0⟩

/-- **THE PADDING COUNTERMODEL'S BREAK IS EXACTLY `paddingHit`.**  Sharpens
`Properties.PaddingCountermodelLocatesPaddingHit`: on the forged absence proof at slot 3
of `threeLeafTree a b`, no case other than `paddingHit` holds. -/
def Properties.PaddingCountermodelExactlyPaddingHit : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256),
    TreeRootBreakExactly h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2
      (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2 3 ⟨0, 0, 0⟩ .paddingHit

/-- **THE PADDING FORGERY IS LIVE AT THE SOURCE'S OWN HEIGHT.**  `threeLeafTree a b` is
published at height 2 by the source's own growth rule, not by a choice of the
statement.  With the extraction-pin padding `hl ⟨0,0,0⟩`, against `hThree a b`'s root at
its own height, `a` has an accepted honest inclusion proof (leaf 1) with no located break
AND an accepted non-inclusion proof (slot 3), whose located break is exactly
`paddingHit`.  So clause 3 of `ProofsExclusiveOrBreakAtOwnHeight` has its premises met on
a reached state, and its first break disjunct is false there.  `hThree a b` is step 2
of `hThreeRun a b`, so the same holds for `RunRootsExclusiveOrBreakAtOwnHeight`. -/
def Properties.PaddingForgeryAtOwnHeight : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    HReaches hSetup (hThree a b) ∧ hThreeRun a b 2 = hThree a b ∧ (hThree a b).height = 2
      ∧ InclusionAccepted h hl ((hThree a b).root h (hl ⟨0, 0, 0⟩) hl) a
          ((hThree a b).tree.leaf 1) 1
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (hThree a b).tree) 1) (hThree a b).height
      ∧ NonInclusionAccepted h hl ((hThree a b).root h (hl ⟨0, 0, 0⟩) hl) a ⟨0, 0, 0⟩ 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (hThree a b).tree) 3) (hThree a b).height
      ∧ ¬ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (hThree a b).tree (hThree a b).height
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (hThree a b).tree) 1) (hThree a b).height 1
          ((hThree a b).tree.leaf 1)
      ∧ TreeRootBreakExactly h (hl ⟨0, 0, 0⟩) hl (hThree a b).tree (hThree a b).height
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (hThree a b).tree) 3) (hThree a b).height 3
          ⟨0, 0, 0⟩ .paddingHit

/-- **THE PREMISES ARE SATISFIABLE, AND THE PADDING FORGERY HITS THE STORED ROOT.**  For
every node and leaf hash and `0 < a < b`, the run `setup; insert a at 0; insert b at 1`
with whole storage does not revert.  It reaches `threeLeafTree a b` with the view
`hThree a b` at height 2, and `root()` returns the `newRoot` of the last insert, `r₂`.
Against `r₂`:

* the contract's own `merklePath(1)` is an accepted inclusion proof for `a`;
* the contract refuses `merklePath(3)` (slot 3 is empty);
* yet the honest siblings of slot 3 are an accepted non-inclusion proof for the delivered
  `a` with the zero leaf, whose located break is exactly `paddingHit`.

So clauses 1 and 3 of `ContractProofsAtStoredRoot` have their premises met, and the
forged absence proof is against the root the contract stores, not a modelled one. -/
def Properties.CThreeLeafWitness : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    ∃ (S₀ S₁ S₂ : CState) (r₁ r₂ : UInt256),
      cSetup h hl = some S₀ ∧ cInsert h hl S₀ a 0 = some (S₁, r₁)
      ∧ cInsert h hl S₁ b 1 = some (S₂, r₂)
      ∧ CReaches h hl S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.toH = hThree a b
      ∧ S₁.fm.height = 1 ∧ S₂.fm.height = 2 ∧ S₂.root = some r₂
      ∧ (∃ p : List UInt256, S₂.merklePath 1 = some p
          ∧ InclusionAccepted h hl r₂ a (S₂.tree.leaf 1) 1 (FullMerkle.pathSibs p) p.length)
      ∧ S₂.merklePath 3 = none
      ∧ NonInclusionAccepted h hl r₂ a ⟨0, 0, 0⟩ 3
          (honestSibs h (zeroLeafHash hl) (leafHashes hl S₂.tree) 3) 2
      ∧ TreeRootBreakExactly h (zeroLeafHash hl) hl S₂.tree 2
          (honestSibs h (zeroLeafHash hl) (leafHashes hl S₂.tree) 3) 2 3 ⟨0, 0, 0⟩ .paddingHit

end Contracts.InteropCommitmentTree.History
