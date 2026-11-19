import EraSpec.Contracts.IndexedMerkleTree.History.Specs.PinnedGate

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false

/-!
# History properties: the deployed reclaim gate at the interop pin `c67894b9`

**The record of an older commit, not a claim about `b17415d20`** (see the Specs module).  Every
statement sets the padding constant to the pin's `hashLeaf({0,0,0})`.  Proofs in
`EraSpec.Contracts.IndexedMerkleTree.History.Proofs.PinnedGate`.

These were `IMTAbstract.ReclaimGateFaithful.Properties.<name>` before round-9 consolidation;
`handoff/2026-11-19/renames/imt.json` maps the names.
-/

namespace IMTAbstract.ReclaimGateFaithful.History

open Clear IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree
open IMTAbstract.ReclaimGateFaithful

/-- **AT THE PIN, AN EMPTY SLOT OPENS THE ABSENCE CHECK FOR EVERY VALUE.**  With the pinned
padding `zeroLeafHash hl = hashLeaf({0,0,0})`, in any state with an empty slot below
capacity at its own `_height`, for every node hash and leaf hash and every nonzero `v`:
`verifyNonInclusion` accepts, against the published root, the zero leaf `{0,0,0}` at index
`leafCount` with that slot's honest siblings and the published path length, and the break
located on that submission is exactly `paddingHit` (no other case of `TreeRootBreak`
holds).  This is `Contracts.InteropCommitmentTree.Properties.PaddingCollisionForgesAbsence`
at the state's own height, with the attribution. -/
def Properties.PinnedGateAcceptsEveryValueBelowCapacity : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (S : HState), S.tree.leafCount < 2 ^ S.height →
    ∀ v : UInt256, v ≠ 0 →
      NonInclusionAccepted h hl (S.root h (zeroLeafHash hl) hl) v ⟨0, 0, 0⟩ S.tree.leafCount
          (honestSibs h (zeroLeafHash hl) (leafHashes hl S.tree) S.tree.leafCount) S.height
        ∧ TreeRootBreakExactly h (zeroLeafHash hl) hl S.tree S.height
            (honestSibs h (zeroLeafHash hl) (leafHashes hl S.tree) S.tree.leafCount) S.height
            S.tree.leafCount ⟨0, 0, 0⟩ .paddingHit

/-- **AT THE PIN, THE ABSENCE CHECK ACCEPTS EVERY VALUE OFF POWERS OF TWO.**  At c67894b9's
padding, for every node hash and leaf hash, at every state reached from `setup` whose leaf
count is not a power of two (3, 5, 6, 7, 9, … leaves), and every nonzero `v`, delivered or
not: `DeployedGate` holds, through the submission of
`PinnedGateAcceptsEveryValueBelowCapacity` (the zero leaf at index `leafCount`, that slot's
honest siblings, the published length), whose located break is exactly `paddingHit`. -/
def Properties.PinnedGateAcceptsEveryValueOffPowersOfTwo : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (S : HState), HReaches hSetup S →
    (∀ k : ℕ, S.tree.leafCount ≠ 2 ^ k) →
      ∀ v : UInt256, v ≠ 0 →
        DeployedGate h (zeroLeafHash hl) hl S v
          ∧ NonInclusionAccepted h hl (S.root h (zeroLeafHash hl) hl) v ⟨0, 0, 0⟩
              S.tree.leafCount
              (honestSibs h (zeroLeafHash hl) (leafHashes hl S.tree) S.tree.leafCount) S.height
          ∧ TreeRootBreakExactly h (zeroLeafHash hl) hl S.tree S.height
              (honestSibs h (zeroLeafHash hl) (leafHashes hl S.tree) S.tree.leafCount) S.height
              S.tree.leafCount ⟨0, 0, 0⟩ .paddingHit

/-- **THE COUNTEREXAMPLE MEETS THE CAPSTONES' HYPOTHESES.**  For every node and leaf hash
and `0 < a < b`, the run `setup; insert a; insert b` (`hThreeRun a b`) satisfies:

* it is an `HRun` from `hSetup`, and its leaf-set projection is a `GuardedEvolution` from
  the genesis singleton `{⟨0, 0⟩}`, which are the hypotheses of
  `guardedEvolution_reclaimable_iff_absent` and `guardedEvolution_delivered_available_forever`;
* at step 2, `a` is delivered, and the capstones' member gate is closed for it;
* yet `verifyNonInclusion` with the pinned padding accepts the zero leaf `{0,0,0}` at the
  empty index 3 for `a`, with that slot's honest siblings, against step 2's published root
  at its own height; the accepted leaf's projection `⟨0, 0⟩` is NOT a leaf of step 2;
* so `DeployedGate` holds for `a` at step 2, and `BreakFreeGate` does not. -/
def Properties.PinnedCounterexampleMeetsCapstoneHypotheses : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    HRun (hThreeRun a b) ∧ hThreeRun a b 0 = hSetup
      ∧ GuardedEvolution (absHistory (hThreeRun a b))
      ∧ absHistory (hThreeRun a b) 0 = ({⟨0, 0⟩} : Finset AbsLeaf)
      ∧ a ∈ keys (absHistory (hThreeRun a b) 2)
      ∧ ¬ MemberGate (absHistory (hThreeRun a b) 2) a
      ∧ NonInclusionAccepted h hl ((hThreeRun a b 2).root h (zeroLeafHash hl) hl) a ⟨0, 0, 0⟩ 3
          (honestSibs h (zeroLeafHash hl) (leafHashes hl (hThreeRun a b 2).tree) 3)
          (hThreeRun a b 2).height
      ∧ (⟨0, 0⟩ : AbsLeaf) ∉ absHistory (hThreeRun a b) 2
      ∧ DeployedGate h (zeroLeafHash hl) hl (hThreeRun a b 2) a
      ∧ ¬ BreakFreeGate h (zeroLeafHash hl) hl (hThreeRun a b 2) a

/-- **THE RECLAIM DICHOTOMY'S READING IS FALSE AT THE PIN.**  For every node hash and leaf
hash, with the pinned padding, `DeployedGate` does not hold exactly on the absent values
along runs from `setup`: it holds for a delivered value. -/
def Properties.PinnedReclaimDichotomyReadingFails : Prop :=
  ∀ (h : Hash) (hl : LeafHash), ¬ ReclaimDichotomyReading h (zeroLeafHash hl) hl

/-- **DELIVERY FINALITY'S READING IS FALSE AT THE PIN.**  For every node hash and leaf hash,
with the pinned padding, `DeployedGate` holds for a value delivered at an on-time step, at
a step meeting the abstract pin `D < t (j + 1)`, along a run from `setup` with a monotone
clock. -/
def Properties.PinnedDeliveryFinalityReadingFails : Prop :=
  ∀ (h : Hash) (hl : LeafHash), ¬ DeliveryFinalityReading h (zeroLeafHash hl) hl

end IMTAbstract.ReclaimGateFaithful.History
