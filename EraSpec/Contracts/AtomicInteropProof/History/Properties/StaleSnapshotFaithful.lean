import EraSpec.Contracts.AtomicInteropProof.History.Specs.StaleSnapshotFaithful

/-!
# Properties (History): the padding reclaim at the extraction pin

Statement over `../Specs/StaleSnapshotFaithful.lean`, proved in `../Proofs/StaleSnapshotFaithful.lean`.

**History.** The record of the H2 padding finding at `c67894b9` (padding constant
`hashLeaf({0,0,0})`), not a claim about `b17415d20`, whose `setup` pads with
`IMT_EMPTY_LEAF_HASH`. What a distinct padding constant buys at `b17415d20` is
`AttackVectors.StaleSnapshotFaithful.Properties.StaleWitnessNotRedeemableOrCollision`.
-/

namespace AttackVectors.StaleSnapshotFaithful.History

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-- **COUNTERMODEL AT THE PIN: AN ACCEPTED, DEADLINE-PINNED RECLAIM OF A DELIVERED
LEG.**  For every node hash and leaf hash, with the extraction-pin padding constant
`hl ⟨0,0,0⟩`, and every `0 < a < b`: `paddedRun a b` is a run from `setup` within
capacity, `paddedRunTime` is monotone, `a` is delivered at the on-time snapshot 2, and
snapshot 2 is deadline-pinned for deadline `0`; yet `verifyNonInclusion` accepts
`{0,0,0}` at the empty slot 3 as an absence proof for `a` against snapshot 2's root.
The accepted low leaf `⟨0,0⟩` is not a leaf of the snapshot, so
`StaleSnapshot.stale_witness_not_redeemable`'s conclusion fails for this accepted
reclaim, and the located break is exactly `paddingHit`.  "Deadline-pinned" is the
abstract pin `D < t (j+1)`; the deployed timeout branches are not part of this
statement (see the module docstring). -/
def Properties.PaddingReclaimRedeemsDeliveredLeg : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    Run (paddedRun a b) ∧ paddedRun a b 0 = setup ∧ Monotone paddedRunTime
      ∧ (∀ n, (paddedRun a b n).leafCount ≤ 2 ^ paddedRunHeight n)
      ∧ paddedRunTime 2 ≤ 0 ∧ a ∈ keys (toAbs (paddedRun a b 2))
      ∧ (0 : UInt256) < paddedRunTime (2 + 1)
      ∧ NonInclusionAccepted h hl
          (root h (hl ⟨0, 0, 0⟩) hl (paddedRun a b 2) (paddedRunHeight 2)) a ⟨0, 0, 0⟩ 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (paddedRun a b 2)) 3) (paddedRunHeight 2)
      ∧ (⟨0, 0⟩ : AbsLeaf) ∉ toAbs (paddedRun a b 2)
      ∧ ¬ (∀ i, paddedRunTime i ≤ 0 → a ∉ keys (toAbs (paddedRun a b i)))
      ∧ TreeRootBreakExactly h (hl ⟨0, 0, 0⟩) hl (paddedRun a b 2) (paddedRunHeight 2)
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (paddedRun a b 2)) 3)
          (paddedRunHeight 2) 3 ⟨0, 0, 0⟩ .paddingHit

end AttackVectors.StaleSnapshotFaithful.History
