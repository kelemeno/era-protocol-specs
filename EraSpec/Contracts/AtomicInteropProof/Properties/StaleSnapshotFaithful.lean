import EraSpec.Contracts.AtomicInteropProof.Specs.StaleSnapshotFaithful

/-!
# Properties: stale-snapshot reclaim against the deployed absence verifier

Statements over `../Specs/StaleSnapshotFaithful.lean`.  Proofs:
`../Proofs/StaleSnapshotFaithful.lean`.

* `StaleWitnessNotRedeemableOrBreak` and `PinningGateRejectsStaleWitnessOrBreak` are
  `StaleSnapshot.stale_witness_not_redeemable` / `pinning_gate_rejects_stale_witness`
  (and `Timestamps.monotone_blocks_the_attack`) for an absence proof ACCEPTED by
  `verifyNonInclusion` against a run's published root, with index and path length the
  prover's: no on-time delivery coexists with a deadline-pinned accepted reclaim, or
  the reclaim proof carries a located `TreeRootBreak`.  No hash premise.
* `PaddingReclaimRedeemsDeliveredLeg` is the countermodel to the original headline's
  reading as a statement about the deployed gate: at the extraction pin (padding
  constant `hashLeaf({0,0,0})`), on a real run with monotone timestamps, a value is
  delivered at an on-time snapshot AND an absence proof for it is accepted at a
  deadline-pinned snapshot.  The accepted low leaf is not a leaf of the snapshot, the
  original conclusion is false, and the break is exactly `paddingHit`.
* `StaleWitnessNotRedeemableOrCollision` is what the upgrade's padding buys: once the
  presented leaf does not hash to the padding constant, the only remaining ways out
  are genuine hash collisions (a wrong path length, a path collision, a leaf-hash
  collision), never a free padding hit.  `StaleWitnessOrCollisionSatisfiable` shows its
  premises hold, with no break, on an honest refund.
-/

namespace AttackVectors.StaleSnapshotFaithful

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-- **NO ON-TIME DELIVERY COEXISTS WITH AN ACCEPTED, DEADLINE-PINNED RECLAIM, OR THE
RECLAIM PROOF CARRIES A LOCATED BREAK.**  Along any contract run from `setup`, with
monotone settlement timestamps, if `verifyNonInclusion` accepts an absence proof for
`v` against snapshot `j`'s published root (at any height, any index, any path length)
and `j` is deadline-pinned (`D < t (j+1)`), then `v` is a key of no on-time snapshot,
or the submitted proof carries a `TreeRootBreak` against snapshot `j`'s root. -/
def Properties.StaleWitnessNotRedeemableOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → Tree) (ht : ℕ → ℕ) (t : ℕ → UInt256)
    (D v : UInt256),
    Run R → R 0 = setup → Monotone t →
    ∀ (j : ℕ) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      D < t (j + 1) →
      NonInclusionAccepted h hl (root h z0 hl (R j) (ht j)) v ℓ idx sibs k →
      (∀ i, t i ≤ D → v ∉ keys (toAbs (R i)))
        ∨ TreeRootBreak h z0 hl (R j) (ht j) sibs k idx ℓ

/-- **THE ATTACKER'S VIEW.**  Given a genuine on-time delivery of `v`, every absence
proof `verifyNonInclusion` accepts against a snapshot's root either fails the pinning
comparison `D < t (j+1)` or carries a located break. -/
def Properties.PinningGateRejectsStaleWitnessOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → Tree) (ht : ℕ → ℕ) (t : ℕ → UInt256)
    (D v : UInt256),
    Run R → R 0 = setup → Monotone t →
    ∀ i, t i ≤ D → v ∈ keys (toAbs (R i)) →
    ∀ (j : ℕ) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      NonInclusionAccepted h hl (root h z0 hl (R j) (ht j)) v ℓ idx sibs k →
      ¬ D < t (j + 1) ∨ TreeRootBreak h z0 hl (R j) (ht j) sibs k idx ℓ

/-- **COUNTERMODEL AT THE PIN: AN ACCEPTED, DEADLINE-PINNED RECLAIM OF A DELIVERED
LEG.**  For every node hash and leaf hash, with the extraction-pin padding constant
`hl ⟨0,0,0⟩`, and every `0 < a < b`: `paddedRun a b` is a run from `setup` within
capacity, `paddedRunTime` is monotone, `a` is delivered at the on-time snapshot 2, and
snapshot 2 is deadline-pinned for deadline `0`; yet `verifyNonInclusion` accepts
`{0,0,0}` at the empty slot 3 as an absence proof for `a` against snapshot 2's root.
The accepted low leaf `⟨0,0⟩` is not a leaf of the snapshot, so
`StaleSnapshot.stale_witness_not_redeemable`'s conclusion fails for this accepted
reclaim, and the located break is exactly `paddingHit`. -/
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

/-- **WHAT THE UPGRADE'S PADDING BUYS.**  As `StaleWitnessNotRedeemableOrBreak`, for a
presented low leaf whose hash is not the padding constant (`hl ℓ ≠ z0`; at the
extraction pin `z0 = hl ⟨0,0,0⟩`, so this fails for the sentinel preimage, and with
`IMT_EMPTY_LEAF_HASH` it is a preimage problem): no coexistence, or the reclaim proof
exhibits a genuine collision — a wrong path length (`HeightBreak`), a path collision
at the tree's height, or an occupied slot holding a different leaf with the same leaf
hash. -/
def Properties.StaleWitnessNotRedeemableOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → Tree) (ht : ℕ → ℕ) (t : ℕ → UInt256)
    (D v : UInt256),
    Run R → R 0 = setup → Monotone t →
    ∀ (j : ℕ) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      D < t (j + 1) →
      NonInclusionAccepted h hl (root h z0 hl (R j) (ht j)) v ℓ idx sibs k →
      hl ℓ ≠ z0 →
      (∀ i, t i ≤ D → v ∉ keys (toAbs (R i)))
        ∨ HeightBreak h z0 (leafHashes hl (R j)) sibs k (ht j) idx (hl ℓ)
        ∨ (k = ht j ∧ PathCollision h z0 (leafHashes hl (R j)) sibs 0 k idx (hl ℓ))
        ∨ (idx < (R j).leafCount ∧ (R j).leaf idx ≠ ℓ ∧ hl ((R j).leaf idx) = hl ℓ)

/-- **THE PREMISES ARE SATISFIABLE, WITH NO BREAK.**  An honest refund under a padding
constant distinct from the sentinel's leaf hash (the toy hashes, padding `1`): the idle
run at `setup`, every snapshot late for deadline `0`, the honest absence proof for `1`
at snapshot 0.  Every premise of `StaleWitnessNotRedeemableOrCollision` holds, the
proof carries no `TreeRootBreak`, and the first disjunct is what holds. -/
def Properties.StaleWitnessOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → Tree) (ht : ℕ → ℕ) (t : ℕ → UInt256)
    (D v : UInt256) (j : ℕ) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    Run R ∧ R 0 = setup ∧ Monotone t ∧ D < t (j + 1)
      ∧ NonInclusionAccepted h hl (root h z0 hl (R j) (ht j)) v ℓ idx sibs k
      ∧ hl ℓ ≠ z0
      ∧ ¬ TreeRootBreak h z0 hl (R j) (ht j) sibs k idx ℓ
      ∧ (∀ i, t i ≤ D → v ∉ keys (toAbs (R i)))

end AttackVectors.StaleSnapshotFaithful
