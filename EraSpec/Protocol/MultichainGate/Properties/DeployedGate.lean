import EraSpec.Protocol.MultichainGate.Specs.DeployedGate

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false

/-!
# The source-bound refund gate as deployed

Statements about `EraSpec.Protocol.MultichainGate.Specs.DeployedGate`; proofs in
`EraSpec.Protocol.MultichainGate.Proofs.DeployedGate`.

## What this corrects

`Contracts.Protocol.Properties.chains_no_double_spend` and
`chains_bound_gate_iff_undelivered` are correct statements about `BoundGate`, a gate
that accepts a LEAF OF THE SOURCE CHAIN'S LEAF SET whose window straddles the value.
Read as statements about the deployed `authorizeRefund` they are false at the
extraction pin.  The deployed gate accepts whatever `verifyNonInclusion` accepts against
the source chain's root, and with `hashLeaf({0,0,0})` as the padding constant that
includes the sentinel opened at any empty in-capacity slot, for any nonzero value
(`Properties.PinnedPaddingDeployedGateRefundsDeliveredLeg`).  The forged proof uses the
tree's own siblings: no hash is broken.  The same countermodel at the single-tree level
is `Contracts.InteropCommitmentTree.Properties.PaddingCollisionRefundsDeliveredLeg`.

## What replaces it

* `Properties.DeployedBoundGateExcludesDeliveredOrBreak`: for any padding constant and
  with no hash premise, an accepted proof for a delivered leg carries a located
  `TreeRootBreak` on that proof.  At the pin its `paddingHit` case costs nothing, so this
  is the honest form, not a security guarantee by itself.
* `Properties.DeployedBoundGateSeparatedPaddingNeedsCollision`: if the presented leaf does
  not hash to the padding constant (a premise about that ONE leaf, which
  `IMT_EMPTY_LEAF_HASH` provides and the pin refutes for `{0,0,0}`), the break is a
  `CollisionBreak`: a hash collision or domain-separation failure on instance values.
* `Properties.DeployedBoundGateFullTreeNeedsCollision`: with ANY padding, including the
  pinned one, a source tree with no empty slot below capacity (`_leafNumber = 2^_height`)
  admits no free forgery; the break is a `CollisionBreak`.
* `Properties.DeployedBoundGateLiveOnUndelivered` and
  `Properties.DeployedBoundGateIffAbstractOrBreak`: the deployed gate opens on every
  undelivered nonzero leg with an honest, break-free proof, and it accepts exactly when
  the abstract `BoundGate` does or an accepted proof carries a located break.  This is the
  precise sense in which `AbsenceWitnessAt` is "what `verifyNonInclusion` accepts".

## Anti-vacuity

`Properties.DeployedGateCollisionPremisesSatisfiable` meets every premise of the two
collision forms together (a reached, full source tree, a delivered value, an accepted
proof, a presented leaf not hashing to the pinned padding) under the toy hash pair, and
the break that results is exactly `leafCollision`.  `Properties.FullAtOwnHeightExamples`
shows the full-tree premise holds at the source's heights for one and two leaves and fails
for three.
-/

namespace Contracts.Protocol

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-! ## The countermodel: the deployed reading is false at the pin -/

/-- **AT THE PIN, THE DEPLOYED BOUND GATE REFUNDS A DELIVERED LEG.**  For every node hash
and leaf hash and every `0 < a < b`: in `paddingStates a b` every chain is reached from
`setup` (so every chain is `Valid`, which is the premise of `chains_no_double_spend`), `a`
is delivered on its declared source chain `0`, and the abstract `BoundGate` rejects it, as
`chains_no_double_spend` says.  Yet the deployed gate for source chain `0`, with the pinned
padding `hashLeaf({0,0,0})`, accepts the sentinel `{0,0,0}` at the empty slot 3, with the
honest siblings, at the source's own height `2`.  That proof's located break is exactly
`paddingHit`, so no hash collision is involved. -/
def Properties.PinnedPaddingDeployedGateRefundsDeliveredLeg : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    StatesFromSetup (paddingStates a b)
      ∧ (∀ c, Valid (paddingStates a b c).tree)
      ∧ Delivered (ofStates (paddingStates a b)) 0 a
      ∧ ¬ BoundGate (ofStates (paddingStates a b)) 0 a
      ∧ (paddingStates a b 0).height = 2
      ∧ DeployedBoundGateBy h (pinPadding hl) hl (paddingStates a b) 0 a ⟨0, 0, 0⟩ 3
          (paddingSlotSibs h hl a b) 2
      ∧ TreeRootBreakExactly h (pinPadding hl) hl (paddingStates a b 0).tree 2
          (paddingSlotSibs h hl a b) 2 3 ⟨0, 0, 0⟩ .paddingHit

/-- **THE DEPLOYED READING OF `chains_no_double_spend` IS FALSE AT THE PIN.**  For every
node hash and leaf hash there are chain states, all reached from `setup`, and a leg that is
both delivered on its declared source chain and accepted by the deployed source-bound gate
under the pinned padding. -/
def Properties.ChainsNoDoubleSpendFailsForDeployedGate : Prop :=
  ∀ (h : Hash) (hl : LeafHash), ∃ (St : ChainStates) (src : Chain) (v : UInt256),
    StatesFromSetup St ∧ Delivered (ofStates St) src v
      ∧ DeployedBoundGate h (pinPadding hl) hl St src v

/-- **THE DEPLOYED READING OF `chains_bound_gate_iff_undelivered` IS FALSE AT THE PIN.**  For
every node hash and leaf hash there are chain states reached from `setup` and a nonzero
value on which the deployed gate does not fire exactly on the undelivered legs. -/
def Properties.ChainsBoundGateIffUndeliveredFailsForDeployedGate : Prop :=
  ∀ (h : Hash) (hl : LeafHash), ∃ (St : ChainStates) (src : Chain) (v : UInt256),
    StatesFromSetup St ∧ v ≠ 0
      ∧ ¬ (DeployedBoundGate h (pinPadding hl) hl St src v ↔ ¬ Delivered (ofStates St) src v)

/-! ## The strongest replacements that hold -/

/-- **A DELIVERED LEG PASSES THE DEPLOYED GATE ONLY ON A PROOF WITH A LOCATED BREAK.**  For
every node hash, leaf hash and padding constant, with no hash premise: if the source
chain's state is reached from `setup` and the leg's value is delivered there, every proof
the deployed gate accepts for it carries a `TreeRootBreak` on its own leaf, index,
siblings and length.  Only the source chain's state is constrained.  At the pin the
`paddingHit` case is free (`Properties.PinnedPaddingDeployedGateRefundsDeliveredLeg`). -/
def Properties.DeployedBoundGateExcludesDeliveredOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (St : ChainStates) (src : Chain),
    HReaches hSetup (St src) → ∀ (v : UInt256), Delivered (ofStates St) src v →
    ∀ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      DeployedBoundGateBy h z0 hl St src v ℓ idx sibs k →
        TreeRootBreak h z0 hl (St src).tree (St src).height sibs k idx ℓ

/-- **WITH THE PADDING SEPARATED FROM THE PRESENTED LEAF, THE BREAK IS A COLLISION.**  The
extra premise `hl ℓ ≠ z0` is about the one leaf the prover presents.  It is what a
dedicated padding constant such as `IMT_EMPTY_LEAF_HASH` provides for that leaf (a
`hashLeaf` preimage is 96 bytes, the constant's preimage is not), and it is false at the
pin for `ℓ = {0,0,0}`. -/
def Properties.DeployedBoundGateSeparatedPaddingNeedsCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (St : ChainStates) (src : Chain),
    HReaches hSetup (St src) → ∀ (v : UInt256), Delivered (ofStates St) src v →
    ∀ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ), hl ℓ ≠ z0 →
      DeployedBoundGateBy h z0 hl St src v ℓ idx sibs k →
        CollisionBreak h z0 hl (St src).tree (St src).height sibs k idx ℓ

/-- **A FULL SOURCE TREE ADMITS NO FREE FORGERY, WHATEVER THE PADDING.**  If the source
tree has no empty slot below its capacity (`_leafNumber = 2 ^ _height`), then for every
padding constant, the pinned one included, an accepted proof for a delivered leg carries a
`CollisionBreak`.  So at the pin the free forgery needs an empty in-capacity slot, which a
reached tree has exactly when its leaf count is not a power of two. -/
def Properties.DeployedBoundGateFullTreeNeedsCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (St : ChainStates) (src : Chain),
    HReaches hSetup (St src) → FullAtOwnHeight (St src) →
    ∀ (v : UInt256), Delivered (ofStates St) src v →
    ∀ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      DeployedBoundGateBy h z0 hl St src v ℓ idx sibs k →
        CollisionBreak h z0 hl (St src).tree (St src).height sibs k idx ℓ

/-- **THE DEPLOYED GATE OPENS ON EVERY UNDELIVERED LEG.**  On a source state reached from
`setup`, for every padding constant and every nonzero value the source chain does not hold,
the honest proof of an occupied low leaf (its `merklePath` at the source's own height)
passes the deployed gate and carries no located break.  So the safety forms above are not
explained by a gate that never opens. -/
def Properties.DeployedBoundGateLiveOnUndelivered : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (St : ChainStates) (src : Chain),
    HReaches hSetup (St src) → ∀ (v : UInt256), v ≠ 0 → ¬ Delivered (ofStates St) src v →
      ∃ i < (St src).tree.leafCount,
        DeployedBoundGateBy h z0 hl St src v ((St src).tree.leaf i) i
            (honestSibs h z0 (leafHashes hl (St src).tree) i) (St src).height
          ∧ ¬ TreeRootBreak h z0 hl (St src).tree (St src).height
              (honestSibs h z0 (leafHashes hl (St src).tree) i) (St src).height i
              ((St src).tree.leaf i)

/-- **THE ABSTRACT GATE IS THE DEPLOYED ONE UP TO A LOCATED BREAK.**  On a source state
reached from `setup` and for a nonzero value, the deployed gate accepts some proof iff the
abstract `BoundGate` holds or some accepted proof carries a located `TreeRootBreak`.  This
replaces the docstring claim that `AbsenceWitnessAt` is what `verifyNonInclusion` accepts
"modulo the Merkle path": the Merkle path does not authenticate membership, and the
difference is exactly the located breaks, of which `paddingHit` is free at the pin. -/
def Properties.DeployedBoundGateIffAbstractOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (St : ChainStates) (src : Chain),
    HReaches hSetup (St src) → ∀ (v : UInt256), v ≠ 0 →
      (DeployedBoundGate h z0 hl St src v
        ↔ BoundGate (ofStates St) src v
          ∨ ∃ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
              DeployedBoundGateBy h z0 hl St src v ℓ idx sibs k
                ∧ TreeRootBreak h z0 hl (St src).tree (St src).height sibs k idx ℓ)

/-! ## Anti-vacuity -/

/-- **THE COLLISION FORMS' PREMISES HOLD TOGETHER, AND THE COLLISION FIRES.**  Under the toy
hash pair (`toyNodeHash`, `toyLeafHash`; not a model of keccak) with the pinned padding
`toyLeafHash {0,0,0}`: `twoLeafState 2` is reached from `setup` and full at height 1, and `2`
is delivered on it.  The low leaf `⟨1,0,3⟩` does not hash to the padding constant, and with
the honest siblings of index 0 it passes the deployed gate for `2`, because it hashes like
the stored leaf 0 `⟨0,1,2⟩`.  Its located break is exactly `leafCollision`.  So every
premise of `DeployedBoundGateSeparatedPaddingNeedsCollision` and
`DeployedBoundGateFullTreeNeedsCollision` is met at once, at the pin's padding. -/
def Properties.DeployedGateCollisionPremisesSatisfiable : Prop :=
  HReaches hSetup (twoLeafState 2)
    ∧ FullAtOwnHeight (twoLeafState 2)
    ∧ Delivered (ofStates (fun _ => twoLeafState 2)) 0 2
    ∧ toyLeafHash toyCollidingLowLeaf ≠ pinPadding toyLeafHash
    ∧ DeployedBoundGateBy toyNodeHash (pinPadding toyLeafHash) toyLeafHash
        (fun _ => twoLeafState 2) 0 2 toyCollidingLowLeaf 0
        (honestSibs toyNodeHash (pinPadding toyLeafHash)
          (leafHashes toyLeafHash (twoLeafState 2).tree) 0) 1
    ∧ TreeRootBreakExactly toyNodeHash (pinPadding toyLeafHash) toyLeafHash
        (twoLeafState 2).tree 1
        (honestSibs toyNodeHash (pinPadding toyLeafHash)
          (leafHashes toyLeafHash (twoLeafState 2).tree) 0) 1 0 toyCollidingLowLeaf
        .leafCollision

/-- **THE FULL-TREE PREMISE AT THE SOURCE'S HEIGHTS.**  `setup` (one leaf, height 0) and
`setup; insert a` (two leaves, height 1) are full; `setup; insert a; insert b` (three
leaves, height 2) is not, which is why the pinned countermodel uses it. -/
def Properties.FullAtOwnHeightExamples : Prop :=
  ∀ a b : UInt256, 0 < a →
    HReaches hSetup (twoLeafState a)
      ∧ FullAtOwnHeight hSetup ∧ FullAtOwnHeight (twoLeafState a)
      ∧ ¬ FullAtOwnHeight (hThree a b)

end Contracts.Protocol
