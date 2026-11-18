import EraSpec.Protocol.MultichainGate.Specs.DeployedGate

/-!
# The source-bound refund gate over the deployed absence verifier

Statements about `EraSpec.Protocol.MultichainGate.Specs.DeployedGate`; proofs in
`EraSpec.Protocol.MultichainGate.Proofs.DeployedGate`.  Namespace
`Contracts.Protocol.DeployedGate`.  Pin: era-contracts `c67894b9`.

## What this corrects

`Contracts.Protocol.Properties.chains_no_double_spend` and
`chains_bound_gate_iff_undelivered` are statements about `BoundGate`, a gate that accepts a
LEAF OF THE SOURCE CHAIN'S LEAF SET whose window straddles the value.  Read as statements
about the deployed `authorizeRefund` gate, which accepts whatever `verifyNonInclusion`
accepts against the source chain's root, both are false at `c67894b9`
(`Properties.ChainsNoDoubleSpendFailsForDeployedGate`,
`Properties.ChainsBoundGateIffUndeliveredFailsForDeployedGate`): with `hashLeaf({0,0,0})`
as the padding constant, the sentinel opened at an empty slot below capacity passes for a
delivered value (`Properties.PinnedPaddingDeployedGateRefundsDeliveredLeg`).  The forged
proof uses the tree's own sibling nodes, and its only located break is `paddingHit`: no
hash collision is involved.  The single-tree form of this countermodel is
`Contracts.InteropCommitmentTree.Properties.PaddingForgeryAtOwnHeight`.
`EraSpec.Refinement.protocol_guarantee` names `chains_no_double_spend`.

## What replaces them

* `Properties.DeployedBoundGateExcludesDeliveredOrBreak`: for any padding constant and with
  no hash premise, every proof the deployed gate accepts for a delivered value carries a
  located `TreeRootBreak` on that proof.  At `c67894b9` its `paddingHit` case needs no
  collision, so on its own this does not exclude a refund of a delivered leg there.
* `Properties.DeployedBoundGateSeparatedPaddingNeedsCollision`: if the presented leaf does
  not hash to the padding constant (a premise about that ONE leaf, false at `c67894b9` for
  `{0,0,0}`), the break is a `CollisionBreak`: a wrong length with a `HeightBreak`, a path
  collision, or a leaf-hash collision with the stored leaf, all on instance values.
* `Properties.DeployedBoundGateFullTreeNeedsCollision`: with any padding, the pinned one
  included, if the source tree has no empty slot below capacity (`_leafNumber = 2^_height`),
  the break is a `CollisionBreak`.  On a state reached from `setup` that is exactly the case
  when the leaf count is a power of two (`Properties.FullAtOwnHeightIffPowerOfTwo`).
* `Properties.DeployedBoundGateLiveOnUndelivered` and
  `Properties.DeployedBoundGateIffAbstractOrBreak`: the deployed gate passes every
  undelivered nonzero value with an honest proof that carries no break, and it accepts some
  proof exactly when the abstract `BoundGate` holds or some accepted proof carries a located
  break.  The `Model` Specs docstring describes `AbsenceWitnessAt` as what `verifyNonInclusion`
  accepts "modulo the Merkle path"; this is the precise relation.

Most of these are the single-tree results of `Contracts.InteropCommitmentTree` read at the
source chain's state, not independent results: `DeployedBoundGateExcludesDeliveredOrBreak`
is `verified_absence_excludes_delivered_or_break`, `DeployedBoundGateLiveOnUndelivered` is
`proofs_exclusive_or_break_at_own_height`, `DeployedBoundGateIffAbstractOrBreak` is
`non_inclusion_sound_or_break`, the countermodels lift `padding_forgery_at_own_height`, and
`DeployedBoundGateSeparatedPaddingNeedsCollision` is the `hl ℓ ≠ z0` case already in
`AttackVectors.StaleSnapshotFaithful.Properties.StaleWitnessNotRedeemableOrCollision`.  The
new content is `DeployedBoundGateFullTreeNeedsCollision` and `FullAtOwnHeightIffPowerOfTwo`.

## Witnesses

`Properties.DeployedGateCollisionPremisesSatisfiable` meets every premise of the two
collision forms together (a reached, full source tree, a delivered value, an accepted
proof, a presented leaf not hashing to the pinned padding) under the toy hash pair, and the
break is exactly `leafCollision`.  `Properties.PinnedPaddingDeployedGateRefundsDeliveredLeg`
meets every premise of `DeployedBoundGateExcludesDeliveredOrBreak` for every hash pair.
`Properties.DeployedBoundGateLiveWitness` meets the premises of the liveness and iff forms on
a reached state with a delivered value.  `Properties.FullAtOwnHeightExamples` shows the
full-tree premise holds at the source's heights for one and two leaves and fails for three.
-/

namespace Contracts.Protocol.DeployedGate

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-! ## The countermodel: the deployed reading fails at `c67894b9` -/

/-- **AT `c67894b9` THE DEPLOYED BOUND GATE PASSES A DELIVERED VALUE.**  For every node hash
and leaf hash and every `0 < a < b`: in `paddingStates a b` every chain is reached from
`setup` (so every chain is `Valid`, the premise of `chains_no_double_spend`), `a` is
delivered on its declared source chain `0`, and the abstract `BoundGate` rejects it, as
`chains_no_double_spend` says.  Yet the deployed gate for source chain `0`, with the pinned
padding `hashLeaf({0,0,0})`, accepts the sentinel `{0,0,0}` at the empty slot 3 with the
honest sibling stream for that slot, at the source's own height `2`.  That proof's located
break is exactly `paddingHit`. -/
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

/-- **THE DEPLOYED READING OF `chains_no_double_spend` FAILS AT `c67894b9`.**  For every node
hash and leaf hash there are chain states, all reached from `setup`, and a value delivered
on its declared source chain that the deployed source-bound gate accepts under the pinned
padding. -/
def Properties.ChainsNoDoubleSpendFailsForDeployedGate : Prop :=
  ∀ (h : Hash) (hl : LeafHash), ∃ (St : ChainStates) (src : Chain) (v : UInt256),
    StatesFromSetup St ∧ Delivered (ofStates St) src v
      ∧ DeployedBoundGate h (pinPadding hl) hl St src v

/-- **THE DEPLOYED READING OF `chains_bound_gate_iff_undelivered` FAILS AT `c67894b9`.**  For
every node hash and leaf hash there are chain states reached from `setup` and a nonzero
value on which "the deployed gate accepts iff the value is undelivered" is false. -/
def Properties.ChainsBoundGateIffUndeliveredFailsForDeployedGate : Prop :=
  ∀ (h : Hash) (hl : LeafHash), ∃ (St : ChainStates) (src : Chain) (v : UInt256),
    StatesFromSetup St ∧ v ≠ 0
      ∧ ¬ (DeployedBoundGate h (pinPadding hl) hl St src v ↔ ¬ Delivered (ofStates St) src v)

/-! ## The forms that hold -/

/-- **A DELIVERED VALUE PASSES THE DEPLOYED GATE ONLY ON A PROOF WITH A LOCATED BREAK.**  For
every node hash, leaf hash and padding constant, with no hash premise: if the source chain's
state is reached from `setup` and the value is delivered there, every proof the deployed
gate accepts for it carries a `TreeRootBreak` on its own leaf, index, siblings and length.
Only the source chain's state is constrained.  At `c67894b9` the `paddingHit` case needs no
collision (`Properties.PinnedPaddingDeployedGateRefundsDeliveredLeg`). -/
def Properties.DeployedBoundGateExcludesDeliveredOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (St : ChainStates) (src : Chain),
    HReaches hSetup (St src) → ∀ (v : UInt256), Delivered (ofStates St) src v →
    ∀ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      DeployedBoundGateBy h z0 hl St src v ℓ idx sibs k →
        TreeRootBreak h z0 hl (St src).tree (St src).height sibs k idx ℓ

/-- **WITH THE PRESENTED LEAF NOT HASHING TO THE PADDING, THE BREAK IS A COLLISION.**  The
extra premise `hl ℓ ≠ z0` is about the one leaf the prover presents.  At `c67894b9`,
`z0 = hl ⟨0,0,0⟩`, so it fails for the sentinel; with the current heads' padding
`IMT_EMPTY_LEAF_HASH` it asks that no presented leaf's `hashLeaf` equal that constant. -/
def Properties.DeployedBoundGateSeparatedPaddingNeedsCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (St : ChainStates) (src : Chain),
    HReaches hSetup (St src) → ∀ (v : UInt256), Delivered (ofStates St) src v →
    ∀ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ), hl ℓ ≠ z0 →
      DeployedBoundGateBy h z0 hl St src v ℓ idx sibs k →
        CollisionBreak h z0 hl (St src).tree (St src).height sibs k idx ℓ

/-- **ON A FULL SOURCE TREE THE BREAK IS A COLLISION, WHATEVER THE PADDING.**  If the source
tree has no empty slot below its capacity (`_leafNumber = 2 ^ _height`), then for every
padding constant, the pinned one included, every proof the deployed gate accepts for a
delivered value carries a `CollisionBreak`. -/
def Properties.DeployedBoundGateFullTreeNeedsCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (St : ChainStates) (src : Chain),
    HReaches hSetup (St src) → FullAtOwnHeight (St src) →
    ∀ (v : UInt256), Delivered (ofStates St) src v →
    ∀ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      DeployedBoundGateBy h z0 hl St src v ℓ idx sibs k →
        CollisionBreak h z0 hl (St src).tree (St src).height sibs k idx ℓ

/-- **A REACHED TREE IS FULL EXACTLY WHEN ITS LEAF COUNT IS A POWER OF TWO.**  On a state
reached from `setup`, `_leafNumber = 2 ^ _height` iff `_leafNumber` is a power of two. -/
def Properties.FullAtOwnHeightIffPowerOfTwo : Prop :=
  ∀ (S : HState), HReaches hSetup S → (FullAtOwnHeight S ↔ ∃ m : ℕ, S.tree.leafCount = 2 ^ m)

/-- **THE DEPLOYED GATE PASSES EVERY UNDELIVERED VALUE.**  On a source state reached from
`setup`, for every padding constant and every nonzero value the source chain does not hold,
the honest proof of some occupied low leaf (its sibling stream at the source's own height)
passes the deployed gate and carries no located break. -/
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
abstract `BoundGate` holds or some accepted proof carries a located `TreeRootBreak`. -/
def Properties.DeployedBoundGateIffAbstractOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (St : ChainStates) (src : Chain),
    HReaches hSetup (St src) → ∀ (v : UInt256), v ≠ 0 →
      (DeployedBoundGate h z0 hl St src v
        ↔ BoundGate (ofStates St) src v
          ∨ ∃ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
              DeployedBoundGateBy h z0 hl St src v ℓ idx sibs k
                ∧ TreeRootBreak h z0 hl (St src).tree (St src).height sibs k idx ℓ)

/-! ## Witnesses -/

/-- **THE COLLISION FORMS' PREMISES HOLD TOGETHER, AND THE COLLISION FIRES.**  Under the toy
hash pair (`toyNodeHash`, `toyLeafHash`; not a model of keccak) with the pinned padding
`toyLeafHash {0,0,0}`: `twoLeafState 2` is reached from `setup` and full at height 1, and
`2` is delivered on it.  The low leaf `⟨1,0,3⟩` does not hash to the padding constant, and
with the honest siblings of index 0 it passes the deployed gate for `2`, because it hashes
like the stored leaf 0 `⟨0,1,2⟩`.  Its located break is exactly `leafCollision`.  So every
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

/-- **THE LIVENESS AND IFF PREMISES ON A REACHED STATE WITH A DELIVERED VALUE.**  For every
node hash, leaf hash and padding constant: `twoLeafState 2` is reached from `setup`, `2` is
delivered on it, `1` is nonzero and not delivered, and the deployed gate accepts a proof
for `1`. -/
def Properties.DeployedBoundGateLiveWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    HReaches hSetup (twoLeafState 2)
      ∧ Delivered (ofStates (fun _ => twoLeafState 2)) 0 2
      ∧ (1 : UInt256) ≠ 0 ∧ ¬ Delivered (ofStates (fun _ => twoLeafState 2)) 0 1
      ∧ DeployedBoundGate h z0 hl (fun _ => twoLeafState 2) 0 1

/-- **THE FULL-TREE PREMISE AT THE SOURCE'S HEIGHTS.**  `setup` (one leaf, height 0) and
`setup; insert a` (two leaves, height 1) are full; `setup; insert a; insert b` (three
leaves, height 2) is not, which is why the countermodel uses it. -/
def Properties.FullAtOwnHeightExamples : Prop :=
  ∀ a b : UInt256, 0 < a →
    HReaches hSetup (twoLeafState a)
      ∧ FullAtOwnHeight hSetup ∧ FullAtOwnHeight (twoLeafState a)
      ∧ ¬ FullAtOwnHeight (hThree a b)

end Contracts.Protocol.DeployedGate
