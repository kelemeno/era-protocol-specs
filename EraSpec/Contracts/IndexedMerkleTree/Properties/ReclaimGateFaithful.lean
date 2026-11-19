import EraSpec.Contracts.IndexedMerkleTree.Specs.ReclaimGateFaithful

/-!
# Properties: the reclaim capstones against the deployed absence check

Statements about `EraSpec.Contracts.IndexedMerkleTree.Specs.ReclaimGateFaithful`; proofs in
`EraSpec.Contracts.IndexedMerkleTree.Proofs.ReclaimGateFaithful`.

The capstones of `Properties/Model.lean` are correct as stated: they quantify over a low
leaf `W ∈ S j`.  What fails is their reading with the deployed absence check
`verifyNonInclusion` in place of that hypothesis, at the source pin: nothing there checks
`W ∈ S j`.  Five groups:

* **The countermodel at c67894b9.**  With the pin's padding constant `hashLeaf({0,0,0})`,
  for every node hash and leaf hash, at every reached snapshot whose leaf count is not a
  power of two, `verifyNonInclusion` accepts the zero leaf at the first empty index for
  EVERY nonzero value, delivered values included, and the break located on that submission
  is exactly `paddingHit` (`PinnedGateAcceptsEveryValueOffPowersOfTwo`).  The counterexample
  run meets the capstones' hypotheses (a `GuardedEvolution` from the genesis singleton), and
  the accepted low leaf projects to `⟨0, 0⟩`, which is not a leaf of the snapshot
  (`PinnedCounterexampleMeetsCapstoneHypotheses`; the order-theoretic side is
  `IMTAbstract.ModelStrong.Properties.padding_leaf_forges_on_guarded_history`).  So both
  readings are false at the pin (`PinnedReclaimDichotomyReadingFails`,
  `PinnedDeliveryFinalityReadingFails`).
* **The capstones re-proved over the refined gate.**  At every padding constant, with no
  hash premise: acceptance on which no `TreeRootBreak` is located discharges `W ∈ S j`
  (`BreakFreeGateImpliesMemberGate`); on run snapshots the break-free gate is the capstones'
  member gate for nonzero values (`BreakFreeGateMatchesMemberGate`); both headlines hold for
  it (`BreakFreeGateDichotomy`, `BreakFreeDeliveryFinality`); and the "no missed refunds"
  half holds for the deployed check itself (`DeployedGateLiveness`).
* **No false refunds, located.**  On every reached snapshot, at every padding constant, an
  absence proof accepted for a delivered value carries one of the three cases `wrongLength`,
  `pathCollision`, `leafCollision` of `TreeRootBreak`, or is a padding hit at the published
  height (`DeliveredRefundLocatesCollisionOrPaddingHit`).  At reached snapshots whose leaf
  count is `2 ^ _height` (on reached states, exactly the power-of-two leaf counts) it always
  carries one of the three cases (`FullSnapshotRefundOfDeliveredNeedsCollision`).  So does
  one presenting a leaf whose hash is not the padding constant, at every reached snapshot
  (`DedicatedPaddingRefundOfDeliveredNeedsCollision`).  The pin's submission shape, replayed
  under a dedicated constant, needs a node-hash collision on its own path
  (`DedicatedPaddingZeroLeafNeedsPathCollision`).
* **The stored root at either revision.**  With the padding constant a parameter of
  `setup`, the transcribed `IndexedMerkleTree.root()` returns `HState.root` on every state
  the transcribed contract reaches, and every state reached from `hSetup` is the view of
  such a state (`StoredRootAtPaddingIsPublished`, `ReachedStatesLiftAtPadding`; at the pin's
  constant the setup is `cSetup`, `SetupAtPaddingIsPinnedSetup`).  So the statements above,
  made at `HState.root`, are about the root `root()` returns at c67894b9's padding and at
  b17415d20's, up to the compiled-code obligation `MODEL-FULLMERKLE`.
* **Witnesses.**  Every premise above is met on a concrete instance; the dedicated padding
  alone does not make either reading hold for every hash
  (`DedicatedPaddingReadingsFailUnderToyHashes`).

The three cases `wrongLength`, `pathCollision` and `leafCollision` (`TreeRootBreakAt`) are
each an equation between hash outputs of values the instance names.  `pathCollision` is a
node-hash collision on the submitted path.  `leafCollision` is a `hashLeaf` collision
between the occupied leaf and the presented one.  `wrongLength` is a node-hash collision on
a re-anchored or split walk, or the presented leaf hash, a stored leaf hash or the padding
constant equal to a node hash.  For `keccak256` each asks for a collision or a preimage on
named inputs.  The fourth case, `paddingHit`, asks only that the presented leaf, at an
empty index, hash to the padding constant; at the pin the leaf `{0,0,0}` does so by
definition, with no collision or preimage search.
-/

namespace IMTAbstract.ReclaimGateFaithful

open Clear IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-! ## The countermodel at c67894b9 -/

/-- **WHICH REACHED SNAPSHOTS HAVE AN EMPTY SLOT.**  On a state reached from `setup`,
`FullMerkle._height` leaves an empty slot below capacity exactly when the leaf count is not
a power of two, and the tree is full at its own height exactly when the leaf count is a
power of two. -/
def Properties.ReachedBelowCapacityIffNotPowerOfTwo : Prop :=
  ∀ S : HState, HReaches hSetup S →
    (S.tree.leafCount < 2 ^ S.height ↔ ∀ k : ℕ, S.tree.leafCount ≠ 2 ^ k)
      ∧ (S.tree.leafCount = 2 ^ S.height ↔ ∃ k : ℕ, S.tree.leafCount = 2 ^ k)

/-! ## The capstones re-proved over the refined gate -/

/-- **BREAK-FREE ACCEPTANCE DISCHARGES `W ∈ S`.**  If `verifyNonInclusion` accepts a
submission for `v` against `S`'s published root, and no `TreeRootBreak` is located on it,
then a MEMBER of the state's leaf set carries a window straddling `v`.  Every state, every
padding constant, no hash premise.  This derives the membership hypothesis of the capstones
from the verifier (it is `Contracts.InteropCommitmentTree.Properties.NonInclusionSoundOrBreak`
at the published height). -/
def Properties.BreakFreeGateImpliesMemberGate : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState) (v : UInt256),
    BreakFreeGate h z0 hl S v → MemberGate (toAbs S.tree) v

/-- **NO MISSED REFUNDS, FOR THE DEPLOYED CHECK.**  Along every run from `setup`, at every
step and every padding constant, every absent nonzero value passes `BreakFreeGate`, hence
`DeployedGate`.  (The proof uses the honest proof of an occupied low leaf, clause 2 of
`Contracts.InteropCommitmentTree.Properties.RunRootsExclusiveOrBreakAtOwnHeight`.)  This is
the half of `ReclaimDichotomyReading` that holds at the pin. -/
def Properties.DeployedGateLiveness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → HState), HRun R → R 0 = hSetup →
    ∀ (j : ℕ) (v : UInt256), v ≠ 0 → v ∉ keys (absHistory R j) →
      BreakFreeGate h z0 hl (R j) v ∧ DeployedGate h z0 hl (R j) v

/-- **THE RECLAIM DICHOTOMY, RE-PROVED OVER THE REFINED GATE.**  Along every run from
`setup`, at every step and every padding constant: a nonzero value passes `BreakFreeGate`
iff it is absent.  This is `guardedEvolution_reclaimable_iff_absent` with `W ∈ S j` replaced
by "no located break on the submission".  It holds at c67894b9 too: there the padding
forgery's submission carries a located `paddingHit` and so does not pass this gate. -/
def Properties.BreakFreeGateDichotomy : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → HState), HRun R → R 0 = hSetup →
    ∀ (j : ℕ) (v : UInt256), v ≠ 0 →
      (BreakFreeGate h z0 hl (R j) v ↔ v ∉ keys (absHistory R j))

/-- **ON RUN SNAPSHOTS, THE BREAK-FREE GATE IS THE CAPSTONES' GATE.**  Along every run from
`setup`, at every step and every padding constant, a nonzero value passes `BreakFreeGate`
iff the capstones' member gate is open for it.  So, along runs from `setup`, the
genesis-rooted reclaim capstone is an exact statement about `verifyNonInclusion` restricted
to break-free submissions.  `DeployedGate`, which does not exclude submissions with a
located break, does not match it at the pin (`PinnedReclaimDichotomyReadingFails`). -/
def Properties.BreakFreeGateMatchesMemberGate : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → HState), HRun R → R 0 = hSetup →
    ∀ (j : ℕ) (v : UInt256), v ≠ 0 →
      (BreakFreeGate h z0 hl (R j) v ↔ MemberGate (absHistory R j) v)

/-- **DELIVERY FINALITY, RE-PROVED OVER THE REFINED GATE.**  Along every run from `setup`
with a monotone settlement clock `t` and deadline `D`, at every padding constant: a value
delivered at an on-time step stays delivered at every later step, and fails
`BreakFreeGate` at every step meeting the abstract pin `D < t (j + 1)`.
`guardedEvolution_delivered_available_forever` with the refined gate in place of
`W ∈ S j`. -/
def Properties.BreakFreeDeliveryFinality : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → HState), HRun R → R 0 = hSetup →
    ∀ (t : ℕ → UInt256) (D v : UInt256) (i : ℕ), Monotone t → t i ≤ D →
      v ∈ keys (absHistory R i) →
        (∀ j : ℕ, i ≤ j → v ∈ keys (absHistory R j))
          ∧ ∀ j : ℕ, D < t (j + 1) → ¬ BreakFreeGate h z0 hl (R j) v

/-! ## No false refunds, located -/

/-- **AN ACCEPTED ABSENCE PROOF FOR A DELIVERED VALUE NAMES ITS BREAK.**  On every state
reached from `setup`, at every padding constant: if `verifyNonInclusion` accepts a
submission for a value the state holds, then the `wrongLength`, `pathCollision` or
`leafCollision` case of `TreeRootBreak` holds on it, or it is a padding hit with the
published path length (the index is empty and the presented leaf hashes to the padding
constant).  This sharpens
`Contracts.InteropCommitmentTree.Properties.VerifiedAbsenceExcludesDeliveredOrBreak` at the
published height: the padding case is reported only at the published length, and a padding
hit at any other length is reported as `wrongLength`.  At the pin the zero leaf `{0,0,0}`
meets the padding case's hash condition by definition. -/
def Properties.DeliveredRefundLocatesCollisionOrPaddingHit : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState), HReaches hSetup S →
    ∀ (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      v ∈ keys (toAbs S.tree) →
      NonInclusionAccepted h hl (S.root h z0 hl) v ℓ idx sibs k →
        TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .wrongLength
          ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .pathCollision
          ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .leafCollision
          ∨ (k = S.height ∧ S.tree.leafCount ≤ idx ∧ hl ℓ = z0)

/-- **AT A FULL SNAPSHOT, EVEN THE PIN NEEDS ONE OF THE THREE OTHER CASES.**  On every state
reached from `setup` whose leaf count is `2 ^ _height` (on reached states exactly the
power-of-two leaf counts 1, 2, 4, 8, …: `ReachedBelowCapacityIffNotPowerOfTwo`), at every
padding constant, the pinned one included: an absence proof accepted for a delivered value
carries the `wrongLength`, `pathCollision` or `leafCollision` case.  With
`PinnedGateAcceptsEveryValueOffPowersOfTwo`, at the pin: on reached snapshots whose leaf
count is not a power of two, every nonzero value, delivered or not, has an accepted absence
proof carrying none of these three cases; on the others, no delivered value has one. -/
def Properties.FullSnapshotRefundOfDeliveredNeedsCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState), HReaches hSetup S →
    S.tree.leafCount = 2 ^ S.height →
    ∀ (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      v ∈ keys (toAbs S.tree) →
      NonInclusionAccepted h hl (S.root h z0 hl) v ℓ idx sibs k →
        TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .wrongLength
          ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .pathCollision
          ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .leafCollision

/-- **WHAT A PRESENTED LEAF OFF THE PADDING CONSTANT BUYS.**  On every state reached from
`setup`, at every padding constant: if the presented low leaf's hash is not the padding
constant, an absence proof accepted for a delivered value carries the `wrongLength`,
`pathCollision` or `leafCollision` case.  The premise is pinned to the one submitted leaf.
At b17415d20 it says the presented leaf is not a `hashLeaf` preimage of
`IMT_EMPTY_LEAF_HASH`; for the pin's attack leaf `{0,0,0}` it is `DedicatedPadding`.  At
c67894b9 it fails for `{0,0,0}`.  Compare
`AttackVectors.StaleSnapshotFaithful.Properties.StaleWitnessNotRedeemableOrCollision`, the
run-level form with an abstract deadline pin; here the value is delivered at the snapshot
the proof is checked against, and the root is at the run's own height. -/
def Properties.DedicatedPaddingRefundOfDeliveredNeedsCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState), HReaches hSetup S →
    ∀ (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      hl ℓ ≠ z0 →
      v ∈ keys (toAbs S.tree) →
      NonInclusionAccepted h hl (S.root h z0 hl) v ℓ idx sibs k →
        TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .wrongLength
          ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .pathCollision
          ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .leafCollision

/-- **THE PIN'S SUBMISSION SHAPE, UNDER A DEDICATED CONSTANT, NEEDS A PATH COLLISION.**
Assume `DedicatedPadding hl z0`: the padding constant is not `hashLeaf({0,0,0})`.  Then in
any state, if `verifyNonInclusion` accepts, for any value, the zero leaf `{0,0,0}` at an
EMPTY index with a path of the published height, that path carries a `PathCollision`: at a
named level, the pair the verifier hashed differs from the tree's pair there and has the
same node hash. -/
def Properties.DedicatedPaddingZeroLeafNeedsPathCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), DedicatedPadding hl z0 →
    ∀ (S : HState) (v : UInt256) (idx : ℕ) (sibs : ℕ → UInt256),
      S.tree.leafCount ≤ idx →
      NonInclusionAccepted h hl (S.root h z0 hl) v ⟨0, 0, 0⟩ idx sibs S.height →
        PathCollision h z0 (leafHashes hl S.tree) sibs 0 S.height idx (hl ⟨0, 0, 0⟩)

/-! ## The stored root at either revision -/

/-- **ONE SETUP FOR BOTH REVISIONS.**  At the pin's padding constant, `cSetupPad` is
the pinned `Contracts.InteropCommitmentTree.cSetup`, and its reached states are exactly
`CReaches`'s. -/
def Properties.SetupAtPaddingIsPinnedSetup : Prop :=
  ∀ (h : Hash) (hl : LeafHash),
    cSetupPad h hl (zeroLeafHash hl) = cSetup h hl
      ∧ ∀ S : CState, CReachesPad h hl (zeroLeafHash hl) S ↔ CReaches h hl S

/-- **THE STORED ROOT IS THE PUBLISHED ROOT, AT EVERY PADDING CONSTANT.**  For every node
hash, leaf hash and padding constant `z0`, every state reached from `cSetupPad h hl z0`
by guarded inserts has, as its `RunHeight` view, a state reached from `hSetup`, and the
transcribed `IndexedMerkleTree.root()` (`_nodes[_height][0]`) returns `HState.root h z0 hl`
of that view.  At `z0 = IMT_EMPTY_LEAF_HASH` this is b17415d20's `setup` and `root()`; at
`z0 = zeroLeafHash hl` it is
`Contracts.InteropCommitmentTree.Properties.CReachesRootIsPublished`. -/
def Properties.StoredRootAtPaddingIsPublished : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (z0 : UInt256) (S : CState), CReachesPad h hl z0 S →
    HReaches hSetup S.toH ∧ S.root = some (S.toH.root h z0 hl)

/-- **NO REACHED STATE IS LOST, AT EVERY PADDING CONSTANT.**  Every state reached from
`hSetup` is the `RunHeight` view of a state reached from `cSetupPad h hl z0`, for every
node hash, leaf hash and padding constant (so no guarded insert on the way reverts inside
`FullMerkle`). -/
def Properties.ReachedStatesLiftAtPadding : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (z0 : UInt256) (S : HState), HReaches hSetup S →
    ∃ C : CState, CReachesPad h hl z0 C ∧ C.toH = S

/-! ## Witnesses -/

/-- **THE PADDING PREMISE: FALSE AT THE PIN, SATISFIABLE IN GENERAL.**  For every leaf hash,
`DedicatedPadding` fails for the pinned constant `zeroLeafHash hl`, by construction.  It
holds for the toy leaf hash with padding `1`.  (For `keccak256` at b17415d20 it holds by the
off-line computation in the spec's module header.) -/
def Properties.DedicatedPaddingPremiseWitness : Prop :=
  (∀ hl : LeafHash, ¬ DedicatedPadding hl (zeroLeafHash hl))
    ∧ DedicatedPadding toyLeafHash 1

/-- **BOTH KINDS OF REACHED SNAPSHOT OCCUR.**  For `0 < a < b`: `hInsert hSetup a 0` (two
leaves at height 1) is reached and full, with a power-of-two leaf count; `hThree a b` (three
leaves at height 2) is reached and below capacity, and its leaf count is no power of two.  So
both sides of both equivalences of `ReachedBelowCapacityIffNotPowerOfTwo` occur, and the
shape premises of `PinnedGateAcceptsEveryValueBelowCapacity`,
`PinnedGateAcceptsEveryValueOffPowersOfTwo` and `FullSnapshotRefundOfDeliveredNeedsCollision`
are each met on a reached state. -/
def Properties.ReachedSnapshotShapesWitness : Prop :=
  ∀ a b : UInt256, 0 < a → a < b →
    HReaches hSetup (hInsert hSetup a 0)
      ∧ (hInsert hSetup a 0).tree.leafCount = 2 ^ (hInsert hSetup a 0).height
      ∧ (∃ k : ℕ, (hInsert hSetup a 0).tree.leafCount = 2 ^ k)
      ∧ HReaches hSetup (hThree a b)
      ∧ (hThree a b).tree.leafCount < 2 ^ (hThree a b).height
      ∧ ∀ k : ℕ, (hThree a b).tree.leafCount ≠ 2 ^ k

/-- **THE REFINED GATE OPENS AND CLOSES ON ONE RUN.**  For every node hash, leaf hash and
padding constant, and `0 < a < b`, on `hThreeRun a b` from `hSetup`: at step 1, `b` is
nonzero and absent, `BreakFreeGate` holds for it and so does the capstones' member gate; at
step 2, `a` is delivered and `BreakFreeGate` fails for it.  So the premise of
`BreakFreeGateImpliesMemberGate` is met, and both sides of `BreakFreeGateDichotomy` and
`BreakFreeGateMatchesMemberGate` occur on one run, for every hash. -/
def Properties.BreakFreeGateRunWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    HRun (hThreeRun a b) ∧ hThreeRun a b 0 = hSetup
      ∧ b ≠ 0 ∧ b ∉ keys (absHistory (hThreeRun a b) 1)
      ∧ BreakFreeGate h z0 hl (hThreeRun a b 1) b
      ∧ MemberGate (absHistory (hThreeRun a b) 1) b
      ∧ a ∈ keys (absHistory (hThreeRun a b) 2)
      ∧ ¬ BreakFreeGate h z0 hl (hThreeRun a b 2) a

/-- **THE PREMISES OF THE FULL-SNAPSHOT AND DEDICATED-PADDING STATEMENTS ARE MET.**  For
`0 < a`, with the toy node and leaf hashes (`L2InteropCommitmentTree/Specs/TreeRoot.lean`)
and the dedicated padding `1`: the state `setup; insert a` is reached and full (two leaves
at height 1), `a` is delivered, `DedicatedPadding` holds (so the presented zero leaf does not
hash to the padding constant), and `verifyNonInclusion` accepts the zero leaf at index 0
with sibling `0` for `a`.  This meets every premise of
`DeliveredRefundLocatesCollisionOrPaddingHit`, `FullSnapshotRefundOfDeliveredNeedsCollision`
and `DedicatedPaddingRefundOfDeliveredNeedsCollision`.  The break located on this submission
is exactly `pathCollision`: addition maps the verifier's level-0 pair `(0, 0)` and the tree's
pair `(-a, a)` to the same value.  So the three conclusions hold here through that case. -/
def Properties.ToyFullSnapshotRefundWitness : Prop :=
  ∀ a : UInt256, 0 < a →
    HReaches hSetup (hInsert hSetup a 0)
      ∧ (hInsert hSetup a 0).height = 1
      ∧ (hInsert hSetup a 0).tree.leafCount = 2 ^ (hInsert hSetup a 0).height
      ∧ a ∈ keys (toAbs (hInsert hSetup a 0).tree)
      ∧ DedicatedPadding toyLeafHash 1
      ∧ NonInclusionAccepted toyNodeHash toyLeafHash
          ((hInsert hSetup a 0).root toyNodeHash 1 toyLeafHash) a ⟨0, 0, 0⟩ 0 (fun _ => 0)
          (hInsert hSetup a 0).height
      ∧ TreeRootBreakExactly toyNodeHash 1 toyLeafHash (hInsert hSetup a 0).tree
          (hInsert hSetup a 0).height (fun _ => 0) (hInsert hSetup a 0).height 0 ⟨0, 0, 0⟩
          .pathCollision

/-- **THE PREMISES OF THE ZERO-LEAF REPLAY STATEMENT ARE MET.**  For `0 < a < b`, with the
toy hashes and the dedicated padding `1`, on the reached state `hThree a b` (three leaves at
height 2, slot 3 empty): `DedicatedPadding` holds, `a` is delivered, and
`verifyNonInclusion` accepts the zero leaf at the empty index 3 with a path of the published
height for `a`, with siblings `b + 1` at level 0 and `-b` at level 1.  The pin's submission
(the zero leaf at index 3 with that slot's honest siblings) is REFUSED there.  This meets
every premise of `DedicatedPaddingZeroLeafNeedsPathCollision`. -/
def Properties.ToyEmptyIndexRefundWitness : Prop :=
  ∀ a b : UInt256, 0 < a → a < b →
    HReaches hSetup (hThree a b) ∧ (hThree a b).height = 2
      ∧ (hThree a b).tree.leafCount ≤ 3
      ∧ a ∈ keys (toAbs (hThree a b).tree)
      ∧ DedicatedPadding toyLeafHash 1
      ∧ NonInclusionAccepted toyNodeHash toyLeafHash
          ((hThree a b).root toyNodeHash 1 toyLeafHash) a ⟨0, 0, 0⟩ 3
          (fun l => if l = 0 then b + 1 else -b) (hThree a b).height
      ∧ ¬ NonInclusionAccepted toyNodeHash toyLeafHash
          ((hThree a b).root toyNodeHash 1 toyLeafHash) a ⟨0, 0, 0⟩ 3
          (honestSibs toyNodeHash 1 (leafHashes toyLeafHash (hThree a b).tree) 3)
          (hThree a b).height

/-- **THE PREMISES OF THE FINALITY STATEMENTS ARE MET.**  For `0 < a < b`, the run
`hThreeRun a b` from `hSetup`, the clock `reclaimGateWitnessClock` (monotone; steps 0–2 at
time 0, later steps at time 1) and deadline `0` make step 2 on time and meet the abstract
pin at step 2 (by step 3), with `a` delivered at step 2. -/
def Properties.FinalityPremisesWitness : Prop :=
  ∀ a b : UInt256, 0 < a → a < b →
    HRun (hThreeRun a b) ∧ hThreeRun a b 0 = hSetup
      ∧ Monotone reclaimGateWitnessClock ∧ reclaimGateWitnessClock 2 ≤ 0
      ∧ a ∈ keys (absHistory (hThreeRun a b) 2)
      ∧ (0 : UInt256) < reclaimGateWitnessClock (2 + 1)

/-- **THE STORED-ROOT PREMISE IS MET ON A GROWN TREE.**  For every node hash, leaf hash and
padding constant, and `0 < a < b`, the transcribed contract reaches from
`cSetupPad h hl z0` a state whose view is `hThree a b` (three leaves at height 2), and
the transcribed `root()` returns `(hThree a b).root h z0 hl` there. -/
def Properties.StoredRootAtPaddingWitness : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (z0 : UInt256) (a b : UInt256), 0 < a → a < b →
    ∃ C : CState, CReachesPad h hl z0 C ∧ C.toH = hThree a b
      ∧ C.root = some ((hThree a b).root h z0 hl)

/-- **A DEDICATED PADDING CONSTANT ALONE DOES NOT MAKE THE READINGS HOLD.**  With the toy
hashes and the padding `1`, which meets `DedicatedPadding`, both readings fail: on
`hThreeRun 1 2`, `DeployedGate` holds at step 2 for the delivered value `1`, through the
submission of `ToyEmptyIndexRefundWitness` (whose path carries a `PathCollision`, by
`DedicatedPaddingZeroLeafNeedsPathCollision`).  So neither reading holds for every hash at
a dedicated padding constant either; what the dedicated constant removes is the padding case
(`DedicatedPaddingRefundOfDeliveredNeedsCollision`). -/
def Properties.DedicatedPaddingReadingsFailUnderToyHashes : Prop :=
  DedicatedPadding toyLeafHash 1
    ∧ ¬ ReclaimDichotomyReading toyNodeHash 1 toyLeafHash
    ∧ ¬ DeliveryFinalityReading toyNodeHash 1 toyLeafHash

end IMTAbstract.ReclaimGateFaithful
