import EraSpec.Contracts.IndexedMerkleTree.Specs.ReclaimGateFaithful

/-!
# Properties: the reclaim capstones against the deployed refund gate

Statements about `EraSpec.Contracts.IndexedMerkleTree.Specs.ReclaimGateFaithful`; proofs in
`EraSpec.Contracts.IndexedMerkleTree.Proofs.ReclaimGateFaithful`.

The capstones of `Properties/Model.lean` are correct as stated: they quantify over a
low leaf `W ∈ S j`.  What fails is their real-contract reading at the source pin,
where the refund gate is `verifyNonInclusion` and nothing checks `W ∈ S j`.  Four
groups:

* **The countermodel at c67894b9.**  With the pin's padding constant
  `hashLeaf({0,0,0})`, the deployed gate accepts a refund for EVERY nonzero value at
  every reached snapshot whose leaf count is not a power of two, delivered values
  included, for every node hash and leaf hash (`PinnedGateAcceptsEveryValueOffPowersOfTwo`).
  The counterexample run meets the capstones' hypotheses exactly (a `GuardedEvolution`
  from the genesis singleton).  The accepted low leaf projects to the non-member
  `⟨0, 0⟩` of `forged_padding_witness_breaks_exclusivity`
  (`PinnedCounterexampleMeetsCapstoneHypotheses`).  So the real-contract readings of
  `guardedEvolution_reclaimable_iff_absent` and of `guardedEvolution_delivered_available_forever`
  part 2 are false (`PinnedReclaimDichotomyReadingFails`, `PinnedDeliveryFinalityReadingFails`).
* **The capstones re-proved over the refined gate.**  These hold at every padding constant
  and take no hash premise.  Acceptance with no located `TreeRootBreak` discharges
  `W ∈ S j` (`BreakFreeGateImpliesMemberGate`).  On run snapshots the break-free gate
  IS the capstones' gate (`BreakFreeGateMatchesMemberGate`).  Both headlines hold for
  it verbatim (`BreakFreeGateDichotomy`, `BreakFreeDeliveryFinality`), and the
  "no missed refunds" half holds for the deployed gate itself (`DeployedGateLiveness`).
* **No false refunds, located.**  An accepted refund for a delivered value carries one
  of the three collision cases, or is a padding hit at the published height
  (`DeliveredRefundLocatesCollisionOrPaddingHit`).  At snapshots with a power-of-two
  leaf count only the collision cases remain, even at the pin
  (`FullSnapshotRefundOfDeliveredNeedsCollision`).  With a dedicated padding constant
  and a presented leaf that is not a preimage of it, only the collision cases remain at
  every snapshot (`DedicatedPaddingRefundOfDeliveredNeedsCollision`).  The pin's exact
  attack, replayed under a dedicated constant, needs a node-hash collision on its own
  path (`DedicatedPaddingZeroLeafNeedsPathCollision`).
* **Witnesses.**  Every premise above is met on a concrete instance.

"The three collision cases" are the `wrongLength`, `pathCollision` and `leafCollision`
cases of `TreeRootBreak` (`TreeRootBreakAt`).  Each is an equation between hash outputs
of values the instance names.  `pathCollision` is a node-hash collision on the
submitted path.  `leafCollision` is a `hashLeaf` collision between the occupied leaf
and the presented one.  `wrongLength` is a path collision on a re-anchored walk, or a
leaf hash or the padding constant equal to a node hash.  For `keccak256` each asks for
a collision or a preimage on named inputs.  The fourth case, `paddingHit`, asks only
for a `hashLeaf` preimage of the padding constant.  At the pin the zero leaf `{0,0,0}`
is one, so this case costs nothing there.
-/

namespace IMTAbstract.ReclaimGateFaithful

open Clear IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-! ## The countermodel at c67894b9 -/

/-- **AT THE PIN, AN EMPTY SLOT OPENS THE GATE FOR EVERY VALUE.**  With the pinned
padding `zeroLeafHash hl = hashLeaf({0,0,0})`, in any state with an empty slot below
capacity at its own `_height`, the deployed refund gate accepts EVERY nonzero value: the
zero leaf at index `leafCount` with that slot's honest siblings.  Every node hash and
leaf hash; no hash premise. -/
def Properties.PinnedGateAcceptsEveryValueBelowCapacity : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (S : HState), S.tree.leafCount < 2 ^ S.height →
    ∀ v : UInt256, v ≠ 0 → DeployedGate h (zeroLeafHash hl) hl S v

/-- **WHICH REACHED SNAPSHOTS HAVE AN EMPTY SLOT.**  On a state reached from `setup`,
`FullMerkle._height` leaves an empty slot below capacity exactly when the leaf count is
not a power of two. -/
def Properties.ReachedBelowCapacityIffNotPowerOfTwo : Prop :=
  ∀ S : HState, HReaches hSetup S →
    (S.tree.leafCount < 2 ^ S.height ↔ ∀ k : ℕ, S.tree.leafCount ≠ 2 ^ k)

/-- **THE PINNED REFUND GATE ACCEPTS EVERYTHING OFF POWERS OF TWO.**  At c67894b9, at
every state reached from `setup` whose leaf count is not a power of two (3, 5, 6, 7, 9, …
leaves), the deployed refund gate accepts every nonzero value.  It accepts the
delivered values too. -/
def Properties.PinnedGateAcceptsEveryValueOffPowersOfTwo : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (S : HState), HReaches hSetup S →
    (∀ k : ℕ, S.tree.leafCount ≠ 2 ^ k) →
      ∀ v : UInt256, v ≠ 0 → DeployedGate h (zeroLeafHash hl) hl S v

/-- **THE COUNTEREXAMPLE MEETS THE CAPSTONES' HYPOTHESES.**  For every node and leaf hash
and `0 < a < b`, the run `setup; insert a; insert b` (`hThreeRun a b`) satisfies:

* it is an `HRun` from `hSetup`, and its leaf-set projection is a `GuardedEvolution` from
  the genesis singleton `{⟨0, 0⟩}`.  These are exactly the hypotheses of
  `guardedEvolution_reclaimable_iff_absent` and
  `guardedEvolution_delivered_available_forever`;
* at step 2, `a` is delivered, and the capstones' member gate is closed for it;
* yet `verifyNonInclusion` with the pinned padding accepts the zero leaf `{0,0,0}` at
  the empty index 3 for `a`, against step 2's published root at its own height.  The
  accepted leaf's projection `⟨0, 0⟩` is NOT a member of step 2's leaf set;
* so the deployed gate is open for `a`, and the break-free gate is closed. -/
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

/-- **THE RECLAIM DICHOTOMY'S REAL-CONTRACT READING IS FALSE AT THE PIN.**  For every
node hash and leaf hash, the deployed refund gate with the pinned padding does NOT fire
exactly on the absent values along runs from `setup`: it refunds a delivered leg. -/
def Properties.PinnedReclaimDichotomyReadingFails : Prop :=
  ∀ (h : Hash) (hl : LeafHash), ¬ ReclaimDichotomyReading h (zeroLeafHash hl) hl

/-- **DELIVERY FINALITY'S REAL-CONTRACT READING IS FALSE AT THE PIN.**  For every node
hash and leaf hash, the pinned deployed gate refunds a leg delivered at an on-time step,
at a deadline-pinned step, along a run from `setup` with a monotone clock. -/
def Properties.PinnedDeliveryFinalityReadingFails : Prop :=
  ∀ (h : Hash) (hl : LeafHash), ¬ DeliveryFinalityReading h (zeroLeafHash hl) hl

/-! ## The capstones re-proved over the refined gate -/

/-- **BREAK-FREE ACCEPTANCE DISCHARGES `W ∈ S`.**  If the deployed gate accepts a
submission for `v` on which no `TreeRootBreak` is located, then a MEMBER of the state's
leaf set carries a window straddling `v`.  Every state, every padding constant, no hash
premise.  This is the membership hypothesis of the capstones, derived from the
verifier instead of assumed. -/
def Properties.BreakFreeGateImpliesMemberGate : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState) (v : UInt256),
    BreakFreeGate h z0 hl S v → MemberGate (toAbs S.tree) v

/-- **NO MISSED REFUNDS, FOR THE DEPLOYED GATE.**  Along every run from `setup`, at every
step and every padding constant, every absent nonzero value passes the deployed refund
gate.  The witness is the contract's own honest proof, on which no break is located.
This is the half of `ReclaimDichotomyReading` that survives at the pin. -/
def Properties.DeployedGateLiveness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → HState), HRun R → R 0 = hSetup →
    ∀ (j : ℕ) (v : UInt256), v ≠ 0 → v ∉ keys (absHistory R j) →
      BreakFreeGate h z0 hl (R j) v ∧ DeployedGate h z0 hl (R j) v

/-- **THE RECLAIM DICHOTOMY, RE-PROVED OVER THE REFINED GATE.**  Along every run from
`setup`, at every step and every padding constant: a nonzero value passes the
break-free refund gate iff it is absent.  `guardedEvolution_reclaimable_iff_absent`
with `W ∈ S j` replaced by "no located break on the submission".  It holds at
c67894b9 as well, where the forged refunds are exactly the submissions with a padding
hit. -/
def Properties.BreakFreeGateDichotomy : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → HState), HRun R → R 0 = hSetup →
    ∀ (j : ℕ) (v : UInt256), v ≠ 0 →
      (BreakFreeGate h z0 hl (R j) v ↔ v ∉ keys (absHistory R j))

/-- **ON RUN SNAPSHOTS, THE BREAK-FREE GATE IS THE CAPSTONES' GATE.**  Along every run
from `setup`, at every step and every padding constant, a nonzero value passes the
break-free deployed gate iff the capstones' member gate is open for it.  So the
abstract capstones are exact statements about the deployed verifier read through this
gate, and through no weaker one. -/
def Properties.BreakFreeGateMatchesMemberGate : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → HState), HRun R → R 0 = hSetup →
    ∀ (j : ℕ) (v : UInt256), v ≠ 0 →
      (BreakFreeGate h z0 hl (R j) v ↔ MemberGate (absHistory R j) v)

/-- **DELIVERY FINALITY, RE-PROVED OVER THE REFINED GATE.**  Along every run from `setup`
with a monotone settlement clock `t` and deadline `D`, at every padding constant: a
value delivered at an on-time step stays delivered at every later step, and the
break-free refund gate refuses it at every deadline-pinned step.
`guardedEvolution_delivered_available_forever` with the refined gate in place of
`W ∈ S j`. -/
def Properties.BreakFreeDeliveryFinality : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → HState), HRun R → R 0 = hSetup →
    ∀ (t : ℕ → UInt256) (D v : UInt256) (i : ℕ), Monotone t → t i ≤ D →
      v ∈ keys (absHistory R i) →
        (∀ j : ℕ, i ≤ j → v ∈ keys (absHistory R j))
          ∧ ∀ j : ℕ, D < t (j + 1) → ¬ BreakFreeGate h z0 hl (R j) v

/-! ## No false refunds, located -/

/-- **A REFUND OF A DELIVERED VALUE NAMES ITS BREAK.**  On every state reached from
`setup`, at every padding constant: if the deployed gate accepts a submission for a
delivered value, then one of the three collision cases is located on it (a wrong-length
break, a collision on the submitted path, a `hashLeaf` collision with the occupied
leaf), or the submission is a padding hit AT THE PUBLISHED HEIGHT.  A padding hit means
the leaf is presented at an empty index and its hash is the padding constant.  At the
pin the last case needs no work: present `{0,0,0}`.  This sharpens
`Contracts.InteropCommitmentTree.Properties.VerifiedAbsenceExcludesDeliveredOrBreak`: a
padding hit can only be the break when the path has the published length. -/
def Properties.DeliveredRefundLocatesCollisionOrPaddingHit : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState), HReaches hSetup S →
    ∀ (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      v ∈ keys (toAbs S.tree) →
      NonInclusionAccepted h hl (S.root h z0 hl) v ℓ idx sibs k →
        TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .wrongLength
          ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .pathCollision
          ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .leafCollision
          ∨ (k = S.height ∧ S.tree.leafCount ≤ idx ∧ hl ℓ = z0)

/-- **AT A FULL SNAPSHOT, EVEN THE PIN NEEDS A COLLISION.**  On every state reached from
`setup` whose leaf count is `2 ^ _height` (1, 2, 4, 8, … leaves), at every padding
constant (the pinned one included), an accepted refund for a delivered value carries one
of the three collision cases.  So the pin's free forgery of a delivered value's refund
exists exactly on the other snapshots (`PinnedGateAcceptsEveryValueOffPowersOfTwo`). -/
def Properties.FullSnapshotRefundOfDeliveredNeedsCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState), HReaches hSetup S →
    S.tree.leafCount = 2 ^ S.height →
    ∀ (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      v ∈ keys (toAbs S.tree) →
      NonInclusionAccepted h hl (S.root h z0 hl) v ℓ idx sibs k →
        TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .wrongLength
          ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .pathCollision
          ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .leafCollision

/-- **WHAT A DEDICATED PADDING CONSTANT BUYS (PINNED PREMISE).**  On every state reached
from `setup`, if the presented low leaf's hash is not the padding constant, an accepted
refund for a delivered value carries one of the three collision cases.  The premise is
pinned to the one submitted leaf.  At e561b9cc2 it says the prover did not find a
`hashLeaf` preimage of `IMT_EMPTY_LEAF_HASH`; for the pin's attack leaf `{0,0,0}` it is
the inequality `DedicatedPadding`.  At c67894b9 the premise fails for `{0,0,0}`, and
that failure is the forgery. -/
def Properties.DedicatedPaddingRefundOfDeliveredNeedsCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState), HReaches hSetup S →
    ∀ (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      hl ℓ ≠ z0 →
      v ∈ keys (toAbs S.tree) →
      NonInclusionAccepted h hl (S.root h z0 hl) v ℓ idx sibs k →
        TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .wrongLength
          ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .pathCollision
          ∨ TreeRootBreakAt h z0 hl S.tree S.height sibs k idx ℓ .leafCollision

/-- **THE PIN'S ATTACK, REPLAYED UNDER A DEDICATED CONSTANT, NEEDS A PATH COLLISION.**
Assume `DedicatedPadding hl z0`, so the padding constant is not `hashLeaf({0,0,0})`.
Then in any state, if `verifyNonInclusion` accepts the zero leaf `{0,0,0}` at an EMPTY
index with a path of the published height, for any value, that path carries a
`PathCollision`.  A `PathCollision` is a node-hash collision between the pair the
verifier hashed and the tree's pair at a named level. -/
def Properties.DedicatedPaddingZeroLeafNeedsPathCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), DedicatedPadding hl z0 →
    ∀ (S : HState) (v : UInt256) (idx : ℕ) (sibs : ℕ → UInt256),
      S.tree.leafCount ≤ idx →
      NonInclusionAccepted h hl (S.root h z0 hl) v ⟨0, 0, 0⟩ idx sibs S.height →
        PathCollision h z0 (leafHashes hl S.tree) sibs 0 S.height idx (hl ⟨0, 0, 0⟩)

/-! ## Witnesses -/

/-- **THE PADDING PREMISE: FALSE AT THE PIN, SATISFIABLE IN GENERAL.**  For every leaf
hash, `DedicatedPadding` fails for the pinned constant `zeroLeafHash hl`, by
construction.  It holds for the toy leaf hash with padding `1`.  (For `keccak256` at
e561b9cc2 it holds by the off-line computation in the spec's module header.) -/
def Properties.DedicatedPaddingPremiseWitness : Prop :=
  (∀ hl : LeafHash, ¬ DedicatedPadding hl (zeroLeafHash hl))
    ∧ DedicatedPadding toyLeafHash 1

/-- **THE PREMISES OF THE FULL-SNAPSHOT AND DEDICATED-PADDING STATEMENTS ARE MET.**  For
`0 < a`, with the toy node and leaf hashes (`L2InteropCommitmentTree/Specs/TreeRoot.lean`)
and the dedicated padding `1`: the state `setup; insert a` is reached and full (two
leaves at height 1), `a` is delivered, `DedicatedPadding` holds, and `verifyNonInclusion`
accepts the zero leaf at index 0 with sibling `0` for `a`.  This meets every premise of
`DeliveredRefundLocatesCollisionOrPaddingHit`,
`FullSnapshotRefundOfDeliveredNeedsCollision` and
`DedicatedPaddingRefundOfDeliveredNeedsCollision`.  Their conclusions therefore force a
collision of the toy hashes on this submission.  Addition provides one: the verifier's
level-0 pair `(0, 0)` and the tree's pair `(-a, a)` have the same sum. -/
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

/-- **THE PREMISES OF THE ZERO-LEAF REPLAY STATEMENT ARE MET.**  For `0 < a < b`, with
the toy hashes and the dedicated padding `1`, on the reached state `hThree a b` (three
leaves at height 2, slot 3 empty): `DedicatedPadding` holds, `a` is delivered, and
`verifyNonInclusion` accepts the zero leaf at the empty index 3 with a path of the
published height for `a`.  The siblings are `b + 1` at level 0 and `-b` at level 1.  The
pin's exact submission, the zero leaf at index 3 with that slot's honest siblings, is
REFUSED there.  This meets every premise of `DedicatedPaddingZeroLeafNeedsPathCollision`. -/
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
`hThreeRun a b` from `hSetup`, the clock `witnessClock` (monotone; steps 0–2 at time 0,
later steps at time 1) and deadline `0` make step 2 on time and deadline-pinned (by
step 3), with `a` delivered at step 2. -/
def Properties.FinalityPremisesWitness : Prop :=
  ∀ a b : UInt256, 0 < a → a < b →
    HRun (hThreeRun a b) ∧ hThreeRun a b 0 = hSetup
      ∧ Monotone witnessClock ∧ witnessClock 2 ≤ 0
      ∧ a ∈ keys (absHistory (hThreeRun a b) 2)
      ∧ (0 : UInt256) < witnessClock (2 + 1)

end IMTAbstract.ReclaimGateFaithful
