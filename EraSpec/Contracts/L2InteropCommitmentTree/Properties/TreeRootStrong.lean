import EraSpec.Contracts.L2InteropCommitmentTree.Specs.TreeRootStrong
import EraSpec.Protocol.Spec

/-!
# Properties: the seven soundness results, under a hash premise a hash can meet

Statements about `EraSpec.Contracts.L2InteropCommitmentTree.Specs.TreeRootStrong`; proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.TreeRootStrong`.

`Properties/TreeRoot.lean` states `AcceptedPathPinsLeaf`, `InclusionSound`,
`NonInclusionSound`, `VerifiedAbsenceExcludesDelivered`, `ProofsExclusive`,
`RunRootsExclusive` and `VerifiedAbsenceIsWitness` under `HashAssumptions`, which no hash
meets (`Properties.HashAssumptionsUnsatisfiable`), so all seven are vacuous. Each is
restated here with the SAME conclusion and `HashAssumptions` replaced by
`TreeRootStrongLogSafe`, a premise on the values one verification touches.

* **The engine** — on an accepted path whose log is safe, no `TreeRootBreak` is located
  (`TreeRootStrongLogSafeExcludesBreak`). Each case of the break names two distinct
  logged pairs with one node hash, or a logged domain hit, so it contradicts one field
  of the premise. The seven results then follow from the `…OrBreak` forms.
* **The log is bounded** — at most `k + 2 ^ height` pairs (`TreeRootStrongLogBounded`).
* **At the published root** — along every run from `hSetup`, at each step's own
  `_height`: completeness with safe honest logs (given a collision-free tree log), and
  exclusivity for safe logs (`TreeRootStrongRunRootsAtOwnHeight`).
* **Anti-vacuity**:
  - on an honest proof the premise holds iff the tree's own log has no node-hash
    collision (`TreeRootStrongHonestLogSafeIff`), for every padding constant;
  - `TreeRootStrongWitness` exhibits that, with accepted honest inclusion and
    non-inclusion proofs on the run state `threeLeafTree 1 2`, at the extraction pin's
    padding; `TreeRootStrongRunRootsAtOwnHeightWitness` does the same on a run;
  - with a dedicated padding constant, the pin's forgery itself has a safe log, and the
    results reject it (`TreeRootStrongDedicatedPaddingWitness`), so the premise is met
    by attacks as well as by honest proofs;
  - the premise cannot be dropped: with it deleted, all seven conclusions fail
    (`TreeRootStrongWithoutPremiseFails`). At the pin, for every hash, the forged absence
    proof for a delivered value is accepted and fails the premise
    (`TreeRootStrongPinForgeryFailsLogSafe`). When the tree's log has no collision, the
    padding clause is the only clause it fails (`TreeRootStrongPinForgeryFailsOnlyPadding`).
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier
open Contracts.InteropCommitmentTree Contracts.Protocol

/-! ## The engine -/

/-- **A SAFE LOG LOCATES NO BREAK.** If a path is accepted against `root h z0 hl T height`
and its query log is safe, then no `TreeRootBreak` is located on it, for any index and
path length the prover chose. -/
def Properties.TreeRootStrongLogSafeExcludesBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ) (sibs : ℕ → UInt256)
    (k idx : ℕ) (ℓ : Leaf),
    PathAccepts h (root h z0 hl T height) sibs k idx (hl ℓ) →
    TreeRootStrongLogSafe h z0 hl T height sibs k idx ℓ →
      ¬ TreeRootBreak h z0 hl T height sibs k idx ℓ

/-- **THE LOG IS BOUNDED.** One verification logs at most `k + 2 ^ height` pairs: `k` along
the submitted path and fewer than `2 ^ height` in the tree. So `nodeInjOn` asks for no
collision among that many pairs, not for injectivity on all pairs. -/
def Properties.TreeRootStrongLogBounded : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ) (sibs : ℕ → UInt256)
    (k idx : ℕ) (ℓ : Leaf),
    (treeRootStrongWalkLog h sibs k idx (hl ℓ)
      ∪ treeRootStrongTreeLog h z0 (leafHashes hl T) height).card ≤ k + 2 ^ height

/-! ## The seven results, with their original conclusions -/

/-- **`AcceptedPathPinsLeaf`, NON-VACUOUS.** An accepted path whose log is safe names an
occupied index holding the presented leaf: the length is the tree's height, the index is
below `leafCount`, and the leaf stored there IS the presented preimage. -/
def Properties.TreeRootStrongAcceptedPathPinsLeaf : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ) (sibs : ℕ → UInt256)
    (k idx : ℕ) (ℓ : Leaf),
    PathAccepts h (root h z0 hl T height) sibs k idx (hl ℓ) →
    TreeRootStrongLogSafe h z0 hl T height sibs k idx ℓ →
      k = height ∧ idx < T.leafCount ∧ T.leaf idx = ℓ

/-- **`InclusionSound`, NON-VACUOUS.** A verified inclusion proof whose log is safe means
delivered: the value is a key of the tree's projection. -/
def Properties.TreeRootStrongInclusionSound : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf)
    (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    InclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k →
    TreeRootStrongLogSafe h z0 hl T height sibs k idx ℓ →
      v ∈ keys (toAbs T)

/-- **`NonInclusionSound`, NON-VACUOUS.** A verified non-inclusion proof whose log is safe is
a reclaim witness in the tree: a member of `toAbs T` whose window straddles `v`. -/
def Properties.TreeRootStrongNonInclusionSound : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf)
    (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k →
    TreeRootStrongLogSafe h z0 hl T height sibs k idx ℓ →
      ∃ W ∈ toAbs T, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- **`VerifiedAbsenceExcludesDelivered`, NON-VACUOUS.** Against a valid tree's root, a
delivered value has no verified absence proof whose log is safe. -/
def Properties.TreeRootStrongVerifiedAbsenceExcludesDelivered : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree), Valid T →
    ∀ (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k →
      TreeRootStrongLogSafe h z0 hl T height sibs k idx ℓ →
        v ∉ keys (toAbs T)

/-- **`ProofsExclusive`, NON-VACUOUS.** Against a valid tree's root, no value has both an
accepted inclusion proof and an accepted non-inclusion proof whose logs are both safe,
whatever leaves, indices, paths and path lengths the two provers present.

The premise on BOTH proofs is needed. At the extraction pin the forged absence proof is
accepted for a delivered value whose honest inclusion proof is accepted too, and it is
the absence proof's log that fails (`Properties.TreeRootStrongPinForgeryFailsLogSafe`). -/
def Properties.TreeRootStrongProofsExclusive : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree), Valid T →
    ∀ (height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      TreeRootStrongLogSafe h z0 hl T height s₁ k₁ i₁ ℓ₁ →
      TreeRootStrongLogSafe h z0 hl T height s₂ k₂ i₂ ℓ₂ →
      ¬ (InclusionAccepted h hl (root h z0 hl T height) v ℓ₁ i₁ s₁ k₁
          ∧ NonInclusionAccepted h hl (root h z0 hl T height) v ℓ₂ i₂ s₂ k₂)

/-- **`RunRootsExclusive`, NON-VACUOUS.** The same at every step of every run from `setup`:
validity is not assumed, it is inherited from the run. -/
def Properties.TreeRootStrongRunRootsExclusive : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → Tree), Run R → R 0 = setup →
    ∀ (n height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      TreeRootStrongLogSafe h z0 hl (R n) height s₁ k₁ i₁ ℓ₁ →
      TreeRootStrongLogSafe h z0 hl (R n) height s₂ k₂ i₂ ℓ₂ →
      ¬ (InclusionAccepted h hl (root h z0 hl (R n) height) v ℓ₁ i₁ s₁ k₁
          ∧ NonInclusionAccepted h hl (root h z0 hl (R n) height) v ℓ₂ i₂ s₂ k₂)

/-- **`VerifiedAbsenceIsWitness`, NON-VACUOUS: the multi-chain hook.** A non-inclusion proof
verified against chain `c`'s root, with a safe log, is an `AbsenceWitnessAt` for `c`, so
the `Protocol` results about absence witnesses apply to it. -/
def Properties.TreeRootStrongVerifiedAbsenceIsWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Chain → Tree) (c : Chain) (height : ℕ)
    (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    NonInclusionAccepted h hl (root h z0 hl (T c) height) v ℓ idx sibs k →
    TreeRootStrongLogSafe h z0 hl (T c) height sibs k idx ℓ →
      AbsenceWitnessAt (ofChains T) c v

/-! ## At the published root, along runs -/

/-- **THE HEADLINE AT THE PUBLISHED ROOT, UNDER PINNED PREMISES.** Along every run from
`hSetup`, at each step `n`, against the root `IndexedMerkleTree.root()` publishes at that
step's own `_height`, for every node hash, leaf hash and padding constant:

1. if the step's tree log has no node-hash collision, every value the tree holds has an
   accepted honest inclusion proof (`merklePath` of an occupied index carrying it) whose
   log is safe;
2. under the same premise, every nonzero value the tree does not hold has an accepted
   honest non-inclusion proof (`merklePath` of an occupied low leaf) whose log is safe;
3. no value has both an accepted inclusion proof and an accepted non-inclusion proof whose
   logs are both safe.

Validity and capacity come from the run. This is `RunRootsExclusive` at the run's own
height, with its vacuous premise replaced, and `RunRootsExclusiveOrBreakAtOwnHeight` with
each located break replaced by the pinned premise. -/
def Properties.TreeRootStrongRunRootsAtOwnHeight : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → HState), HRun R → R 0 = hSetup →
    ∀ n : ℕ,
    (TreeRootStrongPairInjOn h
        (treeRootStrongTreeLog h z0 (leafHashes hl (R n).tree) (R n).height) →
      ∀ v : UInt256, v ∈ keys (toAbs (R n).tree) →
        ∃ i < (R n).tree.leafCount, ((R n).tree.leaf i).value = v
          ∧ InclusionAccepted h hl ((R n).root h z0 hl) v ((R n).tree.leaf i) i
              (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height
          ∧ TreeRootStrongLogSafe h z0 hl (R n).tree (R n).height
              (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height i ((R n).tree.leaf i))
    ∧ (TreeRootStrongPairInjOn h
        (treeRootStrongTreeLog h z0 (leafHashes hl (R n).tree) (R n).height) →
      ∀ v : UInt256, v ≠ 0 → v ∉ keys (toAbs (R n).tree) →
        ∃ i < (R n).tree.leafCount,
          NonInclusionAccepted h hl ((R n).root h z0 hl) v ((R n).tree.leaf i) i
              (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height
          ∧ TreeRootStrongLogSafe h z0 hl (R n).tree (R n).height
              (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height i ((R n).tree.leaf i))
    ∧ (∀ (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      TreeRootStrongLogSafe h z0 hl (R n).tree (R n).height s₁ k₁ i₁ ℓ₁ →
      TreeRootStrongLogSafe h z0 hl (R n).tree (R n).height s₂ k₂ i₂ ℓ₂ →
      ¬ (InclusionAccepted h hl ((R n).root h z0 hl) v ℓ₁ i₁ s₁ k₁
          ∧ NonInclusionAccepted h hl ((R n).root h z0 hl) v ℓ₂ i₂ s₂ k₂))

/-! ## Anti-vacuity -/

/-- **ON AN HONEST PROOF THE PREMISE IS A PROPERTY OF THE TREE.** For an occupied index
within capacity, the honest proof (the tree's own siblings, at the tree's height,
presenting the stored leaf) has a safe log iff the node hash has no collision on the
tree's own log. The prover adds no pair: every pair the honest walk hashes is a tree
pair. This holds for every node hash, leaf hash and padding constant. -/
def Properties.TreeRootStrongHonestLogSafeIff : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height i : ℕ),
    i < T.leafCount → T.leafCount ≤ 2 ^ height →
      (TreeRootStrongLogSafe h z0 hl T height (honestSibs h z0 (leafHashes hl T) i) height i
          (T.leaf i)
        ↔ TreeRootStrongPairInjOn h (treeRootStrongTreeLog h z0 (leafHashes hl T) height))

/-- **THE PREMISES ARE SATISFIABLE.** With the witness hash pair, at the extraction pin's
padding `hl {0,0,0}`, on the valid run state `threeLeafTree 1 2` (reached from `setup` by
a `Run`) at height 2: the tree's log has no node-hash collision; the honest inclusion
proof for `1` (leaf 1) is accepted and its log is safe; and the honest non-inclusion
proof for `3` (low leaf 2) is accepted and its log is safe. So every premise of every
result above holds on some instance (for the two exclusivity results, on two proofs of
different values, as they must). -/
def Properties.TreeRootStrongWitness : Prop :=
  Valid (threeLeafTree 1 2)
    ∧ (∃ R : ℕ → Tree, Run R ∧ R 0 = setup ∧ R 2 = threeLeafTree 1 2)
    ∧ TreeRootStrongPairInjOn treeRootStrongWitnessNodeHash
        (treeRootStrongTreeLog treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
          (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 2)
    ∧ InclusionAccepted treeRootStrongWitnessNodeHash treeRootStrongWitnessLeafHash
        (root treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
          treeRootStrongWitnessLeafHash (threeLeafTree 1 2) 2)
        1 ((threeLeafTree 1 2).leaf 1) 1
        (honestSibs treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
          (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 1) 2
    ∧ TreeRootStrongLogSafe treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
        treeRootStrongWitnessLeafHash (threeLeafTree 1 2) 2
        (honestSibs treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
          (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 1) 2 1
        ((threeLeafTree 1 2).leaf 1)
    ∧ NonInclusionAccepted treeRootStrongWitnessNodeHash treeRootStrongWitnessLeafHash
        (root treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
          treeRootStrongWitnessLeafHash (threeLeafTree 1 2) 2)
        3 ((threeLeafTree 1 2).leaf 2) 2
        (honestSibs treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
          (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 2) 2
    ∧ TreeRootStrongLogSafe treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
        treeRootStrongWitnessLeafHash (threeLeafTree 1 2) 2
        (honestSibs treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
          (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 2) 2 2
        ((threeLeafTree 1 2).leaf 2)

/-- **THE PREMISE HOLDS ON AN ATTACK, AND THE RESULTS REJECT IT.** Keep the witness hash
pair, and replace the pin's padding `hl {0,0,0}` by a dedicated constant `7`, as
`IMT_EMPTY_LEAF_HASH` replaces it in later revisions. On `threeLeafTree 1 2` at height 2,
take the pin's forgery: the sentinel `{0,0,0}` presented at the empty slot 3 with that
slot's honest siblings, as an absence proof for the delivered value `1`. Its log is now
safe, so `TreeRootStrongVerifiedAbsenceExcludesDelivered` applies to it, and
`verifyNonInclusion` does reject it. So the premise is met by an adversarial proof as well
as by honest ones, and the results above are not vacuous on attacks. -/
def Properties.TreeRootStrongDedicatedPaddingWitness : Prop :=
  1 ∈ keys (toAbs (threeLeafTree 1 2))
    ∧ TreeRootStrongLogSafe treeRootStrongWitnessNodeHash 7 treeRootStrongWitnessLeafHash
        (threeLeafTree 1 2) 2
        (honestSibs treeRootStrongWitnessNodeHash 7
          (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 3) 2 3 ⟨0, 0, 0⟩
    ∧ ¬ NonInclusionAccepted treeRootStrongWitnessNodeHash treeRootStrongWitnessLeafHash
        (root treeRootStrongWitnessNodeHash 7 treeRootStrongWitnessLeafHash (threeLeafTree 1 2) 2)
        1 ⟨0, 0, 0⟩ 3
        (honestSibs treeRootStrongWitnessNodeHash 7
          (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 3) 2

/-- **THE RUN-LEVEL PREMISE IS SATISFIABLE.** `hThreeRun 1 2` is an `HRun` from `hSetup`;
its step 2 is `threeLeafTree 1 2` at its own `_height` 2; and with the witness hash pair, at
the extraction pin's padding, that step's tree log has no node-hash collision. So clauses 1
and 2 of `TreeRootStrongRunRootsAtOwnHeight` apply at step 2, and the honest proofs they
return meet the premises of its clause 3 (`TreeRootStrongWitness` exhibits two). -/
def Properties.TreeRootStrongRunRootsAtOwnHeightWitness : Prop :=
  HRun (hThreeRun 1 2) ∧ hThreeRun 1 2 0 = hSetup
    ∧ (hThreeRun 1 2 2).tree = threeLeafTree 1 2 ∧ (hThreeRun 1 2 2).height = 2
    ∧ TreeRootStrongPairInjOn treeRootStrongWitnessNodeHash
        (treeRootStrongTreeLog treeRootStrongWitnessNodeHash
          (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
          (leafHashes treeRootStrongWitnessLeafHash (hThreeRun 1 2 2).tree)
          (hThreeRun 1 2 2).height)

/-- **THE PREMISE CANNOT BE DROPPED.** At the extraction pin (padding `hl {0,0,0}`), for
every node hash and leaf hash and every `0 < a < b`, on the valid run state
`threeLeafTree a b` at height 2: `a` is delivered; its honest inclusion proof (leaf 1) is
accepted; the forged absence proof (the sentinel `{0,0,0}` at the empty slot 3) is
accepted too; no member of the tree's projection straddles `a`; and the forged proof's
log is not safe.

So without the premise the conclusions of `TreeRootStrongAcceptedPathPinsLeaf`,
`TreeRootStrongNonInclusionSound`, `TreeRootStrongVerifiedAbsenceExcludesDelivered`,
`TreeRootStrongProofsExclusive` and `TreeRootStrongVerifiedAbsenceIsWitness` all fail
here, for every hash. (`TreeRootStrongRunRootsExclusive` fails the same way at step 2 of
the run in `Properties.RunRootsExclusiveOrBreakSatisfiable`; `TreeRootStrongInclusionSound`
fails on the forged inclusion proofs of `Properties.TreeRootBreakEveryCaseFires`.) -/
def Properties.TreeRootStrongPinForgeryFailsLogSafe : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    Valid (threeLeafTree a b)
      ∧ a ∈ keys (toAbs (threeLeafTree a b))
      ∧ InclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2) a
          ((threeLeafTree a b).leaf 1) 1
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 1) 2
      ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2) a ⟨0, 0, 0⟩ 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2
      ∧ ¬ (∃ W ∈ toAbs (threeLeafTree a b), W.key < a ∧ (W.nextKey = 0 ∨ a < W.nextKey))
      ∧ ¬ TreeRootStrongLogSafe h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2 3 ⟨0, 0, 0⟩

/-- **WITHOUT A HASH PREMISE THE SEVEN CONCLUSIONS FAIL.** Each conjunct negates one of
the seven statements of `Properties/TreeRoot.lean` with `HashAssumptions` deleted
(`AcceptedPathPinsLeaf`, `NonInclusionSound`, `VerifiedAbsenceExcludesDelivered`,
`ProofsExclusive`, `RunRootsExclusive`, `VerifiedAbsenceIsWitness`, then
`InclusionSound`). The first six fail at the extraction pin's padding `hl {0,0,0}` for
every node hash and leaf hash, on the forged absence proof of
`TreeRootStrongPinForgeryFailsLogSafe` and on the run of
`RunRootsExclusiveOrBreakSatisfiable`. `InclusionSound` fails under the toy hash pair,
on a forged inclusion proof of `TreeRootBreakEveryCaseFires`. So the intended readings
need a hash premise, and `TreeRootStrongLogSafe` is one that can hold. -/
def Properties.TreeRootStrongWithoutPremiseFails : Prop :=
  (∀ (h : Hash) (hl : LeafHash),
    (¬ ∀ (T : Tree) (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf),
        PathAccepts h (root h (hl ⟨0, 0, 0⟩) hl T height) sibs k idx (hl ℓ) →
          k = height ∧ idx < T.leafCount ∧ T.leaf idx = ℓ)
    ∧ (¬ ∀ (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256)
          (k : ℕ),
        NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl T height) v ℓ idx sibs k →
          ∃ W ∈ toAbs T, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
    ∧ (¬ ∀ (T : Tree), Valid T →
        ∀ (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
          NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl T height) v ℓ idx sibs k →
            v ∉ keys (toAbs T))
    ∧ (¬ ∀ (T : Tree), Valid T →
        ∀ (height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256)
          (k₁ k₂ : ℕ),
          ¬ (InclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl T height) v ℓ₁ i₁ s₁ k₁
              ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl T height) v ℓ₂ i₂ s₂ k₂))
    ∧ (¬ ∀ (R : ℕ → Tree), Run R → R 0 = setup →
        ∀ (n height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256)
          (k₁ k₂ : ℕ),
          ¬ (InclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (R n) height) v ℓ₁ i₁ s₁ k₁
              ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (R n) height) v ℓ₂ i₂ s₂ k₂))
    ∧ (¬ ∀ (T : Chain → Tree) (c : Chain) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ)
          (sibs : ℕ → UInt256) (k : ℕ),
        NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (T c) height) v ℓ idx sibs k →
          AbsenceWitnessAt (ofChains T) c v))
  ∧ ¬ ∀ (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256)
      (k : ℕ),
      InclusionAccepted toyNodeHash toyLeafHash (root toyNodeHash 1 toyLeafHash T height) v ℓ idx
        sibs k → v ∈ keys (toAbs T)

/-- **THE PADDING CLAUSE IS THE ONE THAT FAILS.** On the forged absence proof of
`TreeRootStrongPinForgeryFailsLogSafe`, for every node hash and leaf hash:

* the forged walk hashes only pairs of the tree's own log: it is the honest sibling
  stream of the empty slot 3, whose level-0 entry is the padding constant `hl {0,0,0}`;
* when the tree's log has no node-hash collision, the forged proof meets each of the
  other four clauses of `TreeRootStrongLogSafe`, stated field by field: `nodeInjOn`
  (the union of the two logs is the tree's log), and `shortSeparated`, `longSeparated`
  and `openedLeafInj`, which hold because the path length is the height and slot 3 is
  empty;
* the padding clause `padNotPresented` is false here, for every hash (slot 3 is empty,
  and the presented sentinel hashes to the padding constant).

So the forgery involves no collision. It is exactly the domain hit that a dedicated
`IMT_EMPTY_LEAF_HASH` turns into a preimage problem. The collision-freeness premise holds
for the witness hash pair with `a = 1`, `b = 2` (`TreeRootStrongWitness`). -/
def Properties.TreeRootStrongPinForgeryFailsOnlyPadding : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256),
    treeRootStrongWalkLog h (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3)
        2 3 (hl ⟨0, 0, 0⟩)
      ⊆ treeRootStrongTreeLog h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 2
    ∧ (TreeRootStrongPairInjOn h
          (treeRootStrongTreeLog h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 2) →
        TreeRootStrongPairInjOn h
            (treeRootStrongWalkLog h
                (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2 3
                (hl ⟨0, 0, 0⟩)
              ∪ treeRootStrongTreeLog h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 2)
          ∧ (2 < 2 → ∀ p ∈ treeRootStrongTreeLog h (hl ⟨0, 0, 0⟩)
                (leafHashes hl (threeLeafTree a b)) 2, hl ⟨0, 0, 0⟩ ≠ h p.1 p.2)
          ∧ (2 < 2 → ∀ p ∈ treeRootStrongWalkLog h
                (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2 3
                (hl ⟨0, 0, 0⟩),
              ∀ y ∈ hl ⟨0, 0, 0⟩ :: leafHashes hl (threeLeafTree a b), y ≠ h p.1 p.2)
          ∧ (3 < (threeLeafTree a b).leafCount →
              hl ((threeLeafTree a b).leaf 3) = hl ⟨0, 0, 0⟩ →
                (threeLeafTree a b).leaf 3 = ⟨0, 0, 0⟩))
    ∧ ¬ ((threeLeafTree a b).leafCount ≤ 3 → hl ⟨0, 0, 0⟩ ≠ hl ⟨0, 0, 0⟩)

end Contracts.InteropCommitmentTree
