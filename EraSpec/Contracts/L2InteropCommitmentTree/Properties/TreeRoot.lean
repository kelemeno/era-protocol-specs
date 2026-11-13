import EraSpec.Contracts.L2InteropCommitmentTree.Specs.TreeRoot
import EraSpec.Protocol.Spec

/-!
# Properties: the root and the two proof gates

Statements about `EraSpec.Contracts.L2InteropCommitmentTree.Specs.TreeRoot` — the root `FullMerkle` publishes
and the verifiers `verifyInclusion` / `verifyNonInclusion`.  Proofs are in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.TreeRoot`.

Three groups:

* **Fold correspondence** — what "the root after `insert`" means in terms of the
  list state: `insert`'s two hash-tree writes are a `List.set` followed by an
  append, and the resulting root is the `pushNewLeaf` walk.  This is the
  protocol half of root-binding piece (2) in `AttackVectors.RootBinding`; the
  compiled half stays in the sibling repo (obligation O7).
* **Soundness and completeness** — every honest proof is accepted (no hash
  premise).  The soundness statements of the `## Soundness` section take
  `HashAssumptions`, which no hash meets (`Properties.HashAssumptionsUnsatisfiable`),
  so they are vacuous and discharge nothing.  Root-binding piece (3) — the leaves a
  verified proof talks about are the leaves `toAbs` talks about, so that the `W ∈ s`
  hypothesis `IMTAbstract.forged_padding_witness_breaks_exclusivity` proves
  indispensable comes from the Merkle check — holds in two non-vacuous forms: the
  `…OrBreak` results below (the property, or a located `TreeRootBreak` on the
  submitted path, with no hash premise), and the `TreeRootStrong…` results of
  `Properties/TreeRootStrong.lean` (the property itself, under `TreeRootStrongLogSafe`,
  a hash premise pinned to the values one verification touches).
* **The padding countermodel** — `HashAssumptions.padNotLeaf` is false at the
  extraction pin (`setup` pads with `hashLeaf({0,0,0})`), and the consequence is
  a forged absence proof for a delivered leg, on a real contract run, with no
  hash assumption at all.  Later era-contracts revisions pad with a dedicated
  `IMT_EMPTY_LEAF_HASH`; `Properties.PaddingCollisionRefundsDeliveredLeg` is what that
  constant buys.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier
open Contracts.InteropCommitmentTree Contracts.Protocol

/-! ## Fold correspondence -/

/-- `insert` is `updateLeaf` then `pushNewLeaf` on the leaf-hash list: a
`List.set` at the low index followed by an append — the two operations
`MerkleSpec` analyses as M-A and M-B. -/
def Properties.LeafHashesInsert : Prop :=
  ∀ (hl : LeafHash) (T : Tree) (v : UInt256) (low : ℕ), low < T.leafCount →
    leafHashes hl (insert T v low)
      = (leafHashes hl T).set low (hl { T.leaf low with nextIndex := T.leafCount, nextValue := v })
          ++ [hl ⟨v, (T.leaf low).nextIndex, (T.leaf low).nextValue⟩]

/-- The intermediate root `updateLeaf(low, x)` returns is the update walk from
`low` over the OLD tree's siblings (what the contract reads from storage). -/
def Properties.RootAfterUpdateLeaf : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (low : ℕ) (x : UInt256) (height : ℕ),
    low < T.leafCount → T.leafCount ≤ 2 ^ height →
    rootOf h z0 ((leafHashes hl T).set low x) height
      = walkPure h (honestSibs h z0 (leafHashes hl T) low) 0 height low x

/-- The root after `insert` is the `pushNewLeaf` walk from the frontier index
`leafCount` over the post-`updateLeaf` tree, with the new leaf's hash as the
accumulator — exactly the walk the contract performs. -/
def Properties.RootAfterInsert : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (v : UInt256) (low height : ℕ),
    low < T.leafCount → T.leafCount < 2 ^ height →
    root h z0 hl (insert T v low) height
      = walkPure h
          (honestSibs h z0
            ((leafHashes hl T).set low (hl { T.leaf low with nextIndex := T.leafCount, nextValue := v }))
            T.leafCount)
          0 height T.leafCount (hl ⟨v, (T.leaf low).nextIndex, (T.leaf low).nextValue⟩)

/-! ## Soundness

**Every statement in this section is vacuous.**  Each takes `HashAssumptions h z0 hl`,
which no `h`, `z0`, `hl` satisfies (`Properties.HashAssumptionsUnsatisfiable`, below), so
each follows from that alone and guarantees nothing.  With the premise deleted, each
conclusion is false (`Properties.TreeRootStrongWithoutPremiseFails`).  Each docstring
gives the intended reading and names the non-vacuous forms: the `…OrBreak` restatement
further down (no hash premise), and the `TreeRootStrong…` restatement in
`Properties/TreeRootStrong.lean` (the same conclusion under the pinned premise
`TreeRootStrongLogSafe`). -/

/-- **VACUOUS AS STATED** (`HashAssumptions` is unsatisfiable).  Intended reading: an
accepted path names an occupied index holding the presented leaf, whatever index and path
length the prover chose (the length is the tree's height, the index is below
`leafCount`, and the leaf stored there IS the presented preimage).  Without the premise
this is false at the extraction pin for every hash: the forged absence proof opens the
empty slot 3 (`Properties.TreeRootStrongPinForgeryFailsLogSafe`).  Non-vacuous forms:
`Properties.AcceptedPathPinsLeafOrBreak` and `Properties.TreeRootStrongAcceptedPathPinsLeaf`. -/
def Properties.AcceptedPathPinsLeaf : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (T : Tree) (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf),
      PathAccepts h (root h z0 hl T height) sibs k idx (hl ℓ) →
      k = height ∧ idx < T.leafCount ∧ T.leaf idx = ℓ

/-- **VACUOUS AS STATED** (`HashAssumptions` is unsatisfiable).  Intended reading: a
verified inclusion proof means delivered (the value is a key of the tree's projection).
Without the premise this is false: `Properties.TreeRootBreakEveryCaseFires` gives
accepted inclusion proofs on `setup` for values it does not hold, under the toy hash
pair.  Non-vacuous forms: `Properties.InclusionSoundOrBreak` and
`Properties.TreeRootStrongInclusionSound`. -/
def Properties.InclusionSound : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      InclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k → v ∈ keys (toAbs T)

/-- **VACUOUS AS STATED** (`HashAssumptions` is unsatisfiable).  Intended reading: a
verified non-inclusion proof is a reclaim witness IN the tree (the low leaf is a member of
`toAbs T` with a window straddling `v`).  Without the premise this is false at the
extraction pin for every hash: the forged absence proof for a delivered value is accepted,
and no member of the tree straddles it (`Properties.TreeRootStrongPinForgeryFailsLogSafe`).
Non-vacuous forms: `Properties.NonInclusionSoundOrBreak` and
`Properties.TreeRootStrongNonInclusionSound`. -/
def Properties.NonInclusionSound : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k →
      ∃ W ∈ toAbs T, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- **VACUOUS AS STATED** (`HashAssumptions` is unsatisfiable).  Intended reading: a
delivered value has no verified absence proof against a valid tree's root.  Without the
premise this is false at the extraction pin for every hash
(`Properties.PaddingCollisionRefundsDeliveredLeg`).  Non-vacuous forms:
`Properties.VerifiedAbsenceExcludesDeliveredOrBreak` and
`Properties.TreeRootStrongVerifiedAbsenceExcludesDelivered`. -/
def Properties.VerifiedAbsenceExcludesDelivered : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (T : Tree), Valid T →
    ∀ (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k → v ∉ keys (toAbs T)

/-- **VACUOUS AS STATED, AND NOT THE HEADLINE** (`HashAssumptions` is unsatisfiable).
Intended reading: no value has both an accepted inclusion proof and an accepted
non-inclusion proof against a valid tree's root, whatever leaves, indices, paths and path
lengths the two provers present.  Without the premise this is false at the extraction pin
for every hash (`Properties.ProofsExclusiveOrBreakSatisfiable`).  The headline for the
hash side is `Properties.ProofsExclusiveOrBreak` (no hash premise);
`Properties.TreeRootStrongProofsExclusive` states this conclusion under the pinned premise
`TreeRootStrongLogSafe` on both proofs. -/
def Properties.ProofsExclusive : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (T : Tree), Valid T →
    ∀ (height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      ¬ (InclusionAccepted h hl (root h z0 hl T height) v ℓ₁ i₁ s₁ k₁
          ∧ NonInclusionAccepted h hl (root h z0 hl T height) v ℓ₂ i₂ s₂ k₂)

/-- **VACUOUS AS STATED** (`HashAssumptions` is unsatisfiable).  Intended reading: the
exclusivity of `ProofsExclusive` at every step of every run from `setup`, with validity
inherited from the run.  Without the premise this is false at step 2 of a run from
`setup` for every hash (`Properties.RunRootsExclusiveOrBreakSatisfiable`).  Non-vacuous
forms: `Properties.RunRootsExclusiveOrBreak` and `Properties.TreeRootStrongRunRootsExclusive`;
at the run's own published height, `Properties.RunRootsExclusiveOrBreakAtOwnHeight` and
`Properties.TreeRootStrongRunRootsAtOwnHeight`. -/
def Properties.RunRootsExclusive : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (R : ℕ → Tree), Run R → R 0 = setup →
    ∀ (n height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      ¬ (InclusionAccepted h hl (root h z0 hl (R n) height) v ℓ₁ i₁ s₁ k₁
          ∧ NonInclusionAccepted h hl (root h z0 hl (R n) height) v ℓ₂ i₂ s₂ k₂)

/-- **VACUOUS AS STATED; AS A MULTI-CHAIN HOOK IT CARRIES NOTHING** (`HashAssumptions` is
unsatisfiable).  Intended reading: a non-inclusion proof verified against chain `c`'s root
is an `AbsenceWitnessAt` for `c`, so that the `Protocol` results would apply to
root-verified proofs.  Without the premise this is false at the extraction pin for every
hash (`Properties.TreeRootStrongPinForgeryFailsLogSafe`).  Downstream users should consume
`Properties.VerifiedAbsenceIsWitnessOrBreak` (no hash premise) or
`Properties.TreeRootStrongVerifiedAbsenceIsWitness` (under `TreeRootStrongLogSafe`). -/
def Properties.VerifiedAbsenceIsWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (T : Chain → Tree) (c : Chain) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ)
      (sibs : ℕ → UInt256) (k : ℕ),
      NonInclusionAccepted h hl (root h z0 hl (T c) height) v ℓ idx sibs k →
      AbsenceWitnessAt (ofChains T) c v

/-! ## Completeness

Soundness alone would be satisfied by a verifier that rejects everything.  These
need the capacity invariant `leafCount ≤ 2^height`, which `pushNewLeaf`
maintains by growing the height; soundness did not. -/

/-- Every occupied leaf has an accepted inclusion proof for its value: the
honest path (`FullMerkle.merklePath`) at the tree's height. -/
def Properties.InclusionComplete : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ), T.leafCount ≤ 2 ^ height →
    ∀ i : ℕ, i < T.leafCount →
      InclusionAccepted h hl (root h z0 hl T height) (T.leaf i).value (T.leaf i) i
        (honestSibs h z0 (leafHashes hl T) i) height

/-- Every absent nonzero value has an accepted non-inclusion proof: the leaf with
the maximal key below it is a valid low leaf, and its honest path verifies. -/
def Properties.NonInclusionComplete : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree), Valid T →
    ∀ (height : ℕ), T.leafCount ≤ 2 ^ height → ∀ (v : UInt256), v ≠ 0 → v ∉ keys (toAbs T) →
      ∃ (ℓ : Leaf) (idx : ℕ),
        NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx
          (honestSibs h z0 (leafHashes hl T) idx) height

/-! ## The padding countermodel -/

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


/-! ## The hash-assumption bundle is unsatisfiable

Added during the consolidation onto the per-contract layout.  `nodeInj` asks a map
`UInt256 → UInt256 → UInt256` to be injective on all `2^512` pairs, and `leafInj`
asks a map from three-field leaves into `UInt256` to be injective; neither can
hold by counting.  So every statement in this package of the form
`HashAssumptions h z0 hl → …` is vacuously true and is NOT a security guarantee,
and a countermodel stated under that premise exhibits nothing.  The padding
countermodels above do not take the premise and are unaffected.  For this file's seven
soundness statements the repair is in two forms: the `…OrBreak` section below ("the
property holds, or a `TreeRootBreak` is located on the submitted path"), and
`Properties/TreeRootStrong.lean` ("the property holds" under `TreeRootStrongLogSafe`, each
field of the bundle restricted to the values one verification touches, a premise that a
hash can meet).  Elsewhere the repair is the collision form of `LastLeafOrBreak`
(`AtomicInteropProof/Properties/LastLeaf.lean`; its accepted-path variant still needs the
repair) and `Contracts.Refund.Properties.CrossFlowRefundYieldsCollision`: conclude
"the property holds, or a concrete collision among the compared values exists". -/
def Properties.HashAssumptionsUnsatisfiable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), ¬ HashAssumptions h z0 hl


/-! ## Soundness without hash premises: the property, or a located break

Each of these restates a soundness result above with `HashAssumptions` removed and
`∨ TreeRootBreak …` added to the conclusion, the break naming the submitted path(s).
`Properties.HonestProofNoBreak` shows `TreeRootBreak` is false on every honest proof,
and `Properties.ProofsExclusiveOrBreakSatisfiable` / `RunRootsExclusiveOrBreakSatisfiable`
exhibit instances of the premises (both proofs accepted on a valid tree, the padding
countermodel). -/

/-- An accepted path names an occupied index holding the presented leaf at the
tree's height, or a located `TreeRootBreak` on that path. -/
def Properties.AcceptedPathPinsLeafOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ) (sibs : ℕ → UInt256)
    (k idx : ℕ) (ℓ : Leaf),
    PathAccepts h (root h z0 hl T height) sibs k idx (hl ℓ) →
      (k = height ∧ idx < T.leafCount ∧ T.leaf idx = ℓ)
        ∨ TreeRootBreak h z0 hl T height sibs k idx ℓ

/-- A verified inclusion proof means delivered, or a located break on its path. -/
def Properties.InclusionSoundOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf)
    (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    InclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k →
      v ∈ keys (toAbs T) ∨ TreeRootBreak h z0 hl T height sibs k idx ℓ

/-- A verified non-inclusion proof is a reclaim witness in the tree, or a located
break on the low leaf's path. -/
def Properties.NonInclusionSoundOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf)
    (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k →
      (∃ W ∈ toAbs T, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
        ∨ TreeRootBreak h z0 hl T height sibs k idx ℓ

/-- A delivered value has no verified absence proof against a valid tree's root,
unless that proof's path carries a located break. -/
def Properties.VerifiedAbsenceExcludesDeliveredOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree), Valid T →
    ∀ (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k →
        v ∉ keys (toAbs T) ∨ TreeRootBreak h z0 hl T height sibs k idx ℓ

/-- **The headline for the hash side, without hash premises.**  If a value has both
an accepted inclusion proof and an accepted non-inclusion proof against a valid
tree's root, then one of the two submitted paths carries a located `TreeRootBreak`.
(The premises are satisfiable: `Properties.ProofsExclusiveOrBreakSatisfiable`.) -/
def Properties.ProofsExclusiveOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree), Valid T →
    ∀ (height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      InclusionAccepted h hl (root h z0 hl T height) v ℓ₁ i₁ s₁ k₁ →
      NonInclusionAccepted h hl (root h z0 hl T height) v ℓ₂ i₂ s₂ k₂ →
        TreeRootBreak h z0 hl T height s₁ k₁ i₁ ℓ₁ ∨ TreeRootBreak h z0 hl T height s₂ k₂ i₂ ℓ₂

/-- The same at every step of every run from `setup`. -/
def Properties.RunRootsExclusiveOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → Tree), Run R → R 0 = setup →
    ∀ (n height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      InclusionAccepted h hl (root h z0 hl (R n) height) v ℓ₁ i₁ s₁ k₁ →
      NonInclusionAccepted h hl (root h z0 hl (R n) height) v ℓ₂ i₂ s₂ k₂ →
        TreeRootBreak h z0 hl (R n) height s₁ k₁ i₁ ℓ₁
          ∨ TreeRootBreak h z0 hl (R n) height s₂ k₂ i₂ ℓ₂

/-- The multi-chain hook: a non-inclusion proof verified against chain `c`'s root is
an `AbsenceWitnessAt` for `c`, or its path carries a located break. -/
def Properties.VerifiedAbsenceIsWitnessOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Chain → Tree) (c : Chain) (height : ℕ)
    (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    NonInclusionAccepted h hl (root h z0 hl (T c) height) v ℓ idx sibs k →
      AbsenceWitnessAt (ofChains T) c v ∨ TreeRootBreak h z0 hl (T c) height sibs k idx ℓ

/-! ### Anti-vacuity -/

/-- **NON-TRIVIALITY OF `TreeRootBreak`.**  On the honest proof for any occupied
index (the tree's own siblings, at the tree's height, presenting the stored leaf) no
break is located, for every node hash, leaf hash and padding constant. -/
def Properties.HonestProofNoBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height i : ℕ), i < T.leafCount →
    ¬ TreeRootBreak h z0 hl T height (honestSibs h z0 (leafHashes hl T) i) height i (T.leaf i)

/-- **THE PREMISES OF `ProofsExclusiveOrBreak` ARE SATISFIABLE.**  For every node and
leaf hash and every `0 < a < b`, on the valid run `threeLeafTree a b` at height 2
with the extraction-pin padding `hl ⟨0,0,0⟩`, `a` has an accepted inclusion proof
(the honest one for leaf 1) AND an accepted non-inclusion proof (the padding
forgery at slot 3).  The same instance satisfies the premises of
`VerifiedAbsenceExcludesDeliveredOrBreak`, `InclusionSoundOrBreak` and
`NonInclusionSoundOrBreak`. -/
def Properties.ProofsExclusiveOrBreakSatisfiable : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    Valid (threeLeafTree a b)
      ∧ InclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2) a
          ((threeLeafTree a b).leaf 1) 1
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 1) 2
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

/-- **THE PREMISES OF `RunRootsExclusiveOrBreak` ARE SATISFIABLE.**  The run
`setup, insert a, insert b`, constant afterwards, is a `Run` from `setup`, and at
step 2 the two proofs of `Properties.ProofsExclusiveOrBreakSatisfiable` are both
accepted. -/
def Properties.RunRootsExclusiveOrBreakSatisfiable : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    ∃ R : ℕ → Tree, Run R ∧ R 0 = setup ∧ R 2 = threeLeafTree a b
      ∧ InclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (R 2) 2) a ((R 2).leaf 1) 1
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (R 2)) 1) 2
      ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (R 2) 2) a ⟨0, 0, 0⟩ 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (R 2)) 3) 2


/-! ## Every case of the break fires, and is attributed alone

Before this section only `paddingHit` had an instance on which it fires
(`Properties.PaddingCountermodelLocatesPaddingHit`).  The properties below show each
of the other three cases is reachable — not dead code — and is the ONLY case the
located break can be: on the single-leaf `setup` tree at height 1 (valid, within
capacity), an inclusion proof for a value the tree does not hold is accepted, and
`TreeRootBreakExactly` names its case.  Each is stated for every node hash, leaf
hash and padding constant meeting a hypothesis that pins the collision to the
instance (the sentinel leaf `⟨0,0,0⟩`, the tree's top pair, or the root), and
`Properties.ForgedInclusionPremisesSatisfiable` exhibits all of those hypotheses on
the toy hash pair. -/

/-- **THE TWO VIEWS OF THE BREAK AGREE.**  `TreeRootBreak` holds iff the premise of
one of its four constructors does. -/
def Properties.TreeRootBreakIffSomeCase : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ) (sibs : ℕ → UInt256)
    (k idx : ℕ) (ℓ : Leaf),
    TreeRootBreak h z0 hl T height sibs k idx ℓ
      ↔ ∃ c, TreeRootBreakAt h z0 hl T height sibs k idx ℓ c

/-- **`pathCollision` FIRES, ALONE.**  If the node hash collides between the forged
pair `(hl ℓ, s)` and the `setup` tree's top pair `(hl ⟨0,0,0⟩, z0)` — a genuine
collision, since the leaf hashes differ — then the length-1 path with sibling `s`,
presenting `ℓ` at index 0, is accepted against `setup`'s root at height 1 as an
inclusion proof for `ℓ.value`, which the tree does not hold; and the located break
is exactly `pathCollision`. -/
def Properties.PathCollisionForgesInclusion : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (ℓ : Leaf) (s : UInt256),
    ℓ.value ≠ 0 → hl ℓ ≠ hl ⟨0, 0, 0⟩ → h (hl ℓ) s = h (hl ⟨0, 0, 0⟩) z0 →
      Valid setup ∧ setup.leafCount ≤ 2 ^ 1
        ∧ InclusionAccepted h hl (root h z0 hl setup 1) ℓ.value ℓ 0 (fun _ => s) 1
        ∧ ℓ.value ∉ keys (toAbs setup)
        ∧ TreeRootBreakExactly h z0 hl setup 1 (fun _ => s) 1 0 ℓ .pathCollision

/-- **`leafCollision` FIRES, ALONE.**  If the leaf hash collides between a leaf `ℓ`
carrying a nonzero value and the sentinel `⟨0,0,0⟩` stored at index 0, then the
HONEST path for index 0 at the right height, presenting `ℓ`, is accepted as an
inclusion proof for `ℓ.value`, which the tree does not hold; and the located break is
exactly `leafCollision`. -/
def Properties.LeafCollisionForgesInclusion : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (ℓ : Leaf),
    ℓ.value ≠ 0 → hl ℓ = hl ⟨0, 0, 0⟩ →
      Valid setup ∧ setup.leafCount ≤ 2 ^ 1
        ∧ InclusionAccepted h hl (root h z0 hl setup 1) ℓ.value ℓ 0
            (honestSibs h z0 (leafHashes hl setup) 0) 1
        ∧ ℓ.value ∉ keys (toAbs setup)
        ∧ TreeRootBreakExactly h z0 hl setup 1 (honestSibs h z0 (leafHashes hl setup) 0) 1 0 ℓ
            .leafCollision

/-- **`wrongLength` FIRES, ALONE.**  If a leaf `ℓ` carrying a nonzero value hashes to
`setup`'s root at height 1 (and not to the sentinel's leaf hash), then the EMPTY path
at index 0, presenting `ℓ`, is accepted as an inclusion proof for `ℓ.value` — the
`ZeroLengthPathAcceptsRoot` shape — which the tree does not hold; and the located
break is exactly `wrongLength`. -/
def Properties.WrongLengthForgesInclusion : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (ℓ : Leaf) (sibs : ℕ → UInt256),
    ℓ.value ≠ 0 → hl ℓ ≠ hl ⟨0, 0, 0⟩ → hl ℓ = root h z0 hl setup 1 →
      Valid setup ∧ setup.leafCount ≤ 2 ^ 1
        ∧ InclusionAccepted h hl (root h z0 hl setup 1) ℓ.value ℓ 0 sibs 0
        ∧ ℓ.value ∉ keys (toAbs setup)
        ∧ TreeRootBreakExactly h z0 hl setup 1 sibs 0 0 ℓ .wrongLength

/-- **`paddingHit` FIRES, ALONE, ON AN INCLUSION PROOF.**  If a leaf `ℓ` carrying a
nonzero value hashes to the padding constant, the honest path for the EMPTY slot 1
of `setup` at height 1, presenting `ℓ`, is accepted as an inclusion proof for
`ℓ.value`, which the tree does not hold; and the located break is exactly
`paddingHit`.  (For an arbitrary padding constant; at the extraction pin, where
`z0 = hl ⟨0,0,0⟩`, its premise is a leaf-hash collision with the sentinel, so the
padding bug itself adds no inclusion-forging power.) -/
def Properties.PaddingHitForgesInclusion : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (ℓ : Leaf),
    ℓ.value ≠ 0 → hl ℓ = z0 →
      Valid setup ∧ setup.leafCount ≤ 2 ^ 1
        ∧ InclusionAccepted h hl (root h z0 hl setup 1) ℓ.value ℓ 1
            (honestSibs h z0 (leafHashes hl setup) 1) 1
        ∧ ℓ.value ∉ keys (toAbs setup)
        ∧ TreeRootBreakExactly h z0 hl setup 1 (honestSibs h z0 (leafHashes hl setup) 1) 1 1 ℓ
            .paddingHit

/-- **THE PADDING COUNTERMODEL'S BREAK IS EXACTLY `paddingHit`.**  Sharpens
`Properties.PaddingCountermodelLocatesPaddingHit`: on the forged absence proof at slot 3
of `threeLeafTree a b`, no case other than `paddingHit` holds. -/
def Properties.PaddingCountermodelExactlyPaddingHit : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256),
    TreeRootBreakExactly h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2
      (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2 3 ⟨0, 0, 0⟩ .paddingHit

/-- **THE COLLISION HYPOTHESES ABOVE ARE SATISFIABLE.**  With the toy node hash
(addition), the toy leaf hash (`value - nextValue`) and padding constant `1`:
`(hl ⟨1,0,0⟩, 0)` collides with the top pair `(hl ⟨0,0,0⟩, 1)` (`pathCollision`);
`⟨1,0,1⟩` collides with the sentinel (`leafCollision`); `⟨1,0,0⟩` hashes to `setup`'s
root at height 1 (`wrongLength`) and to the padding constant (`paddingHit`). -/
def Properties.ForgedInclusionPremisesSatisfiable : Prop :=
  ((⟨1, 0, 0⟩ : Leaf).value ≠ 0 ∧ toyLeafHash ⟨1, 0, 0⟩ ≠ toyLeafHash ⟨0, 0, 0⟩
      ∧ toyNodeHash (toyLeafHash ⟨1, 0, 0⟩) 0 = toyNodeHash (toyLeafHash ⟨0, 0, 0⟩) 1)
    ∧ ((⟨1, 0, 1⟩ : Leaf).value ≠ 0 ∧ toyLeafHash ⟨1, 0, 1⟩ = toyLeafHash ⟨0, 0, 0⟩)
    ∧ ((⟨1, 0, 0⟩ : Leaf).value ≠ 0 ∧ toyLeafHash ⟨1, 0, 0⟩ ≠ toyLeafHash ⟨0, 0, 0⟩
      ∧ toyLeafHash ⟨1, 0, 0⟩ = root toyNodeHash 1 toyLeafHash setup 1)
    ∧ ((⟨1, 0, 0⟩ : Leaf).value ≠ 0 ∧ toyLeafHash ⟨1, 0, 0⟩ = 1)

/-- **EVERY CASE OF THE BREAK FIRES, IN ONE HASH CONFIGURATION.**  With the toy hash
pair and padding constant `1`, for each of the four cases `c` there is a proof
(siblings, length, index, presented leaf) that `verifyInclusion` accepts against the
valid `setup` tree's root at height 1 for a value that tree does not hold, and whose
located break is exactly `c`.  So no case of `TreeRootBreak` is dead code, and the
case analysis attributes each forgery to the right one. -/
def Properties.TreeRootBreakEveryCaseFires : Prop :=
  ∀ c : TreeRootBreakCase, ∃ (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf),
    Valid setup ∧ setup.leafCount ≤ 2 ^ 1
      ∧ InclusionAccepted toyNodeHash toyLeafHash (root toyNodeHash 1 toyLeafHash setup 1)
          ℓ.value ℓ idx sibs k
      ∧ ℓ.value ∉ keys (toAbs setup)
      ∧ ¬ (k = 1 ∧ idx < setup.leafCount ∧ setup.leaf idx = ℓ)
      ∧ TreeRootBreakExactly toyNodeHash 1 toyLeafHash setup 1 sibs k idx ℓ c

/-! ## Every sub-case of `wrongLength` fires, and is attributed alone

`Properties.WrongLengthForgesInclusion` exhibits `wrongLength` firing on a too-short
path (length 0 against height 1), whose `HeightBreak` is `shortInteriorLeaf`.  The
other three `HeightBreak` constructors — `shortCollision`, and on the too-long side
`longEntryIsNode` and `longCollision` — had no instance inside `TreeRootBreak` on
which they fire.  The properties below give each one: on the single-leaf `setup`
tree at a height within capacity, an inclusion proof for a value the tree does not
hold is accepted with a path of the wrong length, the located `TreeRootBreak` is
exactly `wrongLength` (`TreeRootBreakExactly`), and its `HeightBreak` is exactly the
named sub-case (`HeightBreakExactly`).  Each is stated for every node hash, leaf hash
and padding constant meeting a hypothesis on values fixed by the instance (the
sentinel's leaf hash, the tree's own pairs and root), and
`Properties.WrongLengthSubcasePremisesSatisfiable` exhibits all of those hypotheses on
the toy hash pair. -/

/-- **THE TWO VIEWS OF `HeightBreak` AGREE.**  `HeightBreak` holds iff the premise of
one of its four constructors does. -/
def Properties.HeightBreakIffSomeCase : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k height j : ℕ)
    (x : UInt256),
    HeightBreak h z0 L sibs k height j x ↔ ∃ c, HeightBreakAt h z0 L sibs k height j x c

/-- **THE EXISTING `wrongLength` WITNESS IS EXACTLY `shortInteriorLeaf`.**  Sharpens
`Properties.WrongLengthForgesInclusion`: if `hl ℓ` is `setup`'s root at height 1, then on
the empty path at index 0 presenting `ℓ` (any siblings) the `HeightBreak` is exactly
`shortInteriorLeaf`. -/
def Properties.WrongLengthShortIsInteriorLeaf : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (ℓ : Leaf) (sibs : ℕ → UInt256),
    hl ℓ = root h z0 hl setup 1 →
      HeightBreakExactly h z0 (leafHashes hl setup) sibs 0 1 0 (hl ℓ) .shortInteriorLeaf

/-- **`wrongLength` FIRES AS `shortCollision`, ALONE.**  On `setup` at height 2 (root
`h (h (hl ⟨0,0,0⟩) z0) (h z0 z0)`): if `hl ℓ` is neither the sentinel's leaf hash nor
the level-1 node `h (hl ⟨0,0,0⟩) z0`, and the node hash collides between the forged
pair `(hl ℓ, s)` and the tree's level-1 pair `(h (hl ⟨0,0,0⟩) z0, h z0 z0)`, then the
length-1 path with sibling `s`, presenting `ℓ` at index 0, is accepted as an inclusion
proof for `ℓ.value`, which the tree does not hold; the located break is exactly
`wrongLength`, and its `HeightBreak` exactly `shortCollision`. -/
def Properties.ShortCollisionForgesInclusion : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (ℓ : Leaf) (s : UInt256),
    ℓ.value ≠ 0 → hl ℓ ≠ hl ⟨0, 0, 0⟩ → hl ℓ ≠ h (hl ⟨0, 0, 0⟩) z0 →
    h (hl ℓ) s = h (h (hl ⟨0, 0, 0⟩) z0) (h z0 z0) →
      Valid setup ∧ setup.leafCount ≤ 2 ^ 2
        ∧ InclusionAccepted h hl (root h z0 hl setup 2) ℓ.value ℓ 0 (fun _ => s) 1
        ∧ ℓ.value ∉ keys (toAbs setup)
        ∧ TreeRootBreakExactly h z0 hl setup 2 (fun _ => s) 1 0 ℓ .wrongLength
        ∧ HeightBreakExactly h z0 (leafHashes hl setup) (fun _ => s) 1 2 0 (hl ℓ) .shortCollision

/-- **`wrongLength` FIRES AS `longEntryIsNode`, ALONE.**  On `setup` at height 0 (root
`hl ⟨0,0,0⟩`): if `hl ℓ` is not the sentinel's leaf hash and the node hash maps the
pair `(hl ℓ, s)` to it, then the length-1 path with sibling `s`, presenting `ℓ` at
index 0, is accepted as an inclusion proof for `ℓ.value`, which the tree does not
hold; the located break is exactly `wrongLength`, and its `HeightBreak` exactly
`longEntryIsNode`. -/
def Properties.LongEntryIsNodeForgesInclusion : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (ℓ : Leaf) (s : UInt256),
    ℓ.value ≠ 0 → hl ℓ ≠ hl ⟨0, 0, 0⟩ → h (hl ℓ) s = hl ⟨0, 0, 0⟩ →
      Valid setup ∧ setup.leafCount ≤ 2 ^ 0
        ∧ InclusionAccepted h hl (root h z0 hl setup 0) ℓ.value ℓ 0 (fun _ => s) 1
        ∧ ℓ.value ∉ keys (toAbs setup)
        ∧ TreeRootBreakExactly h z0 hl setup 0 (fun _ => s) 1 0 ℓ .wrongLength
        ∧ HeightBreakExactly h z0 (leafHashes hl setup) (fun _ => s) 1 0 0 (hl ℓ)
            .longEntryIsNode

/-- **`wrongLength` FIRES AS `longCollision`, ALONE.**  On `setup` at height 1 (root
`h (hl ⟨0,0,0⟩) z0`): if `hl ℓ` is not the sentinel's leaf hash, the verifier's first
node `h (hl ℓ) s₀` is not the sentinel's leaf hash either, and the node hash collides
between the pair `(h (hl ℓ) s₀, s₁)` and the tree's top pair `(hl ⟨0,0,0⟩, z0)`, then
the length-2 path with siblings `s₀, s₁`, presenting `ℓ` at index 0, is accepted as an
inclusion proof for `ℓ.value`, which the tree does not hold; the located break is
exactly `wrongLength`, and its `HeightBreak` exactly `longCollision`. -/
def Properties.LongCollisionForgesInclusion : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (ℓ : Leaf) (s₀ s₁ : UInt256),
    ℓ.value ≠ 0 → hl ℓ ≠ hl ⟨0, 0, 0⟩ → h (hl ℓ) s₀ ≠ hl ⟨0, 0, 0⟩ →
    h (h (hl ℓ) s₀) s₁ = h (hl ⟨0, 0, 0⟩) z0 →
      Valid setup ∧ setup.leafCount ≤ 2 ^ 1
        ∧ InclusionAccepted h hl (root h z0 hl setup 1) ℓ.value ℓ 0
            (fun l => if l = 0 then s₀ else s₁) 2
        ∧ ℓ.value ∉ keys (toAbs setup)
        ∧ TreeRootBreakExactly h z0 hl setup 1 (fun l => if l = 0 then s₀ else s₁) 2 0 ℓ
            .wrongLength
        ∧ HeightBreakExactly h z0 (leafHashes hl setup) (fun l => if l = 0 then s₀ else s₁) 2 1 0
            (hl ℓ) .longCollision

/-- **THE HYPOTHESES ABOVE ARE SATISFIABLE.**  With the toy node hash (addition), the
toy leaf hash (`value - nextValue`) and padding constant `1`, where the sentinel's leaf
hash is `0`: `⟨2,0,0⟩` with `s = 1` meets the `shortCollision` hypotheses
(`2 + 1 = (0 + 1) + (1 + 1)`); `⟨1,0,0⟩` with `s = -1` meets the `longEntryIsNode`
ones (`1 + (-1) = 0`); `⟨1,0,0⟩` with `s₀ = s₁ = 0` meets the `longCollision` ones
(`(1 + 0) + 0 = 0 + 1`, and `1 + 0 ≠ 0`). -/
def Properties.WrongLengthSubcasePremisesSatisfiable : Prop :=
  ((⟨2, 0, 0⟩ : Leaf).value ≠ 0 ∧ toyLeafHash ⟨2, 0, 0⟩ ≠ toyLeafHash ⟨0, 0, 0⟩
      ∧ toyLeafHash ⟨2, 0, 0⟩ ≠ toyNodeHash (toyLeafHash ⟨0, 0, 0⟩) 1
      ∧ toyNodeHash (toyLeafHash ⟨2, 0, 0⟩) 1
          = toyNodeHash (toyNodeHash (toyLeafHash ⟨0, 0, 0⟩) 1) (toyNodeHash 1 1))
    ∧ ((⟨1, 0, 0⟩ : Leaf).value ≠ 0 ∧ toyLeafHash ⟨1, 0, 0⟩ ≠ toyLeafHash ⟨0, 0, 0⟩
      ∧ toyNodeHash (toyLeafHash ⟨1, 0, 0⟩) (-1) = toyLeafHash ⟨0, 0, 0⟩)
    ∧ ((⟨1, 0, 0⟩ : Leaf).value ≠ 0 ∧ toyLeafHash ⟨1, 0, 0⟩ ≠ toyLeafHash ⟨0, 0, 0⟩
      ∧ toyNodeHash (toyLeafHash ⟨1, 0, 0⟩) 0 ≠ toyLeafHash ⟨0, 0, 0⟩
      ∧ toyNodeHash (toyNodeHash (toyLeafHash ⟨1, 0, 0⟩) 0) 0
          = toyNodeHash (toyLeafHash ⟨0, 0, 0⟩) 1)

/-- **EVERY SUB-CASE OF `wrongLength` FIRES, IN ONE HASH CONFIGURATION.**  With the toy
hash pair and padding constant `1`, for each of the four `HeightBreak` cases `c` there
is a height (within `setup`'s capacity) and a proof (siblings, a length different from
that height, index, presented leaf) that `verifyInclusion` accepts against the valid
`setup` tree's root at that height for a value the tree does not hold, whose located
`TreeRootBreak` is exactly `wrongLength` and whose `HeightBreak` is exactly `c`. -/
def Properties.WrongLengthEverySubcaseFires : Prop :=
  ∀ c : HeightBreakCase, ∃ (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf),
    Valid setup ∧ setup.leafCount ≤ 2 ^ height
      ∧ InclusionAccepted toyNodeHash toyLeafHash (root toyNodeHash 1 toyLeafHash setup height)
          ℓ.value ℓ idx sibs k
      ∧ ℓ.value ∉ keys (toAbs setup)
      ∧ k ≠ height
      ∧ TreeRootBreakExactly toyNodeHash 1 toyLeafHash setup height sibs k idx ℓ .wrongLength
      ∧ HeightBreakExactly toyNodeHash 1 (leafHashes toyLeafHash setup) sibs k height idx
          (toyLeafHash ℓ) c

end Contracts.InteropCommitmentTree
