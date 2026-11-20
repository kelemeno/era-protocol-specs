import EraSpec.Contracts.Merkle.Specs.DomainSeparation
import EraSpec.Core.Headline

/-!
# History properties: Merkle domain separation at the interop pin's IMT padding (`c67894b9`)

**The record of an older commit, not a claim about `b17415d20`.** At the interop pin `c67894b9`,
`IndexedMerkleTree.setup` padded the tree with `hashLeaf({0,0,0})`, the hash of a leaf preimage
(96 zero bytes, `pinPaddingPre`). That is the H2 padding finding; its IMT-level record is
`EraSpec.Contracts.IndexedMerkleTree.History`. At `b17415d20` the padding is
`IMT_EMPTY_LEAF_HASH`, a 34-byte preimage (`imtEmptyLeafPre`), and the current statements are
`MerkleSpec.DomainSeparation.Properties.TreeRootBreakIsKeccakCollision`,
`ProofsExclusiveOrKeccakBreak`, `InclusionSoundOrKeccakBreak` and `NonInclusionSoundOrKeccakBreak`
(any padding preimage that is neither 64 nor 96 bytes long).

Every statement here instantiates the IMT padding with `imtPadding keccak = hashLeaf({0,0,0})` or
names `pinPaddingPre`. They were `MerkleSpec.DomainSeparation.Properties.<name>` before round-9
consolidation; `handoff/2026-11-19/renames/merkle-libs.json` maps the names. Definitions:
`../../Specs/DomainSeparation.lean`. Proofs: `../Proofs/DomainSeparationPinned.lean`.
-/

namespace MerkleSpec.DomainSeparation.History

open AttackVectors.BundleHashEncoding (HashCollision toBytesBE word)
open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf MerkleSpec.Pinned MerkleSpec.DomainSeparation
open Contracts.InteropCommitmentTree (Leaf Tree LeafHash leafHashes TreeRootBreak InclusionAccepted
  NonInclusionAccepted Valid root setup threeLeafTree toAbs)

/-- **THE ZERO LEAF'S PREIMAGE IS THE EMPTY ENTRY'S.** `abi.encode(0, 0, 0)` is 96 zero bytes, so
the pin's IMT padding `hashLeaf({0, 0, 0})` (`IndexedMerkleTree.sol:47-48`) has the same keccak
input as `new bytes(96)`. -/
def Properties.PinPaddingIsEmptyPre : Prop :=
  pinPaddingPre = emptyPre

/-- **THE FIELDS OF `TreeRoot.HashAssumptions`, INSTANTIATED WITH KECCAK AT THE PIN.** With node hash
`efficientHash keccak`, leaf hash `hashLeaf keccak` and padding `imtPadding keccak = hashLeaf({0,0,0})`:

* `nodeInj` and `leafInj` hold up to a collision on the two named preimages (for `leafInj`, of
  bounded leaves);
* `leafNotNode` and `padNotNode` hold up to a collision on the named 96-byte and 64-byte preimages;
* `padNotLeaf` is refuted EXACTLY at `⟨0, 0, 0⟩`: a bounded leaf hashes to the padding iff it is
  the zero leaf, or its preimage collides with the 96 zero bytes. (The failure at `⟨0, 0, 0⟩` is
  the known `History.PaddingCollisionRefundsDeliveredLeg`.) -/
def Properties.HashAssumptionsFieldsUpToCollision : Prop :=
  ∀ keccak : Keccak,
    (∀ a b c d : UInt256, efficientHash keccak a b = efficientHash keccak c d →
        (a = c ∧ b = d) ∨ HashCollision keccak (nodePre a b) (nodePre c d))
    ∧ (∀ ℓ ℓ' : Leaf, LeafBounded ℓ → LeafBounded ℓ' → hashLeaf keccak ℓ = hashLeaf keccak ℓ' →
        ℓ = ℓ' ∨ HashCollision keccak (imtPre ℓ) (imtPre ℓ'))
    ∧ (∀ (ℓ : Leaf) (a b : UInt256), hashLeaf keccak ℓ = efficientHash keccak a b →
        HashCollision keccak (imtPre ℓ) (nodePre a b))
    ∧ (∀ ℓ : Leaf, LeafBounded ℓ →
        (hashLeaf keccak ℓ = imtPadding keccak ↔ ℓ = ⟨0, 0, 0⟩ ∨ HashCollision keccak (imtPre ℓ) emptyPre))
    ∧ (∀ a b : UInt256, imtPadding keccak = efficientHash keccak a b →
        HashCollision keccak emptyPre (nodePre a b))

/-- **EACH FIELD'S HASH-EQUALITY PREMISE IS MET BY ONE PLANTED COLLISION, AND THE COLLISION DISJUNCTS
ARE NOT FORCED.**

* For every keccak model `κ`, `κ` changed at one string meets the hash equality of each field, on
  instances where the field's non-collision disjunct, if it has one, is false: two distinct node
  pairs, two distinct bounded leaves, a leaf and a node pair, a bounded leaf other than `⟨0, 0, 0⟩`
  and the padding, the padding and a node pair. In each case the collision named is the planted
  one.
* Under the length stand-in, `leafNotNode` and `padNotNode` hold outright: no leaf and not the
  padding hashes to a node (96 versus 64).
* For every keccak, the zero leaf hashes to the padding with no collision: the refutation of
  `padNotLeaf` needs no cryptographic work.
* Under the first-word stand-in, a bounded leaf with nonzero value neither hashes to the padding
  nor collides with the 96 zero bytes. -/
def Properties.HashAssumptionsFieldsWitness : Prop :=
  (∀ (κ : Keccak) (a b c d : UInt256), (a, b) ≠ (c, d) →
      let keccak := plantKeccak κ (nodePre a b) (nodePre c d)
      efficientHash keccak a b = efficientHash keccak c d
        ∧ HashCollision keccak (nodePre a b) (nodePre c d))
    ∧ (∀ (κ : Keccak) (ℓ ℓ' : Leaf), LeafBounded ℓ → LeafBounded ℓ' → ℓ ≠ ℓ' →
        let keccak := plantKeccak κ (imtPre ℓ) (imtPre ℓ')
        hashLeaf keccak ℓ = hashLeaf keccak ℓ' ∧ HashCollision keccak (imtPre ℓ) (imtPre ℓ'))
    ∧ (∀ (κ : Keccak) (ℓ : Leaf) (a b : UInt256),
        let keccak := plantKeccak κ (imtPre ℓ) (nodePre a b)
        hashLeaf keccak ℓ = efficientHash keccak a b
          ∧ HashCollision keccak (imtPre ℓ) (nodePre a b))
    ∧ (∀ (κ : Keccak) (ℓ : Leaf), LeafBounded ℓ → ℓ ≠ ⟨0, 0, 0⟩ →
        let keccak := plantKeccak κ (imtPre ℓ) emptyPre
        hashLeaf keccak ℓ = imtPadding keccak ∧ HashCollision keccak (imtPre ℓ) emptyPre)
    ∧ (∀ (κ : Keccak) (a b : UInt256),
        let keccak := plantKeccak κ emptyPre (nodePre a b)
        imtPadding keccak = efficientHash keccak a b
          ∧ HashCollision keccak emptyPre (nodePre a b))
    ∧ (∀ (ℓ : Leaf) (a b : UInt256), hashLeaf lengthKeccak ℓ ≠ efficientHash lengthKeccak a b
        ∧ imtPadding lengthKeccak ≠ efficientHash lengthKeccak a b)
    ∧ (∀ keccak : Keccak, hashLeaf keccak ⟨0, 0, 0⟩ = imtPadding keccak
        ∧ ¬ HashCollision keccak (imtPre ⟨0, 0, 0⟩) emptyPre)
    ∧ (∀ ℓ : Leaf, LeafBounded ℓ → ℓ.value ≠ 0 →
        hashLeaf firstWordKeccak ℓ ≠ imtPadding firstWordKeccak
          ∧ ¬ HashCollision firstWordKeccak (imtPre ℓ) emptyPre)

/-- **AT THE PIN: A KECCAK COLLISION ON NAMED BYTES, OR THE ZERO LEAF AT AN EMPTY SLOT.** With the
pin's padding `hashLeaf({0,0,0})`, the only located break of the root check that is not a keccak
collision is the zero leaf presented at an unoccupied index: the forged-absence bug. -/
def Properties.TreeRootBreakIsKeccakCollisionAtPin : Prop :=
  ∀ (keccak : Keccak) (T : Tree) (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf),
    TreeBounded T → LeafBounded ℓ →
    TreeRootBreak (efficientHash keccak) (imtPadding keccak) (hashLeaf keccak) T height sibs k idx ℓ →
      (T.leafCount ≤ idx ∧ ℓ = ⟨0, 0, 0⟩) ∨ ImtKeccakBreak keccak pinPaddingPre T height sibs k idx ℓ

/-- **HEADLINE (pin): IMT PROOFS ARE EXCLUSIVE, OR KECCAK COLLIDES ON NAMED BYTES, OR THE ABSENCE PROOF
IS THE PADDING FORGERY.** `ProofsExclusiveOrBreak` with the abstract hashes instantiated by keccak as
at the pin. If a value has an accepted inclusion proof and an accepted non-inclusion proof against a
valid tree's root, then one of:

* the non-inclusion proof presents the zero leaf `⟨0, 0, 0⟩` at an unoccupied index (the
  forged-absence bug, `History.PaddingCollisionRefundsDeliveredLeg`; no keccak work);
* the inclusion proof carries an `ImtKeccakBreak`;
* the non-inclusion proof carries an `ImtKeccakBreak`.

The zero leaf cannot be the inclusion proof's leaf: it carries value 0, and a non-inclusion proof
needs a nonzero value. -/
def Properties.ProofsExclusiveOrKeccakBreakAtPin : Prop :=
  ∀ (keccak : Keccak) (T : Tree), Valid T → TreeBounded T →
    ∀ (height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      LeafBounded ℓ₁ → LeafBounded ℓ₂ →
      InclusionAccepted (efficientHash keccak) (hashLeaf keccak)
        (root (efficientHash keccak) (imtPadding keccak) (hashLeaf keccak) T height) v ℓ₁ i₁ s₁ k₁ →
      NonInclusionAccepted (efficientHash keccak) (hashLeaf keccak)
        (root (efficientHash keccak) (imtPadding keccak) (hashLeaf keccak) T height) v ℓ₂ i₂ s₂ k₂ →
        (T.leafCount ≤ i₂ ∧ ℓ₂ = ⟨0, 0, 0⟩)
          ∨ ImtKeccakBreak keccak pinPaddingPre T height s₁ k₁ i₁ ℓ₁
          ∨ ImtKeccakBreak keccak pinPaddingPre T height s₂ k₂ i₂ ℓ₂

/-- **ONE INCLUSION PROOF, AT THE PIN: THE VALUE IS IN THE TREE, OR KECCAK COLLIDES ON NAMED BYTES.**
`InclusionSoundOrBreak` instantiated with keccak as at the pin, against a valid tree. The padding
forgery gives no inclusion power: the zero leaf carries value 0, which the sentinel holds. -/
def Properties.InclusionSoundOrKeccakBreakAtPin : Prop :=
  ∀ (keccak : Keccak) (T : Tree), Valid T → TreeBounded T →
    ∀ (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      LeafBounded ℓ →
      InclusionAccepted (efficientHash keccak) (hashLeaf keccak)
        (root (efficientHash keccak) (imtPadding keccak) (hashLeaf keccak) T height) v ℓ idx sibs k →
        v ∈ IMTAbstract.keys (toAbs T) ∨ ImtKeccakBreak keccak pinPaddingPre T height sibs k idx ℓ

/-- **ONE ABSENCE PROOF, AT THE PIN: A RECLAIM WITNESS, THE PADDING FORGERY, OR A KECCAK COLLISION ON
NAMED BYTES.** `NonInclusionSoundOrBreak` instantiated with keccak as at the pin: an accepted
non-inclusion proof for `v` names a leaf of the tree whose window brackets `v`; or it presents the
zero leaf at an unoccupied index (the forged-absence bug, which needs no keccak work); or it
carries an `ImtKeccakBreak`. The atomic-interop timeout and refund paths rest on this check
(`verifyNonInclusion`). -/
def Properties.NonInclusionSoundOrKeccakBreakAtPin : Prop :=
  ∀ (keccak : Keccak) (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ)
    (sibs : ℕ → UInt256) (k : ℕ),
    TreeBounded T → LeafBounded ℓ →
    NonInclusionAccepted (efficientHash keccak) (hashLeaf keccak)
      (root (efficientHash keccak) (imtPadding keccak) (hashLeaf keccak) T height) v ℓ idx sibs k →
      (∃ W ∈ toAbs T, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
        ∨ (T.leafCount ≤ idx ∧ ℓ = ⟨0, 0, 0⟩)
        ∨ ImtKeccakBreak keccak pinPaddingPre T height sibs k idx ℓ

/-- **AT THE PIN THE PADDING DISJUNCT CANNOT BE DROPPED, AND THE KECCAK BREAKS ARE NOT TAUTOLOGIES.**
For EVERY keccak and every `0 < a < b`, on the valid run `threeLeafTree a b` at height 2 with the
pin's padding: the honest inclusion proof for `a` (leaf 1) and the padding forgery (the zero leaf
at slot 3) meet every premise of `ProofsExclusiveOrKeccakBreakAtPin`; neither proof carries an
`ImtKeccakBreak`; and the forgery's `TreeRootBreak` holds, so `TreeRootBreakIsKeccakCollisionAtPin`'s
premises are met too, with its keccak disjunct false. -/
@[countermodel] def Properties.PaddingForgeryIsTheOnlyKeccakFreeBreak : Prop :=
  ∀ (keccak : Keccak) (a b : UInt256), 0 < a → a < b →
    Valid (threeLeafTree a b) ∧ TreeBounded (threeLeafTree a b)
      ∧ LeafBounded ((threeLeafTree a b).leaf 1) ∧ LeafBounded ⟨0, 0, 0⟩
      ∧ InclusionAccepted (efficientHash keccak) (hashLeaf keccak)
          (root (efficientHash keccak) (imtPadding keccak) (hashLeaf keccak) (threeLeafTree a b) 2)
          a ((threeLeafTree a b).leaf 1) 1
          (honestSibs (efficientHash keccak) (imtPadding keccak)
            (leafHashes (hashLeaf keccak) (threeLeafTree a b)) 1) 2
      ∧ NonInclusionAccepted (efficientHash keccak) (hashLeaf keccak)
          (root (efficientHash keccak) (imtPadding keccak) (hashLeaf keccak) (threeLeafTree a b) 2)
          a ⟨0, 0, 0⟩ 3
          (honestSibs (efficientHash keccak) (imtPadding keccak)
            (leafHashes (hashLeaf keccak) (threeLeafTree a b)) 3) 2
      ∧ TreeRootBreak (efficientHash keccak) (imtPadding keccak) (hashLeaf keccak) (threeLeafTree a b)
          2 (honestSibs (efficientHash keccak) (imtPadding keccak)
            (leafHashes (hashLeaf keccak) (threeLeafTree a b)) 3) 2 3 ⟨0, 0, 0⟩
      ∧ ¬ ImtKeccakBreak keccak pinPaddingPre (threeLeafTree a b) 2
          (honestSibs (efficientHash keccak) (imtPadding keccak)
            (leafHashes (hashLeaf keccak) (threeLeafTree a b)) 1) 2 1 ((threeLeafTree a b).leaf 1)
      ∧ ¬ ImtKeccakBreak keccak pinPaddingPre (threeLeafTree a b) 2
          (honestSibs (efficientHash keccak) (imtPadding keccak)
            (leafHashes (hashLeaf keccak) (threeLeafTree a b)) 3) 2 3 ⟨0, 0, 0⟩

end MerkleSpec.DomainSeparation.History
