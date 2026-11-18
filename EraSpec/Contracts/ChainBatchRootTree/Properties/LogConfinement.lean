import EraSpec.Contracts.ChainBatchRootTree.Specs.LogConfinement

/-!
# Properties: an accepted L2-log proof against a ZKsync OS batch root passes through leaf 0, or
locates a keccak break

No property assumes anything about `keccak` except where `ReservedSubtreeDocumented` is named.
Proofs: `../Proofs/LogConfinement.lean`.

* `AcceptedWalkCutMatchOrBreak` (any `PreTree`): a walk that returns the tree's value reaches a
  `cut`, or its keccak input at the landing IS the landing node's keccak input, or a
  `LandingBreak` is located there.
* `LogProofPassesLeafZeroOrBreak` (the chain batch root over any subtrees for leaves 1-3 and the
  reserved half with no cut and no 64- or 88-byte leaf preimage): an accepted log proof, of any
  length and mask, passes through leaf 0 at height 3, or locates a `LandingBreak`.
  `PassesLeafZeroExcludesBreak`: the two outcomes exclude each other.
* `ImtPreTreeRoot`, `ZeroPreTreeReserved`: the IMT `PreTree` evaluates to the existing IMT root
  model, and the zero tree to `RESERVED_SUBTREE_NODE` under the documented value.
* `ImtBatchRootLogProofConfinedOrKeccakEvent`: with the two IMT snapshots and the reserved zero
  half, the break is a keccak collision between the 88-byte log preimage or a 64-byte walk node and a
  64-byte node, a 96-byte IMT leaf, the 34-byte IMT padding or a leaf of the multichain subtree, or
  keccak of such a walk string equal to `0` or to a constant of the multichain subtree.
* `HonestLogProofPassesLeafZero`, `LogProofPassesLeafZeroWitness`, `ImtLandingCollisionFires`:
  the honest proof meets every premise, is confined and locates no break; on a concrete keccak
  under which a log hashes to an IMT leaf hash, a proof through leaf 2 is accepted and the break is
  that 88-versus-96-byte collision.
-/

namespace Contracts.ChainBatchRootTree

open MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (HashCollision word toBytesBE)

/-! ## The generic extractor -/

/-- **WHERE AN ACCEPTED WALK LEAVES ANY HONEST TREE.** No hash premise, no length or index premise.
A walk with claimed leaf `keccak xPre` whose result is `T`'s value either reaches a `cut` of `T`
(its value after the remaining steps is the cut's value), or its keccak input at the landing equals
the landing node's keccak input, or a `LandingBreak` is located at the landing. -/
def Properties.AcceptedWalkCutMatchOrBreak : Prop :=
  ∀ (keccak : Keccak) (T : PreTree) (sibs : ℕ → UInt256) (k j : ℕ) (xPre : List UInt8),
    walkPure (node keccak) sibs 0 k j (keccak xPre) = T.val keccak →
      LandingAtCut keccak T sibs k j xPre ∨ LandingPreimageMatch keccak T sibs k j xPre
        ∨ LandingBreak keccak T sibs k j xPre

/-! ## Confinement to leaf 0 -/

/-- **CROSS-SUBTREE CONFINEMENT OF L2-LOG PROOFS.** No height check, no hash premise. Let the
batch's chain batch root be `compute a (T1.val) (T2.val) (T3.val)`, where `T1`, `T2`, `T3` describe
leaves 1-3 and `R` the reserved half (value `RESERVED_SUBTREE_NODE`), none of them containing a
`cut` or a leaf whose keccak input is 64 or 88 bytes long. Then a log proof of any length `k` and
mask `j < 2^k` (`Merkle.sol:133-140`) that returns that root passes through leaf 0 at height 3
(`PassesLeafZero`), or a `LandingBreak` is located in the tree. -/
def Properties.LogProofPassesLeafZeroOrBreak : Prop :=
  ∀ (keccak : Keccak) (a : UInt256) (T1 T2 T3 R : PreTree) (log : L2Log) (sibs : ℕ → UInt256)
    (k j : ℕ),
    T1.CutFree → T2.CutFree → T3.CutFree → R.CutFree →
    T1.LeafLengthsAvoid → T2.LeafLengthsAvoid → T3.LeafLengthsAvoid → R.LeafLengthsAvoid →
    R.val keccak = RESERVED_SUBTREE_NODE →
    j < 2 ^ k →
    walkPure (node keccak) sibs 0 k j (keccak (logPre log))
        = compute keccak a (T1.val keccak) (T2.val keccak) (T3.val keccak) →
      PassesLeafZero keccak a (T1.val keccak) (T2.val keccak) (T3.val keccak) sibs k j
          (keccak (logPre log))
        ∨ LandingBreak keccak (cbrPreTree a T1 T2 T3 R) sibs k j (logPre log)

/-- **THE TWO OUTCOMES EXCLUDE EACH OTHER.** A walk that passes through leaf 0 at height 3 lands on
the leaf-0 cut, so no `LandingBreak` is located. So `LandingBreak` is not satisfied by the outcome
the property calls confined. -/
def Properties.PassesLeafZeroExcludesBreak : Prop :=
  ∀ (keccak : Keccak) (a : UInt256) (T1 T2 T3 R : PreTree) (log : L2Log) (sibs : ℕ → UInt256)
    (k j : ℕ),
    R.val keccak = RESERVED_SUBTREE_NODE →
    PassesLeafZero keccak a (T1.val keccak) (T2.val keccak) (T3.val keccak) sibs k j
        (keccak (logPre log)) →
      ¬ LandingBreak keccak (cbrPreTree a T1 T2 T3 R) sibs k j (logPre log)

/-! ## The IMT subtrees and the reserved half -/

/-- **THE IMT `PreTree` IS THE IMT ROOT MODEL.** For every keccak, tree and height, the value of
`imtPreTree T H` is `Contracts.InteropCommitmentTree.root` over `T`'s `hashLeaf` hashes with node
hash `node keccak` and padding `keccak imtPaddingPre` (`IMT_EMPTY_LEAF_HASH`) at height `H`. -/
def Properties.ImtPreTreeRoot : Prop :=
  ∀ (keccak : Keccak) (T : Contracts.InteropCommitmentTree.Tree) (H : ℕ),
    (imtPreTree T H).val keccak = imtRoot keccak T H

/-- **THE ZERO TREE IS THE RESERVED NODE.** Under the documented reserved value, `zeroPreTree 2`
evaluates to `RESERVED_SUBTREE_NODE`. -/
def Properties.ZeroPreTreeReserved : Prop :=
  ∀ keccak : Keccak, ReservedSubtreeDocumented keccak →
    (zeroPreTree 2).val keccak = RESERVED_SUBTREE_NODE

/-- **CONFINEMENT AGAINST A ZKSYNC OS BATCH WITH ITS TWO IMT SNAPSHOTS.** Under the documented
reserved value, let the batch root be `compute a (T1.val) (imtRoot Tb Hb) (imtRoot Te He)`, with the
multichain subtree `T1` free of cuts and of 64- and 88-byte leaf preimages. A log proof of any
length `k` and mask `j < 2^k` that returns it passes through leaf 0 at height 3, or:

* keccak maps the walk's input at the landing (88 bytes long, the log preimage, or 64 bytes long,
  a node preimage of the walk) and a different string `Y` to the same word, where `Y` is 64, 96 or
  34 bytes long or is a leaf preimage of `T1` (the proof takes `Y` from the landing node: a node
  preimage, an IMT leaf preimage, the IMT padding preimage, or a leaf of `T1`); or
* keccak maps the walk's input at the landing (88 or 64 bytes long) to `0` or to a constant of
  `T1`. -/
def Properties.ImtBatchRootLogProofConfinedOrKeccakEvent : Prop :=
  ∀ (keccak : Keccak) (a : UInt256) (T1 : PreTree) (Tb Te : Contracts.InteropCommitmentTree.Tree)
    (Hb He : ℕ) (log : L2Log) (sibs : ℕ → UInt256) (k j : ℕ),
    ReservedSubtreeDocumented keccak →
    T1.CutFree → T1.LeafLengthsAvoid →
    j < 2 ^ k →
    walkPure (node keccak) sibs 0 k j (keccak (logPre log))
        = compute keccak a (T1.val keccak) (imtRoot keccak Tb Hb) (imtRoot keccak Te He) →
      PassesLeafZero keccak a (T1.val keccak) (imtRoot keccak Tb Hb) (imtRoot keccak Te He) sibs k j
          (keccak (logPre log))
        ∨ (∃ Y, HashCollision keccak
              (landingInput keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)) Y
            ∧ ((landingInput keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)).length
                = 88
              ∨ (landingInput keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)).length
                = 64)
            ∧ (Y.length = 64 ∨ Y.length = 96 ∨ Y.length = 34 ∨ T1.HasLeaf Y))
        ∨ (∃ v, keccak
              (landingInput keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)) = v
            ∧ ((landingInput keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)).length
                = 88
              ∨ (landingInput keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)).length
                = 64)
            ∧ (v = 0 ∨ T1.HasConst v))

/-! ## Non-triviality -/

/-- **THE HONEST PROOF IS CONFINED.** There is an instance of
`ImtBatchRootLogProofConfinedOrKeccakEvent`'s premises (documented reserved value, two IMT
snapshots, multichain leaf `const 0`, a 3-step proof at mask 0 with the honest siblings) where the
walk passes through leaf 0 at height 3 and no `LandingBreak` is located. -/
def Properties.HonestLogProofPassesLeafZero : Prop :=
  ∃ (keccak : Keccak) (a : UInt256) (T1 : PreTree) (Tb Te : Contracts.InteropCommitmentTree.Tree)
    (Hb He : ℕ) (log : L2Log) (sibs : ℕ → UInt256) (k j : ℕ),
    ReservedSubtreeDocumented keccak ∧ T1.CutFree ∧ T1.LeafLengthsAvoid ∧ j < 2 ^ k
      ∧ walkPure (node keccak) sibs 0 k j (keccak (logPre log))
          = compute keccak a (T1.val keccak) (imtRoot keccak Tb Hb) (imtRoot keccak Te He)
      ∧ PassesLeafZero keccak a (T1.val keccak) (imtRoot keccak Tb Hb) (imtRoot keccak Te He) sibs k
          j (keccak (logPre log))
      ∧ ¬ LandingBreak keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)

/-- **THE BREAK FIRES, AS AN 88-VERSUS-96-BYTE COLLISION.** On a concrete keccak (documented
reserved value; every 88- and 96-byte string hashed to one word), a 3-step proof at mask
`IMT_BEGIN_ROOT_LEAF_INDEX` whose claimed leaf is a log hash is accepted against a batch whose IMT
snapshots are the freshly set-up tree. It does not pass through leaf 0, and the located break is
the collision between the 88-byte log preimage and the 96-byte `{0,0,0}` leaf preimage. -/
def Properties.ImtLandingCollisionFires : Prop :=
  ∃ (keccak : Keccak) (a : UInt256) (T1 : PreTree) (log : L2Log) (sibs : ℕ → UInt256),
    ReservedSubtreeDocumented keccak ∧ T1.CutFree ∧ T1.LeafLengthsAvoid
      ∧ IMT_BEGIN_ROOT_LEAF_INDEX < 2 ^ TREE_DEPTH
      ∧ walkPure (node keccak) sibs 0 TREE_DEPTH IMT_BEGIN_ROOT_LEAF_INDEX (keccak (logPre log))
          = compute keccak a (T1.val keccak)
              (imtRoot keccak Contracts.InteropCommitmentTree.setup 0)
              (imtRoot keccak Contracts.InteropCommitmentTree.setup 0)
      ∧ ¬ PassesLeafZero keccak a (T1.val keccak)
          (imtRoot keccak Contracts.InteropCommitmentTree.setup 0)
          (imtRoot keccak Contracts.InteropCommitmentTree.setup 0) sibs TREE_DEPTH
          IMT_BEGIN_ROOT_LEAF_INDEX (keccak (logPre log))
      ∧ landingInput keccak
          (imtBatchPreTree a T1 Contracts.InteropCommitmentTree.setup 0
            Contracts.InteropCommitmentTree.setup 0) sibs TREE_DEPTH IMT_BEGIN_ROOT_LEAF_INDEX
          (logPre log) = logPre log
      ∧ (landing keccak
          (imtBatchPreTree a T1 Contracts.InteropCommitmentTree.setup 0
            Contracts.InteropCommitmentTree.setup 0) sibs TREE_DEPTH IMT_BEGIN_ROOT_LEAF_INDEX
          (logPre log)).1 = .leaf (imtLeafPre ⟨0, 0, 0⟩)
      ∧ HashCollision keccak (logPre log) (imtLeafPre ⟨0, 0, 0⟩)

/-- **WITNESS FOR THE GENERIC CONFINEMENT.** All premises of `LogProofPassesLeafZeroOrBreak` hold
on one instance with nonempty subtrees: leaf 1 `const 0`, leaves 2 and 3 the set-up commitment tree,
the reserved zero half, a documented keccak and a 3-step proof at mask 0; the walk passes through
leaf 0 at height 3. -/
def Properties.LogProofPassesLeafZeroWitness : Prop :=
  ∃ (keccak : Keccak) (a : UInt256) (T1 T2 T3 R : PreTree) (log : L2Log) (sibs : ℕ → UInt256)
    (k j : ℕ),
    T1.CutFree ∧ T2.CutFree ∧ T3.CutFree ∧ R.CutFree
      ∧ T1.LeafLengthsAvoid ∧ T2.LeafLengthsAvoid ∧ T3.LeafLengthsAvoid ∧ R.LeafLengthsAvoid
      ∧ R.val keccak = RESERVED_SUBTREE_NODE ∧ j < 2 ^ k
      ∧ walkPure (node keccak) sibs 0 k j (keccak (logPre log))
          = compute keccak a (T1.val keccak) (T2.val keccak) (T3.val keccak)
      ∧ PassesLeafZero keccak a (T1.val keccak) (T2.val keccak) (T3.val keccak) sibs k j
          (keccak (logPre log))

end Contracts.ChainBatchRootTree
