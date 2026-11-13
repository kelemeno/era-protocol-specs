import EraSpec.Contracts.L2InteropCommitmentTree.Specs.PaddingAtHead

/-!
# Properties: at `main`, an accepted absence proof means absent, or a named keccak collision

Statements about `EraSpec.Contracts.L2InteropCommitmentTree.Specs.PaddingAtHead`; proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.PaddingAtHead`.  Source: era-contracts `main`
`3605e82`, fix commit `78e14b3bc` ("F-04").  No property takes a hash premise.

* **The byte strings.**  The tag is the string literal, and the three keccak preimages
  (`abi.encode` of a leaf, a node pair, the tag) have lengths 96, 64 and 34, so no two of them
  are equal.  A node preimage determines its pair, and a leaf preimage determines what the
  verifiers read from the leaf.
* **The model.**  The pin is the instance `ze = hashLeaf({0,0,0})` of the model with an
  independent padding constant.  At every padding constant, `setup` and every guarded insert keep
  the storage caching the leaf hashes, `root()` is the published root, and the reached list
  states and heights are exactly `RunHeight`'s.
* **The headline.**  On every state reached at `main`, against the root the contract stores, an
  accepted `verifyNonInclusion` means the value is absent, or `KeccakBreakAtHead`: keccak
  collides on two byte strings that the instance names.  The padding case of that break is
  `keccak(abi.encode(ℓ)) = keccak("zkSync:IndexedMerkleTree:emptyLeaf")` for the presented leaf
  `ℓ`.  The same holds for `verifyInclusion`, and for a pair of proofs of the two kinds.
* **Against `TreeRoot`'s break.**  `KeccakBreakAtHead` is a `TreeRootBreak` at `main`'s hashes,
  and each case of `TreeRootBreak` there is a keccak collision on named inputs.  The padding
  case is `hashLeaf(ℓ) = IMT_EMPTY_LEAF_HASH`, a collision between a 96-byte and a 34-byte
  string.  At the pin, the same case held for the zero leaf with no collision.
* **The pin's countermodel at `main`.**  On the three-leaf run, the forged absence proof of
  `PaddingCollisionRefundsDeliveredLeg` / `CThreeLeafWitness` is accepted at `main` exactly when
  keccak collides on `abi.encode(0,0,0)` and the tag, or on a node pair at one of the two steps
  of its path.  For one hash, the same proof against the same tree is accepted with the pin's
  padding and rejected with `main`'s.
* **Out-of-range indices.**  `calculateRoot` still accepts the honest siblings of an empty slot,
  but what they authenticate there is `IMT_EMPTY_LEAF_HASH` itself.  Presenting any leaf at an
  index at or beyond the leaf count is a keccak collision with the tag, a node collision, or a
  wrong length, and beyond `2 ^ _height` only a wrong length.
* **Anti-vacuity.**  Honest proofs locate no break, for every keccak; the contract's own
  `merklePath` outputs are accepted, against the stored root, for present and absent values.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (word HashCollision)

/-! ## The byte strings -/

/-- **THE TAG IS THE STRING LITERAL.**  `imtEmptyLeafTag` is the character codes of
`"zkSync:IndexedMerkleTree:emptyLeaf"`, all below 128, so it is also the string's UTF-8
encoding, which is what `keccak256("…")` hashes (`Config.sol:90`).  It has 34 bytes. -/
def Properties.ImtEmptyLeafTagIsTheLiteral : Prop :=
  imtEmptyLeafTag = "zkSync:IndexedMerkleTree:emptyLeaf".toList.map (fun c => c.toNat.toUInt8)
    ∧ (∀ c ∈ "zkSync:IndexedMerkleTree:emptyLeaf".toList, c.toNat < 128)
    ∧ imtEmptyLeafTag.length = 34

/-- **THE THREE PREIMAGES ARE SEPARATED BY LENGTH.**  A leaf preimage has 96 bytes, a node
preimage 64 and the tag 34, so no leaf preimage is a node preimage or the tag, and no node
preimage is the tag.  This is the content of the `hashLeaf` comment ("the preimage for each
leaf is not 64 bytes long", `IndexedMerkleTree.sol:121-122`) and of `IMT_EMPTY_LEAF_HASH`'s. -/
def Properties.ImtPreimagesDomainSeparated : Prop :=
  (∀ ℓ : Leaf, (imtLeafPreimage ℓ).length = 96)
    ∧ (∀ a b : UInt256, (imtNodePreimage a b).length = 64)
    ∧ (∀ (ℓ : Leaf) (a b : UInt256),
        imtLeafPreimage ℓ ≠ imtNodePreimage a b ∧ imtLeafPreimage ℓ ≠ imtEmptyLeafTag
          ∧ imtNodePreimage a b ≠ imtEmptyLeafTag)

/-- **THE PREIMAGES DETERMINE WHAT IS HASHED.**  A node preimage determines its pair.  A leaf
preimage determines the leaf's `value` and `nextValue`, the two fields the verifiers read, and
the whole leaf when both `nextIndex` fields fit a `uint256`. -/
def Properties.ImtPreimagesDetermineTheirInputs : Prop :=
  (∀ a b c d : UInt256, imtNodePreimage a b = imtNodePreimage c d → a = c ∧ b = d)
    ∧ (∀ ℓ₁ ℓ₂ : Leaf, imtLeafPreimage ℓ₁ = imtLeafPreimage ℓ₂ →
        ℓ₁.value = ℓ₂.value ∧ ℓ₁.nextValue = ℓ₂.nextValue
          ∧ (ℓ₁.nextIndex < 2 ^ 256 → ℓ₂.nextIndex < 2 ^ 256 → ℓ₁ = ℓ₂))

/-! ## The model: the pin is one padding constant, and the storage caches the fold -/

/-- **THE PIN IS THE INSTANCE `ze = hashLeaf({0,0,0})`.**  `CachedRoot`'s `cSetup` is
`cSetupPad` at the pin's padding constant, and `CReaches` is `CReachesPad` there.  So the model
at `main` changes exactly one argument of the pin's model. -/
def Properties.PinSetupIsPadAtZeroLeafHash : Prop :=
  ∀ (h : Hash) (hl : LeafHash), cSetup h hl = cSetupPad h hl (zeroLeafHash hl)
    ∧ ∀ S : CState, CReaches h hl S ↔ CReachesPad h hl (zeroLeafHash hl) S

/-- **`setup` CACHES THE SENTINEL TREE, PADDED WITH `ze`.**  For every node hash, leaf hash and
padding constant, `setup` on fresh storage does not revert.  It gives the sentinel list state
with `hSetup`'s dimensions, the storage caches the one leaf hash `hashLeaf({0,0,0})` padded with
`ze`, and `root()` is that leaf hash. -/
def Properties.CSetupPadCaches : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (ze : UInt256), ∃ S : CState, cSetupPad h hl ze = some S
    ∧ S.tree = setup ∧ S.toH = hSetup
    ∧ FullMerkle.Represents h ze (leafHashes hl S.tree) S.fm
    ∧ S.root = some (hl ⟨0, 0, 0⟩)

/-- **ON EVERY REACHED STATE, `root()` IS THE PUBLISHED ROOT, PADDED WITH `ze`.**  A state
reached from `cSetupPad h hl ze` has a `RunHeight` view reached from `hSetup`, its storage
caches its leaf hashes with padding `ze`, and `root()` returns `HState.root` of the view at its
own `_height`, with padding `ze`. -/
def Properties.CReachesPadRootIsPublished : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (ze : UInt256) (S : CState), CReachesPad h hl ze S →
    HReaches hSetup S.toH
      ∧ FullMerkle.Represents h ze (leafHashes hl S.tree) S.fm
      ∧ S.root = some (S.toH.root h ze hl)

/-- **EVERY RUN FROM `setup` STAYS REACHED.**  Every step of a `CRun` that starts at
`cSetupPad h hl ze` is a reached state, so the results below hold at every step of every run. -/
def Properties.CRunPadReaches : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (ze : UInt256) (R : ℕ → CState), CRun h hl R →
    cSetupPad h hl ze = some (R 0) → ∀ n, CReachesPad h hl ze (R n)

/-- **THE PADDING CONSTANT CHANGES NO LIST STATE AND NO HEIGHT.**  For every padding constant,
the `RunHeight` views of the reached states are exactly the states `HReaches` reaches from
`hSetup`.  The pin and `main` reach the same trees at the same heights; only hash values
differ. -/
def Properties.CReachesPadViewsAreHReaches : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (ze : UInt256) (U : HState),
    (∃ S : CState, CReachesPad h hl ze S ∧ S.toH = U) ↔ HReaches hSetup U

/-! ## The headline -/

/-- **H-1 HEADLINE: AT `main`, A VERIFIED ABSENCE IS AN ABSENCE OR A NAMED KECCAK COLLISION.**
For every function `keccak`, on every state reached from `main`'s `IndexedMerkleTree.setup` by
guarded inserts, `root()` returns some `R`.  If `verifyNonInclusion(R, v, ℓ, idx, proof)`
accepts, for any presented low leaf `ℓ`, index `idx` and sibling path of any length, then
either `v` is not in the tree, or the proof carries a `KeccakBreakAtHead`:

* `idx` is a padding slot and `keccak(abi.encode(ℓ)) = keccak("zkSync:IndexedMerkleTree:emptyLeaf")`;
* `idx` is occupied and keccak collides on the stored leaf's and `ℓ`'s `abi.encode`;
* a node-hash collision at a named step of the path; or
* a wrong path length, located as a keccak collision between a 64-byte node preimage and
  another node, leaf or tag preimage (`LengthKeccakBreak`).

In each case the two byte strings differ, so each is a genuine keccak collision; at the pin the
padding case needed none (`PaddingHitAtPinNeedsNoCollision`). -/
def Properties.NonInclusionAtHeadIsAbsentOrKeccakCollision : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (S : CState), CReachesAtHead keccak S →
    ∃ R : UInt256, S.root = some R ∧
      ∀ (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
        NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) R v ℓ idx sibs k →
          v ∉ keys (toAbs S.tree) ∨ KeccakBreakAtHead keccak S.tree S.fm.height sibs k idx ℓ

/-- **THE SAME FOR `verifyInclusion`.**  An accepted inclusion proof against the stored root
means the value is in the tree, or a `KeccakBreakAtHead` on its path. -/
def Properties.InclusionAtHeadIsPresentOrKeccakCollision : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (S : CState), CReachesAtHead keccak S →
    ∃ R : UInt256, S.root = some R ∧
      ∀ (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
        InclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) R v ℓ idx sibs k →
          v ∈ keys (toAbs S.tree) ∨ KeccakBreakAtHead keccak S.tree S.fm.height sibs k idx ℓ

/-- **NO VALUE IS BOTH PROVED PRESENT AND PROVED ABSENT, SHORT OF A NAMED COLLISION.**  If a
value has an accepted inclusion proof and an accepted non-inclusion proof against the stored
root, one of the two paths carries a `KeccakBreakAtHead`. -/
def Properties.ProofsExclusiveAtHeadOrKeccakCollision : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (S : CState), CReachesAtHead keccak S →
    ∃ R : UInt256, S.root = some R ∧
      ∀ (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
        InclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) R v ℓ₁ i₁ s₁ k₁ →
        NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) R v ℓ₂ i₂ s₂ k₂ →
          KeccakBreakAtHead keccak S.tree S.fm.height s₁ k₁ i₁ ℓ₁
            ∨ KeccakBreakAtHead keccak S.tree S.fm.height s₂ k₂ i₂ ℓ₂

/-! ## Against `TreeRoot`'s located break -/

/-- **EVERY KECCAK BREAK IS A `TreeRootBreak`.**  At `main`'s hashes and padding constant,
`KeccakBreakAtHead` implies `TreeRootBreak` on the same proof.  So it is at least as strong as
the located break that the `…OrBreak` results of this package (and `InteropAtomicity`'s
`ImtProofBreak`) conclude when instantiated there. -/
def Properties.KeccakBreakAtHeadIsTreeRootBreak : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (T : Tree) (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ)
    (ℓ : Leaf),
    KeccakBreakAtHead keccak T height sibs k idx ℓ →
      TreeRootBreak (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtHashLeaf keccak) T height
        sibs k idx ℓ

/-- **`PathCollision` AT `main`'S NODE HASH IS A KECCAK COLLISION.**  For any padding and level-0
list, a positional collision of `Merkle.efficientHash` on a path is exactly a keccak collision
on the two named 64-byte preimages at the same step. -/
def Properties.PathCollisionAtHeadIffKeccak : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256)
    (lvl k j : ℕ) (x : UInt256),
    PathCollision (imtNodeHash keccak) z0 L sibs lvl k j x
      ↔ PathKeccakCollision keccak z0 L sibs lvl k j x

/-- **`HeightBreak` AT `main`'S HASHES IS A KECCAK COLLISION.**  A located wrong path length,
over the tree's leaf hashes with padding `IMT_EMPTY_LEAF_HASH`, is exactly a
`LengthKeccakBreak`: in every case two named byte strings of different kinds or contents
collide. -/
def Properties.HeightBreakAtHeadIffKeccak : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (T : Tree) (height : ℕ) (sibs : ℕ → UInt256) (k j : ℕ)
    (ℓ : Leaf),
    HeightBreak (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtLevel0 keccak T) sibs k height
        j (imtHashLeaf keccak ℓ)
      ↔ LengthKeccakBreak keccak T height sibs k j ℓ

/-- **AT `main`, THE PADDING CASE IS A KECCAK COLLISION WITH THE TAG.**  The `paddingHit` case of
`TreeRootBreak` at `main`'s hashes holds exactly when the index is a padding slot and keccak
takes the same value on the presented leaf's `abi.encode` and on the tag. -/
def Properties.PaddingHitAtHeadIffEmptyLeafCollision : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (T : Tree) (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ)
    (ℓ : Leaf),
    TreeRootBreakAt (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtHashLeaf keccak) T height
        sibs k idx ℓ .paddingHit
      ↔ T.leafCount ≤ idx ∧ HashCollision keccak (imtLeafPreimage ℓ) imtEmptyLeafTag

/-- **AT THE PIN, THE SAME CASE NEEDED NO COLLISION.**  With the pin's padding constant
`hashLeaf({0,0,0})`, which is keccak of the zero leaf's own `abi.encode`, the `paddingHit` case
holds for the zero leaf at every padding slot, for every keccak. -/
def Properties.PaddingHitAtPinNeedsNoCollision : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (T : Tree) (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ),
    T.leafCount ≤ idx →
      zeroLeafHash (imtHashLeaf keccak) = keccak (imtLeafPreimage ⟨0, 0, 0⟩)
        ∧ TreeRootBreakAt (imtNodeHash keccak) (zeroLeafHash (imtHashLeaf keccak))
            (imtHashLeaf keccak) T height sibs k idx ⟨0, 0, 0⟩ .paddingHit

/-- **EVERY LOCATED BREAK AT `main` IS A NAMED KECCAK COLLISION.**  For leaves whose `nextIndex`
fits a `uint256` (every ABI-decoded `IMTLeaf`), a `TreeRootBreak` at `main`'s hashes is one of:
a keccak collision of the presented leaf's `abi.encode` with the tag at a padding slot; of the
stored and the presented leaf's `abi.encode` at an occupied slot; a node collision on the path
at the right length; or a `LengthKeccakBreak`.  This translates the break disjunct of the
`…OrBreak` results of this package and of `InteropAtomicity` (whose `ImtProofBreak` is
`TreeRootBreak`) when they are instantiated at `main`'s hashes and padding constant.  It does
not re-pin anything else those results depend on: `InteropAtomicity` models the manager at
`c67894b9`. -/
def Properties.TreeRootBreakAtHeadIsKeccakCollision : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (T : Tree) (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ)
    (ℓ : Leaf),
    ℓ.nextIndex < 2 ^ 256 → (∀ i < T.leafCount, (T.leaf i).nextIndex < 2 ^ 256) →
    TreeRootBreak (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtHashLeaf keccak) T height
        sibs k idx ℓ →
      (T.leafCount ≤ idx ∧ HashCollision keccak (imtLeafPreimage ℓ) imtEmptyLeafTag)
        ∨ (idx < T.leafCount ∧ HashCollision keccak (imtLeafPreimage (T.leaf idx)) (imtLeafPreimage ℓ))
        ∨ (k = height ∧ PathKeccakCollision keccak (imtEmptyLeafHash keccak) (imtLevel0 keccak T) sibs
            0 k idx (imtHashLeaf keccak ℓ))
        ∨ LengthKeccakBreak keccak T height sibs k idx ℓ

/-- **WITH THE TREE'S OWN SIBLINGS, ACCEPTANCE IS EXACTLY "THE SLOT'S ENTRY, OR A COLLISION".**
For any node hash, padding, level-0 list and index below capacity, the honest sibling path of
`j` accepts a presented hash `x` iff `x` is the level-0 entry at `j` (a leaf hash, or the
padding constant at an empty slot) or the walk meets a `PathCollision`.  So the collision
disjunct of the results below is not slack: one collision anywhere on the path suffices. -/
def Properties.HonestSiblingsAcceptExactly : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (height j : ℕ) (x : UInt256), j < 2 ^ height →
    (walkPure h (honestSibs h z0 L j) 0 height j x = rootOf h z0 L height
      ↔ L.getD j z0 = x ∨ PathCollision h z0 L (honestSibs h z0 L j) 0 height j x)

/-! ## The pin's countermodel, at `main` -/

/-- **THE THREE-LEAF RUN, WITH ANY PADDING CONSTANT.**  For every node hash, leaf hash, padding
constant and `0 < a < b`, the run `setup; insert a at 0; insert b at 1` does not revert.  It
reaches `threeLeafTree a b` with the view `hThree a b` at height 2; `root()` returns the last
insert's `newRoot`, which is the fold at padding `ze`; and `merklePath(3)` reverts.  The three
states are the steps of a `CRun` from `cSetupPad`.  This meets the `CReachesPad` /
`CReachesAtHead` premise of every property here, and the premises of `CRunPadReaches`. -/
def Properties.PaddingAtHeadThreeLeafRun : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (ze a b : UInt256), 0 < a → a < b →
    ∃ (S₀ S₁ S₂ : CState) (r₁ r₂ : UInt256),
      cSetupPad h hl ze = some S₀ ∧ cInsert h hl S₀ a 0 = some (S₁, r₁)
      ∧ cInsert h hl S₁ b 1 = some (S₂, r₂)
      ∧ CReachesPad h hl ze S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.toH = hThree a b
      ∧ S₂.fm.height = 2 ∧ S₂.root = some r₂ ∧ r₂ = root h ze hl (threeLeafTree a b) 2
      ∧ S₂.merklePath 3 = none
      ∧ ∃ R : ℕ → CState, CRun h hl R ∧ R 0 = S₀ ∧ R 1 = S₁ ∧ ∀ n, 2 ≤ n → R n = S₂

/-- **THE PIN'S FORGED ABSENCE PROOF NEEDS A KECCAK COLLISION AT `main`.**  For every keccak and
`0 < a < b`, on the three-leaf run at `main` (stored root `r₂`, height 2), `a` is in the tree, and:

1. any accepted non-inclusion proof for `a` presenting the zero leaf at a padding index
   (`idx ≥ 3`, any siblings, any length) is a keccak collision: `abi.encode(0,0,0)` against
   the tag at the right length, a node collision on the path, or a wrong length;
2. the pin's own instance (the zero leaf at slot 3, with the honest siblings of slot 3 in
   `main`'s tree, length 2), which `PaddingCollisionRefundsDeliveredLeg` and `CThreeLeafWitness`
   accept at the pin for every hash, is accepted at `main` exactly when keccak collides on
   `abi.encode(0,0,0)` and the tag, or on a node pair at one of its two steps. -/
def Properties.PinForgeryAtHeadNeedsKeccakCollision : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (a b : UInt256), 0 < a → a < b →
    ∃ (S₂ : CState) (r₂ : UInt256),
      CReachesAtHead keccak S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.fm.height = 2
      ∧ S₂.root = some r₂ ∧ a ∈ keys (toAbs S₂.tree)
      ∧ (∀ (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ), 3 ≤ idx →
          NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a ⟨0, 0, 0⟩ idx sibs k →
            (k = 2 ∧ HashCollision keccak (imtLeafPreimage ⟨0, 0, 0⟩) imtEmptyLeafTag)
            ∨ (k = 2 ∧ PathKeccakCollision keccak (imtEmptyLeafHash keccak)
                (imtLevel0 keccak (threeLeafTree a b)) sibs 0 k idx (imtHashLeaf keccak ⟨0, 0, 0⟩))
            ∨ LengthKeccakBreak keccak (threeLeafTree a b) 2 sibs k idx ⟨0, 0, 0⟩)
      ∧ (NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a ⟨0, 0, 0⟩ 3
            (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
              (imtLevel0 keccak (threeLeafTree a b)) 3) 2
          ↔ HashCollision keccak (imtLeafPreimage ⟨0, 0, 0⟩) imtEmptyLeafTag
            ∨ PathKeccakCollision keccak (imtEmptyLeafHash keccak)
                (imtLevel0 keccak (threeLeafTree a b))
                (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
                  (imtLevel0 keccak (threeLeafTree a b)) 3) 0 2 3 (imtHashLeaf keccak ⟨0, 0, 0⟩))

/-- **THE PADDING DISJUNCT IS LOAD-BEARING.**  Some keccak collides on `abi.encode(0,0,0)` and
the tag, and for every such keccak the pin's forged proof is accepted at `main` against the
stored root, for the delivered `a`, whose honest inclusion proof (leaf 1) is accepted too; the
located break is the `emptyLeaf` case.  So the premises of
`PinForgeryAtHeadNeedsKeccakCollision`'s clause 1 and of `ProofsExclusiveAtHeadOrKeccakCollision`
are satisfiable, and the padding disjunct cannot be dropped. -/
def Properties.PinForgeryAtHeadFiresOnCollision : Prop :=
  (∃ keccak : List UInt8 → UInt256, HashCollision keccak (imtLeafPreimage ⟨0, 0, 0⟩) imtEmptyLeafTag)
    ∧ ∀ (keccak : List UInt8 → UInt256),
        HashCollision keccak (imtLeafPreimage ⟨0, 0, 0⟩) imtEmptyLeafTag →
      ∀ a b : UInt256, 0 < a → a < b →
        ∃ (S₂ : CState) (r₂ : UInt256),
          CReachesAtHead keccak S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.root = some r₂
          ∧ a ∈ keys (toAbs S₂.tree)
          ∧ InclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a
              ((threeLeafTree a b).leaf 1) 1
              (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
                (imtLevel0 keccak (threeLeafTree a b)) 1) 2
          ∧ NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a ⟨0, 0, 0⟩ 3
              (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
                (imtLevel0 keccak (threeLeafTree a b)) 3) 2
          ∧ KeccakBreakAtHead keccak S₂.tree S₂.fm.height
              (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
                (imtLevel0 keccak (threeLeafTree a b)) 3) 2 3 ⟨0, 0, 0⟩

/-- **THE NODE DISJUNCT FIRES ALONE.**  There is a keccak with no collision on
`abi.encode(0,0,0)` and the tag for which, for every `0 < a < b`, the pin's forged proof is still
accepted at `main` against the stored root for the delivered `a`, through a node-hash collision
on its path.  So the `node` case of `KeccakBreakAtHead` cannot be dropped either. -/
def Properties.NodeCollisionAtHeadFires : Prop :=
  ∃ keccak : List UInt8 → UInt256,
    ¬ HashCollision keccak (imtLeafPreimage ⟨0, 0, 0⟩) imtEmptyLeafTag
    ∧ ∀ a b : UInt256, 0 < a → a < b →
      ∃ (S₂ : CState) (r₂ : UInt256),
        CReachesAtHead keccak S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.root = some r₂
        ∧ a ∈ keys (toAbs S₂.tree)
        ∧ NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a ⟨0, 0, 0⟩ 3
            (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
              (imtLevel0 keccak (threeLeafTree a b)) 3) 2
        ∧ PathKeccakCollision keccak (imtEmptyLeafHash keccak) (imtLevel0 keccak (threeLeafTree a b))
            (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
              (imtLevel0 keccak (threeLeafTree a b)) 3) 0 2 3 (imtHashLeaf keccak ⟨0, 0, 0⟩)

/-- **THE LEAF DISJUNCT IS LOAD-BEARING.**  The fix does not touch occupied slots.  On the
three-leaf run, leaf 0 is `{0, 1, a}`.  For every `0 < a < b` some keccak collides on its
`abi.encode` and that of the fake low leaf `{0, 1, 0}`, and for every such keccak the honest
path of index 0, presenting the fake leaf, is accepted at `main` as an absence proof for the
delivered `a`; its located break is the `leaf` case. -/
def Properties.LeafCollisionAtHeadFires : Prop :=
  (∀ a : UInt256, 0 < a → ∃ keccak : List UInt8 → UInt256,
      HashCollision keccak (imtLeafPreimage ⟨0, 1, a⟩) (imtLeafPreimage ⟨0, 1, 0⟩))
    ∧ ∀ (keccak : List UInt8 → UInt256) (a b : UInt256), 0 < a → a < b →
      HashCollision keccak (imtLeafPreimage ⟨0, 1, a⟩) (imtLeafPreimage ⟨0, 1, 0⟩) →
        ∃ (S₂ : CState) (r₂ : UInt256),
          CReachesAtHead keccak S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.root = some r₂
          ∧ a ∈ keys (toAbs S₂.tree) ∧ S₂.tree.leaf 0 = ⟨0, 1, a⟩
          ∧ NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a ⟨0, 1, 0⟩ 0
              (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
                (imtLevel0 keccak (threeLeafTree a b)) 0) 2
          ∧ KeccakBreakAtHead keccak S₂.tree S₂.fm.height
              (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak)
                (imtLevel0 keccak (threeLeafTree a b)) 0) 2 0 ⟨0, 1, 0⟩

/-- **SAME HASH, SAME TREE, SAME PROOF: ACCEPTED AT THE PIN, REJECTED AT `main`.**  There is a
keccak that does not collide on `abi.encode(0,0,0)` and the tag, such that for every
`0 < a < b`: with the pin's setup the forged proof of slot 3 is accepted against the stored root
for the delivered `a` (as `CThreeLeafWitness` says for every hash), while with `main`'s setup no
path of length 2 at slot 3 presenting the zero leaf is accepted for `a`.  So the conclusion of
`PinForgeryAtHeadNeedsKeccakCollision` is not a tautology, and the only change between the two
runs is the padding constant. -/
def Properties.PinForgeryAcceptedAtPinRejectedAtHead : Prop :=
  ∃ keccak : List UInt8 → UInt256,
    ¬ HashCollision keccak (imtLeafPreimage ⟨0, 0, 0⟩) imtEmptyLeafTag
    ∧ ∀ a b : UInt256, 0 < a → a < b →
      (∃ (S₂ : CState) (r₂ : UInt256),
          CReaches (imtNodeHash keccak) (imtHashLeaf keccak) S₂ ∧ S₂.tree = threeLeafTree a b
          ∧ S₂.root = some r₂ ∧ a ∈ keys (toAbs S₂.tree)
          ∧ NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a ⟨0, 0, 0⟩ 3
              (honestSibs (imtNodeHash keccak) (zeroLeafHash (imtHashLeaf keccak))
                (imtLevel0 keccak (threeLeafTree a b)) 3) 2)
      ∧ (∃ (S₂ : CState) (r₂ : UInt256),
          CReachesAtHead keccak S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.root = some r₂
          ∧ ∀ sibs : ℕ → UInt256,
              ¬ NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a ⟨0, 0, 0⟩ 3
                  sibs 2)

/-! ## Out-of-range indices -/

/-- **WHAT AN INDEX AT OR BEYOND THE LEAF COUNT STILL BUYS.**  `calculateRootMemory` bounds the
index only by `2 ^ pathLength` (`Merkle.sol:133-140`).  On every state reached at `main`, with
stored root `R`:

1. **still accepted:** for every padding slot `leafCount ≤ idx < 2 ^ _height`, the honest
   siblings of `idx` (public, though `merklePath` refuses them) verify with item hash
   `IMT_EMPTY_LEAF_HASH`; the slot commits the tag's keccak, not a leaf hash;
2. **what presenting a leaf there takes:** an accepted path presenting `hashLeaf(ℓ)` at any
   `idx ≥ leafCount` is, at the right length and below capacity, a keccak collision of
   `abi.encode(ℓ)` with the tag, or a node collision on the path; otherwise a wrong length;
3. **beyond capacity** (`idx ≥ 2 ^ _height`), only a longer path with a `LengthKeccakBreak`. -/
def Properties.OutOfRangeIndexAtHead : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (S : CState), CReachesAtHead keccak S →
    ∃ R : UInt256, S.root = some R
      ∧ (∀ idx : ℕ, S.tree.leafCount ≤ idx → idx < 2 ^ S.fm.height →
          PathAccepts (imtNodeHash keccak) R
            (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtLevel0 keccak S.tree) idx)
            S.fm.height idx (imtEmptyLeafHash keccak))
      ∧ (∀ (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf), S.tree.leafCount ≤ idx →
          PathAccepts (imtNodeHash keccak) R sibs k idx (imtHashLeaf keccak ℓ) →
            (k = S.fm.height ∧ idx < 2 ^ S.fm.height
                ∧ HashCollision keccak (imtLeafPreimage ℓ) imtEmptyLeafTag)
            ∨ (k = S.fm.height ∧ PathKeccakCollision keccak (imtEmptyLeafHash keccak)
                (imtLevel0 keccak S.tree) sibs 0 k idx (imtHashLeaf keccak ℓ))
            ∨ LengthKeccakBreak keccak S.tree S.fm.height sibs k idx ℓ)
      ∧ (∀ (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf), 2 ^ S.fm.height ≤ idx →
          PathAccepts (imtNodeHash keccak) R sibs k idx (imtHashLeaf keccak ℓ) →
            S.fm.height < k ∧ LengthKeccakBreak keccak S.tree S.fm.height sibs k idx ℓ)

/-- **THE PREMISES OF `OutOfRangeIndexAtHead`'S CLAUSES 2 AND 3 ARE SATISFIABLE.**  For a keccak
that collides everywhere (the constant one), on the three-leaf run at `main`, a path of length 2
at the padding slot 3 and a path of length 3 at index 4, beyond `2 ^ 2`, both presenting the zero
leaf, are accepted against the stored root. -/
def Properties.OutOfRangeIndexAtHeadWitness : Prop :=
  ∃ keccak : List UInt8 → UInt256, ∀ a b : UInt256, 0 < a → a < b →
    ∃ (S₂ : CState) (r₂ : UInt256),
      CReachesAtHead keccak S₂ ∧ S₂.tree = threeLeafTree a b ∧ S₂.fm.height = 2
      ∧ S₂.root = some r₂
      ∧ PathAccepts (imtNodeHash keccak) r₂ (fun _ => 0) 2 3 (imtHashLeaf keccak ⟨0, 0, 0⟩)
      ∧ PathAccepts (imtNodeHash keccak) r₂ (fun _ => 0) 3 4 (imtHashLeaf keccak ⟨0, 0, 0⟩)

/-! ## Anti-vacuity -/

/-- **THE PREMISES OF THE TWO BRIDGES ARE SATISFIABLE.**  On the `setup` tree at height 1, for the
constant keccak, the zero leaf presented at the padding slot 1 with a length-1 path carries a
`KeccakBreakAtHead` and a `TreeRootBreak` at `main`'s hashes, and every `nextIndex` involved fits
a `uint256`.  This meets the premises of `KeccakBreakAtHeadIsTreeRootBreak` and
`TreeRootBreakAtHeadIsKeccakCollision`. -/
def Properties.PaddingAtHeadBreakPremisesSatisfiable : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (sibs : ℕ → UInt256),
    (⟨0, 0, 0⟩ : Leaf).nextIndex < 2 ^ 256
    ∧ (∀ i < setup.leafCount, (setup.leaf i).nextIndex < 2 ^ 256)
    ∧ KeccakBreakAtHead keccak setup 1 sibs 1 1 ⟨0, 0, 0⟩
    ∧ TreeRootBreak (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtHashLeaf keccak) setup 1
        sibs 1 1 ⟨0, 0, 0⟩

/-- **NON-TRIVIALITY OF `KeccakBreakAtHead`.**  On the honest proof for any occupied index (the
tree's own siblings, at the tree's height, presenting the stored leaf), no keccak break is
located, for every keccak. -/
def Properties.HonestProofNoKeccakBreakAtHead : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (T : Tree) (height i : ℕ), i < T.leafCount →
    ¬ KeccakBreakAtHead keccak T height
        (honestSibs (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtLevel0 keccak T) i)
        height i (T.leaf i)

/-- **THE CONTRACT'S OWN PROOFS, AGAINST THE STORED ROOT, AT `main`.**  On every reached state,
for every keccak, `root()` returns some `R` and:

1. every value the tree holds sits at an occupied index `i` whose `merklePath(i)` is a path of
   length `_height`, accepted as an inclusion proof against `R`, with no keccak break;
2. every nonzero value the tree does not hold has an occupied low leaf `i` whose
   `merklePath(i)` is accepted as a non-inclusion proof against `R`, with no keccak break.

Clause 2 meets the premises of the headline with its first disjunct true and its second
false. -/
def Properties.ContractProofsAtStoredRootAtHead : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (S : CState), CReachesAtHead keccak S →
    ∃ R : UInt256, S.root = some R
      ∧ (∀ v : UInt256, v ∈ keys (toAbs S.tree) →
          ∃ i < S.tree.leafCount, (S.tree.leaf i).value = v
            ∧ ∃ p : List UInt256, S.merklePath i = some p ∧ p.length = S.fm.height
              ∧ InclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) R v (S.tree.leaf i) i
                  (FullMerkle.pathSibs p) p.length
              ∧ ¬ KeccakBreakAtHead keccak S.tree S.fm.height (FullMerkle.pathSibs p) p.length i
                  (S.tree.leaf i))
      ∧ (∀ v : UInt256, v ≠ 0 → v ∉ keys (toAbs S.tree) →
          ∃ i < S.tree.leafCount,
            ∃ p : List UInt256, S.merklePath i = some p ∧ p.length = S.fm.height
              ∧ NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) R v (S.tree.leaf i) i
                  (FullMerkle.pathSibs p) p.length
              ∧ ¬ KeccakBreakAtHead keccak S.tree S.fm.height (FullMerkle.pathSibs p) p.length i
                  (S.tree.leaf i))

/-- **THE HEADLINE'S PREMISES ARE SATISFIABLE.**  For every keccak, `0 < a < b` and nonzero `v`
other than `a` and `b`: on the three-leaf run at `main`, `v` is absent and has an accepted
non-inclusion proof against the stored root (the contract's `merklePath` of its low leaf) with
no keccak break, while the delivered `a` has an accepted inclusion proof with no keccak
break. -/
def Properties.NonInclusionAtHeadWitness : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (a b v : UInt256), 0 < a → a < b → v ≠ 0 → v ≠ a → v ≠ b →
    ∃ (S₂ : CState) (r₂ : UInt256), CReachesAtHead keccak S₂ ∧ S₂.tree = threeLeafTree a b
      ∧ S₂.root = some r₂ ∧ v ∉ keys (toAbs S₂.tree) ∧ a ∈ keys (toAbs S₂.tree)
      ∧ (∃ (i : ℕ) (p : List UInt256), S₂.merklePath i = some p
          ∧ NonInclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ v (S₂.tree.leaf i) i
              (FullMerkle.pathSibs p) p.length
          ∧ ¬ KeccakBreakAtHead keccak S₂.tree S₂.fm.height (FullMerkle.pathSibs p) p.length i
              (S₂.tree.leaf i))
      ∧ (∃ (i : ℕ) (p : List UInt256), S₂.merklePath i = some p
          ∧ InclusionAccepted (imtNodeHash keccak) (imtHashLeaf keccak) r₂ a (S₂.tree.leaf i) i
              (FullMerkle.pathSibs p) p.length
          ∧ ¬ KeccakBreakAtHead keccak S₂.tree S₂.fm.height (FullMerkle.pathSibs p) p.length i
              (S₂.tree.leaf i))

end Contracts.InteropCommitmentTree
