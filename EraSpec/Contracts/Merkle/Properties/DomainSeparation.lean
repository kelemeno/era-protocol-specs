import EraSpec.Contracts.Merkle.Specs.DomainSeparation
import EraSpec.Core.Headline

/-!
# Properties: every Merkle domain premise is a keccak collision on two named byte strings

Statements about `../Specs/DomainSeparation.lean`. Proofs: `../Proofs/DomainSeparation.lean`.

No property here assumes anything about `keccak`, except the last conjunct of
`EmptyConstantsCoincide`, whose premise `KeccakOfEmptyIsDocumented` names one keccak value. Each
property either is a byte-level fact about the preimages (lengths, first words, injectivity of the
fixed-width encodings), or turns an abstract domain premise, or an abstract located break, into
`HashCollision keccak x y` with `x` and `y` named by the instance. A collision conclusion that names
its inputs can be false, unlike "some collision exists" (ASSUMPTIONS.md, "Results whose premises
cannot hold").

The witnesses do two things. They meet each premise that forces a hash equality under a keccak
model changed at ONE string (`plantKeccak κ x y`, for every model `κ`), and show that the collision
the theorem then names is exactly the planted one. And they show the collision conclusions false
on honest instances, for every keccak, or under a stand-in (`lengthKeccak`, `firstWordKeccak`).

Groups, in order:

* (a) the length table, and equal hashes of different-length inputs;
* (b) the 96-byte family (`hashLeaf`, `chainIdLeafHash`, the empty entry, `commitValue`), the three
  empty-entry literals and the IMT sentinel leaf;
* (c) the IMT root check down to keccak: `TreeRootBreakIsKeccakCollision`, and the headline
  `ProofsExclusiveOrKeccakBreak` (with a padding preimage of any length other than 64 and 96, as
  `b17415d20`'s `IMT_EMPTY_LEAF_HASH`, there is no keccak-free break), with its single-proof forms
  `InclusionSoundOrKeccakBreak` and `NonInclusionSoundOrKeccakBreak`. The forms at the interop
  pin's padding `hashLeaf({0,0,0})`, where the forged-absence bug is the only keccak-free break,
  are History (`../History/Properties/DomainSeparationPinned.lean`);
* (d) `Verifier.accept_forces_height`'s domain hypotheses and `LastLeaf.EntriesNotEmpty`, for the
  logs, chain, shared and IMT trees, with the headlines `AcceptOpensPreimageOrKeccakBreak` (any
  tree), `ChainTreeProofOpensBatchOrKeccakBreak`, `SharedTreeProofOpensChainOrKeccakBreak`,
  `AcceptedLastBatchOrKeccakBreak` (a path of the tree's height from an occupied index) and
  `DeployedLastBatchCheckOrKeccakBreak` (the prover's length and index, as deployed);
* (e) the node-collision lift: `PathCollision`, `PinnedBreak.nodeCollision`, `LevelCollision`,
  `TreeCollision` and `WalkCollision` each are 64-byte keccak collisions.

Where the content lies. For (a), (b) and the single-premise forms of (c) and (d), the content is
that the two named byte strings DIFFER; the collision form then follows from the definition of
`HashCollision`. The composed results of (c) and (d) carry protocol content: an accepted proof opens
the tree at the claimed preimage, or keccak collides on two strings the theorem names.

The trees are the `rootOf` fold (Specs, "Model boundaries"): for the chain trees, whose
`DynamicIncrementalMerkle` storage has no transcription here, that the stored root is the fold is
obligation O7.
-/

namespace MerkleSpec.DomainSeparation

open AttackVectors.BundleHashEncoding (HashCollision toBytesBE word)
open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf MerkleSpec.Pinned
open MerkleSpec.LastLeafFaithful (LastBatchPathAccepted)
open Contracts.InteropCommitmentTree (Leaf Tree LeafHash leafHashes TreeRootBreak InclusionAccepted
  NonInclusionAccepted Valid root setup threeLeafTree toAbs)

/-! ## (a) Lengths -/

/-- **THE LENGTH TABLE.** The keccak inputs modelled here, with their lengths: node 64; L2 log
leaf and logs-tree padding 88; chain-id leaf, IMT leaf, empty entry and commit value 96; batch
leaf 128; the priority tree's zero 0; the IMT padding `IMT_EMPTY_LEAF_HASH` 34. None depends on the field values: every
field is fixed-width. -/
def Properties.PreimageLengths : Prop :=
  (∀ a b : UInt256, (nodePre a b).length = 64)
    ∧ (∀ log : L2Log, (logPre log).length = 88)
    ∧ logDefaultPre.length = 88
    ∧ (∀ padC chainIdRoot chainId : UInt256, (chainIdPre padC chainIdRoot chainId).length = 96)
    ∧ (∀ ℓ : Leaf, (imtPre ℓ).length = 96)
    ∧ emptyPre.length = 96
    ∧ (∀ (tag : ℕ) (flowId specHash : UInt256), (commitPre tag flowId specHash).length = 96)
    ∧ (∀ padB batchRoot batchNumber l1Timestamp : UInt256,
        (batchPre padB batchRoot batchNumber l1Timestamp).length = 128)
    ∧ zeroLeafPre.length = 0
    ∧ imtEmptyLeafPre.length = 34

/-- **(a) EQUAL HASHES OF DIFFERENT-LENGTH INPUTS ARE A COLLISION ON THOSE TWO INPUTS.** Byte strings
of different lengths differ, so if keccak maps them to the same word, that is a `HashCollision` on
exactly those two strings. With the length table, in the trees modelled here (the IMT, the logs,
chain and shared trees) every leaf-versus-node and padding-versus-node confusion, and in the chain
tree a batch-leaf-versus-empty-entry confusion, is such a collision. (The chain batch root tree
hashes no leaf preimage at all, and the priority tree's leaves are not modelled.) -/
def Properties.CrossLengthEqIsCollision : Prop :=
  ∀ (keccak : Keccak) (x y : List UInt8), x.length ≠ y.length → keccak x = keccak y →
    HashCollision keccak x y

/-- **ITS PREMISES ARE MET ON A LEAF-VERSUS-NODE INSTANCE, AND ITS CONCLUSION IS NOT FORCED.**
For every keccak model `κ`, every IMT leaf `ℓ` and every node pair `(a, b)`: the leaf's 96-byte
preimage and the node's 64-byte preimage differ in length, and `κ` changed at the one string
`imtPre ℓ` (`plantKeccak`) maps the two to the same word. And the length stand-in has no
cross-length collision among strings shorter than `2^256` bytes. -/
def Properties.CrossLengthEqIsCollisionWitness : Prop :=
  (∀ (κ : Keccak) (ℓ : Leaf) (a b : UInt256),
      (imtPre ℓ).length ≠ (nodePre a b).length
        ∧ plantKeccak κ (imtPre ℓ) (nodePre a b) (imtPre ℓ)
          = plantKeccak κ (imtPre ℓ) (nodePre a b) (nodePre a b))
    ∧ ∀ x y : List UInt8, x.length < 256 ^ 32 → y.length < 256 ^ 32 → x.length ≠ y.length →
        ¬ HashCollision lengthKeccak x y

/-! ## (b) The 96-byte family

Four keccak inputs are 96 bytes long: `hashLeaf`'s, `chainIdLeafHash`'s, the empty entry's and
`commitValue`'s. Length cannot separate them; their first word does. -/

/-- **AN IMT LEAF HAS THE EMPTY ENTRY'S PREIMAGE EXACTLY WHEN IT IS THE ZERO LEAF.** For a leaf whose
`nextIndex` fits a `uint256`, `imtPre ℓ = emptyPre` iff `ℓ = ⟨0, 0, 0⟩`. -/
def Properties.ImtPreEqEmptyPreIff : Prop :=
  ∀ ℓ : Leaf, LeafBounded ℓ → (imtPre ℓ = emptyPre ↔ ℓ = ⟨0, 0, 0⟩)

/-- **A CHAIN-ID LEAF NEVER HAS THE EMPTY ENTRY'S PREIMAGE.** Its first word is
`CHAIN_ID_LEAF_PADDING`, the empty entry's is zero. Premise: `padC ≠ 0`, a fact about
`keccak256("zkSync:ChainIdLeaf")` that Lean cannot evaluate. This is the shared tree's
leaf-versus-empty separation (`MessageRootBase.sol:140, 213-214, 287`). -/
def Properties.ChainIdPreNeEmptyPre : Prop :=
  ∀ padC chainIdRoot chainId : UInt256, padC ≠ 0 → chainIdPre padC chainIdRoot chainId ≠ emptyPre

/-- **AN IMT LEAF HAS A CHAIN-ID LEAF'S PREIMAGE ONLY IF ITS VALUE IS THE PADDING TAG.** The first
words are `ℓ.value` and `CHAIN_ID_LEAF_PADDING`. No bound or tag premise is needed. -/
def Properties.ImtPreNeChainIdPreUnlessPadding : Prop :=
  ∀ (ℓ : Leaf) (padC chainIdRoot chainId : UInt256), ℓ.value ≠ padC →
    imtPre ℓ ≠ chainIdPre padC chainIdRoot chainId

/-- **AND THAT EXCEPTION IS EXACT.** For a bounded leaf, `imtPre ℓ = chainIdPre padC r c` iff
`ℓ = ⟨padC, r, c⟩`: the IMT leaf `⟨CHAIN_ID_LEAF_PADDING, chainIdRoot, chainId⟩` is a chain-id leaf
preimage byte for byte. -/
def Properties.ImtPreEqChainIdPreIff : Prop :=
  ∀ (ℓ : Leaf) (padC chainIdRoot chainId : UInt256), LeafBounded ℓ →
    (imtPre ℓ = chainIdPre padC chainIdRoot chainId ↔ ℓ = ⟨padC, chainIdRoot.val, chainId⟩)

/-- **THAT EXCEPTION NEEDS A KECCAK COLLISION.** Every value inserted into the commitment tree is a
commit value `keccak(commitPre tag flowId bundleHash)`: the tree's only appender is the
AtomicFlowManager (`L2InteropCommitmentTree.sol:51-57, 114-116`), which inserts
`AtomicInteropProof.commitValue(flowId, _bundleHash)` (`AtomicFlowManager.sol:168-170`). And
`CHAIN_ID_LEAF_PADDING` is keccak of the 18 bytes `"zkSync:ChainIdLeaf"` (`MessageHashing.sol:16`).
So an IMT leaf carrying a commit value has a chain-id leaf preimage only if keccak collides on the
96-byte commit preimage and those 18 bytes. -/
def Properties.CommitLeafNotChainIdLeafOrCollision : Prop :=
  ∀ (keccak : Keccak) (tag : ℕ) (flowId bundleHash : UInt256) (nextIndex : ℕ)
    (nextValue chainIdRoot chainId : UInt256),
    imtPre ⟨keccak (commitPre tag flowId bundleHash), nextIndex, nextValue⟩
        = chainIdPre (keccak chainIdLeafPaddingPre) chainIdRoot chainId →
      HashCollision keccak (commitPre tag flowId bundleHash) chainIdLeafPaddingPre

/-- **ITS PREMISE IS MET BY ONE PLANTED COLLISION, AND ITS COLLISION IS NOT FORCED.** For every
keccak model `κ`, every flow id and bundle hash, and every chain-id root and chain id: `κ` changed at
the one commit preimage (with the deployed tag value `atomicCommitLeafTagValue`) to collide with
`"zkSync:ChainIdLeaf"` meets the premise, on the leaf `⟨commitValue, chainIdRoot, chainId⟩`. Under
the length stand-in the named collision is false for every commit preimage. -/
def Properties.CommitLeafNotChainIdLeafWitness : Prop :=
  (∀ (κ : Keccak) (flowId bundleHash chainIdRoot chainId : UInt256),
      let keccak := plantKeccak κ (commitPre atomicCommitLeafTagValue flowId bundleHash)
        chainIdLeafPaddingPre
      imtPre
          ⟨keccak (commitPre atomicCommitLeafTagValue flowId bundleHash), chainIdRoot.val, chainId⟩
        = chainIdPre (keccak chainIdLeafPaddingPre) chainIdRoot chainId)
    ∧ ∀ (tag : ℕ) (flowId bundleHash : UInt256),
        ¬ HashCollision lengthKeccak (commitPre tag flowId bundleHash) chainIdLeafPaddingPre

/-- **THE `bytes4` TAG SLOT IS THE WORD `tag · 2^224`.** `abi.encode` left-aligns the `bytes4`
`ATOMIC_COMMIT_LEAF_TAG` in its slot, so the commit-value preimage is three words like the other
96-byte preimages, the first being `tag · 256^28`. (For every `tag`: both sides keep only its low
four bytes.) -/
def Properties.CommitPreIsThreeWords : Prop :=
  ∀ (tag : ℕ) (flowId specHash : UInt256),
    commitPre tag flowId specHash = word (tag * 256 ^ 28) ++ w32 flowId ++ w32 specHash

/-- **A COMMIT-VALUE PREIMAGE IS NEVER THE EMPTY ENTRY'S.** Premise: the tag is nonzero, a fact
about `bytes4(keccak256("AtomicInterop.commit.v1"))` (`IAtomicInterop.sol:82`). -/
def Properties.CommitPreNeEmptyPre : Prop :=
  ∀ (tag : ℕ) (flowId specHash : UInt256), tag < 256 ^ 4 → tag ≠ 0 →
    commitPre tag flowId specHash ≠ emptyPre

/-- **A COMMIT-VALUE PREIMAGE IS AN IMT LEAF PREIMAGE ONLY FOR A LEAF WHOSE VALUE IS THE TAG
WORD.** -/
def Properties.CommitPreNeImtPreUnlessTag : Prop :=
  ∀ (tag : ℕ) (flowId specHash : UInt256) (ℓ : Leaf), tag < 256 ^ 4 →
    ℓ.value.val ≠ tag * 256 ^ 28 → commitPre tag flowId specHash ≠ imtPre ℓ

/-- **A COMMIT-VALUE PREIMAGE IS A CHAIN-ID LEAF PREIMAGE ONLY IF THE TWO TAGS COINCIDE.** That would
need `CHAIN_ID_LEAF_PADDING = ATOMIC_COMMIT_LEAF_TAG · 2^224`, i.e. a keccak output whose low 224
bits are zero. -/
def Properties.CommitPreNeChainIdPreUnlessTag : Prop :=
  ∀ (tag : ℕ) (flowId specHash padC chainIdRoot chainId : UInt256), tag < 256 ^ 4 →
    padC.val ≠ tag * 256 ^ 28 → commitPre tag flowId specHash ≠ chainIdPre padC chainIdRoot chainId

/-- **THE DEPLOYED TAG VALUES MEET THE PREMISES OF THE 96-BYTE FAMILY.** With `padC` the value
`chainIdLeafPaddingValue` and `tag` the value `atomicCommitLeafTagValue` (both computed outside Lean
from the source strings, Specs "Model boundaries"), and the leaf `⟨2, 0, 0⟩`, every premise above
holds at once. And under the first-word stand-in for keccak, none of the separated pairs collides
there. -/
def Properties.NinetySixByteFamilyWitness : Prop :=
  let padC := chainIdLeafPaddingValue
  let tag := atomicCommitLeafTagValue
  let ℓ : Leaf := ⟨2, 0, 0⟩
  padC ≠ 0 ∧ tag < 256 ^ 4 ∧ tag ≠ 0 ∧ LeafBounded ℓ ∧ ℓ.value ≠ padC
    ∧ ℓ.value.val ≠ tag * 256 ^ 28 ∧ padC.val ≠ tag * 256 ^ 28
    ∧ ∀ chainIdRoot chainId flowId specHash : UInt256,
        ¬ HashCollision firstWordKeccak (chainIdPre padC chainIdRoot chainId) emptyPre
        ∧ ¬ HashCollision firstWordKeccak (imtPre ℓ) (chainIdPre padC chainIdRoot chainId)
        ∧ ¬ HashCollision firstWordKeccak (commitPre tag flowId specHash) emptyPre
        ∧ ¬ HashCollision firstWordKeccak (commitPre tag flowId specHash) (imtPre ℓ)
        ∧ ¬ HashCollision firstWordKeccak (commitPre tag flowId specHash)
            (chainIdPre padC chainIdRoot chainId)

/-- **THREE LITERALS AND THE SENTINEL LEAF, ONE VALUE.** `CHAIN_TREE_EMPTY_ENTRY_HASH`,
`SHARED_ROOT_TREE_EMPTY_HASH` and `EMPTY_IMT_ROOT` are the same literal. The IMT sentinel leaf hash
`hashLeaf({0,0,0})` (`imtPadding`, the padding only at the interop pin) is the empty entry's hash
`keccak(new bytes(96))` for EVERY keccak, and so is the root of the freshly set-up IMT at height 0,
whose only leaf is the sentinel (the claim of `ChainBatchRootTree.sol:32-35`). Under the
documented value of `keccak256(new bytes(96))` (`KeccakOfEmptyIsDocumented`), all of them are that
literal. -/
def Properties.EmptyConstantsCoincide : Prop :=
  CHAIN_TREE_EMPTY_ENTRY_HASH = SHARED_ROOT_TREE_EMPTY_HASH
    ∧ SHARED_ROOT_TREE_EMPTY_HASH = EMPTY_IMT_ROOT
    ∧ (∀ keccak : Keccak, imtPadding keccak = emptyEntryHash keccak
        ∧ root (efficientHash keccak) (imtPadding keccak) (hashLeaf keccak) setup 0
            = emptyEntryHash keccak)
    ∧ (∀ keccak : Keccak, KeccakOfEmptyIsDocumented keccak →
        emptyEntryHash keccak = CHAIN_TREE_EMPTY_ENTRY_HASH
          ∧ imtPadding keccak = EMPTY_IMT_ROOT
          ∧ root (efficientHash keccak) (imtPadding keccak) (hashLeaf keccak) setup 0
              = EMPTY_IMT_ROOT)

/-- **THE DOCUMENTED-VALUE PREMISE CONSTRAINS ONE STRING, AND IS SATISFIABLE.** Every keccak model,
changed at the one string `new bytes(96)` to the documented literal, meets it. -/
def Properties.KeccakOfEmptyIsDocumentedSatisfiable : Prop :=
  ∀ κ : Keccak, KeccakOfEmptyIsDocumented
    (Function.update κ emptyPre 0x46700b4d40ac5c35af2c22dda2787a91eb567b06c924a8fb8ae9a05b20c08c21)

/-- **THE LOGS-TREE PADDING PREIMAGE IS THE ALL-ZERO LOG'S.** `new bytes(88)` is the packed encoding
of the log with every field zero. So the logs-tree padding leaf is a log leaf hash, the analogue of
the IMT's zero leaf; `_getProofData` rejects that leaf hash outright (`HashedLogIsDefault`,
`MessageHashing.sol:165-167`). -/
def Properties.LogDefaultIsZeroLog : Prop :=
  logPre zeroLog = logDefaultPre

/-! ## (c) The IMT: the root check down to keccak -/

/-- **EVERY LOCATED BREAK OF THE IMT ROOT CHECK IS A KECCAK COLLISION ON NAMED BYTES, OR THE PADDING
PREIMAGE ITSELF.** For any padding preimage `zPre` that is not 64 bytes long, a `TreeRootBreak` of
the tree with node hash `efficientHash keccak`, leaf hash `hashLeaf keccak` and padding `keccak zPre`
(over bounded leaves) is an `ImtKeccakBreak`, unless the opened index is empty and the presented
leaf's preimage IS `zPre`. -/
def Properties.TreeRootBreakIsKeccakCollision : Prop :=
  ∀ (keccak : Keccak) (zPre : List UInt8) (T : Tree) (height : ℕ) (sibs : ℕ → UInt256)
    (k idx : ℕ) (ℓ : Leaf),
    zPre.length ≠ 64 → TreeBounded T → LeafBounded ℓ →
    TreeRootBreak (efficientHash keccak) (keccak zPre) (hashLeaf keccak) T height sibs k idx ℓ →
      (T.leafCount ≤ idx ∧ imtPre ℓ = zPre) ∨ ImtKeccakBreak keccak zPre T height sibs k idx ℓ

/-- **HEADLINE (a padding preimage of any other length): IMT PROOFS ARE EXCLUSIVE, OR KECCAK COLLIDES
ON NAMED BYTES.** If the padding's preimage is neither 64 bytes (a node's) nor 96 bytes (a leaf's),
the padding forgery is gone: an accepted inclusion proof and an accepted non-inclusion proof for one
value against a valid tree's root mean that one of the two carries an `ImtKeccakBreak`.
`b17415d20`'s padding `IMT_EMPTY_LEAF_HASH = keccak256("zkSync:IndexedMerkleTree:emptyLeaf")`
(`common/Config.sol:141`) has a 34-byte preimage (`imtEmptyLeafPre`, `UpgPaddingLengthOk`). The
verifier is `verifyInclusion`/`verifyNonInclusion` (`IndexedMerkleTree.sol:134-172`) over
`Merkle.calculateRootMemory`. Premises: the tree is `Valid` with bounded stored leaves, the two
presented leaves are bounded (their `nextIndex` fits a `uint256`, as calldata guarantees), and the
root is the `FullMerkle` fold of the stored leaf hashes at the given height (obligation O7; Specs,
"Model boundaries"). -/
@[headline] def Properties.ProofsExclusiveOrKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (zPre : List UInt8), zPre.length ≠ 64 → zPre.length ≠ 96 →
    ∀ (T : Tree), Valid T → TreeBounded T →
    ∀ (height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      LeafBounded ℓ₁ → LeafBounded ℓ₂ →
      InclusionAccepted (efficientHash keccak) (hashLeaf keccak)
        (root (efficientHash keccak) (keccak zPre) (hashLeaf keccak) T height) v ℓ₁ i₁ s₁ k₁ →
      NonInclusionAccepted (efficientHash keccak) (hashLeaf keccak)
        (root (efficientHash keccak) (keccak zPre) (hashLeaf keccak) T height) v ℓ₂ i₂ s₂ k₂ →
        ImtKeccakBreak keccak zPre T height s₁ k₁ i₁ ℓ₁
          ∨ ImtKeccakBreak keccak zPre T height s₂ k₂ i₂ ℓ₂

/-- **ONE ABSENCE PROOF, WITH A PADDING PREIMAGE OF ANY OTHER LENGTH (as at UPG): A RECLAIM WITNESS, OR
A KECCAK COLLISION ON NAMED BYTES.** The padding disjunct of the interop pin's form (History) is gone. -/
def Properties.NonInclusionSoundOrKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (zPre : List UInt8), zPre.length ≠ 64 → zPre.length ≠ 96 →
    ∀ (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      TreeBounded T → LeafBounded ℓ →
      NonInclusionAccepted (efficientHash keccak) (hashLeaf keccak)
        (root (efficientHash keccak) (keccak zPre) (hashLeaf keccak) T height) v ℓ idx sibs k →
        (∃ W ∈ toAbs T, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
          ∨ ImtKeccakBreak keccak zPre T height sibs k idx ℓ

/-- **ONE INCLUSION PROOF, WITH A PADDING PREIMAGE OF ANY OTHER LENGTH (as at UPG): THE VALUE IS IN
THE TREE, OR KECCAK COLLIDES ON NAMED BYTES.** `InclusionSoundOrBreak` instantiated with keccak and a
padding preimage that is neither 64 nor 96 bytes long. No `Valid` premise: the padding exception of
`TreeRootBreakIsKeccakCollision` needs a 96-byte padding preimage, so it cannot occur. -/
def Properties.InclusionSoundOrKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (zPre : List UInt8), zPre.length ≠ 64 → zPre.length ≠ 96 →
    ∀ (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      TreeBounded T → LeafBounded ℓ →
      InclusionAccepted (efficientHash keccak) (hashLeaf keccak)
        (root (efficientHash keccak) (keccak zPre) (hashLeaf keccak) T height) v ℓ idx sibs k →
        v ∈ IMTAbstract.keys (toAbs T) ∨ ImtKeccakBreak keccak zPre T height sibs k idx ℓ

/-- **THE SINGLE-PROOF ABSENCE PREMISES ARE MET ON A THREE-LEAF TREE, WITH NO KECCAK BREAK.** For
every keccak, every padding preimage and every `0 < a < v < b`: on the valid run `threeLeafTree a b`
(leaves `⟨0, 1, a⟩`, `⟨a, 2, b⟩`, `⟨b, 0, 0⟩`) at height 2, the honest absence proof of `v` (low
leaf 1, that index's honest siblings) is accepted, carries no `ImtKeccakBreak`, and its low leaf is
a reclaim witness. (`ProofsExclusiveOrKeccakBreakSatisfiable` and
`PaddingForgeryIsTheOnlyKeccakFreeBreak` meet the absence forms' premises with another disjunct
true: a planted collision, or, at the interop pin's padding, the padding forgery.) -/
def Properties.NonInclusionSoundWitness : Prop :=
  ∀ (keccak : Keccak) (zPre : List UInt8) (a b v : UInt256), 0 < a → a < v → v < b →
    Valid (threeLeafTree a b) ∧ TreeBounded (threeLeafTree a b)
      ∧ LeafBounded ((threeLeafTree a b).leaf 1)
      ∧ NonInclusionAccepted (efficientHash keccak) (hashLeaf keccak)
          (imtRoot keccak zPre (threeLeafTree a b) 2) v ((threeLeafTree a b).leaf 1) 1
          (imtSibs keccak zPre (threeLeafTree a b) 1) 2
      ∧ ¬ ImtKeccakBreak keccak zPre (threeLeafTree a b) 2
          (imtSibs keccak zPre (threeLeafTree a b) 1) 2 1 ((threeLeafTree a b).leaf 1)
      ∧ (∃ W ∈ toAbs (threeLeafTree a b), W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))

/-- **UPG's PADDING PREIMAGE MEETS THE LENGTH CONDITIONS.** It is 34 bytes long. -/
def Properties.UpgPaddingLengthOk : Prop :=
  imtEmptyLeafPre.length ≠ 64 ∧ imtEmptyLeafPre.length ≠ 96

/-- **THE PREMISES OF `ProofsExclusiveOrKeccakBreak` ARE MET, BY ONE PLANTED COLLISION, AND THE BREAK
IT LOCATES IS THAT COLLISION.** For every keccak model `κ` and every `0 < a < b`, with UPG's 34-byte
padding preimage and `κ` changed at the one string `new bytes(96)` (the zero leaf's preimage) to
send it to UPG's padding value: on the valid run `threeLeafTree a b` at height 2, the honest
inclusion proof for `a` (leaf 1) and the padding forgery (the zero leaf at slot 3, with that slot's
honest siblings) are both accepted, and every premise holds. The inclusion proof carries no
`ImtKeccakBreak`; the forgery's is `paddingCollision`, on the zero leaf's 96-byte preimage and UPG's
34-byte padding preimage: the planted collision. So with UPG's padding the interop pin's forgery is
accepted once keccak collides on those two named strings, and that collision is the break located. -/
@[witness] def Properties.ProofsExclusiveOrKeccakBreakSatisfiable : Prop :=
  ∀ (κ : Keccak) (a b : UInt256), 0 < a → a < b →
    let keccak := plantKeccak κ emptyPre imtEmptyLeafPre
    imtEmptyLeafPre.length ≠ 64 ∧ imtEmptyLeafPre.length ≠ 96 ∧ Valid (threeLeafTree a b)
      ∧ TreeBounded (threeLeafTree a b) ∧ LeafBounded ((threeLeafTree a b).leaf 1)
      ∧ LeafBounded ⟨0, 0, 0⟩
      ∧ InclusionAccepted (efficientHash keccak) (hashLeaf keccak)
          (imtRoot keccak imtEmptyLeafPre (threeLeafTree a b) 2) a ((threeLeafTree a b).leaf 1) 1
          (imtSibs keccak imtEmptyLeafPre (threeLeafTree a b) 1) 2
      ∧ NonInclusionAccepted (efficientHash keccak) (hashLeaf keccak)
          (imtRoot keccak imtEmptyLeafPre (threeLeafTree a b) 2) a ⟨0, 0, 0⟩ 3
          (imtSibs keccak imtEmptyLeafPre (threeLeafTree a b) 3) 2
      ∧ ¬ ImtKeccakBreak keccak imtEmptyLeafPre (threeLeafTree a b) 2
          (imtSibs keccak imtEmptyLeafPre (threeLeafTree a b) 1) 2 1 ((threeLeafTree a b).leaf 1)
      ∧ ImtKeccakBreak keccak imtEmptyLeafPre (threeLeafTree a b) 2
          (imtSibs keccak imtEmptyLeafPre (threeLeafTree a b) 3) 2 3 ⟨0, 0, 0⟩
      ∧ HashCollision keccak (imtPre ⟨0, 0, 0⟩) imtEmptyLeafPre

/-- **`ImtKeccakBreak` IS NOT A TAUTOLOGY.** On the honest proof of any occupied index (the tree's
own siblings, at the tree's height, presenting the stored leaf) no keccak break is located, for
every keccak and every padding preimage. -/
def Properties.ImtKeccakBreakNotTautology : Prop :=
  ∀ (keccak : Keccak) (zPre : List UInt8) (T : Tree) (height i : ℕ), i < T.leafCount →
    ¬ ImtKeccakBreak keccak zPre T height
        (honestSibs (efficientHash keccak) (keccak zPre) (leafList keccak (imtLeafPre T) T.leafCount) i)
        height i (T.leaf i)

/-- **`ImtKeccakBreak` FIRES, ON ONE PLANTED COLLISION: A FORGED INCLUSION PROOF.** For every
keccak model `κ`, every padding preimage (UPG's and the pin's among them), every `0 < a < b` and
every value `c` outside `{0, a, b}`: with `κ` changed at the one string `imtPre ⟨c, 0, 0⟩` to send it
where `κ` sends the preimage of leaf 1 (`⟨a, 2, b⟩`), the inclusion proof for `c` that presents
`⟨c, 0, 0⟩` at index 1 with that index's honest siblings is accepted against the root of the valid run
`threeLeafTree a b` at height 2, yet `c` is not in the tree. Its `TreeRootBreak` holds, the padding
exception does not, and the `ImtKeccakBreak` located is `leafCollision` on the two 96-byte leaf
preimages: the planted collision. So the premises of `TreeRootBreakIsKeccakCollision` (and its History form at the
interop pin's padding) and of the inclusion forms are met with their keccak disjunct the one that holds. -/
def Properties.ImtKeccakBreakFires : Prop :=
  ∀ (κ : Keccak) (zPre : List UInt8) (a b c : UInt256),
    0 < a → a < b → c ≠ 0 → c ≠ a → c ≠ b →
    let keccak := plantKeccak κ (imtPre ⟨c, 0, 0⟩) (imtPre ((threeLeafTree a b).leaf 1))
    Valid (threeLeafTree a b) ∧ TreeBounded (threeLeafTree a b) ∧ LeafBounded ⟨c, 0, 0⟩
      ∧ InclusionAccepted (efficientHash keccak) (hashLeaf keccak)
          (imtRoot keccak zPre (threeLeafTree a b) 2) c ⟨c, 0, 0⟩ 1
          (imtSibs keccak zPre (threeLeafTree a b) 1) 2
      ∧ c ∉ IMTAbstract.keys (toAbs (threeLeafTree a b))
      ∧ TreeRootBreak (efficientHash keccak) (keccak zPre) (hashLeaf keccak) (threeLeafTree a b) 2
          (imtSibs keccak zPre (threeLeafTree a b) 1) 2 1 ⟨c, 0, 0⟩
      ∧ ¬ ((threeLeafTree a b).leafCount ≤ 1 ∧ imtPre ⟨c, 0, 0⟩ = zPre)
      ∧ ImtKeccakBreak keccak zPre (threeLeafTree a b) 2
          (imtSibs keccak zPre (threeLeafTree a b) 1) 2 1 ⟨c, 0, 0⟩
      ∧ HashCollision keccak (imtPre ((threeLeafTree a b).leaf 1)) (imtPre ⟨c, 0, 0⟩)

/-! ## (d) The leaf/node and entry/empty premises of the other trees -/

/-- **`accept_forces_height`'s DOMAIN HYPOTHESES HOLD UP TO NAMED COLLISIONS.** For a tree over
`leafList keccak pre n` with padding `keccak zPre`, claimed leaf `keccak xPre`, and node hash
`efficientHash keccak`, under `LeafDomain` (no preimage is 64 bytes): each of `hL` (no entry is a
node hash), `hz0` (the padding is not) and `hx` (the claimed leaf is not), where it fails, fails by
a collision on the entry's (padding's, claimed leaf's) preimage and the node's 64-byte preimage. -/
def Properties.AcceptForcesHeightHypothesesUpToCollision : Prop :=
  ∀ (keccak : Keccak) (pre : ℕ → List UInt8) (n : ℕ) (zPre xPre : List UInt8),
    LeafDomain pre n zPre xPre →
      (∀ y ∈ leafList keccak pre n, ∀ a b : UInt256, y = efficientHash keccak a b →
          ∃ m < n, y = keccak (pre m) ∧ HashCollision keccak (pre m) (nodePre a b))
        ∧ (∀ a b : UInt256, keccak zPre = efficientHash keccak a b →
            HashCollision keccak zPre (nodePre a b))
        ∧ (∀ a b : UInt256, keccak xPre = efficientHash keccak a b →
            HashCollision keccak xPre (nodePre a b))

/-- **THE FOUR TREES MEET `LeafDomain`.** The logs tree (88 / 88 against 64), the chain tree
(128 / 96), the shared tree (96 / 96) and the IMT (96, with `b17415d20`'s 34-byte padding, or the
interop pin's 96-byte one). -/
def Properties.TreeLeafDomains : Prop :=
  (∀ (logs : ℕ → L2Log) (n : ℕ) (log : L2Log),
      LeafDomain (logsTreePre logs) n logDefaultPre (logPre log))
    ∧ (∀ (padB : UInt256) (B : ℕ → BatchLeaf) (n : ℕ) (b : BatchLeaf),
        LeafDomain (chainTreePre padB B) n emptyPre
          (batchPre padB b.batchRoot b.batchNumber b.l1Timestamp))
    ∧ (∀ (padC : UInt256) (C : ℕ → ChainIdLeaf) (n : ℕ) (c : ChainIdLeaf),
        LeafDomain (sharedTreePre padC C) n emptyPre (chainIdPre padC c.chainIdRoot c.chainId))
    ∧ (∀ (T : Tree) (ℓ : Leaf), LeafDomain (imtLeafPre T) T.leafCount pinPaddingPre (imtPre ℓ))
    ∧ (∀ (T : Tree) (ℓ : Leaf), LeafDomain (imtLeafPre T) T.leafCount imtEmptyLeafPre (imtPre ℓ))

/-- **THE CHAIN AND SHARED TREES MEET `EntryDomain`, AND SO DOES THE IMT WITH UPG's PADDING.** No
chain-tree entry preimage is the 96 zero bytes (128 bytes long); no shared-tree entry preimage is
(first word `CHAIN_ID_LEAF_PADDING ≠ 0`); no IMT leaf preimage is UPG's 34-byte padding preimage.
At the interop pin's padding the IMT fails it: right after `setup`, entry 0 is the zero leaf, whose preimage is the
padding preimage (last conjunct). -/
def Properties.TreeEntryDomains : Prop :=
  (∀ (padB : UInt256) (B : ℕ → BatchLeaf) (n : ℕ), EntryDomain (chainTreePre padB B) n emptyPre)
    ∧ (∀ (padC : UInt256) (C : ℕ → ChainIdLeaf) (n : ℕ), padC ≠ 0 →
        EntryDomain (sharedTreePre padC C) n emptyPre)
    ∧ (∀ T : Tree, EntryDomain (imtLeafPre T) T.leafCount imtEmptyLeafPre)
    ∧ ¬ EntryDomain (imtLeafPre setup) setup.leafCount pinPaddingPre

/-- **`LastLeaf.EntriesNotEmpty` HOLDS UP TO A NAMED COLLISION.** For a tree over
`leafList keccak pre n` with empty entry `keccak zPre`, under `EntryDomain`: either no occupied
entry equals the empty entry, or keccak collides on a named entry's preimage and `zPre`. -/
def Properties.EntriesNotEmptyOrCollision : Prop :=
  ∀ (keccak : Keccak) (pre : ℕ → List UInt8) (n : ℕ) (zPre : List UInt8),
    EntryDomain pre n zPre →
      EntriesNotEmpty (keccak zPre) (leafList keccak pre n)
        ∨ ∃ m < n, HashCollision keccak (pre m) zPre

/-- **THE CHAIN TREE: `EntriesNotEmpty` HOLDS UP TO A 128-VERSUS-96-BYTE COLLISION.** No pushed batch
leaf equals `CHAIN_TREE_EMPTY_ENTRY_HASH`, or keccak collides on a named batch's 128-byte preimage
and the 96 zero bytes. This is the domain premise of `LastLeaf`'s pinned results for the tree
`_verifyLastBatchInRoot` checks, with no hash premise and no premise on `BATCH_LEAF_PADDING`. -/
def Properties.ChainTreeEntriesNotEmptyOrCollision : Prop :=
  ∀ (keccak : Keccak) (padB : UInt256) (B : ℕ → BatchLeaf) (n : ℕ),
    EntriesNotEmpty (emptyEntryHash keccak) (leafList keccak (chainTreePre padB B) n)
      ∨ ∃ m < n, HashCollision keccak (chainTreePre padB B m) emptyPre

/-- **THE HYPOTHESES OF (d) ARE MET BY PLANTED COLLISIONS, AND ITS COLLISION DISJUNCTS ARE NOT
FORCED.**

* Under the length stand-in, on any chain tree: the three hash equalities of
  `AcceptForcesHeightHypothesesUpToCollision` all fail (so `accept_forces_height`'s domain
  hypotheses hold outright), and `EntriesNotEmpty` holds outright.
* For every keccak model `κ`, on any chain tree, `κ` changed at one string meets each of those hash
  equalities: an occupied entry, the empty entry, or a claimed batch leaf hashing to a given node
  pair. And `κ` changed at one occupied entry's preimage to send it to the empty entry's value
  makes `EntriesNotEmpty` fail, the collision named by `EntriesNotEmptyOrCollision` being the
  planted one. -/
def Properties.TreeDomainsWitness : Prop :=
  (∀ (padB : UInt256) (B : ℕ → BatchLeaf) (n : ℕ) (b : BatchLeaf),
    (∀ y ∈ leafList lengthKeccak (chainTreePre padB B) n, ∀ a c : UInt256,
        y ≠ efficientHash lengthKeccak a c)
      ∧ (∀ a c : UInt256, lengthKeccak emptyPre ≠ efficientHash lengthKeccak a c)
      ∧ (∀ a c : UInt256, lengthKeccak (batchPre padB b.batchRoot b.batchNumber b.l1Timestamp)
          ≠ efficientHash lengthKeccak a c)
      ∧ EntriesNotEmpty (lengthKeccak emptyPre) (leafList lengthKeccak (chainTreePre padB B) n))
    ∧ (∀ (κ : Keccak) (padB : UInt256) (B : ℕ → BatchLeaf) (n m : ℕ) (a c : UInt256), m < n →
        let keccak := plantKeccak κ (chainTreePre padB B m) (nodePre a c)
        keccak (chainTreePre padB B m) ∈ leafList keccak (chainTreePre padB B) n
          ∧ keccak (chainTreePre padB B m) = efficientHash keccak a c)
    ∧ (∀ (κ : Keccak) (a c : UInt256),
        let keccak := plantKeccak κ emptyPre (nodePre a c)
        keccak emptyPre = efficientHash keccak a c)
    ∧ (∀ (κ : Keccak) (padB : UInt256) (b : BatchLeaf) (a c : UInt256),
        let keccak :=
          plantKeccak κ (batchPre padB b.batchRoot b.batchNumber b.l1Timestamp) (nodePre a c)
        keccak (batchPre padB b.batchRoot b.batchNumber b.l1Timestamp) = efficientHash keccak a c)
    ∧ (∀ (κ : Keccak) (padB : UInt256) (B : ℕ → BatchLeaf) (n m : ℕ), m < n →
        let keccak := plantKeccak κ (chainTreePre padB B m) emptyPre
        ¬ EntriesNotEmpty (keccak emptyPre) (leafList keccak (chainTreePre padB B) n)
          ∧ HashCollision keccak (chainTreePre padB B m) emptyPre)

/-- **A WRONG-LENGTH BREAK IS A KECCAK COLLISION.** Under `LeafDomain`, every `HeightBreak` of the
keccak-instantiated tree is a `HeightKeccakBreak`: each of its four cases is a collision on named
byte strings. -/
def Properties.HeightBreakIsKeccakCollision : Prop :=
  ∀ (keccak : Keccak) (pre : ℕ → List UInt8) (n : ℕ) (zPre xPre : List UInt8)
    (sibs : ℕ → UInt256) (k height j : ℕ),
    LeafDomain pre n zPre xPre →
    HeightBreak (efficientHash keccak) (keccak zPre) (leafList keccak pre n) sibs k height j
        (keccak xPre) →
      HeightKeccakBreak keccak pre n zPre sibs k height j xPre

/-- **`accept_forces_height`, REPAIRED DOWN TO KECCAK.** A walk of any length `k` from any index
`j < 2^k`, accepted against the root at any `height`, has `k = height` or exhibits a
`HeightKeccakBreak`. No hash premise; the domain hypotheses are `LeafDomain`, a length fact. -/
def Properties.AcceptForcesHeightOrKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (pre : ℕ → List UInt8) (n : ℕ) (zPre xPre : List UInt8)
    (sibs : ℕ → UInt256) (k height j : ℕ),
    LeafDomain pre n zPre xPre → j < 2 ^ k →
    walkPure (efficientHash keccak) sibs 0 k j (keccak xPre)
        = rootOf (efficientHash keccak) (keccak zPre) (leafList keccak pre n) height →
      k = height ∨ HeightKeccakBreak keccak pre n zPre sibs k height j xPre

/-- **HEADLINE (any tree): AN ACCEPTED PATH OPENS THE CLAIMED PREIMAGE, OR KECCAK COLLIDES ON NAMED
BYTES.** `accept_pins_entry_any_length` without any hash premise, and down to bytes. For a tree over
`leafList keccak pre n` with padding `keccak zPre`, under `LeafDomain`, a walk accepted against the
root presenting `keccak xPre` has the tree's height and, at its index, the level-0 preimage IS `xPre`
(the entry's if occupied, the padding's if not); or one of:

* keccak collides on that level-0 preimage and `xPre`;
* the right length, and a 64-byte collision on the submitted path (`PathKeccakCollision`);
* a wrong length, located (`HeightKeccakBreak`).

`TreeLeafDomains` instantiates `LeafDomain` for the logs, chain, shared and IMT trees. -/
def Properties.AcceptOpensPreimageOrKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (pre : ℕ → List UInt8) (n : ℕ) (zPre xPre : List UInt8)
    (sibs : ℕ → UInt256) (k height j : ℕ),
    LeafDomain pre n zPre xPre → j < 2 ^ k →
    walkPure (efficientHash keccak) sibs 0 k j (keccak xPre)
        = rootOf (efficientHash keccak) (keccak zPre) (leafList keccak pre n) height →
      (k = height ∧ entryPre pre n zPre j = xPre)
        ∨ (k = height ∧ HashCollision keccak (entryPre pre n zPre j) xPre)
        ∨ (k = height ∧ PathKeccakCollision keccak (keccak zPre) (leafList keccak pre n) sibs 0 k j
            (keccak xPre))
        ∨ HeightKeccakBreak keccak pre n zPre sibs k height j xPre

/-- **THE HONEST PROOF IS ACCEPTED, WITH NO BREAK.** For every keccak and every tree over named
preimages, the honest path of an occupied index `j < 2^height` is accepted, and none of the three
collision disjuncts of `AcceptOpensPreimageOrKeccakBreak` holds on it: the first disjunct is what
holds. -/
def Properties.HonestProofNoKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (pre : ℕ → List UInt8) (n : ℕ) (zPre : List UInt8) (height j : ℕ),
    j < n → j < 2 ^ height →
      walkPure (efficientHash keccak)
          (honestSibs (efficientHash keccak) (keccak zPre) (leafList keccak pre n) j) 0 height j
          (keccak (pre j))
        = rootOf (efficientHash keccak) (keccak zPre) (leafList keccak pre n) height
      ∧ entryPre pre n zPre j = pre j
      ∧ ¬ HashCollision keccak (entryPre pre n zPre j) (pre j)
      ∧ ¬ PathKeccakCollision keccak (keccak zPre) (leafList keccak pre n)
          (honestSibs (efficientHash keccak) (keccak zPre) (leafList keccak pre n) j) 0 height j
          (keccak (pre j))
      ∧ ¬ HeightKeccakBreak keccak pre n zPre
          (honestSibs (efficientHash keccak) (keccak zPre) (leafList keccak pre n) j) height height j
          (pre j)

/-- **THE PREMISES OF `AcceptOpensPreimageOrKeccakBreak` AND ITS OCCUPIED FORM ARE MET, WITH EVERY
COLLISION DISJUNCT FALSE.** For every keccak, every padding tag and every two-batch chain tree at
height 1 (entries `B 0`, `B 1`, empty entry `new bytes(96)`), the honest proof of batch 1 meets every
premise (`LeafDomain`, the claimed preimage is not the padding preimage, `1 < 2^1`, acceptance), opens
the claimed preimage, and carries none of the three collision disjuncts. -/
def Properties.AcceptOpensPreimageWitness : Prop :=
  ∀ (keccak : Keccak) (padB : UInt256) (B : ℕ → BatchLeaf),
    let pre := chainTreePre padB B
    let sibs := honestSibs (efficientHash keccak) (keccak emptyPre) (leafList keccak pre 2) 1
    LeafDomain pre 2 emptyPre (pre 1) ∧ pre 1 ≠ emptyPre ∧ 1 < 2 ^ 1
      ∧ walkPure (efficientHash keccak) sibs 0 1 1 (keccak (pre 1))
          = rootOf (efficientHash keccak) (keccak emptyPre) (leafList keccak pre 2) 1
      ∧ entryPre pre 2 emptyPre 1 = pre 1
      ∧ ¬ HashCollision keccak (entryPre pre 2 emptyPre 1) (pre 1)
      ∧ ¬ PathKeccakCollision keccak (keccak emptyPre) (leafList keccak pre 2) sibs 0 1 1
          (keccak (pre 1))
      ∧ ¬ HeightKeccakBreak keccak pre 2 emptyPre sibs 1 1 1 (pre 1)

/-- **`HeightKeccakBreak` FIRES, ON ONE PLANTED COLLISION: A ZERO-LENGTH PATH PRESENTING A BATCH
LEAF AS THE ROOT.** `Merkle.calculateRootMemory` does not compare the path length with the tree's
height (`ZeroLengthPathAcceptsRoot`). For every keccak model `κ`, every padding tag, every two-batch
chain tree at height 1 (entries `B 0`, `B 1`) and every batch `b` other than those two: with `κ`
changed at the one string `batchPre b` to send it to the root's value, the zero-length path at
index 0 presenting `batchLeafHash(b)` is accepted against the chain root. Every premise of
`ChainTreeProofOpensBatchOrKeccakBreak` holds, with `k = 0 ≠ height = 1`, so only its last disjunct
can hold. The `HeightBreak` holds, so `HeightBreakIsKeccakCollision`'s premises are met (with
`TreeLeafDomains`); and the `HeightKeccakBreak` located is `leafIsNode`, on the 128-byte batch
preimage and the root's 64-byte node preimage: the planted collision. -/
def Properties.HeightKeccakBreakFires : Prop :=
  ∀ (κ : Keccak) (padB : UInt256) (B : ℕ → BatchLeaf) (b : BatchLeaf), b ≠ B 0 → b ≠ B 1 →
    let pre := chainTreePre padB B
    let xPre := batchPre padB b.batchRoot b.batchNumber b.l1Timestamp
    let keccak := plantKeccak κ xPre (nodePre (κ (pre 0)) (κ (pre 1)))
    let sibs : ℕ → UInt256 := fun _ => 0
    0 < 2 ^ 0
      ∧ walkPure (efficientHash keccak) sibs 0 0 0
          (batchLeafHash keccak padB b.batchRoot b.batchNumber b.l1Timestamp)
        = rootOf (efficientHash keccak) (emptyEntryHash keccak) (leafList keccak pre 2) 1
      ∧ HeightBreak (efficientHash keccak) (emptyEntryHash keccak) (leafList keccak pre 2) sibs 0 1 0
          (batchLeafHash keccak padB b.batchRoot b.batchNumber b.l1Timestamp)
      ∧ HeightKeccakBreak keccak pre 2 emptyPre sibs 0 1 0 xPre
      ∧ HashCollision keccak xPre
          (pairPre (treePair (efficientHash keccak) (keccak emptyPre) (leafList keccak pre 2) 0 0))

/-- **AN ACCEPTED PATH OPENS AN OCCUPIED ENTRY WITH EXACTLY THE CLAIMED PREIMAGE, OR KECCAK COLLIDES.**
`AcceptOpensPreimageOrKeccakBreak` when the claimed preimage is not the padding preimage: then the
opened position is occupied, and its entry's preimage IS the claimed one. For the chain tree
(128 versus 96 bytes) and the shared tree (`CHAIN_ID_LEAF_PADDING ≠ 0`) that premise is a byte
fact; for the logs tree it is what `_getProofData`'s default-leaf check gives
(`MessageHashing.sol:165-167`: a leaf hash different from the padding's has a different preimage). -/
def Properties.AcceptOpensOccupiedPreimageOrKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (pre : ℕ → List UInt8) (n : ℕ) (zPre xPre : List UInt8)
    (sibs : ℕ → UInt256) (k height j : ℕ),
    LeafDomain pre n zPre xPre → xPre ≠ zPre → j < 2 ^ k →
    walkPure (efficientHash keccak) sibs 0 k j (keccak xPre)
        = rootOf (efficientHash keccak) (keccak zPre) (leafList keccak pre n) height →
      (k = height ∧ j < n ∧ pre j = xPre)
        ∨ (k = height ∧ HashCollision keccak (entryPre pre n zPre j) xPre)
        ∨ (k = height ∧ PathKeccakCollision keccak (keccak zPre) (leafList keccak pre n) sibs 0 k j
            (keccak xPre))
        ∨ HeightKeccakBreak keccak pre n zPre sibs k height j xPre

/-- **HEADLINE (chain tree): AN ACCEPTED BATCH-LEAF PATH OPENS THAT BATCH, OR KECCAK COLLIDES ON NAMED
BYTES.** A path accepted against a chain root (the `rootOf` fold of the pushed batch leaves with
empty entry `keccak(new bytes(96))`; any path length `k`, any index below `2^k`), presenting the
batch leaf `batchLeafHash(batchRoot, batchNumber, l1Timestamp)`, has the chain tree's height and
opens an occupied position `j` whose pushed batch has exactly those three fields; or keccak collides
on the opened 128-byte (or 96-byte padding) preimage and the claimed one, on a 64-byte node
preimage of the path, or, for a wrong length, as `HeightKeccakBreak` names. So "a batch leaf of
another batch number or root" is a keccak collision. No premise on `BATCH_LEAF_PADDING`. -/
def Properties.ChainTreeProofOpensBatchOrKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (padB : UInt256) (B : ℕ → BatchLeaf) (n : ℕ) (b : BatchLeaf)
    (sibs : ℕ → UInt256) (k height j : ℕ),
    j < 2 ^ k →
    walkPure (efficientHash keccak) sibs 0 k j
        (batchLeafHash keccak padB b.batchRoot b.batchNumber b.l1Timestamp)
      = rootOf (efficientHash keccak) (emptyEntryHash keccak)
          (leafList keccak (chainTreePre padB B) n) height →
      (k = height ∧ j < n ∧ B j = b)
        ∨ (k = height ∧ HashCollision keccak (entryPre (chainTreePre padB B) n emptyPre j)
            (batchPre padB b.batchRoot b.batchNumber b.l1Timestamp))
        ∨ (k = height ∧ PathKeccakCollision keccak (emptyEntryHash keccak)
            (leafList keccak (chainTreePre padB B) n) sibs 0 k j
            (batchLeafHash keccak padB b.batchRoot b.batchNumber b.l1Timestamp))
        ∨ HeightKeccakBreak keccak (chainTreePre padB B) n emptyPre sibs k height j
            (batchPre padB b.batchRoot b.batchNumber b.l1Timestamp)

/-- **HEADLINE (shared tree): AN ACCEPTED CHAIN-ID-LEAF PATH OPENS THAT CHAIN'S LEAF, OR KECCAK
COLLIDES ON NAMED BYTES.** As for the chain tree, against a shared root with empty entry
`SHARED_ROOT_TREE_EMPTY_HASH`, read as `keccak(new bytes(96))`: the path has the shared tree's
height and the opened position is occupied by exactly the presented `(chainIdRoot, chainId)`, or
keccak collides on named bytes as there. So "a chain-id leaf equal to the padding or to another
chain's leaf" is a keccak collision. Premise: `CHAIN_ID_LEAF_PADDING ≠ 0`. -/
def Properties.SharedTreeProofOpensChainOrKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (padC : UInt256) (C : ℕ → ChainIdLeaf) (n : ℕ) (c : ChainIdLeaf)
    (sibs : ℕ → UInt256) (k height j : ℕ),
    padC ≠ 0 → j < 2 ^ k →
    walkPure (efficientHash keccak) sibs 0 k j (chainIdLeafHash keccak padC c.chainIdRoot c.chainId)
      = rootOf (efficientHash keccak) (emptyEntryHash keccak)
          (leafList keccak (sharedTreePre padC C) n) height →
      (k = height ∧ j < n ∧ C j = c)
        ∨ (k = height ∧ HashCollision keccak (entryPre (sharedTreePre padC C) n emptyPre j)
            (chainIdPre padC c.chainIdRoot c.chainId))
        ∨ (k = height ∧ PathKeccakCollision keccak (emptyEntryHash keccak)
            (leafList keccak (sharedTreePre padC C) n) sibs 0 k j
            (chainIdLeafHash keccak padC c.chainIdRoot c.chainId))
        ∨ HeightKeccakBreak keccak (sharedTreePre padC C) n emptyPre sibs k height j
            (chainIdPre padC c.chainIdRoot c.chainId)

/-- **THE TWO TREE HEADLINES' PREMISES ARE MET, WITH THE FIRST DISJUNCT THE ONE THAT HOLDS.** For
every keccak, every batch padding tag, and the deployed `CHAIN_ID_LEAF_PADDING` value
(`chainIdLeafPaddingValue`, computed outside Lean): the honest proof of entry 1 of a two-entry chain
tree, and of a two-entry shared tree, at height 1, meets every premise (`1 < 2^1`, the tag nonzero,
acceptance), opens entry 1, and carries none of the collision disjuncts. -/
def Properties.TreeProofOpensWitness : Prop :=
  ∀ (keccak : Keccak) (padB : UInt256) (B : ℕ → BatchLeaf) (C : ℕ → ChainIdLeaf),
    (1 < 2 ^ 1
      ∧ walkPure (efficientHash keccak)
          (honestSibs (efficientHash keccak) (emptyEntryHash keccak)
            (leafList keccak (chainTreePre padB B) 2) 1) 0 1 1
          (batchLeafHash keccak padB (B 1).batchRoot (B 1).batchNumber (B 1).l1Timestamp)
        = rootOf (efficientHash keccak) (emptyEntryHash keccak)
            (leafList keccak (chainTreePre padB B) 2) 1
      ∧ ¬ HashCollision keccak (entryPre (chainTreePre padB B) 2 emptyPre 1)
          (batchPre padB (B 1).batchRoot (B 1).batchNumber (B 1).l1Timestamp)
      ∧ ¬ PathKeccakCollision keccak (emptyEntryHash keccak)
          (leafList keccak (chainTreePre padB B) 2)
          (honestSibs (efficientHash keccak) (emptyEntryHash keccak)
            (leafList keccak (chainTreePre padB B) 2) 1) 0 1 1
          (batchLeafHash keccak padB (B 1).batchRoot (B 1).batchNumber (B 1).l1Timestamp)
      ∧ ¬ HeightKeccakBreak keccak (chainTreePre padB B) 2 emptyPre
          (honestSibs (efficientHash keccak) (emptyEntryHash keccak)
            (leafList keccak (chainTreePre padB B) 2) 1) 1 1 1
          (batchPre padB (B 1).batchRoot (B 1).batchNumber (B 1).l1Timestamp))
    ∧ (chainIdLeafPaddingValue ≠ 0
      ∧ walkPure (efficientHash keccak)
          (honestSibs (efficientHash keccak) (emptyEntryHash keccak)
            (leafList keccak (sharedTreePre chainIdLeafPaddingValue C) 2) 1) 0 1 1
          (chainIdLeafHash keccak chainIdLeafPaddingValue (C 1).chainIdRoot (C 1).chainId)
        = rootOf (efficientHash keccak) (emptyEntryHash keccak)
            (leafList keccak (sharedTreePre chainIdLeafPaddingValue C) 2) 1
      ∧ ¬ HashCollision keccak (entryPre (sharedTreePre chainIdLeafPaddingValue C) 2 emptyPre 1)
          (chainIdPre chainIdLeafPaddingValue (C 1).chainIdRoot (C 1).chainId)
      ∧ ¬ PathKeccakCollision keccak (emptyEntryHash keccak)
          (leafList keccak (sharedTreePre chainIdLeafPaddingValue C) 2)
          (honestSibs (efficientHash keccak) (emptyEntryHash keccak)
            (leafList keccak (sharedTreePre chainIdLeafPaddingValue C) 2) 1) 0 1 1
          (chainIdLeafHash keccak chainIdLeafPaddingValue (C 1).chainIdRoot (C 1).chainId)
      ∧ ¬ HeightKeccakBreak keccak (sharedTreePre chainIdLeafPaddingValue C) 2 emptyPre
          (honestSibs (efficientHash keccak) (emptyEntryHash keccak)
            (leafList keccak (sharedTreePre chainIdLeafPaddingValue C) 2) 1) 1 1 1
          (chainIdPre chainIdLeafPaddingValue (C 1).chainIdRoot (C 1).chainId))

/-- **THE BATCH AND CHAIN-ID PREIMAGES DETERMINE THEIR FIELDS.** Equal batch-leaf preimages (under
one padding) have equal batch root, number and timestamp; equal chain-id preimages have equal root
and chain id. So two batch leaves, or two chain-id leaves, with different fields and equal hashes
are a keccak collision on two named strings. -/
def Properties.BatchAndChainIdPreimagesInjective : Prop :=
  (∀ (padB : UInt256) (b b' : BatchLeaf),
      batchPre padB b.batchRoot b.batchNumber b.l1Timestamp
          = batchPre padB b'.batchRoot b'.batchNumber b'.l1Timestamp → b = b')
    ∧ ∀ (padC : UInt256) (c c' : ChainIdLeaf),
        chainIdPre padC c.chainIdRoot c.chainId = chainIdPre padC c'.chainIdRoot c'.chainId → c = c'

/-- **THE LAST-LEAF BREAK IS A KECCAK COLLISION.** Under `EntryDomain`, every `PinnedBreak` of the
keccak-instantiated tree is a `PinnedKeccakBreak`. -/
def Properties.PinnedBreakIsKeccakCollision : Prop :=
  ∀ (keccak : Keccak) (pre : ℕ → List UInt8) (n : ℕ) (zPre : List UInt8) (j : ℕ),
    EntryDomain pre n zPre →
    PinnedBreak (efficientHash keccak) (keccak zPre) (leafList keccak pre n) j →
      PinnedKeccakBreak keccak pre n zPre j

/-- **THE LAST-LEAF CHECK, DOWN TO KECCAK (any tree).** `AcceptedLastLeafOrPinnedBreak` for a tree
over `leafList keccak pre n` with empty entry `keccak zPre`, under `EntryDomain`: an accepted path
whose left-child siblings are all the zero cascade is at the last leaf, or keccak collides on named
bytes (`PinnedKeccakBreak` on the subtree that starts at `j + 1`, or `PathKeccakCollision` on the
submitted path). -/
def Properties.AcceptedLastLeafOrKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (pre : ℕ → List UInt8) (n : ℕ) (zPre : List UInt8) (sibs : ℕ → UInt256)
    (height j : ℕ) (x : UInt256),
    EntryDomain pre n zPre → n ≤ 2 ^ height → j < n →
    walkPure (efficientHash keccak) sibs 0 height j x
        = rootOf (efficientHash keccak) (keccak zPre) (leafList keccak pre n) height →
    (∀ l < height, (j / 2 ^ l) % 2 = 0 → sibs l = zeros (efficientHash keccak) (keccak zPre) l) →
      j + 1 = n ∨ PinnedKeccakBreak keccak pre n zPre j
        ∨ PathKeccakCollision keccak (keccak zPre) (leafList keccak pre n) sibs 0 height j x

/-- **HEADLINE (chain tree): `_verifyLastBatchInRoot` IDENTIFIES THE LAST BATCH, OR KECCAK COLLIDES ON
NAMED BYTES.** The chain tree's entries are the batch leaves (`MessageRootBase.sol:207-209`), its
empty entry `CHAIN_TREE_EMPTY_ENTRY_HASH`, read as `keccak(new bytes(96))` (equal to the literal under
`KeccakOfEmptyIsDocumented`), its zero cascade the one `AtomicInteropProof.sol:130-143` checks
against. An accepted path of the tree's height from an occupied index `j` (with at most `2^height`
pushed batches), whose left-child siblings are all that cascade, is at the last pushed batch, or
keccak collides: on a 64-byte node preimage of the subtree starting at `j + 1` and the cascade's, on
the 128-byte preimage of batch `j + 1` and the 96 zero bytes, or on the submitted path. No premise
on `BATCH_LEAF_PADDING`. This is the source comment "wherever the path node is a left child (mask
bit 0), the right sibling must be that level's empty-subtree hash" (`AtomicInteropProof.sol:126-128`)
read as a last-leaf check, in collision form, with the collision named. The path length and the occupied index are premises here; the deployed check fixes
neither (`DeployedLastBatchCheckOrKeccakBreak` takes both from the prover). -/
def Properties.AcceptedLastBatchOrKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (padB : UInt256) (B : ℕ → BatchLeaf) (n : ℕ) (sibs : ℕ → UInt256)
    (height j : ℕ) (x : UInt256),
    n ≤ 2 ^ height → j < n →
    walkPure (efficientHash keccak) sibs 0 height j x
        = rootOf (efficientHash keccak) (emptyEntryHash keccak)
            (leafList keccak (chainTreePre padB B) n) height →
    (∀ l < height, (j / 2 ^ l) % 2 = 0 →
        sibs l = zeros (efficientHash keccak) (emptyEntryHash keccak) l) →
      j + 1 = n ∨ PinnedKeccakBreak keccak (chainTreePre padB B) n emptyPre j
        ∨ PathKeccakCollision keccak (emptyEntryHash keccak) (leafList keccak (chainTreePre padB B) n)
            sibs 0 height j x

/-- **ITS PREMISES ARE SATISFIABLE WITH THE CHECK EXERCISED, AND ITS CONCLUSION IS NOT A
TAUTOLOGY.**

* For every keccak and two batches at height 2, the honest path for batch 1 is accepted and the
  zero check fires (and passes) at level 1.
* Under the length stand-in, two batches at height 1: the honest path for batch 0 is accepted, yet
  batch 0 is not last, and no `PinnedKeccakBreak` and no `PathKeccakCollision` exists. The zero
  check is the premise that instance fails; this follows from `AcceptedLastBatchOrKeccakBreak`
  and is stated outright as `AcceptedLastBatchWitnessFailsZeroCheck` in the Proofs file. -/
def Properties.AcceptedLastBatchWitness : Prop :=
  (∀ (keccak : Keccak) (padB : UInt256) (B : ℕ → BatchLeaf),
      2 ≤ 2 ^ 2 ∧ 1 < 2
        ∧ walkPure (efficientHash keccak)
            (honestSibs (efficientHash keccak) (emptyEntryHash keccak)
              (leafList keccak (chainTreePre padB B) 2) 1) 0 2 1
            (keccak (chainTreePre padB B 1))
          = rootOf (efficientHash keccak) (emptyEntryHash keccak)
              (leafList keccak (chainTreePre padB B) 2) 2
        ∧ (∀ l < 2, (1 / 2 ^ l) % 2 = 0 →
            honestSibs (efficientHash keccak) (emptyEntryHash keccak)
              (leafList keccak (chainTreePre padB B) 2) 1 l
              = zeros (efficientHash keccak) (emptyEntryHash keccak) l)
        ∧ (∃ l < 2, (1 / 2 ^ l) % 2 = 0))
    ∧ ∀ (padB : UInt256) (B : ℕ → BatchLeaf),
        walkPure (efficientHash lengthKeccak)
            (honestSibs (efficientHash lengthKeccak) (emptyEntryHash lengthKeccak)
              (leafList lengthKeccak (chainTreePre padB B) 2) 0) 0 1 0
            (lengthKeccak (chainTreePre padB B 0))
          = rootOf (efficientHash lengthKeccak) (emptyEntryHash lengthKeccak)
              (leafList lengthKeccak (chainTreePre padB B) 2) 1
        ∧ ¬ (0 + 1 = 2 ∨ PinnedKeccakBreak lengthKeccak (chainTreePre padB B) 2 emptyPre 0
            ∨ PathKeccakCollision lengthKeccak (emptyEntryHash lengthKeccak)
                (leafList lengthKeccak (chainTreePre padB B) 2)
                (honestSibs (efficientHash lengthKeccak) (emptyEntryHash lengthKeccak)
                  (leafList lengthKeccak (chainTreePre padB B) 2) 0) 0 1 0
                (lengthKeccak (chainTreePre padB B 0)))

/-- **`PinnedKeccakBreak` FIRES, ON ONE PLANTED COLLISION: A NON-LAST BATCH PASSES THE ZERO CHECK.** For
every keccak model `κ`, every padding tag and every two-batch chain tree at height 1: with `κ` changed
at the one string `batchPre (B 1)` to send it to the empty entry's value, batch 1's leaf equals the
empty entry. Then the honest path of batch 0 is accepted and passes the zero check (its level-0
sibling is the cascade's level-0 value), so every premise of `AcceptedLastBatchOrKeccakBreak` holds,
yet batch 0 is not the last batch. `PinnedBreak` holds (so `PinnedBreakIsKeccakCollision`'s premises
are met, with `TreeEntryDomains`); no `PathKeccakCollision` is located on the honest path; and the
`PinnedKeccakBreak` located is `entryIsEmpty`, on batch 1's 128-byte preimage and the 96 zero bytes:
the planted collision. -/
def Properties.PinnedKeccakBreakFires : Prop :=
  ∀ (κ : Keccak) (padB : UInt256) (B : ℕ → BatchLeaf),
    let pre := chainTreePre padB B
    let keccak := plantKeccak κ (pre 1) emptyPre
    let sibs := honestSibs (efficientHash keccak) (emptyEntryHash keccak) (leafList keccak pre 2) 0
    2 ≤ 2 ^ 1 ∧ 0 < 2
      ∧ walkPure (efficientHash keccak) sibs 0 1 0 (keccak (pre 0))
          = rootOf (efficientHash keccak) (emptyEntryHash keccak) (leafList keccak pre 2) 1
      ∧ (∀ l < 1, (0 / 2 ^ l) % 2 = 0 →
          sibs l = zeros (efficientHash keccak) (emptyEntryHash keccak) l)
      ∧ 0 + 1 ≠ 2
      ∧ PinnedBreak (efficientHash keccak) (emptyEntryHash keccak) (leafList keccak pre 2) 0
      ∧ ¬ PathKeccakCollision keccak (emptyEntryHash keccak) (leafList keccak pre 2) sibs 0 1 0
          (keccak (pre 0))
      ∧ PinnedKeccakBreak keccak pre 2 emptyPre 0
      ∧ HashCollision keccak (pre 1) emptyPre

/-- **HEADLINE (chain tree, as deployed): THE BATCH-LEAF HOP AND `_verifyLastBatchInRoot` PIN THE LAST
PUSHED BATCH, WITH EXACTLY THE PRESENTED FIELDS, OR KECCAK COLLIDES ON NAMED BYTES.** The deployed
checks take the batch-leaf path length `k` and mask `j` from the prover
(`LastLeafFaithful.LastBatchPathAccepted`: `j < 2^k`, the walk recomputes the chain root, and the
zero check over the `k` submitted levels). For a chain tree over the `n ≤ 2^height` pushed batch
leaves, with empty entry `keccak(new bytes(96))`, and a submission presenting
`batchLeafHash(batchRoot, batchNumber, l1Timestamp)` that passes those checks: the path has the
tree's height, `j` is the last pushed batch, and that batch has exactly the three presented fields;
or a `LastBatchKeccakBreak` (a wrong length, located; a padded index with the presented 128-byte
preimage colliding with the 96 zero bytes; the last batch's preimage colliding with the presented
one; a `PinnedKeccakBreak`; or a `PathKeccakCollision`).

This is `LastLeafFaithful.AcceptedLastLeafAnyLengthOrBreak` with the hashes instantiated: the
wrong-length and padded-entry cases, which that topic leaves to hash domain separation, become
collisions on named byte strings. No premise on `BATCH_LEAF_PADDING`. As there, the walk is taken to
reach the chain's own root: the chain-id-leaf hop above it is `SharedTreeProofOpensChainOrKeccakBreak`,
and the two are not composed here.

Premises, in plain words: `keccak` is any function on byte strings (no cryptographic premise);
`BATCH_LEAF_PADDING` is any word; the chain tree holds `n ≤ 2^height` pushed batch leaves and the
chain root the check is run against is their `FullMerkle` fold at `height` with empty entry
`keccak(new bytes(96))` (O7; for `DynamicIncrementalMerkle` storage with at least one push,
`DynamicIncrementalMerkle` topic `Model`, `RunRootIsFold`, at the minimal height); the submission
passes the deployed batch-leaf walk and `_verifyLastBatchInRoot` with the prover's own path length
and mask. Scope: the chain-id-leaf hop above the chain root is not composed with this one. -/
@[headline] def Properties.DeployedLastBatchCheckOrKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (padB : UInt256) (B : ℕ → BatchLeaf) (n : ℕ) (b : BatchLeaf)
    (sibs : ℕ → UInt256) (k height j : ℕ),
    n ≤ 2 ^ height →
    LastBatchPathAccepted (efficientHash keccak) (emptyEntryHash keccak)
        (leafList keccak (chainTreePre padB B) n) height sibs k j
        (batchLeafHash keccak padB b.batchRoot b.batchNumber b.l1Timestamp) →
      (k = height ∧ j + 1 = n ∧ B j = b) ∨ LastBatchKeccakBreak keccak padB B n sibs k height j b

/-- **ITS PREMISES ARE MET ON A DEPLOYED SHAPE WITH THE ZERO CHECK EXERCISED, AND
`LastBatchKeccakBreak` IS NOT A TAUTOLOGY.** For every keccak, every padding tag and every three
pushed batches at height 2 (the height `DynamicIncrementalMerkle.push` reaches with three leaves):
the honest path of batch 2 (that index's siblings in the tree) passes the deployed checks, the zero
check comparing at level 0, where the path goes left, against the empty entry. No
`LastBatchKeccakBreak` holds; the first disjunct does (batch 2 is the last, presented with its own
fields). -/
@[witness] def Properties.DeployedLastBatchCheckWitness : Prop :=
  ∀ (keccak : Keccak) (padB : UInt256) (B : ℕ → BatchLeaf),
    let L := leafList keccak (chainTreePre padB B) 3
    let sibs := honestSibs (efficientHash keccak) (emptyEntryHash keccak) L 2
    3 ≤ 2 ^ 2
      ∧ LastBatchPathAccepted (efficientHash keccak) (emptyEntryHash keccak) L 2 sibs 2 2
          (batchLeafHash keccak padB (B 2).batchRoot (B 2).batchNumber (B 2).l1Timestamp)
      ∧ (2 / 2 ^ 0) % 2 = 0
      ∧ (2 = 2 ∧ 2 + 1 = 3 ∧ B 2 = B 2)
      ∧ ¬ LastBatchKeccakBreak keccak padB B 3 sibs 2 2 2 (B 2)

/-- **THE PADDED-ENTRY CASE FIRES, ON ONE PLANTED COLLISION: AN EMPTY SLOT PASSES AS THE LAST
BATCH.** For every keccak model `κ`, every padding tag, every three pushed batches at height 2 and
every batch `b`: with `κ` changed at the one string `batchPre b` to send it where `κ` sends the 96
zero bytes, the submission presenting `batchLeafHash(b)` at the empty slot 3, with that slot's
honest siblings, passes the deployed checks (slot 3 is a right child at both levels, so the zero
check compares nothing). Slot 3 is past the three pushed batches, so the first disjunct of
`DeployedLastBatchCheckOrKeccakBreak` fails; the break located is `paddedEntry`, on `b`'s 128-byte
preimage and the 96 zero bytes: the planted collision. -/
def Properties.DeployedLastBatchPaddedEntryFires : Prop :=
  ∀ (κ : Keccak) (padB : UInt256) (B : ℕ → BatchLeaf) (b : BatchLeaf),
    let xPre := batchPre padB b.batchRoot b.batchNumber b.l1Timestamp
    let keccak := plantKeccak κ xPre emptyPre
    let L := leafList keccak (chainTreePre padB B) 3
    let sibs := honestSibs (efficientHash keccak) (emptyEntryHash keccak) L 3
    3 ≤ 2 ^ 2
      ∧ LastBatchPathAccepted (efficientHash keccak) (emptyEntryHash keccak) L 2 sibs 2 3
          (batchLeafHash keccak padB b.batchRoot b.batchNumber b.l1Timestamp)
      ∧ 3 + 1 ≠ 3
      ∧ LastBatchKeccakBreak keccak padB B 3 sibs 2 2 3 b
      ∧ HashCollision keccak xPre emptyPre

/-! ## (e) The node-collision lift -/

/-- **A NODE-HASH COLLISION ON TWO PAIRS IS A KECCAK COLLISION ON THEIR 64-BYTE PREIMAGES.** The node
preimage is injective (two words), so distinct pairs have distinct preimages, and conversely. -/
def Properties.PairCollisionIsKeccakCollision : Prop :=
  ∀ (keccak : Keccak) (p q : UInt256 × UInt256),
    (p ≠ q ∧ efficientHash keccak p.1 p.2 = efficientHash keccak q.1 q.2)
      ↔ HashCollision keccak (pairPre p) (pairPre q)

/-- **THE NODE-COLLISION LIFT.** With the node hash instantiated as `efficientHash keccak`:

* `Verifier.PathCollision` is exactly `PathKeccakCollision`;
* the premises of `LastLeaf.PinnedBreak.nodeCollision` are exactly a keccak collision on the two
  named 64-byte preimages (the node over the subtree at `j + 1`, and the zero cascade's);
* `RootForgeryPinned.LevelCollision` is exactly a keccak collision on two named parent preimages.

Each is an equivalence, so nothing is lost: each of these located node collisions (and, by
`TreeAndWalkCollisionLift`, `TreeCollision` and `WalkCollision`) is a `HashCollision keccak` on two
64-byte strings. -/
def Properties.NodeCollisionLift : Prop :=
  ∀ keccak : Keccak,
    (∀ (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (lvl k j : ℕ) (x : UInt256),
        PathCollision (efficientHash keccak) z0 L sibs lvl k j x
          ↔ PathKeccakCollision keccak z0 L sibs lvl k j x)
      ∧ (∀ (z0 : UInt256) (L : List UInt256) (l m : ℕ),
          (childPair (efficientHash keccak) z0 L l m ≠ zeroPair (efficientHash keccak) z0 l
            ∧ efficientHash keccak (childPair (efficientHash keccak) z0 L l m).1
                (childPair (efficientHash keccak) z0 L l m).2
              = efficientHash keccak (zeroPair (efficientHash keccak) z0 l).1
                (zeroPair (efficientHash keccak) z0 l).2)
          ↔ HashCollision keccak (pairPre (childPair (efficientHash keccak) z0 L l m))
              (pairPre (zeroPair (efficientHash keccak) z0 l)))
      ∧ (∀ (z : UInt256) (L₁ L₂ : List UInt256),
          LevelCollision (efficientHash keccak) z L₁ L₂
            ↔ ∃ m < (L₁.length + 1) / 2,
                HashCollision keccak (pairPre (parentPair z L₁ m)) (pairPre (parentPair z L₂ m)))

/-- **THE SAME FOR THE TREE-VERSUS-TREE AND WALK-VERSUS-WALK COLLISIONS** of `RootForgeryPinned`. -/
def Properties.TreeAndWalkCollisionLift : Prop :=
  ∀ keccak : Keccak,
    (∀ (z0 : UInt256) (L₁ L₂ : List UInt256) (height i : ℕ),
        TreeCollision (efficientHash keccak) z0 L₁ L₂ height i
          ↔ ∃ l < height,
              HashCollision keccak (pairPre (treePair (efficientHash keccak) z0 L₁ l (i / 2 ^ l)))
                (pairPre (treePair (efficientHash keccak) z0 L₂ l (i / 2 ^ l))))
      ∧ (∀ (s₁ s₂ : ℕ → UInt256) (lvl k j : ℕ) (x y : UInt256),
          WalkCollision (efficientHash keccak) s₁ s₂ lvl k j x y
            ↔ ∃ i < k,
                HashCollision keccak (pairPre (walkPair (efficientHash keccak) s₁ lvl j x i))
                  (pairPre (walkPair (efficientHash keccak) s₂ lvl j y i)))

/-- **THE LIFTED PREDICATES ARE NOT TAUTOLOGIES.** For every keccak: on the honest path no
`PathKeccakCollision` is located, and a level compared with itself has no collision. -/
def Properties.NodeCollisionLiftWitness : Prop :=
  ∀ keccak : Keccak,
    (∀ (z0 : UInt256) (L : List UInt256) (height j : ℕ),
        ¬ PathKeccakCollision keccak z0 L (honestSibs (efficientHash keccak) z0 L j) 0 height j
            (L.getD j z0))
      ∧ ∀ (z : UInt256) (L : List UInt256), ¬ LevelCollision (efficientHash keccak) z L L

end MerkleSpec.DomainSeparation
