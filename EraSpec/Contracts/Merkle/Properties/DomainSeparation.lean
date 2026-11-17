import EraSpec.Contracts.Merkle.Specs.DomainSeparation

/-!
# Properties: every Merkle domain premise is a keccak collision on two named byte strings

Statements about `../Specs/DomainSeparation.lean`. Proofs: `../Proofs/DomainSeparation.lean`.

No property here assumes anything about `keccak`. Each one either is a byte-level fact about the
preimages (lengths, first words, injectivity of the fixed-width encodings), or turns an abstract
domain premise, or an abstract located break, into `HashCollision keccak x y` with `x` and `y`
named by the instance. A collision conclusion that names its inputs can be false, unlike "some
collision exists" (ASSUMPTIONS.md, "Results whose premises cannot hold"); the witnesses at the end
of each group show it false on concrete instances.

Groups, in order:

* (a) the length table, and equal hashes of different-length inputs;
* (b) the 96-byte family (`hashLeaf`, `chainIdLeafHash`, the empty entry, `commitValue`) and the
  four coinciding empty constants;
* (c) the fields of `TreeRoot.HashAssumptions` at the pin, and the IMT root check down to keccak:
  `TreeRootBreakIsKeccakCollision`, and the headlines `ProofsExclusiveOrKeccakBreakAtPin` (the
  forged-absence bug is the only keccak-free break) and `ProofsExclusiveOrKeccakBreak` (with a
  padding preimage of any other length, as at UPG, there is none), with their single-proof forms
  `InclusionSoundOrKeccakBreakAtPin`, `NonInclusionSoundOrKeccakBreakAtPin` and
  `NonInclusionSoundOrKeccakBreak`;
* (d) `Verifier.accept_forces_height`'s domain hypotheses and `LastLeaf.EntriesNotEmpty`, for the
  logs, chain, shared and IMT trees, with the headlines `AcceptOpensPreimageOrKeccakBreak` (any
  tree), `ChainTreeProofOpensBatchOrKeccakBreak`, `SharedTreeProofOpensChainOrKeccakBreak` and
  `AcceptedLastBatchOrKeccakBreak`;
* (e) the node-collision lift: `PathCollision`, `PinnedBreak.nodeCollision`, `LevelCollision`,
  `TreeCollision` and `WalkCollision` each are 64-byte keccak collisions.

Where the content lies. For (a), (b) and the single-premise forms of (c) and (d), the content is
that the two named byte strings DIFFER; the collision form then follows from the definition of
`HashCollision`. The composed results of (c) and (d) carry protocol content: an accepted proof opens
the tree at the claimed preimage, or keccak collides on two strings the theorem names.
-/

namespace MerkleSpec.DomainSeparation

open AttackVectors.BundleHashEncoding (HashCollision toBytesBE word)
open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf MerkleSpec.Pinned
open Contracts.InteropCommitmentTree (Leaf Tree LeafHash leafHashes TreeRootBreak InclusionAccepted
  NonInclusionAccepted Valid root setup threeLeafTree toAbs)

/-! ## (a) Lengths -/

/-- **THE LENGTH TABLE.** The keccak inputs of the corpus, with their lengths: node 64; L2 log
leaf and logs-tree padding 88; chain-id leaf, IMT leaf, empty entry and commit value 96; batch
leaf 128; the priority tree's zero 0; UPG's IMT padding 34. None depends on the field values: every
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
exactly those two strings. With the length table, every leaf-versus-node, padding-versus-node and
batch-leaf-versus-empty-entry confusion in the corpus is such a collision. -/
def Properties.CrossLengthEqIsCollision : Prop :=
  ∀ (keccak : Keccak) (x y : List UInt8), x.length ≠ y.length → keccak x = keccak y →
    HashCollision keccak x y

/-- **ITS PREMISES ARE SATISFIABLE, AND ITS CONCLUSION IS NOT FORCED.** Some keccak model maps two
strings of different lengths to the same word (the constant one), and some keccak model has no
cross-length collision among strings shorter than `2^256` bytes (the length function). -/
def Properties.CrossLengthEqIsCollisionWitness : Prop :=
  (∃ (keccak : Keccak) (x y : List UInt8), x.length ≠ y.length ∧ keccak x = keccak y)
    ∧ ∀ x y : List UInt8, x.length < 256 ^ 32 → y.length < 256 ^ 32 → x.length ≠ y.length →
        ¬ HashCollision lengthKeccak x y

/-! ## (b) The 96-byte family

Four keccak inputs are 96 bytes long: `hashLeaf`'s, `chainIdLeafHash`'s, the empty entry's and
`commitValue`'s. Length cannot separate them; their first word does. -/

/-- **THE ZERO LEAF'S PREIMAGE IS THE EMPTY ENTRY'S.** `abi.encode(0, 0, 0)` is 96 zero bytes, so
the pin's IMT padding `hashLeaf({0, 0, 0})` (`IndexedMerkleTree.sol:47-48`) has the same keccak
input as `new bytes(96)`. -/
def Properties.PinPaddingIsEmptyPre : Prop :=
  pinPaddingPre = emptyPre

/-- **AN IMT LEAF HAS THE EMPTY ENTRY'S PREIMAGE EXACTLY WHEN IT IS THE ZERO LEAF.** For a leaf whose
`nextIndex` fits a `uint256`, `imtPre ℓ = emptyPre` iff `ℓ = ⟨0, 0, 0⟩`. -/
def Properties.ImtPreEqEmptyPreIff : Prop :=
  ∀ ℓ : Leaf, LeafBounded ℓ → (imtPre ℓ = emptyPre ↔ ℓ = ⟨0, 0, 0⟩)

/-- **A CHAIN-ID LEAF NEVER HAS THE EMPTY ENTRY'S PREIMAGE.** Its first word is
`CHAIN_ID_LEAF_PADDING`, the empty entry's is zero. Premise: `padC ≠ 0`, a fact about
`keccak256("zkSync:ChainIdLeaf")` that Lean cannot evaluate. This is the shared tree's
leaf-versus-empty separation (`MessageRootBase.sol:164, 264-265, 352`). -/
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

/-- **AT THE PIN, THAT EXCEPTION NEEDS A KECCAK COLLISION.** Every value the pin inserts into the IMT
is a commit value `keccak(commitPre tag flowId bundleHash)`: the tree's only appender is the
AtomicFlowManager (`L2InteropCommitmentTree.sol:53-57, 82-84`), which inserts
`AtomicInteropProof.commitValue(_flowId, _bundleHash)` (`AtomicFlowManager.sol:97-99`). And
`CHAIN_ID_LEAF_PADDING` is keccak of the 18 bytes `"zkSync:ChainIdLeaf"` (`MessageHashing.sol:16`).
So an IMT leaf carrying a commit value has a chain-id leaf preimage only if keccak collides on the
96-byte commit preimage and those 18 bytes. -/
def Properties.CommitLeafNotChainIdLeafOrCollision : Prop :=
  ∀ (keccak : Keccak) (tag : ℕ) (flowId bundleHash : UInt256) (nextIndex : ℕ)
    (nextValue chainIdRoot chainId : UInt256),
    imtPre ⟨keccak (commitPre tag flowId bundleHash), nextIndex, nextValue⟩
        = chainIdPre (keccak chainIdLeafPaddingPre) chainIdRoot chainId →
      HashCollision keccak (commitPre tag flowId bundleHash) chainIdLeafPaddingPre

/-- **ITS PREMISE IS SATISFIABLE, AND ITS COLLISION IS NOT FORCED.** Under the constant keccak the
premise holds (every commit value and the tag are `0`); under the length stand-in the named
collision is false for every commit preimage. -/
def Properties.CommitLeafNotChainIdLeafWitness : Prop :=
  (∃ (keccak : Keccak) (tag : ℕ) (flowId bundleHash : UInt256) (nextIndex : ℕ)
      (nextValue chainIdRoot chainId : UInt256),
      imtPre ⟨keccak (commitPre tag flowId bundleHash), nextIndex, nextValue⟩
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
about `bytes4(keccak256("AtomicInterop.commit.v1"))` (`IAtomicInterop.sol:94`). -/
def Properties.CommitPreNeEmptyPre : Prop :=
  ∀ (tag : ℕ) (flowId specHash : UInt256), tag < 256 ^ 4 → tag ≠ 0 →
    commitPre tag flowId specHash ≠ emptyPre

/-- **A COMMIT-VALUE PREIMAGE IS AN IMT LEAF PREIMAGE ONLY FOR A LEAF WHOSE VALUE IS THE TAG WORD.** -/
def Properties.CommitPreNeImtPreUnlessTag : Prop :=
  ∀ (tag : ℕ) (flowId specHash : UInt256) (ℓ : Leaf), tag < 256 ^ 4 →
    ℓ.value.val ≠ tag * 256 ^ 28 → commitPre tag flowId specHash ≠ imtPre ℓ

/-- **A COMMIT-VALUE PREIMAGE IS A CHAIN-ID LEAF PREIMAGE ONLY IF THE TWO TAGS COINCIDE.** That would
need `CHAIN_ID_LEAF_PADDING = ATOMIC_COMMIT_LEAF_TAG · 2^224`, i.e. a keccak output whose low 224
bits are zero. -/
def Properties.CommitPreNeChainIdPreUnlessTag : Prop :=
  ∀ (tag : ℕ) (flowId specHash padC chainIdRoot chainId : UInt256), tag < 256 ^ 4 →
    padC.val ≠ tag * 256 ^ 28 → commitPre tag flowId specHash ≠ chainIdPre padC chainIdRoot chainId

/-- **THE PREMISES OF THE 96-BYTE FAMILY ARE JOINTLY SATISFIABLE.** One choice of tags and leaf
meets every premise above at once: `padC = 1`, `tag = 1`, and the leaf `⟨2, 0, 0⟩`. And under the
first-word stand-in for keccak, none of the separated pairs collides there. -/
def Properties.NinetySixByteFamilyWitness : Prop :=
  ∃ (padC : UInt256) (tag : ℕ) (ℓ : Leaf),
    padC ≠ 0 ∧ tag < 256 ^ 4 ∧ tag ≠ 0 ∧ LeafBounded ℓ ∧ ℓ.value ≠ padC
      ∧ ℓ.value.val ≠ tag * 256 ^ 28 ∧ padC.val ≠ tag * 256 ^ 28
      ∧ ∀ chainIdRoot chainId flowId specHash : UInt256,
          ¬ HashCollision firstWordKeccak (chainIdPre padC chainIdRoot chainId) emptyPre
          ∧ ¬ HashCollision firstWordKeccak (imtPre ℓ) (chainIdPre padC chainIdRoot chainId)
          ∧ ¬ HashCollision firstWordKeccak (commitPre tag flowId specHash) emptyPre
          ∧ ¬ HashCollision firstWordKeccak (commitPre tag flowId specHash) (imtPre ℓ)
          ∧ ¬ HashCollision firstWordKeccak (commitPre tag flowId specHash)
              (chainIdPre padC chainIdRoot chainId)

/-- **FOUR CONSTANTS, ONE VALUE.** `CHAIN_TREE_EMPTY_ENTRY_HASH`, `SHARED_ROOT_TREE_EMPTY_HASH` and
`EMPTY_IMT_ROOT` are the same literal. The pin's IMT padding `hashLeaf({0,0,0})` is the empty
entry's hash for EVERY keccak, and so is the root of the freshly set-up IMT at height 0 (the claim
of `ChainBatchRootTree.sol:50-54`). Under the documented value of `keccak256(new bytes(96))`, all
of them are that literal. -/
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

/-- **THE DOCUMENTED-VALUE PREMISE IS SATISFIABLE.** Some keccak model maps `new bytes(96)` to the
documented literal. -/
def Properties.KeccakOfEmptyIsDocumentedSatisfiable : Prop :=
  ∃ keccak : Keccak, KeccakOfEmptyIsDocumented keccak

/-- **THE LOGS-TREE PADDING PREIMAGE IS THE ALL-ZERO LOG'S.** `new bytes(88)` is the packed encoding
of the log with every field zero. So the logs-tree padding leaf is a log leaf hash, the analogue of
the IMT's zero leaf; `_getProofData` rejects that leaf hash outright (`HashedLogIsDefault`,
`MessageHashing.sol:165-169`). -/
def Properties.LogDefaultIsZeroLog : Prop :=
  logPre zeroLog = logDefaultPre

/-! ## (c) The IMT: `HashAssumptions` at the pin, and the root check down to keccak -/

/-- **THE FIELDS OF `TreeRoot.HashAssumptions`, INSTANTIATED WITH KECCAK AT THE PIN.** With node hash
`efficientHash keccak`, leaf hash `hashLeaf keccak` and padding `imtPadding keccak = hashLeaf({0,0,0})`:

* `nodeInj` and `leafInj` hold up to a collision on the two named preimages (for `leafInj`, of
  bounded leaves);
* `leafNotNode` and `padNotNode` hold up to a collision on the named 96-byte and 64-byte preimages;
* `padNotLeaf` is refuted EXACTLY at `⟨0, 0, 0⟩`: a bounded leaf hashes to the padding iff it is
  the zero leaf, or its preimage collides with the 96 zero bytes. (The failure at `⟨0, 0, 0⟩` is
  the known `PaddingCollisionRefundsDeliveredLeg`.) -/
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

/-- **THOSE PREMISES ARE SATISFIABLE, AND THE COLLISION DISJUNCTS ARE NOT FORCED.**

* Under the constant keccak every hash equality in the premises holds, so each premise is met.
* Under the length stand-in, `leafNotNode` and `padNotNode` hold outright: no leaf and not the
  padding hashes to a node (96 versus 64).
* For every keccak, the zero leaf hashes to the padding with no collision: the refutation of
  `padNotLeaf` needs no cryptographic work.
* Under the first-word stand-in, a bounded leaf with nonzero value neither hashes to the padding
  nor collides with the 96 zero bytes. -/
def Properties.HashAssumptionsFieldsWitness : Prop :=
  (∀ (ℓ : Leaf) (a b : UInt256), hashLeaf constKeccak ℓ = efficientHash constKeccak a b
      ∧ imtPadding constKeccak = efficientHash constKeccak a b)
    ∧ (∀ (ℓ : Leaf) (a b : UInt256), hashLeaf lengthKeccak ℓ ≠ efficientHash lengthKeccak a b
        ∧ imtPadding lengthKeccak ≠ efficientHash lengthKeccak a b)
    ∧ (∀ keccak : Keccak, hashLeaf keccak ⟨0, 0, 0⟩ = imtPadding keccak
        ∧ ¬ HashCollision keccak (imtPre ⟨0, 0, 0⟩) emptyPre)
    ∧ (∀ ℓ : Leaf, LeafBounded ℓ → ℓ.value ≠ 0 →
        hashLeaf firstWordKeccak ℓ ≠ imtPadding firstWordKeccak
          ∧ ¬ HashCollision firstWordKeccak (imtPre ℓ) emptyPre)

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
  forged-absence bug, `PaddingCollisionRefundsDeliveredLeg`; no keccak work);
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

/-- **HEADLINE (a padding preimage of any other length): IMT PROOFS ARE EXCLUSIVE, OR KECCAK COLLIDES
ON NAMED BYTES.** If the padding's preimage is neither 64 bytes (a node's) nor 96 bytes (a leaf's),
the padding forgery is gone: an accepted inclusion proof and an accepted non-inclusion proof for one
value against a valid tree's root mean that one of the two carries an `ImtKeccakBreak`. UPG's
`IMT_EMPTY_LEAF_HASH = keccak256("zkSync:IndexedMerkleTree:emptyLeaf")` has a 34-byte preimage
(`imtEmptyLeafPre`); UPG's verifier (`verifyInclusion`, `verifyNonInclusion`, `hashLeaf`,
`Merkle.sol`) is unchanged from the pin, and its `setup` differs only in that padding. -/
def Properties.ProofsExclusiveOrKeccakBreak : Prop :=
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
carries an `ImtKeccakBreak`. This is the form the timeout and refund gates consume. -/
def Properties.NonInclusionSoundOrKeccakBreakAtPin : Prop :=
  ∀ (keccak : Keccak) (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ)
    (sibs : ℕ → UInt256) (k : ℕ),
    TreeBounded T → LeafBounded ℓ →
    NonInclusionAccepted (efficientHash keccak) (hashLeaf keccak)
      (root (efficientHash keccak) (imtPadding keccak) (hashLeaf keccak) T height) v ℓ idx sibs k →
      (∃ W ∈ toAbs T, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
        ∨ (T.leafCount ≤ idx ∧ ℓ = ⟨0, 0, 0⟩)
        ∨ ImtKeccakBreak keccak pinPaddingPre T height sibs k idx ℓ

/-- **ONE ABSENCE PROOF, WITH A PADDING PREIMAGE OF ANY OTHER LENGTH (as at UPG): A RECLAIM WITNESS, OR
A KECCAK COLLISION ON NAMED BYTES.** The padding disjunct of the pin form is gone. -/
def Properties.NonInclusionSoundOrKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (zPre : List UInt8), zPre.length ≠ 64 → zPre.length ≠ 96 →
    ∀ (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      TreeBounded T → LeafBounded ℓ →
      NonInclusionAccepted (efficientHash keccak) (hashLeaf keccak)
        (root (efficientHash keccak) (keccak zPre) (hashLeaf keccak) T height) v ℓ idx sibs k →
        (∃ W ∈ toAbs T, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
          ∨ ImtKeccakBreak keccak zPre T height sibs k idx ℓ

/-- **THE SINGLE-PROOF PREMISES ARE SATISFIABLE, WITH NO KECCAK BREAK.** For every keccak and every
padding preimage, the honest absence proof of the value `5` in the freshly set-up tree (the sentinel
as low leaf, at height 0) is accepted, carries no `ImtKeccakBreak`, and its low leaf is a reclaim
witness. (For the pin's inclusion form, `PaddingForgeryIsTheOnlyKeccakFreeBreak`'s honest inclusion
proof meets the premises with no keccak break; its padding forgery meets the absence form's premises
with only the padding disjunct true.) -/
def Properties.NonInclusionSoundWitness : Prop :=
  ∀ (keccak : Keccak) (zPre : List UInt8),
    TreeBounded setup ∧ LeafBounded ⟨0, 0, 0⟩
      ∧ NonInclusionAccepted (efficientHash keccak) (hashLeaf keccak)
          (root (efficientHash keccak) (keccak zPre) (hashLeaf keccak) setup 0) 5 ⟨0, 0, 0⟩ 0
          (honestSibs (efficientHash keccak) (keccak zPre) (leafHashes (hashLeaf keccak) setup) 0) 0
      ∧ ¬ ImtKeccakBreak keccak zPre setup 0
          (honestSibs (efficientHash keccak) (keccak zPre) (leafHashes (hashLeaf keccak) setup) 0)
          0 0 ⟨0, 0, 0⟩
      ∧ (∃ W ∈ toAbs setup, W.key < 5 ∧ (W.nextKey = 0 ∨ 5 < W.nextKey))

/-- **UPG's PADDING PREIMAGE MEETS THE LENGTH CONDITIONS.** It is 34 bytes long. -/
def Properties.UpgPaddingLengthOk : Prop :=
  imtEmptyLeafPre.length ≠ 64 ∧ imtEmptyLeafPre.length ≠ 96

/-- **AT THE PIN THE PADDING DISJUNCT CANNOT BE DROPPED, AND THE KECCAK BREAKS ARE NOT TAUTOLOGIES.**
For EVERY keccak and every `0 < a < b`, on the valid run `threeLeafTree a b` at height 2 with the
pin's padding: the honest inclusion proof for `a` (leaf 1) and the padding forgery (the zero leaf
at slot 3) meet every premise of `ProofsExclusiveOrKeccakBreakAtPin`; neither proof carries an
`ImtKeccakBreak`; and the forgery's `TreeRootBreak` holds, so `TreeRootBreakIsKeccakCollisionAtPin`'s
premises are met too, with its keccak disjunct false. -/
def Properties.PaddingForgeryIsTheOnlyKeccakFreeBreak : Prop :=
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

/-- **THE PREMISES OF `ProofsExclusiveOrKeccakBreak` ARE SATISFIABLE.** With UPG's padding preimage,
under the constant keccak (every pair of distinct strings collides), `threeLeafTree 1 2` at height 2
has an accepted inclusion proof and an accepted non-inclusion proof for the value `1`. The
conclusion then holds by a located keccak collision. -/
def Properties.ProofsExclusiveOrKeccakBreakSatisfiable : Prop :=
  ∃ (keccak : Keccak) (zPre : List UInt8) (T : Tree) (height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf)
    (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
    zPre.length ≠ 64 ∧ zPre.length ≠ 96 ∧ Valid T ∧ TreeBounded T ∧ LeafBounded ℓ₁ ∧ LeafBounded ℓ₂
      ∧ InclusionAccepted (efficientHash keccak) (hashLeaf keccak)
          (root (efficientHash keccak) (keccak zPre) (hashLeaf keccak) T height) v ℓ₁ i₁ s₁ k₁
      ∧ NonInclusionAccepted (efficientHash keccak) (hashLeaf keccak)
          (root (efficientHash keccak) (keccak zPre) (hashLeaf keccak) T height) v ℓ₂ i₂ s₂ k₂

/-- **`ImtKeccakBreak` IS NOT A TAUTOLOGY.** On the honest proof of any occupied index (the tree's
own siblings, at the tree's height, presenting the stored leaf) no keccak break is located, for
every keccak and every padding preimage. -/
def Properties.ImtKeccakBreakNotTautology : Prop :=
  ∀ (keccak : Keccak) (zPre : List UInt8) (T : Tree) (height i : ℕ), i < T.leafCount →
    ¬ ImtKeccakBreak keccak zPre T height
        (honestSibs (efficientHash keccak) (keccak zPre) (leafList keccak (imtLeafPre T) T.leafCount) i)
        height i (T.leaf i)

/-- **`ImtKeccakBreak` FIRES.** Under the constant keccak, with UPG's padding preimage, a forged
inclusion proof for a value the `setup` tree does not hold is accepted; its `TreeRootBreak` holds,
the padding exception does not, and the break located is an `ImtKeccakBreak`. So the premises of
`TreeRootBreakIsKeccakCollision` are satisfiable away from the exception. -/
def Properties.ImtKeccakBreakFires : Prop :=
  ∃ (keccak : Keccak) (zPre : List UInt8) (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf),
    zPre.length ≠ 64 ∧ TreeBounded setup ∧ LeafBounded ℓ
      ∧ InclusionAccepted (efficientHash keccak) (hashLeaf keccak)
          (root (efficientHash keccak) (keccak zPre) (hashLeaf keccak) setup height) ℓ.value ℓ idx sibs k
      ∧ ℓ ≠ setup.leaf idx
      ∧ TreeRootBreak (efficientHash keccak) (keccak zPre) (hashLeaf keccak) setup height sibs k idx ℓ
      ∧ ¬ (setup.leafCount ≤ idx ∧ imtPre ℓ = zPre)
      ∧ ImtKeccakBreak keccak zPre setup height sibs k idx ℓ

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
(128 / 96), the shared tree (96 / 96) and the IMT (96, with the pin's 96-byte padding or UPG's
34-byte one). -/
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
(At the pin the IMT fails it: right after `setup`, entry 0 is the zero leaf.) -/
def Properties.TreeEntryDomains : Prop :=
  (∀ (padB : UInt256) (B : ℕ → BatchLeaf) (n : ℕ), EntryDomain (chainTreePre padB B) n emptyPre)
    ∧ (∀ (padC : UInt256) (C : ℕ → ChainIdLeaf) (n : ℕ), padC ≠ 0 →
        EntryDomain (sharedTreePre padC C) n emptyPre)
    ∧ (∀ T : Tree, EntryDomain (imtLeafPre T) T.leafCount imtEmptyLeafPre)

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

/-- **THE PREMISES OF (d) ARE SATISFIABLE, AND ITS COLLISION DISJUNCTS ARE NOT FORCED.** Under the
length stand-in, on any chain tree: the three hash equalities of
`AcceptForcesHeightHypothesesUpToCollision` all fail (so `accept_forces_height`'s domain hypotheses
hold outright), and `EntriesNotEmpty` holds outright. -/
def Properties.TreeDomainsWitness : Prop :=
  ∀ (padB : UInt256) (B : ℕ → BatchLeaf) (n : ℕ) (b : BatchLeaf),
    (∀ y ∈ leafList lengthKeccak (chainTreePre padB B) n, ∀ a c : UInt256,
        y ≠ efficientHash lengthKeccak a c)
      ∧ (∀ a c : UInt256, lengthKeccak emptyPre ≠ efficientHash lengthKeccak a c)
      ∧ (∀ a c : UInt256, lengthKeccak (batchPre padB b.batchRoot b.batchNumber b.l1Timestamp)
          ≠ efficientHash lengthKeccak a c)
      ∧ EntriesNotEmpty (lengthKeccak emptyPre) (leafList lengthKeccak (chainTreePre padB B) n)

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

/-- **THE PREMISES OF `AcceptOpensPreimageOrKeccakBreak` ARE JOINTLY SATISFIABLE, WITH EVERY COLLISION
DISJUNCT FALSE.** For every keccak there is an instance (a two-batch chain tree at height 1, the
honest proof of batch 1) meeting every premise, at a positive height, on which the proof opens the
claimed preimage and no collision disjunct holds. -/
def Properties.AcceptOpensPreimageWitness : Prop :=
  ∀ keccak : Keccak, ∃ (pre : ℕ → List UInt8) (n : ℕ) (zPre xPre : List UInt8)
    (sibs : ℕ → UInt256) (k height j : ℕ),
    LeafDomain pre n zPre xPre ∧ j < 2 ^ k ∧ 0 < height
      ∧ walkPure (efficientHash keccak) sibs 0 k j (keccak xPre)
          = rootOf (efficientHash keccak) (keccak zPre) (leafList keccak pre n) height
      ∧ (k = height ∧ entryPre pre n zPre j = xPre)
      ∧ ¬ HashCollision keccak (entryPre pre n zPre j) xPre
      ∧ ¬ PathKeccakCollision keccak (keccak zPre) (leafList keccak pre n) sibs 0 k j (keccak xPre)
      ∧ ¬ HeightKeccakBreak keccak pre n zPre sibs k height j xPre

/-- **AN ACCEPTED PATH OPENS AN OCCUPIED ENTRY WITH EXACTLY THE CLAIMED PREIMAGE, OR KECCAK COLLIDES.**
`AcceptOpensPreimageOrKeccakBreak` when the claimed preimage is not the padding preimage: then the
opened position is occupied, and its entry's preimage IS the claimed one. For the chain tree
(128 versus 96 bytes) and the shared tree (`CHAIN_ID_LEAF_PADDING ≠ 0`) that premise is a byte
fact; for the logs tree it is what `_getProofData`'s default-leaf check gives
(`MessageHashing.sol:165-169`: a leaf hash different from the padding's has a different preimage). -/
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
BYTES.** A path accepted against a chain root (any length, any index), presenting the batch leaf
`batchLeafHash(batchRoot, batchNumber, l1Timestamp)`, has the chain tree's height and opens an
occupied position `j` whose pushed batch has exactly those three fields; or keccak collides on the
opened 128-byte (or 96-byte padding) preimage and the claimed one, on a 64-byte node preimage of the
path, or on a named pair for a wrong length. So "a batch leaf of another batch number or root" is a
keccak collision. No premise on `BATCH_LEAF_PADDING`. -/
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
`SHARED_ROOT_TREE_EMPTY_HASH`: the opened position is occupied by exactly the presented
`(chainIdRoot, chainId)`. So "a chain-id leaf equal to the padding or to another chain's leaf" is a
keccak collision. Premise: `CHAIN_ID_LEAF_PADDING ≠ 0`. -/
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

/-- **THE TWO TREE HEADLINES' PREMISES ARE SATISFIABLE, WITH THE FIRST DISJUNCT THE ONE THAT HOLDS.**
For every keccak and every tags: the honest proof of entry 1 of a two-entry chain tree, and of a
two-entry shared tree (with `padC = 1`), at height 1, is accepted, opens entry 1, and carries none
of the collision disjuncts. -/
def Properties.TreeProofOpensWitness : Prop :=
  ∀ (keccak : Keccak) (padB : UInt256) (B : ℕ → BatchLeaf) (C : ℕ → ChainIdLeaf),
    (walkPure (efficientHash keccak)
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
          (batchLeafHash keccak padB (B 1).batchRoot (B 1).batchNumber (B 1).l1Timestamp))
    ∧ ((1 : UInt256) ≠ 0
      ∧ walkPure (efficientHash keccak)
          (honestSibs (efficientHash keccak) (emptyEntryHash keccak)
            (leafList keccak (sharedTreePre 1 C) 2) 1) 0 1 1
          (chainIdLeafHash keccak 1 (C 1).chainIdRoot (C 1).chainId)
        = rootOf (efficientHash keccak) (emptyEntryHash keccak)
            (leafList keccak (sharedTreePre 1 C) 2) 1
      ∧ ¬ HashCollision keccak (entryPre (sharedTreePre 1 C) 2 emptyPre 1)
          (chainIdPre 1 (C 1).chainIdRoot (C 1).chainId)
      ∧ ¬ PathKeccakCollision keccak (emptyEntryHash keccak)
          (leafList keccak (sharedTreePre 1 C) 2)
          (honestSibs (efficientHash keccak) (emptyEntryHash keccak)
            (leafList keccak (sharedTreePre 1 C) 2) 1) 0 1 1
          (chainIdLeafHash keccak 1 (C 1).chainIdRoot (C 1).chainId))

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
NAMED BYTES.** The chain tree's entries are the batch leaves (`MessageRootBase.sol:257-259`), its
empty entry `CHAIN_TREE_EMPTY_ENTRY_HASH = keccak(new bytes(96))`, its zero cascade the one
`AtomicInteropProof.sol:219-229` checks against. An accepted batch-leaf path whose left-child
siblings are all that cascade is at the last pushed batch, or keccak collides: on a 64-byte node
preimage of the subtree starting at `j + 1` and the cascade's, on the 128-byte preimage of batch
`j + 1` and the 96 zero bytes, or on the submitted path. No premise on `BATCH_LEAF_PADDING`. This
makes the source comment "a populated right subtree ... whose hash cannot collide with the zero
cascade" (`AtomicInteropProof.sol:213-214`) a theorem. -/
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
  check is the premise that instance fails. -/
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

Each is an equivalence, so nothing is lost: every located node collision of the corpus is a
`HashCollision keccak` on two 64-byte strings. -/
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
