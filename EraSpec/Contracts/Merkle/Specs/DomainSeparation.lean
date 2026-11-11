import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned
import EraSpec.Contracts.Merkle.Specs.RootForgeryPinned
import EraSpec.Contracts.AtomicInteropProof.Specs.LastLeaf
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.TreeRoot

/-!
# Spec: Merkle domain separation by preimage length, down to keccak

## Why this file exists

Every inclusion and absence result in `Merkle`, `AtomicInteropProof` and
`L2InteropCommitmentTree` is stated over an abstract node hash `h : UInt256 → UInt256 → UInt256`,
an abstract leaf hash, and an abstract padding constant. Its domain hypotheses are abstract too:

* `leafNotNode`, `padNotNode`, `padNotLeaf` (`TreeRoot.HashAssumptions`);
* `LastLeaf.EntriesNotEmpty`;
* the `hL`, `hz0`, `hx` hypotheses of `Verifier.accept_forces_height`;
* and the located breaks that replaced global injectivity (`PathCollision`, `HeightBreak`,
  `PinnedBreak`, `TreeRootBreak`, `RootForgeryPinned.LevelCollision`, ...).

At the pin these hold only because of **preimage lengths**. Every hash in the corpus is one
function, `keccak256`, applied to byte strings of these lengths:

| keccak input | length | source |
|---|---|---|
| internal node `efficientHash(l, r)` | 64 | `Merkle.sol:125-131` |
| L2 log leaf `getLeafHashFromLog` | 88 | `MessageHashing.sol:64-69` |
| logs-tree padding `L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH` | 88 | system-contracts `Constants.sol:103-106` |
| `chainIdLeafHash` | 96 | `MessageHashing.sol:89-91` |
| IMT `hashLeaf` | 96 | `IndexedMerkleTree.sol:123-125` |
| empty entry `new bytes(96)` | 96 | `IMessageRoot.sol:8-16`, `ChainBatchRootTree.sol:50-55` |
| `commitValue` | 96 | `AtomicInteropProof.sol:100-102` |
| `batchLeafHash` | 128 | `MessageHashing.sol:78-84` |
| `ZERO_LEAF_HASH = keccak256("")` | 0 | `PriorityTree.sol:22` |
| UPG `IMT_EMPTY_LEAF_HASH` | 34 | UPG `common/Config.sol:131-134` |

So two hashes of different-length inputs can be equal only through a keccak collision on two
**named** byte strings: `HashCollision keccak x y` (`InteropDataEncoding/Specs/BundleHashPinned.lean`),
with `x` and `y` read off the instance. Within the 96-byte family the inputs are told apart by
their first word (a padding tag, a leaf value, or zero), and four constants coincide as one value,
`keccak256` of 96 zero bytes: `EMPTY_IMT_ROOT = CHAIN_TREE_EMPTY_ENTRY_HASH =
SHARED_ROOT_TREE_EMPTY_HASH = hashLeaf({0,0,0})`.

This file defines the byte encoders, the keccak instantiation of the abstract hashes, and the
keccak-level forms of the located breaks. `../Properties/DomainSeparation.lean` states the
reductions; `../Proofs/DomainSeparation.lean` proves them.

## The trees, and what separates their levels

* **IMT** (`IndexedMerkleTree`, a `FullMerkle`): leaves `hashLeaf` (96), nodes 64. Padding at the pin
  is `hashLeaf({0,0,0})` (`IndexedMerkleTree.sol:47-48`): the padding preimage IS a leaf preimage,
  which is the known forged-absence bug (`PaddingCollisionRefundsDeliveredLeg`, not re-reported here).
  At UPG the padding is `keccak256("zkSync:IndexedMerkleTree:emptyLeaf")` (UPG
  `IndexedMerkleTree.sol:44-53`), a 34-byte preimage.
* **Chain tree** (per chain, `DynamicIncrementalMerkle`): leaves `batchLeafHash` (128), empty entry
  `CHAIN_TREE_EMPTY_ENTRY_HASH` (96, `MessageRootBase.sol:350`), nodes 64. Fully length-separated.
* **Shared tree** (`DynamicIncrementalMerkle`): leaves `chainIdLeafHash` (96), empty entry
  `SHARED_ROOT_TREE_EMPTY_HASH` (96, `MessageRootBase.sol:164`), nodes 64. Leaf and empty entry have
  the same length and differ in their first word, `CHAIN_ID_LEAF_PADDING` versus zero.
* **L2 logs tree**: leaves 88, padding `keccak256(new bytes(88))` (88), nodes 64. The padding preimage
  is the all-zero log's preimage (`Properties.LogDefaultIsZeroLog`); `_getProofData` rejects that
  leaf hash outright (`MessageHashing.sol:165-169`).
* **Chain batch root tree** (`ChainBatchRootTree`, height 3): its leaves are used directly
  (`ChainBatchRootTree.sol:17`), so it has no leaf/node separation at all; the fixed depth carries
  that role. Out of scope here (backlog W-MER-3).
* **Priority tree**: zero `keccak256("")` (0 bytes) versus nodes (64). Its leaves are canonical
  transaction hashes, whose preimages are not modelled.

## Model boundaries

* `keccak : List UInt8 → UInt256` is an arbitrary function. Nothing about it is assumed. The
  keccak-derived constants (`CHAIN_ID_LEAF_PADDING`, `BATCH_LEAF_PADDING`,
  `ATOMIC_COMMIT_LEAF_TAG`) cannot be evaluated in Lean, so they are parameters `padC`, `padB`,
  `tag`; the results that need them take `padC ≠ 0` or `tag ≠ 0` as a named premise. No result
  here needs a premise on `padB`: the 128-byte batch preimage is the only one of its length.
* The 32-byte words are `word` (`InteropDataEncoding/Specs/BundleHashEncoding.lean`), big-endian.
  `abi.encodePacked` of a `bytes32`/`uint256` and `abi.encode` of a `uint256` both produce that word;
  a `bytes4` is left-aligned in its `abi.encode` slot. These are the ABI specification, not a
  Solidity semantics (`SOL-ABI`).
* `Leaf.nextIndex` is a natural number in the model, a `uint256` in the contract. `word` truncates
  above `2^256`, so the results that need `hashLeaf`'s preimage to determine the leaf take
  `LeafBounded` (the stored index is a `uint256`) as a premise.
* The trees are the `FullMerkle` fold `rootOf` over a level-0 list (`FullMerkle/Specs/Model.lean`),
  as everywhere in `Merkle`. That stored roots and `DynamicIncrementalMerkle` roots equal that fold
  is obligation O7 (`Refinement.lean`) and backlog W-MER-2.
-/

namespace MerkleSpec.DomainSeparation

open AttackVectors.BundleHashEncoding (HashCollision toBytesBE word)
open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf
open Contracts.InteropCommitmentTree (Leaf Tree LeafHash leafHashes)

/-- `keccak256` over byte strings. An arbitrary function: nothing is assumed about it. -/
abbrev Keccak := List UInt8 → UInt256

/-- The 32-byte big-endian word of a `bytes32` / `uint256` value. -/
abbrev w32 (x : UInt256) : List UInt8 := word x.val

/-! ## The keccak inputs -/

/-- **THE NODE PREIMAGE, 64 BYTES.** `Merkle.efficientHash(_lhs, _rhs)` (`Merkle.sol:125-131`):

    mstore(0x00, _lhs)  mstore(0x20, _rhs)  result := keccak256(0x00, 0x40)

Every internal node of every tree in the corpus is this hash: `Merkle.calculateRootMemory`
(`Merkle.sol:62-67`), `FullMerkle` (`FullMerkle.sol:49, 82-87`), `DynamicIncrementalMerkle`
(`DynamicIncrementalMerkle.sol:104, 126-128, 150-151`), the last-batch zero cascade
(`AtomicInteropProof.sol:228`), and `ChainBatchRootTree.compute` (`ChainBatchRootTree.sol:78-84`,
`keccak256(bytes.concat(l, r))`, the same 64 bytes). -/
def nodePre (a b : UInt256) : List UInt8 := w32 a ++ w32 b

/-- The node preimage of an ordered pair, as the collision predicates (`walkPair`, `treePair`,
`childPair`, `parentPair`) name their pairs. -/
def pairPre (p : UInt256 × UInt256) : List UInt8 := nodePre p.1 p.2

/-- `struct L2Log` (`common/Messaging.sol:27-34`). `txNumberInBatch` is a `uint16` and `sender` an
`address`; the model keeps them as naturals, and the packed encoding takes their low 2 and 20
bytes. -/
structure L2Log where
  l2ShardId : UInt8
  isService : Bool
  txNumberInBatch : ℕ
  sender : ℕ
  key : UInt256
  value : UInt256

/-- A packed `bool`: one byte, `0x01` or `0x00`. -/
def boolByte (b : Bool) : UInt8 := if b then 1 else 0

/-- **THE L2 LOG LEAF PREIMAGE, 88 BYTES.** `MessageHashing.getLeafHashFromLog`
(`MessageHashing.sol:64-69`):

    keccak256(abi.encodePacked(l2ShardId, isService, txNumberInBatch, sender, key, value))

1 + 1 + 2 + 20 + 32 + 32 = 88 bytes, the `L2_TO_L1_LOG_SERIALIZE_SIZE` of system-contracts
`Constants.sol:99-101`. -/
def logPre (log : L2Log) : List UInt8 :=
  [log.l2ShardId] ++ [boolByte log.isService] ++ toBytesBE 2 log.txNumberInBatch
    ++ toBytesBE 20 log.sender ++ w32 log.key ++ w32 log.value

/-- The all-zero log: shard 0, `isService = false`, transaction 0, sender 0, key 0, value 0. -/
def zeroLog : L2Log := ⟨0, false, 0, 0, 0, 0⟩

/-- **THE LOGS-TREE PADDING PREIMAGE, 88 BYTES.** `L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH` "is actually
equal to `keccak256(new bytes(L2_TO_L1_LOG_SERIALIZE_SIZE))`" (system-contracts
`Constants.sol:103-106`). -/
def logDefaultPre : List UInt8 := List.replicate 88 0

/-- **THE CHAIN-ID LEAF PREIMAGE, 96 BYTES.** `MessageHashing.chainIdLeafHash`
(`MessageHashing.sol:89-91`):

    keccak256(abi.encodePacked(CHAIN_ID_LEAF_PADDING, chainIdRoot, chainId))

`padC` stands for `CHAIN_ID_LEAF_PADDING = keccak256("zkSync:ChainIdLeaf")` (`:16`). -/
def chainIdPre (padC chainIdRoot chainId : UInt256) : List UInt8 :=
  w32 padC ++ w32 chainIdRoot ++ w32 chainId

/-- **THE BATCH LEAF PREIMAGE, 128 BYTES.** `MessageHashing.batchLeafHash`
(`MessageHashing.sol:78-84`):

    keccak256(abi.encodePacked(BATCH_LEAF_PADDING, batchRoot, batchNumber, l1Timestamp))

`padB` stands for `BATCH_LEAF_PADDING = keccak256("zkSync:BatchLeaf")` (`:15`). -/
def batchPre (padB batchRoot batchNumber l1Timestamp : UInt256) : List UInt8 :=
  w32 padB ++ w32 batchRoot ++ w32 batchNumber ++ w32 l1Timestamp

/-- **THE IMT LEAF PREIMAGE, 96 BYTES.** `IndexedMerkleTree.hashLeaf` (`IndexedMerkleTree.sol:123-125`):

    keccak256(abi.encode(_leaf.value, _leaf.nextIndex, _leaf.nextValue))

The comment at `:120-121` asks that "the preimage for each leaf is not 64 bytes long". -/
def imtPre (ℓ : Leaf) : List UInt8 := w32 ℓ.value ++ word ℓ.nextIndex ++ w32 ℓ.nextValue

/-- **THE EMPTY-ENTRY PREIMAGE: 96 ZERO BYTES.** "We use hash of `new bytes(96)` as the hash of an
empty leaf" (`IMessageRoot.sol:8, 13`), for both `CHAIN_TREE_EMPTY_ENTRY_HASH` and
`SHARED_ROOT_TREE_EMPTY_HASH`; and `EMPTY_IMT_ROOT` is "the keccak256 of 96 zero bytes"
(`ChainBatchRootTree.sol:50-55`). -/
def emptyPre : List UInt8 := List.replicate 96 0

/-- **THE PRIORITY TREE'S ZERO PREIMAGE: THE EMPTY STRING.** `ZERO_LEAF_HASH = keccak256("")`
(`PriorityTree.sol:22`). -/
def zeroLeafPre : List UInt8 := []

/-- **THE COMMIT-VALUE PREIMAGE, 96 BYTES.** `AtomicInteropProof.commitValue`
(`AtomicInteropProof.sol:100-102`):

    uint256(keccak256(abi.encode(ATOMIC_COMMIT_LEAF_TAG, _flowId, _specHash)))

`ATOMIC_COMMIT_LEAF_TAG` is a `bytes4` (`IAtomicInterop.sol:94`), so `abi.encode` puts its four
bytes first in a 32-byte slot and pads the slot with 28 zero bytes on the right. `tag` is that
four-byte value, read big-endian. -/
def commitPre (tag : ℕ) (flowId specHash : UInt256) : List UInt8 :=
  (toBytesBE 4 tag ++ List.replicate 28 0) ++ w32 flowId ++ w32 specHash

/-- The pin's IMT padding preimage: `setup` pads with `hashLeaf(IMTLeaf({0, 0, 0}))`
(`IndexedMerkleTree.sol:47-48`). -/
def pinPaddingPre : List UInt8 := imtPre ⟨0, 0, 0⟩

/-- **THE UPG IMT PADDING PREIMAGE, 34 BYTES.** UPG `common/Config.sol:131-134`:
`IMT_EMPTY_LEAF_HASH = keccak256("zkSync:IndexedMerkleTree:emptyLeaf")`, "deliberately NOT a valid
`hashLeaf(IMTLeaf)` output". These are the 34 ASCII bytes of that string, written out because Lean
does not reduce `String.toUTF8` in proofs. -/
def imtEmptyLeafPre : List UInt8 :=
  [0x7a, 0x6b, 0x53, 0x79, 0x6e, 0x63, 0x3a, 0x49, 0x6e, 0x64, 0x65, 0x78, 0x65, 0x64, 0x4d, 0x65,
    0x72, 0x6b, 0x6c, 0x65, 0x54, 0x72, 0x65, 0x65, 0x3a, 0x65, 0x6d, 0x70, 0x74, 0x79, 0x4c, 0x65,
    0x61, 0x66]

/-- **`CHAIN_ID_LEAF_PADDING`'s PREIMAGE, 18 BYTES.** `keccak256("zkSync:ChainIdLeaf")`
(`MessageHashing.sol:16`): the 18 ASCII bytes of that string, written out. The results that only
need the tag to be nonzero keep it as a parameter `padC`; `CommitLeafNotChainIdLeafOrCollision` uses
this definition instead. -/
def chainIdLeafPaddingPre : List UInt8 :=
  [0x7a, 0x6b, 0x53, 0x79, 0x6e, 0x63, 0x3a, 0x43, 0x68, 0x61, 0x69, 0x6e, 0x49, 0x64, 0x4c, 0x65,
    0x61, 0x66]

/-! ## The hashes, instantiated with keccak -/

/-- `Merkle.efficientHash`, the node hash of every tree: keccak of the 64-byte node preimage. -/
def efficientHash (keccak : Keccak) : Hash := fun a b => keccak (nodePre a b)

/-- `IndexedMerkleTree.hashLeaf`. -/
def hashLeaf (keccak : Keccak) : LeafHash := fun ℓ => keccak (imtPre ℓ)

/-- The pin's IMT padding constant, `hashLeaf({0, 0, 0})` (`IndexedMerkleTree.sol:47-48`). This is
the `z0` that `ProofsExclusiveOrBreakSatisfiable` and the padding countermodel use. -/
def imtPadding (keccak : Keccak) : UInt256 := hashLeaf keccak ⟨0, 0, 0⟩

/-- `MessageHashing.chainIdLeafHash`. -/
def chainIdLeafHash (keccak : Keccak) (padC chainIdRoot chainId : UInt256) : UInt256 :=
  keccak (chainIdPre padC chainIdRoot chainId)

/-- `MessageHashing.batchLeafHash`. -/
def batchLeafHash (keccak : Keccak) (padB batchRoot batchNumber l1Timestamp : UInt256) : UInt256 :=
  keccak (batchPre padB batchRoot batchNumber l1Timestamp)

/-- `keccak256(new bytes(96))`: the value of the three empty-entry constants below. -/
def emptyEntryHash (keccak : Keccak) : UInt256 := keccak emptyPre

/-! ## The empty-entry constants, as written in the source -/

/-- `CHAIN_TREE_EMPTY_ENTRY_HASH` (`IMessageRoot.sol:8-11`). -/
def CHAIN_TREE_EMPTY_ENTRY_HASH : UInt256 :=
  0x46700b4d40ac5c35af2c22dda2787a91eb567b06c924a8fb8ae9a05b20c08c21

/-- `SHARED_ROOT_TREE_EMPTY_HASH` (`IMessageRoot.sol:13-16`). -/
def SHARED_ROOT_TREE_EMPTY_HASH : UInt256 :=
  0x46700b4d40ac5c35af2c22dda2787a91eb567b06c924a8fb8ae9a05b20c08c21

/-- `ChainBatchRootTree.EMPTY_IMT_ROOT` (`ChainBatchRootTree.sol:50-55`). -/
def EMPTY_IMT_ROOT : UInt256 :=
  0x46700b4d40ac5c35af2c22dda2787a91eb567b06c924a8fb8ae9a05b20c08c21

/-- **THE DOCUMENTED VALUE OF `keccak256(new bytes(96))`.** The source hardcodes the three constants
above and documents them as this hash. Lean cannot evaluate keccak, so this is a premise, used only
to connect the hex literals to `emptyEntryHash`. -/
def KeccakOfEmptyIsDocumented (keccak : Keccak) : Prop :=
  keccak emptyPre = 0x46700b4d40ac5c35af2c22dda2787a91eb567b06c924a8fb8ae9a05b20c08c21

/-! ## Trees whose level 0 is keccak of named preimages -/

/-- The level-0 list of a tree whose `n` entries are `keccak (pre m)`. -/
def leafList (keccak : Keccak) (pre : ℕ → List UInt8) (n : ℕ) : List UInt256 :=
  (List.range n).map (fun m => keccak (pre m))

/-- The keccak input behind level-0 position `m` of that tree: the entry's preimage if `m` is
occupied, the padding preimage `zPre` otherwise (`FullMerkle` reads `_zeros[0]` there). -/
def entryPre (pre : ℕ → List UInt8) (n : ℕ) (zPre : List UInt8) (m : ℕ) : List UInt8 :=
  if m < n then pre m else zPre

/-- **LEAF/NODE DOMAIN SEPARATION BY LENGTH.** No entry preimage, no padding preimage, and no claimed
leaf preimage `xPre` is 64 bytes long. This is what the `hashLeaf` comment
(`IndexedMerkleTree.sol:120-121`) and the "no length check needed" comment
(`MessageVerification.sol:94-96`) rely on. -/
def LeafDomain (pre : ℕ → List UInt8) (n : ℕ) (zPre xPre : List UInt8) : Prop :=
  (∀ m < n, (pre m).length ≠ 64) ∧ zPre.length ≠ 64 ∧ xPre.length ≠ 64

/-- **ENTRY/EMPTY DOMAIN SEPARATION, AT THE BYTE LEVEL.** No entry preimage is the padding preimage.
The `DynamicIncrementalMerkle.setup` comment asks this of the zero value: "a value that is not
expected to be part of the tree" (`DynamicIncrementalMerkle.sol:50-52`). -/
def EntryDomain (pre : ℕ → List UInt8) (n : ℕ) (zPre : List UInt8) : Prop :=
  ∀ m < n, pre m ≠ zPre

/-- The fields of a chain-tree leaf: `batchLeafHash(batchRoot, batchNumber, l1Timestamp)` as pushed
by `MessageRootBase._pushChainBatchRoot` (`MessageRootBase.sol:257-259`). -/
structure BatchLeaf where
  batchRoot : UInt256
  batchNumber : UInt256
  l1Timestamp : UInt256

/-- The chain tree's entry preimages: entry `m` is the batch leaf of the `m`-th pushed batch. -/
def chainTreePre (padB : UInt256) (B : ℕ → BatchLeaf) : ℕ → List UInt8 :=
  fun m => batchPre padB (B m).batchRoot (B m).batchNumber (B m).l1Timestamp

/-- The fields of a shared-tree leaf: `chainIdLeafHash(chainIdRoot, chainId)`
(`MessageRootBase.sol:264-265, 352`). -/
structure ChainIdLeaf where
  chainIdRoot : UInt256
  chainId : UInt256

/-- The shared tree's entry preimages: entry `m` is the chain-id leaf of the `m`-th chain. -/
def sharedTreePre (padC : UInt256) (C : ℕ → ChainIdLeaf) : ℕ → List UInt8 :=
  fun m => chainIdPre padC (C m).chainIdRoot (C m).chainId

/-- The L2 logs tree's entry preimages: entry `m` is the `m`-th log. -/
def logsTreePre (logs : ℕ → L2Log) : ℕ → List UInt8 := fun m => logPre (logs m)

/-- The IMT's entry preimages: entry `m` is `hashLeaf` of the leaf stored at `m`. With this,
`leafList keccak (imtLeafPre T) T.leafCount` is `leafHashes (hashLeaf keccak) T`. -/
def imtLeafPre (T : Tree) : ℕ → List UInt8 := fun m => imtPre (T.leaf m)

/-- A leaf whose `nextIndex` fits a `uint256`, as every leaf the contract stores or receives in
calldata does (`IMTLeaf`, `IndexedMerkleTree.sol:21-25`). -/
def LeafBounded (ℓ : Leaf) : Prop := ℓ.nextIndex < 256 ^ 32

/-- Every occupied leaf of the tree is `LeafBounded`. -/
def TreeBounded (T : Tree) : Prop := ∀ i < T.leafCount, LeafBounded (T.leaf i)

/-! ## The located breaks, in keccak terms -/

/-- **A `PathCollision`, AS A KECCAK COLLISION ON TWO NAMED 64-BYTE STRINGS.** At a step `i < k` of
the submitted walk, the node preimage the verifier hashed differs from the node preimage the tree
hashed at the same position, and keccak maps them to the same word. Both strings are determined by
the instance (tree, siblings, index, claimed leaf) and `i`. -/
def PathKeccakCollision (keccak : Keccak) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256)
    (lvl k j : ℕ) (x : UInt256) : Prop :=
  ∃ i < k, HashCollision keccak (pairPre (walkPair (efficientHash keccak) sibs lvl j x i))
    (pairPre (treePair (efficientHash keccak) z0 L (lvl + i) (j / 2 ^ i)))

/-- **A WRONG PATH LENGTH, LOCATED AS A KECCAK COLLISION.** `HeightBreak` for the tree over
`leafList keccak pre n` with padding `keccak zPre` and claimed leaf `keccak xPre`, with each case
turned into a collision on named byte strings:

* `leafIsNode` (too short): the claimed leaf's preimage `xPre` and the node preimage of the tree's
  pair at level `height - k - 1` below `j` hash equal (a cross-length collision when `xPre` is not
  64 bytes);
* `shortCollision` (too short): the re-anchored walk collides on a 64-byte node preimage;
* `entryIsNode` (too long): the level-0 preimage at `j / 2^(k - height)` (an entry's, or the
  padding's) and the node preimage of the verifier's own pair at its last step below the split hash
  equal;
* `longCollision` (too long): the top `height` steps collide on a 64-byte node preimage. -/
inductive HeightKeccakBreak (keccak : Keccak) (pre : ℕ → List UInt8) (n : ℕ) (zPre : List UInt8)
    (sibs : ℕ → UInt256) (k height j : ℕ) (xPre : List UInt8) : Prop
  | leafIsNode : k < height →
      HashCollision keccak xPre
        (pairPre (treePair (efficientHash keccak) (keccak zPre) (leafList keccak pre n)
          (height - k - 1) (2 * j))) →
      HeightKeccakBreak keccak pre n zPre sibs k height j xPre
  | shortCollision : k < height →
      PathKeccakCollision keccak (keccak zPre) (leafList keccak pre n)
        (fun l => sibs (l - (height - k))) (height - k) k j (keccak xPre) →
      HeightKeccakBreak keccak pre n zPre sibs k height j xPre
  | entryIsNode : height < k →
      HashCollision keccak (entryPre pre n zPre (j / 2 ^ (k - height)))
        (pairPre (walkPair (efficientHash keccak) sibs 0 j (keccak xPre) (k - height - 1))) →
      HeightKeccakBreak keccak pre n zPre sibs k height j xPre
  | longCollision : height < k →
      PathKeccakCollision keccak (keccak zPre) (leafList keccak pre n)
        (fun l => sibs (l + (k - height))) 0 height (j / 2 ^ (k - height))
        (walkPure (efficientHash keccak) sibs 0 (k - height) j (keccak xPre)) →
      HeightKeccakBreak keccak pre n zPre sibs k height j xPre

/-- **THE LAST-LEAF BREAK, LOCATED AS A KECCAK COLLISION.** `LastLeaf.PinnedBreak` for the tree over
`leafList keccak pre n` with empty entry `keccak zPre`, with each case a collision on named strings:

* `nodeCollision l m`: the node preimage of the level-`(l+1)` node `m` whose subtree starts at
  `j + 1` and the zero cascade's node preimage at level `l` differ and hash equal (64 bytes each);
* `entryIsEmpty`: the preimage of entry `j + 1` and the empty-entry preimage hash equal. -/
inductive PinnedKeccakBreak (keccak : Keccak) (pre : ℕ → List UInt8) (n : ℕ) (zPre : List UInt8)
    (j : ℕ) : Prop
  | nodeCollision (l m : ℕ) : j + 1 < n → m * 2 ^ (l + 1) = j + 1 →
      HashCollision keccak
        (pairPre (childPair (efficientHash keccak) (keccak zPre) (leafList keccak pre n) l m))
        (pairPre (zeroPair (efficientHash keccak) (keccak zPre) l)) →
      PinnedKeccakBreak keccak pre n zPre j
  | entryIsEmpty : j + 1 < n → HashCollision keccak (pre (j + 1)) zPre →
      PinnedKeccakBreak keccak pre n zPre j

/-- **A BREAK OF THE IMT ROOT CHECK, LOCATED AS A KECCAK COLLISION.** `TreeRootBreak` for the tree
`T` with node hash `efficientHash keccak`, leaf hash `hashLeaf keccak` and padding `keccak zPre`,
each case turned into a collision on named byte strings:

* `wrongLength`: a `HeightKeccakBreak` on the leaf preimages `imtPre (T.leaf m)`;
* `pathCollision`: the right length, and a 64-byte collision on the submitted path;
* `leafCollision`: the preimages of the stored leaf at the opened index and of the presented leaf
  hash equal (two 96-byte strings);
* `paddingCollision`: the opened index is empty, and the presented leaf's preimage and the padding
  preimage hash equal.

At the pin `zPre = pinPaddingPre = imtPre ⟨0, 0, 0⟩`, so for the presented leaf `⟨0, 0, 0⟩` the
`paddingCollision` strings are EQUAL and the case is not a collision: that is the forged-absence
bug, which the theorems keep as a separate, keccak-free disjunct. -/
inductive ImtKeccakBreak (keccak : Keccak) (zPre : List UInt8) (T : Tree) (height : ℕ)
    (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf) : Prop
  | wrongLength :
      HeightKeccakBreak keccak (imtLeafPre T) T.leafCount zPre sibs k height idx (imtPre ℓ) →
      ImtKeccakBreak keccak zPre T height sibs k idx ℓ
  | pathCollision : k = height →
      PathKeccakCollision keccak (keccak zPre) (leafList keccak (imtLeafPre T) T.leafCount) sibs
        0 k idx (keccak (imtPre ℓ)) →
      ImtKeccakBreak keccak zPre T height sibs k idx ℓ
  | leafCollision : idx < T.leafCount → HashCollision keccak (imtPre (T.leaf idx)) (imtPre ℓ) →
      ImtKeccakBreak keccak zPre T height sibs k idx ℓ
  | paddingCollision : T.leafCount ≤ idx → HashCollision keccak (imtPre ℓ) zPre →
      ImtKeccakBreak keccak zPre T height sibs k idx ℓ

/-! ## Stand-ins for keccak, for the witnesses only

None of these is a model of keccak. Each is a simple function whose collisions can be read off,
so that a witness can show a collision predicate is FALSE on a named instance. -/

/-- Hashes a byte string to its length. It never collides across lengths below `2^256`, and
always collides within one length. -/
def lengthKeccak : Keccak := fun x => Nat.toUInt256 x.length

/-- Hashes a byte string to its first 32 bytes read as a word. It tells the 96-byte family apart
by first word (a tag, a leaf value, or zero). -/
def firstWordKeccak : Keccak := fun x =>
  Nat.toUInt256 (AttackVectors.BundleHashEncoding.fromBytesBE (x.take 32))

/-- Hashes every byte string to `0`: every pair of distinct strings collides. -/
def constKeccak : Keccak := fun _ => 0

end MerkleSpec.DomainSeparation
