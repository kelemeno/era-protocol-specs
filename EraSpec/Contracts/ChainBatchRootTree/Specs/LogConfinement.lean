import EraSpec.Contracts.ChainBatchRootTree.Specs.Layout

/-!
# Spec: an L2-log proof against a ZKsync OS chain batch root, and where it can land

Source: era-contracts `draft/v0.35.0` head `b17415d20`, `l1-contracts/contracts/` (cited without that
prefix).

    common/MessageVerification.sol:85-108   _proveL2LogInclusion
        bytes32 hashedLog = MessageHashing.getLeafHashFromLog(_log);
        // It is ok to not check length of `_proof` array, as length
        // of leaf preimage (which is `L2_TO_L1_LOG_SERIALIZE_SIZE`) is not
        // equal to the length of other nodes preimages (which are `2 * 32`)
        // We can use `index` as a mask, since the `LocalLogsRoot` is on the left part of the tree.
        return _proveL2LeafInclusion(..., _leafProofMask: _index, _leaf: hashedLog, _proof: _proof);
    common/libraries/MessageHashing.sol:64-68   getLeafHashFromLog: keccak256(abi.encodePacked(
        l2ShardId, isService, txNumberInBatch, sender, key, value)), 1+1+2+20+32+32 = 88 bytes
        (`L2_TO_L1_LOG_SERIALIZE_SIZE = 88`, common/Config.sol:24)
    common/libraries/MessageHashing.sol:174-178  batchSettlementRoot =
        Merkle.calculateRootMemory(slice of logLeafProofLen siblings, _leafProofMask, _leaf)
    common/libraries/MessageHashing.sol:101-143  logLeafProofLen: a metadata byte, or the whole
        proof's length in the old format; nothing compares it with a tree height
    core/message-root/MessageRootBase.sol:343-348, :364-373  on the settlement layer a final-node
        proof is accepted iff batchSettlementRoot == chainBatchRoots[c][n] != 0 (n > 0)

So on L1 the walk's length `k` and its mask `j < 2^k` are the prover's. For a ZKsync OS chain the
recorded root is `ChainBatchRootTree.compute(logsRoot, multichainRoot, imtBegin, imtEnd)`
(`Executor.sol:163-166` records the committed `l2LogsTreeRoot`, `protocol-docs/message-root.md:60-74`).
Leaf 0 is the logs tree, whose leaves are 88-byte log preimages; leaves 2 and 3 are interop
commitment tree roots, whose leaves are 96-byte `hashLeaf` preimages and whose padding is the 34-byte
`IMT_EMPTY_LEAF_HASH` preimage (`IndexedMerkleTree.sol:46-54, 124-126`, `common/Config.sol:141`);
leaves 4 … 7 are zero. The tree has no leaf/node separation of its own.

## Model

* **`PreTree`, the honest structure below a value.** `node l r` is keccak of the 64-byte node
  preimage of its children's values; `leaf p` is keccak of the byte string `p`; `const v` is a
  value with no keccak preimage in the model (the reserved zero leaves); `cut v` is a subtree the
  statement does not look into (the logs tree below leaf 0). `val` evaluates a tree; `pre?` is the
  keccak input behind a `node` or `leaf`.
* **`land`, where the walk leaves the honest tree.** From the top, while the pair the walk hashed at
  the current step equals the node's pair of child values, descend to the child the index's bit
  selects. Stop at a non-`node`, when no walk steps are left, or at the first mismatch. The result is
  the landing subtree and the number of walk steps below it. It is a function of the instance
  (keccak, tree, siblings, index, claimed leaf), so the break located there is pinned to it.
* **`walkPre`, the walk's keccak inputs.** After `0` steps it is the claimed leaf's preimage (the
  88-byte log); after `i + 1` steps the 64-byte node preimage of the pair hashed at step `i`.
* **`LandingBreak`**: at the landing, the walk's keccak input and the landing node's keccak input
  differ and hash equal (`HashCollision` on two named strings), or the landing node is a `const`
  and the walk's keccak input hashes to it.
* `PassesLeafZero` is the outcome the source comment intends: the walk is at least 3 long, the
  top three mask bits are zero, its value after `k - 3` steps is the leaf-0 value, and the top
  three siblings are the honest ones.
* `imtPreTree T H` is the complete height-`H` tree over `T`'s leaf preimages, padded with the
  `IMT_EMPTY_LEAF_HASH` preimage; `zeroPreTree 2` is the reserved half over four `const 0` leaves.
* The outer proof hops (batch leaf into the chain tree, chain-id leaf into the shared root) are not
  modelled: "accepted" here means the first hop's walk returns the batch's chain batch root, which is
  what those hops (or the final-node comparison on L1) conclude. That the recorded root is `compute`
  of the batch's honest subtrees is the batch's validity, also not modelled here.

**This file is definitions only.** Results: `../Properties/LogConfinement.lean`.
-/

namespace Contracts.ChainBatchRootTree

open MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (HashCollision word toBytesBE)

/-! ## The L2 log leaf -/

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
(`MessageHashing.sol:64-68`): `abi.encodePacked(l2ShardId, isService, txNumberInBatch, sender, key,
value)`, `1 + 1 + 2 + 20 + 32 + 32` bytes. -/
def logPre (log : L2Log) : List UInt8 :=
  [log.l2ShardId] ++ [boolByte log.isService] ++ toBytesBE 2 log.txNumberInBatch
    ++ toBytesBE 20 log.sender ++ w32 log.key ++ w32 log.value

/-! ## Preimage trees -/

/-- The honest structure below a value. See the module docstring. -/
inductive PreTree where
  /-- keccak of the 64-byte node preimage of the children's values. -/
  | node (l r : PreTree)
  /-- keccak of the byte string `pre`. -/
  | leaf (pre : List UInt8)
  /-- a value with no keccak preimage in the model. -/
  | const (v : UInt256)
  /-- a subtree with value `v` that the statement does not look into. -/
  | cut (v : UInt256)

namespace PreTree

/-- The value of a tree. -/
def val (keccak : Keccak) : PreTree → UInt256
  | .node l r => Contracts.ChainBatchRootTree.node keccak (l.val keccak) (r.val keccak)
  | .leaf p => keccak p
  | .const v => v
  | .cut v => v

/-- The keccak input behind a `node` or a `leaf`. -/
def pre? (keccak : Keccak) : PreTree → Option (List UInt8)
  | .node l r => some (nodePre (l.val keccak) (r.val keccak))
  | .leaf p => some p
  | .const _ => none
  | .cut _ => none

/-- **WHERE A WALK LEAVES THE TREE.** For a walk of `k` steps with index `j`, siblings `sibs` and
claimed leaf value `x`: from the top, while the pair the walk hashed at its current step equals the
node's pair of child values, descend to the child that bit of `j` selects. Returns the subtree where
it stops and the number of walk steps below that subtree. -/
def land (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256) : PreTree → ℕ → PreTree × ℕ
  | .node l r, k + 1 =>
      if walkPair (Contracts.ChainBatchRootTree.node keccak) sibs 0 j x k
          = (l.val keccak, r.val keccak) then
        if j / 2 ^ k % 2 = 1 then r.land keccak sibs j x k else l.land keccak sibs j x k
      else (.node l r, k + 1)
  | T, k => (T, k)

/-- `S` is a subtree of `T`. -/
inductive Sub : PreTree → PreTree → Prop
  | refl (T : PreTree) : Sub T T
  | left {S l r : PreTree} : Sub S l → Sub S (.node l r)
  | right {S l r : PreTree} : Sub S r → Sub S (.node l r)

/-- No `cut` anywhere in the tree. -/
def CutFree : PreTree → Prop
  | .node l r => l.CutFree ∧ r.CutFree
  | .leaf _ => True
  | .const _ => True
  | .cut _ => False

/-- No leaf's keccak input is 64 or 88 bytes long: no leaf can be read as a node, and none as an
L2 log. -/
def LeafLengthsAvoid : PreTree → Prop
  | .node l r => l.LeafLengthsAvoid ∧ r.LeafLengthsAvoid
  | .leaf p => p.length ≠ 64 ∧ p.length ≠ 88
  | .const _ => True
  | .cut _ => True

/-- `q` is the keccak input of some leaf of the tree. -/
def HasLeaf (q : List UInt8) : PreTree → Prop
  | .node l r => l.HasLeaf q ∨ r.HasLeaf q
  | .leaf p => p = q
  | .const _ => False
  | .cut _ => False

/-- `v` is the value of some `const` of the tree. -/
def HasConst (v : UInt256) : PreTree → Prop
  | .node l r => l.HasConst v ∨ r.HasConst v
  | .leaf _ => False
  | .const w => w = v
  | .cut _ => False

end PreTree

/-- **THE WALK'S KECCAK INPUTS.** After `0` steps, the claimed leaf's preimage `xPre`; after `i + 1`
steps, the 64-byte node preimage of the pair the walk hashed at step `i`. -/
def walkPre (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (xPre : List UInt8) : ℕ → List UInt8
  | 0 => xPre
  | i + 1 => pairPre (walkPair (node keccak) sibs 0 j (keccak xPre) i)

/-- The landing subtree and the walk steps left, for a walk whose claimed leaf is `keccak xPre`. -/
def landing (keccak : Keccak) (T : PreTree) (sibs : ℕ → UInt256) (k j : ℕ) (xPre : List UInt8) :
    PreTree × ℕ :=
  T.land keccak sibs j (keccak xPre) k

/-- The walk's keccak input at the landing. -/
def landingInput (keccak : Keccak) (T : PreTree) (sibs : ℕ → UInt256) (k j : ℕ)
    (xPre : List UInt8) : List UInt8 :=
  walkPre keccak sibs j xPre (landing keccak T sibs k j xPre).2

/-- **A BREAK LOCATED AT THE LANDING.** The walk's keccak input and the landing node's keccak input
differ and hash equal (`collision`), or the landing node is a constant with no modelled preimage
and the walk's keccak input hashes to it (`constHit`). Both are facts about strings and values the
instance determines. -/
inductive LandingBreak (keccak : Keccak) (T : PreTree) (sibs : ℕ → UInt256) (k j : ℕ)
    (xPre : List UInt8) : Prop
  | collision (Y : List UInt8) :
      (landing keccak T sibs k j xPre).1.pre? keccak = some Y →
      HashCollision keccak (landingInput keccak T sibs k j xPre) Y →
      LandingBreak keccak T sibs k j xPre
  | constHit (v : UInt256) :
      (landing keccak T sibs k j xPre).1 = .const v →
      keccak (landingInput keccak T sibs k j xPre) = v →
      LandingBreak keccak T sibs k j xPre

/-- The walk reaches a `cut`: its value after the remaining steps is the cut's value. -/
def LandingAtCut (keccak : Keccak) (T : PreTree) (sibs : ℕ → UInt256) (k j : ℕ)
    (xPre : List UInt8) : Prop :=
  ∃ v, (landing keccak T sibs k j xPre).1 = .cut v
    ∧ walkPure (node keccak) sibs 0 (landing keccak T sibs k j xPre).2 j (keccak xPre) = v

/-- The walk's keccak input at the landing IS the landing node's keccak input: an honest leaf
opening, or a 64-byte string doubling as a leaf preimage or as the claimed leaf's preimage. -/
def LandingPreimageMatch (keccak : Keccak) (T : PreTree) (sibs : ℕ → UInt256) (k j : ℕ)
    (xPre : List UInt8) : Prop :=
  (landing keccak T sibs k j xPre).1.pre? keccak = some (landingInput keccak T sibs k j xPre)

/-! ## The chain batch root's honest tree -/

/-- **THE HONEST TREE UNDER A ZKSYNC OS CHAIN BATCH ROOT.** Leaf 0 (the logs root `a`) is cut;
`T1` (the multichain leaf), `T2`, `T3` (the IMT roots) and `R` (the reserved half) describe the rest
(`ChainBatchRootTree.sol:49-62`). -/
def cbrPreTree (a : UInt256) (T1 T2 T3 R : PreTree) : PreTree :=
  .node (.node (.node (.cut a) T1) (.node T2 T3)) R

/-- **THE WALK PASSES THROUGH LEAF 0 AT HEIGHT 3.** The walk is at least 3 steps long, the top
three bits of its mask are zero (`j < 2^(k-3)`), its value after `k - 3` steps is the leaf-0 value
`a`, and its top three siblings are the honest ones: `b`, `node c d`, `RESERVED_SUBTREE_NODE`. -/
def PassesLeafZero (keccak : Keccak) (a b c d : UInt256) (sibs : ℕ → UInt256) (k j : ℕ)
    (x : UInt256) : Prop :=
  3 ≤ k ∧ j < 2 ^ (k - 3) ∧ walkPure (node keccak) sibs 0 (k - 3) j x = a
    ∧ sibs (k - 3) = b ∧ sibs (k - 2) = node keccak c d ∧ sibs (k - 1) = RESERVED_SUBTREE_NODE

/-! ## The interop commitment trees and the reserved half -/

/-- The complete tree of height `h` whose leftmost leaf is entry `o` of `f`. -/
def completePreTree (f : ℕ → PreTree) : ℕ → ℕ → PreTree
  | 0, o => f o
  | h + 1, o => .node (completePreTree f h o) (completePreTree f h (o + 2 ^ h))

/-- **AN INTEROP COMMITMENT TREE AS A `PreTree`.** The complete height-`H` tree over `T`'s leaves:
leaf `m` is `hashLeaf`'s 96-byte preimage of `T.leaf m` while `m < T.leafCount`, and the 34-byte
`IMT_EMPTY_LEAF_HASH` preimage beyond (`IndexedMerkleTree.sol:46-54`, `FullMerkle` padding). -/
def imtPreTree (T : Contracts.InteropCommitmentTree.Tree) (H : ℕ) : PreTree :=
  completePreTree
    (fun m => if m < T.leafCount then .leaf (imtLeafPre (T.leaf m)) else .leaf imtPaddingPre) H 0

/-- The interop commitment tree's root, as `FullMerkle` computes it at height `H` with keccak:
`Contracts.InteropCommitmentTree.root` with node hash `node keccak`, padding
`IMT_EMPTY_LEAF_HASH = keccak imtPaddingPre` and leaf hash `hashLeaf`. -/
def imtRoot (keccak : Keccak) (T : Contracts.InteropCommitmentTree.Tree) (H : ℕ) : UInt256 :=
  Contracts.InteropCommitmentTree.root (node keccak) (keccak imtPaddingPre) (imtHashLeaf keccak) T H

/-- The all-zero tree of height `h` over `const 0` leaves: `zeroPreTree 2` is the reserved half of
the chain batch root (`ChainBatchRootTree.sol:27-30`). -/
def zeroPreTree : ℕ → PreTree
  | 0 => .const 0
  | h + 1 => .node (zeroPreTree h) (zeroPreTree h)

/-- **THE HONEST TREE OF A ZKSYNC OS BATCH WITH ITS TWO IMT SNAPSHOTS.** Leaf 0 cut at `a`, the
multichain leaf `T1`, the IMT at batch begin `Tb` (height `Hb`) and at batch end `Te` (height `He`),
and the reserved zero half. -/
def imtBatchPreTree (a : UInt256) (T1 : PreTree) (Tb : Contracts.InteropCommitmentTree.Tree)
    (Hb : ℕ) (Te : Contracts.InteropCommitmentTree.Tree) (He : ℕ) : PreTree :=
  cbrPreTree a T1 (imtPreTree Tb Hb) (imtPreTree Te He) (zeroPreTree 2)

end Contracts.ChainBatchRootTree
