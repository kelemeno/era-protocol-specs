import EraSpec.Contracts.MessageHashing.Specs.LogLeafSeparation
import EraSpec.Contracts.Merkle.Specs.PathCollision

/-!
# Spec: an L1 status proof against a ZKsync OS chain batch root

Source: era-contracts `draft/v0.35.0` head `b17415d20`, paths relative to
`l1-contracts/contracts/`. `MV` is `common/MessageVerification.sol`, `MH`
`common/libraries/MessageHashing.sol`, `MRB` `core/message-root/MessageRootBase.sol`, `CBR`
`common/libraries/ChainBatchRootTree.sol`.

## The L1 check

`L1Nullifier._verifyAndClearTransfer` (`bridge/L1Nullifier.sol:218-248`) calls
`MESSAGE_ROOT.proveL1ToL2TransactionStatusShared(chainId, l2TxHash, batch, index, txNumber, proof,
status)`. That function (`MV:129-147`) builds `getL2LogFromL1ToL2Transaction(txNumber, l2TxHash,
status)` and calls `_proveL2LogInclusion` (`MV:85-108`), the function the public
`proveL2LogInclusionShared` (`MV:111-126`) calls with a caller-supplied log. It hashes the log
(`getLeafHashFromLog`) and calls `_proveL2LeafInclusion` with the message index as the Merkle mask.
On L1 that is `MRB._proveL2LeafInclusionRecursive` (`MRB:328-361`):

* `_getProofData` (`MH:152-236`) rejects an empty proof (`:159-161`) and the leaf hash
  `L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH` (`:163-167`), parses the metadata (`:169`), and walks the leaf
  up the log-leaf section of the proof with `Merkle.calculateRootMemory(path, index, leaf)`
  (`:174-178`), which requires `pathLength < 256` and `index < 2^pathLength`
  (`common/libraries/Merkle.sol:53-70, 133-140`);
* on a final-node proof the walk's result must equal `chainBatchRoots[chainId][batch]` and be
  nonzero (`MRB:343-347`, `:364-373`).

`LogProofAccepted` is that conjunction for one log, with the walk as `walkPure`; the mask is the
index `j`, the path the stream `sibs` read at levels `0 .. k-1`, and `R` the stored root.
`StatusProofAccepted` is `LogProofAccepted` on the status log: the status entry point adds no check
of its own beyond fixing the log's shape.

## The tree behind a ZKsync OS batch root (L2 side)

`CBR:6-62`: the chain batch root is a height-3 tree over four live leaves, the batch's L2 → L1 logs
tree root (leaf 0), the chain's multichain root (1), and the interop commitment tree's roots at
batch begin and end (2, 3); leaves 4-7 are zero, and the right subtree over them is the constant
`RESERVED_SUBTREE_NODE`, documented as `keccak(z1 ‖ z1)` with `z1 = keccak(0 ‖ 0)` (`CBR:27-30`).
`chainBatchRoot` is `ChainBatchRootTree.compute` (`CBR:49-62`) with that constant written by its
documented definition. The bootloader computes the root (`CBR:6-8`); the logs tree itself is
built by ZKsync OS and is not in this repository. `BatchRootCommitsLogs` states, as a premise, that
the recorded root is the chain batch root over the `FullMerkle` fold of the batch's log leaves at
some height `H`, padded with `keccak(new bytes(88))`, which `common/Config.sol:26-27` documents as
`L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH`.

`BootloaderLogsAreStatusLogs` is the second L2-side premise: every log of the batch whose sender is
the bootloader is the status log of an L1 → L2 transaction with that transaction's real status.
The L1 side cannot check this: `proveL2LogInclusionShared` accepts a proof for any log the tree
holds, with any sender.

## Model boundaries

* `keccak` is an arbitrary function; the node hash is `efficientHash keccak`, keccak of the
  64-byte `nodePre`.
* Only the final-node branch is modelled. On the multi-hop branch (`MRB:349-360`,
  `core/message-root/L1MessageRoot.sol:96-120`) the same walk's result is wrapped in a batch leaf
  and authenticated against a settlement layer that the chain asset handler accepts for the batch;
  that the result is then the chain's genuine batch root is not modelled here.
* The source compares the leaf with the hex constant `L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH`; the model
  compares it with `keccak logDefaultPre`, the value the constant is documented to be. The batch
  root is likewise compared with a value `R`, not read from storage.
* Reject-only checks not modelled: the empty-proof revert, the metadata version, the
  final-node/length consistency check (`MH:140-142`), `BatchZeroNotAllowed` (`MRB:366`). Leaving
  them out only adds accepted calls.
-/

namespace Contracts.MessageVerification

open Contracts.MessageHashing
open MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (HashCollision)

/-- `Merkle.efficientHash` (`common/libraries/Merkle.sol:125-131`) with keccak: the node hash of
the logs tree and of the chain batch root tree. -/
def efficientHash (keccak : Keccak) : Hash := fun a b => keccak (nodePre a b)

/-- `ChainBatchRootTree.RESERVED_SUBTREE_NODE` (`CBR:27-30`), by its documented definition:
`z2 = h(z1, z1)` with `z1 = h(0, 0)`. -/
def reservedSubtreeNode (h : Hash) : UInt256 := h (h 0 0) (h 0 0)

/-- **THE CHAIN BATCH ROOT.** `ChainBatchRootTree.compute(logsRoot, multichainRoot, imtRootBegin,
imtRootEnd)` (`CBR:49-62`). -/
def chainBatchRoot (h : Hash) (logsRoot multichainRoot imtRootBegin imtRootEnd : UInt256) :
    UInt256 :=
  h (h (h logsRoot multichainRoot) (h imtRootBegin imtRootEnd)) (reservedSubtreeNode h)

/-- The four live leaves of the chain batch root tree, in order (`CBR:13-25`). -/
def batchLeaves (logsRoot multichainRoot imtRootBegin imtRootEnd : UInt256) : List UInt256 :=
  [logsRoot, multichainRoot, imtRootBegin, imtRootEnd]

/-! ## The walk against a chain batch root, over an abstract node hash -/

/-- **A BREAK OF A WALK ACCEPTED AGAINST A CHAIN BATCH ROOT, LOCATED.** The chain batch root here is
`chainBatchRoot h (rootOf h z0 L H) mc b e`: the logs tree over `L` at height `H` with padding `z0`,
under the height-3 tree over `[logs root, mc, b, e]` (padding 0). The walk has length `k`, index
`j`, claimed leaf `x`, siblings `sibs`. When `k = m + 3`, its first `m` steps reach a value at level
`m` of index `j / 2^m`, and its last three steps climb the height-3 tree from there.

* `short`: `k < 3`, and the walk is a wrong-length break (`HeightBreak`) of the height-3 tree;
* `top`: the last three steps collide on the height-3 tree (`PathCollision`, shifted siblings);
* `otherLeaf`: below the last three steps the walk reaches index `q = j / 2^m ≠ 0` of the height-3
  tree, and its value there IS that tree's leaf `q`: the multichain root, an interop-tree root, or a
  reserved zero, not the logs root;
* `logsCollision`: the walk has the right shape (`k = H + 3`, `j < 2^H`) and its first `H` steps
  collide on the logs tree;
* `logsHeight`: below the last three steps the walk stays in the logs root's subtree
  (`j < 2^m`) and is a wrong-length break of the logs tree (`m ≠ H`).

Every compared value is a function of the instance. -/
inductive BatchWalkBreak (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ)
    (mc b e : UInt256) (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256) : Prop
  | short : k < 3 →
      HeightBreak h 0 (batchLeaves (rootOf h z0 L H) mc b e) sibs k 3 j x →
      BatchWalkBreak h z0 L H mc b e sibs k j x
  | top (m : ℕ) : k = m + 3 →
      PathCollision h 0 (batchLeaves (rootOf h z0 L H) mc b e) (fun l => sibs (l + m)) 0 3
        (j / 2 ^ m) (walkPure h sibs 0 m j x) →
      BatchWalkBreak h z0 L H mc b e sibs k j x
  | otherLeaf (m : ℕ) : k = m + 3 → j / 2 ^ m ≠ 0 →
      walkPure h sibs 0 m j x = (batchLeaves (rootOf h z0 L H) mc b e).getD (j / 2 ^ m) 0 →
      BatchWalkBreak h z0 L H mc b e sibs k j x
  | logsCollision : k = H + 3 → j < 2 ^ H → PathCollision h z0 L sibs 0 H j x →
      BatchWalkBreak h z0 L H mc b e sibs k j x
  | logsHeight (m : ℕ) : k = m + 3 → j < 2 ^ m → HeightBreak h z0 L sibs m H j x →
      BatchWalkBreak h z0 L H mc b e sibs k j x

/-- The honest sibling stream of logs-tree index `j` through the chain batch root: the logs tree's
own siblings (`honestSibs`) at levels below `H`, then those of leaf 0 of the height-3 tree. -/
def honestBatchSibs (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ) (mc b e : UInt256)
    (j : ℕ) : ℕ → UInt256 := fun l =>
  if l < H then honestSibs h z0 L j l
  else honestSibs h 0 (batchLeaves (rootOf h z0 L H) mc b e) 0 (l - H)

/-! ## The L1 check -/

/-- **`_proveL2LogInclusion` RETURNS `true` ON THE FINAL-NODE BRANCH**, for the log `ℓ`, mask `j`,
log-leaf path `sibs` of length `k`, against the stored batch root `R`: the leaf is not the default
leaf hash (`MH:163-167`), `k < 256` and `j < 2^k` (`Merkle.sol:133-140`), the walk reaches `R`, and
`R ≠ 0` (`MRB:343-347`). -/
def LogProofAccepted (keccak : Keccak) (R : UInt256) (ℓ : L2Log) (j : ℕ) (sibs : ℕ → UInt256)
    (k : ℕ) : Prop :=
  logLeaf keccak ℓ ≠ keccak logDefaultPre ∧ k < 256 ∧ j < 2 ^ k
    ∧ walkPure (efficientHash keccak) sibs 0 k j (logLeaf keccak ℓ) = R ∧ R ≠ 0

/-- **`proveL1ToL2TransactionStatusShared(…, txNumber, …, status)` RETURNS `true`** (`MV:129-147`):
the log check on `getL2LogFromL1ToL2Transaction(txNumber, txHash, status)`. -/
def StatusProofAccepted (keccak : Keccak) (R : UInt256) (t : ℕ) (tx : UInt256) (s : TxStatus)
    (j : ℕ) (sibs : ℕ → UInt256) (k : ℕ) : Prop :=
  LogProofAccepted keccak R (statusLog t tx s) j sibs k

/-! ## The L2 side -/

/-- The logs tree's level-0 list: the leaf hashes of the batch's logs, in order. -/
def logsLeaves (keccak : Keccak) (logs : List L2Log) : List UInt256 := logs.map (logLeaf keccak)

/-- The batch's logs tree root: the `FullMerkle` fold of the log leaves at height `H`, padded with
`keccak(new bytes(88))`. -/
def logsRootOf (keccak : Keccak) (logs : List L2Log) (H : ℕ) : UInt256 :=
  rootOf (efficientHash keccak) (keccak logDefaultPre) (logsLeaves keccak logs) H

/-- **L2-SIDE PREMISE: THE RECORDED ROOT COMMITS THE BATCH'S LOGS.** `R` is the chain batch root
over the logs tree of `logs` at height `H`, with multichain root `mc` and interop-tree roots `b`,
`e`. -/
def BatchRootCommitsLogs (keccak : Keccak) (R : UInt256) (logs : List L2Log) (H : ℕ)
    (mc b e : UInt256) : Prop :=
  R = chainBatchRoot (efficientHash keccak) (logsRootOf keccak logs H) mc b e

/-- **L2-SIDE PREMISE: BOOTLOADER LOGS ARE GENUINE STATUS LOGS.** Every log of the batch whose
sender is the bootloader is `statusLog t tx s` for some transaction number `t`, transaction `tx` and
status `s`, and `s` is `tx`'s real status (`truth tx = some s`). -/
def BootloaderLogsAreStatusLogs (truth : UInt256 → Option TxStatus) (logs : List L2Log) : Prop :=
  ∀ log ∈ logs, log.sender = BOOTLOADER_ADDRESS →
    ∃ (t : ℕ) (tx : UInt256) (s : TxStatus), log = statusLog t tx s ∧ truth tx = some s

/-- A stand-in for keccak, used by the witnesses only: it hashes the padding preimage
`new bytes(88)` to `1` and every other byte string to its length. All 88-byte logs collide under
it; the padding leaf and node hashes (`64`) do not meet a log leaf (`88`). -/
def paddingAwareLengthKeccak : Keccak := fun x =>
  if x = logDefaultPre then 1 else Nat.toUInt256 x.length

end Contracts.MessageVerification
