import EraSpec.Contracts.MessageVerification.Specs.StatusProof

/-!
# Spec: the located breaks of a status proof, as keccak collisions on named byte strings

Source: era-contracts `draft/v0.35.0` head `b17415d20`; `MV` is
`l1-contracts/contracts/common/MessageVerification.sol`.

`_proveL2LogInclusion` does not check the proof's length. The comment at `MV:94-96` gives the
reason:

    // It is ok to not check length of `_proof` array, as length
    // of leaf preimage (which is `L2_TO_L1_LOG_SERIALIZE_SIZE`) is not
    // equal to the length of other nodes preimages (which are `2 * 32`)

`StatusProof`'s `BatchWalkBreak` locates an accepted walk that does not open the batch's log at its
index, over an abstract node hash. Here the node hash is `efficientHash keccak` (keccak of the
64-byte `nodePre`), the logs tree's entries are keccak of 88-byte log preimages or of the 88-byte
padding preimage, and the claimed leaf is keccak of an 88-byte preimage `xPre`. Then every case of
`BatchWalkBreak` but one is a keccak collision on two byte strings the instance names:

* a `PathCollision` is a collision on two 64-byte node preimages (`PathKeccakCollision`);
* a wrong-length case is a collision between an 88-byte string (the claimed preimage, or the
  preimage of a logs-tree entry) and a 64-byte node preimage: the comment's argument, made
  precise. Different lengths make the two strings different, so equal hashes are a collision.

The exception is `otherLeaf`: the walk reaches the multichain root, an interop-tree root or a
reserved zero leaf of the chain batch root tree. Those values are free in this model (their own
trees are not modelled here), so the case stays a located equation, not a keccak statement.
-/

namespace Contracts.MessageVerification

open Contracts.MessageHashing
open MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (HashCollision)

/-- The 64-byte node preimage of an ordered pair, as `walkPair` and `treePair` name their pairs. -/
def pairPre (p : UInt256 × UInt256) : List UInt8 := nodePre p.1 p.2

/-- **A `PathCollision` OF `efficientHash keccak`, AS KECCAK COLLISIONS ON NAMED 64-BYTE STRINGS.**
At a step `i < k` of the walk, the node preimage the verifier hashed and the node preimage the tree
hashed at the same position differ and keccak maps them to the same word. -/
def PathKeccakCollision (keccak : Keccak) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256)
    (lvl k j : ℕ) (x : UInt256) : Prop :=
  ∃ i < k, HashCollision keccak (pairPre (walkPair (efficientHash keccak) sibs lvl j x i))
    (pairPre (treePair (efficientHash keccak) z0 L (lvl + i) (j / 2 ^ i)))

/-- The 88-byte preimage behind position `q` of the logs tree: the `q`-th log's preimage, or the
padding preimage `new bytes(88)` beyond the batch's logs. -/
def logEntryPre (logs : List L2Log) (q : ℕ) : List UInt8 :=
  match logs[q]? with
  | some log => logPre log
  | none => logDefaultPre

/-- **A BREAK OF A STATUS-PROOF WALK, AS KECCAK COLLISIONS ON NAMED BYTE STRINGS.** The tree is the
chain batch root over the logs tree of `logs` at height `H` (node hash `efficientHash keccak`,
padding `keccak logDefaultPre`) and the roots `mc`, `b`, `e`; the claimed leaf is `keccak xPre`.
Abbreviations used below: `h = efficientHash keccak`, `z0 = keccak logDefaultPre`,
`L = logsLeaves keccak logs`, `O = batchLeaves (rootOf h z0 L H) mc b e`, `x = keccak xPre`.

* `shortLeafIsNode`, `shortCollision` (`k < 3`): `xPre` and the 64-byte preimage of a named pair
  of the height-3 tree collide; or a 64-byte collision on the re-anchored walk;
* `top`: a 64-byte collision on the last three steps;
* `otherLeaf`: as in `BatchWalkBreak` (not a keccak statement);
* `logsCollision`: the right shape, and a 64-byte collision on the logs tree;
* `logsLeafIsNode`, `logsShortCollision` (below the top three steps, fewer than `H` steps):
  `xPre` and the preimage of a named logs-tree pair collide; or a 64-byte collision;
* `logsEntryIsNode`, `logsLongCollision` (more than `H` steps): the 88-byte preimage of a named
  logs-tree position and the preimage of the verifier's own pair collide; or a 64-byte
  collision. -/
inductive StatusWalkKeccakBreak (keccak : Keccak) (logs : List L2Log) (H : ℕ) (mc b e : UInt256)
    (sibs : ℕ → UInt256) (k j : ℕ) (xPre : List UInt8) : Prop
  | shortLeafIsNode : k < 3 →
      HashCollision keccak xPre
        (pairPre (treePair (efficientHash keccak) 0
          (batchLeaves (rootOf (efficientHash keccak) (keccak logDefaultPre)
            (logsLeaves keccak logs) H) mc b e) (3 - k - 1) (2 * j))) →
      StatusWalkKeccakBreak keccak logs H mc b e sibs k j xPre
  | shortCollision : k < 3 →
      PathKeccakCollision keccak 0
        (batchLeaves (rootOf (efficientHash keccak) (keccak logDefaultPre)
          (logsLeaves keccak logs) H) mc b e)
        (fun l => sibs (l - (3 - k))) (3 - k) k j (keccak xPre) →
      StatusWalkKeccakBreak keccak logs H mc b e sibs k j xPre
  | top (m : ℕ) : k = m + 3 →
      PathKeccakCollision keccak 0
        (batchLeaves (rootOf (efficientHash keccak) (keccak logDefaultPre)
          (logsLeaves keccak logs) H) mc b e)
        (fun l => sibs (l + m)) 0 3 (j / 2 ^ m)
        (walkPure (efficientHash keccak) sibs 0 m j (keccak xPre)) →
      StatusWalkKeccakBreak keccak logs H mc b e sibs k j xPre
  | otherLeaf (m : ℕ) : k = m + 3 → j / 2 ^ m ≠ 0 →
      walkPure (efficientHash keccak) sibs 0 m j (keccak xPre)
        = (batchLeaves (rootOf (efficientHash keccak) (keccak logDefaultPre)
            (logsLeaves keccak logs) H) mc b e).getD (j / 2 ^ m) 0 →
      StatusWalkKeccakBreak keccak logs H mc b e sibs k j xPre
  | logsCollision : k = H + 3 → j < 2 ^ H →
      PathKeccakCollision keccak (keccak logDefaultPre) (logsLeaves keccak logs) sibs 0 H j
        (keccak xPre) →
      StatusWalkKeccakBreak keccak logs H mc b e sibs k j xPre
  | logsLeafIsNode (m : ℕ) : k = m + 3 → j < 2 ^ m → m < H →
      HashCollision keccak xPre
        (pairPre (treePair (efficientHash keccak) (keccak logDefaultPre) (logsLeaves keccak logs)
          (H - m - 1) (2 * j))) →
      StatusWalkKeccakBreak keccak logs H mc b e sibs k j xPre
  | logsShortCollision (m : ℕ) : k = m + 3 → j < 2 ^ m → m < H →
      PathKeccakCollision keccak (keccak logDefaultPre) (logsLeaves keccak logs)
        (fun l => sibs (l - (H - m))) (H - m) m j (keccak xPre) →
      StatusWalkKeccakBreak keccak logs H mc b e sibs k j xPre
  | logsEntryIsNode (m : ℕ) : k = m + 3 → j < 2 ^ m → H < m →
      HashCollision keccak (logEntryPre logs (j / 2 ^ (m - H)))
        (pairPre (walkPair (efficientHash keccak) sibs 0 j (keccak xPre) (m - H - 1))) →
      StatusWalkKeccakBreak keccak logs H mc b e sibs k j xPre
  | logsLongCollision (m : ℕ) : k = m + 3 → j < 2 ^ m → H < m →
      PathKeccakCollision keccak (keccak logDefaultPre) (logsLeaves keccak logs)
        (fun l => sibs (l + (m - H))) 0 H (j / 2 ^ (m - H))
        (walkPure (efficientHash keccak) sibs 0 (m - H) j (keccak xPre)) →
      StatusWalkKeccakBreak keccak logs H mc b e sibs k j xPre

/-- A stand-in for keccak, used by a witness only: it hashes the padding preimage `new bytes(88)`
to `1` and every other byte string to `2`, so every two other strings collide under it. -/
def twoValuedKeccak : Keccak := fun x => if x = logDefaultPre then 1 else 2

end Contracts.MessageVerification
