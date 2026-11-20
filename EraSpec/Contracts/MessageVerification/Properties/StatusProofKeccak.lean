import EraSpec.Contracts.MessageVerification.Specs.StatusProofKeccak
import EraSpec.Core.Headline

/-!
# Properties: the located breaks of a status proof are keccak collisions on named byte strings

Statements about `../Specs/StatusProofKeccak.lean`. Proofs: `../Proofs/StatusProofKeccak.lean`.

No property takes a premise about keccak. The content is that the strings each collision names
differ: two node preimages differ when their pairs do (`PathCollisionIffKeccakCollision`), and an
88-byte log or padding preimage differs from every 64-byte node preimage, which is the fact the
comment at `common/MessageVerification.sol:94-96` relies on (`BatchWalkBreakIffKeccakBreak`).
-/

namespace Contracts.MessageVerification

open Contracts.MessageHashing
open MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (HashCollision)

/-- **A `PathCollision` OF `efficientHash keccak` IS EXACTLY A 64-BYTE KECCAK COLLISION** on the two
named node preimages at the same step: the pairs differ iff their preimages do. -/
def Properties.PathCollisionIffKeccakCollision : Prop :=
  ∀ (keccak : Keccak) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (lvl k j : ℕ)
    (x : UInt256),
    PathCollision (efficientHash keccak) z0 L sibs lvl k j x
      ↔ PathKeccakCollision keccak z0 L sibs lvl k j x

/-- **`BatchWalkBreak`, OVER KECCAK, IS EXACTLY `StatusWalkKeccakBreak`.** For the keccak-built
chain batch root over the logs of a batch and an 88-byte claimed preimage `xPre` (every log
preimage is 88 bytes, `LeafAndNodePreimageLengths`), a `BatchWalkBreak` of the walk from
`keccak xPre` holds iff a `StatusWalkKeccakBreak` does: each wrong-length case is a collision
between an 88-byte and a 64-byte string, each path case a 64-byte collision, and `otherLeaf` is
unchanged. -/
def Properties.BatchWalkBreakIffKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (logs : List L2Log) (H : ℕ) (mc b e : UInt256) (sibs : ℕ → UInt256)
    (k j : ℕ) (xPre : List UInt8), xPre.length = 88 →
    (BatchWalkBreak (efficientHash keccak) (keccak logDefaultPre) (logsLeaves keccak logs) H mc b e
        sibs k j (keccak xPre)
      ↔ StatusWalkKeccakBreak keccak logs H mc b e sibs k j xPre)

/-- **HEADLINE, DOWN TO KECCAK: A FAILURE PROOF FOR A TRANSACTION THAT SUCCEEDED.** Under the
premises of `FailureProofForSucceededTxLocatesBreak` (met by `StatusProofWitness`), an accepted
Failure proof gives a keccak collision between the batch's log at the proof's index and the Failure
log (two 88-byte preimages), or a `StatusWalkKeccakBreak`: a collision on named byte strings in
every case except `otherLeaf`. -/
@[headline] def Properties.FailureProofForSucceededTxIsKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (logs : List L2Log) (H : ℕ) (mc b e R : UInt256)
    (truth : UInt256 → Option TxStatus) (t : ℕ) (tx : UInt256) (j : ℕ) (sibs : ℕ → UInt256)
    (k : ℕ),
    (∀ log ∈ logs, LogWellFormed log) → t < 256 ^ 2 →
    BatchRootCommitsLogs keccak R logs H mc b e → BootloaderLogsAreStatusLogs truth logs →
    truth tx = some .success → StatusProofAccepted keccak R t tx .failure j sibs k →
      (k = H + 3 ∧ j < 2 ^ H
          ∧ ∃ log : L2Log, logs[j]? = some log
            ∧ HashCollision keccak (logPre log) (logPre (statusLog t tx .failure)))
        ∨ StatusWalkKeccakBreak keccak logs H mc b e sibs k j (logPre (statusLog t tx .failure))

/-- **`StatusWalkKeccakBreak` IS NOT A TAUTOLOGY.** For every keccak, batch and index `j < 2^H`,
the honest proof of position `j` claims the preimage `logEntryPre logs j` (whose hash is the tree's
entry there), and no case of `StatusWalkKeccakBreak` holds on it. -/
@[witness] def Properties.HonestStatusWalkNoKeccakBreak : Prop :=
  ∀ (keccak : Keccak) (logs : List L2Log) (H : ℕ) (mc b e : UInt256) (j : ℕ), j < 2 ^ H →
    keccak (logEntryPre logs j) = (logsLeaves keccak logs).getD j (keccak logDefaultPre)
      ∧ ¬ StatusWalkKeccakBreak keccak logs H mc b e
          (honestBatchSibs (efficientHash keccak) (keccak logDefaultPre) (logsLeaves keccak logs) H
            mc b e j) (H + 3) j (logEntryPre logs j)

/-- **WITNESS: A ZERO-LENGTH FAILURE PROOF IS A CROSS-LENGTH COLLISION.** With the stand-in
`twoValuedKeccak`, for a batch at logs-tree height 1 holding only the Success log of transaction 5
(number 3): the Failure proof with an empty log-leaf path at index 0 passes every modelled check of
`StatusProofAccepted`, because the Failure leaf hash equals the chain batch root. (The proof format
with a metadata word allows an empty log-leaf path: `logLeafProofLen = 0`,
`common/libraries/MessageHashing.sol:101-143`.) The break located is `shortLeafIsNode`: keccak
collides on the 88-byte Failure preimage and the 64-byte preimage of the height-3 tree's top pair.
Both sides of `BatchWalkBreakIffKeccakBreak` hold here. -/
@[countermodel] def Properties.ShortStatusProofIsCrossLengthCollision : Prop :=
  StatusProofAccepted twoValuedKeccak
      (chainBatchRoot (efficientHash twoValuedKeccak)
        (logsRootOf twoValuedKeccak [statusLog 3 5 .success] 1) 0 7 7)
      3 5 .failure 0 (fun _ => 0) 0
    ∧ BatchWalkBreak (efficientHash twoValuedKeccak) (twoValuedKeccak logDefaultPre)
        (logsLeaves twoValuedKeccak [statusLog 3 5 .success]) 1 0 7 7 (fun _ => 0) 0 0
        (twoValuedKeccak (logPre (statusLog 3 5 .failure)))
    ∧ StatusWalkKeccakBreak twoValuedKeccak [statusLog 3 5 .success] 1 0 7 7 (fun _ => 0) 0 0
        (logPre (statusLog 3 5 .failure))
    ∧ HashCollision twoValuedKeccak (logPre (statusLog 3 5 .failure))
        (pairPre (treePair (efficientHash twoValuedKeccak) 0
          (batchLeaves (logsRootOf twoValuedKeccak [statusLog 3 5 .success] 1) 0 7 7) 2 0))

end Contracts.MessageVerification
