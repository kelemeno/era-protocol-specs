import EraSpec.Contracts.MessageVerification.Specs.StatusProof
import EraSpec.Core.Headline

/-!
# Properties: an accepted status proof for a status the batch never recorded locates a break

Statements about `../Specs/StatusProof.lean`. Proofs: `../Proofs/StatusProof.lean`.

No property takes a premise about the hash. Groups, in order:

* the walk over an abstract node hash: `ChainBatchRootTree.compute` is the height-3 fold, and a
  walk accepted against a chain batch root opens the logs tree's entry at its index with the
  right shape, or is a located `BatchWalkBreak`; the honest proof is accepted with no break;
* the L1 check over keccak: a log proof of a log the batch does not hold, and a status proof
  whose status is not the transaction's real status (headline: a Failure proof for a transaction
  that succeeded), are accepted only with a keccak collision on the batch's log at the proof's
  index and the claimed log (two named 88-byte preimages), or a located `BatchWalkBreak`; and every
  log the batch holds is provable;
* a witness meeting every premise of the three, and two countermodels: without the L2-side
  premise `BootloaderLogsAreStatusLogs`, and without the default-leaf check, a proof passing the
  remaining checks satisfies neither disjunct of the conclusion.
-/

namespace Contracts.MessageVerification

open Contracts.MessageHashing
open MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (HashCollision)

/-! ## The walk, over an abstract node hash -/

/-- **`ChainBatchRootTree.compute` IS THE HEIGHT-3 FOLD** over its four live leaves with zero
padding: the reserved right subtree is the zero cascade's level-2 node. -/
def Properties.ChainBatchRootIsFold : Prop :=
  ∀ (h : Hash) (a b c d : UInt256), chainBatchRoot h a b c d = rootOf h 0 (batchLeaves a b c d) 3

/-- **A WALK ACCEPTED AGAINST A CHAIN BATCH ROOT OPENS THE LOGS TREE, OR A LOCATED BREAK.** For any
node hash `h`: a walk of any length `k` from any index `j < 2^k` whose result is the chain batch
root over the logs tree (`L`, padding `z0`, height `H`) and the roots `mc`, `b`, `e` has length
`H + 3`, an index below `2^H`, and claimed leaf `L.getD j z0` (the `j`-th leaf hash, or the padding
constant if `j` is not occupied); or it is a `BatchWalkBreak`. -/
def Properties.BatchWalkOpensLogsEntryOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ) (mc b e : UInt256)
    (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256),
    j < 2 ^ k → walkPure h sibs 0 k j x = chainBatchRoot h (rootOf h z0 L H) mc b e →
      (k = H + 3 ∧ j < 2 ^ H ∧ L.getD j z0 = x) ∨ BatchWalkBreak h z0 L H mc b e sibs k j x

/-- **WITNESS FOR `BatchWalkOpensLogsEntryOrBreak`, AND `BatchWalkBreak` IS NOT A TAUTOLOGY.** For
every node hash, logs tree, roots `mc`, `b`, `e` and index `j < 2^H` (occupied or padded), the
honest stream of length `H + 3` meets both premises (`j < 2^(H+3)`, and the walk from
`L.getD j z0` reaches the chain batch root), and no case of `BatchWalkBreak` holds on it. -/
@[witness] def Properties.HonestBatchWalkNoBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ) (mc b e : UInt256) (j : ℕ), j < 2 ^ H →
    j < 2 ^ (H + 3)
      ∧ walkPure h (honestBatchSibs h z0 L H mc b e j) 0 (H + 3) j (L.getD j z0)
          = chainBatchRoot h (rootOf h z0 L H) mc b e
      ∧ ¬ BatchWalkBreak h z0 L H mc b e (honestBatchSibs h z0 L H mc b e j) (H + 3) j
          (L.getD j z0)

/-! ## The L1 check, over keccak -/

/-- **(d) A LOG PROOF OF A LOG THE BATCH DOES NOT HOLD LOCATES A BREAK.** Let the recorded root
commit the batch's well-formed logs (`BatchRootCommitsLogs`), and let `ℓ` be a well-formed log that
is not one of them. If `_proveL2LogInclusion` returns `true` for `ℓ` on the final-node branch
(`LogProofAccepted`), then either the proof has the logs tree's shape (`k = H + 3`, `j < 2^H`), the
batch holds a log at position `j`, and keccak collides on that log's 88-byte preimage and `ℓ`'s; or
the walk is a `BatchWalkBreak`. -/
def Properties.LogProofOfAbsentLogLocatesBreak : Prop :=
  ∀ (keccak : Keccak) (logs : List L2Log) (H : ℕ) (mc b e R : UInt256) (ℓ : L2Log) (j : ℕ)
    (sibs : ℕ → UInt256) (k : ℕ),
    (∀ log ∈ logs, LogWellFormed log) → LogWellFormed ℓ → ℓ ∉ logs →
    BatchRootCommitsLogs keccak R logs H mc b e → LogProofAccepted keccak R ℓ j sibs k →
      (k = H + 3 ∧ j < 2 ^ H
          ∧ ∃ log : L2Log, logs[j]? = some log ∧ HashCollision keccak (logPre log) (logPre ℓ))
        ∨ BatchWalkBreak (efficientHash keccak) (keccak logDefaultPre) (logsLeaves keccak logs) H
            mc b e sibs k j (logLeaf keccak ℓ)

/-- **(d)+(e) A STATUS PROOF OF A STATUS THE TRANSACTION DID NOT HAVE LOCATES A BREAK.** Let the
recorded root commit the batch's well-formed logs, and let every bootloader log of the batch be a
genuine status log (`BootloaderLogsAreStatusLogs truth`). If `proveL1ToL2TransactionStatusShared`
returns `true` on the final-node branch (`StatusProofAccepted`) for status `s` of `tx`
(transaction number `t < 2^16`) while `s` is not `tx`'s real status
(`truth tx ≠ some s`), then the proof has the logs tree's shape, the batch holds a log at position
`j`, and keccak collides on that log's preimage and the claimed status log's; or the walk is a
`BatchWalkBreak`. -/
def Properties.StatusProofOfUnrealStatusLocatesBreak : Prop :=
  ∀ (keccak : Keccak) (logs : List L2Log) (H : ℕ) (mc b e R : UInt256)
    (truth : UInt256 → Option TxStatus) (t : ℕ) (tx : UInt256) (s : TxStatus) (j : ℕ)
    (sibs : ℕ → UInt256) (k : ℕ),
    (∀ log ∈ logs, LogWellFormed log) → t < 256 ^ 2 →
    BatchRootCommitsLogs keccak R logs H mc b e → BootloaderLogsAreStatusLogs truth logs →
    truth tx ≠ some s → StatusProofAccepted keccak R t tx s j sibs k →
      (k = H + 3 ∧ j < 2 ^ H
          ∧ ∃ log : L2Log, logs[j]? = some log
            ∧ HashCollision keccak (logPre log) (logPre (statusLog t tx s)))
        ∨ BatchWalkBreak (efficientHash keccak) (keccak logDefaultPre) (logsLeaves keccak logs) H
            mc b e sibs k j (logLeaf keccak (statusLog t tx s))

/-- **HEADLINE (d)+(e). A FAILURE PROOF FOR A TRANSACTION THAT SUCCEEDED LOCATES A BREAK.**
`StatusProofOfUnrealStatusLocatesBreak` at `s = Failure` and `truth tx = some Success`. The check
that `L1Nullifier.bridgeRecoverFailedTransfer` makes before a deposit is refunded
(`bridge/L1Nullifier.sol:202, 222-231`), as modelled on the final-node branch, accepts such a proof
only with a keccak collision on the batch's log at the proof's index and the Failure log (two
named 88-byte preimages), or a located `BatchWalkBreak`. -/
def Properties.FailureProofForSucceededTxLocatesBreak : Prop :=
  ∀ (keccak : Keccak) (logs : List L2Log) (H : ℕ) (mc b e R : UInt256)
    (truth : UInt256 → Option TxStatus) (t : ℕ) (tx : UInt256) (j : ℕ) (sibs : ℕ → UInt256)
    (k : ℕ),
    (∀ log ∈ logs, LogWellFormed log) → t < 256 ^ 2 →
    BatchRootCommitsLogs keccak R logs H mc b e → BootloaderLogsAreStatusLogs truth logs →
    truth tx = some .success → StatusProofAccepted keccak R t tx .failure j sibs k →
      (k = H + 3 ∧ j < 2 ^ H
          ∧ ∃ log : L2Log, logs[j]? = some log
            ∧ HashCollision keccak (logPre log) (logPre (statusLog t tx .failure)))
        ∨ BatchWalkBreak (efficientHash keccak) (keccak logDefaultPre) (logsLeaves keccak logs) H
            mc b e sibs k j (logLeaf keccak (statusLog t tx .failure))

/-- **COMPLETENESS: EVERY LOG THE BATCH HOLDS IS PROVABLE.** For every keccak, batch and position
`j < 2^H` holding `log`, with `H + 3 < 256`, a nonzero recorded root and a leaf that is not the
default leaf hash, the honest proof of position `j` passes `LogProofAccepted` for `log`, whatever
its sender. For a status log this is `StatusProofAccepted`: a status the batch recorded is
provable. And the L1 check cannot tell a genuine status log from another bootloader-sender log the
batch holds, which is why `BootloaderLogsAreStatusLogs` is a premise above. -/
@[headline] def Properties.HeldLogIsProvable : Prop :=
  ∀ (keccak : Keccak) (logs : List L2Log) (H : ℕ) (mc b e R : UInt256) (j : ℕ) (log : L2Log),
    BatchRootCommitsLogs keccak R logs H mc b e → logs[j]? = some log → j < 2 ^ H →
    H + 3 < 256 → R ≠ 0 → logLeaf keccak log ≠ keccak logDefaultPre →
      LogProofAccepted keccak R log j
        (honestBatchSibs (efficientHash keccak) (keccak logDefaultPre) (logsLeaves keccak logs) H
          mc b e j) (H + 3)

/-- **WITNESS FOR `HeldLogIsProvable`.** With `paddingAwareLengthKeccak`, a batch at logs-tree
height 1 holding a message log at position 0 and the Failure status log of transaction 5
(number 3) at position 1 meets every premise at `j = 1`, and the honest proof passes
`StatusProofAccepted` for that Failure log. -/
@[witness] def Properties.HeldLogIsProvableWitness : Prop :=
  let K := paddingAwareLengthKeccak
  let logs : List L2Log := [messageLog K ⟨2, 0x1234, [1, 2, 3]⟩, statusLog 3 5 .failure]
  let R := chainBatchRoot (efficientHash K) (logsRootOf K logs 1) 0 7 7
  BatchRootCommitsLogs K R logs 1 0 7 7 ∧ logs[1]? = some (statusLog 3 5 .failure)
    ∧ (1 : ℕ) < 2 ^ 1 ∧ 1 + 3 < 256 ∧ R ≠ 0
    ∧ logLeaf K (statusLog 3 5 .failure) ≠ K logDefaultPre
    ∧ StatusProofAccepted K R 3 5 .failure 1
        (honestBatchSibs (efficientHash K) (K logDefaultPre) (logsLeaves K logs) 1 0 7 7 1) 4

/-! ## Witness and countermodels -/

/-- **WITNESS FOR THE THREE (d) STATEMENTS.** With the stand-in `paddingAwareLengthKeccak` (all
88-byte logs collide under it): a batch at logs-tree height 1 holding a message log at position 0
and the Success status log of transaction 5 (number 3) at position 1, with real status Success for
transaction 5, and an accepted Failure proof for it at index 1. Every premise of
`FailureProofForSucceededTxLocatesBreak`, `StatusProofOfUnrealStatusLocatesBreak` (at
`s = Failure`) and `LogProofOfAbsentLogLocatesBreak` (at `ℓ` the Failure log) holds; the proof has
the honest shape, and what the theorems locate is the keccak collision between the Success log at
the proof's index and the Failure log. -/
@[witness] def Properties.StatusProofWitness : Prop :=
  ∃ (keccak : Keccak) (logs : List L2Log) (H : ℕ) (mc b e R : UInt256)
    (truth : UInt256 → Option TxStatus) (t : ℕ) (tx : UInt256) (j : ℕ) (sibs : ℕ → UInt256)
    (k : ℕ),
    (∀ log ∈ logs, LogWellFormed log) ∧ t < 256 ^ 2
      ∧ LogWellFormed (statusLog t tx .failure) ∧ statusLog t tx .failure ∉ logs
      ∧ BatchRootCommitsLogs keccak R logs H mc b e ∧ BootloaderLogsAreStatusLogs truth logs
      ∧ truth tx = some .success ∧ truth tx ≠ some .failure
      ∧ StatusProofAccepted keccak R t tx .failure j sibs k
      ∧ 0 < H ∧ t ≠ 0 ∧ tx ≠ 0 ∧ (∃ log ∈ logs, log.sender = MESSENGER_ADDRESS)
      ∧ k = H + 3 ∧ j < 2 ^ H ∧ logs[j]? = some (statusLog t tx .success)
      ∧ HashCollision keccak (logPre (statusLog t tx .success)) (logPre (statusLog t tx .failure))

/-- **COUNTERMODEL: THE L2-SIDE PREMISE IS LOAD-BEARING.** A batch at logs-tree height 1 holds a log
from another sender at position 0 and, at position 1, a bootloader log that is the Failure status
log of transaction 5 while 5's real status is Success. So `BootloaderLogsAreStatusLogs` fails and
every other premise of `FailureProofForSucceededTxLocatesBreak` holds. For every keccak under which
the recorded root is nonzero and the Failure leaf is not the default leaf hash, the honest Failure
proof of position 1 is accepted and the conclusion fails: no collision, no break.
`paddingAwareLengthKeccak` is such a keccak. -/
@[countermodel] def Properties.BootloaderPremiseLoadBearing : Prop :=
  ∃ (logs : List L2Log) (H : ℕ) (mc b e : UInt256) (truth : UInt256 → Option TxStatus) (t : ℕ)
    (tx : UInt256) (j k : ℕ),
    (∀ log ∈ logs, LogWellFormed log) ∧ t < 256 ^ 2 ∧ truth tx = some .success
      ∧ ¬ BootloaderLogsAreStatusLogs truth logs
      ∧ (∀ keccak : Keccak,
          chainBatchRoot (efficientHash keccak) (logsRootOf keccak logs H) mc b e ≠ 0 →
          logLeaf keccak (statusLog t tx .failure) ≠ keccak logDefaultPre →
          ∃ sibs : ℕ → UInt256,
            StatusProofAccepted keccak
                (chainBatchRoot (efficientHash keccak) (logsRootOf keccak logs H) mc b e)
                t tx .failure j sibs k
            ∧ ¬ ((k = H + 3 ∧ j < 2 ^ H
                  ∧ ∃ log : L2Log, logs[j]? = some log
                    ∧ HashCollision keccak (logPre log) (logPre (statusLog t tx .failure)))
                ∨ BatchWalkBreak (efficientHash keccak) (keccak logDefaultPre)
                    (logsLeaves keccak logs) H mc b e sibs k j
                    (logLeaf keccak (statusLog t tx .failure))))
      ∧ chainBatchRoot (efficientHash paddingAwareLengthKeccak)
          (logsRootOf paddingAwareLengthKeccak logs H) mc b e ≠ 0
      ∧ logLeaf paddingAwareLengthKeccak (statusLog t tx .failure)
          ≠ paddingAwareLengthKeccak logDefaultPre

/-- **COUNTERMODEL: THE DEFAULT-LEAF CHECK IS LOAD-BEARING.** Drop `_getProofData`'s rejection of
the default leaf hash (`MH:163-167`) from `LogProofAccepted`. A batch at logs-tree height 1 holding
one well-formed log has a padded position 1; the all-zero log, well-formed and not in the batch,
has preimage `new bytes(88)`, so its leaf is the padding constant, and for every keccak under which
the recorded root is nonzero the honest proof of position 1 passes every remaining check while
the conclusion of `LogProofOfAbsentLogLocatesBreak` fails. `paddingAwareLengthKeccak` is such a
keccak. Status logs are never the zero log (`StatusPreimageNeDefault`). -/
@[countermodel] def Properties.DefaultLeafCheckLoadBearing : Prop :=
  ∃ (logs : List L2Log) (H : ℕ) (mc b e : UInt256) (j k : ℕ),
    (∀ log ∈ logs, LogWellFormed log) ∧ LogWellFormed zeroLog ∧ zeroLog ∉ logs
      ∧ logLeaf paddingAwareLengthKeccak zeroLog = paddingAwareLengthKeccak logDefaultPre
      ∧ (∀ keccak : Keccak,
          chainBatchRoot (efficientHash keccak) (logsRootOf keccak logs H) mc b e ≠ 0 →
          ∃ sibs : ℕ → UInt256,
            k < 256 ∧ j < 2 ^ k
            ∧ walkPure (efficientHash keccak) sibs 0 k j (logLeaf keccak zeroLog)
                = chainBatchRoot (efficientHash keccak) (logsRootOf keccak logs H) mc b e
            ∧ ¬ ((k = H + 3 ∧ j < 2 ^ H
                  ∧ ∃ log : L2Log, logs[j]? = some log
                    ∧ HashCollision keccak (logPre log) (logPre zeroLog))
                ∨ BatchWalkBreak (efficientHash keccak) (keccak logDefaultPre)
                    (logsLeaves keccak logs) H mc b e sibs k j (logLeaf keccak zeroLog)))
      ∧ chainBatchRoot (efficientHash paddingAwareLengthKeccak)
          (logsRootOf paddingAwareLengthKeccak logs H) mc b e ≠ 0

end Contracts.MessageVerification
