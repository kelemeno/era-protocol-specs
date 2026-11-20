import EraSpec.Contracts.MessageHashing.Specs.LogLeafSeparation
import EraSpec.Core.Headline

/-!
# Properties: a status log's leaf preimage differs from every other log's

Statements about `../Specs/LogLeafSeparation.lean`. Proofs: `../Proofs/LogLeafSeparation.lean`.

No property takes a premise about `keccak`. Groups, in order:

* (a) the preimage: 88 bytes for every log, 64 for every node (the lengths the comment at
  `common/MessageVerification.sol:94-96` relies on), and injective on well-formed logs;
* (b) status logs: a Failure preimage is never a Success preimage, a status preimage determines
  its transaction number, hash and status, and no status preimage is a message preimage, the
  padding preimage, or the preimage of any well-formed log with another sender;
* (c) pinned forms: equal leaf hashes of two different well-formed logs are a keccak collision on
  their two named 88-byte preimages; for two different well-formed messages, a collision on those
  or on the two message bodies.

Each premise-carrying statement has a witness instantiating every premise, and the collision
predicates are shown false on named instances.
-/

namespace Contracts.MessageHashing

open AttackVectors.BundleHashEncoding (HashCollision toBytesBE word)

/-! ## (a) The preimage -/

/-- **THE PREIMAGE LENGTHS.** Every log's leaf preimage is 88 bytes and every node preimage
`Merkle.efficientHash` hashes is 64 bytes. These are the lengths the comment at
`MessageVerification.sol:94-96` cites for leaving the proof length unchecked. -/
def Properties.LeafAndNodePreimageLengths : Prop :=
  (∀ log : L2Log, (logPre log).length = 88) ∧ ∀ a b : UInt256, (nodePre a b).length = 64

/-- **(a) THE PREIMAGE DETERMINES A WELL-FORMED LOG.** Two well-formed logs with the same leaf
preimage are the same log. -/
def Properties.LogPreimageInjective : Prop :=
  ∀ log log' : L2Log, LogWellFormed log → LogWellFormed log' → logPre log = logPre log' →
    log = log'

/-- **WITNESS FOR `LogPreimageInjective`.** Its premises hold on a status log with nonzero
transaction number and hash; and without well-formedness the conclusion fails: transaction
numbers `0` and `2^16` give the same packed preimage (`toBytesBE 2` keeps the low two bytes), which
a `uint16` field cannot hold. -/
@[witness] def Properties.LogPreimageInjectiveWitness : Prop :=
  (∃ log log' : L2Log, LogWellFormed log ∧ LogWellFormed log' ∧ logPre log = logPre log'
      ∧ log.txNumberInBatch ≠ 0 ∧ log.key ≠ 0 ∧ log.sender = BOOTLOADER_ADDRESS)
    ∧ ∃ log log' : L2Log, log ≠ log' ∧ logPre log = logPre log'
        ∧ LogWellFormed log ∧ ¬ LogWellFormed log'

/-! ## (b) Status logs -/

/-- **(b) A FAILURE PREIMAGE IS NEVER A SUCCESS PREIMAGE**, for any transaction numbers and hashes:
the last 32 bytes are the status word, 0 against 1. No well-formedness premise. -/
def Properties.StatusPreimageFailureNeSuccess : Prop :=
  ∀ (t t' : ℕ) (tx tx' : UInt256),
    logPre (statusLog t tx .failure) ≠ logPre (statusLog t' tx' .success)

/-- **(b) A STATUS PREIMAGE DETERMINES ITS TRANSACTION NUMBER, HASH AND STATUS**, for transaction
numbers that fit a `uint16`. -/
def Properties.StatusPreimageInjective : Prop :=
  ∀ (t t' : ℕ) (tx tx' : UInt256) (s s' : TxStatus), t < 256 ^ 2 → t' < 256 ^ 2 →
    logPre (statusLog t tx s) = logPre (statusLog t' tx' s') → t = t' ∧ tx = tx' ∧ s = s'

/-- **WITNESS FOR `StatusPreimageInjective`.** Its premises hold at transaction number 7 and hash 5
(equal preimages need equal arguments, so both sides carry them); and the `uint16` bound is needed:
transaction numbers `0` and `2^16` with the same hash and status give the same preimage. -/
@[witness] def Properties.StatusPreimageInjectiveWitness : Prop :=
  (∃ (t t' : ℕ) (tx tx' : UInt256) (s s' : TxStatus), t < 256 ^ 2 ∧ t' < 256 ^ 2
      ∧ logPre (statusLog t tx s) = logPre (statusLog t' tx' s') ∧ t ≠ 0 ∧ tx ≠ 0)
    ∧ ∀ (tx : UInt256) (s : TxStatus),
        logPre (statusLog 0 tx s) = logPre (statusLog (256 ^ 2) tx s)

/-- **(b) NO STATUS PREIMAGE IS A MESSAGE PREIMAGE**, for every keccak, status and message: bytes
4..24 are the sender, `0x…8001` against `0x…8008`. No well-formedness premise. -/
def Properties.StatusPreimageNeMessagePreimage : Prop :=
  ∀ (keccak : Keccak) (t : ℕ) (tx : UInt256) (s : TxStatus) (m : L2Message),
    logPre (statusLog t tx s) ≠ logPre (messageLog keccak m)

/-- **(b) NO STATUS PREIMAGE IS THE PADDING PREIMAGE**, and the padding preimage `new bytes(88)` is
exactly the all-zero log's preimage. -/
def Properties.StatusPreimageNeDefault : Prop :=
  (∀ (t : ℕ) (tx : UInt256) (s : TxStatus), logPre (statusLog t tx s) ≠ logDefaultPre)
    ∧ logPre zeroLog = logDefaultPre

/-- **(b) A STATUS PREIMAGE IS NOT THE PREIMAGE OF ANY WELL-FORMED LOG WITH ANOTHER SENDER.** The
sender bytes separate the bootloader's logs from every other well-formed log. -/
def Properties.OtherSenderPreimageNeStatusPreimage : Prop :=
  ∀ (log : L2Log), LogWellFormed log → log.sender ≠ BOOTLOADER_ADDRESS →
    ∀ (t : ℕ) (tx : UInt256) (s : TxStatus), logPre log ≠ logPre (statusLog t tx s)

/-- **WITNESS FOR `OtherSenderPreimageNeStatusPreimage`.** Its premises hold on a message log of
a well-formed message, for every keccak. -/
@[witness] def Properties.OtherSenderPreimageWitness : Prop :=
  ∀ keccak : Keccak, ∃ m : L2Message, MessageWellFormed m ∧ m.txNumberInBatch ≠ 0 ∧ m.sender ≠ 0
    ∧ LogWellFormed (messageLog keccak m)
    ∧ (messageLog keccak m).sender ≠ BOOTLOADER_ADDRESS

/-! ## (c) Pinned forms -/

/-- **(c) EQUAL LEAF HASHES PIN THE LOG, OR KECCAK COLLIDES ON THE TWO NAMED PREIMAGES.**
Premises: both logs are well-formed (`LogWellFormed log` and `LogWellFormed log'`), and their leaf
hashes are equal.  Then the logs are equal, or keccak collides on their two preimages. -/
@[headline] def Properties.LeafHashPinsLogOrCollision : Prop :=
  ∀ (keccak : Keccak) (log log' : L2Log), LogWellFormed log → LogWellFormed log' →
    logLeaf keccak log = logLeaf keccak log' →
      log = log' ∨ HashCollision keccak (logPre log) (logPre log')

/-- **HEADLINE (c). A FAILURE LEAF IS MET BY ANOTHER LOG'S LEAF ONLY THROUGH A KECCAK COLLISION ON
THE TWO NAMED 88-BYTE PREIMAGES.** For a status log `statusLog t tx Failure` with `t` below `2^16`,
and any well-formed log different from it (the Success log of the same transaction, another
transaction's status log, a message log, any other log): if the two leaf hashes are equal, keccak
collides on the two preimages. -/
@[headline] def Properties.FailureLeafOfOtherLogIsCollision : Prop :=
  ∀ (keccak : Keccak) (t : ℕ) (tx : UInt256) (log : L2Log), t < 256 ^ 2 → LogWellFormed log →
    log ≠ statusLog t tx .failure →
    logLeaf keccak log = logLeaf keccak (statusLog t tx .failure) →
      HashCollision keccak (logPre log) (logPre (statusLog t tx .failure))

/-- **(c) A SUCCESS LEAF MEETS A FAILURE LEAF ONLY THROUGH A COLLISION**, for any transaction
numbers and hashes; no well-formedness premise. -/
@[headline] def Properties.FailureLeafOfSuccessLogIsCollision : Prop :=
  ∀ (keccak : Keccak) (t t' : ℕ) (tx tx' : UInt256),
    logLeaf keccak (statusLog t' tx' .success) = logLeaf keccak (statusLog t tx .failure) →
      HashCollision keccak (logPre (statusLog t' tx' .success)) (logPre (statusLog t tx .failure))

/-- **(c) A MESSAGE LEAF MEETS A STATUS LEAF ONLY THROUGH A COLLISION**, for any message and any
status log; no well-formedness premise. -/
@[headline] def Properties.StatusLeafOfMessageIsCollision : Prop :=
  ∀ (keccak : Keccak) (t : ℕ) (tx : UInt256) (s : TxStatus) (m : L2Message),
    messageLeaf keccak m = logLeaf keccak (statusLog t tx s) →
      HashCollision keccak (logPre (messageLog keccak m)) (logPre (statusLog t tx s))

/-- **(c) EQUAL MESSAGE LEAVES PIN THE MESSAGE, OR KECCAK COLLIDES ON NAMED INPUTS.** Two
well-formed messages with equal leaf hashes are equal, or keccak collides on their two 88-byte log
preimages, or on their two bodies (the logs' value words are `keccak(data)`). -/
@[headline] def Properties.MessageLeafPinsMessageOrCollision : Prop :=
  ∀ (keccak : Keccak) (m m' : L2Message), MessageWellFormed m → MessageWellFormed m' →
    messageLeaf keccak m = messageLeaf keccak m' →
      m = m' ∨ HashCollision keccak (logPre (messageLog keccak m)) (logPre (messageLog keccak m'))
        ∨ HashCollision keccak m.data m'.data

/-! ## Witnesses for (c) -/

/-- **WITNESS FOR THE STATUS-LEAF FORMS.** With the stand-in `lengthKeccak`, which maps every two
strings of one length to one word:

* every premise of `FailureLeafOfOtherLogIsCollision` holds, at transaction number 7 and hash 5,
  with `log` the Success log of the same transaction (so every premise of
  `FailureLeafOfSuccessLogIsCollision` holds too);
* every premise of `StatusLeafOfMessageIsCollision` holds, for a well-formed message with nonzero
  number and sender.

And the collision predicates are not forced: with `pointKeccak` of the Failure preimage, keccak
does not collide on the Failure and Success preimages, nor on the Failure and message preimages. -/
@[witness] def Properties.StatusLeafCollisionWitness : Prop :=
  let fail := statusLog 7 5 .failure
  let succ := statusLog 7 5 .success
  let m : L2Message := ⟨3, 0x1234, [1, 2, 3]⟩
  ((7 : ℕ) < 256 ^ 2 ∧ LogWellFormed succ ∧ succ ≠ fail
      ∧ logLeaf lengthKeccak succ = logLeaf lengthKeccak fail)
    ∧ (MessageWellFormed m ∧ messageLeaf lengthKeccak m = logLeaf lengthKeccak fail)
    ∧ ¬ HashCollision (pointKeccak (logPre fail)) (logPre succ) (logPre fail)
    ∧ ¬ HashCollision (pointKeccak (logPre fail))
        (logPre (messageLog (pointKeccak (logPre fail)) m)) (logPre fail)

/-- **WITNESS FOR `LeafHashPinsLogOrCollision` AND `MessageLeafPinsMessageOrCollision`, AND BOTH
COLLISION DISJUNCTS ARE NEEDED.** With `lengthKeccak`:

* two well-formed status logs of different transactions have equal leaf hashes, and the
  88-byte collision disjunct is the one that holds;
* two well-formed messages from different senders have equal leaf hashes; they differ, their
  bodies do not collide (equal bodies), and the 88-byte disjunct holds;
* two well-formed messages differing only in their (equal-length) bodies have equal leaf hashes;
  their 88-byte log preimages are EQUAL, so only the body disjunct holds. -/
@[witness] def Properties.LeafPinningWitness : Prop :=
  let a := statusLog 7 5 .success
  let b := statusLog 8 6 .success
  let m₁ : L2Message := ⟨3, 0x1234, [1, 2, 3]⟩
  let m₂ : L2Message := ⟨3, 0x5678, [1, 2, 3]⟩
  let m₃ : L2Message := ⟨3, 0x1234, [4, 5, 6]⟩
  (LogWellFormed a ∧ LogWellFormed b ∧ logLeaf lengthKeccak a = logLeaf lengthKeccak b
      ∧ a ≠ b ∧ HashCollision lengthKeccak (logPre a) (logPre b))
    ∧ (MessageWellFormed m₁ ∧ MessageWellFormed m₂
      ∧ messageLeaf lengthKeccak m₁ = messageLeaf lengthKeccak m₂ ∧ m₁ ≠ m₂
      ∧ HashCollision lengthKeccak (logPre (messageLog lengthKeccak m₁))
          (logPre (messageLog lengthKeccak m₂))
      ∧ ¬ HashCollision lengthKeccak m₁.data m₂.data)
    ∧ (MessageWellFormed m₃ ∧ messageLeaf lengthKeccak m₁ = messageLeaf lengthKeccak m₃
      ∧ m₁ ≠ m₃
      ∧ ¬ HashCollision lengthKeccak (logPre (messageLog lengthKeccak m₁))
          (logPre (messageLog lengthKeccak m₃))
      ∧ HashCollision lengthKeccak m₁.data m₃.data)

end Contracts.MessageHashing
