import EraSpec.Contracts.L1InteropHandler.Specs.MessageLog

/-!
# Properties: the gate's message log is MessageHashing's message log

Statements about `Specs/MessageLog.lean`; proofs in `Proofs/MessageLog.lean`. None takes a premise
on keccak: `C.keccak` is the gate codec's arbitrary hash.
-/

namespace Contracts.L1WithdrawalGate

open AttackVectors.BundleHashEncoding (HashCollision)

/-- **REFINEMENT: ONE MODEL OF `_l2MessageToLog`.** For every codec and every message, the gate's
`msgToLog` (the log its verification query proves) is MessageHashing's `messageLog` of the same
message, with the codec's keccak: shard `0`, `isService = true`, the message's transaction number,
sender the messenger `0x8008`, key the message sender as a word, value `keccak(data)`
(`MessageHashing.sol:27-37` at `b17415d20`). -/
def Properties.MsgToLogIsMessageLog : Prop :=
  ∀ (C : Codec) (m : L2Message),
    toHashingLog (msgToLog C m) = MessageHashing.messageLog C.keccak (toHashingMsg m)

/-- **THE TRANSLATED MESSAGE IS WELL-FORMED EXACTLY WHEN ITS TRANSACTION NUMBER FITS A `uint16`.**
The gate's sender is a 20-byte address by its type, so MessageHashing's `MessageWellFormed` adds only
the `uint16` bound on `txNumberInBatch`. -/
def Properties.HashingMsgWellFormedIff : Prop :=
  ∀ m : L2Message,
    MessageHashing.MessageWellFormed (toHashingMsg m) ↔ m.txNumberInBatch < 256 ^ 2

/-- **THE GATE'S QUERY LEAF IS NOT A STATUS LEAF, UP TO A NAMED COLLISION.** For every codec, every
message the gate checks, and every L1 → L2 transaction status log (`getL2LogFromL1ToL2Transaction`,
`MessageHashing.sol:39-62`): if the leaf of the gate's query log equals the status log's leaf, then
keccak collides on the two named 88-byte leaf preimages. So a withdrawal message proof cannot be
answered by a deposit-status leaf, or the reverse, without a keccak collision on those two inputs.
No premise. -/
def Properties.GateQueryLeafIsStatusLeafOnlyByCollision : Prop :=
  ∀ (C : Codec) (m : L2Message) (t : ℕ) (tx : UInt256) (s : MessageHashing.TxStatus),
    MessageHashing.logLeaf C.keccak (toHashingLog (msgToLog C m))
        = MessageHashing.logLeaf C.keccak (MessageHashing.statusLog t tx s) →
      HashCollision C.keccak (MessageHashing.logPre (toHashingLog (msgToLog C m)))
        (MessageHashing.logPre (MessageHashing.statusLog t tx s))

end Contracts.L1WithdrawalGate
