import EraSpec.Contracts.L1InteropHandler.Specs.WithdrawalGate
import EraSpec.Contracts.MessageHashing.Specs.LogLeafSeparation

/-!
# Spec: the gate's message log is MessageHashing's message log

`WithdrawalGate` writes its own `L2Log`, `L2Message` and `msgToLog` for the log whose leaf hash
`proveL2MessageInclusionShared` proves: `_l2MessageToLog` (`common/libraries/MessageHashing.sol:27-37`
at era-contracts `b17415d20`). `MessageHashing` `LogLeafSeparation` models the same function
(`messageLog`) together with the 88-byte leaf preimage. The two models differ only in their types:
the gate's addresses are `Fin (256 ^ 20)` and its shard id a natural number; MessageHashing's are
natural numbers with a well-formedness bound and a `UInt8`.

This file defines the translation of the gate's types into MessageHashing's. The refinement lemma
(`Properties.MsgToLogIsMessageLog`) says that `msgToLog` is `messageLog` under it, so the gate and
MessageHashing describe one `_l2MessageToLog`, and MessageHashing's leaf-separation results apply to
the gate's verification query.

**Definitions only.** Statements in `EraSpec.Contracts.L1InteropHandler.Properties.MessageLog`,
proofs in `EraSpec.Contracts.L1InteropHandler.Proofs.MessageLog`.
-/

namespace Contracts.L1WithdrawalGate

/-- A gate message as a MessageHashing message: the sender as its natural number. -/
def toHashingMsg (m : L2Message) : MessageHashing.L2Message :=
  ⟨m.txNumberInBatch, m.sender.val, m.data⟩

/-- A gate log as a MessageHashing log: the shard id as a byte, the sender as its natural number. -/
def toHashingLog (l : L2Log) : MessageHashing.L2Log :=
  ⟨UInt8.ofNat l.l2ShardId, l.isService, l.txNumberInBatch, l.sender.val, l.key, l.value⟩

end Contracts.L1WithdrawalGate
