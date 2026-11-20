import EraSpec.Contracts.L1InteropHandler.Properties.MessageLog
import EraSpec.Contracts.MessageHashing.Proofs.LogLeafSeparation

/-! Proofs for `Properties/MessageLog.lean`. -/

namespace Contracts.L1WithdrawalGate

theorem MsgToLogIsMessageLog : Properties.MsgToLogIsMessageLog := by
  intro C m
  have hs : padAddr m.sender = Nat.toUInt256 m.sender.val := by
    apply Fin.ext
    simp only [padAddr, Nat.toUInt256, Fin.val_ofNat]
    exact (Nat.mod_eq_of_lt (lt_trans m.sender.isLt (by norm_num [UInt256.size]))).symm
  simp only [toHashingLog, msgToLog, MessageHashing.messageLog, toHashingMsg, hs]
  rfl

theorem HashingMsgWellFormedIff : Properties.HashingMsgWellFormedIff := by
  intro m
  simp only [MessageHashing.MessageWellFormed, toHashingMsg]
  exact ⟨fun h => h.1, fun h => ⟨h, m.sender.isLt⟩⟩

theorem GateQueryLeafIsStatusLeafOnlyByCollision :
    Properties.GateQueryLeafIsStatusLeafOnlyByCollision := by
  intro C m t tx s h
  rw [MsgToLogIsMessageLog C m] at h ⊢
  exact MessageHashing.StatusLeafOfMessageIsCollision C.keccak t tx s (toHashingMsg m) h

end Contracts.L1WithdrawalGate
