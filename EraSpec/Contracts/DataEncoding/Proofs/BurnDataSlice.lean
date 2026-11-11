import EraSpec.Contracts.DataEncoding.Properties.BurnDataSlice
import EraSpec.Contracts.DataEncoding.Proofs.TxDataHash
import EraSpec.Codegen.VaultPreparationSlice.Proofs.Denotation

/-!
# Proofs: the burn data here and in the vault's codegen slice

Both directions go through the slice's own closed forms (`encodeBurnData_eq`, `decode_three`,
`bAmount_encodeBurnData` and its siblings, `Codegen/VaultPreparationSlice/Proofs/Denotation.lean`)
and this folder's `encAddr_eq_encWord`, `decodeBridgeBurnData_ne_none_iff` and
`encode_of_decodeBridgeBurnData`.
-/

namespace Contracts.DataEncoding

open Codegen.VaultPreparationSlice (encodeBurnData encodeBurnData_eq decode_three
  bAmount_encodeBurnData bReceiver_encodeBurnData bHint_encodeBurnData natCast_addr)

theorem EncodeBurnDataAgreesWithSlice : Properties.EncodeBurnDataAgreesWithSlice := by
  intro b
  rw [encodeBurnData_eq, encodeBridgeBurnData, encAddr_eq_encWord b.receiver,
    encAddr_eq_encWord b.tokenHint]
  rfl

theorem DecodeBurnDataAgreesWithSlice : Properties.DecodeBurnDataAgreesWithSlice := by
  intro data env hl
  constructor
  · have hlib : decodeBridgeBurnData data = none ↔
        ¬ (AttackVectors.BundleHashEncoding.fromBytesBE ((data.drop 32).take 32) < 2 ^ 160
          ∧ AttackVectors.BundleHashEncoding.fromBytesBE ((data.drop 64).take 32) < 2 ^ 160) := by
      have := decodeBridgeBurnData_ne_none_iff data
      constructor
      · intro hn hc
        exact (this.mpr ⟨hl, hc.1, hc.2⟩) hn
      · intro hc
        by_contra hne
        exact hc ⟨(this.mp hne).2.1, (this.mp hne).2.2⟩
    rw [decode_three data env hl, hlib]
    split_ifs with hc
    · exact ⟨fun h => by simp at h, fun h => absurd hc h⟩
    · exact ⟨fun _ => hc, fun _ => rfl⟩
  · intro b hb
    -- `subst` would unfold the encoder; rewrite instead
    have hd : data = encodeBurnData b := by
      have h2 := encode_of_decodeBridgeBurnData hb
      rw [EncodeBurnDataAgreesWithSlice b]
      exact h2
    rw [hd] at hl ⊢
    rw [decode_three _ env hl]
    rw [ite_eq_left ⟨by rw [bReceiver_encodeBurnData]; exact b.receiver.isLt,
      by rw [bHint_encodeBurnData]; exact b.tokenHint.isLt⟩, bAmount_encodeBurnData,
      bReceiver_encodeBurnData, bHint_encodeBurnData, natCast_addr, natCast_addr]

end Contracts.DataEncoding
