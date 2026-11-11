import EraSpec.Codegen.VaultPreparationSlice.Properties.MintDataBytes
import EraSpec.Codegen.VaultPreparationSlice.Proofs.Denotation

/-! # Proofs: the bytes `bridgeBurn` takes and returns -/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Contracts.BridgedStandardERC20 (Address)
open Contracts.NativeTokenVaultBase (BurnData MintData)

theorem EncodeMintDataLayout : Properties.EncodeMintDataLayout := encodeMintData_eq

theorem EncodeBurnDataLayout : Properties.EncodeBurnDataLayout := encodeBurnData_eq

/-- Peel one 32-byte word off two equal byte strings. -/
theorem word32_append_inj {x x' : ℕ} {l l' : Bytes} (hx : x < 2 ^ 256) (hx' : x' < 2 ^ 256)
    (h : word32 x ++ l = word32 x' ++ l') : x = x' ∧ l = l' := by
  obtain ⟨hw, hl⟩ := List.append_inj h (by rw [length_word32, length_word32])
  exact ⟨by rw [← fromBytes_word32 hx, ← fromBytes_word32 hx', hw], hl⟩

theorem addr_lt (a : Address) : a.val < 2 ^ 256 := lt_trans a.isLt (by decide)

theorem word_lt (w : Word) : w.val < 2 ^ 256 := by simpa [UInt256.size] using w.isLt

theorem EncodeMintDataInjective : Properties.EncodeMintDataInjective := by
  intro m m' hm hm' h
  rw [encodeMintData_eq, encodeMintData_eq] at h
  simp only [List.append_assoc] at h
  obtain ⟨h1, h⟩ := word32_append_inj (addr_lt _) (addr_lt _) h
  obtain ⟨h2, h⟩ := word32_append_inj (addr_lt _) (addr_lt _) h
  obtain ⟨h3, h⟩ := word32_append_inj (addr_lt _) (addr_lt _) h
  obtain ⟨h4, h⟩ := word32_append_inj (word_lt _) (word_lt _) h
  obtain ⟨-, h⟩ := word32_append_inj (by decide) (by decide) h
  obtain ⟨h6, h⟩ := word32_append_inj hm hm' h
  have hmd : m.metadata = m'.metadata := by
    have := congrArg (List.take m.metadata.length) h
    rwa [pad32, pad32, AttackVectors.BundleHashEncoding.pad32,
      AttackVectors.BundleHashEncoding.pad32, List.take_left' rfl, h6,
      List.take_left' rfl] at this
  obtain ⟨oc, rr, ot, amt, md⟩ := m
  obtain ⟨oc', rr', ot', amt', md'⟩ := m'
  simp only [MintData.mk.injEq]
  exact ⟨Fin.ext h1, Fin.ext h2, Fin.ext h3, Fin.ext h4, hmd⟩

end Codegen.VaultPreparationSlice
