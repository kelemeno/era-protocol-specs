import EraSpec.Codegen.VaultPreparationSlice.Properties.RevertOrder
import EraSpec.Codegen.VaultPreparationSlice.Proofs.Denotation

/-! # Proofs: which check fails first, and with what revert data -/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls
open Codegen.BridgedTokenSlice (addrWord addrWord_zero addrWord_eq_zero)
open Contracts.NativeTokenVaultBase (BurnData)

theorem L2ValueCheckedFirst : Properties.L2ValueCheckedFirst := by
  intro W M e c l2v a oc data st w h
  rw [xcall_bridgeBurn]
  simp [burnDenote, h]

theorem RouterCheckedSecond : Properties.RouterCheckedSecond := by
  intro W M e c a oc data st w h
  rw [xcall_bridgeBurn]
  simp [burnDenote, h]

theorem PauseCheckedThird : Properties.PauseCheckedThird := by
  intro W M e c a oc data st w h1 h2
  rw [xcall_bridgeBurn]
  simp [burnDenote, h1, h2]

theorem BurnDataLengthCheckedFourth : Properties.BurnDataLengthCheckedFourth := by
  intro W M e c a oc data st w h1 h2 h3
  rw [xcall_bridgeBurn]
  simp [burnDenote, h1, h2, h3]

theorem resolve_hint (st : Storage) (a : Word) (b : BurnData) :
    resolve st a (addrWord b.tokenHint) = hintedToken st a b := by
  unfold resolve hintedToken
  by_cases h : b.tokenHint = 0 <;> simp [h, addrWord_zero, addrWord_eq_zero]

/-- `bridgeBurn` with well-formed burn data, past the modifiers: its tail. -/
theorem xcall_bridgeBurn_decoded {W : Type} (M : Machine W) (e : Env) (c a oc : Word)
    (b : BurnData) (st : Storage) (w : W) (h1 : e.sender = st.scalars "_assetRouter")
    (h2 : st.scalars "_paused" = 0) :
    xcall M vaultProgram "bridgeBurn" e
      [.word c, .word 0, .word a, .word oc, .bytes (encodeBurnData b)] st w =
      some (burnTail M e c a oc b.amount (addrWord b.receiver) (hintedToken st a b) st w) := by
  rw [xcall_bridgeBurn]
  unfold burnDenote
  rw [length_encodeBurnData, bAmount_encodeBurnData, bReceiver_encodeBurnData,
    bHint_encodeBurnData, natCast_addr, natCast_addr, resolve_hint]
  simp only [ne_eq, not_true_eq_false, ite_false, h1, h2, b.receiver.isLt, b.tokenHint.isLt,
    and_self]

theorem NativeAssetLeavesTheSlice : Properties.NativeAssetLeavesTheSlice := by
  intro W M e c a oc b st w h1 h2 h3 h4 h5 h6
  rw [xcall_bridgeBurn_decoded M e c a oc b st w h1 h2]
  unfold burnTail
  simp [h3, h4, h5, h6]

theorem BaseAssetLeavesTheSlice : Properties.BaseAssetLeavesTheSlice := by
  intro W M e c a oc b st w h1 h2 h3 h4 h5 h6 h7
  rw [xcall_bridgeBurn_decoded M e c a oc b st w h1 h2]
  unfold burnTail
  simp [h3, h4, h5, h6, h7]

/-- A vault storage with router `2`, the token `3` registered for asset `7` whose origin
chain is `origin`, and base asset `base`. -/
def edgeStorage (origin base : Word) : Storage :=
  ⟨fun k => if k = "_assetRouter" then 2 else if k = "_baseTokenAssetId" then base else 0,
    fun m _key => if m = "_tokenAddress" then 3 else if m = "_assetIdOf" then 7
      else if m = "_originChainId" then origin else 0⟩

theorem RevertOrderPremisesSatisfiable : Properties.RevertOrderPremisesSatisfiable := by
  refine ⟨⟨1, by decide⟩, ⟨⟨0, 1, 0, 0⟩, Storage.zero, by simp [Storage.zero]⟩,
    ⟨⟨0, 0, 0, 0⟩, ⟨fun k => if k = "_paused" then 1 else 0, fun _ _ => 0⟩, by simp⟩,
    ⟨⟨0, 0, 0, 0⟩, Storage.zero, [], by simp [Storage.zero]⟩, ?_, ?_⟩
  · refine ⟨⟨0, 2, 0, 10⟩, edgeStorage 10 0, 7, ⟨10, 6, 0⟩, ?_⟩
    simp [edgeStorage, hintedToken]
  · refine ⟨⟨0, 2, 0, 10⟩, edgeStorage 1 7, 7, ⟨10, 6, 0⟩, ?_⟩
    simp [edgeStorage, hintedToken]

end Codegen.VaultPreparationSlice
