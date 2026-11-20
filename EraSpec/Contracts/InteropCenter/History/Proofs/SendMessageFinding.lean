import EraSpec.Contracts.InteropCenter.History.Properties.SendMessageFinding
import EraSpec.Contracts.InteropCenter.Proofs.Send

/-!
# History proofs: the `c67894b9` `sendMessage` finding

**History is the record of an older commit, not a claim about `b17415d20`.** The two parsers agree
because their restriction tables agree on the seven indices (`MaskTableIsPinTable`, then
`pinParseFrom_eq_parseFrom`).
-/

namespace Contracts.InteropCenter.Send.History

open Contracts.AtomicFlowManager (LegState)

theorem MaskTableIsPinTable : Properties.MaskTableIsPinTable := by
  intro i hi r
  interval_cases i <;> cases r <;> rfl

/-- The two loops agree from any state: they differ only in the restriction table, and the tables
agree on the seven indices (`MaskTableIsPinTable`). -/
theorem pinParseFrom_eq_parseFrom (r : Restriction) :
    ∀ (attrs : List Attribute) (used : List ℕ) (x : CallAttributes × BundleAttributes),
      pinParseFrom r used x attrs = parseFrom r used x attrs
  | [], _, _ => rfl
  | a :: rest, used, x => by
    have ih := pinParseFrom_eq_parseFrom r rest
    rw [pinParseFrom, parseFrom]
    cases hi : a.index with
    | none => rfl
    | some i =>
      simp only
      rw [MaskTableIsPinTable i (Attribute.index_lt_seven hi) r, ih]

theorem PinParserIsHeadParser : Properties.PinParserIsHeadParser := fun attrs r =>
  pinParseFrom_eq_parseFrom r attrs [] _

theorem PinSendMessageDroppedAtomicBundle : Properties.PinSendMessageDroppedAtomicBundle := by
  refine ⟨⟨headMsgAttrs, ⟨_, _, List.mem_cons_self⟩, ?_⟩, ?_⟩
  · rw [show pinParseAttributes headMsgAttrs .callAndBundleAttributes
      = some (noCallAttributes, ⟨[], [], false, 1⟩) by rfl]
    exact Option.some_ne_none _
  · intro attrs _ _
    refine ⟨rfl, fun P S d hd => ?_⟩
    simp [Contracts.InteropCenter.History.State.afterSend, Contracts.InteropCenter.History.Dispatch.isAtomic, hd,
      pinSendMessageAtomicSend]

theorem PinFindingRejectedAtHead : Properties.PinFindingRejectedAtHead := by
  intro attrs hhas _
  refine ⟨(parseAtomicSend_isAtomic_iff attrs).mpr hhas, fun P S S' d hs hlog he hattrs => ?_⟩
  obtain ⟨-, h2, -, -, -, h6, h7⟩ := SendMessageAlwaysAtomic P S S' d hs hlog he
  exact ⟨hattrs ▸ h2, h6, h7⟩

theorem SendAtHeadStepWitness : Properties.SendAtHeadStepWitness := by
  refine ⟨headStep1, rfl, rfl, ⟨_, _, List.mem_cons_self⟩, ?_, rfl, ?_, by rfl, headStep2,
    headStep3 _ (fun _ => by rfl), rfl, rfl, not_has_salt_only 3, rfl,
    headStep3 _ (fun _ => by rfl), ⟨{ headMsg with attrs := [] }, rfl, ?_⟩, rfl⟩
  · show pinParseAttributes headMsgAttrs .callAndBundleAttributes ≠ none
    rw [show pinParseAttributes headMsgAttrs .callAndBundleAttributes
      = some (noCallAttributes, ⟨[], [], false, 1⟩) by rfl]
    exact Option.some_ne_none _
  · rw [headS1_legState]
    exact LegState.noConfusion
  · rintro ⟨_, _, h⟩
    simp at h

end Contracts.InteropCenter.Send.History
