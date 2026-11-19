import EraSpec.Contracts.SecondProofSystem.Properties.DiamondRefinement
import EraSpec.Contracts.SecondProofSystem.Proofs.FlagAuthorityV35
import EraSpec.Contracts.SecondProofSystem.Proofs.MigrationV35

/-!
# Proofs: MigrationV35's diamond calls refine FlagAuthorityV35's

`DiamondStepRefines` is a case split on the diamond call: each branch of `dstep` makes the same
checks, in the same order, as the FlagAuthorityV35 branch it maps to. The three derived facts
apply the FlagAuthorityV35 theorem to the image of the call.
-/

namespace Contracts.SecondProofSystem.DiamondRefinement

open Clear

private lemma projPS_bit (p : MigrationV35.ProofSystem) :
    (projPS p).bit = p.bit := by
  cases p <;> rfl

private lemma projPS_eq_zisk {p : MigrationV35.ProofSystem} :
    projPS p = .zisk ↔ p = .zisk := by
  cases p <;> simp [projPS]

private lemma ziskBit_eq : FlagAuthorityV35.ziskBit = MigrationV35.ziskBit := rfl

private lemma mp_eq : FlagAuthorityV35.MULTI_PROOF_TYPE = MigrationV35.MULTI_PROOF_TYPE := rfl

private lemma newMask_eq (m : UInt8) (p : MigrationV35.ProofSystem) (en : Bool) :
    FlagAuthorityV35.newMask m (projPS p) en = MigrationV35.newMask m p en := by
  simp [FlagAuthorityV35.newMask, MigrationV35.newMask, projPS_bit]

theorem DiamondStepRefines : Properties.DiamondStepRefines := by
  intro E owner ctm c dc d d' h
  cases dc with
  | setPendingAdmin a =>
    simp only [MigrationV35.dstep] at h
    split_ifs at h with h1
    cases h
    refine ⟨?_, rfl⟩
    simp [FlagAuthorityV35.step, FlagAuthorityV35.stepWith, projCall, proj, h1]
  | acceptAdmin =>
    simp only [MigrationV35.dstep] at h
    split_ifs at h with h1
    cases h
    refine ⟨?_, rfl⟩
    simp [FlagAuthorityV35.step, FlagAuthorityV35.stepWith, projCall, proj, h1]
  | setProofSystemStatus p en =>
    simp only [MigrationV35.dstep] at h
    split_ifs at h with h1 h2
    cases h
    have hp : p = .zisk := by simpa using h2
    subst hp
    refine ⟨?_, rfl⟩
    have h1' : c = FlagAuthorityV35.callerRule (proj ctm owner d) en := by
      simp only [not_not] at h1
      simp [h1, MigrationV35.authorized, FlagAuthorityV35.callerRule, proj]
    simp only [FlagAuthorityV35.step, FlagAuthorityV35.stepWith,
      FlagAuthorityV35.setProofSystemStatusWith, projCall, projPS]
    rw [ite_eq_right (not_not.2 h1'), ite_eq_right (by simp)]
    have hm := newMask_eq d.disabledProofSystems .zisk en
    simp only [projPS] at hm
    simp [proj, hm]
  | permanentlyRequireSecondProofSystem =>
    simp only [MigrationV35.dstep] at h
    split_ifs at h with h1 h2 h3 h4
    cases h
    refine ⟨?_, rfl⟩
    simp only [not_not] at h1
    simp [FlagAuthorityV35.step, FlagAuthorityV35.stepWith, FlagAuthorityV35.permanentlyRequire,
      projCall, proj, projEnv, h1, h2, h3, mp_eq] at h4 ⊢
    simp_all
  | makePermanentRollup =>
    simp only [MigrationV35.dstep] at h
    split_ifs at h
    cases h
    exact ⟨rfl, rfl⟩
  | upgrade nv =>
    refine ⟨?_, rfl⟩
    cases nv with
    | none =>
      simp only [MigrationV35.dstep, MigrationV35.postCutCheck] at h
      split_ifs at h with h1
      cases h
      simp [FlagAuthorityV35.step, FlagAuthorityV35.stepWith, FlagAuthorityV35.executeDiamondCut,
        FlagAuthorityV35.runInit, FlagAuthorityV35.genuineInit, projCall, proj, projEnv, mp_eq] at h1 ⊢
      have hc : ¬(d.secondProofSystemRequired = true ∧
          ¬E.proofMode d.verifier 0 = some MigrationV35.MULTI_PROOF_TYPE) := fun hc => hc.2 (h1 hc.1)
      simp [hc]
    | some v =>
      simp only [MigrationV35.dstep, MigrationV35.postCutCheck] at h
      split_ifs at h with h1 h2
      cases h
      simp only [FlagAuthorityV35.step, FlagAuthorityV35.stepWith,
        FlagAuthorityV35.executeDiamondCut, FlagAuthorityV35.runInit, FlagAuthorityV35.genuineInit,
        projCall, proj, projEnv, mp_eq]
      have hc : ¬(d.secondProofSystemRequired = true ∧
          ¬E.proofMode v 0 = some MigrationV35.MULTI_PROOF_TYPE) := by simpa using h2
      simp [h1, hc]
  | breakGlassCut f =>
    refine ⟨?_, rfl⟩
    simp only [MigrationV35.dstep] at h
    rcases hf : f d with _ | d₁
    · simp [hf] at h
    · simp only [hf, MigrationV35.postCutCheck] at h
      split_ifs at h with h1
      cases h
      simp [FlagAuthorityV35.step, FlagAuthorityV35.stepWith, FlagAuthorityV35.executeDiamondCut,
        FlagAuthorityV35.runInit, projCall, proj, projEnv, hf, mp_eq] at h1 ⊢
      have hc : ¬(d'.secondProofSystemRequired = true ∧
          ¬E.proofMode d'.verifier 0 = some MigrationV35.MULTI_PROOF_TYPE) := fun hc => hc.2 (h1 hc.1)
      simp [hc]

private lemma image_not_breakGlass {ctm owner : MigrationV35.Address} {d : MigrationV35.Diamond}
    {dc : MigrationV35.DCall} (h : isBreakGlassD dc = false) :
    (projCall ctm owner d dc).isBreakGlass = false := by
  cases dc <;> simp_all [projCall, isBreakGlassD, FlagAuthorityV35.Call.isBreakGlass,
    FlagAuthorityV35.Init.isArbitrary]

theorem DiamondFlagMonotoneStep : Properties.DiamondFlagMonotoneStep := by
  intro E owner c dc d d' hbg h hf
  have hs := (DiamondStepRefines E owner 0 c dc d d' h).1
  exact FlagAuthorityV35.FlagMonotoneStep (projEnv E) c _ _ _ (image_not_breakGlass hbg) hs hf

theorem DiamondMaskWrittenOnlyBySetStatus : Properties.DiamondMaskWrittenOnlyBySetStatus := by
  intro E owner c dc d d' hbg h hne
  have hs := (DiamondStepRefines E owner 0 c dc d d' h).1
  obtain ⟨en, hen⟩ := FlagAuthorityV35.MaskWrittenOnlyBySetStatus (projEnv E) c _ _ _
    (image_not_breakGlass hbg) hs hne
  refine ⟨en, ?_⟩
  cases dc with
  | setProofSystemStatus p en' =>
    simp only [projCall, FlagAuthorityV35.Call.setProofSystemStatus.injEq] at hen
    obtain ⟨hp, rfl⟩ := hen
    rw [projPS_eq_zisk.1 hp]
  | _ => simp [projCall] at hen

theorem DiamondZiskOffOnFlaggedIsOwners : Properties.DiamondZiskOffOnFlaggedIsOwners := by
  intro E owner c dc d d' hbg h hf hon hoff
  have hs := (DiamondStepRefines E owner 0 c dc d d' h).1
  obtain ⟨hcall, hc⟩ := FlagAuthorityV35.ZiskOffOnFlaggedIsOwners (projEnv E) c _ _ _
    (image_not_breakGlass hbg) hs hf hon hoff
  refine ⟨?_, hc⟩
  cases dc with
  | setProofSystemStatus p en' =>
    simp only [projCall, FlagAuthorityV35.Call.setProofSystemStatus.injEq] at hcall
    obtain ⟨hp, rfl⟩ := hcall
    rw [projPS_eq_zisk.1 hp]
  | _ => simp [projCall] at hcall

end Contracts.SecondProofSystem.DiamondRefinement
