import EraSpec.Protocol.InteropAtomicity.Properties.FinalityFaithful
import EraSpec.Protocol.InteropAtomicity.Proofs.Timeout

/-!
# Proofs: finalizability at a destination that has to authenticate the roots

Certificates for `EraSpec.Protocol.InteropAtomicity.Properties.FinalityFaithful`.  Each
replacement is the matching `…OrBreak` proof of `Proofs/Atomicity.lean` with one extra step:
the batch the honest proof is against settled by the deadline, the destination's root was
created at or after it and aggregates honestly, so that root aggregates the batch
(`canAuthenticate_of_postDeadlineRoot`).
-/

namespace Contracts.FinalityFaithful

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree
open Contracts.Atomicity Contracts.Timeout

/-- An honest root created at or after the deadline aggregates every on-time batch, so the
destination holding it can authenticate any of them. -/
lemma canAuthenticate_of_postDeadlineRoot {S : System} {I : Imports} {d : Chain} {D : ℕ}
    (hroot : PostDeadlineRootAt S I d D) {c : Chain} {n : ℕ} (hon : S.time c n ≤ D) :
    CanAuthenticate I d c n := by
  obtain ⟨R, hI, hD, hagg⟩ := hroot
  exact ⟨R, hI, hagg c n (le_trans hon hD)⟩

/-! ## The replacements -/

theorem executed_implies_finalizable_at_importing_destination_or_break {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {I : Imports} {d : Chain} {F : Flow} {ev : GateEvidence}
    {leg : FlowLeg} (hex : ExecutedViaBy h z0 hl cv fh S F ev leg)
    (hroot : PostDeadlineRootAt S I d F.deadline) (other : FlowLeg) (hother : other ∈ F.legs) :
    LegFinalizableAt h z0 hl cv S A I d F other
      ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2 := by
  obtain ⟨hon, hacc⟩ := hex.2.2 other hother
  rcases finality_means_membership_or_break hacc with hmem | hb
  · obtain ⟨i, hi, hacc'⟩ := honest_accepts (h := h) (z0 := z0) (hl := hl) hS hmem
    exact Or.inl ⟨(ev other).1, honestProof h z0 hl S other.chain (ev other).1 i, hon,
      hDA _ _ _ hi, canAuthenticate_of_postDeadlineRoot hroot hon, hacc'⟩
  · exact Or.inr hb

theorem none_or_all_at_importing_destination_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {I : Imports} {d : Chain} (F : Flow) (ev : GateEvidence)
    (hroot : PostDeadlineRootAt S I d F.deadline) :
    FlowFinalizableAt h z0 hl cv S A I d F
      ∨ (∀ leg, ¬ ExecutedViaBy h z0 hl cv fh S F ev leg)
      ∨ GateBreak h z0 hl S F ev := by
  by_cases hex : ∃ leg, ExecutedViaBy h z0 hl cv fh S F ev leg
  · obtain ⟨leg, hleg⟩ := hex
    by_cases hb : GateBreak h z0 hl S F ev
    · exact Or.inr (Or.inr hb)
    · refine Or.inl fun other hother => ?_
      rcases executed_implies_finalizable_at_importing_destination_or_break hS hDA hleg hroot
          other hother with hf | hbo
      · exact hf
      · exact absurd ⟨other, hother, hbo⟩ hb
  · exact Or.inr (Or.inl fun leg hleg => hex ⟨leg, hleg⟩)

theorem executed_finality_persists_at_authenticating_destination_or_break {h : Hash}
    {z0 : UInt256} {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S)
    {A : Access} (hDA : DataAvailable h z0 hl S A) {I : Imports} {F : Flow} {ev : GateEvidence}
    {leg : FlowLeg} (hex : ExecutedViaBy h z0 hl cv fh S F ev leg) (other : FlowLeg)
    (hother : other ∈ F.legs) :
    (∀ (d : Chain) (m : ℕ), (ev other).1 ≤ m → S.time other.chain m ≤ F.deadline →
        CanAuthenticate I d other.chain m → LegFinalizableAt h z0 hl cv S A I d F other)
      ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2 := by
  obtain ⟨_, hacc⟩ := hex.2.2 other hother
  rcases finality_means_membership_or_break hacc with hmem | hb
  · refine Or.inl fun d m hnm hon' hauth => ?_
    obtain ⟨i, hi, hacc'⟩ := honest_accepts (h := h) (z0 := z0) (hl := hl) hS
      (keys_mono_batch hS other.chain hnm hmem)
    exact ⟨m, honestProof h z0 hl S other.chain m i, hon', hDA _ _ _ hi, hauth, hacc'⟩
  · exact Or.inr hb

/-! ## The concrete configuration -/

lemma everyChainSystem_wf {a b : UInt256} (ha : 0 < a) (hab : a < b) :
    Wf (everyChainSystem a b) := by
  obtain ⟨hg1, hg2⟩ := threeLeafTree_guards ha hab
  refine ⟨fun _ => Reaches.tail (Reaches.tail Reaches.refl hg1) hg2, fun _ _ => Reaches.refl,
    fun _ _ _ hij => hij, fun _ _ => ?_⟩
  show (3 : ℕ) ≤ 2 ^ 2
  norm_num

lemma threeLeafTree_leaf_two_value (a b : UInt256) : ((threeLeafTree a b).leaf 2).value = b := by
  simp [threeLeafTree, Contracts.InteropCommitmentTree.insert, setup]

/-- The honest gate evidence for `twoChainFlow`: batch 0, and the `merklePath` proof of the
leaf whose index is the leg's commit value (`1` at index 1, `2` at index 2). -/
def twoChainEvidence (h : Hash) (z0 : UInt256) (hl : LeafHash) : GateEvidence :=
  fun l => (0, honestProof h z0 hl (everyChainSystem 1 2) l.chain 0 l.bundleHash.val)

lemma twoChainFlow_legs (l : FlowLeg) (hl' : l ∈ twoChainFlow.legs) :
    l = ⟨0, 1⟩ ∨ l = ⟨1, 2⟩ := by
  simpa [twoChainFlow] using hl'

lemma twoChain_index_lt (l : FlowLeg) (hl' : l ∈ twoChainFlow.legs) :
    l.bundleHash.val < ((everyChainSystem 1 2).tree l.chain 0).leafCount := by
  rcases twoChainFlow_legs l hl' with rfl | rfl
  · show (1 : ℕ) < 3; norm_num
  · show (2 : ℕ) < 3; norm_num

lemma twoChain_accepts (h : Hash) (z0 : UInt256) (hl : LeafHash) (l : FlowLeg)
    (hl' : l ∈ twoChainFlow.legs) :
    Accepts h z0 hl (everyChainSystem 1 2) l.chain 0 (legValue (fun _ bh => bh) twoChainFlow l)
      (twoChainEvidence h z0 hl l).2 := by
  have hcap : (threeLeafTree 1 2).leafCount ≤ 2 ^ 2 := by
    show (3 : ℕ) ≤ 2 ^ 2; norm_num
  rcases twoChainFlow_legs l hl' with rfl | rfl
  · have := inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := threeLeafTree 1 2)
      (height := 2) hcap (i := 1) (by show (1 : ℕ) < 3; norm_num)
    rw [threeLeafTree_leaf_one_value] at this
    exact this
  · have := inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := threeLeafTree 1 2)
      (height := 2) hcap (i := 2) (by show (2 : ℕ) < 3; norm_num)
    rw [threeLeafTree_leaf_two_value] at this
    exact this

lemma twoChain_executes (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ExecutedViaBy h z0 hl (fun _ bh => bh) (honestFlowHash twoChainFlow) (everyChainSystem 1 2)
      twoChainFlow (twoChainEvidence h z0 hl) ⟨0, 1⟩ :=
  ⟨by simp [twoChainFlow], (honest_flowHash_no_clash twoChainFlow).1,
    fun l hl' => ⟨le_refl 0, twoChain_accepts h z0 hl l hl'⟩⟩

lemma twoChain_no_gate_break (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ¬ GateBreak h z0 hl (everyChainSystem 1 2) twoChainFlow (twoChainEvidence h z0 hl) := by
  rintro ⟨l, hl', hb⟩
  exact honestProof_no_break h z0 hl (everyChainSystem 1 2) l.chain 0 l.bundleHash.val
    (twoChain_index_lt l hl') hb

lemma twoChain_finalizableAt (h : Hash) (z0 : UInt256) (hl : LeafHash) {I : Imports} {d : Chain}
    (hauth : ∀ c, CanAuthenticate I d c 0) :
    FlowFinalizableAt h z0 hl (fun _ bh => bh) (everyChainSystem 1 2)
      (honestAccess h z0 hl (everyChainSystem 1 2)) I d twoChainFlow :=
  fun l hl' => ⟨0, (twoChainEvidence h z0 hl l).2, le_refl 0,
    ⟨l.bundleHash.val, twoChain_index_lt l hl', rfl⟩, hauth l.chain, twoChain_accepts h z0 hl l hl'⟩

lemma importsAtFive_authenticates (c : Chain) : CanAuthenticate importsAtFive 5 c 0 :=
  ⟨timeOneRoot, ⟨rfl, rfl⟩, Nat.zero_le _⟩

lemma importsAtFive_six_empty (R : SlRoot) : ¬ importsAtFive 6 R := fun hR =>
  absurd hR.1 (by decide)

/-! ## The countermodel and the witness -/

theorem executed_flow_not_finalizable_at_unimported_destination (h : Hash) (z0 : UInt256)
    (hl : LeafHash) :
    ∃ (A : Access) (ev : GateEvidence),
      Wf (everyChainSystem 1 2)
        ∧ DataAvailable h z0 hl (everyChainSystem 1 2) A
        ∧ ExecutedAtBy h z0 hl (fun _ bh => bh) (honestFlowHash twoChainFlow)
            (everyChainSystem 1 2) importsAtFive 5 twoChainFlow ev ⟨0, 1⟩
        ∧ FlowFinalizableBy h z0 hl (fun _ bh => bh) (everyChainSystem 1 2) A twoChainFlow
        ∧ ¬ LegFinalizableAt h z0 hl (fun _ bh => bh) (everyChainSystem 1 2) A importsAtFive 6
            twoChainFlow ⟨1, 2⟩
        ∧ ¬ FlowFinalizableAt h z0 hl (fun _ bh => bh) (everyChainSystem 1 2) A importsAtFive 6
            twoChainFlow
        ∧ ¬ PostDeadlineRootAt (everyChainSystem 1 2) importsAtFive 6 twoChainFlow.deadline := by
  have hnot : ¬ LegFinalizableAt h z0 hl (fun _ bh => bh) (everyChainSystem 1 2)
      (honestAccess h z0 hl (everyChainSystem 1 2)) importsAtFive 6 twoChainFlow ⟨1, 2⟩ := by
    rintro ⟨_, _, _, _, ⟨R, hR, _⟩, _⟩
    exact importsAtFive_six_empty R hR
  refine ⟨honestAccess h z0 hl (everyChainSystem 1 2), twoChainEvidence h z0 hl,
    everyChainSystem_wf (by decide) (by decide), honestAccess_dataAvailable h z0 hl _,
    ⟨twoChain_executes h z0 hl, fun l _ => importsAtFive_authenticates l.chain⟩, ?_, hnot,
    fun hf => hnot (hf ⟨1, 2⟩ (by simp [twoChainFlow])), ?_⟩
  · intro l hl'
    obtain ⟨n, p, hon, hA, _, hacc⟩ :=
      twoChain_finalizableAt h z0 hl (fun c => importsAtFive_authenticates c) l hl'
    exact ⟨n, p, hon, hA, hacc⟩
  · rintro ⟨R, hR, _⟩
    exact importsAtFive_six_empty R hR

theorem finalizable_at_importing_destination_witness (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (A : Access) (ev : GateEvidence),
      Wf (everyChainSystem 1 2) ∧ DataAvailable h z0 hl (everyChainSystem 1 2) A
        ∧ ExecutedViaBy h z0 hl (fun _ bh => bh) (honestFlowHash twoChainFlow)
            (everyChainSystem 1 2) twoChainFlow ev ⟨0, 1⟩
        ∧ PostDeadlineRootAt (everyChainSystem 1 2) importsAtFive 5 twoChainFlow.deadline
        ∧ ¬ GateBreak h z0 hl (everyChainSystem 1 2) twoChainFlow ev
        ∧ FlowFinalizableAt h z0 hl (fun _ bh => bh) (everyChainSystem 1 2) A importsAtFive 5
            twoChainFlow :=
  ⟨honestAccess h z0 hl (everyChainSystem 1 2), twoChainEvidence h z0 hl,
    everyChainSystem_wf (by decide) (by decide), honestAccess_dataAvailable h z0 hl _,
    twoChain_executes h z0 hl,
    ⟨timeOneRoot, ⟨rfl, rfl⟩, Nat.zero_le _, fun _ _ hn => hn⟩,
    twoChain_no_gate_break h z0 hl,
    twoChain_finalizableAt h z0 hl (fun c => importsAtFive_authenticates c)⟩

end Contracts.FinalityFaithful

/-! ## Certificates -/

namespace Contracts.FinalityFaithful

theorem ExecutedFlowNotFinalizableAtUnimportedDestination :
    Properties.ExecutedFlowNotFinalizableAtUnimportedDestination :=
  executed_flow_not_finalizable_at_unimported_destination
theorem ExecutedImpliesFinalizableAtImportingDestinationOrBreak :
    Properties.ExecutedImpliesFinalizableAtImportingDestinationOrBreak :=
  fun _ _ _ _ _ _ hS _ hDA _ _ _ _ _ hex hroot other hother =>
    executed_implies_finalizable_at_importing_destination_or_break hS hDA hex hroot other hother
theorem NoneOrAllAtImportingDestinationOrBreak :
    Properties.NoneOrAllAtImportingDestinationOrBreak :=
  fun _ _ _ _ _ _ hS _ hDA _ _ F ev hroot =>
    none_or_all_at_importing_destination_or_break hS hDA F ev hroot
theorem ExecutedFinalityPersistsAtAuthenticatingDestinationOrBreak :
    Properties.ExecutedFinalityPersistsAtAuthenticatingDestinationOrBreak :=
  fun _ _ _ _ _ _ hS _ hDA _ _ _ _ hex other hother =>
    executed_finality_persists_at_authenticating_destination_or_break hS hDA hex other hother
theorem FinalizableAtImportingDestinationWitness :
    Properties.FinalizableAtImportingDestinationWitness :=
  finalizable_at_importing_destination_witness

end Contracts.FinalityFaithful
