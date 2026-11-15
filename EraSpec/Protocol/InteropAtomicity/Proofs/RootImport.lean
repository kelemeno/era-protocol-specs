import EraSpec.Protocol.InteropAtomicity.Properties.RootImport
import EraSpec.Protocol.InteropAtomicity.Proofs.Atomicity
import EraSpec.Protocol.InteropAtomicity.Proofs.SourceHeight
import EraSpec.Protocol.InteropAtomicity.Proofs.FlowBinding

/-!
# Proofs: finalizability on the destination that has to finalize

Proofs of `EraSpec.Protocol.InteropAtomicity.Properties.RootImport`.

Two small facts carry the corrected results.  A destination's acceptance contains the old
acceptance (`leg_finalizable_at_imp_by`, `executed_at_projects`).  And on a ready destination
the honest multi-hop settlement proof supplies the rest (`leg_finalizable_at_of_by`).  Each
corrected result is the matching `Contracts.Atomicity` (or `Contracts.FlowBinding`) result
pushed through those two facts.  No hash premise enters: the hash side is only ever reached
through the existing `…OrBreak` lemmas.

The countermodel's rejection on `dB` needs no hash reasoning at all.  `dB` has imported
nothing, so `SettlementAccepted` fails on every proof.
-/

namespace Contracts.RootImport

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree Contracts.Atomicity

/-! ## The destination gate and the old predicates -/

theorem executed_at_projects {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {W : World} {S : System} {d : Dest} {sl : Chain} {F : Flow}
    {ev : GateEvidenceAt} {leg : FlowLeg} (hex : ExecutedAtBy h z0 hl cv fh W S d sl F ev leg) :
    ExecutedViaBy h z0 hl cv fh S F (imtEvidence ev) leg := by
  obtain ⟨hmem, hchk, _, hall⟩ := hex
  exact ⟨hmem, hchk, fun l hl' => ⟨(hall l hl').1, (hall l hl').2.2.2⟩⟩

theorem accepted_at_shape {h : Hash} {z0 : UInt256} {hl : LeafHash} {W : World} {S : System}
    {d : Dest} {sl c : Chain} {n : ℕ} {v : UInt256} {p : ImtProof} {sp : SettlementProof}
    (hacc : AcceptsAt h z0 hl W S d sl c n v p sp) :
    sp.finalProofNode = false ∧ sp.slChainId = sl ∧ W.imported d sl sp.slBlock
      ∧ RootImported W d sl c n ∧ Accepts h z0 hl S c n v p := by
  obtain ⟨⟨hfin, himp, hcov⟩, hsl, hA⟩ := hacc
  subst hsl
  exact ⟨hfin, rfl, himp, ⟨sp.slBlock, himp, hcov⟩, hA⟩

/-- A leg finalizable on a destination is finalizable in `Contracts.Atomicity`'s sense: drop
the settlement proof. -/
theorem leg_finalizable_at_imp_by {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {W : World} {S : System} {A : Access} {SA : SettlementAccess} {d : Dest} {sl : Chain}
    {F : Flow} {leg : FlowLeg} (hf : LegFinalizableAt h z0 hl cv W S A SA d sl F leg) :
    LegFinalizableBy h z0 hl cv S A F leg := by
  obtain ⟨n, p, _, hon, hA, _, _, _, hacc⟩ := hf
  exact ⟨n, p, hon, hA, hacc⟩

/-- On a destination with import availability, and with settlement data available, a leg
finalizable in `Contracts.Atomicity`'s sense is finalizable on the destination.  The
covering import gives the root, and settlement data availability gives the honest multi-hop
proof to it. -/
theorem leg_finalizable_at_of_by {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {W : World} {S : System} {A : Access} {SA : SettlementAccess} {d : Dest} {sl : Chain}
    {F : Flow} {leg : FlowLeg} (hSA : SettlementDataAvailable W SA)
    (hI : ImportAvailable W S d sl F.deadline) (hf : LegFinalizableBy h z0 hl cv S A F leg) :
    LegFinalizableAt h z0 hl cv W S A SA d sl F leg := by
  obtain ⟨n, p, hon, hA, hacc⟩ := hf
  obtain ⟨k, himp, hcov⟩ := hI leg.chain n hon
  exact ⟨n, p, honestSettlementProof sl k, hon, hA, hSA _ _ _ _ hcov, ⟨rfl, himp, hcov⟩, rfl, hacc⟩

theorem flow_finalizable_at_imp_by {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {W : World} {S : System} {A : Access} {SA : SettlementAccess} {d : Dest} {sl : Chain}
    {F : Flow} (hf : FlowFinalizableAt h z0 hl cv W S A SA d sl F) :
    FlowFinalizableBy h z0 hl cv S A F :=
  fun leg hleg => leg_finalizable_at_imp_by (hf.2 leg hleg)

theorem ready_finalizable_at_iff_by {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {W : World} {S : System} {A : Access} {SA : SettlementAccess} (hSA : SettlementDataAvailable W SA)
    {d : Dest} {sl : Chain} {F : Flow} (hl1 : W.l1 d = sl) (hI : ImportAvailable W S d sl F.deadline) :
    FlowFinalizableAt h z0 hl cv W S A SA d sl F ↔ FlowFinalizableBy h z0 hl cv S A F :=
  ⟨flow_finalizable_at_imp_by,
    fun hf => ⟨hl1, fun leg hleg => leg_finalizable_at_of_by hSA hI (hf leg hleg)⟩⟩

/-! ## Discharging the new premises -/

theorem honest_settlement_access_available (W : World) :
    SettlementDataAvailable W (honestSettlementAccess W) :=
  fun _ _ sl k hcov => ⟨sl, k, hcov, rfl⟩

theorem import_available_of_post_deadline_import {W : World} {S : System} {d : Dest} {sl : Chain}
    {k D : ℕ} (himp : W.imported d sl k) (hD : D ≤ (W.slRoot sl k).created)
    (hagg : Contracts.Timeout.Aggregates S (W.slRoot sl k)) : ImportAvailable W S d sl D :=
  fun c n hn => ⟨k, himp, hagg c n (le_trans hn hD)⟩

theorem finalizable_at_persists_as_imports_grow {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {W W' : World} {S : System} {A : Access} {SA : SettlementAccess} {d : Dest}
    {sl : Chain} {F : Flow} (hg : ImportsGrow W W') :
    (ImportAvailable W S d sl F.deadline → ImportAvailable W' S d sl F.deadline)
      ∧ (SettlementDataAvailable W SA → SettlementDataAvailable W' SA)
      ∧ (FlowFinalizableAt h z0 hl cv W S A SA d sl F →
          FlowFinalizableAt h z0 hl cv W' S A SA d sl F) := by
  obtain ⟨hroot, hl1, himp⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · intro hI c n hn
    obtain ⟨k, hk, hcov⟩ := hI c n hn
    exact ⟨k, himp _ _ _ hk, by rw [hroot]; exact hcov⟩
  · intro hSA c n sl' k hcov
    rw [hroot] at hcov
    exact hSA c n sl' k hcov
  · rintro ⟨hl1d, hall⟩
    refine ⟨by rw [hl1]; exact hl1d, fun leg hleg => ?_⟩
    obtain ⟨n, p, sp, hon, hA, hsa, ⟨hfin, hk, hcov⟩, hsl, hacc⟩ := hall leg hleg
    exact ⟨n, p, sp, hon, hA, hsa, ⟨hfin, himp _ _ _ hk, by rw [hroot]; exact hcov⟩, hsl, hacc⟩

/-! ## The corrected finalizability results -/

/-- **MEMBERSHIP, DATA AVAILABILITY AND A COVERING IMPORT GIVE A PROOF THE DESTINATION
ACCEPTS.** -/
theorem member_is_finalizable_at {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {W : World} {S : System} (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A)
    {SA : SettlementAccess} (hSA : SettlementDataAvailable W SA) {d : Dest} {sl : Chain}
    {F : Flow} {leg : FlowLeg} {n : ℕ} (hon : S.time leg.chain n ≤ F.deadline)
    (himp : RootImported W d sl leg.chain n)
    (hmem : legValue cv F leg ∈ keys (toAbs (S.tree leg.chain n))) :
    LegFinalizableAt h z0 hl cv W S A SA d sl F leg := by
  obtain ⟨i, hi, hacc⟩ := honest_accepts (h := h) (z0 := z0) (hl := hl) hS hmem
  obtain ⟨k, hk, hcov⟩ := himp
  exact ⟨n, honestProof h z0 hl S leg.chain n i, honestSettlementProof sl k, hon, hDA _ _ _ hi,
    hSA _ _ _ _ hcov, ⟨rfl, hk, hcov⟩, rfl, hacc⟩

theorem executed_implies_all_finalizable_at_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {W : World} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {SA : SettlementAccess} (hSA : SettlementDataAvailable W SA)
    {d : Dest} {sl : Chain} {F : Flow} (hI : ImportAvailable W S d sl F.deadline)
    {ev : GateEvidence} {leg : FlowLeg} (hex : ExecutedViaBy h z0 hl cv fh S F ev leg)
    (other : FlowLeg) (hother : other ∈ F.legs) :
    LegFinalizableAt h z0 hl cv W S A SA d sl F other
      ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2 := by
  obtain ⟨hon, hacc⟩ := hex.2.2 other hother
  rcases finality_means_membership_or_break hacc with hmem | hb
  · exact Or.inl (member_is_finalizable_at hS hDA hSA hon (hI _ _ hon) hmem)
  · exact Or.inr hb

theorem executed_at_implies_all_finalizable_at_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {W : World} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {SA : SettlementAccess} (hSA : SettlementDataAvailable W SA)
    {dA dB : Dest} {sl : Chain} {F : Flow} {ev : GateEvidenceAt} {leg : FlowLeg}
    (hex : ExecutedAtBy h z0 hl cv fh W S dA sl F ev leg) (hl1 : W.l1 dB = sl)
    (hI : ImportAvailable W S dB sl F.deadline) :
    FlowFinalizableAt h z0 hl cv W S A SA dB sl F ∨ GateBreak h z0 hl S F (imtEvidence ev) := by
  by_cases hb : GateBreak h z0 hl S F (imtEvidence ev)
  · exact Or.inr hb
  · refine Or.inl ⟨hl1, fun other hother => ?_⟩
    rcases executed_implies_all_finalizable_at_or_break hS hDA hSA hI (executed_at_projects hex)
        other hother with hf | hbo
    · exact hf
    · exact absurd ⟨other, hother, hbo⟩ hb

theorem none_or_all_at_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {W : World} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {SA : SettlementAccess} (hSA : SettlementDataAvailable W SA)
    {d : Dest} {sl : Chain} {F : Flow} (hl1 : W.l1 d = sl) (hI : ImportAvailable W S d sl F.deadline)
    (ev : GateEvidence) :
    FlowFinalizableAt h z0 hl cv W S A SA d sl F
      ∨ (∀ leg, ¬ ExecutedViaBy h z0 hl cv fh S F ev leg)
      ∨ GateBreak h z0 hl S F ev := by
  rcases none_or_all_or_break (cv := cv) (fh := fh) hS hDA F ev with hf | hno | hb
  · exact Or.inl ((ready_finalizable_at_iff_by hSA hl1 hI).2 hf)
  · exact Or.inr (Or.inl hno)
  · exact Or.inr (Or.inr hb)

theorem first_stranded_leg_at_unique {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {W : World} {S : System} {A : Access} {SA : SettlementAccess} {d : Dest} {sl : Chain}
    {F : Flow} {l₁ l₂ : FlowLeg} (h₁ : FirstStrandedLegAt h z0 hl cv W S A SA d sl F l₁)
    (h₂ : FirstStrandedLegAt h z0 hl cv W S A SA d sl F l₂) : l₁ = l₂ := by
  obtain ⟨pre₁, post₁, he₁, hp₁, hn₁⟩ := h₁
  obtain ⟨pre₂, post₂, he₂, hp₂, hn₂⟩ := h₂
  exact first_failure_unique pre₁ pre₂ post₁ post₂ l₁ l₂ (he₁.symm.trans he₂) hp₁ hn₁ hp₂ hn₂

theorem ready_first_stranded_leg_at_iff {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {W : World} {S : System} {A : Access} {SA : SettlementAccess}
    (hSA : SettlementDataAvailable W SA) {d : Dest} {sl : Chain} {F : Flow}
    (hI : ImportAvailable W S d sl F.deadline) (leg : FlowLeg) :
    FirstStrandedLegAt h z0 hl cv W S A SA d sl F leg ↔ FirstStrandedLeg h z0 hl cv S A F leg := by
  have hiff : ∀ l, LegFinalizableAt h z0 hl cv W S A SA d sl F l ↔ LegFinalizableBy h z0 hl cv S A F l :=
    fun _ => ⟨leg_finalizable_at_imp_by, leg_finalizable_at_of_by hSA hI⟩
  constructor
  · rintro ⟨pre, post, he, hpre, hn⟩
    exact ⟨pre, post, he, fun l hl' => (hiff l).1 (hpre l hl'), fun hb => hn ((hiff leg).2 hb)⟩
  · rintro ⟨pre, post, he, hpre, hn⟩
    exact ⟨pre, post, he, fun l hl' => (hiff l).2 (hpre l hl'), fun hb => hn ((hiff leg).1 hb)⟩

/-- On a destination with import availability, the pinned break there is the world's pinned
break. -/
theorem pinned_gate_break_at_iff {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {W : World} {S : System} {A : Access} {SA : SettlementAccess}
    (hSA : SettlementDataAvailable W SA) {d : Dest} {sl : Chain} {F : Flow}
    (hI : ImportAvailable W S d sl F.deadline) (ev : GateEvidence) :
    PinnedGateBreakAt h z0 hl cv W S A SA d sl F ev ↔ PinnedGateBreak h z0 hl cv S A F ev := by
  constructor
  · rintro ⟨leg, hf, hb⟩
    exact ⟨leg, (ready_first_stranded_leg_at_iff hSA hI leg).1 hf, hb⟩
  · rintro ⟨leg, hf, hb⟩
    exact ⟨leg, (ready_first_stranded_leg_at_iff hSA hI leg).2 hf, hb⟩

theorem none_or_all_at_or_break_pinned {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {W : World} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {SA : SettlementAccess} (hSA : SettlementDataAvailable W SA)
    {d : Dest} {sl : Chain} {F : Flow} (hl1 : W.l1 d = sl) (hI : ImportAvailable W S d sl F.deadline)
    (ev : GateEvidence) :
    FlowFinalizableAt h z0 hl cv W S A SA d sl F
      ∨ (∀ leg, ¬ ExecutedViaBy h z0 hl cv fh S F ev leg)
      ∨ PinnedGateBreakAt h z0 hl cv W S A SA d sl F ev := by
  rcases none_or_all_or_break_pinned (cv := cv) (fh := fh) hS hDA F ev with hf | hno | hp
  · exact Or.inl ((ready_finalizable_at_iff_by hSA hl1 hI).2 hf)
  · exact Or.inr (Or.inl hno)
  · exact Or.inr (Or.inr ((pinned_gate_break_at_iff hSA hI ev).2 hp))

theorem executed_implies_finality_persists_at_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {W : World} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {SA : SettlementAccess} (hSA : SettlementDataAvailable W SA)
    {d : Dest} {sl : Chain} {F : Flow} {ev : GateEvidence} {leg : FlowLeg}
    (hex : ExecutedViaBy h z0 hl cv fh S F ev leg) (other : FlowLeg) (hother : other ∈ F.legs) :
    (∃ n, S.time other.chain n ≤ F.deadline ∧
      ∀ m, n ≤ m → S.time other.chain m ≤ F.deadline → RootImported W d sl other.chain m →
        ∃ (p : ImtProof) (sp : SettlementProof), A other.chain m p ∧ SA other.chain m sp
          ∧ AcceptsAt h z0 hl W S d sl other.chain m (legValue cv F other) p sp)
      ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2 := by
  rcases executed_implies_finality_persists_or_break hS hDA hex other hother with
    ⟨n, hon, hall⟩ | hb
  · refine Or.inl ⟨n, hon, fun m hnm hm himp => ?_⟩
    obtain ⟨p, hp, hacc⟩ := hall m hnm hm
    obtain ⟨k, hk, hcov⟩ := himp
    exact ⟨p, honestSettlementProof sl k, hp, hSA _ _ _ _ hcov, ⟨rfl, hk, hcov⟩, rfl, hacc⟩
  · exact Or.inr hb

theorem none_or_all_at_or_break_pinned_from_runs {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {St : Chain → ℕ → HState} {time : Chain → ℕ → ℕ}
    (hW : RunsWf St time) {A : Access} (hDA : DataAvailable h z0 hl (systemOfRuns St time) A)
    {W : World} {SA : SettlementAccess} (hSA : SettlementDataAvailable W SA) {d : Dest}
    {sl : Chain} {F : Flow} (hl1 : W.l1 d = sl)
    (hI : ImportAvailable W (systemOfRuns St time) d sl F.deadline) (ev : GateEvidence) :
    FlowFinalizableAt h z0 hl cv W (systemOfRuns St time) A SA d sl F
      ∨ (∀ leg, ¬ ExecutedViaBy h z0 hl cv fh (systemOfRuns St time) F ev leg)
      ∨ PinnedGateBreakAt h z0 hl cv W (systemOfRuns St time) A SA d sl F ev :=
  none_or_all_at_or_break_pinned (wf_of_runs St time hW) hDA hSA hl1 hI ev

theorem executed_implies_real_flow_finalizable_at_or_logged_clash {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {W : World} {SA : SettlementAccess}
    (hSA : SettlementDataAvailable W SA) {Ms Ns : Contracts.Refund.Managers}
    {log : List Contracts.FlowBinding.CheckedCall}
    (hrun : Contracts.FlowBinding.RunLog h z0 hl cv fh S Ms Ns log)
    {e : Contracts.FlowBinding.ExecCall} (he : Contracts.FlowBinding.CheckedCall.execute e ∈ log)
    {c : Contracts.FlowBinding.CheckedCall} (hc : c ∈ log) (hid : c.flow.flowId = e.flow.flowId)
    {d : Dest} {sl : Chain} (hl1 : W.l1 d = sl) (hI : ImportAvailable W S d sl c.flow.deadline) :
    FlowFinalizableAt h z0 hl cv W S A SA d sl c.flow
      ∨ PinnedGateBreak h z0 hl cv S A e.flow e.evidence
      ∨ FlowIdClash fh e.flow c.flow := by
  rcases Contracts.FlowBinding.ExecutedImpliesRealFlowFinalizableOrLoggedClash h z0 hl cv fh S hS A
      hDA Ms Ns log hrun e he c hc hid with hf | hp | hcl
  · exact Or.inl ((ready_finalizable_at_iff_by hSA hl1 hI).2 hf)
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr hcl)

/-! ## The concrete configurations -/

lemma twoChainSystem_tree_zero (a b : UInt256) (n : ℕ) :
    (twoChainSystem a b).tree 0 n = insert setup a 0 := by simp [twoChainSystem]

lemma twoChainSystem_tree_one (a b : UInt256) (n : ℕ) :
    (twoChainSystem a b).tree 1 n = insert setup b 0 := by
  simp [twoChainSystem, (by decide : (1 : Chain) ≠ 0)]

lemma twoChainSystem_tree_other {a b : UInt256} {c : Chain} (h0 : c ≠ 0) (h1 : c ≠ 1) (n : ℕ) :
    (twoChainSystem a b).tree c n = setup := by simp [twoChainSystem, h0, h1]

lemma twoChainSystem_height_zero (a b : UInt256) (n : ℕ) :
    (twoChainSystem a b).height 0 n = 1 := by simp [twoChainSystem]

lemma twoChainSystem_height_one (a b : UInt256) (n : ℕ) :
    (twoChainSystem a b).height 1 n = 1 := by simp [twoChainSystem]

lemma twoChainSystem_height_other {a b : UInt256} {c : Chain} (h0 : c ≠ 0) (h1 : c ≠ 1) (n : ℕ) :
    (twoChainSystem a b).height c n = 0 := by simp [twoChainSystem, h0, h1]

lemma twoChainSystem_wf {a b : UInt256} (ha : 0 < a) (hb : 0 < b) : Wf (twoChainSystem a b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    by_cases h0 : c = 0
    · subst h0
      rw [twoChainSystem_tree_zero]
      exact Reaches.tail Reaches.refl (setup_insertGuard ha)
    by_cases h1 : c = 1
    · subst h1
      rw [twoChainSystem_tree_one]
      exact Reaches.tail Reaches.refl (setup_insertGuard hb)
    rw [twoChainSystem_tree_other h0 h1]
    exact Reaches.refl
  · intro c n
    exact Reaches.refl
  · intro c i j hij
    exact hij
  · intro c n
    by_cases h0 : c = 0
    · subst h0
      rw [twoChainSystem_tree_zero, twoChainSystem_height_zero, insertSetup_leafCount]
      norm_num
    by_cases h1 : c = 1
    · subst h1
      rw [twoChainSystem_tree_one, twoChainSystem_height_one, insertSetup_leafCount]
      norm_num
    rw [twoChainSystem_tree_other h0 h1, twoChainSystem_height_other h0 h1]
    show (1 : ℕ) ≤ 2 ^ 0
    norm_num

lemma twoChain_wf : Wf (twoChainSystem 1 2) := twoChainSystem_wf (by decide) (by decide)

/-- In a system whose chain-`c` tree at batch `n` is `insert setup v 0`, the honest proof of
leaf 1 is accepted for `v`. -/
lemma accepts_inserted_leaf {h : Hash} {z0 : UInt256} {hl : LeafHash} {S : System} {c : Chain}
    {n : ℕ} {v : UInt256} (hT : S.tree c n = insert setup v 0)
    (hcap : (S.tree c n).leafCount ≤ 2 ^ S.height c n) :
    Accepts h z0 hl S c n v (honestProof h z0 hl S c n 1) := by
  have hcount : (S.tree c n).leafCount = 2 := by rw [hT]; rfl
  have hI := inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := S.tree c n)
    (height := S.height c n) hcap (i := 1) (by rw [hcount]; norm_num)
  have hv : ((S.tree c n).leaf 1).value = v := by rw [hT, insertSetup_leaf_one_value]
  rw [hv] at hI
  exact hI

/-- Each leg of `mixedFlow 0 1 2` sits at index 1 of its chain's tree in `twoChainSystem 1 2`. -/
lemma twoChain_leg_tree {l : FlowLeg} (hl' : l ∈ (mixedFlow 0 1 2).legs) (n : ℕ) :
    (twoChainSystem 1 2).tree l.chain n = insert setup l.bundleHash 0 := by
  rcases List.mem_cons.mp hl' with rfl | hl'
  · exact twoChainSystem_tree_zero 1 2 n
  · obtain rfl := List.mem_singleton.mp hl'
    exact twoChainSystem_tree_one 1 2 n

lemma twoChain_leg_pos {l : FlowLeg} (hl' : l ∈ (mixedFlow 0 1 2).legs) : 0 < l.bundleHash := by
  rcases List.mem_cons.mp hl' with rfl | hl'
  · show (0 : UInt256) < 1
    decide
  · obtain rfl := List.mem_singleton.mp hl'
    show (0 : UInt256) < 2
    decide

lemma twoChain_leg_mem {l : FlowLeg} (hl' : l ∈ (mixedFlow 0 1 2).legs) (n : ℕ) :
    legValue (fun _ b => b) (mixedFlow 0 1 2) l ∈ keys (toAbs ((twoChainSystem 1 2).tree l.chain n)) := by
  rw [twoChain_leg_tree hl' n]
  exact mem_insertSetup (twoChain_leg_pos hl')

lemma twoChain_leg_accepts (h : Hash) (z0 : UInt256) (hl : LeafHash) {l : FlowLeg}
    (hl' : l ∈ (mixedFlow 0 1 2).legs) :
    Accepts h z0 hl (twoChainSystem 1 2) l.chain 0 (legValue (fun _ b => b) (mixedFlow 0 1 2) l)
      (honestProof h z0 hl (twoChainSystem 1 2) l.chain 0 1) :=
  accepts_inserted_leaf (twoChain_leg_tree hl' 0) (twoChain_wf.capacity _ _)

/-- Honest destination evidence on `twoChainSystem 1 2`: for each leg, batch 0, the honest
proof of leaf 1 of its chain's tree, and the honest multi-hop proof to the root of `sl` at
block 0. -/
def twoChainEvidence (h : Hash) (z0 : UInt256) (hl : LeafHash) (sl : Chain) : GateEvidenceAt :=
  fun l => (0, honestProof h z0 hl (twoChainSystem 1 2) l.chain 0 1, honestSettlementProof sl 0)

/-- A destination that has imported the root is ready for every deadline up to the root's
creation, on any system that root aggregates. -/
theorem importWorld_ready {imp : Dest → Prop} {sl : Chain} {d : Dest} (hd : imp d) (S : System)
    (hagg : Contracts.Timeout.Aggregates S Contracts.Timeout.timeOneRoot) {D : ℕ} (hD : D ≤ 1) :
    ImportAvailable (importWorld sl imp) S d sl D :=
  import_available_of_post_deadline_import (k := 0) ⟨hd, rfl, rfl⟩ hD hagg

/-- A destination that has imported nothing has no import availability, as soon as one batch
settled by the deadline. -/
theorem importWorld_not_ready {imp : Dest → Prop} {sl : Chain} {d : Dest} (hd : ¬ imp d)
    {S : System} {D : ℕ} (h0 : S.time 0 0 ≤ D) : ¬ ImportAvailable (importWorld sl imp) S d sl D := by
  intro hI
  obtain ⟨_, ⟨hk, _, _⟩, _⟩ := hI 0 0 h0
  exact hd hk

/-- …and accepts no settlement proof at all. -/
theorem importWorld_rejects {imp : Dest → Prop} {sl : Chain} {d : Dest} (hd : ¬ imp d) {c : Chain}
    {n : ℕ} {sp : SettlementProof} : ¬ SettlementAccepted (importWorld sl imp) d c n sp := by
  rintro ⟨_, ⟨hk, _⟩, _⟩
  exact hd hk

theorem twoChain_executed_at (h : Hash) (z0 : UInt256) (hl : LeafHash) {sl : Chain}
    {imp : Dest → Prop} {d : Dest} (hd : imp d) :
    ExecutedAtBy h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2)) (importWorld sl imp)
      (twoChainSystem 1 2) d sl (mixedFlow 0 1 2) (twoChainEvidence h z0 hl sl) ⟨0, 1⟩ := by
  refine ⟨List.mem_cons_self, (honest_flowHash_no_clash _).1, rfl, fun l hl' => ?_⟩
  exact ⟨le_refl _, ⟨rfl, ⟨hd, rfl, rfl⟩, Nat.zero_le _⟩, rfl, twoChain_leg_accepts h z0 hl hl'⟩

theorem twoChain_flow_finalizable_at (h : Hash) (z0 : UInt256) (hl : LeafHash) {sl : Chain}
    {imp : Dest → Prop} {d : Dest} (hd : imp d) :
    FlowFinalizableAt h z0 hl (fun _ b => b) (importWorld sl imp) (twoChainSystem 1 2)
      (honestAccess h z0 hl (twoChainSystem 1 2)) (honestSettlementAccess (importWorld sl imp)) d sl
      (mixedFlow 0 1 2) :=
  ⟨rfl, fun _ hl' => member_is_finalizable_at twoChain_wf (honestAccess_dataAvailable h z0 hl _)
    (honest_settlement_access_available _) (n := 0) (le_refl _) ⟨0, ⟨hd, rfl, rfl⟩, Nat.zero_le _⟩
    (twoChain_leg_mem hl' 0)⟩

/-- The honest evidence `twoChainEvidence` carries no `GateBreak` on `mixedFlow 0 1 2`.
`GateBreak` reads only the IMT half of the evidence and the system, not the world. -/
theorem twoChain_evidence_no_gate_break (h : Hash) (z0 : UInt256) (hl : LeafHash) (sl : Chain) :
    ¬ GateBreak h z0 hl (twoChainSystem 1 2) (mixedFlow 0 1 2)
      (imtEvidence (twoChainEvidence h z0 hl sl)) := by
  rintro ⟨l, hl', hb⟩
  have hlt : 1 < ((twoChainSystem 1 2).tree l.chain 0).leafCount := by
    rw [twoChain_leg_tree hl' 0, insertSetup_leafCount]
    norm_num
  exact honestProof_no_break h z0 hl (twoChainSystem 1 2) l.chain 0 1 hlt hb

/-! ## Countermodels -/

theorem without_import_flow_sits_half_executed (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (sl : Chain) (dA dB : Dest) (hne : dA ≠ dB) :
    Wf (twoChainSystem 1 2)
      ∧ DataAvailable h z0 hl (twoChainSystem 1 2) (honestAccess h z0 hl (twoChainSystem 1 2))
      ∧ SettlementDataAvailable (importWorld sl (· = dA))
          (honestSettlementAccess (importWorld sl (· = dA)))
      ∧ (importWorld sl (· = dA)).l1 dA = sl ∧ (importWorld sl (· = dA)).l1 dB = sl
      ∧ ImportAvailable (importWorld sl (· = dA)) (twoChainSystem 1 2) dA sl
          (mixedFlow 0 1 2).deadline
      ∧ ¬ ImportAvailable (importWorld sl (· = dA)) (twoChainSystem 1 2) dB sl
          (mixedFlow 0 1 2).deadline
      ∧ (∃ ev : GateEvidenceAt,
          ExecutedAtBy h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
            (importWorld sl (· = dA)) (twoChainSystem 1 2) dA sl (mixedFlow 0 1 2) ev ⟨0, 1⟩
          ∧ ¬ GateBreak h z0 hl (twoChainSystem 1 2) (mixedFlow 0 1 2) (imtEvidence ev))
      ∧ FlowFinalizableBy h z0 hl (fun _ b => b) (twoChainSystem 1 2)
          (honestAccess h z0 hl (twoChainSystem 1 2)) (mixedFlow 0 1 2)
      ∧ (∀ (fh : FlowHash) (leg : FlowLeg), ¬ ExecutedAt h z0 hl (fun _ b => b) fh
          (importWorld sl (· = dA)) (twoChainSystem 1 2) dB sl (mixedFlow 0 1 2) leg)
      ∧ (∀ (A : Access) (SA : SettlementAccess), ∀ leg ∈ (mixedFlow 0 1 2).legs,
          ¬ LegFinalizableAt h z0 hl (fun _ b => b) (importWorld sl (· = dA))
              (twoChainSystem 1 2) A SA dB sl (mixedFlow 0 1 2) leg)
      ∧ (∀ other ∈ (mixedFlow 0 1 2).legs, ∀ (N : ℕ) (q : ImtProof),
          ¬ LegRefundableBy h z0 hl (fun _ b => b) (twoChainSystem 1 2) (mixedFlow 0 1 2)
              other N q
            ∨ AbsenceBreak h z0 hl (twoChainSystem 1 2) (mixedFlow 0 1 2).deadline other.chain
                N q) := by
  have hnB : ¬ (dB = dA) := fun he => hne he.symm
  refine ⟨twoChain_wf, honestAccess_dataAvailable h z0 hl _, honest_settlement_access_available _,
    rfl, rfl, importWorld_ready rfl _ (fun _ _ hn => hn) (Nat.zero_le _),
    importWorld_not_ready hnB (le_refl _),
    ⟨twoChainEvidence h z0 hl sl, twoChain_executed_at h z0 hl rfl,
      twoChain_evidence_no_gate_break h z0 hl sl⟩,
    flow_finalizable_at_imp_by (twoChain_flow_finalizable_at h z0 hl (sl := sl) (imp := (· = dA)) rfl),
    ?_, ?_, ?_⟩
  · rintro fh leg ⟨ev, _, _, _, hall⟩
    exact importWorld_rejects hnB (hall ⟨0, 1⟩ List.mem_cons_self).2.1
  · rintro A SA leg _ ⟨n, p, sp, _, _, _, hset, _, _⟩
    exact importWorld_rejects hnB hset
  · intro other hother N q
    exact member_not_refundable_or_break twoChain_wf (n := 0) (le_refl _)
      (twoChain_leg_mem hother 0) N q

/-- The negation of `executed_at_implies_all_finalizable_at_or_break` without the import
premise on `dB`, refuted by `without_import_flow_sits_half_executed` at `dA = 0`, `dB = 1`. -/
theorem without_import_cross_destination_fails :
    ¬ ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (W : World)
      (S : System), Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
      ∀ (SA : SettlementAccess), SettlementDataAvailable W SA →
      ∀ (dA dB : Dest) (sl : Chain) (F : Flow) (ev : GateEvidenceAt) (leg : FlowLeg),
        ExecutedAtBy h z0 hl cv fh W S dA sl F ev leg → W.l1 dB = sl →
          FlowFinalizableAt h z0 hl cv W S A SA dB sl F
            ∨ GateBreak h z0 hl S F (imtEvidence ev) := by
  intro hall
  obtain ⟨hwf, hda, hsa, _, hl1B, _, _, ⟨ev, hex, hnb⟩, _, _, hnf, _⟩ :=
    without_import_flow_sits_half_executed (fun _ _ => 0) 0 toyLeafHash 0 0 1 (by decide)
  rcases hall _ _ _ _ _ _ _ hwf _ hda _ hsa _ _ _ _ ev _ hex hl1B with hF | hb
  · exact hnf _ _ ⟨0, 1⟩ List.mem_cons_self (hF.2 ⟨0, 1⟩ List.mem_cons_self)
  · exact hnb hb

theorem import_alone_restores_finalizability (h : Hash) (z0 : UInt256) (hl : LeafHash) (sl : Chain)
    (dA dB : Dest) :
    ImportsGrow (importWorld sl (· = dA)) (importWorld sl (fun d => d = dA ∨ d = dB))
      ∧ ImportAvailable (importWorld sl (fun d => d = dA ∨ d = dB)) (twoChainSystem 1 2) dB sl
          (mixedFlow 0 1 2).deadline
      ∧ FlowFinalizableAt h z0 hl (fun _ b => b) (importWorld sl (fun d => d = dA ∨ d = dB))
          (twoChainSystem 1 2) (honestAccess h z0 hl (twoChainSystem 1 2))
          (honestSettlementAccess (importWorld sl (fun d => d = dA ∨ d = dB))) dB sl
          (mixedFlow 0 1 2) :=
  ⟨⟨rfl, rfl, fun _ _ _ ⟨hd, hc, hk⟩ => ⟨Or.inl hd, hc, hk⟩⟩,
    importWorld_ready (Or.inr rfl) _ (fun _ _ hn => hn) (Nat.zero_le _),
    twoChain_flow_finalizable_at h z0 hl (Or.inr rfl)⟩

theorem without_settlement_data_leg_is_stuck (h : Hash) (z0 : UInt256) (hl : LeafHash) (sl : Chain)
    (d : Dest) :
    ImportAvailable (importWorld sl (· = d)) (twoChainSystem 1 2) d sl (mixedFlow 0 1 2).deadline
      ∧ ¬ SettlementDataAvailable (importWorld sl (· = d)) noSettlementAccess
      ∧ LegFinalizedAt h z0 hl (fun _ b => b) (importWorld sl (· = d)) (twoChainSystem 1 2) d sl
          (mixedFlow 0 1 2) ⟨0, 1⟩
      ∧ (∀ A : Access, ¬ LegFinalizableAt h z0 hl (fun _ b => b) (importWorld sl (· = d))
          (twoChainSystem 1 2) A noSettlementAccess d sl (mixedFlow 0 1 2) ⟨0, 1⟩)
      ∧ ∀ (N : ℕ) (q : ImtProof),
          ¬ LegRefundableBy h z0 hl (fun _ b => b) (twoChainSystem 1 2) (mixedFlow 0 1 2)
              ⟨0, 1⟩ N q
            ∨ AbsenceBreak h z0 hl (twoChainSystem 1 2) (mixedFlow 0 1 2).deadline 0 N q := by
  have hmemA : (⟨0, 1⟩ : FlowLeg) ∈ (mixedFlow 0 1 2).legs := List.mem_cons_self
  refine ⟨importWorld_ready rfl _ (fun _ _ hn => hn) (Nat.zero_le _), ?_, ?_, ?_, ?_⟩
  · intro hSA
    exact hSA 0 0 sl 0 (Nat.zero_le _)
  · exact ⟨0, honestProof h z0 hl (twoChainSystem 1 2) 0 0 1, honestSettlementProof sl 0, le_refl _,
      ⟨rfl, ⟨rfl, rfl, rfl⟩, Nat.zero_le _⟩, rfl, twoChain_leg_accepts h z0 hl hmemA⟩
  · rintro A ⟨_, _, _, _, _, hsa, _⟩
    exact hsa
  · intro N q
    exact member_not_refundable_or_break twoChain_wf (n := 0) (le_refl _) (twoChain_leg_mem hmemA 0) N q

/-! ## Anti-vacuity -/

theorem executed_at_or_break_satisfiable (h : Hash) (z0 : UInt256) (hl : LeafHash) (sl : Chain)
    (dA dB : Dest) :
    Wf (twoChainSystem 1 2)
      ∧ DataAvailable h z0 hl (twoChainSystem 1 2) (honestAccess h z0 hl (twoChainSystem 1 2))
      ∧ SettlementDataAvailable (importWorld sl (fun d => d = dA ∨ d = dB))
          (honestSettlementAccess (importWorld sl (fun d => d = dA ∨ d = dB)))
      ∧ (importWorld sl (fun d => d = dA ∨ d = dB)).l1 dB = sl
      ∧ ImportAvailable (importWorld sl (fun d => d = dA ∨ d = dB)) (twoChainSystem 1 2) dB sl
          (mixedFlow 0 1 2).deadline
      ∧ ∃ ev : GateEvidenceAt,
          ExecutedAtBy h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
            (importWorld sl (fun d => d = dA ∨ d = dB)) (twoChainSystem 1 2) dA sl
            (mixedFlow 0 1 2) ev ⟨0, 1⟩
          ∧ ¬ GateBreak h z0 hl (twoChainSystem 1 2) (mixedFlow 0 1 2) (imtEvidence ev)
          ∧ FlowFinalizableAt h z0 hl (fun _ b => b) (importWorld sl (fun d => d = dA ∨ d = dB))
              (twoChainSystem 1 2) (honestAccess h z0 hl (twoChainSystem 1 2))
              (honestSettlementAccess (importWorld sl (fun d => d = dA ∨ d = dB))) dB sl
              (mixedFlow 0 1 2) := by
  refine ⟨twoChain_wf, honestAccess_dataAvailable h z0 hl _, honest_settlement_access_available _,
    rfl, importWorld_ready (Or.inr rfl) _ (fun _ _ hn => hn) (Nat.zero_le _),
    twoChainEvidence h z0 hl sl, twoChain_executed_at h z0 hl (Or.inl rfl),
    twoChain_evidence_no_gate_break h z0 hl sl,
    twoChain_flow_finalizable_at h z0 hl (Or.inr rfl)⟩

theorem none_or_all_at_or_break_pinned_stranded_not_tautology (h : Hash) (z0 : UInt256)
    (hl : LeafHash) (sl : Chain) (d : Dest) :
    Wf (mixedSystem 1)
      ∧ DataAvailable h z0 hl (mixedSystem 1) (honestAccess h z0 hl (mixedSystem 1))
      ∧ SettlementDataAvailable (importWorld sl (· = d))
          (honestSettlementAccess (importWorld sl (· = d)))
      ∧ (importWorld sl (· = d)).l1 d = sl
      ∧ ImportAvailable (importWorld sl (· = d)) (mixedSystem 1) d sl (mixedFlow 0 1 2).deadline
      ∧ ¬ FlowFinalizableAt h z0 hl (fun _ b => b) (importWorld sl (· = d)) (mixedSystem 1)
          (honestAccess h z0 hl (mixedSystem 1)) (honestSettlementAccess (importWorld sl (· = d)))
          d sl (mixedFlow 0 1 2)
      ∧ FirstStrandedLegAt h z0 hl (fun _ b => b) (importWorld sl (· = d)) (mixedSystem 1)
          (honestAccess h z0 hl (mixedSystem 1)) (honestSettlementAccess (importWorld sl (· = d)))
          d sl (mixedFlow 0 1 2) ⟨1, 2⟩
      ∧ ∃ ev : GateEvidence,
          (∀ leg, ¬ ExecutedViaBy h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
              (mixedSystem 1) (mixedFlow 0 1 2) ev leg)
          ∧ ¬ PinnedGateBreakAt h z0 hl (fun _ b => b) (importWorld sl (· = d)) (mixedSystem 1)
              (honestAccess h z0 hl (mixedSystem 1))
              (honestSettlementAccess (importWorld sl (· = d))) d sl (mixedFlow 0 1 2) ev := by
  obtain ⟨hS, hDA, _, hnf, hfirst, ev, _, _, hnex, hnp⟩ :=
    NoneOrAllOrBreakPinnedStrandedNotTautology h z0 hl
  have hSA := honest_settlement_access_available (importWorld sl (· = d))
  have hI : ImportAvailable (importWorld sl (· = d)) (mixedSystem 1) d sl (mixedFlow 0 1 2).deadline :=
    importWorld_ready rfl _ (fun _ _ hn => hn) (Nat.zero_le _)
  exact ⟨hS, hDA, hSA, rfl, hI, fun hf => hnf (flow_finalizable_at_imp_by hf),
    (ready_first_stranded_leg_at_iff hSA hI _).2 hfirst, ev, hnex,
    fun hp => hnp ((pinned_gate_break_at_iff hSA hI ev).1 hp)⟩

theorem pinned_gate_break_at_fires (h : Hash) (z0 : UInt256) (sl : Chain) (d : Dest) :
    ∃ ev : GateEvidenceAt,
      ExecutedAtBy h z0 toyLeafHash (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
          (importWorld sl (· = d)) (mixedSystem 1) d sl (mixedFlow 0 1 2) ev ⟨0, 1⟩
        ∧ ¬ FlowFinalizableAt h z0 toyLeafHash (fun _ b => b) (importWorld sl (· = d))
            (mixedSystem 1) (honestAccess h z0 toyLeafHash (mixedSystem 1))
            (honestSettlementAccess (importWorld sl (· = d))) d sl (mixedFlow 0 1 2)
        ∧ PinnedGateBreakAt h z0 toyLeafHash (fun _ b => b) (importWorld sl (· = d))
            (mixedSystem 1) (honestAccess h z0 toyLeafHash (mixedSystem 1))
            (honestSettlementAccess (importWorld sl (· = d))) d sl (mixedFlow 0 1 2)
            (imtEvidence ev)
        ∧ ¬ InclusionBreak h z0 toyLeafHash (mixedSystem 1) 0 (imtEvidence ev ⟨0, 1⟩).1
            (imtEvidence ev ⟨0, 1⟩).2 := by
  obtain ⟨_, _, _, _, evF, _, hnbA, hexF, _, hpinF, _, _⟩ :=
    PinnedGateBreakFiresOnlyOnStrandedLeg h z0
  obtain ⟨_, nfinB, _⟩ := mixed_stranded_world h z0 toyLeafHash
  have hSA := honest_settlement_access_available (importWorld sl (· = d))
  have hI : ImportAvailable (importWorld sl (· = d)) (mixedSystem 1) d sl (mixedFlow 0 1 2).deadline :=
    importWorld_ready rfl _ (fun _ _ hn => hn) (Nat.zero_le _)
  have hmemB : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 0 1 2).legs :=
    List.mem_cons_of_mem _ (List.mem_singleton_self _)
  let ev : GateEvidenceAt := fun l => ((evF l).1, (evF l).2, honestSettlementProof sl 0)
  have hev : imtEvidence ev = evF := rfl
  refine ⟨ev, ⟨hexF.1, hexF.2.1, rfl, fun l hl' => ?_⟩, fun hf => nfinB
    (leg_finalizable_at_imp_by (hf.2 _ hmemB)), ?_, hnbA⟩
  · obtain ⟨hon, hacc⟩ := hexF.2.2 l hl'
    have hcov : (evF l).1 ≤ 1 := le_trans hon (Nat.zero_le _)
    exact ⟨hon, ⟨rfl, ⟨rfl, rfl, rfl⟩, hcov⟩, rfl, hacc⟩
  · rw [hev]
    exact (pinned_gate_break_at_iff hSA hI evF).2 hpinF

theorem none_or_all_at_or_break_pinned_from_runs_stranded (h : Hash) (z0 : UInt256)
    (hl : LeafHash) (sl : Chain) (d : Dest) :
    ∃ St : Chain → ℕ → HState, RunsWf St (fun _ n => n)
      ∧ DataAvailable h z0 hl (systemOfRuns St (fun _ n => n))
          (honestAccess h z0 hl (systemOfRuns St (fun _ n => n)))
      ∧ SettlementDataAvailable (importWorld sl (· = d))
          (honestSettlementAccess (importWorld sl (· = d)))
      ∧ (importWorld sl (· = d)).l1 d = sl
      ∧ ImportAvailable (importWorld sl (· = d)) (systemOfRuns St (fun _ n => n)) d sl
          (mixedFlow 0 1 2).deadline
      ∧ ¬ FlowFinalizableAt h z0 hl (fun _ b => b) (importWorld sl (· = d))
            (systemOfRuns St (fun _ n => n)) (honestAccess h z0 hl (systemOfRuns St (fun _ n => n)))
            (honestSettlementAccess (importWorld sl (· = d))) d sl (mixedFlow 0 1 2)
      ∧ ∃ ev : GateEvidence,
          (∀ leg, ¬ ExecutedViaBy h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
              (systemOfRuns St (fun _ n => n)) (mixedFlow 0 1 2) ev leg)
          ∧ ¬ PinnedGateBreakAt h z0 hl (fun _ b => b) (importWorld sl (· = d))
              (systemOfRuns St (fun _ n => n))
              (honestAccess h z0 hl (systemOfRuns St (fun _ n => n)))
              (honestSettlementAccess (importWorld sl (· = d))) d sl (mixedFlow 0 1 2) ev := by
  obtain ⟨St, hW, hEq⟩ := MixedSystemFromRuns 1 (by decide)
  obtain ⟨_, hDA, hSA, hl1, hI, hnf, _, ev, hnex, hnp⟩ :=
    none_or_all_at_or_break_pinned_stranded_not_tautology h z0 hl sl d
  refine ⟨St, hW, ?_⟩
  rw [hEq]
  exact ⟨hDA, hSA, hl1, hI, hnf, ev, hnex, hnp⟩

theorem executed_implies_real_flow_finalizable_at_or_logged_clash_witness (h : Hash) (z0 : UInt256)
    (hl : LeafHash) (sl : Chain) (d : Dest) :
    ∃ (log : List Contracts.FlowBinding.CheckedCall) (e : Contracts.FlowBinding.ExecCall),
      Wf (twoChainSystem 1 2)
        ∧ DataAvailable h z0 hl (twoChainSystem 1 2) (honestAccess h z0 hl (twoChainSystem 1 2))
        ∧ SettlementDataAvailable (importWorld sl (· = d))
            (honestSettlementAccess (importWorld sl (· = d)))
        ∧ Contracts.FlowBinding.RunLog h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
            (twoChainSystem 1 2) Contracts.Refund.emptyManagers Contracts.Refund.emptyManagers log
        ∧ Contracts.FlowBinding.CheckedCall.execute e ∈ log
        ∧ e.flow = mixedFlow 0 1 2
        ∧ (importWorld sl (· = d)).l1 d = sl
        ∧ ImportAvailable (importWorld sl (· = d)) (twoChainSystem 1 2) d sl e.flow.deadline
        ∧ FlowFinalizableAt h z0 hl (fun _ b => b) (importWorld sl (· = d)) (twoChainSystem 1 2)
            (honestAccess h z0 hl (twoChainSystem 1 2))
            (honestSettlementAccess (importWorld sl (· = d))) d sl e.flow
        ∧ ¬ PinnedGateBreak h z0 hl (fun _ b => b) (twoChainSystem 1 2)
            (honestAccess h z0 hl (twoChainSystem 1 2)) e.flow e.evidence
        ∧ ¬ FlowIdClash (honestFlowHash (mixedFlow 0 1 2)) e.flow e.flow := by
  let e : Contracts.FlowBinding.ExecCall :=
    ⟨mixedFlow 0 1 2, imtEvidence (twoChainEvidence h z0 hl sl), ⟨0, 1⟩⟩
  have hver : e.Verified h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
      (twoChainSystem 1 2) :=
    executed_at_projects (twoChain_executed_at h z0 hl (sl := sl) (imp := (· = d)) rfl)
  have hfin := twoChain_flow_finalizable_at h z0 hl (sl := sl) (imp := (· = d)) rfl
  refine ⟨[.execute e], e, twoChain_wf, honestAccess_dataAvailable h z0 hl _,
    honest_settlement_access_available _,
    Contracts.FlowBinding.RunLog.execute e Contracts.FlowBinding.RunLog.refl hver,
    List.mem_singleton_self _, rfl, rfl, importWorld_ready rfl _ (fun _ _ hn => hn) (Nat.zero_le _),
    hfin, ?_, fun hcl => hcl.1 rfl⟩
  rintro ⟨leg, hf, _⟩
  exact first_stranded_leg_iff_not_finalizable.1 ⟨leg, hf⟩ (flow_finalizable_at_imp_by hfin)

end Contracts.RootImport

/-! ## Certificates -/

namespace Contracts.RootImport

theorem ExecutedAtProjects : Properties.ExecutedAtProjects := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ hex
  exact executed_at_projects hex

theorem AcceptedAtShape : Properties.AcceptedAtShape := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ hacc
  exact accepted_at_shape hacc

theorem FinalizableAtImpliesBy : Properties.FinalizableAtImpliesBy := by
  intro _ _ _ _ _ _ _ _ _ _ _ hf
  exact flow_finalizable_at_imp_by hf

theorem ReadyFinalizableAtIffBy : Properties.ReadyFinalizableAtIffBy := by
  intro _ _ _ _ _ _ _ _ hSA _ _ _ hl1 hI
  exact ready_finalizable_at_iff_by hSA hl1 hI

theorem HonestSettlementAccessAvailable : Properties.HonestSettlementAccessAvailable :=
  honest_settlement_access_available

theorem ImportAvailableOfPostDeadlineImport : Properties.ImportAvailableOfPostDeadlineImport := by
  intro _ _ _ _ _ _ himp hD hagg
  exact import_available_of_post_deadline_import himp hD hagg

theorem FinalizableAtPersistsAsImportsGrow : Properties.FinalizableAtPersistsAsImportsGrow := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ hg
  exact finalizable_at_persists_as_imports_grow hg

theorem MemberIsFinalizableAt : Properties.MemberIsFinalizableAt := by
  intro _ _ _ _ _ _ hS _ hDA _ hSA _ _ _ _ _ hon himp hmem
  exact member_is_finalizable_at hS hDA hSA hon himp hmem

theorem ExecutedImpliesAllFinalizableAtOrBreak : Properties.ExecutedImpliesAllFinalizableAtOrBreak := by
  intro _ _ _ _ _ _ _ hS _ hDA _ hSA _ _ _ hI _ _ hex other hother
  exact executed_implies_all_finalizable_at_or_break hS hDA hSA hI hex other hother

theorem ExecutedAtImpliesAllFinalizableAtOrBreak :
    Properties.ExecutedAtImpliesAllFinalizableAtOrBreak := by
  intro _ _ _ _ _ _ _ hS _ hDA _ hSA _ _ _ _ _ _ hex hl1 hI
  exact executed_at_implies_all_finalizable_at_or_break hS hDA hSA hex hl1 hI

theorem NoneOrAllAtOrBreak : Properties.NoneOrAllAtOrBreak := by
  intro _ _ _ _ _ _ _ hS _ hDA _ hSA _ _ _ hl1 hI ev
  exact none_or_all_at_or_break hS hDA hSA hl1 hI ev

theorem FirstStrandedLegAtUnique : Properties.FirstStrandedLegAtUnique := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂
  exact first_stranded_leg_at_unique h₁ h₂

theorem ReadyFirstStrandedLegAtIff : Properties.ReadyFirstStrandedLegAtIff := by
  intro _ _ _ _ _ _ _ _ hSA _ _ _ hI leg
  exact ready_first_stranded_leg_at_iff hSA hI leg

theorem NoneOrAllAtOrBreakPinned : Properties.NoneOrAllAtOrBreakPinned := by
  intro _ _ _ _ _ _ _ hS _ hDA _ hSA _ _ _ hl1 hI ev
  exact none_or_all_at_or_break_pinned hS hDA hSA hl1 hI ev

theorem ExecutedImpliesFinalityPersistsAtOrBreak :
    Properties.ExecutedImpliesFinalityPersistsAtOrBreak := by
  intro _ _ _ _ _ _ _ hS _ hDA _ hSA _ _ _ _ _ hex other hother
  exact executed_implies_finality_persists_at_or_break hS hDA hSA hex other hother

theorem NoneOrAllAtOrBreakPinnedFromRuns : Properties.NoneOrAllAtOrBreakPinnedFromRuns := by
  intro _ _ _ _ _ _ _ hW _ hDA _ _ hSA _ _ _ hl1 hI ev
  exact none_or_all_at_or_break_pinned_from_runs hW hDA hSA hl1 hI ev

theorem ExecutedImpliesRealFlowFinalizableAtOrLoggedClash :
    Properties.ExecutedImpliesRealFlowFinalizableAtOrLoggedClash := by
  intro _ _ _ _ _ _ hS _ hDA _ _ hSA _ _ _ hrun _ he _ hc hid _ _ hl1 hI
  exact executed_implies_real_flow_finalizable_at_or_logged_clash hS hDA hSA hrun he hc hid hl1 hI

theorem WithoutImportFlowSitsHalfExecuted : Properties.WithoutImportFlowSitsHalfExecuted :=
  without_import_flow_sits_half_executed

theorem WithoutImportCrossDestinationFails : Properties.WithoutImportCrossDestinationFails :=
  without_import_cross_destination_fails

theorem ImportAloneRestoresFinalizability : Properties.ImportAloneRestoresFinalizability :=
  import_alone_restores_finalizability

theorem WithoutSettlementDataLegIsStuck : Properties.WithoutSettlementDataLegIsStuck :=
  without_settlement_data_leg_is_stuck

theorem ExecutedAtOrBreakSatisfiable : Properties.ExecutedAtOrBreakSatisfiable :=
  executed_at_or_break_satisfiable

theorem NoneOrAllAtOrBreakPinnedStrandedNotTautology :
    Properties.NoneOrAllAtOrBreakPinnedStrandedNotTautology :=
  none_or_all_at_or_break_pinned_stranded_not_tautology

theorem PinnedGateBreakAtFires : Properties.PinnedGateBreakAtFires := pinned_gate_break_at_fires

theorem NoneOrAllAtOrBreakPinnedFromRunsStranded :
    Properties.NoneOrAllAtOrBreakPinnedFromRunsStranded :=
  none_or_all_at_or_break_pinned_from_runs_stranded

theorem ExecutedImpliesRealFlowFinalizableAtOrLoggedClashWitness :
    Properties.ExecutedImpliesRealFlowFinalizableAtOrLoggedClashWitness :=
  executed_implies_real_flow_finalizable_at_or_logged_clash_witness

end Contracts.RootImport
