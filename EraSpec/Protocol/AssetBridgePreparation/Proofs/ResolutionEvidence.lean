import EraSpec.Protocol.AssetBridgePreparation.Properties.ResolutionEvidence
import EraSpec.Protocol.AssetBridgePreparation.Proofs.Resolution
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund
import EraSpec.Protocol.MultichainGate.Proofs.Model

/-!
# Proofs: the two-chain trace driven by the protocol's own evidence

The soundness of each gate is an existing protocol result
(`Contracts.Refund.ExecutedObligationNeverRefundedOrBreak`,
`Contracts.Protocol.chains_no_double_spend`); the two-chain results then follow from
`Proofs/Resolution.lean`. The witnesses reuse the generic runs `TwoChainExample.doublePay_run`
and `TwoChainExample.split_run` with the existing protocol witnesses as evidence.
-/

namespace AssetBridgePreparation

open Contracts MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Refund
open Contracts.AtomicFlowManager TwoChainExample

/-! ## Atomic interop -/

theorem InteropGateSoundOrBreak : Properties.InteropGateSoundOrBreak := by
  intro h z0 hl cv fh S route hS i ev w hf hr
  rcases ExecutedObligationNeverRefundedOrBreak h z0 hl cv fh S hS (route i).1 ev (route i).2 hf
      w.1 w.2 hr.1 with hn | hb
  · exact absurd hr.2 hn
  · exact hb

/-- The interop gate is sound up to the break that also records both passing witnesses. -/
private theorem interop_soundOrBreak_witnessed {A B : Type} {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} {route : ResolutionLegRoute}
    {E : TwoChainEnv A B GateEvidence InteropRefundWitness}
    (hE : E.gate = interopResolutionGate h z0 hl cv fh S route) (hS : Wf S) :
    E.gate.SoundOrBreak fun i ev w =>
      E.gate.finalize i ev ∧ E.gate.recover i w ∧
        interopResolutionBreak h z0 hl fh S route i ev w := by
  intro i ev w hfin hrec
  refine ⟨hfin, hrec, ?_⟩
  rw [hE] at hfin hrec
  exact InteropGateSoundOrBreak h z0 hl cv fh S route hS i ev w hfin hrec

theorem InteropTwoChainConservedOrBreak : Properties.InteropTwoChainConservedOrBreak := by
  intro A B h z0 hl cv fh S route E s t ls hE hS hw hf hrun
  rcases TwoChainConservedOrBreak A B _ _ E _ s t ls (interop_soundOrBreak_witnessed hE hS) hw hf
      hrun with hc | ⟨i, ev, ⟨Ms, log⟩, hmd, hmr, hfin, hrec, hbrk⟩
  · exact Or.inl hc
  · rw [hE] at hfin hrec
    exact Or.inr ⟨i, ev, Ms, log, hmd, hmr, hfin, hrec.1, hbrk⟩

theorem InteropTwoChainResolvesOnceOrBreak : Properties.InteropTwoChainResolvesOnceOrBreak := by
  intro A B h z0 hl cv fh S route E s t ls hE hS hf hrun i
  rcases TwoChainResolvesOnceOrBreak A B _ _ E _ s t ls (interop_soundOrBreak_witnessed hE hS) hf
      hrun i with hc | ⟨ev, ⟨Ms, log⟩, hmd, hmr, _, _, hbrk⟩
  · exact Or.inl hc
  · exact Or.inr ⟨ev, Ms, log, hmd, hmr, hbrk⟩

/-- Entry `0` on the executed one-leg flow, every other entry on the refunded leg. -/
def interopResolutionWitnessRoute : ResolutionLegRoute :=
  fun i => if i = 0 then (subsetFlow 0 1, ⟨0, 1⟩) else (mixedFlow 1 1 2, ⟨1, 2⟩)

theorem InteropTwoChainSatisfiable : Properties.InteropTwoChainSatisfiable := by
  intro h z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  let ev : GateEvidence := fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1)
  let G := interopResolutionGate h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1)
    interopResolutionWitnessRoute
  have hf : G.finalize 0 ev :=
    (subsetFlow_executes h z0 hl lengthFlowHash lengthFlowHash_checks_subset).1
  have hr : G.recover 1 (twoFlowMs, [twoFlowCall h z0 hl]) := by
    refine ⟨twoFlow_run h z0 hl, ?_⟩
    show 2 ≤ rank (stateOf (setAt twoFlowM1 1 ((twoFlowM1 1).set 1 2 .Revertable)) ⟨1, 2, 1⟩)
    rw [stateOf_setAt_self]
    simp [rank]
  obtain ⟨pre, post, _, _, _, _, hrun, hd, hrf, _, _, _, hval⟩ :=
    split_run G ev (twoFlowMs, [twoFlowCall h z0 hl]) hf hr
  refine ⟨_, _, _, _, env G, start, post, _, ev, twoFlowMs, [twoFlowCall h z0 hl], rfl,
    mixedSystem_wf h1, start_wellFormed, start_fresh, hrun, by simp, by simp,
    List.cons_ne_nil _ _, hd, hrf, ?_, hval⟩
  show ¬ RefundBreak h z0 hl lengthFlowHash (mixedSystem 1) (subsetFlow 0 1) ev
    (obligationOf (subsetFlow 0 1) ⟨0, 1⟩) [twoFlowCall h z0 hl]
  have hneq : obligationOf (twoFlowCall h z0 hl).flow (twoFlowCall h z0 hl).leg
      ≠ obligationOf (subsetFlow 0 1) ⟨0, 1⟩ := by
    intro he
    have hid : (1 : UInt256) = 0 := congrArg Obligation.flowId he
    exact absurd hid (by decide)
  intro hb
  cases hb with
  | flowIdClash a ha hobl _ =>
    rw [List.mem_singleton] at ha
    subst ha
    exact hneq hobl
  | inclusion a ha hobl _ _ =>
    rw [List.mem_singleton] at ha
    subst ha
    exact hneq hobl
  | absence a ha hobl _ _ =>
    rw [List.mem_singleton] at ha
    subst ha
    exact hneq hobl

theorem InteropTwoChainPaddingDoublePayLocated :
    Properties.InteropTwoChainPaddingDoublePayLocated := by
  intro h hl a b ha hab
  obtain ⟨cv, fh, F, ev, leg, Ms, log, hS, hexec, hreach, hrefunded, hbrk, hcalls⟩ :=
    PaddingRefundOfExecutedObligationLocatesAbsenceBreak h hl a b ha hab
  let G := interopResolutionGate h (hl ⟨0, 0, 0⟩) hl cv fh (paddedSystem a b) fun _ => (F, leg)
  obtain ⟨t, hrun, hd, hr, hamt, hval⟩ :=
    doublePay_run G ev (Ms, log) hexec ⟨hreach, hrefunded⟩
  exact ⟨cv, fh, fun _ => (F, leg), env G, start, t, _, ev, Ms, log, rfl, hS, start_wellFormed,
    start_fresh, hrun, by simp, by simp, hd, hr, by rw [hamt]; decide, hval, hbrk, hcalls⟩

/-! ## Multichain refund gate -/

theorem MultichainGateSound : Properties.MultichainGateSound := by
  intro T route hV i _ _ hboth
  exact Contracts.Protocol.chains_no_double_spend hV hboth

theorem MultichainTwoChainConserved : Properties.MultichainTwoChainConserved := by
  intro A B T route E s t ls hE hV hw hf hrun
  have hs : E.gate.Sound := by
    rw [hE]
    exact MultichainGateSound T route hV
  exact ⟨(TwoChainConservation A B Unit Unit E s t ls hs hw hf hrun).1,
    TwoChainResolvesOnce A B Unit Unit E s t ls hs hf hrun⟩

/-- Entry `0` on chain `0` (which inserted `v`), every other entry on chain `1` (which did
not). -/
def multichainResolutionWitnessRoute (v : UInt256) : ResolutionValueRoute :=
  fun i => if i = 0 then (0, v) else (1, v)

theorem MultichainTwoChainSatisfiable : Properties.MultichainTwoChainSatisfiable := by
  intro v hv
  obtain ⟨hV, hdel, _, _, hbound⟩ :=
    Contracts.Protocol.chains_unbound_gate_refunds_delivered_leg hv
  let G := multichainResolutionGate (Contracts.Protocol.attackChains v)
    (multichainResolutionWitnessRoute v)
  obtain ⟨pre, post, _, _, _, _, hrun, hd, hr, _⟩ := split_run G () () hdel hbound
  exact ⟨multichainResolutionWitnessRoute v, env G, start, post, _, rfl, hV, start_wellFormed,
    start_fresh, hrun, hd, hr⟩

theorem MultichainUnboundGateDoublePays : Properties.MultichainUnboundGateDoublePays := by
  intro v hv
  obtain ⟨hV, hdel, hunb, _, _⟩ :=
    Contracts.Protocol.chains_unbound_gate_refunds_delivered_leg hv
  let G := unboundMultichainResolutionGate (Contracts.Protocol.attackChains v) fun _ => (0, v)
  obtain ⟨t, hrun, hd, hr, hamt, hval⟩ := doublePay_run G () () hdel hunb
  exact ⟨env G, start, t, _, rfl, hV, start_wellFormed, start_fresh, hrun, hd, hr,
    by rw [hamt]; decide, hval⟩

end AssetBridgePreparation
