import EraSpec.Protocol.L1WithdrawalProvenance.Properties.Provenance
import EraSpec.Contracts.L1InteropHandler.Proofs.WithdrawalGate
import EraSpec.Contracts.L1Messenger.Proofs.SenderKeying
import Mathlib.Tactic

/-!
# Proofs: L1 withdrawal provenance, from the L1 gate to the modelled source chains

A verification's queried message log is in its chain's output (`InclusionSoundOn`) and is center-keyed
(the handler checked the sender), so by `L1Messenger` `CenterKeyedLogsAreItsWithdrawals`, applied to the
verified chain's run (`ChainsRunTheModelOn`, `HooksAsDocumentedOn`), it is the log of one of the center's
dispatches, whose bundle has `WithdrawalShape` (the guard of the model's `withdrawal` step). The two logs
carry the keccak of the queried and the sent message: equal messages give the dispatched bundle (by the
decoder round trip, `DispatchRoundTripOn`), different ones are a named collision. A delivery is
`ProvenBy` a verification of its own bytes or collides with verified bytes (`L1InteropHandler`
`DeliveredCallIsProvenOrKeccakClash`); the dispatched bundle's shape then fixes its index, sender and
pause flag through `DeliveriesAreCheckedRouterCalls`. The witnesses are evaluated by `decide`.
-/

namespace Contracts.L1WithdrawalProvenance

open Contracts.L1WithdrawalGate
open Contracts.L1MessengerKeying (HookSem HooksAsDocumented ChainParams L2State WithdrawalShape
  CenterKeyed dispatchLog messageLog wGatedHooks wUngatedHooks wS₄ wS₄_reach
  wGatedHooks_documented CenterKeyedLogsAreItsWithdrawals)

theorem ProvenBundlesAreDispatchedOrCollide : Properties.ProvenBundlesAreDispatchedOrCollide := by
  intro P Q H runs s txs hrun hH hrt hinc v hv
  obtain ⟨hdec, _, _, hsender, hdata⟩ := VerificationsAreChecked P s txs v hv
  obtain ⟨_, hreach⟩ := hrun v hv
  obtain ⟨hfilt, hshape⟩ := CenterKeyedLogsAreItsWithdrawals P.codec (Q v.proof.chainId)
    (H v.proof.chainId) (runs v.proof.chainId) (hH v hv) hreach
  have hck : CenterKeyed (msgToLog P.codec v.query) := ⟨rfl, by simp [msgToLog, hsender]⟩
  have hin : msgToLog P.codec v.query ∈
      (runs v.proof.chainId).out.filter (fun L => decide (CenterKeyed L)) :=
    List.mem_filter.2 ⟨hinc v hv, by simpa using hck⟩
  rw [hfilt] at hin
  obtain ⟨w, hw, hlog⟩ := List.mem_map.1 hin
  have hval : P.codec.keccak (bundleIdentifier :: P.codec.enc w.bundle) =
      P.codec.keccak (bundleIdentifier :: v.bytes) := by
    have := congrArg L2Log.value hlog
    simpa [dispatchLog, messageLog, msgToLog, hdata] using this
  by_cases heq : v.bytes = P.codec.enc w.bundle
  · left
    refine ⟨w, hw, heq, ?_, hshape w hw⟩
    rw [heq, hrt v hv w hw] at hdec
    exact (Option.some.inj hdec).symm
  · right
    exact ⟨w, hw, fun h => heq (List.cons.inj h).2, hval.symm⟩

theorem DeliveredWithdrawalWasDispatchedOrCollision :
    Properties.DeliveredWithdrawalWasDispatchedOrCollision := by
  intro P Q H runs txs hrun hH hrt hinc d hd
  rcases DeliveredCallIsProvenOrKeccakClash P txs d hd with ⟨v, hv, hp⟩ | hc
  · obtain ⟨hvb, _, _, hchain, _, _, _, _⟩ := hp
    rcases ProvenBundlesAreDispatchedOrCollide P Q H runs init txs hrun hH hrt hinc v hv with
      ⟨w, hw, hbytes, _, hshape⟩ | hm
    · left
      obtain ⟨_, htarget, hvalue, b, c, hdec, _, hc, _, _, hfrom, _, _, hsingle⟩ :=
        DeliveriesAreCheckedRouterCalls P init txs d hd
      have hb : b = w.bundle := by
        rw [← hvb, hbytes, hrt v hv w hw] at hdec
        exact (Option.some.inj hdec).symm
      subst hb
      obtain ⟨_, _, _, _, c0, hcalls, _, _, hfrom0, _, _⟩ := hshape
      have hlen : w.bundle.calls.length = 1 := by rw [hcalls]; rfl
      obtain ⟨hidx, hpaused⟩ := hsingle hlen
      have hcc0 : c = c0 := by
        rw [hcalls, hidx] at hc
        simpa using hc.symm
      refine ⟨w, hchain ▸ hw, by rw [← hvb, hbytes], hlen, hidx, ?_, hvalue, htarget, hpaused⟩
      rw [hfrom, hcc0, hfrom0]
    · exact Or.inr (Or.inr ⟨v, hv, hm⟩)
  · exact Or.inr (Or.inl hc)

lemma wRuns_reach (H : HookSem) (c : ℕ) :
    Contracts.L1MessengerKeying.Reach wCodec (wQ c) H L2State.init (wRuns H c) := by
  unfold wRuns
  split_ifs with hc
  · subst hc
    exact wS₄_reach H (by decide) (by decide)
  · exact .refl _

lemma wRuns_roundTrip (H : HookSem) (c : ℕ) :
    ∀ w ∈ (wRuns H c).dispatched, wCodec.decode (wCodec.enc w.bundle) = some w.bundle := by
  intro w hw
  unfold wRuns at hw
  split_ifs at hw with hc
  · simp only [wS₄, Contracts.L1MessengerKeying.wS₃, Contracts.L1MessengerKeying.wS₂,
      Contracts.L1MessengerKeying.wS₁, L2State.init, List.nil_append, List.mem_singleton] at hw
    subst hw
    decide
  · simp [L2State.init] at hw

theorem ProvenanceEndToEndWitness : Properties.ProvenanceEndToEndWitness := by
  refine ⟨?_, ?_, fun v _ => ⟨rfl, wRuns_reach _ _⟩, fun _ _ => wGatedHooks_documented,
    fun v _ => wRuns_roundTrip _ _, ?_, ?_, ?_⟩ <;> decide

/-- The one verification of the countermodel's L1 run: `[2]`, decoded to `wTwo`, with `wProofTx2`. -/
lemma wVerifyTx2_verification :
    (⟨[2], wTwo, wProofTx2⟩ : Verification) ∈
      verifications (submitAll wParams init [wVerifyTx2, wUnbundleTwo]).2 := by
  decide

theorem UngatedHookDeliversUndispatchedCalls : Properties.UngatedHookDeliversUndispatchedCalls := by
  refine ⟨fun v _ => ⟨rfl, wRuns_reach _ _⟩, fun v _ => wRuns_roundTrip _ _, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · intro h
    have hg := (h _ wVerifyTx2_verification).messengerCallerGated
      Contracts.L1MessengerKeying.wForger 0 (l2InteropCenterAddr, []) (by decide)
    simp [wUngatedHooks] at hg
  · decide
  · decide
  · decide

end Contracts.L1WithdrawalProvenance
