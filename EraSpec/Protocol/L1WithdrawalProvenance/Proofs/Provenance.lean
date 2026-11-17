import EraSpec.Protocol.L1WithdrawalProvenance.Properties.Provenance
import EraSpec.Contracts.L1InteropHandler.Proofs.WithdrawalGate
import EraSpec.Contracts.L1Messenger.Proofs.SenderKeying
import Mathlib.Tactic

/-!
# Proofs: L1 withdrawal provenance, from the gate to the source chains' code

A verification's queried message log is in its chain's output (`InclusionSoundOn`) and is center-keyed
(the handler checked the sender), so by `L1Messenger` `CenterKeyedLogsAreItsWithdrawals` it is the log
of one of the center's dispatches. The two logs carry the keccak of the queried and the sent message:
equal messages give the dispatched bundle (by the decoder round trip), different ones are a named
collision. A delivery is `ProvenBy` a verification of its own bytes or collides with verified bytes
(`L1InteropHandler` `DeliveredCallIsProvenOrKeccakClash`); the dispatched bundle's shape then fixes its
index, sender and pause flag through `DeliveriesAreCheckedRouterCalls`. The witnesses are evaluated by
`decide`.
-/

namespace Contracts.L1WithdrawalProvenance

open Contracts.L1WithdrawalGate
open Contracts.L1MessengerKeying (HookSem HooksAsDocumented ChainParams L2State WithdrawalShape
  CenterKeyed dispatchLog messageLog wGatedHooks wUngatedHooks wS₄ wS₄_reach
  wGatedHooks_documented CenterKeyedLogsAreItsWithdrawals)

theorem ProvenBundlesAreDispatchedOrCollide : Properties.ProvenBundlesAreDispatchedOrCollide := by
  intro P Q H runs s txs hrun hH hrt hinc v hv
  obtain ⟨hdec, _, _, hsender, hdata⟩ := VerificationsAreChecked P s txs v hv
  obtain ⟨_, hreach⟩ := hrun v.proof.chainId
  obtain ⟨hfilt, hshape⟩ := CenterKeyedLogsAreItsWithdrawals P.codec (Q v.proof.chainId)
    (H v.proof.chainId) (runs v.proof.chainId) (hH _) hreach
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
    rw [heq, hrt _ w hw] at hdec
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
        rw [← hvb, hbytes, hrt _ w hw] at hdec
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

lemma wRuns_roundTrip (H : HookSem) : RoundTripOn wCodec (wRuns H) := by
  intro c w hw
  unfold wRuns at hw
  split_ifs at hw with hc
  · simp only [wS₄, Contracts.L1MessengerKeying.wS₃, Contracts.L1MessengerKeying.wS₂,
      Contracts.L1MessengerKeying.wS₁, L2State.init, List.nil_append, List.mem_singleton] at hw
    subst hw
    decide
  · simp [L2State.init] at hw

theorem ProvenanceEndToEndWitness : Properties.ProvenanceEndToEndWitness := by
  refine ⟨fun c => ⟨rfl, wRuns_reach _ c⟩, fun _ => wGatedHooks_documented,
    wRuns_roundTrip _, ?_, ?_, ?_⟩ <;> decide

theorem UngatedHookDeliversUndispatchedCalls : Properties.UngatedHookDeliversUndispatchedCalls := by
  refine ⟨fun c => ⟨rfl, wRuns_reach _ c⟩, wRuns_roundTrip _, ?_, ?_, ?_, ?_⟩ <;> decide

end Contracts.L1WithdrawalProvenance
