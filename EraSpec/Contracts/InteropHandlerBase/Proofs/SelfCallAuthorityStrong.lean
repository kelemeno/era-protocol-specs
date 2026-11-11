import EraSpec.Contracts.InteropHandlerBase.Properties.SelfCallAuthorityStrong
import Mathlib.Tactic

/-!
# Proofs: a self-call relays the original sender's authority, exactly when every branch checks

Soundness is a case split on the call. A direct call's gate has a false self-call disjunct, so
its attribute check is the conclusion. A relayed call's gate passes by its self-call disjunct and
proves nothing; the authority comes from the branch's check, against the parsed pair, which the
round trip turns into the original sender — or, for the ungated `verifyBundle`, from the empty
attribute. Conversely an unchecked gated branch admits a relayed call from `(1, 9)` for a bundle
naming `(1, 7)`.
-/

namespace AttackVectors.SelfCallAuthority

/-- A gated entry point's attribute, when both attributes name `(1, 7)`. -/
lemma gateAttr_wAttrs7 {e : Gated} (he : e.isGated = true) : gateAttr e wAttrs7 = some (1, 7) := by
  cases e <;> simp_all [Gated.isGated, gateAttr, wAttrs7]

/-- `(1, 7)` does not allow `(1, 9)`. -/
lemma not_allows_7_9 : ¬ attrAllows (some (1, 7)) 1 1 9 := by
  rintro ⟨-, h, -⟩
  exact absurd h (by decide)

theorem SelfCallRelaySoundIffEveryGatedBranchChecked :
    Properties.SelfCallRelaySoundIffEveryGatedBranchChecked := by
  intro dispatch
  constructor
  · intro hsound br hbr hg
    by_contra hck
    have hck' : br.checked = false := by simpa using hck
    have hadm : Admitted wHandler dispatch wAttrs7 (.relayed 1 9 br) :=
      ⟨hbr, fun h => absurd h (by rw [hck']; decide), Or.inl rfl⟩
    have hauth := hsound _ wHandler wAttrs7 (.relayed 1 9 br) rfl hadm
    simp only [Authorized, GateCall.entry, GateCall.principal, gateAttr_wAttrs7 hg] at hauth
    exact not_allows_7_9 hauth
  · intro hchk Sender H A c hrt hadm
    cases c with
    | direct e caller =>
      obtain ⟨hne, hg⟩ := hadm
      rcases hg with hself | hallow
      · exact absurd hself hne
      · exact hallow
    | relayed src fromAddr br =>
      obtain ⟨hmem, hck, -⟩ := hadm
      have hrt' : H.parse (H.fmt src fromAddr) = (src, fromAddr) := hrt
      cases hg : br.target.isGated with
      | true =>
        have hallow := hck (hchk br hmem hg)
        rw [hrt'] at hallow
        exact hallow
      | false =>
        have hv : br.target = .verifyBundle := by
          cases ht : br.target <;> simp_all [Gated.isGated]
        simp only [Authorized, GateCall.entry, hv, gateAttr, attrAllows]

theorem DeployedSelfCallRelaysOriginalSenderAuthority :
    Properties.DeployedSelfCallRelaysOriginalSenderAuthority := by
  have hchk : ∀ br ∈ deployedDispatch, br.target.isGated = true → br.checked = true := by
    decide
  have hsound := (SelfCallRelaySoundIffEveryGatedBranchChecked deployedDispatch).2 hchk
  refine ⟨hsound, fun Sender H A src fromAddr br ch addr hrt hadm hattr => ?_⟩
  have hauth := hsound Sender H A (.relayed src fromAddr br) hrt hadm
  simp only [Authorized, GateCall.entry, GateCall.principal, hattr, attrAllows] at hauth
  exact ⟨hauth.2.1, hauth.1⟩

theorem UncheckedAtomicBranchWidensAuthority :
    Properties.UncheckedAtomicBranchWidensAuthority := by
  refine ⟨rfl, ⟨List.mem_cons_self, fun h => absurd h (by decide), Or.inl rfl⟩, ?_, ?_⟩
  · simp only [Authorized, GateCall.entry, GateCall.principal, gateAttr, wAttrs7]
    exact not_allows_7_9
  · intro h
    exact absurd (h _ List.mem_cons_self rfl) (by decide)

theorem MisparsedSenderBreaksTheRelay : Properties.MisparsedSenderBreaksTheRelay := by
  refine ⟨fun h => ?_, ⟨by simp [deployedDispatch], fun _ => ?_, Or.inl rfl⟩, ?_⟩
  · have := congrArg Prod.snd h
    exact absurd this (by decide)
  · simp [wMisparsingHandler, gateAttr, wAttrs7, attrAllows]
  · simp only [Authorized, GateCall.entry, GateCall.principal, gateAttr, wAttrs7]
    exact not_allows_7_9

theorem SelfCallRelayWitness : Properties.SelfCallRelayWitness := by
  refine ⟨rfl, ⟨by simp [deployedDispatch], fun _ => ?_, Or.inl rfl⟩,
    ⟨by simp [deployedDispatch], fun _ => ?_, Or.inl rfl⟩,
    ⟨by simp [deployedDispatch], fun h => absurd h (by decide), Or.inl rfl⟩,
    ⟨by simp [wHandler], Or.inr ?_⟩, ?_, Or.inl rfl, ?_, ?_, ?_⟩
  · simp [wHandler, gateAttr, wAttrs7, attrAllows]
  · simp [wHandler, gateAttr, wAttrs7, attrAllows]
  · simp [wHandler, gateAttr, wAttrs7, attrAllows]
  · rintro ⟨hne, -⟩
    exact hne rfl
  · rintro ⟨-, h, -⟩
    exact absurd h (by decide)
  · rintro ⟨-, h, -⟩
    exact absurd h (by decide)
  · rintro ⟨-, hck, -⟩
    have h := hck rfl
    simp only [wHandler, gateAttr, wAttrs42, attrAllows, id] at h
    exact absurd h.2.1 (by decide)

end AttackVectors.SelfCallAuthority
