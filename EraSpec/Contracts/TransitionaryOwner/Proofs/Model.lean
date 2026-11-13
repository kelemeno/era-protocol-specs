import EraSpec.Contracts.TransitionaryOwner.Properties.Model

/-!
# Proofs: the transitionary owner hands ownership on, once per nomination

One-step results are case analyses of `Step`; run-level results are inductions on `Reach`.
-/

namespace Contracts.TransitionaryOwner

theorem ClaimHandsToGovernance : Properties.ClaimHandsToGovernance := by
  intro K s s' c h
  cases h with
  | claim _ hp => exact ⟨hp, rfl, rfl, rfl⟩

theorem NeverParkedWithoutGovernanceNominee :
    Properties.NeverParkedWithoutGovernanceNominee := by
  intro K s₀ s hTO hG h0 hR
  induction hR with
  | refl => exact h0
  | step _ hs ih =>
    cases hs with
    | transfer _ hc ho => intro h; exact absurd (ho.trans h) hc
    | accept _ hc _ => intro h; exact absurd h hc
    | renounce _ _ _ => intro h; exact absurd h.symm hTO
    | claim _ _ => intro _; rfl

theorem ClaimsBoundedByNominations : Properties.ClaimsBoundedByNominations := by
  intro K o s hTO hG hR
  induction hR with
  | refl => simp [fresh, Ne.symm hTO]
  | step _ hs ih =>
    cases hs with
    | @transfer caller newOwner _ _ _ =>
      by_cases hn : newOwner = K.TO
      · simp only [hn, ite_true]
        split_ifs at ih <;> omega
      · simp only [hn, ite_false]
        split_ifs at ih <;> omega
    | accept _ hc hp =>
      simp only [hp, hc, ite_false] at ih
      simp only [Ne.symm hTO, ite_false]; omega
    | renounce _ _ _ =>
      simp only [Ne.symm hTO, ite_false]
      split_ifs at ih <;> omega
    | claim _ hp =>
      simp only [hp, ite_true] at ih
      simp only [hG, ite_false]; omega

theorem SecondClaimFails : Properties.SecondClaimFails := by
  intro K s s' s'' c c' hG h1 h2
  cases h1
  cases h2 with
  | claim _ hp => exact hG hp

theorem ZeroGovernanceStrandsOwnership : Properties.ZeroGovernanceStrandsOwnership := by
  intro K s s' s'' c hG hTO h1 hR
  cases h1
  induction hR with
  | refl => exact ⟨rfl, hG⟩
  | step _ hs ih =>
    obtain ⟨ho, hp⟩ := ih
    cases hs with
    | transfer _ hc hco => exact absurd (hco.trans ho) hc
    | accept hc0 _ hpc => exact absurd (hpc.symm.trans hp) hc0
    | renounce _ hc hco => exact absurd (hco.trans ho) hc
    | claim _ hpt => exact absurd (hpt.symm.trans hp) hTO

theorem UncheckedClaimTakesOwnership : Properties.UncheckedClaimTakesOwnership :=
  ⟨⟨2, 3⟩, 1, _, by decide, by decide, by decide, .claim, rfl, by simp [fresh]⟩

theorem HandoffWitness : Properties.HandoffWitness :=
  ⟨⟨3, 0, 1, 1⟩,
    .step (.step (.step .refl (.transfer (newOwner := 2) (by decide) (by decide) rfl))
      (.claim (caller := 5) (by decide) rfl)) (.accept (caller := 3) (by decide) (by decide) rfl),
    rfl, rfl, rfl, rfl⟩

end Contracts.TransitionaryOwner
