import EraSpec.Contracts.ChainAssetHandler.Properties.Pause
import EraSpec.Contracts.ChainAssetHandler.Proofs.Migration

/-!
# Proofs: the migration pauses

One-step inversions of `Step`, then inductions over `Run` for the run-level statements.
-/

namespace Contracts.ChainAssetHandler

theorem PauseBlocksMigrationSteps : Properties.PauseBlocksMigrationSteps := by
  intro W s s' l h x hst hmv
  cases hst with
  | burn _ hp he heco hctm =>
    obtain ⟨rfl, rfl⟩ := hmv; exact ⟨he, hp, heco, hctm⟩
  | mintFresh _ _ _ _ hp he heco hctm =>
    obtain ⟨rfl, rfl⟩ := hmv; exact ⟨he, hp, heco, hctm⟩
  | mintReturn _ _ _ _ hp he heco hctm =>
    obtain ⟨rfl, rfl⟩ := hmv; exact ⟨he, hp, heco, hctm⟩
  | _ => simp [Label.movesUnder] at hmv

theorem PausedCTMChainsDoNotMove : Properties.PausedCTMChainsDoNotMove := by
  intro W s s'
  refine ⟨fun h c t a orig hst hrt => ?_, fun h i c a hst => ?_⟩
  · cases hst with
    | burn _ _ _ _ hctm _ ha =>
      rw [ha, hrt] at hctm; exact hctm
  · cases hst with
    | mintFresh _ _ _ _ _ _ _ hctm => simpa [mintPost, upd2_apply] using hctm
    | mintReturn _ _ _ _ _ _ _ hctm => simpa [mintPost, upd2_apply] using hctm

/-- A CTM pause stays set across a step that does not unpause it. -/
theorem ctmPaused_stays {W : World} {s s' : Sys} {l : Label} {h : ChainId} {x : Address}
    (hst : Step W s l s') (hp : s.ctmPaused h x = true) (hn : ¬ l.unpausesCTM h x) :
    s'.ctmPaused h x = true := by
  cases hst with
  | @pauseCTM h' x' => simp only [upd2_apply]; split_ifs <;> simp [hp]
  | @unpauseCTM h' x' snd =>
    simp only [upd2_apply]; split_ifs with hq
    · exact absurd (show Label.unpausesCTM h x (.unpauseCTM h' x' snd) from
        ⟨hq.1.symm, hq.2.symm⟩) hn
    · exact hp
  | confirm => cases ‹Bool› <;> exact hp
  | _ => exact hp

/-- The ecosystem pause stays set across a step that does not lift it. -/
theorem ecoPaused_stays {W : World} {s s' : Sys} {l : Label} {h : ChainId}
    (hst : Step W s l s') (hp : s.ecoPaused h = true) (hn : ¬ l.unpausesEcosystem h) :
    s'.ecoPaused h = true := by
  cases hst with
  | @pauseMigration h' => simp only [upd]; split_ifs <;> simp [hp]
  | @unpauseMigration h' =>
    simp only [upd]; split_ifs with hq
    · exact absurd hq.symm (by simpa [Label.unpausesEcosystem] using hn)
    · exact hp
  | confirm => cases ‹Bool› <;> exact hp
  | _ => exact hp

/-- `paused()` stays set across a step that does not unpause. -/
theorem paused_stays {W : World} {s s' : Sys} {l : Label} {h : ChainId}
    (hst : Step W s l s') (hp : s.paused h = true) (hn : ¬ l.unpausesHub h) :
    s'.paused h = true := by
  cases hst with
  | @pause h' => simp only [upd]; split_ifs <;> simp [hp]
  | @unpause h' =>
    simp only [upd]; split_ifs with hq
    · exact absurd hq.symm (by simpa [Label.unpausesHub] using hn)
    · exact hp
  | confirm => cases ‹Bool› <;> exact hp
  | _ => exact hp

/-- A burn or mint on hub `h` needs `paused()` and the ecosystem pause off there. -/
theorem movesOn_blocked {W : World} {s s' : Sys} {l : Label} {h : ChainId}
    (hst : Step W s l s') (hmv : l.movesOn h) : s.paused h = false ∧ s.ecoPaused h = false := by
  cases hst with
  | burn _ hp _ heco => subst hmv; exact ⟨hp, heco⟩
  | mintFresh _ _ _ _ hp _ heco => subst hmv; exact ⟨hp, heco⟩
  | mintReturn _ _ _ _ hp _ heco => subst hmv; exact ⟨hp, heco⟩
  | _ => simp [Label.movesOn] at hmv

theorem PauseHoldsUntilUnpaused : Properties.PauseHoldsUntilUnpaused := by
  intro W s s' ls h hrun
  induction hrun with
  | nil => exact ⟨fun _ _ _ l hl => by simp at hl, fun _ _ l hl => by simp at hl,
      fun _ _ l hl => by simp at hl⟩
  | @cons s0 s1 s2 l ls hst _ ih =>
    refine ⟨fun x hp hn l' hl' hmv => ?_, fun hp hn l' hl' hmv => ?_, fun hp hn l' hl' hmv => ?_⟩
    · rcases List.mem_cons.1 hl' with rfl | hmem
      · have := (PauseBlocksMigrationSteps W _ _ _ h x hst hmv).2.2.2; simp [hp] at this
      · exact (ih.1 x (ctmPaused_stays hst hp (hn l (by simp)))
          (fun l'' h'' => hn l'' (by simp [h'']))) l' hmem hmv
    · rcases List.mem_cons.1 hl' with rfl | hmem
      · have := (movesOn_blocked hst hmv).2; simp [hp] at this
      · exact (ih.2.1 (ecoPaused_stays hst hp (hn l (by simp)))
          (fun l'' h'' => hn l'' (by simp [h'']))) l' hmem hmv
    · rcases List.mem_cons.1 hl' with rfl | hmem
      · have := (movesOn_blocked hst hmv).1; simp [hp] at this
      · exact (ih.2.2 (paused_stays hst hp (hn l (by simp)))
          (fun l'' h'' => hn l'' (by simp [h'']))) l' hmem hmv

/-- A step that changes a CTM pause is that CTM owner's pause or unpause. -/
theorem ctmPaused_change {W : World} {s s' : Sys} {l : Label} {h : ChainId} {x : Address}
    (hst : Step W s l s') (hne : s'.ctmPaused h x ≠ s.ctmPaused h x) :
    W.ctmRegistered h x = true ∧ l.togglesCTMPause h x (W.ctmOwner x) := by
  cases hst with
  | @pauseCTM h' x' snd hreg hsnd =>
    simp only [upd2_apply] at hne
    split_ifs at hne with hq
    · obtain ⟨rfl, rfl⟩ := hq; exact ⟨hreg, rfl, rfl, hsnd⟩
    · exact absurd rfl hne
  | @unpauseCTM h' x' snd hreg hsnd =>
    simp only [upd2_apply] at hne
    split_ifs at hne with hq
    · obtain ⟨rfl, rfl⟩ := hq; exact ⟨hreg, rfl, rfl, hsnd⟩
    · exact absurd rfl hne
  | confirm => cases ‹Bool› <;> exact absurd rfl hne
  | _ => exact absurd rfl hne

/-- A step that changes the ecosystem pause is the owner's pause or unpause. -/
theorem ecoPaused_change {W : World} {s s' : Sys} {l : Label} {h : ChainId}
    (hst : Step W s l s') (hne : s'.ecoPaused h ≠ s.ecoPaused h) :
    l.togglesEcosystemPause h (W.owner h) := by
  cases hst with
  | @pauseMigration h' snd hsnd =>
    simp only [upd] at hne
    split_ifs at hne with hq
    · subst hq; exact ⟨rfl, hsnd⟩
    · exact absurd rfl hne
  | @unpauseMigration h' snd hsnd =>
    simp only [upd] at hne
    split_ifs at hne with hq
    · subst hq; exact ⟨rfl, hsnd⟩
    · exact absurd rfl hne
  | confirm => cases ‹Bool› <;> exact absurd rfl hne
  | _ => exact absurd rfl hne

theorem OnlyOwnersTogglePauses : Properties.OnlyOwnersTogglePauses := by
  intro W s s' ls h hrun
  induction hrun with
  | nil => exact ⟨fun x hne => absurd rfl hne, fun hne => absurd rfl hne⟩
  | @cons s0 s1 s2 l ls hst _ ih =>
    refine ⟨fun x hne => ?_, fun hne => ?_⟩
    · by_cases h1 : s1.ctmPaused h x = s0.ctmPaused h x
      · obtain ⟨hreg, l', hl', ht⟩ := ih.1 x (by rw [h1]; exact hne)
        exact ⟨hreg, l', List.mem_cons_of_mem _ hl', ht⟩
      · obtain ⟨hreg, ht⟩ := ctmPaused_change hst h1
        exact ⟨hreg, l, List.mem_cons_self, ht⟩
    · by_cases h1 : s1.ecoPaused h = s0.ecoPaused h
      · obtain ⟨l', hl', ht⟩ := ih.2 (by rw [h1]; exact hne)
        exact ⟨l', List.mem_cons_of_mem _ hl', ht⟩
      · exact ⟨l, List.mem_cons_self, ecoPaused_change hst h1⟩

theorem RecoveryIgnoresPauses : Properties.RecoveryIgnoresPauses := by
  intro W s s' i c f hst
  cases hst with
  | @confirm _ m _ hm hsrc hf hs hreg hctm hnum haway hdpv =>
    have heq : pauseAll (confirmPost W s i m f) =
        confirmPost { W with migrationsEnabled := false } (pauseAll s) i m f := by
      cases f <;> rfl
    rw [heq]
    exact Step.confirm hm hsrc hf hs hreg hctm hnum haway hdpv

end Contracts.ChainAssetHandler
