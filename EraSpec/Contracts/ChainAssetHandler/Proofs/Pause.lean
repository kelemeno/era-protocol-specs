import EraSpec.Contracts.ChainAssetHandler.Properties.Pause
import EraSpec.Contracts.ChainAssetHandler.Proofs.Migration

/-!
# Proofs: the migration pauses

One-step inversions of `Step`, then inductions over `Run` for the run-level statements. The
witnesses are concrete runs of `cahWorld` (and `cahWorldMismatched`), checked by evaluation.
-/

namespace Contracts.ChainAssetHandler

theorem PauseBlocksMigrationSteps : Properties.PauseBlocksMigrationSteps := by
  intro W s s' l h x hst hmv
  cases hst with
  | burn hg =>
    obtain ⟨rfl, rfl⟩ := hmv; exact ⟨hg.enabled, hg.notPaused, hg.ecoOff, hg.ctmOff⟩
  | mintFresh hg =>
    obtain ⟨rfl, rfl⟩ := hmv; exact ⟨hg.enabled, hg.notPaused, hg.ecoOff, hg.ctmOff⟩
  | mintReturn hg =>
    obtain ⟨rfl, rfl⟩ := hmv; exact ⟨hg.enabled, hg.notPaused, hg.ecoOff, hg.ctmOff⟩
  | _ => simp [Label.movesUnder] at hmv

theorem PausedCTMChainsDoNotMove : Properties.PausedCTMChainsDoNotMove := by
  intro W s s'
  refine ⟨fun h c t a hst hrt => ?_, fun h i c a hst => ?_⟩
  · obtain ⟨hg, -⟩ := burn_inv hst
    have hoff := hg.ctmOff
    rw [hg.asset, hrt] at hoff
    exact hoff
  · obtain ⟨m, hg, rfl, rfl, hcase⟩ := mint_inv hst
    rcases hcase with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;>
      simpa [mintPost, upd2_apply] using hg.ctmOff

/-- A CTM pause stays set across a step that does not unpause it. -/
theorem ctmPaused_stays {W : World} {s s' : Sys} {l : Label} {h : ChainId} {x : Address}
    (hst : Step W s l s') (hp : s.ctmPaused h x = true) (hn : ¬ l.unpausesCTM h x) :
    s'.ctmPaused h x = true := by
  cases hst with
  | pauseCTM => simp only [upd2_apply]; split_ifs <;> simp [hp]
  | @unpauseCTM h' x' snd _ _ =>
    simp only [upd2_apply]; split_ifs with hq
    · exact absurd (show Label.unpausesCTM h x (.unpauseCTM h' x' snd) from
        ⟨hq.1.symm, hq.2.symm⟩) hn
    · exact hp
  | @confirm i m f _ => cases f <;> exact hp
  | _ => exact hp

/-- The ecosystem pause stays set across a step that does not lift it. -/
theorem ecoPaused_stays {W : World} {s s' : Sys} {l : Label} {h : ChainId}
    (hst : Step W s l s') (hp : s.ecoPaused h = true) (hn : ¬ l.unpausesEcosystem h) :
    s'.ecoPaused h = true := by
  cases hst with
  | pauseMigration => simp only [upd]; split_ifs <;> simp [hp]
  | @unpauseMigration h' snd _ =>
    simp only [upd]; split_ifs with hq
    · exact absurd hq.symm (by simpa [Label.unpausesEcosystem] using hn)
    · exact hp
  | @confirm i m f _ => cases f <;> exact hp
  | _ => exact hp

/-- `paused()` stays set across a step that does not unpause. -/
theorem paused_stays {W : World} {s s' : Sys} {l : Label} {h : ChainId}
    (hst : Step W s l s') (hp : s.paused h = true) (hn : ¬ l.unpausesHub h) :
    s'.paused h = true := by
  cases hst with
  | pause => simp only [upd]; split_ifs <;> simp [hp]
  | @unpause h' snd _ _ =>
    simp only [upd]; split_ifs with hq
    · exact absurd hq.symm (by simpa [Label.unpausesHub] using hn)
    · exact hp
  | @confirm i m f _ => cases f <;> exact hp
  | _ => exact hp

/-- A burn or mint on hub `h` needs `paused()` and the ecosystem pause off there. -/
theorem movesOn_blocked {W : World} {s s' : Sys} {l : Label} {h : ChainId}
    (hst : Step W s l s') (hmv : l.movesOn h) : s.paused h = false ∧ s.ecoPaused h = false := by
  cases hst with
  | burn hg => subst hmv; exact ⟨hg.notPaused, hg.ecoOff⟩
  | mintFresh hg => subst hmv; exact ⟨hg.notPaused, hg.ecoOff⟩
  | mintReturn hg => subst hmv; exact ⟨hg.notPaused, hg.ecoOff⟩
  | _ => simp [Label.movesOn] at hmv

theorem PauseHoldsUntilUnpaused : Properties.PauseHoldsUntilUnpaused := by
  intro W s s' ls h hrun
  induction hrun with
  | nil => exact ⟨fun _ _ _ l hl => by simp at hl, fun _ _ l hl => by simp at hl,
      fun _ _ l hl => by simp at hl⟩
  | @cons s0 s1 s2 l ls hst _ ih =>
    refine ⟨fun x hp hn l' hl' hmv => ?_, fun hp hn l' hl' hmv => ?_,
      fun hp hn l' hl' hmv => ?_⟩
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
    W.ctmRegistered h x = true ∧ l.togglesCTMPause h x (W.ctmOwner h x) := by
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
  | @confirm i m f _ => cases f <;> exact absurd rfl hne
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
  | @confirm i m f _ => cases f <;> exact absurd rfl hne
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

/-- `pauseAllBut h` keeps hub `h`'s `paused()`. -/
theorem pauseAllBut_paused {h : ChainId} {s : Sys} :
    (pauseAllBut h s).paused h = s.paused h := by simp [pauseAllBut]

/-- `pauseAllBut h` keeps hub `h`'s ecosystem pause. -/
theorem pauseAllBut_ecoPaused {h : ChainId} {s : Sys} :
    (pauseAllBut h s).ecoPaused h = s.ecoPaused h := by simp [pauseAllBut]

/-- `pauseAllBut h` keeps hub `h`'s CTM pauses. -/
theorem pauseAllBut_ctmPaused {h : ChainId} {s : Sys} {x : Address} :
    (pauseAllBut h s).ctmPaused h x = s.ctmPaused h x := by simp [pauseAllBut]

/-- A mint's guards on hub `h` survive pausing every other hub. -/
theorem MintOk.pauseAllBut {W : World} {s : Sys} {h : ChainId} {i : ℕ} {m : Msg}
    (hg : MintOk W s h i m) : MintOk W (pauseAllBut h s) h i m :=
  { msgAt := hg.msgAt, pending := hg.pending, forHub := hg.forHub, hubNonzero := hg.hubNonzero
    notPaused := by rw [pauseAllBut_paused]; exact hg.notPaused
    enabled := hg.enabled
    ecoOff := by rw [pauseAllBut_ecoPaused]; exact hg.ecoOff
    ctmOff := by rw [pauseAllBut_ctmPaused]; exact hg.ctmOff
    l1Numbers := hg.l1Numbers, l1Interval := hg.l1Interval, ctmKnown := hg.ctmKnown
    notHere := hg.notHere }

theorem PausesArePerHub : Properties.PausesArePerHub := by
  intro W s s' l h hst hmv
  cases hst with
  | @burn h' c t a hg =>
    simp only [Label.movesOn] at hmv; subst hmv
    have hok : BurnOk W (pauseAllBut h' s) h' c t a :=
      { hubNonzero := hg.hubNonzero
        notPaused := by rw [pauseAllBut_paused]; exact hg.notPaused
        enabled := hg.enabled
        ecoOff := by rw [pauseAllBut_ecoPaused]; exact hg.ecoOff
        ctmOff := by rw [pauseAllBut_ctmPaused]; exact hg.ctmOff
        ctmSet := hg.ctmSet, asset := hg.asset, dstListed := hg.dstListed
        settlesHere := hg.settlesHere, notSL := hg.notSL, registered := hg.registered
        atCtmVersion := hg.atCtmVersion, sameCtm := hg.sameCtm, toL1 := hg.toL1
        notAway := hg.notAway, dstDiamond := hg.dstDiamond, belowMax := hg.belowMax
        l1Record := hg.l1Record }
    have heq : pauseAllBut h' (burnPost W s h' c t a) = burnPost W (pauseAllBut h' s) h' c t a :=
      rfl
    rw [heq]; exact Step.burn hok
  | @mintFresh h' i m hg hnew hpv hl2 =>
    simp only [Label.movesOn] at hmv; subst hmv
    have heq : pauseAllBut h' (mintPost W s h' i m (W.ctmOfAsset h' m.asset) true) =
        mintPost W (pauseAllBut h' s) h' i m (W.ctmOfAsset h' m.asset) true := rfl
    rw [heq]; exact Step.mintFresh hg.pauseAllBut hnew hpv hl2
  | @mintReturn h' i m hg hold hpv haway =>
    simp only [Label.movesOn] at hmv; subst hmv
    have heq : pauseAllBut h' (mintPost W s h' i m (W.ctmOfAsset h' m.asset) false) =
        mintPost W (pauseAllBut h' s) h' i m (W.ctmOfAsset h' m.asset) false := rfl
    rw [heq]; exact Step.mintReturn hg.pauseAllBut hold hpv haway
  | _ => simp [Label.movesOn] at hmv

theorem RecoveryIgnoresPauses : Properties.RecoveryIgnoresPauses := by
  intro W s s' i c f hst
  cases hst with
  | @confirm _ m _ hg =>
    have heq : pauseAll (confirmPost W s i m f) =
        confirmPost { W with migrationsEnabled := false } (pauseAll s) i m f := by
      cases f <;> rfl
    rw [heq]
    exact Step.confirm
      { msgAt := hg.msgAt, fromL1 := hg.fromL1, failed := hg.failed, executed := hg.executed
        registered := hg.registered, ctmSet := hg.ctmSet, failNum := hg.failNum
        failAway := hg.failAway, failPv := hg.failPv }


/-! ## Witnesses -/

/-- After the setup and CTM `7`'s owner pausing it on L1. -/
def cahStCtmPaused : Sys :=
  { cahStSetup with ctmPaused := upd2 cahStSetup.ctmPaused 1 7 true }
/-- …and the owner lifting it again. -/
def cahStCtmUnpaused : Sys :=
  { cahStCtmPaused with ctmPaused := upd2 cahStCtmPaused.ctmPaused 1 7 false }

theorem CahCTMPauseWitness : Properties.CahCTMPauseWitness := by
  have hp : Step cahWorld cahStSetup (.pauseCTM 1 7 11) cahStCtmPaused :=
    Step.pauseCTM (by decide) rfl
  have hrun : Run cahWorld cahInit (cahSetup ++ [.pauseCTM 1 7 11]) cahStCtmPaused :=
    .cons cah_create_gw (.cons cah_create_chain (.cons hp .nil))
  refine ⟨cahStCtmPaused, hrun, hrun.reach (.init cahInit_init), by decide, rfl, ?_,
    cahStCtmUnpaused, _, Step.unpauseCTM (by decide) rfl, Step.burn (by constructor <;> decide),
    by decide, ⟨rfl, rfl⟩⟩
  rintro ⟨s', hst⟩
  obtain ⟨hg, -⟩ := burn_inv hst
  exact absurd hg.ctmOff (by decide)

/-- After the setup, CTM `7`'s pause and the ecosystem pause on L1. -/
def cahStBothPaused : Sys :=
  { cahStCtmPaused with ecoPaused := upd cahStCtmPaused.ecoPaused 1 true }
/-- …then the gateway paused… -/
def cahStGwPaused : Sys := { cahStBothPaused with paused := upd cahStBothPaused.paused 2 true }
/-- …and unpaused. -/
def cahStGwUnpaused : Sys := { cahStGwPaused with paused := upd cahStGwPaused.paused 2 false }
/-- …then L1's ecosystem pause lifted… -/
def cahStEcoLifted : Sys :=
  { cahStGwUnpaused with ecoPaused := upd cahStGwUnpaused.ecoPaused 1 false }
/-- …and CTM `7`'s pause lifted. -/
def cahStAllLifted : Sys :=
  { cahStEcoLifted with ctmPaused := upd2 cahStEcoLifted.ctmPaused 1 7 false }

theorem CahPauseHoldsWitness : Properties.CahPauseHoldsWitness := by
  have hp1 : Step cahWorld cahStSetup (.pauseCTM 1 7 11) cahStCtmPaused :=
    Step.pauseCTM (by decide) rfl
  have hp2 : Step cahWorld cahStCtmPaused (.pauseMigration 1 10) cahStBothPaused :=
    Step.pauseMigration rfl
  have hrun : Run cahWorld cahInit (cahSetup ++ [.pauseCTM 1 7 11, .pauseMigration 1 10])
      cahStBothPaused :=
    .cons cah_create_gw (.cons cah_create_chain (.cons hp1 (.cons hp2 .nil)))
  have hgw : Run cahWorld cahStBothPaused [.pause 2 10, .unpause 2 10] cahStGwUnpaused :=
    .cons (Step.pause rfl (by decide)) (.cons (Step.unpause rfl (by decide)) .nil)
  have hnot : ∀ s : Sys, (s.ecoPaused 1 = true ∨ s.ctmPaused 1 7 = true) →
      ¬ ∃ s', Step cahWorld s (.burn 1 3 2 5) s' := by
    rintro s hs ⟨s', hst⟩
    obtain ⟨hg, -⟩ := burn_inv hst
    rcases hs with hs | hs
    · rw [hg.ecoOff] at hs; cases hs
    · have := hg.ctmOff; rw [show cahWorld.ctmOfAsset 1 5 = 7 from rfl, hs] at this; cases this
  refine ⟨cahStBothPaused, hrun, hrun.reach (.init cahInit_init), by decide, by decide,
    cahStGwUnpaused, hgw, ?_, hnot _ (Or.inl (by decide)), cahStEcoLifted, cahStAllLifted,
    Step.unpauseMigration rfl, hnot _ (Or.inr (by decide)), Step.unpauseCTM (by decide) rfl, _,
    Step.burn (by constructor <;> decide)⟩
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> simp [Label.unpausesCTM, Label.unpausesEcosystem]

/-- With chain `3` on the gateway, L1's `pause()`. -/
def cahStL1Paused : Sys := { cahStOnGw with paused := upd cahStOnGw.paused 1 true }
/-- …then the gateway's burn back… -/
def cahStL1PausedBack : Sys := burnPost cahWorld cahStL1Paused 2 3 1 5
/-- …and the gateway owner's ecosystem pause. -/
def cahStGwEco : Sys :=
  { cahStL1PausedBack with ecoPaused := upd cahStL1PausedBack.ecoPaused 2 true }

theorem CahPausedHubWitness : Properties.CahPausedHubWitness := by
  have hp : Step cahWorld cahStOnGw (.pause 1 10) cahStL1Paused := Step.pause rfl (by decide)
  have hrun : Run cahWorld cahInit (cahSetup ++ [.burn 1 3 2 5, .mint 2 0 3 5, .pause 1 10])
      cahStL1Paused :=
    .cons cah_create_gw (.cons cah_create_chain (.cons cah_burn_out (.cons cah_mint_gw
      (.cons hp .nil))))
  have hb : Step cahWorld cahStL1Paused (.burn 2 3 1 5) cahStL1PausedBack :=
    Step.burn (by constructor <;> decide)
  have he : Step cahWorld cahStL1PausedBack (.pauseMigration 2 10) cahStGwEco :=
    Step.pauseMigration rfl
  refine ⟨cahStL1Paused, hrun, hrun.reach (.init cahInit_init), by decide, cahStL1PausedBack,
    cahStGwEco, hb, rfl, he, .cons hb (.cons he .nil), ?_, by decide, ?_⟩
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> simp [Label.unpausesHub]
  · rintro ⟨s'', hst⟩
    obtain ⟨m, hg, -, -, -⟩ := mint_inv hst
    exact absurd hg.notPaused (by decide)

/-- In `cahWorldMismatched`: after the setup… -/
def cahStSetupMismatched : Sys :=
  createPost cahWorldMismatched (createPost cahWorldMismatched cahInit 2 7) 3 7
/-- …and CTM `7`'s owner pausing it on L1. -/
def cahStMismatchedPaused : Sys :=
  { cahStSetupMismatched with ctmPaused := upd2 cahStSetupMismatched.ctmPaused 1 7 true }

theorem CahMismatchedRegistryReadsAnotherPause :
    Properties.CahMismatchedRegistryReadsAnotherPause := by
  have hrun : Run cahWorldMismatched cahInit (cahSetup ++ [.pauseCTM 1 7 11])
      cahStMismatchedPaused :=
    .cons (Step.createChain ⟨by decide, by decide, by decide, by decide, rfl, rfl⟩)
      (.cons (Step.createChain ⟨by decide, by decide, by decide, by decide, by decide,
        by decide⟩) (.cons (Step.pauseCTM (by decide) rfl) .nil))
  exact ⟨cahStMismatchedPaused, _, hrun, hrun.reach (.init cahInit_init), by decide, by decide,
    by decide, Step.burn (by constructor <;> decide)⟩

end Contracts.ChainAssetHandler
