import EraSpec.Contracts.ChainAdminOwnable.Properties.AdminRoles
import EraSpec.Contracts.ChainAdminOwnable.Proofs.Authority

/-!
# Proofs: the admin roles a `ChainAdminOwnable` holds

The diamond results are `sem_renounced` (`Proofs/Authority.lean`) read at a diamond. The Bridgehub
results invert the one call the setter can make there; the recovery is an explicit run.
-/

namespace Contracts.ChainAdminOwnable

/-! ## The diamond -/

theorem RenouncedCaoKeepsDiamondAdmin : Properties.RenouncedCaoKeepsDiamondAdmin := by
  intro cfg S S' L D hwf ho hp hD h hcut
  exact ((sem_renounced hwf h ⟨ho, hp⟩).2.1 D hD hcut).1

theorem RenounceStrandsDiamondAdminRole : Properties.RenounceStrandsDiamondAdminRole := by
  intro cfg S S' L D hwf ho hp hD h hcut s sel hm
  exact ((sem_renounced hwf h ⟨ho, hp⟩).2.1 D hD hcut).2 s sel hm

theorem RenouncedCaoReachesOnlySetTokenMultiplier :
    Properties.RenouncedCaoReachesOnlySetTokenMultiplier := by
  intro cfg S S' L hwf ho hp h
  obtain ⟨_, _, he⟩ := sem_renounced hwf h ⟨ho, hp⟩
  exact ⟨fun D sel hm => he _ hm rfl, fun sel hm => he _ hm rfl⟩

/-! ## The Bridgehub -/

theorem BridgehubAdminRecoverable : Properties.BridgehubAdminRecoverable := by
  intro cfg S x arg ho0 hocao hopa hx0 hxcao hxpa harg
  have hdec1 : decodeAdminOp cfg.abi (SEL_SET_PENDING_ADMIN ++ arg) = some (.setPending x) := by
    simp [decodeAdminOp, SEL_SET_PENDING_ADMIN, harg]
  have hdec2 : decodeAdminOp cfg.abi SEL_ACCEPT_ADMIN = some .accept := by
    simp [decodeAdminOp, SEL_ACCEPT_ADMIN, SEL_SET_PENDING_ADMIN]
  have hstep1 : hubAdminStep S.hub.owner S.hub (.setPending x) =
      some { S.hub with pendingAdmin := x } := by
    simp [hubAdminStep, hx0]
  have hstep2 : hubAdminStep x { S.hub with pendingAdmin := x } .accept =
      some { S.hub with admin := x, pendingAdmin := 0 } := by
    simp [hubAdminStep]
  exact ⟨_, _,
    Sem.actsCall (c := ⟨cfg.hub, 0, SEL_SET_PENDING_ADMIN ++ arg⟩) (ok := true) hocao ho0
      (Sem.hubAdmin rfl hopa rfl hdec1 hstep1) <|
    Sem.actsCall (c := ⟨cfg.hub, 0, SEL_ACCEPT_ADMIN⟩) (ok := true) hxcao hx0
      (Sem.hubAdmin rfl hxpa rfl hdec2 hstep2) <|
    Sem.actsNil, rfl, rfl, rfl, rfl⟩

theorem SetterCallToBridgehubReverts : Properties.SetterCallToBridgehubReverts := by
  intro cfg S S' L v n d hwf h
  obtain ⟨_, hcaoHub, _, hhubChain⟩ := hwf
  cases h with
  | caoReceive ht _ => exact hcaoHub ht.symm
  | caoView ht _ _ => exact hcaoHub ht.symm
  | caoOwn ht _ _ _ => exact hcaoHub ht.symm
  | caoSetSetter ht _ _ _ _ => exact hcaoHub ht.symm
  | caoMulticall ht _ _ _ _ _ => exact hcaoHub ht.symm
  | caoSetMultiplier ht _ _ _ _ _ => exact hcaoHub ht.symm
  | chainAdmin hch _ _ _ => rw [hhubChain] at hch; cases hch
  | chainGated hch _ _ _ => rw [hhubChain] at hch; cases hch
  | chainCut hch _ _ _ => rw [hhubChain] at hch; cases hch
  | chainOther hch _ _ => rw [hhubChain] at hch; cases hch
  | hubOwn _ _ _ hdec _ => rw [decodeOwnOp_multiplierData] at hdec; cases hdec
  | hubAdmin _ _ _ hdec _ => rw [decodeAdminOp_multiplierData] at hdec; cases hdec
  | hubOther _ _ hmem _ _ =>
      rw [multiplierData_take] at hmem
      exact setMultiplier_not_bridgehub hmem
  | external _ hne _ _ => exact hne rfl

theorem SetTokenMultiplierOnBridgehubReverts :
    Properties.SetTokenMultiplierOnBridgehubReverts := by
  intro cfg S S' L s v data n d hwf hsel hargs h
  have hwf' := hwf
  obtain ⟨_, hcaoHub, hcaoChain, _⟩ := hwf
  cases h with
  | caoReceive _ hnil =>
      change data = [] at hnil
      rw [hnil] at hsel
      exact absurd hsel (by decide)
  | caoView _ _ hmem =>
      rw [hsel] at hmem
      exact absurd hmem (by decide)
  | caoOwn _ _ hdec _ =>
      have h1 : SEL_SET_MULTIPLIER_VIA ≠ SEL_TRANSFER_OWNERSHIP := by decide
      have h2 : SEL_SET_MULTIPLIER_VIA ≠ SEL_ACCEPT_OWNERSHIP := by decide
      have h3 : SEL_SET_MULTIPLIER_VIA ≠ SEL_RENOUNCE_OWNERSHIP := by decide
      simp [decodeOwnOp, hsel, h1, h2, h3] at hdec
  | caoSetSetter _ _ hs _ _ =>
      rw [hsel] at hs
      exact absurd hs (by decide)
  | caoMulticall _ hs _ _ _ _ =>
      rw [hsel] at hs
      exact absurd hs (by decide)
  | caoSetMultiplier _ _ _ hdec _ hinner =>
      rw [hargs] at hdec
      cases hdec
      exact SetterCallToBridgehubReverts cfg _ _ _ 0 _ _ hwf' hinner
  | chainAdmin hch _ _ _ => rw [hcaoChain] at hch; cases hch
  | chainGated hch _ _ _ => rw [hcaoChain] at hch; cases hch
  | chainCut hch _ _ _ => rw [hcaoChain] at hch; cases hch
  | chainOther hch _ _ => rw [hcaoChain] at hch; cases hch
  | hubOwn ht _ _ _ _ => exact hcaoHub ht
  | hubAdmin ht _ _ _ _ => exact hcaoHub ht
  | hubOther ht _ _ _ _ => exact hcaoHub ht
  | external hne _ _ _ => exact hne rfl

private theorem sem_noSetterCallToHub {cfg : Config} (hwf : cfg.WF) {j : Judgement}
    {S S' : State} {L : List Event} (h : Sem cfg j S L S') :
    ∀ inv pre t n d c ok, Event.caoCall (.multiplier inv pre t n d) c ok ∈ L → t ≠ cfg.hub := by
  induction h with
  | callFails => intro _ _ _ _ _ _ _ hm; simp at hm
  | caoReceive => intro _ _ _ _ _ _ _ hm; simp at hm
  | caoView => intro _ _ _ _ _ _ _ hm; simp at hm
  | caoOwn => intro _ _ _ _ _ _ _ hm; simp at hm
  | caoSetSetter => intro _ _ _ _ _ _ _ hm; simp at hm
  | caoMulticall _ _ _ _ _ _ ih => exact ih
  | @caoSetMultiplier s c S S' L t n d _ _ _ _ _ hinner ih =>
      intro inv pre t' n' d' c' ok hm
      rcases List.mem_append.mp hm with hm | hm
      · exact ih inv pre t' n' d' c' ok hm
      · simp only [List.mem_singleton, Event.caoCall.injEq, Origin.multiplier.injEq] at hm
        obtain ⟨⟨-, -, rfl, -, -⟩, -, -⟩ := hm
        rintro rfl
        exact SetterCallToBridgehubReverts cfg _ _ _ 0 n d hwf hinner
  | chainAdmin => intro _ _ _ _ _ _ _ hm; simp at hm
  | chainGated _ _ _ _ ih =>
      intro inv pre t n d c ok hm
      simp only [List.mem_cons, reduceCtorEq, false_or] at hm
      exact ih inv pre t n d c ok hm
  | chainCut _ _ _ _ ih =>
      intro inv pre t n d c ok hm
      simp only [List.mem_cons, reduceCtorEq, false_or] at hm
      exact ih inv pre t n d c ok hm
  | chainOther _ _ _ ih =>
      intro inv pre t n d c ok hm
      simp only [List.mem_cons, reduceCtorEq, false_or] at hm
      exact ih inv pre t n d c ok hm
  | hubOwn => intro _ _ _ _ _ _ _ hm; simp at hm
  | hubAdmin => intro _ _ _ _ _ _ _ hm; simp at hm
  | hubOther _ _ _ _ _ ih =>
      intro inv pre t n d c ok hm
      simp only [List.mem_cons, reduceCtorEq, false_or] at hm
      exact ih inv pre t n d c ok hm
  | external _ _ _ _ ih => exact ih
  | loopDone => intro _ _ _ _ _ _ _ hm; simp at hm
  | loopStep _ _ _ _ ih1 ih2 =>
      intro inv pre t n d c ok hm
      rcases List.mem_append.mp hm with hm | hm
      · exact ih1 inv pre t n d c ok hm
      rcases List.mem_cons.mp hm with hm | hm
      · simp at hm
      · exact ih2 inv pre t n d c ok hm
  | actsNil => intro _ _ _ _ _ _ _ hm; simp at hm
  | actsCall _ _ _ _ ih1 ih2 =>
      intro inv pre t n d c ok hm
      rcases List.mem_append.mp hm with hm | hm
      · exact ih1 inv pre t n d c ok hm
      · exact ih2 inv pre t n d c ok hm

theorem NoSetterCallReachesBridgehub : Properties.NoSetterCallReachesBridgehub := by
  intro cfg S S' L hwf h
  exact sem_noSetterCallToHub hwf h

/-! ## Which premises are needed -/

theorem PendingDiamondAdminEscapes : Properties.PendingDiamondAdminEscapes := by
  refine ⟨⟨_, w_multicallOutlivesRenounce⟩, rfl, rfl, by decide, _, _,
    Sem.actsCall (s := 12) (c := ⟨4, 0, SEL_ACCEPT_ADMIN⟩) (ok := true) (by decide)
      (by decide)
      (Sem.chainAdmin (op := .accept) (p := ⟨12, 0⟩) (by decide) rfl (by decide) (by decide)) <|
    Sem.actsNil, ?_, ?_⟩
  · decide
  · decide

theorem CtmCutMovesRenouncedAdmin : Properties.CtmCutMovesRenouncedAdmin := by
  refine ⟨rfl, rfl, by decide, _, _,
    Sem.actsCall (s := 5) (c := ⟨4, 0, SEL_EXECUTE_UPGRADE⟩) (ok := true) (by decide)
      (by decide)
      (Sem.chainCut (p := ⟨13, 0⟩) (by decide) (by decide) (Or.inr rfl) Sem.actsNil) <|
    Sem.actsNil, ?_, ?_⟩
  · decide
  · decide

theorem AdminRoleLiveBeforeRenounce : Properties.AdminRoleLiveBeforeRenounce := by
  refine ⟨by decide, by decide, by decide, _, _,
    Sem.actsCall (s := 6) (c := ⟨1, 0, SEL_MULTICALL ++ [3]⟩) (ok := true) (by decide)
      (by decide)
      (Sem.caoMulticall (cs := wCallsC) (rs := true) rfl (by decide) (by decide) rfl (by decide)
        (Sem.loopStep (c := ⟨4, 0, withWord SEL_SET_TRANSACTION_FILTERER 13⟩) (ok := true)
          (by decide)
          (Sem.chainGated (by decide) rfl (Or.inl ⟨by decide, by decide⟩) Sem.actsNil)
          (fun _ => rfl)
          (Sem.loopDone (by decide)))) Sem.actsNil, ?_, ?_⟩
  · decide
  · decide

/-! ## Witnesses -/

/-- The `ChainAdminOwnable`'s call `setTokenMultiplier(3, 2)` to diamond `4`, from a state where it
is the diamond's admin. -/
private theorem w_caoCallsChain {S : State} (hadm : (S.chain 4).admin = 1) :
    Sem wCfg (.call wCfg.cao ⟨4, 0, multiplierData 3 2⟩ true) S
      [.chainEntry 4 1 SEL_SET_MULTIPLIER] S :=
  Sem.chainGated (by decide) rfl (Or.inr ⟨by decide, Or.inl hadm.symm⟩) Sem.actsNil

theorem AdminRolesWitness : Properties.AdminRolesWitness := by
  refine ⟨wCfg_wellFormed, rfl, rfl, by decide, rfl, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, _, _,
    Sem.actsCall (s := 7) (c := ⟨1, 0, viaData 4 3 2⟩) (ok := true) (by decide) (by decide)
      (Sem.caoSetMultiplier (t := 4) (n := 3) (d := 2) rfl rfl (by decide) (by decide) rfl
        (w_caoCallsChain rfl)) <|
    Sem.actsCall (s := 5) (c := ⟨4, 0, SEL_CHANGE_FEE_PARAMS⟩) (ok := true) (by decide)
      (by decide)
      (Sem.chainGated (by decide) rfl (Or.inr ⟨by decide, Or.inr rfl⟩) Sem.actsNil) <|
    Sem.actsCall (s := 9) (c := ⟨2, 0, withWord SEL_SET_PENDING_ADMIN 8⟩) (ok := true)
      (by decide) (by decide)
      (Sem.hubAdmin (op := .setPending 8) (h := ⟨9, 0, 1, 8⟩) rfl (by decide) rfl (by decide)
        (by decide)) <|
    Sem.actsCall (s := 8) (c := ⟨2, 0, SEL_ACCEPT_ADMIN⟩) (ok := true) (by decide) (by decide)
      (Sem.hubAdmin (op := .accept) (h := ⟨9, 0, 8, 0⟩) rfl (by decide) rfl (by decide)
        (by decide)) <|
    Sem.actsNil, ?_⟩
  decide

theorem SetterReachesDiamondNotBridgehub : Properties.SetterReachesDiamondNotBridgehub := by
  refine ⟨wCfg_wellFormed, ⟨_, _, w_caoCallsChain rfl⟩,
    ⟨_, _, Sem.caoSetMultiplier (t := 4) (n := 3) (d := 2) rfl rfl (by decide) (by decide) rfl
      (w_caoCallsChain rfl)⟩, by decide, by decide⟩

end Contracts.ChainAdminOwnable
