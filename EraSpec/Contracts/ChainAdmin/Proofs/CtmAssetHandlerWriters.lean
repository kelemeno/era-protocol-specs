import EraSpec.Contracts.ChainAdmin.Properties.CtmAssetHandlerWriters
import EraSpec.Contracts.ChainAdmin.Proofs.PermanentRestrictionMigration

/-!
# Proofs: the CTM asset's handler is the chain asset handler, so P's check is off

`step_handler_cases` sorts every call by what it does to the handler at a CTM's id; the run
results are inductions that carry an invariant and lift a step's collision into the run's
log.  The headline then applies `PermanentRestrictionMigration.HandlerOffBridgehubSkipsCheck`.
-/

namespace Contracts.ChainAdmin.CtmAssetHandlerWriters

open Contracts.AssetRouter (AssetIdOf Router upd senderOf writtenId SetGuard setHandler)
open PermanentRestrictionMigration (Abi Env Call Bytes MigrationRequest
  BridgehubAnswersNoChainId validateCall newAdminFromMigration burnAdmin prmCall prmEnv
  prmRequest)

/-! ## Point updates and the CTMDT's id -/

lemma upd_apply (f : AssetId → Address) (a : AssetId) (v : Address) (x : AssetId) :
    upd f a v x = if x = a then v else f x := rfl

lemma upd_ne {f : AssetId → Address} {a x : AssetId} {v : Address} (h : x ≠ a) :
    upd f a v x = f x := by simp [upd, h]

lemma upd_same (f : AssetId → Address) (a : AssetId) (v : Address) : upd f a v a = v := by
  simp [upd]

/-- The CTMDT is not the vault, so its registrations hash its own address. -/
lemma writtenId_ctmdt (K : Cfg) (ctm : Address) :
    writtenId K.enc K.l1 K.ntv K.ntvAddr K.ctmdt ctm = ctmAssetId K ctm := by
  simp [writtenId, senderOf, ctmAssetId, K.ctmdtNotNtv]

/-- A registration by anyone but the CTMDT hashes a sender other than the CTMDT. -/
lemma senderOf_ne_ctmdt (K : Cfg) {caller : Address} (h : caller ≠ K.ctmdt) :
    senderOf K.ntv K.ntvAddr caller ≠ K.ctmdt := by
  unfold senderOf
  split_ifs
  · exact fun e => K.ctmdtNotNtvAddr e.symm
  · exact h

/-! ## What one call does to a CTM's handler -/

/-- If a step changes the handler at `x`, it wrote `x`: either a CTMDT write of `x`, a
fallback at an unset `x`, or a call whose handler triple hashes to `x`. -/
lemma step_handler_cases {K : Cfg} {s s' : St} {op : Op} (h : Step K s op s') (x : AssetId)
    (hx : s'.router.handler x ≠ s.router.handler x) :
    (∃ ctm, (op = .registerCTMAssetOnL1 ctm ∨ op = .setCtmAssetHandlerAddressOnL1 ctm) ∧
      x = ctmAssetId K ctm ∧ s'.router.handler x = s.chainAssetHandler) ∨
    (op = .finalize x ∧ s.router.handler x = 0) ∨
    (∃ t : Chain × Address × AssetData, op.handlerTriple K = some t ∧
      t.2.1 ≠ K.ctmdt ∧ K.enc t.1 t.2.1 t.2.2 = x) := by
  cases h with
  | @registerCTMAssetOnL1 ctm _ _ _ =>
    left
    simp only [setHandler, writtenId_ctmdt] at hx ⊢
    by_cases hxa : x = ctmAssetId K ctm
    · exact ⟨ctm, Or.inl rfl, hxa, by rw [hxa, upd_same]⟩
    · exact absurd (upd_ne hxa) hx
  | @setCtmAssetHandlerAddressOnL1 ctm _ =>
    left
    simp only [setHandler, writtenId_ctmdt] at hx ⊢
    by_cases hxa : x = ctmAssetId K ctm
    · exact ⟨ctm, Or.inr rfl, hxa, by rw [hxa, upd_same]⟩
    · exact absurd (upd_ne hxa) hx
  | @register caller d hh hne _ =>
    right; right
    simp only [setHandler] at hx
    by_cases hxa : x = writtenId K.enc K.l1 K.ntv K.ntvAddr caller d
    · exact ⟨(K.l1, senderOf K.ntv K.ntvAddr caller, d), rfl, senderOf_ne_ctmdt K hne, hxa.symm⟩
    · exact absurd (upd_ne hxa) hx
  | @finalize a h0 =>
    right; left
    by_cases hxa : x = a
    · subst hxa; exact ⟨rfl, h0⟩
    · exact absurd (upd_ne hxa) hx
  | setNativeTokenVault =>
    right; right
    by_cases hxa : x = K.enc K.l1 K.ntvAddr K.ethToken
    · exact ⟨(K.l1, K.ntvAddr, K.ethToken), rfl, fun e => K.ctmdtNotNtvAddr e.symm, hxa.symm⟩
    · exact absurd (upd_ne hxa) hx
  | setAssetDeploymentTracker => exact absurd rfl hx
  | setAddresses => exact absurd rfl hx
  | setCTMAssetAddress => exact absurd rfl hx
  | addChainTypeManager => exact absurd rfl hx
  | removeChainTypeManager => exact absurd rfl hx

/-- Every step but `setAddresses` keeps the Bridgehub's chain asset handler. -/
lemma step_chainAssetHandler {K : Cfg} {s s' : St} {op : Op} (h : Step K s op s')
    (hop : ¬ op.IsSetAddresses) : s'.chainAssetHandler = s.chainAssetHandler := by
  cases h <;> first | rfl | exact absurd trivial hop

/-- A step keeps `ChainAssetHandlerOk` if it is not a `setAddresses` naming zero or the
Bridgehub. -/
lemma step_chainAssetHandlerOk {K : Cfg} {s s' : St} {op : Op} (h : Step K s op s')
    (hk : op.KeepsChainAssetHandlerOk K) (hok : ChainAssetHandlerOk K s) :
    ChainAssetHandlerOk K s' := by
  cases h with
  | setAddresses => exact hk
  | _ => exact hok

/-- A step's own collision with the CTM's triple, from `step_handler_cases`'s last case. -/
lemma collision_of_triple {K : Cfg} {op : Op} {ctm : Address} {t : Chain × Address × AssetData}
    (ht : op.handlerTriple K = some t) (hs : t.2.1 ≠ K.ctmdt)
    (he : K.enc t.1 t.2.1 t.2.2 = ctmAssetId K ctm) :
    ∃ t : Chain × Address × AssetData, op.handlerTriple K = some t ∧
      t ≠ (K.l1, K.ctmdt, ctm) ∧ K.enc t.1 t.2.1 t.2.2 = ctmAssetId K ctm :=
  ⟨t, ht, fun e => hs (by rw [e]), he⟩

lemma collides_cons {K : Cfg} {ctm : Address} {op : Op} {ops : List Op} :
    CollidesWithCtm K ctm ops → CollidesWithCtm K ctm (op :: ops) := by
  rintro ⟨op', hm, rest⟩
  exact ⟨op', List.mem_cons_of_mem _ hm, rest⟩

lemma collides_head {K : Cfg} {ctm : Address} {op : Op} {ops : List Op}
    (h : ∃ t : Chain × Address × AssetData, op.handlerTriple K = some t ∧
      t ≠ (K.l1, K.ctmdt, ctm) ∧ K.enc t.1 t.2.1 t.2.2 = ctmAssetId K ctm) :
    CollidesWithCtm K ctm (op :: ops) :=
  ⟨op, List.mem_cons_self, h⟩

/-! ## (d) The writers -/

theorem CtmTrackerWritesChainAssetHandler : Properties.CtmTrackerWritesChainAssetHandler := by
  intro K s s' op ctm hop h
  rcases hop with rfl | rfl
  · cases h with
    | registerCTMAssetOnL1 _ _ _ =>
      refine ⟨?_, ?_, fun a ha => ?_, rfl, fun _ => ?_⟩ <;>
        simp only [setHandler, writtenId_ctmdt]
      · exact upd_same _ _ _
      · exact upd_same _ _ _
      · exact upd_ne ha
      · exact upd_same _ _ _
  · cases h with
    | setCtmAssetHandlerAddressOnL1 _ =>
      refine ⟨?_, ?_, fun a ha => ?_, rfl, fun h => nomatch h⟩ <;>
        simp only [setHandler, writtenId_ctmdt]
      · exact upd_same _ _ _
      · exact upd_same _ _ _
      · exact upd_ne ha

theorem OnlyCtmTrackerRewritesCtmHandler : Properties.OnlyCtmTrackerRewritesCtmHandler := by
  intro K s s' op ctm h hx
  rcases step_handler_cases h (ctmAssetId K ctm) hx with
    ⟨ctm', hop, hid, _⟩ | hfin | ⟨t, ht, hs, he⟩
  · by_cases hc : ctm' = ctm
    · subst hc; exact Or.inl hop
    · right; right
      refine ⟨(K.l1, K.ctmdt, ctm'), ?_, ?_, hid.symm⟩
      · rcases hop with rfl | rfl <;> rfl
      · intro e; exact hc (Prod.ext_iff.mp (Prod.ext_iff.mp e).2).2
  · exact Or.inr (Or.inl hfin)
  · exact Or.inr (Or.inr (collision_of_triple ht hs he))

theorem OnlySetAddressesMovesChainAssetHandler :
    Properties.OnlySetAddressesMovesChainAssetHandler := by
  intro K s s' op h hne
  by_contra hop
  exact hne (step_chainAssetHandler h hop)

/-! ## Runs -/

/-- One step of `CtmHandlerStaysOffBridgehub`. -/
lemma step_offBridgehub {K : Cfg} {s s' : St} {op : Op} {ctm : Address} (h : Step K s op s')
    (hoff : HandlerOffBridgehub K ctm s) (hok : ChainAssetHandlerOk K s)
    (hk : op.KeepsChainAssetHandlerOk K) :
    (HandlerOffBridgehub K ctm s' ∧ ChainAssetHandlerOk K s') ∨
    ∃ t : Chain × Address × AssetData, op.handlerTriple K = some t ∧
      t ≠ (K.l1, K.ctmdt, ctm) ∧ K.enc t.1 t.2.1 t.2.2 = ctmAssetId K ctm := by
  have hok' := step_chainAssetHandlerOk h hk hok
  by_cases hx : s'.router.handler (ctmAssetId K ctm) = s.router.handler (ctmAssetId K ctm)
  · left
    exact ⟨by unfold HandlerOffBridgehub; rw [hx]; exact hoff, hok'⟩
  rcases step_handler_cases h (ctmAssetId K ctm) hx with
    ⟨_, _, _, hv⟩ | ⟨_, h0⟩ | ⟨t, ht, hs, he⟩
  · exact Or.inl ⟨by unfold HandlerOffBridgehub; rw [hv]; exact hok, hok'⟩
  · exact absurd h0 hoff.1
  · exact Or.inr (collision_of_triple ht hs he)

theorem CtmHandlerStaysOffBridgehub : Properties.CtmHandlerStaysOffBridgehub := by
  intro K s s' ops ctm hrun
  induction hrun with
  | nil => intro hoff hok _; exact Or.inl ⟨hoff, hok⟩
  | @cons s1 s2 s3 op ops hs _ ih =>
    intro hoff hok hk
    rcases step_offBridgehub hs hoff hok (hk op List.mem_cons_self) with ⟨hoff2, hok2⟩ | hc
    · rcases ih hoff2 hok2 (fun o ho => hk o (List.mem_cons_of_mem _ ho)) with h | h
      · exact Or.inl h
      · exact Or.inr (collides_cons h)
    · exact Or.inr (collides_head hc)

theorem CtmHandlerOffBridgehubAfterRegistration :
    Properties.CtmHandlerOffBridgehubAfterRegistration := by
  intro K s s' ops ctm hrun
  induction hrun with
  | nil => intro _ _ hw; obtain ⟨_, hm, _⟩ := hw; exact absurd hm (List.not_mem_nil)
  | @cons s1 s2 s3 op ops hs hrest ih =>
    intro hok hk hw
    have hk' : ∀ o ∈ ops, o.KeepsChainAssetHandlerOk K := fun o ho => hk o (List.mem_cons_of_mem _ ho)
    have hok2 := step_chainAssetHandlerOk hs (hk op List.mem_cons_self) hok
    by_cases hop : op.WritesCtmHandler ctm
    · obtain ⟨hv, _, _, hcah, _⟩ := CtmTrackerWritesChainAssetHandler K s1 s2 op ctm hop hs
      have hoff2 : HandlerOffBridgehub K ctm s2 := by
        unfold HandlerOffBridgehub; rw [hv]; exact hok
      rcases CtmHandlerStaysOffBridgehub K s2 s3 ops ctm hrest hoff2 hok2 hk' with h | h
      · exact Or.inl h.1
      · exact Or.inr (collides_cons h)
    · obtain ⟨o, hm, ho⟩ := hw
      have hm' : o ∈ ops := by
        rcases List.mem_cons.mp hm with rfl | hm'
        · exact absurd ho hop
        · exact hm'
      rcases ih hok2 hk' ⟨o, hm', ho⟩ with h | h
      · exact Or.inl h
      · exact Or.inr (collides_cons h)

/-- One step of `CtmHandlerIsChainAssetHandler`. -/
lemma step_isChainAssetHandler {K : Cfg} {s s' : St} {op : Op} {ctm : Address}
    (h : Step K s op s') (hv : s.router.handler (ctmAssetId K ctm) = s.chainAssetHandler)
    (hnz : s.chainAssetHandler ≠ 0) (hop : ¬ op.IsSetAddresses) :
    (s'.router.handler (ctmAssetId K ctm) = s'.chainAssetHandler ∧ s'.chainAssetHandler ≠ 0) ∨
    ∃ t : Chain × Address × AssetData, op.handlerTriple K = some t ∧
      t ≠ (K.l1, K.ctmdt, ctm) ∧ K.enc t.1 t.2.1 t.2.2 = ctmAssetId K ctm := by
  have hc := step_chainAssetHandler h hop
  by_cases hx : s'.router.handler (ctmAssetId K ctm) = s.router.handler (ctmAssetId K ctm)
  · exact Or.inl ⟨by rw [hx, hv, hc], by rw [hc]; exact hnz⟩
  rcases step_handler_cases h (ctmAssetId K ctm) hx with
    ⟨_, _, _, hv'⟩ | ⟨_, h0⟩ | ⟨t, ht, hs, he⟩
  · exact Or.inl ⟨by rw [hv', hc], by rw [hc]; exact hnz⟩
  · exact absurd (h0 ▸ hv).symm hnz
  · exact Or.inr (collision_of_triple ht hs he)

theorem CtmHandlerIsChainAssetHandler : Properties.CtmHandlerIsChainAssetHandler := by
  intro K s s' ops ctm hrun
  induction hrun with
  | nil => intro hv _ _; exact Or.inl hv
  | @cons s1 s2 s3 op ops hs _ ih =>
    intro hv hnz hno
    rcases step_isChainAssetHandler hs hv hnz (hno op List.mem_cons_self) with ⟨hv2, hnz2⟩ | hc
    · rcases ih hv2 hnz2 (fun o ho => hno o (List.mem_cons_of_mem _ ho)) with h | h
      · exact Or.inl h
      · exact Or.inr (collides_cons h)
    · exact Or.inr (collides_head hc)

theorem CtmHandlerIsChainAssetHandlerAfterRegistration :
    Properties.CtmHandlerIsChainAssetHandlerAfterRegistration := by
  intro K s s' ops ctm hrun
  induction hrun with
  | nil => intro _ _ hw; obtain ⟨_, hm, _⟩ := hw; exact absurd hm (List.not_mem_nil)
  | @cons s1 s2 s3 op ops hs hrest ih =>
    intro hnz hno hw
    have hno' : ∀ o ∈ ops, ¬ o.IsSetAddresses := fun o ho => hno o (List.mem_cons_of_mem _ ho)
    have hc := step_chainAssetHandler hs (hno op List.mem_cons_self)
    have hnz2 : s2.chainAssetHandler ≠ 0 := by rw [hc]; exact hnz
    by_cases hop : op.WritesCtmHandler ctm
    · obtain ⟨hv, _, _, _, _⟩ := CtmTrackerWritesChainAssetHandler K s1 s2 op ctm hop hs
      rcases CtmHandlerIsChainAssetHandler K s2 s3 ops ctm hrest (by rw [hv, hc]) hnz2 hno' with
        h | h
      · exact Or.inl h
      · exact Or.inr (collides_cons h)
    · obtain ⟨o, hm, ho⟩ := hw
      have hm' : o ∈ ops := by
        rcases List.mem_cons.mp hm with rfl | hm'
        · exact absurd ho hop
        · exact hm'
      rcases ih hnz2 hno' ⟨o, hm', ho⟩ with h | h
      · exact Or.inl h
      · exact Or.inr (collides_cons h)

theorem DeployedRunsDisableMigrationCheck : Properties.DeployedRunsDisableMigrationCheck := by
  intro K s s' ops ctm A E chainAdmin c bridgehubData hrun hok hk hw hnc hE hr hno hne
  rcases CtmHandlerOffBridgehubAfterRegistration K s s' ops ctm hrun hok hk hw with hoff | hc
  · obtain ⟨hbh, _, _, hh, _, _⟩ := hE
    have hh' : E.assetHandlerAddress (ctmAssetId K ctm) ≠ E.bridgehub := by
      rw [hh, hbh]; exact hoff.2
    refine ⟨(PermanentRestrictionMigration.HandlerOffBridgehubSkipsCheck A E chainAdmin c
      (ctmAssetId K ctm) bridgehubData hr hh' hno hne).1, fun allowed => ?_⟩
    exact (PermanentRestrictionMigration.HandlerOffBridgehubSkipsCheck A
      { E with allowedL2Admins := allowed } chainAdmin c (ctmAssetId K ctm) bridgehubData hr hh'
      hno hne).2
  · exact absurd hc hnc

/-! ## Witnesses and load-bearing premises -/

/-- The deployment sequence runs from `cawS0` to `cawS1`. -/
lemma caw_run : Run cawCfg cawS0 cawOps cawS1 :=
  Run.cons Step.setAssetDeploymentTracker
    (Run.cons (Step.registerCTMAssetOnL1 (by decide) ⟨Or.inr (by decide), by decide⟩ rfl) Run.nil)

theorem CtmWritersDeploymentWitness : Properties.CtmWritersDeploymentWitness := by
  refine ⟨caw_run, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_,
    ⟨.registerCTMAssetOnL1 30, by simp [cawOps],
    Or.inl rfl⟩, ?_, by decide, rfl, by decide, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, [1], prmRequest, [2], rfl, by decide, rfl, rfl, by decide⟩, rfl, by decide, by decide,
    rfl, by decide⟩
  · intro op hop
    simp only [cawOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl <;> trivial
  · intro op hop
    simp only [cawOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl <;> exact id
  · rintro ⟨op, hop, t, ht, hne, _⟩
    simp only [cawOps, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl
    · exact nomatch ht
    · simp only [Op.handlerTriple, Option.some.injEq] at ht
      exact hne ht.symm

theorem BridgehubAsChainAssetHandlerWitness :
    Properties.BridgehubAsChainAssetHandlerWitness := by
  have hrun : Run cawCfg cawS0 cawOpsBridgehubAsHandler cawS3 :=
    Run.cons Step.setAssetDeploymentTracker
      (Run.cons (Step.registerCTMAssetOnL1 (by decide) ⟨Or.inr (by decide), by decide⟩ rfl)
        (Run.cons Step.setAddresses
          (Run.cons (Step.setCtmAssetHandlerAddressOnL1 ⟨Or.inr (by decide), by decide⟩)
            Run.nil)))
  refine ⟨cawS3, cawEnvBridgehubAsHandler, hrun, ?_, by decide, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, [1], prmRequest, [2], rfl, by decide, rfl, rfl, by decide⟩, by decide, by decide⟩
  rintro ⟨op, hop, t, ht, hne, _⟩
  simp only [cawOpsBridgehubAsHandler, cawOps, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl
  · exact nomatch ht
  · simp only [Op.handlerTriple, Option.some.injEq] at ht
    exact hne ht.symm
  · exact nomatch ht
  · simp only [Op.handlerTriple, Option.some.injEq] at ht
    exact hne ht.symm

theorem RepointingToChainAssetHandlerDisablesCheck :
    Properties.RepointingToChainAssetHandlerDisablesCheck := by
  have hlast : Run cawCfg cawS4 [.setCtmAssetHandlerAddressOnL1 30] cawS5 :=
    Run.cons (Step.setCtmAssetHandlerAddressOnL1 ⟨Or.inr (by decide), by decide⟩) Run.nil
  refine ⟨Run.cons Step.setAddresses hlast, by decide, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, by decide,
    ⟨by decide, by decide⟩, by decide, hlast, ?_, ⟨by decide, by decide⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, by decide⟩
  rintro ⟨op, hop, t, ht, hne, _⟩
  simp only [cawOpsRepoint, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl
  · exact nomatch ht
  · simp only [Op.handlerTriple, Option.some.injEq] at ht
    exact hne ht.symm

theorem CtmHandlerCollisionWitness : Properties.CtmHandlerCollisionWitness := by
  refine ⟨_, Run.cons Step.setAssetDeploymentTracker
      (Run.cons (Step.registerCTMAssetOnL1 (by decide) ⟨Or.inr (by decide), by decide⟩ rfl)
        (Run.cons (Step.register (by decide) ⟨Or.inl rfl, by decide⟩) Run.nil)),
    ⟨by decide, by decide⟩, ?_, by decide,
    ⟨.register 14 30 10, by simp, (1, 0x10004, 30), by decide, by decide, by decide⟩⟩
  intro op hop
  simp only [cawOps, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hop
  rcases hop with rfl | rfl | rfl <;> trivial

end Contracts.ChainAdmin.CtmAssetHandlerWriters
