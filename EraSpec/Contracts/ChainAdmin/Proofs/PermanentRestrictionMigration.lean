import EraSpec.Contracts.ChainAdmin.Properties.PermanentRestrictionMigration

/-!
# Proofs: when `PermanentRestriction` checks a migration, and why it never does

`_getNewAdminFromMigration` is a cascade of early returns.  `newAdminFromMigrationWith_cases`
splits every call into the four ways through it; on a migration request the result is
`afterRequest`, the tail that reads the asset id (`newAdminFromMigrationWith_of_request`).
Every property is a computation on those two lemmas.
-/

namespace Contracts.ChainAdmin.PermanentRestrictionMigration

/-! ## The four ways through `_getNewAdminFromMigration` -/

/-- The tail of `_getNewAdminFromMigration` after the asset id is decoded (:348-364). -/
def afterRequest (A : Abi) (E : Env) (expectedHandler : Address) (chainAssetId : AssetId)
    (bridgehubData : Bytes) : MigrationRead :=
  if E.ctmAssetIdToAddress chainAssetId = 0 then .notMigration
  else if E.assetHandlerAddress chainAssetId ≠ expectedHandler then .notMigration
  else
    match burnAdmin A bridgehubData with
    | none => .reverts
    | some l2Admin => .migration l2Admin

lemma selector_append (args : Bytes) :
    ¬ (requestL2TransactionTwoBridgesSelector ++ args).length < 4 ∧
    selectorOf (requestL2TransactionTwoBridgesSelector ++ args) =
      requestL2TransactionTwoBridgesSelector ∧
    argsOf (requestL2TransactionTwoBridgesSelector ++ args) = args := by
  simp [requestL2TransactionTwoBridgesSelector, selectorOf, argsOf]

lemma newAdminFromMigrationWith_cases (A : Abi) (E : Env) (c : Call) :
    (∀ x, newAdminFromMigrationWith A E x c = .notMigration) ∨
    (c.target = E.bridgehub ∧
      ∃ args, c.data = requestL2TransactionTwoBridgesSelector ++ args ∧
        A.decodeTwoBridges args = none ∧ ∀ x, newAdminFromMigrationWith A E x c = .reverts) ∨
    (c.target = E.bridgehub ∧
      ∃ (args : Bytes) (request : TwoBridgesRequest) (encodedData : Bytes),
        c.data = requestL2TransactionTwoBridgesSelector ++ args ∧
        A.decodeTwoBridges args = some request ∧
        request.secondBridgeAddress = E.assetRouter ∧
        request.secondBridgeCalldata = NEW_ENCODING_VERSION :: encodedData ∧
        A.decodeAssetData encodedData = none ∧
        ∀ x, newAdminFromMigrationWith A E x c = .reverts) ∨
    (∃ (chainAssetId : AssetId) (bridgehubData : Bytes),
      MigrationRequest A E c chainAssetId bridgehubData ∧
      ∀ x, newAdminFromMigrationWith A E x c = afterRequest A E x chainAssetId bridgehubData) := by
  by_cases h1 : c.target = E.bridgehub
  swap
  · left; intro x; simp [newAdminFromMigrationWith, h1]
  by_cases h2 : c.data.length < 4
  · left; intro x; simp [newAdminFromMigrationWith, h1, h2]
  by_cases h3 : selectorOf c.data = requestL2TransactionTwoBridgesSelector
  swap
  · left; intro x; simp [newAdminFromMigrationWith, h1, h2, h3]
  have hd : c.data = requestL2TransactionTwoBridgesSelector ++ argsOf c.data := by
    rw [← h3]; exact (List.take_append_drop 4 c.data).symm
  rcases hreq : A.decodeTwoBridges (argsOf c.data) with _ | request
  · right; left
    exact ⟨h1, argsOf c.data, hd, hreq, fun x => by simp [newAdminFromMigrationWith, h1, h2, h3, hreq]⟩
  by_cases h4 : request.secondBridgeAddress = E.assetRouter
  swap
  · left; intro x; simp [newAdminFromMigrationWith, h1, h2, h3, hreq, h4]
  rcases hsb : request.secondBridgeCalldata with _ | ⟨version, encodedData⟩
  · left; intro x; simp [newAdminFromMigrationWith, h1, h2, h3, hreq, h4, hsb]
  by_cases h5 : version = NEW_ENCODING_VERSION
  swap
  · left; intro x; simp [newAdminFromMigrationWith, h1, h2, h3, hreq, h4, hsb, h5]
  subst h5
  rcases hdec : A.decodeAssetData encodedData with _ | ⟨chainAssetId, bridgehubData⟩
  · right; right; left
    exact ⟨h1, argsOf c.data, request, encodedData, hd, hreq, h4, hsb, hdec,
      fun x => by simp [newAdminFromMigrationWith, h1, h2, h3, hreq, h4, hsb, hdec]⟩
  · right; right; right
    refine ⟨chainAssetId, bridgehubData,
      ⟨h1, argsOf c.data, request, encodedData, hd, hreq, h4, hsb, hdec⟩, fun x => ?_⟩
    simp only [newAdminFromMigrationWith, afterRequest, h1, h2, h3, hreq, h4, hsb, hdec,
      ne_eq, not_true_eq_false, ite_false, ite_not]
    rcases hb : A.decodeBurnData bridgehubData with _ | burnData
    · simp [burnAdmin, hb]
    · rcases ha : A.decodeAdminAndBytes burnData.ctmData with _ | ⟨l2Admin, rest⟩
      · simp [burnAdmin, hb, ha]
      · simp [burnAdmin, hb, ha]

/-- On a migration request, `_getNewAdminFromMigration` is the tail that reads the asset
id, whatever handler it expects. -/
lemma newAdminFromMigrationWith_of_request {A : Abi} {E : Env} {c : Call}
    {chainAssetId : AssetId} {bridgehubData : Bytes}
    (h : MigrationRequest A E c chainAssetId bridgehubData) (x : Address) :
    newAdminFromMigrationWith A E x c = afterRequest A E x chainAssetId bridgehubData := by
  obtain ⟨h1, args, request, encodedData, hd, hreq, h4, hsb, hdec⟩ := h
  obtain ⟨h2, h3, hargs⟩ := selector_append args
  rw [← hd] at h2 h3 hargs
  simp only [newAdminFromMigrationWith, afterRequest, h1, h2, h3, hargs, hreq, h4, hsb, hdec,
    ne_eq, not_true_eq_false, ite_false, ite_not]
  rcases hb : A.decodeBurnData bridgehubData with _ | burnData
  · simp [burnAdmin, hb]
  · rcases ha : A.decodeAdminAndBytes burnData.ctmData with _ | ⟨l2Admin, rest⟩
    · simp [burnAdmin, hb, ha]
    · simp [burnAdmin, hb, ha]

/-- `validateCallWith` passes only if its migration check passes. -/
lemma migration_of_validateCallWith {A : Abi} {E : Env} {x chainAdmin : Address} {c : Call}
    (h : validateCallWith A E x chainAdmin c = true) : validateMigrationToL2With A E x c = true := by
  unfold validateCallWith at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

/-- On a migration request whose handler is the expected one and whose id has a CTM, the
migration check passes only with a whitelisted admin. -/
lemma whitelisted_of_check {A : Abi} {E : Env} {x : Address} {c : Call} {chainAssetId : AssetId}
    {bridgehubData : Bytes} (hr : MigrationRequest A E c chainAssetId bridgehubData)
    (hc : E.ctmAssetIdToAddress chainAssetId ≠ 0) (hh : E.assetHandlerAddress chainAssetId = x)
    (hm : validateMigrationToL2With A E x c = true) :
    ∃ l2Admin, burnAdmin A bridgehubData = some l2Admin ∧ E.allowedL2Admins l2Admin = true := by
  unfold validateMigrationToL2With at hm
  rw [newAdminFromMigrationWith_of_request hr, afterRequest] at hm
  rcases hb : burnAdmin A bridgehubData with _ | l2Admin
  · simp [hc, hh, hb] at hm
  · simp [hc, hh, hb] at hm
    exact ⟨l2Admin, rfl, hm⟩

/-! ## (a) When the check fires -/

theorem MigrationCheckFiresIff : Properties.MigrationCheckFiresIff := by
  intro A E c l2Admin
  unfold newAdminFromMigration
  constructor
  · intro h
    rcases newAdminFromMigrationWith_cases A E c with
      h0 | ⟨_, _, _, _, h0⟩ | ⟨_, _, _, _, _, _, _, _, _, h0⟩ | ⟨chainAssetId, bridgehubData, hr, h0⟩
    · rw [h0] at h; cases h
    · rw [h0] at h; cases h
    · rw [h0] at h; cases h
    · refine ⟨chainAssetId, bridgehubData, hr, ?_⟩
      rw [h0, afterRequest] at h
      by_cases hc : E.ctmAssetIdToAddress chainAssetId = 0
      · simp [hc] at h
      by_cases hh : E.assetHandlerAddress chainAssetId = E.bridgehub
      swap
      · simp [hc, hh] at h
      rcases hb : burnAdmin A bridgehubData with _ | a
      · simp [hc, hh, hb] at h
      · simp [hc, hh, hb] at h
        exact ⟨hc, hh, h ▸ rfl⟩
  · rintro ⟨chainAssetId, bridgehubData, hr, hc, hh, hb⟩
    rw [newAdminFromMigrationWith_of_request hr, afterRequest]
    simp [hc, hh, hb]

theorem MigrationCheckOutcome : Properties.MigrationCheckOutcome := by
  intro A E c chainAssetId bridgehubData hr
  unfold validateMigrationToL2 validateMigrationToL2With
  rw [newAdminFromMigrationWith_of_request hr, afterRequest]
  by_cases hc : E.ctmAssetIdToAddress chainAssetId = 0
  · simp [hc]
  by_cases hh : E.assetHandlerAddress chainAssetId = E.bridgehub
  · rcases burnAdmin A bridgehubData with _ | l2Admin
    · simp [hc, hh]
    · simp [hc, hh]
  · simp [hc, hh]

theorem MigrationReadRevertsOnlyOnUndecodableData :
    Properties.MigrationReadRevertsOnlyOnUndecodableData := by
  intro A E c h
  unfold newAdminFromMigration at h
  rcases newAdminFromMigrationWith_cases A E c with
    h0 | ⟨h1, args, hd, hreq, _⟩ | ⟨h1, args, request, encodedData, hd, hreq, h4, hsb, hdec, _⟩ |
      ⟨chainAssetId, bridgehubData, hr, h0⟩
  · rw [h0] at h; cases h
  · exact ⟨h1, args, hd, Or.inl hreq⟩
  · exact ⟨h1, args, hd, Or.inr (Or.inl ⟨request, encodedData, hreq, h4, hsb, hdec⟩)⟩
  · obtain ⟨h1, args, _, _, hd, _⟩ := id hr
    refine ⟨h1, args, hd, Or.inr (Or.inr ⟨chainAssetId, bridgehubData, hr, ?_⟩)⟩
    rw [h0, afterRequest] at h
    by_cases hc : E.ctmAssetIdToAddress chainAssetId = 0
    · simp [hc] at h
    by_cases hh : E.assetHandlerAddress chainAssetId = E.bridgehub
    swap
    · simp [hc, hh] at h
    rcases hb : burnAdmin A bridgehubData with _ | a
    · rfl
    · simp [hc, hh, hb] at h

theorem MigrationRequestPassesOtherChecks : Properties.MigrationRequestPassesOtherChecks := by
  intro A E chainAdmin x c ht hno hne
  unfold BridgehubAnswersNoChainId at hno
  have h1 : validateAsChainAdmin A E chainAdmin c = true := by
    have hnot : isAdminOfAChain E chainAdmin c.target = false := by
      rw [ht]; unfold isAdminOfAChain; split_ifs <;> simp [hno]
    simp [validateAsChainAdmin, hnot]
  have h2 : validateRemoveRestriction A E chainAdmin c = true := by
    simp [validateRemoveRestriction, ht, hne]
  refine ⟨h1, h2, ?_⟩
  simp [validateCallWith, h1, h2]

/-! ## (b) The deployed configuration -/

theorem HandlerOffBridgehubSkipsCheck : Properties.HandlerOffBridgehubSkipsCheck := by
  intro A E chainAdmin c chainAssetId bridgehubData hr hh hno hne
  have hm : newAdminFromMigration A E c = .notMigration := by
    unfold newAdminFromMigration
    rw [newAdminFromMigrationWith_of_request hr, afterRequest]
    simp [hh]
  refine ⟨hm, ?_⟩
  obtain ⟨_, _, h3⟩ := MigrationRequestPassesOtherChecks A E chainAdmin E.bridgehub c hr.1 hno hne
  unfold validateCall
  rw [h3]
  unfold newAdminFromMigration at hm
  unfold validateMigrationToL2With
  rw [hm]

theorem DeployedConfigDisablesMigrationCheck :
    Properties.DeployedConfigDisablesMigrationCheck := by
  intro A E chainAdmin c chainAssetId bridgehubData hr hcah hne' hno hne
  have hh : E.assetHandlerAddress chainAssetId ≠ E.bridgehub := by rw [hcah]; exact hne'
  refine ⟨(HandlerOffBridgehubSkipsCheck A E chainAdmin c chainAssetId bridgehubData hr hh hno
    hne).1, fun allowed => ?_⟩
  exact (HandlerOffBridgehubSkipsCheck A { E with allowedL2Admins := allowed } chainAdmin c
    chainAssetId bridgehubData hr hh hno hne).2

/-! ## (c) The Bridgehub as handler -/

theorem HandlerIsBridgehubForcesWhitelist : Properties.HandlerIsBridgehubForcesWhitelist := by
  intro A E chainAdmin c chainAssetId bridgehubData hr hc hh hv
  exact whitelisted_of_check hr hc hh (migration_of_validateCallWith hv)

theorem HandlerIsBridgehubCheckIsTheWhitelist :
    Properties.HandlerIsBridgehubCheckIsTheWhitelist := by
  intro A E chainAdmin c chainAssetId bridgehubData hr hc hh hno hne
  obtain ⟨_, _, h3⟩ := MigrationRequestPassesOtherChecks A E chainAdmin E.bridgehub c hr.1 hno hne
  unfold validateCall
  rw [h3]
  have hout := MigrationCheckOutcome A E c chainAssetId bridgehubData hr
  unfold validateMigrationToL2 at hout
  rw [hout]
  simp [hc, hh]

/-! ## (e) The check never guards a migration that could succeed -/

theorem CheckedRequestsBurnAtBridgehub : Properties.CheckedRequestsBurnAtBridgehub := by
  intro A E c l2Admin hnz h
  obtain ⟨chainAssetId, bridgehubData, hr, _, hh, _⟩ := (MigrationCheckFiresIff A E c l2Admin).1 h
  exact ⟨chainAssetId, bridgehubData, hr, by simp [burnTarget, hh, hnz]⟩

theorem DeliverableMigrationsPassUnchecked :
    Properties.DeliverableMigrationsPassUnchecked := by
  intro A E chainAdmin c chainAssetId bridgehubData hbb hnz hr hdel hno hne
  have hh : E.assetHandlerAddress chainAssetId ≠ E.bridgehub := by
    intro hh
    have ht : burnTarget E chainAssetId = E.bridgehub := by simp [burnTarget, hh, hnz]
    rw [ht, hbb] at hdel
    exact Bool.false_ne_true hdel
  refine ⟨(HandlerOffBridgehubSkipsCheck A E chainAdmin c chainAssetId bridgehubData hr hh hno
    hne).1, fun allowed => ?_⟩
  exact (HandlerOffBridgehubSkipsCheck A { E with allowedL2Admins := allowed } chainAdmin c
    chainAssetId bridgehubData hr hh hno hne).2

/-! ## The repair -/

theorem RepairedCheckForcesWhitelist : Properties.RepairedCheckForcesWhitelist := by
  intro A E chainAdmin c chainAssetId bridgehubData hr hc hh hv
  exact whitelisted_of_check hr hc hh (migration_of_validateCallWith hv)

theorem RepairedCheckGuardsChainAssetHandlerBurns :
    Properties.RepairedCheckGuardsChainAssetHandlerBurns := by
  intro A E chainAdmin c chainAssetId bridgehubData hntv hr hc ht hv
  have hh : E.assetHandlerAddress chainAssetId = E.chainAssetHandler := by
    unfold burnTarget at ht
    split_ifs at ht
    · exact absurd ht hntv
    · exact ht
  exact RepairedCheckForcesWhitelist A E chainAdmin c chainAssetId bridgehubData hr hc hh hv

theorem RepairedAgreesOffMigrationRequests : Properties.RepairedAgreesOffMigrationRequests := by
  intro A E chainAdmin c hnot
  have heq : newAdminFromMigrationWith A E E.chainAssetHandler c =
      newAdminFromMigrationWith A E E.bridgehub c := by
    rcases newAdminFromMigrationWith_cases A E c with
      h0 | ⟨_, _, _, _, h0⟩ | ⟨_, _, _, _, _, _, _, _, _, h0⟩ | ⟨chainAssetId, bridgehubData, hr, _⟩
    · simp only [h0]
    · simp only [h0]
    · simp only [h0]
    · exact absurd hr (hnot chainAssetId bridgehubData)
  unfold validateCallRepaired validateCall validateCallWith validateMigrationToL2With
  rw [heq]

/-! ## Countermodel and witnesses -/

private lemma prmRequestOf (E : Env) (hb : E.bridgehub = 10) (ha : E.assetRouter = 12) :
    MigrationRequest prmAbi E prmCall 100 [3] :=
  ⟨hb ▸ rfl, [1], prmRequest, [2], rfl, by decide, ha ▸ rfl, rfl, by decide⟩

theorem PRMigrationDeployedCountermodel : Properties.PRMigrationDeployedCountermodel := by
  refine ⟨prmRequestOf prmEnv rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | exact rfl

theorem PRMigrationHandlerIsBridgehubWitness : Properties.PRMigrationHandlerIsBridgehubWitness := by
  refine ⟨prmRequestOf prmEnvHandlerIsBridgehub rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | decide | exact rfl

theorem MigrationWhitelistGuaranteeFails : Properties.MigrationWhitelistGuaranteeFails := by
  intro h
  obtain ⟨hr, hb, hw, hc, -, -, -, -, -, -, -, -, hv⟩ := PRMigrationDeployedCountermodel
  obtain ⟨l2Admin, hb', hw'⟩ := h prmAbi prmEnv 20 prmCall 100 [3] hr hc hv
  rw [hb] at hb'
  cases hb'
  rw [hw] at hw'
  exact Bool.false_ne_true hw'

theorem PRMigrationRepairWitness : Properties.PRMigrationRepairWitness := by
  refine ⟨by decide, by decide, by decide, by decide, fun chainAssetId bridgehubData h => ?_⟩
  exact absurd h.1 (by decide)

theorem PRMigrationUndecodableWitness : Properties.PRMigrationUndecodableWitness := by
  refine ⟨?_, ?_⟩ <;> decide

end Contracts.ChainAdmin.PermanentRestrictionMigration
