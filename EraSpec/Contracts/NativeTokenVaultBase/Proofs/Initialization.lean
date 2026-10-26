import EraSpec.Contracts.NativeTokenVaultBase.Properties.Initialization
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Initialization

namespace Contracts.NativeTokenVaultBase

variable {Accounting : Type}

private theorem registration_view {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) :
    (s.config.assetId = hooks.assetIdFor s.config.originChainId origin ∧
      s.config.originChainId ≠ s.config.chainId) ∧
    ∃ deployed initialized accounting,
      hooks.deploy s.config.originChainId origin = some deployed ∧
      BridgedStandardERC20.initializeToken BridgedStandardERC20.freshProxy
        s.config.vault s.config.assetId origin hooks.metadataDecoded = some initialized ∧
      deployed = s.config.tokenAddress ∧
      hooks.registerTracker s.accounting (installRegistry s.registry s.config.assetId deployed)
        initialized.token s.config.assetId s.config.originChainId = some accounting ∧
      out = ⟨⟨s.config, installRegistry s.registry s.config.assetId deployed, s.paused,
        initialized.token, accounting⟩, initialized.version⟩ := by
  unfold registerRepresentation at h
  split at h
  · rename_i hg
    cases hd : hooks.deploy s.config.originChainId origin with
    | none => simp only [hd] at h
    | some deployed =>
      simp only [hd] at h
      cases hi : BridgedStandardERC20.initializeToken BridgedStandardERC20.freshProxy
          s.config.vault s.config.assetId origin hooks.metadataDecoded with
      | none => simp only [hi] at h
      | some initialized =>
        simp only [hi] at h
        split at h
        · rename_i he
          cases ht : hooks.registerTracker s.accounting
              (installRegistry s.registry s.config.assetId deployed) initialized.token
              s.config.assetId s.config.originChainId with
          | none => simp only [ht] at h
          | some accounting =>
            simp only [ht] at h
            exact ⟨hg, deployed, initialized, accounting, rfl, rfl, he,
              ht, (Option.some.inj h).symm⟩
        · cases h
  · cases h

private theorem fresh_ledger : BridgedStandardERC20.WellFormed BridgedStandardERC20.freshProxy.token := by
  refine ⟨?_, ?_, rfl⟩
  · exact Finset.sum_const_zero
  · norm_num [BridgedStandardERC20.freshProxy, BridgedStandardERC20.empty, UInt256.size]

theorem registration_establishes_representation {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) :
    Properties.registration_establishes_representation h := by
  obtain ⟨_hc, deployed, initialized, accounting, _hd, hi, he, _ht, rfl⟩ := registration_view h
  rcases BridgedStandardERC20.initialization_binds_inputs hi with ⟨hv, ha, _, _, _⟩
  refine ⟨hv, ha, ?_, ?_⟩
  · exact (Function.update_same _ _ _).trans he
  · dsimp only [installRegistry]
    rw [← he]
    exact Function.update_same _ _ _

theorem registration_establishes_ledger {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) :
    Properties.registration_establishes_ledger h := by
  obtain ⟨_hc, deployed, initialized, accounting, _hd, hi, _he, _ht, rfl⟩ := registration_view h
  exact BridgedStandardERC20.initialization_preserves_ledger fresh_ledger hi

theorem registration_establishes_wellformed {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) :
    Properties.registration_establishes_wellformed h :=
  ⟨registration_establishes_ledger h, registration_establishes_representation h⟩

theorem registration_initial_fields {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) : Properties.registration_initial_fields h := by
  obtain ⟨_hc, deployed, initialized, accounting, _hd, hi, _he, _ht, rfl⟩ := registration_view h
  rcases BridgedStandardERC20.initialization_binds_inputs hi with ⟨_, _, ho, hn, hv⟩
  rcases BridgedStandardERC20.initialization_preserves_balances hi with ⟨hb, hs⟩
  refine ⟨ho, hn, hv, hs, ?_⟩
  intro a
  exact congrFun hb a

theorem registration_registry_frame {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) : Properties.registration_registry_frame h := by
  obtain ⟨_hc, deployed, initialized, accounting, _hd, _hi, he, _ht, rfl⟩ := registration_view h
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro asset ha
    exact Function.update_noteq ha _ _
  · intro token ht
    have hn : token ≠ deployed := by simpa only [he] using ht
    exact Function.update_noteq hn _ _

theorem registration_hook_snapshot {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) : Properties.registration_hook_snapshot h := by
  obtain ⟨_hc, deployed, initialized, accounting, _hd, _hi, _he, ht, rfl⟩ := registration_view h
  exact ht

theorem registration_checks_asset {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) : Properties.registration_checks_asset h :=
  (registration_view h).1

theorem failed_tracker_registration {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address}
    (h : ∀ registry token, hooks.registerTracker s.accounting registry token
      s.config.assetId s.config.originChainId = none) :
    Properties.failed_tracker_registration (origin := origin) h := by
  unfold Properties.failed_tracker_registration
  cases hr : registerRepresentation hooks s origin with
  | none => rfl
  | some out =>
    obtain ⟨_hc, deployed, initialized, accounting, _hd, _hi, _he, ht, _hout⟩ := registration_view hr
    rw [h] at ht
    cases ht

theorem existing_asset_not_freshly_deployed {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address}
    (h : s.registry.tokenForAsset s.config.assetId ≠ 0) :
    Properties.existing_asset_not_freshly_deployed (hooks := hooks) (origin := origin) h := by
  exact if_neg h

theorem fresh_registration_preconditions {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerFreshBranch hooks s origin = some out) : Properties.fresh_registration_preconditions h := by
  unfold registerFreshBranch at h
  split at h
  · rename_i hf
    exact ⟨hf, h⟩
  · cases h

theorem registration_enabled {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {accounting : Accounting}
    (ha : s.config.assetId = hooks.assetIdFor s.config.originChainId origin)
    (hc : s.config.originChainId ≠ s.config.chainId) (ho : origin ≠ 0)
    (hm : hooks.metadataDecoded = true)
    (hd : hooks.deploy s.config.originChainId origin = some s.config.tokenAddress)
    (ht : hooks.registerTracker s.accounting
      (installRegistry s.registry s.config.assetId s.config.tokenAddress)
      (registeredToken s.config origin) s.config.assetId s.config.originChainId = some accounting) :
    Properties.registration_enabled ha hc ho hm hd ht := by
  have hg : s.config.assetId = hooks.assetIdFor s.config.originChainId origin ∧
      s.config.originChainId ≠ s.config.chainId := ⟨ha, hc⟩
  have hi : BridgedStandardERC20.initializeToken BridgedStandardERC20.freshProxy s.config.vault
      s.config.assetId origin hooks.metadataDecoded = some ⟨registeredToken s.config origin, 1⟩ := by
    simp [BridgedStandardERC20.initializeToken, BridgedStandardERC20.InitializeAllowed,
      BridgedStandardERC20.freshProxy, BridgedStandardERC20.empty, registeredToken, ho, hm]
  unfold Properties.registration_enabled
  simp only [registerRepresentation, if_pos hg, hd, hi, if_pos rfl, ht]
  exact ⟨_, rfl⟩

theorem wrong_initializer_caller_breaks_consistency (s : RegistrationState Accounting)
    (actualCaller origin : Address) (hc : actualCaller ≠ s.config.vault) (ho : origin ≠ 0) :
    Properties.wrong_initializer_caller_breaks_consistency s actualCaller origin hc ho := by
  obtain ⟨token, hi, _hw, _hs, _hb⟩ :=
    BridgedStandardERC20.fresh_initialization_enabled actualCaller origin s.config.assetId ho
  refine ⟨token, hi, ?_⟩
  intro hr
  have hv := (BridgedStandardERC20.initialization_binds_inputs hi).1
  exact hc (hv.symm.trans hr.1)

end Contracts.NativeTokenVaultBase
