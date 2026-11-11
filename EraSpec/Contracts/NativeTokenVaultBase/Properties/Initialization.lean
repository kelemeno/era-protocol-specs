import EraSpec.Contracts.NativeTokenVaultBase.Specs.Initialization

set_option linter.unusedVariables false

namespace Contracts.NativeTokenVaultBase

variable {Accounting : Type}

/-- The consistency base case requires no prior agreement between token and
vault and no assumed correctness of the old registry entries being installed. -/
abbrev Properties.registration_establishes_representation {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) := RepresentationConsistent out.state

abbrev Properties.registration_establishes_ledger {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) := LedgerInvariant out.state

abbrev Properties.registration_establishes_wellformed {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) := WellFormed out.state

abbrev Properties.registration_initial_fields {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) :=
  out.state.token.config.originToken = origin ∧ origin ≠ 0 ∧ out.tokenVersion = 1 ∧
  out.state.token.totalSupply = 0 ∧ (∀ a, out.state.token.balances a = 0)

/-- Other keys are unchanged. This is a map-frame theorem, not a proof that two
different assets cannot share the target token address. -/
abbrev Properties.registration_registry_frame {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) :=
  out.state.config = s.config ∧ out.state.paused = s.paused ∧
  (∀ asset, asset ≠ s.config.assetId →
    out.state.registry.tokenForAsset asset = s.registry.tokenForAsset asset) ∧
  (∀ token, token ≠ s.config.tokenAddress →
    out.state.registry.assetForToken token = s.registry.assetForToken token)

abbrev Properties.registration_hook_snapshot {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) :=
  hooks.registerTracker s.accounting out.state.registry out.state.token
    s.config.assetId s.config.originChainId = some out.state.accounting

abbrev Properties.registration_checks_asset {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) :=
  s.config.assetId = hooks.assetIdFor s.config.originChainId origin ∧
  s.config.originChainId ≠ s.config.chainId

abbrev Properties.failed_tracker_registration {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address}
    (h : ∀ registry token, hooks.registerTracker s.accounting registry token
      s.config.assetId s.config.originChainId = none) :=
  registerRepresentation hooks s origin = none

abbrev Properties.existing_asset_not_freshly_deployed {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address}
    (h : s.registry.tokenForAsset s.config.assetId ≠ 0) := registerFreshBranch hooks s origin = none

/-- The outer new-token branch really starts at a missing forward slot and runs
the checked deployment/initialization/registration helper. -/
abbrev Properties.fresh_registration_preconditions {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerFreshBranch hooks s origin = some out) :=
  s.registry.tokenForAsset s.config.assetId = 0 ∧ registerRepresentation hooks s origin = some out

abbrev Properties.registration_enabled {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {accounting : Accounting}
    (ha : s.config.assetId = hooks.assetIdFor s.config.originChainId origin)
    (hc : s.config.originChainId ≠ s.config.chainId) (ho : origin ≠ 0)
    (hm : hooks.metadataDecoded = true)
    (hd : hooks.deploy s.config.originChainId origin = some s.config.tokenAddress)
    (ht : hooks.registerTracker s.accounting
      (installRegistry s.registry s.config.assetId s.config.tokenAddress)
      (registeredToken s.config origin) s.config.assetId s.config.originChainId = some accounting) :=
  ∃ out, registerRepresentation hooks s origin = some out

/-- Countermodel: a fresh public initializer binds whoever called it. Supplying
a different caller than the intended vault breaks the cross-contract agreement.
The intended atomic deployment path avoids this by making the vault the caller. -/
abbrev Properties.wrong_initializer_caller_breaks_consistency (s : RegistrationState Accounting)
    (actualCaller origin : Address) (hc : actualCaller ≠ s.config.vault) (ho : origin ≠ 0) :=
  ∃ token, BridgedStandardERC20.initializeToken BridgedStandardERC20.freshProxy actualCaller
    s.config.assetId origin true = some token ∧
    ¬ RepresentationConsistent ⟨s.config,
      installRegistry s.registry s.config.assetId s.config.tokenAddress,
      s.paused, token.token, s.accounting⟩

end Contracts.NativeTokenVaultBase
