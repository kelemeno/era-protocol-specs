import EraSpec.Contracts.NativeTokenVaultBase.Specs.RepresentationPreparation

set_option linter.unusedVariables false

namespace Contracts.NativeTokenVaultBase

variable {Accounting : Type}

abbrev Properties.wrong_router_rejected {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} (h : r.caller ≠ s.config.router) := prepare hooks s r = none

abbrev Properties.paused_preparation_rejected {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} (h : s.paused = true) := prepare hooks s r = none

abbrev Properties.zero_amount_rejected {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} (h : r.data.amount = 0) := prepare hooks s r = none

abbrev Properties.wrong_asset_rejected {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} (hw : WellFormed s) (h : r.assetId ≠ s.config.assetId) :=
  prepare hooks s r = none

end Contracts.NativeTokenVaultBase
