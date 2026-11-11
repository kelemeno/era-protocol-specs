import EraSpec.Contracts.BridgedStandardERC20.Specs.Initialization

set_option linter.unusedVariables false

namespace Contracts.BridgedStandardERC20

abbrev Properties.initialization_binds_inputs {s t : InitState} {caller origin : Address}
    {asset : UInt256} {decoded : Bool}
    (h : initializeToken s caller asset origin decoded = some t) :=
  t.token.config.vault = caller ∧ t.token.config.assetId = asset ∧
  t.token.config.originToken = origin ∧ origin ≠ 0 ∧ t.version = 1

/-- Initialization does not clear an existing ledger, even if its values are bad. -/
abbrev Properties.initialization_preserves_balances {s t : InitState} {caller origin : Address}
    {asset : UInt256} {decoded : Bool}
    (h : initializeToken s caller asset origin decoded = some t) :=
  t.token.balances = s.token.balances ∧ t.token.totalSupply = s.token.totalSupply

abbrev Properties.initialization_preserves_ledger {s t : InitState} {caller origin : Address}
    {asset : UInt256} {decoded : Bool} (hw : WellFormed s.token)
    (h : initializeToken s caller asset origin decoded = some t) := WellFormed t.token

abbrev Properties.fresh_initialization_enabled (caller origin : Address) (asset : UInt256)
    (ho : origin ≠ 0) :=
  ∃ t, initializeToken freshProxy caller asset origin true = some t ∧
    WellFormed t.token ∧ t.token.totalSupply = 0 ∧ (∀ a, t.token.balances a = 0)

/-- A completed top-level initialization cannot be repeated by another caller. -/
abbrev Properties.initialization_once {s t : InitState} {caller origin : Address}
    {asset : UInt256} {decoded : Bool}
    (h : initializeToken s caller asset origin decoded = some t)
    (nextCaller nextOrigin : Address) (nextAsset : UInt256) (nextDecoded : Bool) :=
  initializeToken t nextCaller nextAsset nextOrigin nextDecoded = none

abbrev Properties.implementation_initialization_disabled (caller origin : Address)
    (asset : UInt256) (decoded : Bool) :=
  initializeToken disabledImplementation caller asset origin decoded = none

abbrev Properties.failed_metadata_initialization {s : InitState} (caller origin : Address)
    (asset : UInt256) := initializeToken s caller asset origin false = none

end Contracts.BridgedStandardERC20
