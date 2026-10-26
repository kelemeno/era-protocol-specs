import EraSpec.Protocol.AssetBridgePreparation.Specs.Model
import EraSpec.Contracts.NativeTokenVaultBase.Specs.Initialization

set_option linter.unusedVariables false

namespace AssetBridgePreparation

open Contracts
variable {Accounting : Type}

/-- Derive the invariants from registration, then preserve them through local
token operations and preparation/spending traces. No input WellFormed or
RepresentationConsistent hypothesis is required. The token phase may mint under
its vault guard; its cross-chain funding authorization is a separate obligation. -/
abbrev Properties.initialized_preparation_trace
    {initHooks : NativeTokenVaultBase.RegistrationHooks Accounting}
    {start : NativeTokenVaultBase.RegistrationState Accounting}
    {origin : NativeTokenVaultBase.Address} {registered : NativeTokenVaultBase.Registered Accounting}
    {fundedToken : BridgedStandardERC20.State} {hooks : NativeTokenVaultBase.Hooks Accounting}
    {t : Ledger Accounting}
    (hi : NativeTokenVaultBase.registerFreshBranch initHooks start origin = some registered)
    (ht : BridgedStandardERC20.Reach registered.state.token fundedToken)
    (hp : Reach hooks ⟨{ registered.state with token := fundedToken }, []⟩ t) :=
  NativeTokenVaultBase.LedgerInvariant t.vault ∧
  NativeTokenVaultBase.RepresentationConsistent t.vault ∧
  t.vault.token.totalSupply + pendingAmount t.pending = fundedToken.totalSupply

end AssetBridgePreparation
