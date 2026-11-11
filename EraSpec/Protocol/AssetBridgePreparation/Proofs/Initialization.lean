import EraSpec.Protocol.AssetBridgePreparation.Properties.Initialization
import EraSpec.Protocol.AssetBridgePreparation.Proofs.Model
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.Initialization
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Model

namespace AssetBridgePreparation

open Contracts
variable {Accounting : Type}

theorem initialized_preparation_trace
    {initHooks : NativeTokenVaultBase.RegistrationHooks Accounting}
    {start : NativeTokenVaultBase.RegistrationState Accounting}
    {origin : NativeTokenVaultBase.Address} {registered : NativeTokenVaultBase.Registered Accounting}
    {fundedToken : BridgedStandardERC20.State} {hooks : NativeTokenVaultBase.Hooks Accounting}
    {t : Ledger Accounting}
    (hi : NativeTokenVaultBase.registerFreshBranch initHooks start origin = some registered)
    (ht : BridgedStandardERC20.Reach registered.state.token fundedToken)
    (hp : Reach hooks ⟨{ registered.state with token := fundedToken }, []⟩ t) :
    Properties.initialized_preparation_trace hi ht hp := by
  have hinner := (NativeTokenVaultBase.fresh_registration_preconditions hi).2
  have hw := NativeTokenVaultBase.registration_establishes_wellformed hinner
  obtain ⟨hfunded, hconfig⟩ := BridgedStandardERC20.reachable_ledger hw.1 ht
  have hs : NativeTokenVaultBase.WellFormed { registered.state with token := fundedToken } := by
    refine ⟨hfunded, ?_, ?_, hw.2.2.2⟩
    · exact (congrArg BridgedStandardERC20.Config.vault hconfig).trans hw.2.1
    · exact (congrArg BridgedStandardERC20.Config.assetId hconfig).trans hw.2.2.1
  obtain ⟨hfinal, hsum, _hc⟩ := reachable_conservation
    (s := ⟨{ registered.state with token := fundedToken }, []⟩) (t := t) (hooks := hooks) hs hp
  exact ⟨hfinal.1, hfinal.2, hsum⟩

end AssetBridgePreparation
