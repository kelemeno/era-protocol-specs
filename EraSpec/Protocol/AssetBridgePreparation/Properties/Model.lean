import EraSpec.Protocol.AssetBridgePreparation.Specs.Model

set_option linter.unusedVariables false

namespace AssetBridgePreparation

open Contracts
variable {Accounting : Type}

/-- Every burn moves exactly its amount from circulating supply into the trace's
pending liability, for arbitrary numbers of transfers and interleaved spending. -/
abbrev Properties.reachable_conservation {hooks : NativeTokenVaultBase.Hooks Accounting}
    {s t : Ledger Accounting} (hw : NativeTokenVaultBase.WellFormed s.vault)
    (h : Reach hooks s t) :=
  NativeTokenVaultBase.WellFormed t.vault ∧
  t.vault.token.totalSupply + pendingAmount t.pending =
    s.vault.token.totalSupply + pendingAmount s.pending ∧ t.vault.config = s.vault.config

/-- Starting with no pending claims, their total never exceeds the initial
source supply. This does not claim a router cannot publish the same data twice. -/
abbrev Properties.pending_backed_by_initial_supply {hooks : NativeTokenVaultBase.Hooks Accounting}
    {s t : Ledger Accounting} (hw : NativeTokenVaultBase.WellFormed s.vault)
    (he : s.pending = []) (h : Reach hooks s t) :=
  pendingAmount t.pending ≤ s.vault.token.totalSupply

/-- Later preparation and ordinary spending cannot replace previously prepared
data, including beneficiary, amount, asset, or destination. -/
abbrev Properties.prepared_data_persists {hooks : NativeTokenVaultBase.Hooks Accounting}
    {s t : Ledger Accounting} (h : Reach hooks s t) :=
  ∃ later, t.pending = s.pending ++ later

end AssetBridgePreparation
