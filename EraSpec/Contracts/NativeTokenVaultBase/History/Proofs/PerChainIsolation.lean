import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistryAndEscrow
import EraSpec.Contracts.NativeTokenVaultBase.History.Properties.PerChainIsolation

/-! # Proofs: no per-chain enforcement in the pin's ledger (History) -/

namespace Contracts.NativeTokenVault.History

theorem PerChainIsolationFails : Properties.PerChainIsolationFails :=
  fun _ _ _ ht0 _ _ hAB =>
    ⟨_, (per_chain_isolation_fails ht0 hAB).1, (per_chain_isolation_fails ht0 hAB).2.1,
      (per_chain_isolation_fails ht0 hAB).2.2.1, (per_chain_isolation_fails ht0 hAB).2.2.2⟩

end Contracts.NativeTokenVault.History
