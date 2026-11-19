import EraSpec.Contracts.NativeTokenVaultBase.Specs.RegistryAndEscrow

/-!
# History: the vault ledger had no per-chain enforcement at the pin `c67894b9`

**Record of an older commit, not a claim about `b17415d20`.**  At the pin `c67894b9` the L1 vault's
only ledger was the aggregate `bridgedOut`, and `NativeTokenVaultBase.bridgeMint`'s NatSpec said
"there is no on-chain per-chain balance enforcement".  The registry-and-escrow model
(`Specs/RegistryAndEscrow.lean`) has that ledger, and this statement shows, in the model, a run where
one chain is credited what only another chain sent.  At `b17415d20` the L1 vault also keeps
per-chain totals with a cap on withdrawals (L1NativeTokenVault `InteropPool`, `BulkheadIsolation`;
`BulkheadPendingChainUncapped` is the case still uncapped there), and the NatSpec sentence is gone.

Proofs are in `EraSpec.Contracts.NativeTokenVaultBase.History.Proofs.PerChainIsolation`.
-/

namespace Contracts.NativeTokenVault.History

/-- **PER-CHAIN ISOLATION DOES NOT HOLD.**  A two-chain run in which the aggregate
books balance exactly, yet chain `cA` bridged in an asset that only chain `cB` ever
had bridged out to it.

The ledger carries no chain index — `_handleBridgeToChain`'s chain parameter is
unnamed — so this is by design, with the sending chain's ZK proof standing where a
per-chain balance would. Stated here so that `Solvency` is not read as more than it
is. -/
def Properties.PerChainIsolationFails : Prop :=
  ∀ (e : NtvAssetId) (thisChain : Chain),
    ∀ (t : Address), t ≠ 0 → ∀ (cA cB : Chain), cA ≠ cB →
      ∃ W : World, Reach e thisChain empty W
        ∧ W.audit.totalIn (e thisChain t) = W.audit.totalOut (e thisChain t)
        ∧ W.audit.outTo cA (e thisChain t) = 0
        ∧ W.audit.innFrom cA (e thisChain t) = 1

end Contracts.NativeTokenVault.History
