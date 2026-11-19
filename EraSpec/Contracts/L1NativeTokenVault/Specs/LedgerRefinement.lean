import EraSpec.Contracts.L1NativeTokenVault.Specs.InteropPool
import EraSpec.Contracts.NativeTokenVaultBase.Specs.TrackerHooks
import EraSpec.Contracts.NativeTokenVaultBase.Specs.EscrowLedgerAtHead

/-!
# Refinement: the `b17415d20` vault ledger against the `bridgedOut`-only models

Source: era-contracts `draft/v0.35.0` head `b17415d20`, `l1-contracts/contracts/bridge/ntv/
L1NativeTokenVault.sol` (`L1NTV`).

`InteropPool` (`Specs/InteropPool.lean`) is the canonical model of the L1 vault's ledger at
`b17415d20`: `bridgedOut` together with the per-chain totals, the backfill and the interop pool.
Three older models keep `bridgedOut` alone:

* `NativeTokenVaultBase.L1Ledger` with the hooks `l1ToChain` and `l1FromChain`
  (`NativeTokenVaultBase/Specs/TrackerHooks.lean`): the hooks the vault model's preparation and
  resolution use on L1;
* the registry-and-escrow model `Contracts.NativeTokenVault` (`NativeTokenVaultBase/Specs/
  RegistryAndEscrow.lean`), whose `bridgeOut` and `bridgeIn` move `bridgedOut` with the escrow;
* its extension with `populateBridgedOut`, `EscrowLedgerAtHead` (`populateAtHead`).

At `b17415d20` the two hooks (`L1NTV:424-433`, `:439-459`) first update `bridgedOut` exactly as at
the pin and then, for a tracked chain balance, the per-chain totals, with a cap check that can only
revert.  This file states the relation used to compare them: the `bridgedOut` maps agree.  The
results (`Properties/LedgerRefinement.lean`) show that every successful hook or population of
`InteropPool` is the corresponding step of each older model on `bridgedOut`, that its other calls
leave `bridgedOut` alone, and that the converse fails: the per-chain cap rejects a withdrawal the
`bridgedOut`-only hook accepts.  So results about `bridgedOut` in the older models that hold for
every hook call cover the `b17415d20` hooks, and results about the per-chain totals live in
`InteropPool` and `BulkheadIsolation` only.
-/

namespace Contracts.L1NativeTokenVault.LedgerRefinement

open Contracts.L1NativeTokenVault.InteropPool

/-- The `L1Ledger`'s `bridgedOut` words are `InteropPool`'s `bridgedOut` values. -/
def L1LedgerMatches (acc : NativeTokenVaultBase.L1Ledger) (s : PoolSys) : Prop :=
  ∀ b, (acc.bridgedOut b).val = s.bridgedOut b

/-- The registry model's `bridgedOut` is `InteropPool`'s. -/
def RegistryLedgerMatches (V : NativeTokenVault.Vault) (s : PoolSys) : Prop :=
  V.bridgedOut = s.bridgedOut

/-- The `InteropPool` calls that write `bridgedOut`: the two hooks and one entry of
`populateBridgedOut`. -/
def WritesBridgedOut : PoolCall → Prop
  | .toChain .. => True
  | .fromChain .. => True
  | .populateBridgedOut .. => True
  | _ => False

end Contracts.L1NativeTokenVault.LedgerRefinement
