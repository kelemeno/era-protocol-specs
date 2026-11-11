import EraSpec.Protocol.AssetBridgePreparation.Specs.Model

/-!
# The preparation trace against the registry model's flow audit

`Specs/Model.lean`'s trace keeps a ghost `pending` list: one obligation per successful
preparation, with its destination chain, asset and mint data.  The registry model of
the same vault (`Contracts.NativeTokenVault`, `Specs/RegistryAndEscrow.lean` of
`NativeTokenVaultBase`) keeps a separate ghost flow audit: per asset, the total
bridged out (`totalOut`) and in (`totalIn`), and the amount bridged out towards each
destination chain (`outTo`).  Neither is vault storage.

`Properties/RegistryCorrespondence.lean` relates the two along a trace that starts
from the tightened registration `registerFreshBranch'`
(`NativeTokenVaultBase/Specs/RegistrationUnified.lean`).  The only new definition is
the per-destination pending total it needs.

**This file is definitions only.**
-/

namespace AssetBridgePreparation

/-- The total pending amount towards destination chain `c`: the trace-side counterpart
of the registry audit's `outTo c`. -/
def pendingAmountTo (c : UInt256) (pending : List Obligation) : ℕ :=
  ((pending.filter fun o => decide (o.destinationChain = c)).map
    fun o => o.data.amount.val).sum

end AssetBridgePreparation
