import EraSpec.Protocol.AssetBridgePreparation.Specs.RegistryCorrespondence
import EraSpec.Contracts.NativeTokenVaultBase.Properties.RegistrationUnified

/-!
# Properties: the preparation trace is the registry model's recorded outflow

Statements about `Specs/RegistryCorrespondence.lean`; proofs are in
`Proofs/RegistryCorrespondence.lean`.

`TightTraceIsRegistryOutflow` takes the premises of `initialized_preparation_trace`
(`Properties/Initialization.lean`) with the tightened registration
`registerFreshBranch'` in place of `registerFreshBranch`, plus the registry-side
premises of `NativeTokenVaultBase.Properties.UnifiedLifecycleCorresponds`: a bounded
registry run from fresh storage under the bounded hash premise on its pairs, a
corresponding registration state, and agreeing asset encoders at the registered
pair.  It concludes that the whole composed run is simulated by a registry run in two
segments, registration plus funding (`Wf`) and then the trace (`W'`), such that:

* the registry vault is the registration's write throughout, `t` corresponds to it,
  and both models' invariants hold (`Valid`, `WellFormed`);
* at the end of funding, the funded supply plus the asset's recorded outflow equals
  its recorded inflow;
* during the trace the registry records no inflow of the asset, and its recorded
  outflow grows by exactly the trace's pending total — towards each destination chain
  `c`, by exactly the pending total towards `c`;
* every pending obligation is for the tracked asset;
* (as in `initialized_preparation_trace`) supply plus pending equals the funded supply.

`Wf` and `W'` are existential: they are the registry run the simulation builds, with
each funding mint mapped to a `bridgeIn`, each nonzero funding burn and each
preparation to a `bridgeOut` (a preparation's towards its own destination chain), and
transfers, zero burns and spends to no step.  So the trace's ghost pending list and
the ghost flow audit of that matching run count the same outflows.  This says nothing
about other registry runs from `W`, whose flows of a registered non-native asset the
registry model does not bound
(`NativeTokenVaultBase.Properties.LifecycleIdentityNotRegistryInvariant`).  Neither
ghost record is evidence of publication (`REP-PUBLISH`, `MODEL-TRACE`).

`TightTraceIsRegistryOutflowSatisfiable` meets every premise with a nonempty pending
list.
-/

namespace AssetBridgePreparation

open Contracts

/-- **THE PENDING LIST IS THE REGISTRY'S RECORDED OUTFLOW.**  See the module header for
the premises and conclusions in words.  `Wf` and `W'` are the registry run the
simulation builds (mints to `bridgeIn`, nonzero burns and preparations to
`bridgeOut`), so the audit equalities hold for that matching run and constrain no
other registry run. -/
def Properties.TightTraceIsRegistryOutflow : Prop :=
  ∀ (Accounting : Type) (initHooks : NativeTokenVaultBase.RegistrationHooks Accounting)
    (start : NativeTokenVaultBase.RegistrationState Accounting)
    (origin : NativeTokenVaultBase.Address)
    (registered : NativeTokenVaultBase.Registered Accounting)
    (fundedToken : BridgedStandardERC20.State) (hooks : NativeTokenVaultBase.Hooks Accounting)
    (t : Ledger Accounting) (e : NativeTokenVault.NtvAssetId)
    (S : Set (NativeTokenVault.Chain × NativeTokenVault.Address))
    (thisChain : NativeTokenVault.Chain) (W : NativeTokenVault.World),
    NativeTokenVault.IdAssumptionsOn e S → thisChain ≠ 0 →
    NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W →
    (start.config.originChainId, NativeTokenVaultBase.widen origin) ∈ S →
    NativeTokenVaultBase.CorrPre start thisChain W.vault →
    NativeTokenVaultBase.registerFreshBranch' initHooks start origin = some registered →
    initHooks.assetIdFor start.config.originChainId origin =
      e start.config.originChainId (NativeTokenVaultBase.widen origin) →
    BridgedStandardERC20.Reach registered.state.token fundedToken →
    Reach hooks ⟨{ registered.state with token := fundedToken }, []⟩ t →
      ∃ Wf W' : NativeTokenVault.World,
        NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty Wf
        ∧ NativeTokenVault.ReachIn e thisChain S Wf W'
        ∧ Wf.vault = NativeTokenVaultBase.correspondingRegistration start origin W.vault
        ∧ W'.vault = Wf.vault
        ∧ NativeTokenVaultBase.Corr t.vault thisChain W'.vault
        ∧ NativeTokenVault.Valid e thisChain W'.vault
        ∧ NativeTokenVaultBase.WellFormed t.vault
        ∧ fundedToken.totalSupply + Wf.audit.totalOut start.config.assetId
            = Wf.audit.totalIn start.config.assetId
        ∧ W'.audit.totalIn start.config.assetId = Wf.audit.totalIn start.config.assetId
        ∧ W'.audit.totalOut start.config.assetId
            = Wf.audit.totalOut start.config.assetId + pendingAmount t.pending
        ∧ (∀ c, W'.audit.outTo c start.config.assetId
            = Wf.audit.outTo c start.config.assetId + pendingAmountTo c t.pending)
        ∧ (∀ o ∈ t.pending, o.assetId = start.config.assetId)
        ∧ t.vault.token.totalSupply + pendingAmount t.pending = fundedToken.totalSupply

/-- **THE PREMISES ARE SATISFIABLE, WITH A NONEMPTY PENDING LIST.**  Every premise of
`TightTraceIsRegistryOutflow`: a registry prefix holding a native asset, a funding mint
of one unit, and a trace with one preparation. -/
def Properties.TightTraceIsRegistryOutflowSatisfiable : Prop :=
  ∃ (initHooks : NativeTokenVaultBase.RegistrationHooks Unit)
    (start : NativeTokenVaultBase.RegistrationState Unit) (origin : NativeTokenVaultBase.Address)
    (registered : NativeTokenVaultBase.Registered Unit) (fundedToken : BridgedStandardERC20.State)
    (hooks : NativeTokenVaultBase.Hooks Unit) (t : Ledger Unit) (e : NativeTokenVault.NtvAssetId)
    (S : Set (NativeTokenVault.Chain × NativeTokenVault.Address))
    (thisChain : NativeTokenVault.Chain) (W : NativeTokenVault.World),
    NativeTokenVault.IdAssumptionsOn e S ∧ thisChain ≠ 0
    ∧ NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W
    ∧ (start.config.originChainId, NativeTokenVaultBase.widen origin) ∈ S
    ∧ NativeTokenVaultBase.CorrPre start thisChain W.vault
    ∧ NativeTokenVaultBase.registerFreshBranch' initHooks start origin = some registered
    ∧ initHooks.assetIdFor start.config.originChainId origin =
        e start.config.originChainId (NativeTokenVaultBase.widen origin)
    ∧ BridgedStandardERC20.Reach registered.state.token fundedToken
    ∧ Reach hooks ⟨{ registered.state with token := fundedToken }, []⟩ t
    ∧ t.pending ≠ []

end AssetBridgePreparation
