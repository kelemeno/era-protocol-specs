import EraSpec.Contracts.NativeTokenVaultBase.Specs.ModelCorrespondence
import EraSpec.Contracts.NativeTokenVaultBase.Specs.Resolution

/-!
# Properties: resolution in the registry-wide vault model

Statements relating `EraSpec.Contracts.NativeTokenVaultBase.Specs.Resolution` to the
registry-wide model `Contracts.NativeTokenVault` (`Specs/RegistryAndEscrow.lean`) through the
existing correspondence `Corr` (`Specs/ModelCorrespondence.lean`). Proofs are in
`EraSpec.Contracts.NativeTokenVaultBase.Proofs.ResolutionCorrespondence`.

The registry model abstracts both `bridgeMint` and `_disburseFailedTransfer` as one
`bridgeIn` flow (`NativeTokenVault.bridgeIn`): for a native asset it releases escrow and
shrinks `bridgedOut`, for any other asset it leaves the vault alone, and either way it records
the inflow in the audit. `ResolutionIsForeignBridgeIn` shows that the representation model's
two resolution entry points are such a step, on the non-native branch, as
`PreparationIsForeignBridgeOut` does for preparation and `bridgeOut`. So the registry model's
run results (`RunValidOn`, `LoggedRunSound`, the flow audit) cover resolution steps of the
representation model on corresponding states. No hash premise is involved.

`ResolutionCorrespondenceSatisfiable` meets the premises, with the registry vault `Valid` and
the representation state `WellFormed`.
-/

namespace Contracts.NativeTokenVaultBase

open NativeTokenVault (Chain Vault World NtvAssetId Valid)

/-- **RESOLUTION IS A FOREIGN `bridgeIn`.** On a representation state corresponding to `W.vault`,
a successful destination `bridgeMint` or source `bridgeRecoverFailedTransfer` is a registry-model
`bridgeIn` step of the call's asset and amount from the call's chain. The asset is not native in
the registry model, so that step leaves the registry vault unchanged (it only records the inflow
in the audit), and the post-state still corresponds. No representation invariant is assumed: the
registered bridged branch supplies a registered, foreign asset. -/
def Properties.ResolutionIsForeignBridgeIn : Prop :=
  ∀ (Accounting : Type) (rh : ResolutionHooks Accounting) (s t : State Accounting)
    (c : ResolutionCall) (e : NtvAssetId) (thisChain : Chain) (W : World),
    Corr s thisChain W.vault →
    (bridgeMint rh s c = some t ∨ bridgeRecoverFailedTransfer rh s c = some t) →
      NativeTokenVault.Step e thisChain W
          (NativeTokenVault.bridgeIn thisChain W c.chain c.assetId c.data.amount.val)
        ∧ ¬ NativeTokenVault.Native thisChain W.vault c.assetId
        ∧ (NativeTokenVault.bridgeIn thisChain W c.chain c.assetId c.data.amount.val).vault =
            W.vault
        ∧ Corr t thisChain W.vault

/-- **THE PREMISES ARE SATISFIABLE.** A `Valid` registry vault, a corresponding `WellFormed`
representation state, and a call of nonzero amount on which both `bridgeMint` and
`bridgeRecoverFailedTransfer` succeed. -/
def Properties.ResolutionCorrespondenceSatisfiable : Prop :=
  ∃ (e : NtvAssetId) (thisChain : Chain) (W : World) (rh : ResolutionHooks Unit)
    (s t : State Unit) (c : ResolutionCall),
    Valid e thisChain W.vault ∧ Corr s thisChain W.vault ∧ WellFormed s ∧
    bridgeMint rh s c = some t ∧ bridgeRecoverFailedTransfer rh s c ≠ none ∧
    c.data.amount ≠ 0

end Contracts.NativeTokenVaultBase
