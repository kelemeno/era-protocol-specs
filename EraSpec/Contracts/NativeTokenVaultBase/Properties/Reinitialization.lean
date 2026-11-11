import EraSpec.Contracts.NativeTokenVaultBase.Specs.Reinitialization

/-!
# Properties: reinitializing the tracked token leaves the vault's view of it alone

Statements about `EraSpec.Contracts.NativeTokenVaultBase.Specs.Reinitialization`. Proofs are
in `EraSpec.Contracts.NativeTokenVaultBase.Proofs.Reinitialization`.

* **No vault-model slot changes** (`ReinitLeavesVaultStateUnchanged`): after any successful
  `reinitializeToken` on the tracked token, the vault state with the token's new
  ledger-and-identity projection is the vault state before. So `LedgerInvariant`,
  `RepresentationConsistent` and `WellFormed` hold after exactly when they held before
  (`ReinitPreservesVaultInvariants`).
* **Of a later preparation, only the metadata bytes can change.** A request that prepared
  before the reinitialization prepares after it to the same vault state and the same mint data
  except `metadata`, provided the metadata read succeeds on the new metadata
  (`ReinitKeepsPreparationExceptMetadata`); and whenever both preparations succeed they agree on
  original caller, receiver, origin token and amount (`ReinitChangesOnlyPreparedMetadata`).
* `VaultReinitWitness` runs both on a concrete `WellFormed` vault, where the metadata bytes do
  change (from the old name to the new one) and nothing else does.
-/

namespace Contracts.NativeTokenVaultBase

/-- **NO VAULT-MODEL SLOT CHANGES.** After a successful `reinitializeToken` on the tracked
token's storage, whoever calls it and whatever it writes, writing the token's ledger-and-identity
projection back into the vault state gives the vault state before. -/
def Properties.ReinitLeavesVaultStateUnchanged : Prop :=
  ∀ {Accounting : Type} (s : State Accounting) (version : UInt8)
    (metadata : BridgedStandardERC20.Metadata) (beaconOwner : Option Address) (caller : Address)
    (getters : BridgedStandardERC20.Getters) (name symbol : BridgedStandardERC20.Text)
    (version' : UInt8) (t : BridgedStandardERC20.TokenStorage),
    BridgedStandardERC20.reinitializeToken beaconOwner (trackedStorage s version metadata) caller
      getters name symbol version' = some t →
    withTracked s t = s

/-- **THE VAULT INVARIANTS ARE KEPT, EACH ON ITS OWN.** After a successful reinitialization of the
tracked token, each of `LedgerInvariant`, `RepresentationConsistent` and `WellFormed` holds of the
vault state exactly when it held before. -/
def Properties.ReinitPreservesVaultInvariants : Prop :=
  ∀ {Accounting : Type} (s : State Accounting) (version : UInt8)
    (metadata : BridgedStandardERC20.Metadata) (beaconOwner : Option Address) (caller : Address)
    (getters : BridgedStandardERC20.Getters) (name symbol : BridgedStandardERC20.Text)
    (version' : UInt8) (t : BridgedStandardERC20.TokenStorage),
    BridgedStandardERC20.reinitializeToken beaconOwner (trackedStorage s version metadata) caller
      getters name symbol version' = some t →
    (LedgerInvariant (withTracked s t) ↔ LedgerInvariant s) ∧
    (RepresentationConsistent (withTracked s t) ↔ RepresentationConsistent s) ∧
    (WellFormed (withTracked s t) ↔ WellFormed s)

/-- **A PREPARATION THAT WORKED STILL WORKS, CHANGED ONLY IN ITS METADATA BYTES.** If a request
prepared to `out` while the token's metadata was `metadata`, then after a successful
reinitialization it prepares to the same vault state and the same mint data except `metadata`,
which becomes whatever the metadata read returns on the new metadata, provided that read
succeeds. -/
def Properties.ReinitKeepsPreparationExceptMetadata : Prop :=
  ∀ {Accounting : Type} (hooks : MetaHooks Accounting) (s : State Accounting) (version : UInt8)
    (metadata : BridgedStandardERC20.Metadata) (beaconOwner : Option Address) (caller : Address)
    (getters : BridgedStandardERC20.Getters) (name symbol : BridgedStandardERC20.Text)
    (version' : UInt8) (t : BridgedStandardERC20.TokenStorage) (r : Request)
    (out : Result Accounting) (bytes : Bytes),
    BridgedStandardERC20.reinitializeToken beaconOwner (trackedStorage s version metadata) caller
      getters name symbol version' = some t →
    prepare (hooks.toHooks metadata) s r = some out →
    hooks.metadata t.metadata out.state.token s.config.originChainId = some bytes →
    prepare (hooks.toHooks t.metadata) (withTracked s t) r =
      some ⟨out.state, { out.data with metadata := bytes }⟩

/-- **A REINITIALIZATION CHANGES, OF A PREPARATION, ONLY THE METADATA BYTES.** If the same request
prepares both before and after a successful reinitialization, the two results have the same
vault state and the same original caller, receiver, origin token and amount. -/
def Properties.ReinitChangesOnlyPreparedMetadata : Prop :=
  ∀ {Accounting : Type} (hooks : MetaHooks Accounting) (s : State Accounting) (version : UInt8)
    (metadata : BridgedStandardERC20.Metadata) (beaconOwner : Option Address) (caller : Address)
    (getters : BridgedStandardERC20.Getters) (name symbol : BridgedStandardERC20.Text)
    (version' : UInt8) (t : BridgedStandardERC20.TokenStorage) (r : Request)
    (out out' : Result Accounting),
    BridgedStandardERC20.reinitializeToken beaconOwner (trackedStorage s version metadata) caller
      getters name symbol version' = some t →
    prepare (hooks.toHooks metadata) s r = some out →
    prepare (hooks.toHooks t.metadata) (withTracked s t) r = some out' →
    out'.state = out.state ∧ out'.data.originalCaller = out.data.originalCaller ∧
    out'.data.remoteReceiver = out.data.remoteReceiver ∧
    out'.data.originToken = out.data.originToken ∧ out'.data.amount = out.data.amount

/-- **THE PREMISES ARE SATISFIABLE, AND THE BYTES DO CHANGE.** On the `WellFormed` witness vault
with the token at version 1 named `[0x41]`, the beacon owner `13` reinitializes it to version 2
named `[0x42]`. The witness request prepares both before and after; the two results have the same
vault state and amount, and their metadata bytes are the old and the new name. -/
def Properties.VaultReinitWitness : Prop :=
  ∃ (t : BridgedStandardERC20.TokenStorage) (out out' : Result Unit),
    WellFormed wVault ∧
    BridgedStandardERC20.reinitializeToken (some 13) (trackedStorage wVault 1 wMetadata) 13
      ⟨false, false, false⟩ [0x42] [0x42] 2 = some t ∧
    prepare (wHooks.toHooks wMetadata) wVault wRequest = some out ∧
    prepare (wHooks.toHooks t.metadata) (withTracked wVault t) wRequest = some out' ∧
    out.data.metadata = [0x41] ∧ out'.data.metadata = [0x42] ∧
    out'.state = out.state ∧ out'.data.amount = out.data.amount

end Contracts.NativeTokenVaultBase
