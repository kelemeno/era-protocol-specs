import EraSpec.Protocol.AssetBridgePreparation.Specs.Model
import EraSpec.Contracts.NativeTokenVaultBase.Specs.Reinitialization
import EraSpec.Contracts.NativeTokenVaultBase.Specs.Initialization

/-!
# The preparation trace, with reinitializations of the tracked token

Source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`,
`l1-contracts/contracts/bridge/BridgedStandardERC20.sol:141-164` (`reinitializeToken`) and the
vault's preparation branch (`bridge/ntv/NativeTokenVaultBase.sol:315-444`), as modelled in
`BridgedStandardERC20/Specs/Reinitialization.lean`,
`NativeTokenVaultBase/Specs/RepresentationPreparation.lean` and
`NativeTokenVaultBase/Specs/Reinitialization.lean`.

**This file is definitions only.** The results are in
`EraSpec.Protocol.AssetBridgePreparation.Properties.Reinitialization` and are proved in
`EraSpec.Protocol.AssetBridgePreparation.Proofs.Reinitialization`.

## What is added to the trace

`Specs/Model.lean`'s trace (`Step`) has two steps: a successful vault preparation, which appends
its returned mint data to the ghost `pending` list once, and an ordinary token transfer. Its
`pending` list is trace bookkeeping, not storage. `ReinitStep` adds the third thing that can
happen to the tracked token in between: a successful `reinitializeToken` by whoever the beacon
reports as its owner, with any arguments. To say what that call does, the trace state carries the
token's initializer version and metadata as well (`TokenTrace`), and a preparation step reads the
metadata through `MetaHooks` at the token's current metadata (`hooks.toHooks s.metadata`), since
the source's metadata read calls the token's getters (`NativeTokenVaultBase.sol:432-444`,
`BridgeHelper.sol:20-50`).

The reinitialization step writes the call's resulting ledger-and-identity state back into the
vault state (`withTracked`) and keeps the pending list; nothing about it is assumed.

`PendingNamesToken` is the property that every pending obligation names the tracked token's asset
id and origin token: what REVIEW.md's token row asks of reinitialization ("cannot change the asset
represented by pending obligations").

## Witness data

`wRegHooks` and `wRegStart` describe a concrete fresh registration of the witness token of
`NativeTokenVaultBase/Specs/Reinitialization.lean`: the same vault configuration, an empty
registry, the asset encoder answering `5`, the deployer answering token `3`, and a tracker hook
that always succeeds.
-/

namespace AssetBridgePreparation

open Contracts

variable {Accounting : Type}

/-- A preparation-trace state together with the tracked token's initializer version and metadata. -/
structure TokenTrace (Accounting : Type) where
  ledger : Ledger Accounting
  version : UInt8
  metadata : BridgedStandardERC20.Metadata

/-- The tracked token's full storage in a trace state. -/
def TokenTrace.storage (s : TokenTrace Accounting) : BridgedStandardERC20.TokenStorage :=
  NativeTokenVaultBase.trackedStorage s.ledger.vault s.version s.metadata

/-- One step: a trace step of `Specs/Model.lean` with the metadata read at the token's current
metadata, or a successful `reinitializeToken` on the tracked token. -/
inductive ReinitStep (hooks : NativeTokenVaultBase.MetaHooks Accounting) :
    TokenTrace Accounting → TokenTrace Accounting → Prop
  /-- A preparation or an ordinary transfer; the version and metadata stay. -/
  | trace {s : TokenTrace Accounting} {l : Ledger Accounting} :
      Step (hooks.toHooks s.metadata) s.ledger l →
      ReinitStep hooks s ⟨l, s.version, s.metadata⟩
  /-- `reinitializeToken`, by any caller, whatever the beacon reports as its owner. -/
  | reinitialize {s : TokenTrace Accounting} {t : BridgedStandardERC20.TokenStorage}
      {beaconOwner : Option NativeTokenVaultBase.Address} {caller : NativeTokenVaultBase.Address}
      {getters : BridgedStandardERC20.Getters} {name symbol : BridgedStandardERC20.Text}
      {version : UInt8} :
      BridgedStandardERC20.reinitializeToken beaconOwner s.storage caller getters name symbol
        version = some t →
      ReinitStep hooks s
        ⟨⟨NativeTokenVaultBase.withTracked s.ledger.vault t, s.ledger.pending⟩, t.version,
          t.metadata⟩

inductive ReinitReach (hooks : NativeTokenVaultBase.MetaHooks Accounting) :
    TokenTrace Accounting → TokenTrace Accounting → Prop
  | refl {s} : ReinitReach hooks s s
  | tail {s t u} : ReinitReach hooks s t → ReinitStep hooks t u → ReinitReach hooks s u

/-- Every pending obligation names the tracked token's asset id and origin token. -/
def PendingNamesToken (l : Ledger Accounting) : Prop :=
  ∀ o ∈ l.pending, o.assetId = l.vault.token.config.assetId ∧
    o.data.originToken = l.vault.token.config.originToken

/-! ## Witness data -/

/-- Registration dependencies for the witness: the asset encoder answers `5`, the deployer
answers token `3`, the outer metadata decode succeeds, and the tracker hook always succeeds. -/
def wRegHooks : NativeTokenVaultBase.RegistrationHooks Unit :=
  ⟨fun _ _ => 5, fun _ _ => some 3, true, fun a _ _ _ _ => some a⟩

/-- The witness vault before registration: `NativeTokenVaultBase.wVault`'s configuration, an
empty registry, not paused. -/
def wRegStart : NativeTokenVaultBase.RegistrationState Unit :=
  ⟨NativeTokenVaultBase.wVault.config, ⟨fun _ => 0, fun _ => 0⟩, false, ()⟩

end AssetBridgePreparation
