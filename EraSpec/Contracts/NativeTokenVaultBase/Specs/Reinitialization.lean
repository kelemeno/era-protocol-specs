import EraSpec.Contracts.NativeTokenVaultBase.Specs.RepresentationPreparation
import EraSpec.Contracts.BridgedStandardERC20.Specs.Reinitialization

/-!
# The vault's tracked token, reinitialized

Source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`, paths relative to
`l1-contracts/contracts/bridge/`: `ntv/NativeTokenVaultBase.sol` (cited as `NTV:N`),
`BridgeHelper.sol`, and `BridgedStandardERC20.sol` (cited as `BSE:N`).

**This file is definitions only.** The results are in
`EraSpec.Contracts.NativeTokenVaultBase.Properties.Reinitialization` and are proved in
`EraSpec.Contracts.NativeTokenVaultBase.Proofs.Reinitialization`.

## How the two models meet

The vault model (`Specs/RepresentationPreparation.lean`) carries its one tracked token as a
`BridgedStandardERC20.State`: the token's ledger and identity (vault, origin token, asset id).
The token's full storage (`BridgedStandardERC20.TokenStorage`, in
`BridgedStandardERC20/Specs/Reinitialization.lean`) adds the initializer version and the
metadata slots. So a vault state `s`, with the token's version and metadata, determines the
tracked token's full storage (`trackedStorage`), and after a call on that storage the vault
state is `s` with the new storage's ledger-and-identity projection (`withTracked`).
`reinitializeToken` is a call on the token, by the beacon's owner; the vault takes no part in
it, and no vault slot changes.

## Metadata in preparation

`bridgeBurn`'s representation branch reads the token's metadata after the burn:
`_bridgeBurnToken` encodes `_getERC20Metadata(token, assetId, true)` into the returned mint data
(NTV:415-421); that reads `getERC20Getters(token, originChainId)` (NTV:432-444, :501-510),
i.e. `BridgeHelper.getERC20Getters` (`BridgeHelper.sol:20-50`), which `staticcall`s the token's
`name()`, `symbol()` and `decimals()`, uses empty bytes for a getter that reverts (:30-46), and
encodes the three with the origin chain (:48-49). `reinitializeToken` changes what those getters
return: the name, the symbol, and which getters revert (BSE:198-223, :159-161).

The vault model's `Hooks.metadata` sees only the ledger-and-identity state, so it cannot express
that dependence. `MetaHooks` lets the metadata read see the token's `Metadata` as well, and
`hooks.toHooks m` is the vault model's hook record with the token's metadata fixed at `m`. The
accounting hook (the asset tracker) does not read token metadata and is shared.

The source's metadata read cannot itself revert (each getter is a `staticcall` whose failure is
replaced by empty bytes); `MetaHooks.metadata` is still allowed to fail, as `Hooks.metadata` is
(`DEP-RESULTS`).
-/

namespace Contracts.NativeTokenVaultBase

variable {Accounting : Type}

/-- The tracked token's full storage: the vault model's token state, with the token's
initializer version and metadata. -/
def trackedStorage (s : State Accounting) (version : UInt8)
    (metadata : BridgedStandardERC20.Metadata) : BridgedStandardERC20.TokenStorage :=
  ⟨s.token, version, metadata⟩

/-- The vault state after a call on the tracked token: its ledger-and-identity projection
replaces the vault model's token state; nothing else changes. -/
def withTracked (s : State Accounting) (t : BridgedStandardERC20.TokenStorage) : State Accounting :=
  { s with token := t.token }

/-- Preparation hooks whose metadata read also sees the token's metadata (`BridgeHelper.sol:20-50`
calls the token's `name()`, `symbol()`, `decimals()`). -/
structure MetaHooks (Accounting : Type) where
  /-- The accounting hook of `Hooks`: it does not read token metadata. -/
  account : Accounting → BridgedStandardERC20.State → UInt256 → UInt256 → UInt256 →
    Option Accounting
  /-- The metadata read, on the token's metadata, the burned token state and the origin chain. -/
  metadata : BridgedStandardERC20.Metadata → BridgedStandardERC20.State → UInt256 →
    Option Bytes

/-- The vault model's hooks while the tracked token's metadata is `m`. -/
def MetaHooks.toHooks (hooks : MetaHooks Accounting) (m : BridgedStandardERC20.Metadata) :
    Hooks Accounting :=
  ⟨hooks.account, hooks.metadata m⟩

/-! ## Witness data

A small concrete vault, used by the witnesses here and in
`AssetBridgePreparation.Properties.Reinitialization`. Addresses and words are small numbers. -/

/-- The witness token: vault `1`, origin token `9`, asset `5`; ten units minted to account `4`. -/
def wToken : BridgedStandardERC20.State :=
  BridgedStandardERC20.mintEffect (BridgedStandardERC20.empty ⟨1, 9, 5⟩) 4 10

/-- The witness vault: vault `1`, router `2`, tracked token `3` for asset `5`, base asset `6`,
this chain `7`, origin chain `8`. The registry sends every asset to token `3` and every token
to asset `5`; only the entries for `5` and `3` matter. Not paused; no accounting state. -/
def wVault : State Unit :=
  ⟨⟨1, 2, 3, 5, 6, 7, 8⟩, ⟨fun _ => 3, fun _ => 5⟩, false, wToken, ()⟩

/-- A request from the router to send three units of asset `5` from account `4` to receiver
`12` on chain `11`, with no token hint and no value. -/
def wRequest : Request := ⟨2, 11, 5, 4, 0, 0, ⟨3, 12, 0⟩⟩

/-- Hooks whose accounting always succeeds and whose metadata read returns the token's name. -/
def wHooks : MetaHooks Unit := ⟨fun a _ _ _ _ => some a, fun m _ _ => some m.name⟩

/-- The witness token's metadata at version 1: name `[0x41]`, all else empty. -/
def wMetadata : BridgedStandardERC20.Metadata :=
  { BridgedStandardERC20.emptyMetadata with name := [0x41] }

end Contracts.NativeTokenVaultBase
