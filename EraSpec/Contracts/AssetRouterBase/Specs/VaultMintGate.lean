import Mathlib.Tactic
import EraSpec.Contracts.AssetRouterBase.Specs.AllWriters
import EraSpec.Contracts.NativeTokenVaultBase.Specs.RegistryAndEscrow

/-!
# Model link: the router's vault-mint premise, from the vault's registry model

Source: the pinned era-contracts tree (`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`), paths
relative to `l1-contracts/contracts/`, with `bridge/ntv/` shortened to `NTV/`.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.AssetRouterBase.Properties.VaultMintGate` and are proved in
`EraSpec.Contracts.AssetRouterBase.Proofs.VaultMintGate`.

`AllWriters` assumes `MintsOnlyNtvIds`: the vault's `bridgeMint`, reached from
`_finalizeDeposit`'s fallback, succeeds only for vault ids.  This file states that
premise in terms of the vault's own model, `Contracts.NativeTokenVault`
(`NativeTokenVaultBase/Specs/RegistryAndEscrow.lean`), so that it can be proved rather
than assumed.

* **The two encodings are one hash.**  `encodeNTVAssetId(c, t)` is
  `keccak256(abi.encode(c, L2_NATIVE_TOKEN_VAULT_ADDR, t))`
  (`common/libraries/DataEncoding.sol:151-153`).  `encodeAssetId(c, t, s)` is
  `keccak256(abi.encode(c, s, t))` (:135-137).  So the vault's id is the router's id at
  `s = L2_NATIVE_TOKEN_VAULT_ADDR` (`EncodingsAgree`).
* **What the vault model mints.**  In the vault model, `bridgeIn` is the accounting of
  `bridgeMint` (`NTV/NativeTokenVaultBase.sol:240-267`), and its guard requires the id to
  be registered (`FlowInGuard.registered`).  The first mint of a token native elsewhere
  registers it first (`_ensureAndSaveTokenDeployed`, :253-255), which is the model's
  `registerBridged` step, guarded by `assetIdCheck` (`RegisterBridgedGuard.idChecked`).
  So the ids at which `bridgeMint` can succeed are the ids at which `bridgeIn` is
  enabled in some state the vault model reaches from fresh storage (`VaultModelMints`).

Boundary: the vault model omits `L2NativeTokenVault.updateL2`'s unchecked base-token
registry write (`NTV/L2NativeTokenVault.sol:170-172`) and the legacy paths.  The router
model needs no such id: L2's `finalizeDeposit` rejects the base token (`AllWriters`,
`AStep.finalize`).
-/

namespace Contracts.AssetRouter.AllWriters

/-- The vault's asset-id encoding is the router's at sender `L2_NATIVE_TOKEN_VAULT_ADDR`. -/
def EncodingsAgree (e : Contracts.NativeTokenVault.NtvAssetId) (enc : AssetIdOf)
    (ntvAddr : Address) : Prop :=
  ∀ (c : Chain) (t : Address), e c t = enc c ntvAddr t

/-- The ids at which the vault model admits an inbound transfer, in some state reachable
from fresh storage: the ids for which the vault's `bridgeMint` can succeed. -/
def VaultModelMints (e : Contracts.NativeTokenVault.NtvAssetId) (thisChain : Chain)
    (a : AssetId) : Prop :=
  ∃ (W : Contracts.NativeTokenVault.World) (amt : ℕ),
    Contracts.NativeTokenVault.Reach e thisChain Contracts.NativeTokenVault.empty W ∧
    Contracts.NativeTokenVault.FlowInGuard thisChain W.vault a amt

end Contracts.AssetRouter.AllWriters
