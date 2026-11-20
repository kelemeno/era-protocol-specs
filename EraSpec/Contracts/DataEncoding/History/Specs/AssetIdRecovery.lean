import EraSpec.Contracts.DataEncoding.Specs.AssetId
import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery

/-! **History: a record of the interop pin `c67894b9`, not a claim about era-contracts `b17415d20`.**
This topic instantiates the router's atomic-recovery model (`AssetRouterBase` `AtomicRecovery`),
which transcribes `L2AssetRouter.recoverAtomicCall` at `c67894b9`, where a recovered
`finalizeDeposit` call always went to the vault. At `b17415d20` `recoverAtomicCall`
(`bridge/asset-router/L2AssetRouter.sol:269-303`) reverts for an L1 destination, reads the asset's
registered handler, reverts when there is none, and calls that handler's
`bridgeRecoverFailedTransfer`, so a custom asset's refund no longer reaches the vault. The library
side (`assetIdCheck`, `DataEncoding.sol:207-213` at `b17415d20`) is unchanged and is modelled in the
current `Specs/AssetId.lean`. Namespace `Contracts.DataEncoding.History`. -/

/-!
# Spec: atomic recovery of a custom asset, with keccak as the id hash

This topic adds no definitions. It instantiates the router's atomic-recovery model
(`Contracts.AssetRouter.AtomicRecovery`, `AssetRouterBase/Specs/AtomicRecovery.lean`, pinned at
`c67894b9`) with `enc := routerEnc keccak` from `Specs/AssetId.lean`.

Statements are in `EraSpec.Contracts.DataEncoding.Properties.AssetIdRecovery`, proofs in
`EraSpec.Contracts.DataEncoding.Proofs.AssetIdRecovery`.

## Why the hash matters there

At `c67894b9`, `L2AssetRouter.recoverAtomicCall` (`bridge/asset-router/L2AssetRouter.sol:281-296`)
sends every `finalizeDeposit` call it recovers to the vault, whatever the asset's registered
handler. For a custom asset (an id `encodeAssetId(c₀, d, s)` with `s` not the vault) the vault
refund then reverts, unless `assetIdCheck` passes on the origin pair decoded from the call's mint
data. The check is in `_ensureAndSaveTokenDeployedInner` (`bridge/ntv/NativeTokenVaultBase.sol:580`),
which the L2 vault's `_ensureAndSaveTokenDeployed` override calls
(`bridge/ntv/L2NativeTokenVault.sol:195-209`, at `:202`). It passes only if the custom id equals
the NTV id of that pair. The atomic-recovery model states this with an abstract `enc`, either as
"the refund reverts or the two ids are equal" (`CustomAssetRecoveryRevertsOrCollision`) or under
`IdInjOn` on the compared triples (`CustomHandlerDepositRefundReverts`).

At byte level the two compared ids are keccak of two 96-byte preimages:

* the custom triple's `routerPreimage c₀ s d` (for a real address `s`, `abi.encode(c₀, s, d)`);
* the NTV id's `routerPreimage c cfg.ntv (widen t)` (for the vault address `cfg.ntv`,
  `abi.encode(c, vault, originToken)`).

With `cfg.ntv` the normalised `L2_NATIVE_TOKEN_VAULT_ADDR` (as on an L2), the second is exactly
`assetIdPreimageOfToken c L2_NTV t`, the bytes `assetIdCheck` hashes
(`Properties.VaultModelIsLibrary`, `Properties.VaultModelIsRouterModelAtNtv`). Since `s` is not the
vault, the two preimages differ, so equal ids are a keccak collision on those named bytes.

## Later trees

At `e561b9cc2`, draft/v0.35.0 (`d9f6789`, `b17415d20`) and main (`3605e82`, `70096e2ea`),
`recoverAtomicCall` is different code (`L2AssetRouter.sol:269-303`; `:275-309` on main). It
reverts for an L1 destination (`RecoverToL1NotSupported`), reads `assetHandlerAddress[assetId]`,
reverts when that is zero (`AssetHandlerDoesNotExist`), and calls that handler's
`bridgeRecoverFailedTransfer`. A custom-handler asset's refund goes to its own handler there, not
to the vault. So the custom-asset results of this topic, like those of `AtomicRecovery`, describe
the code at `c67894b9` only. `FailsAssetIdCheckIsLibraryRevert` relates the model's guard to the
library's `assetIdCheck`, which is unchanged on those trees (`Specs/AssetId.lean`).

## Model boundaries

Those of the atomic-recovery model, unchanged, and of `Specs/AssetId.lean`.
-/
