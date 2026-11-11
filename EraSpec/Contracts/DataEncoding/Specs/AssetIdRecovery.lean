import EraSpec.Contracts.DataEncoding.Specs.AssetId
import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery

/-!
# Spec: atomic recovery of a custom asset, with keccak as the id hash

This topic adds no definitions. It instantiates the router's atomic-recovery model
(`Contracts.AssetRouter.AtomicRecovery`, `AssetRouterBase/Specs/AtomicRecovery.lean`, backlog
item B1) with `enc := routerEnc keccak` from `Specs/AssetId.lean`.

Statements are in `EraSpec.Contracts.DataEncoding.Properties.AssetIdRecovery`, proofs in
`EraSpec.Contracts.DataEncoding.Proofs.AssetIdRecovery`.

## Why the hash matters there

`L2AssetRouter.recoverAtomicCall` refunds every router-routed leg through the vault, whatever the
asset's registered handler. For a custom asset (an id `encodeAssetId(c₀, d, s)` with `s` not the
vault) the vault refund then reverts, unless `assetIdCheck` passes on the origin pair decoded
from the call's mint data (`NativeTokenVaultBase.sol:580`, inside `_ensureAndSaveTokenDeployed`).
It passes only if the custom id equals the NTV id of that pair. B1 states this with an abstract
`enc`, either as "the refund reverts or the two ids are equal"
(`CustomAssetRecoveryRevertsOrCollision`) or under `IdInjOn` on the compared triples
(`CustomHandlerDepositRefundReverts`).

At byte level the two compared ids are keccak of two 96-byte preimages:

* the custom triple's `abi.encode(c₀, s, d)` (`routerPreimage c₀ s d`);
* the NTV id's `abi.encode(c, vault, originToken)` (`routerPreimage c cfg.ntv (widen t)`).

With `cfg.ntv` the normalised `L2_NATIVE_TOKEN_VAULT_ADDR` (as on an L2), the second is exactly
`assetIdPreimageOfToken c L2_NTV t`, the bytes `assetIdCheck` hashes
(`Properties.VaultModelIsLibrary`, `Properties.VaultModelIsRouterModelAtNtv`). Since `s` is not the
vault, the two preimages differ, so equal ids are a keccak collision on those named bytes.

## Model boundaries

Those of the atomic-recovery model, unchanged, and of `Specs/AssetId.lean`.
-/
