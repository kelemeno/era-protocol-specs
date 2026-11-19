# DataEncoding

## Headline guarantees

About `common/libraries/DataEncoding.sol` at era-contracts `draft/v0.35.0` head `b17415d20`. No
headline takes a premise on keccak: `keccak` is any function from byte strings to 256-bit words, and
a collision is always named (`HashCollision keccak x y`: the two given byte strings differ and hash
alike). The byte layouts follow the Solidity ABI specification, not solc's emitted code (`SOL-ABI`).

| Guarantee | Premises | Lean name |
|---|---|---|
| The asset-id preimage `abi.encode(chainId, sender, assetData)` determines the chain, sender and data | none | `Contracts.DataEncoding.Properties.AssetIdPreimageInjective` |
| Both `encodeNTVAssetId` overloads equal `encodeAssetId` with sender `L2_NATIVE_TOKEN_VAULT_ADDR`, for every keccak | none | `Properties.OverloadsCoincide` |
| A native registration keys the vault and the router by one id: the vault's `encodeNTVAssetId(c, t)` is the id the router writes for the vault's `setAssetHandlerAddressThisChain` call | none (any vault address, any keccak) | `Properties.NativeRegistrationIdsAgree` |
| `assetIdCheck(c, a, t)` passes exactly when `a = encodeNTVAssetId(c, t)` | none | `Properties.AssetIdCheckPassesIff` |
| Two passing `assetIdCheck`s for one id name the same origin chain and token, or keccak collides on their two named preimages | both checks passed | `Properties.AssetIdCheckPinsOriginOrCollision` |
| Equal deposit-record hashes (`encodeTxDataHash`) mean the same sender, asset id and transfer data, or a keccak collision on the two named record preimages | both transfer data are shorter than `2^256` bytes (the EVM length bound) | `Properties.TxDataHashBindsOrCollision` |
| A record hash equals a hash of the removed legacy format only through a keccak collision on the two named preimages | the two hashes are equal | `Properties.NewHashMatchesLegacyOnlyByCollision` |
| A record hash is zero (the nullifier's "no record") exactly when keccak sends the named record preimage to zero | none | `Properties.TxDataHashZeroIsPreimageEvent` |
| `decodeBridgeBurnData` returns `b` exactly on the bytes `encodeBridgeBurnData(b)` | none | `Properties.BurnDataDecodeIffEncode` |
| A claim whose transfer data the vault's parser accepts and whose hash matches an NTV deposit record names that record's sender, asset id and burn data, or keccak collides on the two named record preimages | the claim's data decodes as burn data; the two record hashes are equal | `Properties.NtvClaimNamesRecordedDepositOrCollision` |

Witnesses (`@[witness]`): `AssetIdCheckPinWitness`, `TxDataHashWitness`,
`NtvClaimNamesRecordedDepositOrCollisionWitness`, `AssetIdClashPremisesSatisfiable`,
`RouterNoBreakSatisfiable`, `VaultNoBreakSatisfiable`. Countermodels (`@[countermodel]`):
`TxDataHashCollisionDisjunctNeeded` (the collision disjuncts cannot be dropped),
`ZeroPreimageIndependentOfCollisions` (no collision does not give a nonzero id).

## Source and scope

Source: `l1-contracts/contracts/common/libraries/DataEncoding.sol` at `b17415d20`, with the call
sites that hash its outputs: the router's handler registration (`AssetRouterBase.sol:65-76`), the
vault's native registration and `assetIdCheck` (`NativeTokenVaultBase.sol:492-499`, `:557`), and the
L1 nullifier's deposit record and claim (`L1Nullifier.sol:155-163`, `:234-247`). The Specs headers
give every line. The modelled functions are the same at the old interop pin `c67894b9`.

Review `Specs/` for the byte layouts and the model instances, and `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact
named propositions, plus auxiliary lemmas. `AssetIdRuns` and `BurnDataSlice` add no definitions;
their spec modules only import and explain.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| AssetId | [Specs/AssetId.lean](Specs/AssetId.lean) | [Properties/AssetId.lean](Properties/AssetId.lean) | [Proofs/AssetId.lean](Proofs/AssetId.lean) |
| AssetIdRuns | [Specs/AssetIdRuns.lean](Specs/AssetIdRuns.lean) | [Properties/AssetIdRuns.lean](Properties/AssetIdRuns.lean) | [Proofs/AssetIdRuns.lean](Proofs/AssetIdRuns.lean) |
| TxDataHash | [Specs/TxDataHash.lean](Specs/TxDataHash.lean) | [Properties/TxDataHash.lean](Properties/TxDataHash.lean) | [Proofs/TxDataHash.lean](Proofs/TxDataHash.lean) |
| BurnDataSlice | [Specs/BurnDataSlice.lean](Specs/BurnDataSlice.lean) | [Properties/BurnDataSlice.lean](Properties/BurnDataSlice.lean) | [Proofs/BurnDataSlice.lean](Proofs/BurnDataSlice.lean) |

- **AssetId.** The library's four id encoders and `assetIdCheck` at byte level, and byte-level
  instances of the router's and the vault's abstract id hashes (`routerEnc keccak`,
  `vaultEnc keccak`). Every preimage is 96 bytes and determines its arguments. The model instances
  are the library on real addresses (`RouterModelIsLibrary`, `VaultModelIsLibrary`). The bounded
  premises `IdInjOn (routerEnc keccak) S` and `IdAssumptionsOn (vaultEnc keccak) S` of the router and
  vault models hold exactly when keccak has no collision (vault: and no zero preimage) among the
  preimages of `S` (`RouterIdInjOnIffNoCollision`, `VaultIdAssumptionsOnIffNoKeccakEvent`).
  `VaultModelIsRouterModelAtNtv` relates the router's atomic-recovery model's `ntvId` (a model of
  the old pin `c67894b9`, in `AssetRouterBase`) to the vault instance.
- **AssetIdRuns.** The router's and the vault's id-dependent results with `enc := routerEnc keccak`
  / `e := vaultEnc keccak` and no premise on keccak: the model's conclusion, or a keccak collision
  (vault: or zero preimage) on preimages the call or the logged run names. These are
  reduction-style forms of results that `CRYPTO-ID` (ASSUMPTIONS.md) covers. They inherit the
  scope of the router (`AssetRouterBase` `HandlerRegistration`) and vault (`NativeTokenVaultBase`
  `RegistryAndEscrow`) models they instantiate, so they are not listed as headlines here.
- **TxDataHash.** `encodeTxDataHash`'s preimage `0x01 || abi.encode(address, bytes32, bytes)`, the
  legacy `abi.encode(address, address, uint256)` format the `b17415d20` comment calls removed (its
  layout is the one the old pin's storage comment gave), and the vault's burn data
  `abi.encode(uint256, address, address)`.
- **BurnDataSlice.** The burn-data encoder and decoder here agree with the independently written
  transcriptions in `Codegen/VaultPreparationSlice`. Agreement of two transcriptions is evidence
  about both, not a proof about solc's output.

Not modelled here: the L1 nullifier's storage, its status oracle and its claim flow (only the
bytes both call sites hash are fixed), keccak itself, and the emitted ABI code.

## History

`History/` is a record of an older commit, not a claim about `b17415d20`.

- **AssetIdRecovery** (`c67894b9`, namespace `Contracts.DataEncoding.History`): the router's
  atomic-recovery model with `enc := routerEnc keccak`. At `c67894b9`
  `L2AssetRouter.recoverAtomicCall` sent every recovered `finalizeDeposit` to the vault; at
  `b17415d20` (`L2AssetRouter.sol:269-303`) it calls the asset's registered handler, so the
  custom-asset results describe the pin only.
  [Specs](History/Specs/AssetIdRecovery.lean), [Properties](History/Properties/AssetIdRecovery.lean),
  [Proofs](History/Proofs/AssetIdRecovery.lean).
