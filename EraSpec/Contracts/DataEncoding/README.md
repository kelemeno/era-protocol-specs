# DataEncoding

Source: `contracts/common/libraries/DataEncoding.sol` in the pinned era-contracts tree
(`c67894b9`), with the call sites that hash its outputs: the router's handler registration, the
vault's native registration and `assetIdCheck`, and the L1 nullifier's deposit record and claim.
`Specs/AssetId.lean` and `Specs/TxDataHash.lean` also record the same code at `e561b9cc2`,
draft/v0.35.0 (`d9f6789`, `b17415d20`) and main (`3605e82`, `70096e2ea`): the modelled functions
are unchanged there; line numbers move, and on v0.35.0 and `e561b9cc2` some internal getters at
the call sites are renamed. `Specs/AssetIdRecovery.lean` records what did change: on those trees
`L2AssetRouter.recoverAtomicCall` sends a refund to the asset's registered handler, not always to
the vault, so the custom-asset results of `AssetIdRecovery` describe `c67894b9` only.

Review `Specs/` for the byte layouts and the model instances, and `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact
named propositions, plus auxiliary lemmas. `AssetIdRuns`, `AssetIdRecovery` and
`BurnDataSlice` add no definitions; their spec modules only import and explain.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| AssetId | [Specs/AssetId.lean](Specs/AssetId.lean) | [Properties/AssetId.lean](Properties/AssetId.lean) | [Proofs/AssetId.lean](Proofs/AssetId.lean) |
| AssetIdRuns | [Specs/AssetIdRuns.lean](Specs/AssetIdRuns.lean) | [Properties/AssetIdRuns.lean](Properties/AssetIdRuns.lean) | [Proofs/AssetIdRuns.lean](Proofs/AssetIdRuns.lean) |
| AssetIdRecovery | [Specs/AssetIdRecovery.lean](Specs/AssetIdRecovery.lean) | [Properties/AssetIdRecovery.lean](Properties/AssetIdRecovery.lean) | [Proofs/AssetIdRecovery.lean](Proofs/AssetIdRecovery.lean) |
| TxDataHash | [Specs/TxDataHash.lean](Specs/TxDataHash.lean) | [Properties/TxDataHash.lean](Properties/TxDataHash.lean) | [Proofs/TxDataHash.lean](Proofs/TxDataHash.lean) |
| BurnDataSlice | [Specs/BurnDataSlice.lean](Specs/BurnDataSlice.lean) | [Properties/BurnDataSlice.lean](Properties/BurnDataSlice.lean) | [Proofs/BurnDataSlice.lean](Proofs/BurnDataSlice.lean) |

No property in this folder takes a premise on keccak. `keccak` is an arbitrary function
`List UInt8 → UInt256`, and every hash-level statement either holds for every keccak or
names a keccak event on byte strings the instance determines: `HashCollision keccak x y` on two
named strings (from `InteropDataEncoding`), or `ZeroPreimage keccak x`, keccak sending a named
string to the zero word that every `bytes32` mapping reads as unset. The ABI layouts follow the
Solidity ABI specification, not solc's emitted code (`SOL-ABI`).

- **AssetId.** The library's four id encoders and `assetIdCheck` at byte level, and byte-level
  instances of the router's and the vault's abstract id hashes (`routerEnc keccak`,
  `vaultEnc keccak`). Every preimage is 96 bytes and determines its arguments
  (`AssetIdPreimageInjective` and siblings). The two `encodeAssetId` overloads, the two
  `encodeNTVAssetId` overloads, and the router's id for a vault registration compute the same
  keccak input, so they agree for every keccak (`OverloadsCoincide`,
  `NativeRegistrationIdsAgree`); the model instances are the library on real addresses
  (`RouterModelIsLibrary`, `VaultModelIsLibrary`), and the atomic-recovery model's `ntvId` is the
  vault instance when the configured vault is `L2_NATIVE_TOKEN_VAULT_ADDR`
  (`VaultModelIsRouterModelAtNtv`). The bounded premises `IdInjOn (routerEnc keccak) S` and
  `IdAssumptionsOn (vaultEnc keccak) S` hold exactly when keccak has no collision (vault: and no
  zero preimage) among the preimages of `S` (`RouterIdInjOnIffNoCollision`,
  `VaultIdAssumptionsOnIffNoKeccakEvent`). `assetIdCheck` passes exactly on the vault id of the
  origin pair (`AssetIdCheckPassesIff`, `AssetIdCheckIsRegistryIdCheck`), and two passing checks
  for one id name the same origin pair or a keccak collision on the two named preimages
  (`AssetIdCheckPinsOriginOrCollision`). Every abstract encoding is a keccak instance
  (`RouterEncodingsAreKeccakInstances`, `VaultEncodingsAreKeccakInstances`), the no-break
  premises are satisfiable (`RouterNoBreakSatisfiable`, `VaultNoBreakSatisfiable`), and the
  breaks are contingent (`IdBreaksAreContingent`, `ZeroPreimageIndependentOfCollisions`).
- **AssetIdRuns.** The router's and the vault's id-dependent results with `enc := routerEnc
  keccak` / `e := vaultEnc keccak` and no premise on keccak: the model's conclusion, or a keccak
  collision (vault: or zero preimage) on the two preimages one call compares
  (`NoHijackOrKeccakCollision`, `NtvTouchesOnlyItsOwnIdsOrKeccakCollision`,
  `RegisterNativeIdFreshOrKeccakEvent`), or among the preimages a logged run hashed
  (`LoggedRunNoHijackOrKeccakCollision`, which adds the watched triple,
  `LoggedRunKeepsVaultRoutesOrKeccakCollision`, `LoggedRunSoundOrKeccakEvent`). These are
  reduction-style (collision-finding) forms of results that `CRYPTO-ID` (ASSUMPTIONS.md) covers;
  that row lists which results are restated. For the others, the bounded premise at byte level is
  exactly the absence of the named events (topic `AssetId`). Each has a witness with the event
  disjunct false (the abstract model's own witness, carried to byte level), and the event
  disjuncts fire: `KeccakCollisionHijacks`,
  `KeccakCollisionOnLogTakesOverLiveRoute`, `RegisterNativeIdTakenByKeccakCollision`,
  `LoggedRunSoundEventNeeded`.
- **AssetIdRecovery** (`c67894b9`). The atomic-recovery model's abstract id guard
  `FailsAssetIdCheck` is, at byte level with the vault at `L2_NATIVE_TOKEN_VAULT_ADDR`, exactly
  the library's `assetIdCheck` reverting (`FailsAssetIdCheckIsLibraryRevert`). Its custom-asset
  results (`AssetRouterBase` `AtomicRecovery`, `MODEL-ATOMIC-RECOVERY`) at byte level, with no
  premise on keccak: the refund of a custom asset's `finalizeDeposit` call reverts, or keccak
  collides on the custom preimage and a named NTV preimage
  (`CustomAssetRecoveryRevertsOrKeccakCollision`,
  `CustomHandlerDepositRefundRevertsOrKeccakCollision`). The witnesses meet every premise with
  the collision disjuncts false, on a custom asset registered on the witness world's own chain;
  under the collision the refund of a custom asset the vault does not know returns `true`
  instead of reverting (`KeccakCollisionLetsVaultMintCustomAsset`).
- **TxDataHash.** `encodeTxDataHash`'s preimage `0x01 || abi.encode(address, bytes32, bytes)`,
  the legacy `abi.encode(address, address, uint256)` format named by the nullifier's storage
  comment, and the vault's burn data `abi.encode(uint256, address, address)`. The record
  preimage is `129 + 32·⌈len/32⌉` bytes (`TxDataPreimageLength`, `TxDataPreimageMinimumIs129`),
  determines its record for `len < 2^256` (`NewPreimageInjective`), and is never a legacy
  preimage, by its first byte and by its length (`NewNeverLegacy`). At the hash level: equal
  record hashes mean the same record or a keccak collision on the two named preimages
  (`TxDataHashBindsOrCollision`); a record hash equals a legacy hash only by a named collision
  (`NewHashMatchesLegacyOnlyByCollision`); a zero record hash is a zero preimage
  (`TxDataHashZeroIsPreimageEvent`). `TxDataHashWitness` and the countermodel
  `TxDataHashCollisionDisjunctNeeded` use an NTV deposit whose claim changes only the amount.
  The decoder accepts exactly the 96-byte strings whose two address words fit 160 bits and
  inverts the encoder (`BurnDataDecodeIffEncode`, `BurnDataAcceptsIff`). Together: a claim whose
  transfer data the vault's parser accepts and whose hash matches an NTV deposit record names
  that record's sender, asset id and burn data, or keccak collides on the two named record
  preimages (`NtvClaimNamesRecordedDepositOrCollision`; the L1 vault then pays the decoded
  amount to the claimed sender, which is described in the spec, not modelled).
- **BurnDataSlice.** The burn-data encoder and decoder here agree with the independently written
  transcriptions in `Codegen/VaultPreparationSlice` (`EncodeBurnDataAgreesWithSlice`,
  `DecodeBurnDataAgreesWithSlice`). Agreement of two transcriptions is evidence about both, not
  a proof about solc's output.

Not modelled here: the L1 nullifier's storage, its status oracle and its claim flow (only the
bytes both call sites hash are fixed), keccak itself, and the emitted ABI code.
