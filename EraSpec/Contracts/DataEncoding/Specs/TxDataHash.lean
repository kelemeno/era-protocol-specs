import EraSpec.Contracts.DataEncoding.Specs.AssetId

/-!
# Spec: the deposit record hash `encodeTxDataHash`, the legacy record format, and the burn data

**This file is definitions only.** Statements are in
`EraSpec.Contracts.DataEncoding.Properties.TxDataHash`, proofs in
`EraSpec.Contracts.DataEncoding.Proofs.TxDataHash`.

## Source (era-contracts `draft/v0.35.0` head `b17415d20`, `l1-contracts/contracts/`)

`common/libraries/DataEncoding.sol`:

    159  function encodeTxDataHash(address _originalCaller, bytes32 _assetId, bytes memory _transferData)
    ...
    164      // The txDataHash is collision-resistant with the removed legacy format: the legacy hash encoded an
    165      // address as its first word, whose most significant bytes are always zero, so it can never collide
    166      // with the `NEW_ENCODING_VERSION` (0x01) prefix used here.
    167      txDataHash = keccak256(
    168          bytes.concat(NEW_ENCODING_VERSION, abi.encode(_originalCaller, _assetId, _transferData))

with `NEW_ENCODING_VERSION = 0x01` (`bridge/asset-router/IAssetRouterBase.sol:6`). It has two call
sites, and they must agree byte for byte:

* the RECORD: `AssetRouterBase._bridgehubDepositNonBaseTokenAsset`
  (`bridge/asset-router/AssetRouterBase.sol:162-166`) computes it for a deposit, and the L1
  nullifier stores it at `depositHappened[chainId][txHash]` (`bridge/L1Nullifier.sol:155-163`,
  reached through `L1AssetRouter.bridgehubConfirmL2Transaction`, `L1AssetRouter.sol:244-250`);
* the CLAIM: `L1Nullifier._verifyAndClearTransfer` (`bridge/L1Nullifier.sol:234-247`) recomputes
  it from the claimant's `(depositSender, assetId, assetData)` and reverts with
  `DepositDoesNotExist` unless it equals the stored word, then deletes the slot.

The legacy format. No code path at `b17415d20` computes a legacy hash; the comment at
`DataEncoding.sol:164-166` calls it removed and says only that its first word was an address. Its
layout is the one the storage comment of the old interop pin `c67894b9` gave
(`bridge/L1Nullifier.sol:64` there):

    // keccak256(abi.encode(account, tokenAddress, amount)) for legacy transfers

At `b17415d20` that storage comment (`L1Nullifier.sol:64-66`) names only the record format,
`keccak256(0x01 || abi.encode(originalCaller, assetId, transferData))`. The comment's claim that
the two formats cannot collide because their first bytes differ is checked here in two halves:
`NewNeverLegacy` (the preimages differ) and `NewHashMatchesLegacyOnlyByCollision` (equal hashes
are a keccak collision).

`decodeBridgeBurnData` (`DataEncoding.sol:51-60`) is the NTV's parser for the `_data` of
`bridgeBurn` (in `_decodeBurnAndCheckAssetId`, `NativeTokenVaultBase.sol:341`) and of
`tryRegisterTokenFromBurnData` (`:323`):

    54      if (_data.length != 96) { revert InvalidNTVBurnData(); }
    59      (amount, receiver, maybeTokenAddress) = abi.decode(_data, (uint256, address, address));

and `encodeBridgeBurnData` (`:35-41`) is `abi.encode(_amount, _remoteReceiver, _maybeTokenAddress)`.
They are `decodeNtvBurnData` and `encodeNtvBurnData` here, on the vault model's `BurnData`.

The two meet at the claim. After `_verifyAndClearTransfer`, the nullifier passes the claim's
`(depositSender, assetId, assetData)` to the router, which checks that the asset's handler is
allowed for the chain (`_checkAssetHandlerAllowed`, reject-only) and forwards `assetData` as `_data`
to the asset's handler (`L1AssetRouter.bridgeConfirmTransferResult`,
`bridge/asset-router/L1AssetRouter.sol:306-319`). For a vault asset the handler is
`L1NativeTokenVault.bridgeConfirmTransferResult` (`bridge/ntv/L1NativeTokenVault.sol:351-380`),
which accepts only the failure status, decodes `_data` with `decodeBridgeBurnData`, requires a
nonzero amount, and pays that amount to `depositSender` (`_disburseFailedTransfer`). So for a
vault asset the hashed transfer data is burn data, and its amount and the claimed sender are
what the refund pays.

The modelled code is the same at the earlier pins (`c67894b9`, `e561b9cc2`), at other line
numbers.

## The ABI layout

`abi.encode(address, bytes32, bytes)` is three heads and one tail (Solidity ABI specification):

* the address head (`encAddr`) and the `bytes32` head (`encWord`);
* the offset of the dynamic argument, `0x60 = 3 · 32`, from the start of the encoding;
* the tail: the length word of the bytes, then the bytes right-padded with zeros to a multiple
  of 32 (`pad32`, from `InteropDataEncoding`).

`bytes.concat(0x01, X)` is the byte `0x01` followed by `X`. So the record preimage is
`0x01 :: (four words ++ pad32 transferData)`, and the legacy one three words.

`abi.decode(data, (uint256, address, address))` reads three words. With the ABI coder v2
default of solc 0.8, it reverts when an address word does not fit 160 bits
(`validator_revert_t_address`). Trailing bytes would be ignored, but the explicit length check
rejects them.

## Model boundaries

* `keccak` is arbitrary (`Keccak`, from `Specs/AssetId.lean`).
* The layouts follow the ABI specification, not the emitted Yul (`SOL-ABI`).
* The L1 nullifier's storage, its status oracle and its claim flow are not modelled here; this
  topic only fixes the bytes both call sites hash.
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding (toBytesBE fromBytesBE word pad32 HashCollision)

/-- `NEW_ENCODING_VERSION = 0x01` (`bridge/asset-router/IAssetRouterBase.sol:6`). -/
def newEncodingVersion : UInt8 := 0x01

/-! ## The record format -/

/-- `abi.encode(_originalCaller, _assetId, _transferData)`, types `(address, bytes32, bytes)`:
the address head, the asset-id head, the offset `0x60`, the length word, and the bytes padded
to a multiple of 32. -/
def txDataAbiEncoding (s : Addr) (a : UInt256) (d : List UInt8) : List UInt8 :=
  encAddr s ++ encWord a ++ word 0x60 ++ word d.length ++ pad32 d

/-- **THE RECORD PREIMAGE**:
`bytes.concat(NEW_ENCODING_VERSION, abi.encode(_originalCaller, _assetId, _transferData))`
(`DataEncoding.sol:167-169`). -/
def txDataPreimage (s : Addr) (a : UInt256) (d : List UInt8) : List UInt8 :=
  newEncodingVersion :: txDataAbiEncoding s a d

/-- `encodeTxDataHash(_originalCaller, _assetId, _transferData)` (`DataEncoding.sol:159-170`):
the value the nullifier records and the value a claim recomputes. -/
def encodeTxDataHash (keccak : Keccak) (s : Addr) (a : UInt256) (d : List UInt8) : UInt256 :=
  keccak (txDataPreimage s a d)

/-! ## The legacy format -/

/-- **THE LEGACY PREIMAGE**: `abi.encode(account, tokenAddress, amount)`, types
`(address, address, uint256)`, the layout the `c67894b9` storage comment gave
(`L1Nullifier.sol:64` there). -/
def legacyTxDataPreimage (account token : Addr) (amount : UInt256) : List UInt8 :=
  encAddr account ++ encAddr token ++ encWord amount

/-- The legacy record hash, `keccak256(abi.encode(account, tokenAddress, amount))`. -/
def legacyTxDataHash (keccak : Keccak) (account token : Addr) (amount : UInt256) : UInt256 :=
  keccak (legacyTxDataPreimage account token amount)

/-! ## The burn data -/

/-- `encodeBridgeBurnData(_amount, _remoteReceiver, _maybeTokenAddress)` (`DataEncoding.sol:35-41`):
`abi.encode(uint256, address, address)` of the vault model's burn data. -/
def encodeNtvBurnData (b : NativeTokenVaultBase.BurnData) : List UInt8 :=
  encWord b.amount ++ encAddr b.receiver ++ encAddr b.tokenHint

/-- `decodeBridgeBurnData(_data)` (`DataEncoding.sol:51-60`); `none` is a revert. It reverts with
`InvalidNTVBurnData` unless the data is exactly 96 bytes. It then `abi.decode`s three words, and
reverts when the receiver or token word does not fit 160 bits. -/
def decodeNtvBurnData (data : List UInt8) : Option NativeTokenVaultBase.BurnData :=
  if data.length = 96 then
    if hr : fromBytesBE ((data.drop 32).take 32) < 2 ^ 160 then
      if ht : fromBytesBE ((data.drop 64).take 32) < 2 ^ 160 then
        some ⟨Nat.toUInt256 (fromBytesBE (data.take 32)), ⟨_, hr⟩, ⟨_, ht⟩⟩
      else none
    else none
  else none

end Contracts.DataEncoding
