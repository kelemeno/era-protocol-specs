import EraSpec.Contracts.DataEncoding.Specs.Abi

/-!
# Spec: `DataEncoding`'s transfer-data encoders and decoders

Source: `l1-contracts/contracts/common/libraries/DataEncoding.sol` at era-contracts
`d9f678900e1bc8286412b78f56d4a9f443983c29` (draft/v0.35.0). Line numbers below are in that file
unless another file is named.

Each encoder is transcribed as the byte string `abi.encode` / `bytes.concat` / `abi.encodePacked`
produces (see `Specs/Abi.lean`); each decoder as a partial function, `none` being a revert, with
the source's own checks in source order followed by the checks of `abi.decode`.

| Solidity | Lean |
|---|---|
| `encodeBridgeBurnData` (:35-41) | `encodeBridgeBurnData` |
| `decodeBridgeBurnData` (:51-60) | `decodeBridgeBurnData` |
| `encodeAssetRouterBridgehubDepositData` (:62-67) | `encodeDepositData` |
| `decodeAssetRouterBridgehubDepositData` (:69-75) | `decodeDepositData` |
| `encodeBridgeMintData` (:84-92) | `encodeBridgeMintData` |
| `decodeBridgeMintData` (:101-118) | `decodeBridgeMintData` |
| `decodeTokenData` (:173-185) | `decodeTokenData` |
| `encodeTokenData` (:194-201) | `encodeTokenData` |
| `encodeAssetRouterFinalizeDepositData` (:215-227) | `encodeFinalizeDepositData` |
| `decodeAssetRouterFinalizeDepositData` (:229-245) | `decodeFinalizeDepositData` |

Not modelled here: `getSelector` (:297-300), and the interop call-starter builders (:254-295),
which are modelled in `Contracts/AttributesDecoder` where their output is decoded.
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding

/-! ## Bridge burn data: `abi.encode(uint256, address, address)` -/

/-- `encodeBridgeBurnData(_amount, _remoteReceiver, _maybeTokenAddress)` (:35-41):
`abi.encode(_amount, _remoteReceiver, _maybeTokenAddress)`, three head words. -/
def encodeBridgeBurnData (amount receiver token : ℕ) : List UInt8 :=
  word amount ++ (word receiver ++ word token)

/-- `decodeBridgeBurnData(_data)` (:51-60). First the source's own check
`if (_data.length != 96) revert InvalidNTVBurnData()` (:54-57), then
`abi.decode(_data, (uint256, address, address))` (:59), which validates the two address words. -/
def decodeBridgeBurnData (d : List UInt8) : Option (ℕ × ℕ × ℕ) :=
  if d.length ≠ 96 then none
  else do
    let r ← decAddr d 32
    let t ← decAddr d 64
    pure (readWord d 0, r, t)

/-- **Ablation, not source.** `decodeBridgeBurnData` with its own length check (:54-57) removed:
only `abi.decode`'s head check (`length ≥ 96`) remains. Used to show that check is load-bearing. -/
def decodeBridgeBurnDataNoLengthCheck (d : List UInt8) : Option (ℕ × ℕ × ℕ) :=
  if d.length < 96 then none
  else do
    let r ← decAddr d 32
    let t ← decAddr d 64
    pure (readWord d 0, r, t)

/-! ## Bridge mint data: `abi.encode(address, address, address, uint256, bytes)` -/

/-- `encodeBridgeMintData(_originalCaller, _remoteReceiver, _originToken, _amount, _erc20Metadata)`
(:84-92). Five head words (the fifth the offset `0xa0 = 160` of the `bytes` tail), then the tail. -/
def encodeBridgeMintData (caller receiver token amount : ℕ) (metadata : List UInt8) : List UInt8 :=
  word caller ++ (word receiver ++ (word token ++ (word amount ++ (word 160 ++ bytesTail metadata))))

/-- `decodeBridgeMintData(_bridgeMintData)` (:101-118): `abi.decode(_, (address, address, address,
uint256, bytes))` with no length check of its own. Returns
`(originalCaller, remoteReceiver, originToken, amount, erc20Metadata)`. -/
def decodeBridgeMintData (d : List UInt8) : Option (ℕ × ℕ × ℕ × ℕ × List UInt8) :=
  if d.length < 160 then none
  else do
    let c ← decAddr d 0
    let r ← decAddr d 32
    let t ← decAddr d 64
    let m ← decBytes d 128
    pure (c, r, t, readWord d 96, m)

/-! ## Asset-router bridgehub deposit data: `0x01 ‖ abi.encode(bytes32, bytes)` -/

/-- `encodeAssetRouterBridgehubDepositData(_assetId, _transferData)` (:62-67):
`bytes.concat(NEW_ENCODING_VERSION, abi.encode(_assetId, _transferData))`. -/
def encodeDepositData (assetId : ℕ) (transferData : List UInt8) : List UInt8 :=
  NEW_ENCODING_VERSION :: (word assetId ++ (word 64 ++ bytesTail transferData))

/-- `decodeAssetRouterBridgehubDepositData(_dataWithVersion)` (:69-75), in source order:
`require(length >= 33)` (:72), `require(_dataWithVersion[0] == NEW_ENCODING_VERSION)` (:73), then
`abi.decode(_dataWithVersion[1:], (bytes32, bytes))` (:74). -/
def decodeDepositData (d : List UInt8) : Option (ℕ × List UInt8) :=
  if d.length < 33 then none
  else if d.head? ≠ some NEW_ENCODING_VERSION then none
  else if (d.drop 1).length < 64 then none
  else do
    let t ← decBytes (d.drop 1) 32
    pure (readWord (d.drop 1) 0, t)

/-! ## Token data: `0x01 ‖ abi.encode(uint256, bytes, bytes, bytes)` -/

/-- `encodeTokenData(_chainId, _name, _symbol, _decimals)` (:194-201):
`bytes.concat(NEW_ENCODING_VERSION, abi.encode(_chainId, _name, _symbol, _decimals))`. Four head
words: the chain id and three tail offsets (`0x80`, then each following tail's start). -/
def encodeTokenData (chainId : ℕ) (name symbol decimals : List UInt8) : List UInt8 :=
  NEW_ENCODING_VERSION ::
    (word chainId ++ (word 128 ++ (word (128 + (bytesTail name).length) ++
      (word (128 + (bytesTail name).length + (bytesTail symbol).length) ++
        (bytesTail name ++ (bytesTail symbol ++ bytesTail decimals))))))

/-- `decodeTokenData(_tokenData)` (:173-185): `if (length == 0) revert EmptyData()` (:176-178);
the first byte must be `NEW_ENCODING_VERSION` else `UnsupportedEncodingVersion` (:179-184); then
`abi.decode(_tokenData[1:], (uint256, bytes, bytes, bytes))` (:181). -/
def decodeTokenData (d : List UInt8) : Option (ℕ × List UInt8 × List UInt8 × List UInt8) :=
  if d.length = 0 then none
  else if d.head? ≠ some NEW_ENCODING_VERSION then none
  else if (d.drop 1).length < 128 then none
  else do
    let n ← decBytes (d.drop 1) 32
    let s ← decBytes (d.drop 1) 64
    let k ← decBytes (d.drop 1) 96
    pure (readWord (d.drop 1) 0, n, s, k)

/-! ## Finalize-deposit message: `abi.encodePacked(bytes4, uint256, bytes32, bytes)` -/

/-- `encodeAssetRouterFinalizeDepositData(_messageSourceChainId, _assetId, _transferData)`
(:215-227): `abi.encodePacked(IAssetRouterShared.finalizeDeposit.selector, _messageSourceChainId,
_assetId, _transferData)`. The selector is a parameter `sel < 2^32`. -/
def encodeFinalizeDepositData (sel chainId assetId : ℕ) (transferData : List UInt8) : List UInt8 :=
  be 4 sel ++ (word chainId ++ (word assetId ++ transferData))

/-- `decodeAssetRouterFinalizeDepositData(_l2ToL1message)` (:229-245). `UnsafeBytes.readUint32`
at offset 0 (:236) runs before the length check; it reads out of bounds when the message is
shorter than 4 bytes, but then `require(length >= 68)` (:240) reverts, so the value is never
observed and the model reads `d.take 4`. Then `readUint256` at 4 (:242), `readBytes32` at 36
(:243) and `readRemainingBytes` from 68 (:244). Returns `(selector, sourceChainId, assetId,
transferData)`. -/
def decodeFinalizeDepositData (d : List UInt8) : Option (ℕ × ℕ × ℕ × List UInt8) :=
  if d.length < 68 then none
  else some (fromBytesBE (d.take 4), readWord d 4, readWord d 36, d.drop 68)

end Contracts.DataEncoding
