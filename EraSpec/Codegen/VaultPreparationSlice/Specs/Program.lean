import EraSpec.Codegen.Calls
import EraSpec.Codegen.BridgedTokenSlice.Specs.Program

/-!
# The vault's preparation path as a program

Transcribed from era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af` (paths under
`l1-contracts/contracts/`): `bridge/ntv/NativeTokenVaultBase.sol` `bridgeBurn` (315-339)
with its modifiers, `_decodeBurnAndCheckAssetId` (357-374), `_bridgeBurnToken` (381-430),
`_getERC20Metadata` (432-444) and `_getTokenAndBridgeToChain` (446-479);
`bridge/interfaces/AssetHandlerModifiers.sol` `requireZeroValue` (11-16);
`common/libraries/DataEncoding.sol` `decodeBridgeBurnData` (51-60) and
`encodeBridgeMintData` (84-93); and OpenZeppelin upgradeable v4 at submodule commit
`2d081f24cac1a867f6f73d512f2022e1fa987854`, `security/PausableUpgradeable.sol`
`whenNotPaused` (49-52) and `_requireNotPaused` (76-78).

The body keeps the source's statement order and revert data, so the two can be
compared on which check fails first, not only on success.  Each statement cites the
source line it stands for.

**The branch transcribed** is the registered bridged-token case: the asset's origin
chain is not this chain, and the asset is not the base token.  That is the branch
`Contracts.NativeTokenVaultBase.prepare` models.  At the two places the source
branches away from it, the program reverts with `OutsideSlice()` instead:

* `originChainId[_assetId] == block.chainid` (a native token: WETH check and
  `_depositFunds`, `NativeTokenVaultBase.sol:392-396, 473-477`);
* `_assetId == _baseTokenAssetId()` (the base-token branch, `:456-467`).

`OutsideSlice` is not a source error.  It marks the edge of the comparison scope.  Below
the first edge `_isBridgedToken` (`:389`) is true, so its later tests (`:410`, `:438`,
`:471`) are transcribed as their bridged branch.

**Other deliberate differences**, all outside the comparison scope:

* `bytes32` values (`_assetId`, the `assetId` mapping) are words of type `uint256`, as
  `Codegen.Ty` has no `bytes32`.  The ABI encoding of the two is the same word; the
  function selector differs.
* `_assetRouter()` and `_baseTokenAssetId()` are immutables or constants of the L1 and
  L2 vaults.  Here they are the storage slots `_assetRouter` and `_baseTokenAssetId`.
  `block.chainid` is the call's chain id.
* `_handleBridgeToChain` (`:527`) and `_getERC20GettersInner` (`:505-510`) are
  `internal virtual`.  They are hooks here, given meaning by the world the program runs
  in.  `getERC20Getters` (`:501-503`) is inlined into its one call.
* `_getOriginTokenFromAddress` (`:124-126`) is the base contract's, a call to the token's
  `originToken()`.  `L2NativeTokenVault` overrides it only for the base-token system
  contract (`L2NativeTokenVault.sol:333-338`), whose asset is the base token, outside the
  slice.
* Storage names carry a leading underscore and the `assetId` mapping is `_assetIdOf`, so
  that no mapping shares a name with a getter or a local.
* `bridgeBurn` is not `nonReentrant` at the pin, and there is nothing to guard here: the
  token makes no calls back (`Codegen.Calls` has no reentrancy).
* No ownership, pausing or unpausing, registration, `bridgeMint`, recovery, legacy
  paths or storage-layout compatibility.  The views read the mappings the source
  exposes as public getters.

The token the vault calls is `tokenProgram`: the bridged-token slice of
`Codegen.BridgedTokenSlice` with the two getters `originToken()` and `assetId()` of the
public variables at `bridge/BridgedStandardERC20.sol:42,48` added.
-/

namespace Codegen.VaultPreparationSlice

open Codegen Codegen.Calls

/-! ## The token -/

/-- `originToken()`, the getter of `address public override originToken`
(`BridgedStandardERC20.sol:42`). -/
def originTokenFn : Fn where
  name := "originToken"
  params := []
  returns := some .address
  mutability := .view
  body := [.ret (.sload "_originToken")]

/-- `assetId()`, the getter of `bytes32 public assetId` (`BridgedStandardERC20.sol:48`). -/
def assetIdFn : Fn where
  name := "assetId"
  params := []
  returns := some .uint256
  mutability := .view
  body := [.ret (.sload "_assetId")]

/-- The token: `Codegen.BridgedTokenSlice.program`'s functions, unchanged, then the two
getters.  The constructor also takes the origin token, and refuses `0` for it as
`bridgeInitialize` does (`BridgedStandardERC20.sol:86`). -/
def tokenProgram : Contract where
  name := "BridgedTokenSliceWithOrigin"
  scalars := BridgedTokenSlice.program.scalars ++
    [⟨"_originToken", .address⟩, ⟨"_assetId", .uint256⟩]
  maps := BridgedTokenSlice.program.maps
  errors := BridgedTokenSlice.program.errors
  events := BridgedTokenSlice.program.events
  ctorParams := [⟨"vault", .address⟩, ⟨"assetId_", .uint256⟩, ⟨"originToken_", .address⟩]
  ctorBody :=
    [ .require (.ne (.var "vault") BridgedTokenSlice.zeroAddr) (.custom "ZeroAddress" []),
      .require (.ne (.var "originToken_") BridgedTokenSlice.zeroAddr) (.custom "ZeroAddress" []),
      .sstore "_nativeTokenVault" (.var "vault"),
      .sstore "_assetId" (.var "assetId_"),
      .sstore "_originToken" (.var "originToken_") ]
  fns := BridgedTokenSlice.program.fns ++ [originTokenFn, assetIdFn]

/-! ## The vault -/

def zeroAddr : Expr := .lit .address 0
def zero : Expr := .lit .uint256 0

/-- `if (parsedTokenAddress == address(0)) parsedTokenAddress = tokenAddress[_suppliedAssetId];`
(`NativeTokenVaultBase.sol:363-367`): a zero token hint means the token registered for the
asset. -/
def resolveToken : XStmt :=
  .ifThen (.eq (.var "parsedTokenAddress") zeroAddr)
    (.assign "parsedTokenAddress" (.mload "_tokenAddress" (.var "_assetId")))

/-- `bridgeBurn(uint256 _chainId, uint256 _l2MsgValue, bytes32 _assetId,
address _originalCaller, bytes calldata _data) payable returns (bytes)`,
`NativeTokenVaultBase.sol:315-339`, with the helpers it calls inlined in call order. -/
def bridgeBurn : XFn where
  name := "bridgeBurn"
  params :=
    [ ⟨"_chainId", .base .uint256⟩, ⟨"_l2MsgValue", .base .uint256⟩,
      ⟨"_assetId", .base .uint256⟩, ⟨"_originalCaller", .base .address⟩,
      ⟨"_data", .bytes⟩ ]
  returns := some .bytes
  payable := true
  body :=
    [ -- `requireZeroValue(_l2MsgValue)`: AssetHandlerModifiers.sol:12-14
      .base (.require (.eq (.var "_l2MsgValue") zero) (.custom "NonEmptyMsgValue" [])),
      -- `onlyAssetRouter`: NativeTokenVaultBase.sol:108
      .base (.require (.eq .sender (.sload "_assetRouter")) (.custom "Unauthorized" [.sender])),
      -- `whenNotPaused`: PausableUpgradeable.sol:50, 77
      .base (.require (.eq (.sload "_paused") (.lit .bool 0)) (.message "Pausable: paused")),
      -- `_decodeBurnAndCheckAssetId` (:330, :357-374) and
      -- `DataEncoding.decodeBridgeBurnData` (DataEncoding.sol:54-59)
      .requireLength "_data" 96 (.custom "InvalidNTVBurnData" []),
      .decode "_data" [⟨"amount", .uint256⟩, ⟨"receiver", .address⟩,
        ⟨"parsedTokenAddress", .address⟩],
      resolveToken,                                                             -- :363-367
      .base (.require (.ne (.var "parsedTokenAddress") zeroAddr)
        (.custom "ZeroAddress" [])),                                            -- :370
      .base (.local_ .uint256 "storedAssetId"
        (.mload "_assetIdOf" (.var "parsedTokenAddress"))),                    -- :372
      .base (.require (.eq (.var "_assetId") (.var "storedAssetId"))
        (.custom "AssetIdMismatch" [.var "storedAssetId", .var "_assetId"])),  -- :373
      -- `_bridgeBurnToken`: :390
      .base (.require (.ne (.var "amount") zero) (.custom "AmountMustBeGreaterThanZero" [])),
      -- slice edge, the native-token branch: :389, :392-396
      .base (.require (.ne (.mload "_originChainId" (.var "_assetId")) (.var blockChainId))
        (.custom "OutsideSlice" [])),
      -- `_getTokenAndBridgeToChain`; slice edge, the base-token branch: :456
      .base (.require (.ne (.var "_assetId") (.sload "_baseTokenAssetId"))
        (.custom "OutsideSlice" [])),
      .hook "_handleBridgeToChain" [.var "_chainId", .var "_assetId", .var "amount"]
        .none,                                                                 -- :469
      .base (.require (.eq (.var msgValue) zero) (.custom "NonEmptyMsgValue" [])), -- :470
      .call (.var "parsedTokenAddress") "bridgeBurn" [.var "_originalCaller", .var "amount"]
        .none,                                                                 -- :472
      -- origin token of a bridged token: :409-413, `_getOriginTokenFromAddress` :124-126
      .call (.var "parsedTokenAddress") "originToken" [] (.word "originToken"),  -- :411
      .base (.require (.ne (.var "originToken") zeroAddr) (.custom "ZeroAddress" [])), -- :412
      -- `_getERC20Metadata`: :437-443, `getERC20Getters` :501-503
      .base (.local_ .uint256 "tokenOriginChainId"
        (.mload "_originChainId" (.var "_assetId"))),                          -- :437
      .base (.require (.ne (.var "tokenOriginChainId") zero) (.custom "ZeroAddress" [])), -- :441
      .hook "_getERC20GettersInner" [.var "parsedTokenAddress", .var "tokenOriginChainId"]
        (.bytes "erc20Metadata"),                                              -- :502
      -- `DataEncoding.encodeBridgeMintData`: :415-421, DataEncoding.sol:92
      .encode "_bridgeMintData"
        [ .word .address (.var "_originalCaller"), .word .address (.var "receiver"),
          .word .address (.var "originToken"), .word .uint256 (.var "amount"),
          .bytes "erc20Metadata" ],
      -- `emit BridgeBurn(...)`: :423-429
      .base (.emit "BridgeBurn"
        [.var "_chainId", .var "_assetId", .var "_originalCaller", .var "receiver", .var "amount"]),
      .retBytes "_bridgeMintData" ]

/-- `paused()`: OZ `PausableUpgradeable.paused`. -/
def pausedFn : XFn where
  name := "paused"
  params := []
  returns := some (.base .bool)
  payable := false
  body := [.base (.ret (.sload "_paused"))]

/-- `tokenAddress(bytes32)`: the public mapping at `NativeTokenVaultBase.sol:80`. -/
def tokenAddressFn : XFn where
  name := "tokenAddress"
  params := [⟨"assetId_", .base .uint256⟩]
  returns := some (.base .address)
  payable := false
  body := [.base (.ret (.mload "_tokenAddress" (.var "assetId_")))]

/-- `assetId(address)`: the public mapping at `NativeTokenVaultBase.sol:85`. -/
def assetIdOfFn : XFn where
  name := "assetId"
  params := [⟨"token", .base .address⟩]
  returns := some (.base .uint256)
  payable := false
  body := [.base (.ret (.mload "_assetIdOf" (.var "token")))]

/-- `originChainId(bytes32)`: the public mapping at `NativeTokenVaultBase.sol:75`. -/
def originChainIdFn : XFn where
  name := "originChainId"
  params := [⟨"assetId_", .base .uint256⟩]
  returns := some (.base .uint256)
  payable := false
  body := [.base (.ret (.mload "_originChainId" (.var "assetId_")))]

def vaultProgram : XContract where
  name := "NativeTokenVaultPreparationSlice"
  scalars := [⟨"_assetRouter", .address⟩, ⟨"_paused", .bool⟩, ⟨"_baseTokenAssetId", .uint256⟩]
  maps :=
    [ ("_tokenAddress", .uint256, .address), ("_assetIdOf", .address, .uint256),
      ("_originChainId", .uint256, .uint256) ]
  errors :=
    [ ⟨"NonEmptyMsgValue", []⟩, ⟨"Unauthorized", [⟨"caller", .address⟩]⟩,
      ⟨"InvalidNTVBurnData", []⟩, ⟨"ZeroAddress", []⟩,
      ⟨"AssetIdMismatch", [⟨"expected", .uint256⟩, ⟨"supplied", .uint256⟩]⟩,
      ⟨"AmountMustBeGreaterThanZero", []⟩, ⟨"OutsideSlice", []⟩ ]
  events :=
    [ ⟨"BridgeBurn", [⟨"chainId", .uint256, true⟩, ⟨"assetId", .uint256, true⟩,
        ⟨"sender", .address, true⟩, ⟨"receiver", .address, false⟩,
        ⟨"amount", .uint256, false⟩]⟩ ]
  fns := [bridgeBurn, pausedFn, tokenAddressFn, assetIdOfFn, originChainIdFn]

end Codegen.VaultPreparationSlice
