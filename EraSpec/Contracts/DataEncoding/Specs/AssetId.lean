import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned
import EraSpec.Contracts.AssetRouterBase.Specs.HandlerRegistrationRuns
import EraSpec.Contracts.NativeTokenVaultBase.Specs.ModelCorrespondence

/-!
# Spec: asset ids at byte level — the four `DataEncoding` encoders and `assetIdCheck`

The router and the vault take their asset-id hash as an ABSTRACT function and assume
things about it:

* the router (`Contracts.AssetRouter`, `Specs/HandlerRegistration.lean`) takes
  `enc : AssetIdOf` and the bounded premise `IdInjOn enc S`;
* the vault (`Contracts.NativeTokenVault`, `Specs/RegistryAndEscrow.lean`) takes
  `e : NtvAssetId` and `IdAssumptionsOn e S` (injective and nonzero on `S`).

Nothing so far tied those functions to the bytes the library hashes, to each other, or to
keccak. This file writes the library down at byte level so that the premises can be
reduced to statements about keccak on named byte strings.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.DataEncoding.Properties.AssetId`, proofs in
`EraSpec.Contracts.DataEncoding.Proofs.AssetId`.

## Source (pinned tree `c67894b9`, `l1-contracts/contracts/`)

`common/libraries/DataEncoding.sol`:

    126  function encodeAssetId(uint256 _chainId, bytes32 _assetData, address _sender) ... {
    127      return keccak256(abi.encode(_chainId, _sender, _assetData));
    135  function encodeAssetId(uint256 _chainId, address _tokenAddress, address _sender) ... {
    136      return keccak256(abi.encode(_chainId, _sender, _tokenAddress));
    143  function encodeNTVAssetId(uint256 _chainId, bytes32 _assetData) ... {
    144      return keccak256(abi.encode(_chainId, L2_NATIVE_TOKEN_VAULT_ADDR, _assetData));
    151  function encodeNTVAssetId(uint256 _chainId, address _tokenAddress) ... {
    152      return keccak256(abi.encode(_chainId, L2_NATIVE_TOKEN_VAULT_ADDR, _tokenAddress));
    208  function assetIdCheck(uint256 _tokenOriginChainId, bytes32 _assetId, address _originToken) ... {
    209      bytes32 expectedAssetId = encodeNTVAssetId(_tokenOriginChainId, _originToken);
    210      if (_assetId != expectedAssetId) {
    212          revert AssetIdMismatch(expectedAssetId, _assetId);

Note the argument order: every encoder hashes `(chainId, sender, data)`, while the first
`encodeAssetId` overload takes `(chainId, data, sender)`.

`L2_NATIVE_TOKEN_VAULT_ADDR = address(BUILT_IN_CONTRACTS_OFFSET + 0x04)` with
`BUILT_IN_CONTRACTS_OFFSET = 0x10000` (`common/l2-helpers/L2ContractAddresses.sol:12, 99`).

The call sites that make the overloads matter:

* `bridge/asset-router/AssetRouterBase.sol:78-80` (`_setAssetHandlerAddressThisChain`): the
  router keys a registration by the `bytes32` overload, with the vault caller normalised to
  `L2_NATIVE_TOKEN_VAULT_ADDR`.
* `bridge/ntv/NativeTokenVaultBase.sol:515-522` (`_unsafeRegisterNativeToken`): the vault
  stores the token under `encodeNTVAssetId(block.chainid, _nativeToken)` (the `address`
  overload) and asks the router to register
  `setAssetHandlerAddressThisChain(bytes32(uint256(uint160(_nativeToken))), address(this))`,
  which the router hashes with the `bytes32` overload. The two halves of one registration
  are keyed by the same id only if the two overloads agree on these arguments.
* `bridge/ntv/NativeTokenVaultBase.sol:580` (`_ensureAndSaveTokenDeployedInner`): a bridged
  token is registered only after `assetIdCheck` passes.
* Also `bridge/asset-router/L1AssetRouter.sol:163` (`setAssetDeploymentTracker`) and
  `core/bridgehub/BridgehubBase.sol:290` (the CTM asset id) use the `bytes32` overload.

## The ABI layout

All three arguments are static, so `abi.encode` is three 32-byte heads and no tail
(Solidity ABI specification, "Formal Specification of the Encoding"):

* `uint256`: 32 bytes, big-endian (`encWord`);
* `address`: as `uint160`, big-endian and padded on the left with 12 zero bytes
  (`encAddr`);
* `bytes32`: its 32 bytes, unpadded. As everywhere in this package a `bytes32` value is
  the `uint256` with the same bytes, so its head is `encWord` too. The conversion
  `bytes32(uint256(uint160(t)))` keeps the bits; it is the vault's zero extension
  `Contracts.NativeTokenVaultBase.widen`.

So every preimage here is 96 bytes.

## Two layers

* **The library**, with the Solidity types: chain ids and `bytes32` values are 256-bit
  words, addresses are 160-bit (`Addr`, the vault representation model's address type).
  `encodeAssetId`, `encodeAssetIdOfToken`, `encodeNTVAssetId`, `encodeNTVAssetIdOfToken`
  and `assetIdCheck` transcribe the five functions above.
* **The model instances.** The router and vault models carry addresses as 256-bit words.
  `routerEnc keccak` and `vaultEnc keccak` are the byte-level instances of their abstract
  `AssetIdOf` and `NtvAssetId`: each hashes the 96-byte preimage `routerPreimage` or
  `vaultPreimage` with `keccak`. On a real address (a `widen`ed `Addr`) they ARE the library
  functions; `Properties.RouterModelIsLibrary` and `Properties.VaultModelIsLibrary` say so.
  A model word above `2^160` is not an address; the instances encode it as a full 32-byte
  word, which keeps the preimage injective on every model triple.

## Named keccak events

`HashCollision keccak x y` (from `InteropDataEncoding`, `Specs/BundleHashPinned.lean`) is a
collision of keccak on two NAMED byte strings. `ZeroPreimage keccak x` is keccak sending the
named string `x` to the zero word, which every `bytes32` mapping reads as "unset". The second
is a preimage event, not a collision. `RouterIdBreakOn` and `VaultIdBreakOn` collect these
events over the preimages of an explicit set of triples or pairs, such as the ones a logged
run hashed. Both are pinned: the colliding inputs are determined by the set.

## Model boundaries

* `keccak` is an arbitrary function `List UInt8 → UInt256`. Nothing is assumed about it.
* `abi.encode` is modelled from the ABI specification for static arguments, not from the
  Yul solc emits (`SOL-ABI`).
* The router model's other writers and the counterpart path are not touched here; only the
  hash they share is.
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding (toBytesBE fromBytesBE word HashCollision)

/-- keccak256, as an arbitrary function on byte strings. Nothing is assumed about it. -/
abbrev Keccak := List UInt8 → UInt256

/-- A Solidity `address`: 160 bits. This is the vault representation model's address type
(`Contracts.NativeTokenVaultBase.Address`, `Fin (2 ^ 160)`). -/
abbrev Addr := Contracts.NativeTokenVaultBase.Address

/-! ## ABI heads, by static type -/

/-- The ABI head of a `uint256`, and of a `bytes32` read as the `uint256` with the same bytes:
32 bytes, big-endian. -/
def encWord (w : UInt256) : List UInt8 := word w.val

/-- The ABI head of an `address`: its 20 bytes, big-endian, padded on the higher-order (left)
side with 12 zero bytes. -/
def encAddr (a : Addr) : List UInt8 := List.replicate 12 0 ++ toBytesBE 20 a.val

/-- `bytes32(uint256(uint160(t)))`: an address converted to a `bytes32`. The conversions keep
the bits, so this is the zero extension `widen` of the vault models. -/
abbrev addrAsBytes32 (t : Addr) : UInt256 := Contracts.NativeTokenVaultBase.widen t

/-- `L2_NATIVE_TOKEN_VAULT_ADDR = address(0x10000 + 0x04)` (`L2ContractAddresses.sol:12, 99`). The
router normalises the vault caller to it on every chain (`AssetRouterBase.sol:79`), and both
`encodeNTVAssetId` overloads hash it as the sender. -/
def l2NtvAddr : Addr := 0x10004

/-! ## The library -/

/-- `abi.encode(_chainId, _sender, _assetData)` with `_assetData : bytes32`
(`DataEncoding.sol:127`, and `:144` with `_sender = L2_NATIVE_TOKEN_VAULT_ADDR`). -/
def assetIdPreimage (c : UInt256) (s : Addr) (d : UInt256) : List UInt8 :=
  encWord c ++ encAddr s ++ encWord d

/-- `abi.encode(_chainId, _sender, _tokenAddress)` with `_tokenAddress : address`
(`DataEncoding.sol:136`, and `:152` with `_sender = L2_NATIVE_TOKEN_VAULT_ADDR`). -/
def assetIdPreimageOfToken (c : UInt256) (s : Addr) (t : Addr) : List UInt8 :=
  encWord c ++ encAddr s ++ encAddr t

/-- `encodeAssetId(uint256 _chainId, bytes32 _assetData, address _sender)`
(`DataEncoding.sol:126-128`). -/
def encodeAssetId (keccak : Keccak) (c : UInt256) (d : UInt256) (s : Addr) : UInt256 :=
  keccak (assetIdPreimage c s d)

/-- `encodeAssetId(uint256 _chainId, address _tokenAddress, address _sender)`
(`DataEncoding.sol:135-137`). -/
def encodeAssetIdOfToken (keccak : Keccak) (c : UInt256) (t : Addr) (s : Addr) : UInt256 :=
  keccak (assetIdPreimageOfToken c s t)

/-- `encodeNTVAssetId(uint256 _chainId, bytes32 _assetData)` (`DataEncoding.sol:143-145`). -/
def encodeNTVAssetId (keccak : Keccak) (c : UInt256) (d : UInt256) : UInt256 :=
  keccak (assetIdPreimage c l2NtvAddr d)

/-- `encodeNTVAssetId(uint256 _chainId, address _tokenAddress)` (`DataEncoding.sol:151-153`).
This is the overload the vault uses: `_unsafeRegisterNativeToken` (`NativeTokenVaultBase.sol:516`)
and `assetIdCheck` (`DataEncoding.sol:209`). -/
def encodeNTVAssetIdOfToken (keccak : Keccak) (c : UInt256) (t : Addr) : UInt256 :=
  keccak (assetIdPreimageOfToken c l2NtvAddr t)

/-- `assetIdCheck(_tokenOriginChainId, _assetId, _originToken)` (`DataEncoding.sol:208-214`):
`some ()` when it returns, `none` when it reverts with `AssetIdMismatch`. -/
def assetIdCheck (keccak : Keccak) (c : UInt256) (a : UInt256) (t : Addr) : Option Unit :=
  if a = encodeNTVAssetIdOfToken keccak c t then some () else none

/-! ## The model instances -/

/-- The preimage of the router model's id `enc c s d`: three 32-byte words. The sender is a
256-bit word in that model; on a real address (`widen s`) its word is the address's ABI head
(`Properties.AddressWordIsWidenedWord`). -/
def routerPreimage (c s d : UInt256) : List UInt8 :=
  encWord c ++ encWord s ++ encWord d

/-- **THE ROUTER MODEL'S ID HASH AT BYTE LEVEL**: an `AssetIdOf` for
`Contracts.AssetRouter` (`HandlerRegistration`), keccak of `routerPreimage`. -/
def routerEnc (keccak : Keccak) : AssetRouter.AssetIdOf :=
  fun c s d => keccak (routerPreimage c s d)

/-- The preimage of the vault model's id `e c t`: the chain word, the head of
`L2_NATIVE_TOKEN_VAULT_ADDR`, and the token as a 256-bit word. -/
def vaultPreimage (c t : UInt256) : List UInt8 :=
  encWord c ++ encAddr l2NtvAddr ++ encWord t

/-- **THE VAULT MODEL'S ID HASH AT BYTE LEVEL**: an `NtvAssetId` for
`Contracts.NativeTokenVault` (`RegistryAndEscrow`), keccak of `vaultPreimage`. -/
def vaultEnc (keccak : Keccak) : NativeTokenVault.NtvAssetId :=
  fun c t => keccak (vaultPreimage c t)

/-! ## Named keccak events -/

/-- **A NAMED ZERO PREIMAGE.** keccak sends the named byte string `x` to the zero word, the
value every `bytes32` mapping reads as unset. Finding such an `x` is a preimage attack on a
fixed value, not a collision. -/
def ZeroPreimage (keccak : Keccak) (x : List UInt8) : Prop := keccak x = 0

/-- **A KECCAK COLLISION AMONG THE PREIMAGES OF NAMED ROUTER TRIPLES.** Two triples of `S`
whose preimages differ but hash alike. For a run, `S` is the set of triples the run itself
hashed, so the colliding inputs are named by the run. -/
def RouterIdBreakOn (keccak : Keccak)
    (S : Set (AssetRouter.Chain × AssetRouter.Address × AssetRouter.AssetData)) : Prop :=
  ∃ p ∈ S, ∃ q ∈ S,
    HashCollision keccak (routerPreimage p.1 p.2.1 p.2.2) (routerPreimage q.1 q.2.1 q.2.2)

/-- **A KECCAK EVENT AMONG THE PREIMAGES OF NAMED VAULT PAIRS**: two pairs of `S` whose
preimages collide, or one pair of `S` whose preimage hashes to zero. -/
def VaultIdBreakOn (keccak : Keccak)
    (S : Set (NativeTokenVault.Chain × NativeTokenVault.Address)) : Prop :=
  (∃ p ∈ S, ∃ q ∈ S, HashCollision keccak (vaultPreimage p.1 p.2) (vaultPreimage q.1 q.2))
  ∨ ∃ p ∈ S, ZeroPreimage keccak (vaultPreimage p.1 p.2)

end Contracts.DataEncoding
