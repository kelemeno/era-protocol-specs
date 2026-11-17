import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned

/-!
# Spec at draft/v0.35.0: the bundle hash is keccak of the bundle bytes

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`
(`V35/l1-contracts/contracts/`). The same code is at `main` `3605e82` (`InteropDataEncoding.sol:14-16`,
`InteropCenter.sol:690-692`). The change from the pin `c67894b9` came in `a1d5c34d4`
("remove public interop, make all interop atomic", #2280).

**This file is definitions only.** The statements are in
`EraSpec.Contracts.InteropDataEncoding.Properties.BundleHashAtV35` and the proofs in
`EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashAtV35`. The pin's model
(`Specs/BundleHashPinned.lean`, `Specs/BundleHashEncoding.lean`) is unchanged and still describes
the pin.

## The code at v35

    interop/InteropDataEncoding.sol:14-16
        function encodeInteropBundleHash(bytes memory _bundle) internal pure returns (bytes32) {
            return keccak256(_bundle);
        }

The pin hashed `keccak256(abi.encode(_sourceChainId, _bundle))`
(pin `InteropDataEncoding.sol:11-13`). At v35 the outer chain-id word and the
`abi.encode(uint256, bytes)` wrapper are gone. The library has exactly three call sites
(`grep -rn encodeInteropBundleHash contracts/`), not the four the pin header of
`BundleHashEncoding.lean` lists:

    interop/InteropCenter.sol:690-692        _hashBundle(b) = encodeInteropBundleHash(abi.encode(b))
        (called by _dispatchBundle :731 and the always-reverting preview :353)
    interop/interop-handler/InteropHandlerBase.sol:231   encodeInteropBundleHash(_bundle)   // raw bytes
    atomic-interop/AtomicFlowManager.sol:252             encodeInteropBundleHash(_bundle)   // raw bytes

So the source and both receivers hash the same function of the same bytes. Neither receiver mixes
in a decoded `sourceChainId` any more. Cross-chain separation now rests only on the bundle's own
`sourceChainId` field, which `_buildInteropBundle` sets to `block.chainid` (`InteropCenter.sol:634`)
and which `abi.encode(bundle)` writes at bytes 64..96.

The bundle layout (`common/Messaging.sol:268-276`) is unchanged from the pin, field for field:

    struct InteropBundle { bytes1 version; uint256 sourceChainId; uint256 destinationChainId;
        bytes32 destinationBaseTokenAssetId; bytes32 interopBundleSalt;
        InteropCall[] calls; BundleAttributes bundleAttributes; }

So `bundleEncoding` and `bundleSaltSlot` from `BundleHashPinned` still describe `abi.encode(bundle)`,
and they now index the keccak preimage directly. The salt sits at bytes 160..192 of the preimage,
not 256..288 (`preimageSaltSlot` is the pin's offset). The source chain id sits at bytes 64..96
(`bundleSourceSlot`) and the destination at 96..128 (`bundleDestSlot`).

The salt derivation and guard are unchanged in substance:

    interop/InteropCenter.sol:562-566
        require(!isInteropBundleSaltUsed[msg.sender][_bundleAttributes.salt], ...);
        isInteropBundleSaltUsed[msg.sender][_bundleAttributes.salt] = true;
    interop/InteropCenter.sol:638
        interopBundleSalt: keccak256(abi.encodePacked(msg.sender, _bundleAttributes.salt)),

The NatSpec at `InteropCenter.sol:125-127` and `:561` still states uniqueness absolutely ("makes
every emitted bundle hash unique"). The results here make it precise at v35, with fewer named
preimages than at the pin.

## Model boundaries

* Keccak is an arbitrary function `List UInt8 → UInt256`. Nothing about it is assumed.
* `bundleEncoding`, `word`, `toBytesBE` are the byte models of `BundleHashPinned` /
  `BundleHashEncoding`. They are not the Yul solc emits (see `Refinement.lean`).
* The headlines quantify over every byte string `B` with the stated slots, not only canonical
  encodings.
* The witness tails carry a non-empty unbundler: `sendMessage` (:217-219) and `_parseBundleInputs`
  (:520-522) default an empty unbundler to `formatEvmV1(block.chainid, msg.sender)`, so no sent bundle
  has an empty one. `formatEvmV1` below is that encoding
  (`vendor/draft-InteroperableAddress.sol:48-51`).
-/

namespace AttackVectors.BundleHashEncoding.AtV35

open AttackVectors.BundleHashEncoding

/-- **THE BUNDLE HASH AT v35.** `encodeInteropBundleHash(_bundle) = keccak256(_bundle)`
(`InteropDataEncoding.sol:14-16`). The center applies it to `abi.encode(bundle)`
(`InteropCenter.sol:691`). The handler (`InteropHandlerBase.sol:231`) and the manager's `claimRefund`
(`AtomicFlowManager.sol:252`) apply it to the raw bytes they are given. -/
def bundleHashV35 (keccak : List UInt8 → UInt256) (B : List UInt8) : UInt256 := keccak B

/-- **THE SOURCE-CHAIN SLOT OF THE BUNDLE BYTES.** In `B = abi.encode(bundle)`,
`bundle.sourceChainId` occupies bytes 64..96: past the outer offset word and the `version` word. -/
def bundleSourceSlot (B : List UInt8) : List UInt8 := (B.drop 64).take 32

/-- **THE DESTINATION SLOT OF THE BUNDLE BYTES.** `bundle.destinationChainId` occupies bytes 96..128.
`_dispatchBundle` branches on this field (`InteropCenter.sol:733`). -/
def bundleDestSlot (B : List UInt8) : List UInt8 := (B.drop 96).take 32

/-- **THE PIN'S KECCAK PREIMAGE FOR THE SAME BYTES.** At the pin, the hash of bundle bytes `B` sent from
chain `c` was `keccak(abi.encode(c, B))` (pin `InteropDataEncoding.sol:11-13`,
`InteropCenter.sol:644`). It is named here only to relate the two versions. -/
def pinPreimage (c : ℕ) (B : List UInt8) : List UInt8 := abiEncode c B

/-- `InteroperableAddress.formatEvmV1(chainid, addr)` (`vendor/draft-InteroperableAddress.sol:48-51`):
`bytes4(0x00010000)`, the chain-reference length, the chain reference (`_toChainReference`, the
minimal big-endian bytes of the chain id, :215-221), `uint8(20)`, then the 20 address bytes. It is
the default unbundler (`InteropCenter.sol:217-219`, `:520-522`). -/
def formatEvmV1 (chainRef : List UInt8) (addr : ℕ) : List UInt8 :=
  [0x00, 0x01, 0x00, 0x00, UInt8.ofNat chainRef.length] ++ chainRef ++ [0x14] ++ toBytesBE 20 addr

/-- `_toChainReference(324)` = `0x0144`. -/
def chainRef324 : List UInt8 := [0x01, 0x44]

/-- `_toChainReference(326)` = `0x0146`. -/
def chainRef326 : List UInt8 := [0x01, 0x46]

/-- **THE CANONICAL TAIL OF A BUNDLE WITH NO CALLS AND UNBUNDLER `u`.** After the seven head words of
the `InteropBundle` tuple (`bundleEncoding`, with `callsOffset = 224` and `attributesOffset = 256`):

* the empty `calls` array (its length word, `0`);
* the `BundleAttributes` head: the offsets `128` and `160` of its two `bytes` fields,
  `useFixedFee = false`, and the user salt `s`;
* the empty `executionAddress` (its length word) and the unbundler `u` (its length word, then `u`
  right-padded).

The pin's witness tail (`BundleHashPinned` proofs) is this tail with `u = []`, `s = 0`. -/
def bundleTailV35 (u : List UInt8) (s : ℕ) : List UInt8 :=
  word 0 ++ (word 128 ++ (word 160 ++ (word 0 ++ (word s ++ (word 0 ++ (word u.length ++ pad32 u))))))

end AttackVectors.BundleHashEncoding.AtV35
