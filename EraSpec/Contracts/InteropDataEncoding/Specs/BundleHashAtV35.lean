import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned

/-!
# Spec at draft/v0.35.0: the bundle hash is keccak of the bundle bytes

Source: era-contracts `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`
(`l1-contracts/contracts/`). Every file cited below (`interop/`, `atomic-interop/`,
`common/Messaging.sol`, `vendor/draft-InteroperableAddress.sol`, `vendor/Bytes.sol`) is unchanged
from the earlier `draft/v0.35.0` commit `d9f678900e1bc8286412b78f56d4a9f443983c29`, so the line
numbers are the same at both. The change from the interop pin `c67894b9` came in `a1d5c34d4`
("remove public interop, make all interop atomic", #2280), which is also on `main`. At `main`
`70096e2ea6eeb5373992e178064c4b26dcf6436a` the code transcribed here is the same, at these lines:
`InteropDataEncoding.sol:14-16` and `InteropHandlerBase.sol:231` (unchanged), `InteropCenter.sol:689-691`
(`_hashBundle`, there declared `view`), `:633` and `:637` (the source chain id and the salt),
`:821` (`from`), `AtomicFlowManager.sol:249`, and `Messaging.sol:225-230`, `:241-248`, `:269-277`
(the three structs).

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

The pin hashed `keccak256(abi.encode(_sourceChainId, _bundle))` (pin `InteropDataEncoding.sol:11-13`).
At v35 the outer chain-id word and the `abi.encode(uint256, bytes)` wrapper are gone. The library
has three call sites, as at the pin (where they were `InteropCenter.sol:644`,
`InteropHandlerBase.sol:249`, `AtomicFlowManager.sol:167`):

    interop/InteropCenter.sol:690-692        _hashBundle(b) = encodeInteropBundleHash(abi.encode(b))
        (called by _dispatchBundle :731 and by the always-reverting preview :353)
    interop/interop-handler/InteropHandlerBase.sol:231   encodeInteropBundleHash(_bundle)   // raw bytes
    atomic-interop/AtomicFlowManager.sol:252             encodeInteropBundleHash(_bundle)   // raw bytes

So the source and both receivers apply one function to bytes. At the pin, the two receivers mixed in
the `sourceChainId` they decoded from the bytes; at v35 they do not. The one chain-id word the hash
always sees is the bundle's own `sourceChainId` field, which `_buildInteropBundle` sets to
`block.chainid` (`InteropCenter.sol:634`) and which `abi.encode(bundle)` writes at bytes 64..96.

The bundle layout (`common/Messaging.sol:268-276`) is unchanged from the pin, field for field:

    struct InteropBundle { bytes1 version; uint256 sourceChainId; uint256 destinationChainId;
        bytes32 destinationBaseTokenAssetId; bytes32 interopBundleSalt;
        InteropCall[] calls; BundleAttributes bundleAttributes; }

So `bundleEncoding` and `bundleSaltSlot` from `BundleHashPinned` still describe `abi.encode(bundle)`,
and they now index the keccak preimage directly. The salt sits at bytes 160..192 of the preimage,
not 256..288 (`preimageSaltSlot` is the pin's offset). The source chain id sits at bytes 64..96
(`bundleSourceSlotV35`) and the destination at 96..128 (`bundleDestSlotV35`).

The salt derivation and guard are unchanged in substance:

    interop/InteropCenter.sol:562-566
        require(!isInteropBundleSaltUsed[msg.sender][_bundleAttributes.salt], ...);
        isInteropBundleSaltUsed[msg.sender][_bundleAttributes.salt] = true;
    interop/InteropCenter.sol:638
        interopBundleSalt: keccak256(abi.encodePacked(msg.sender, _bundleAttributes.salt)),

The NatSpec at `InteropCenter.sol:125-127` and the comment at `:561` state uniqueness absolutely
("makes every emitted bundle hash unique"). The results here state it at v35 with the named keccak
preimages that make it precise: the two bundle byte strings and the two packed salt preimages.

## The bytes of a `sendMessage` bundle

`sendMessage` (`InteropCenter.sol:197-244`) builds a bundle with exactly one call
(`:221-226`). For a direct call, `_processCallStarter` (`:823-830`) fills it as
`InteropCall({version: 0x01, shadowAccount: false, to: recipient, data: payload, value, from:
msg.sender})`. The bundle's attributes are the parsed `BundleAttributes`
(`InteropAttributeParser.sol:61-76`), and an empty unbundler is replaced by
`formatEvmV1(block.chainid, msg.sender)` (`:217-219`; `_parseBundleInputs` does the same for
`sendBundle`, `:520-522`). `sendMessageBytesV35` is `abi.encode(bundle)` for such a send, in the
canonical layout, following the ABI specification:

* the head of `bundleEncoding`, with `calls` at offset `224` and the attributes right after it;
* the `calls` array: its length word `1`, the offset `32` of its one element, then the element;
* the element (`directCallEncodingV35`, `Messaging.sol:240-247`): six head words (`version`,
  `shadowAccount`, `to`, `from`, `value`, and the offset `192` of `data`), then `data`'s length word
  and its bytes, right-padded to 32;
* the attributes (`bundleAttributesEncodingV35`, `Messaging.sol:224-229`): the offsets `128` and `160`
  of the two `bytes` fields, `useFixedFee = false`, the 32 bytes of the user salt, the empty
  `executionAddress` (its length word) and the unbundler (its length word, then its bytes,
  right-padded).

It covers a send with a direct call and no `executionAddress`, `useFixedFee` or `unbundler`
attribute, so the unbundler is the default. The witnesses use it, and so do the `SendMessage…`
statements. The general headlines (`SendsDistinctBundleHashes…V35`) do not depend on it: they
quantify over every byte string with the stated slots.

`noCallBytesV35` is the same layout for a bundle with no calls and a given unbundler. It is used only
in the countermodel `SaltCollisionDisjunctNeededV35`.

## Model boundaries

* Keccak is an arbitrary function `List UInt8 → UInt256`. Nothing about it is assumed.
* `bundleEncoding`, `word`, `pad32`, `toBytesBE` are the byte models of `BundleHashPinned` /
  `BundleHashEncoding`, and the encodings here are written from the ABI specification. They are
  not the Yul solc emits (see `Refinement.lean`). `Properties.SendMessageBytesMatchAbiEncoderV35`
  compares them with an independent ABI encoder's output on three instances; that is evidence on
  those instances, not a proof for every input.
* `toChainReferenceV35` uses Mathlib's `Nat.log 256` for OpenZeppelin's `Math.log256` (rounded down,
  `0` for `0`); the OpenZeppelin dependency is not in the exported tree.
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
def bundleSourceSlotV35 (B : List UInt8) : List UInt8 := (B.drop 64).take 32

/-- **THE DESTINATION SLOT OF THE BUNDLE BYTES.** `bundle.destinationChainId` occupies bytes 96..128.
`_dispatchBundle` branches on this field (`InteropCenter.sol:733`). -/
def bundleDestSlotV35 (B : List UInt8) : List UInt8 := (B.drop 96).take 32

/-- **THE PIN'S KECCAK PREIMAGE FOR THE SAME BYTES.** At the pin, the hash of bundle bytes `B` sent
from chain `c` was `keccak(abi.encode(c, B))` (pin `InteropDataEncoding.sol:11-13`,
`InteropCenter.sol:644`). It is named here only to relate the two versions. -/
def pinPreimageV35 (c : ℕ) (B : List UInt8) : List UInt8 := abiEncode c B

/-- `_toChainReference(chainid)` (`vendor/draft-InteroperableAddress.sol:215-221`):
`abi.encodePacked(chainid).slice(32 - length)` with `length = Math.log256(chainid) + 1`, i.e. the last
`length` bytes of the 32-byte big-endian word (`vendor/Bytes.sol:77-79`). That these bytes are the
chain id's minimal big-endian bytes, with `0x0144` for `324`, is
`Properties.ToChainReferenceMinimalBytesV35`. -/
def toChainReferenceV35 (c : ℕ) : List UInt8 := toBytesBE (Nat.log 256 c + 1) c

/-- `InteroperableAddress.formatEvmV1(chainid, addr)` (`vendor/draft-InteroperableAddress.sol:48-51`):
`abi.encodePacked(bytes4(0x00010000), uint8(chainReference.length), chainReference, uint8(20), addr)`.
It is the default unbundler (`InteropCenter.sol:217-219`, `:520-522`). -/
def formatEvmV1V35 (c addr : ℕ) : List UInt8 :=
  [0x00, 0x01, 0x00, 0x00, UInt8.ofNat (toChainReferenceV35 c).length] ++ toChainReferenceV35 c
    ++ [0x14] ++ toBytesBE 20 addr

/-- **THE ABI ENCODING OF ONE DIRECT `InteropCall`** (`Messaging.sol:240-247`) as an element of the
`calls` array: `version = 0x01` (left-aligned), `shadowAccount = false`, the addresses `to` and `from`,
`value`, the offset `192` of `data`, then `data`'s length word and its right-padded bytes. -/
def directCallEncodingV35 (toAddr fromAddr value : ℕ) (data : List UInt8) : List UInt8 :=
  bytes1Word 1 ++ (word 0 ++ (word toAddr ++ (word fromAddr ++ (word value ++ (word 192
    ++ (word data.length ++ pad32 data))))))

/-- **THE ABI ENCODING OF A `BundleAttributes`** (`Messaging.sol:224-229`) with an empty
`executionAddress`, unbundler `u`, `useFixedFee = false` and user salt `s` (its 32 bytes): the head
words (the offsets `128` and `160` of the two `bytes` fields, `false`, `s`), then the empty
`executionAddress` (its length word) and `u` (its length word, then its right-padded bytes). -/
def bundleAttributesEncodingV35 (u s : List UInt8) : List UInt8 :=
  word 128 ++ (word 160 ++ (word 0 ++ (s ++ (word 0 ++ (word u.length ++ pad32 u)))))

/-- **THE BYTES OF A `sendMessage` BUNDLE.** `abi.encode(bundle)` for the bundle that sender `a` on
chain `c` builds with `sendMessage` (`InteropCenter.sol:197-244`): one direct call to `recipient` with
call value `value` and `payload`, destination `d` with base-token asset id `base`, user salt `s`, and
no other bundle attribute, so the unbundler is `formatEvmV1(c, a)` (`:217-219`). The salt word is
`keccak(abi.encodePacked(a, s))` (`:638`). `calls` sits at offset `224`, right after the seven head
words, and consists of its length word `1`, one offset word and the element. The attributes follow
at offset `288` plus the element's length. -/
def sendMessageBytesV35 (keccak : List UInt8 → UInt256) (c d base a recipient value : ℕ)
    (s payload : List UInt8) : List UInt8 :=
  bundleEncoding 1 c d base (keccak (packedSalt a s)).val 224
    (288 + (directCallEncodingV35 recipient a value payload).length)
    (word 1 ++ (word 32 ++ (directCallEncodingV35 recipient a value payload
      ++ bundleAttributesEncodingV35 (formatEvmV1V35 c a) s)))

/-- **THE BYTES OF A BUNDLE WITH NO CALLS.** `abi.encode(bundle)` for a bundle with an empty `calls`
array (its length word `0`, so the attributes sit at offset `256`), source `c`, destination `d`, base
token asset id `base`, salt word `keccak(abi.encodePacked(a, s))` and attributes with unbundler `u`
and user salt `s`. Used only in the countermodel that needs two senders to build one byte string: a
direct call carries its sender in `from` (`InteropCenter.sol:829`). -/
def noCallBytesV35 (keccak : List UInt8 → UInt256) (c d base a : ℕ) (s u : List UInt8) :
    List UInt8 :=
  bundleEncoding 1 c d base (keccak (packedSalt a s)).val 224 256
    (word 0 ++ bundleAttributesEncodingV35 u s)

end AttackVectors.BundleHashEncoding.AtV35
