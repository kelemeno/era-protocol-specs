import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashEncoding
import EraSpec.Core.Word

/-!
# Spec: distinct sends give distinct bundle hashes, or a collision on named inputs

`Properties.distinct_sends_distinct_hashes` (topic `BundleHashEncoding`) concludes that two sends
with distinct `(sender, salt)` pairs get distinct bundle hashes. It takes two premises:

* `hsalt_inj : Function.Injective saltHash`, with `saltHash : List UInt8 → Hash`;
* `hbundle_inj : Function.Injective bundleHashOf`.

At the deployed hash type `Hash = UInt256` (`bytes32`) neither premise can hold:

* `List UInt8` is infinite. Even the well-formed salt preimages, 20 sender bytes and 32 salt bytes,
  number `2^416 > 2^256` (`Properties.SaltHashNotInjOnPackedPreimages`).
* So is the deployed bundle type, because `InteropBundle.calls` is a dynamic array
  (`Properties.BundleHashInjUnsatisfiable`).

So the property is vacuous there. This topic restates it with no hash premise, in pinned form:
either the two bundle hashes differ, or the hash collides on two inputs that the instance names.
Every map from an infinite type into `UInt256` collides somewhere, so a disjunct of the form "some
collision exists" would be always true and say nothing (ASSUMPTIONS.md, "Results whose premises
cannot hold"). `HashCollision f x y` names the two inputs, so it can be false, and the witnesses
show that it is false on concrete instances.

The source, at the pinned tree (`PIN/l1-contracts/contracts/`):

    interop/InteropCenter.sol:479-483
        require(!isInteropBundleSaltUsed[msg.sender][_bundleAttributes.salt], ...);
        isInteropBundleSaltUsed[msg.sender][_bundleAttributes.salt] = true;
    interop/InteropCenter.sol:500, 507
        sourceChainId: block.chainid,
        interopBundleSalt: keccak256(abi.encodePacked(msg.sender, _bundleAttributes.salt)),
    interop/InteropCenter.sol:643-644
        bytes memory interopBundleBytes = abi.encode(_bundle);
        bundleHash = InteropDataEncoding.encodeInteropBundleHash(block.chainid, interopBundleBytes);
    interop/InteropDataEncoding.sol:11-13
        return keccak256(abi.encode(_sourceChainId, _bundle));
    common/Messaging.sol:288-296
        struct InteropBundle { bytes1 version; uint256 sourceChainId; uint256 destinationChainId;
            bytes32 destinationBaseTokenAssetId; bytes32 interopBundleSalt;
            InteropCall[] calls; BundleAttributes bundleAttributes; }

The NatSpec at `InteropCenter.sol:124-128` says that making each `(sender, salt)` pair single-use
"makes every emitted bundle hash unique". The results here make that precise. Distinct pairs give
distinct bundle hashes unless keccak collides on one of two named pairs of byte strings:

* the two packed salt preimages `abi.encodePacked(sender, salt)`;
* the two keccak preimages `abi.encode(block.chainid, abi.encode(bundle))` of the bundle hashes.

This file does not model the guard itself, i.e. that each `(sender, salt)` is used at most once in
a run. The premise `¬ (a = a' ∧ s = s')` stands for it, as in `distinct_sends_distinct_hashes`.

## Two layers

* **Abstract**, with the original's signature: `saltHash`, `bundleHashOf` and `saltField` are
  arbitrary functions. The conclusion's disjuncts are a collision of `saltHash` on the two named
  packed preimages, or a collision of `bundleHashOf` on the two named bundles.
* **Keccak**. The bundle is its ABI bytes `B`, and the bundle hash is `keccak (abiEncode c B)`
  (`bundleHashOfBytes`). The only facts about `B` that the argument uses are that its salt slot
  (`bundleSaltSlot`, bytes 160..192) holds the salt word, and that this slot sits at bytes 256..288
  of the keccak preimage (`preimageSaltSlot`). Both collision disjuncts are then collisions of the
  one function `keccak`, on named byte strings. `bundleEncoding` transcribes the ABI head layout of
  `InteropBundle` so that the slot offset can be checked.

## Model boundaries

* Keccak is an arbitrary function `List UInt8 → UInt256`. Nothing about it is assumed.
* `abiEncode`, `toBytesBE` and `word` are the byte-level models from `BundleHashEncoding`. They are
  not the Yul that solc emits (see that file and `Refinement.lean`).
* `bundleEncoding` models the head of `abi.encode(InteropBundle)` from the ABI specification. It is
  not derived from a Solidity semantics; the encodings of `calls` and `bundleAttributes` are left
  as an arbitrary `tail`.
* The headline quantifies over every byte string `B` whose salt slot holds the salt word, not only
  over canonical encodings, so it does not depend on the rest of the layout.
-/

namespace AttackVectors.BundleHashEncoding

universe u v

/-- **A COLLISION OF `f` ON TWO NAMED INPUTS.** `x` and `y` differ and `f` maps them to the same
value. Both inputs are given by the instance, so this can be false, unlike "`f` has some
collision", which every map from `List UInt8` into `UInt256` satisfies. -/
def HashCollision {α : Type u} {β : Type v} (f : α → β) (x y : α) : Prop :=
  x ≠ y ∧ f x = f y

/-- `abi.encodePacked(msg.sender, _bundleAttributes.salt)` (`InteropCenter.sol:507`): the 20 bytes of
the sender address followed by the 32 bytes of the user's salt. These are the same bytes as
`toBytesBE 20 a ++ s` in `Properties.packed_addr_salt_inj` and `distinct_sends_distinct_hashes`. -/
def packedSalt (a : ℕ) (s : List UInt8) : List UInt8 := toBytesBE 20 a ++ s

/-- Every well-formed salt preimage: a sender below `2^160` and a 32-byte salt. -/
def packedPreimages : Set (List UInt8) :=
  {p | ∃ (a : ℕ) (s : List UInt8), a < 256 ^ 20 ∧ s.length = 32 ∧ p = packedSalt a s}

/-! ## The bundle bytes, and where the salt sits in them -/

/-- The ABI word of a `bytes1` value. Fixed-size `bytesN` values are left-aligned: the byte, then 31
zero bytes. -/
def bytes1Word (v : UInt8) : List UInt8 := v :: List.replicate 31 0

/-- **THE HEAD OF `abi.encode(bundle)` FOR AN `InteropBundle`** (`Messaging.sol:288-296`), followed
by an arbitrary dynamic `tail`. `abi.encode` of one argument of a dynamic struct type is:

* the offset word `0x20`;
* then the struct's tuple encoding: one head word per field, in declaration order (the value of each
  of the five static fields, and an offset for each of the two dynamic fields `calls` and
  `bundleAttributes`);
* then the tails of the dynamic fields.

Offsets are counted from the start of the tuple. In a canonical encoding `callsOffset = 7 · 32`.
Nothing here depends on that. -/
def bundleEncoding (version : UInt8) (sourceChainId destinationChainId baseTokenAssetId salt
    callsOffset attributesOffset : ℕ) (tail : List UInt8) : List UInt8 :=
  word 0x20 ++ (bytes1Word version ++ (word sourceChainId ++ (word destinationChainId ++
    (word baseTokenAssetId ++ (word salt ++ (word callsOffset ++ (word attributesOffset ++ tail)))))))

/-- **THE SALT SLOT OF THE BUNDLE BYTES.** In `B = abi.encode(bundle)`, `bundle.interopBundleSalt`
occupies bytes 160..192: `0x20 + 4 · 0x20`, past the outer offset word and the four static fields
declared before the salt. -/
def bundleSaltSlot (B : List UInt8) : List UInt8 := (B.drop 160).take 32

/-- **THE SAME SLOT INSIDE THE BUNDLE HASH'S KECCAK PREIMAGE.** In `abi.encode(chainId, B)`, `B`
starts after three words (the chain id, the offset `0x40` and `B`'s length), so the salt sits at
`96 + 160 = 256`. -/
def preimageSaltSlot (E : List UInt8) : List UInt8 := (E.drop 256).take 32

/-- **THE BUNDLE HASH, COMPUTED FROM THE BUNDLE BYTES.**
`encodeInteropBundleHash(chainId, B) = keccak256(abi.encode(chainId, B))`
(`InteropDataEncoding.sol:11-13`), called at `InteropCenter.sol:644` with `chainId = block.chainid`
and `B = abi.encode(_bundle)`. -/
def bundleHashOfBytes (keccak : List UInt8 → UInt256) (c : ℕ) (B : List UInt8) : UInt256 :=
  keccak (abiEncode c B)

end AttackVectors.BundleHashEncoding
