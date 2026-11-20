import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned

/-!
# History: the bundle hash at the interop pin `c67894b9`

**This folder is a record of an older commit, not a claim about era-contracts `b17415d20`.** It
keeps the keccak layer of topic `BundleHashPinned` as it was stated for the interop pin
`c67894b9`, where

    interop/InteropDataEncoding.sol:11-13
        return keccak256(abi.encode(_sourceChainId, _bundle));
    interop/InteropCenter.sol:643-644
        bytes memory interopBundleBytes = abi.encode(_bundle);
        bundleHash = InteropDataEncoding.encodeInteropBundleHash(block.chainid, interopBundleBytes);

so the keccak input of a bundle hash was `abi.encode(chainId, B)` with `B = abi.encode(bundle)`
(salt guard at pin `InteropCenter.sol:479-483`, salt derivation `:507`). At `b17415d20` the hash is
`keccak256(abi.encode(bundle))` with no outer chain-id word; that is topic `BundleHashAtV35`, which
restates every statement of this record at `b17415d20` (`…V35`). The shared definitions
(`HashCollision`, `packedSalt`, `bundleEncoding`, `bundleSaltSlot`) and the hash-agnostic
statements stay in `Specs/BundleHashPinned.lean`.

Two definitions are specific to the pin:

* `preimageSaltSlot`: the salt slot inside `abi.encode(chainId, B)`, bytes 256..288;
* `bundleHashOfBytes keccak c B = keccak (abiEncode c B)`.

Both collision disjuncts of the History statements are collisions of the one function `keccak` on
named byte strings: the two packed salt preimages, or the two preimages `abi.encode(c, B)`.
-/

namespace AttackVectors.BundleHashEncoding.History

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

end AttackVectors.BundleHashEncoding.History
