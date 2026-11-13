import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned

/-!
# Spec: the byte-level ABI toolkit used by the encoding libraries

The libraries modelled in `Contracts/DataEncoding`, `Contracts/AttributesDecoder` and
`Contracts/InteroperableAddress` build and read byte strings with `abi.encode`,
`abi.encodePacked`, `bytes.concat` and `abi.decode`. This file fixes one byte-level meaning for
those constructs. Values are natural numbers with the bound of their Solidity type stated where it
is used (`uint256`, `bytes32`: below `2^256`; `address`: below `2^160`; `bytesN`: below `2^(8N)`).
`bytes` values are `List UInt8`.

It reuses `toBytesBE`, `fromBytesBE`, `word` and `pad32` from
`InteropDataEncoding/Specs/BundleHashEncoding.lean`, and `HashCollision` from
`InteropDataEncoding/Specs/BundleHashPinned.lean`.

## Decoding (`abi.decode`, ABI coder v2)

Decoding is partial: `none` is a revert. The model follows the checks of solc's
`abi_decode_tuple_*` helpers for the types used here:

* the encoded tuple must hold its whole head (`data.length ≥ 32 · #fields`), else revert;
* an `address` word must be below `2^160` and a `bool` word at most `1` (cleanup validation),
  else revert; `uint256` and `bytes32` words are read as they are;
* a `bytes` field: its head word is an offset `o` relative to the tuple start; revert unless
  `o < 2^64` and `o + 32 ≤ data.length`; the length word `L` at `o` must satisfy `L < 2^64`
  and `o + 32 + L ≤ data.length`; the value is the `L` bytes after the length word.
  Padding bytes are neither required nor checked;
* bytes past the end of the encoding are ignored (`abi.decode` accepts trailing data).

## Model boundary

This is the ABI specification plus the documented solc decoder checks, not a semantics of the
Yul that solc emits (`SOL-ABI` in `ASSUMPTIONS.md`; `MODEL-ABI-BYTES` for this toolkit).
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding

/-- `bytesN` / `uintM` big-endian bytes: `n` as `k` bytes. -/
abbrev be (k n : ℕ) : List UInt8 := toBytesBE k n

/-- The word at byte offset `o` of `d`, read as a number. -/
def readWord (d : List UInt8) (o : ℕ) : ℕ := fromBytesBE ((d.drop o).take 32)

/-- `abi.decode` of an `address` word at offset `o`: reverts on dirty upper bits. -/
def decAddr (d : List UInt8) (o : ℕ) : Option ℕ :=
  if readWord d o < 2 ^ 160 then some (readWord d o) else none

/-- `abi.decode` of a `bool` word at offset `o`: reverts unless the word is `0` or `1`. -/
def decBool (d : List UInt8) (o : ℕ) : Option Bool :=
  if readWord d o = 0 then some false else if readWord d o = 1 then some true else none

/-- `abi.decode` of a `bytes` field whose head word sits at offset `o` of the tuple `d`. -/
def decBytes (d : List UInt8) (o : ℕ) : Option (List UInt8) :=
  if 2 ^ 64 ≤ readWord d o then none
  else if d.length < readWord d o + 32 then none
  else if 2 ^ 64 ≤ readWord d (readWord d o) then none
  else if d.length < readWord d o + 32 + readWord d (readWord d o) then none
  else some ((d.drop (readWord d o + 32)).take (readWord d (readWord d o)))

/-- The tail of a `bytes` value in a canonical `abi.encode`: its length word, then its contents
right-padded to a multiple of 32. -/
def bytesTail (b : List UInt8) : List UInt8 := word b.length ++ pad32 b

/-- `abi.encode(bytes)` of a single `bytes` argument: the offset `0x20`, then the tail. -/
def encodeBytes (b : List UInt8) : List UInt8 := word 0x20 ++ bytesTail b

/-- `NEW_ENCODING_VERSION = 0x01` (`bridge/asset-router/IAssetRouterBase.sol:6`). -/
def NEW_ENCODING_VERSION : UInt8 := 1

end Contracts.DataEncoding
