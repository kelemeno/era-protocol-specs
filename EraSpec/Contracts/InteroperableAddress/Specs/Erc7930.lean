import EraSpec.Contracts.DataEncoding.Specs.Abi

/-!
# Spec: `InteroperableAddress` — ERC-7930 (version 1) formatting and parsing

Source: `l1-contracts/contracts/vendor/draft-InteroperableAddress.sol` at era-contracts
`d9f678900e1bc8286412b78f56d4a9f443983c29` (draft/v0.35.0), a vendored OpenZeppelin draft. Line
numbers are in that file unless another file is named. `ERC7930_V1_MIN_LENGTH = 0x06` is
`interop/InteropConstants.sol:7`.

Byte strings are `List UInt8`; numbers are naturals with the bound of their Solidity type stated
where used (`bytes2`: below `2^16`; `address`: below `2^160`; `uint256`: below `2^256`). Byte-level
helpers (`be`, `word`, `fromBytesBE`) come from `Contracts/DataEncoding/Specs/Abi.lean`.

| Solidity | Lean |
|---|---|
| `formatV1(bytes2, bytes, bytes)` (:27-42) | `formatV1` (`none` = revert), bytes `formatV1Bytes` |
| `formatEvmV1(uint256, address)` (:48-51) | `formatEvmV1` |
| `formatEvmV1(uint256)` (:56-59) | `formatEvmV1Chain` |
| `formatEvmV1(address)` (:64-66) | `formatEvmV1Addr` |
| `tryParseV1` (:95-119), `tryParseV1Calldata` (:124-148) | `tryParseV1` (`none` = `success == false`) |
| `parseV1`, `parseV1Calldata` (:72-89) | `tryParseV1` (`none` = revert) |
| `tryParseEvmV1` (:178-191), `tryParseEvmV1Calldata` (:196-213) | `tryParseEvmV1` |
| `parseEvmV1`, `parseEvmV1Calldata` (:159-172) | `tryParseEvmV1` (`none` = revert) |
| `_toChainReference` (:215-221) | `toChainReference` |

The memory and calldata variants run the same checks in the same order on the same bytes and
differ only in where the result lives; one Lean function models both. A `try…` function returns
`success = false` with zero outputs where the `parse…` wrapper reverts; both are `none` here.

## Model boundaries (`MODEL-ERC7930` in `ASSUMPTIONS.md`)

* `Math.log256` (OpenZeppelin v4) is taken to be `⌊log₂₅₆ n⌋`, with `log256(0) = 0`
  (`Nat.log 256`). Its bit-twiddling implementation is not modelled.
* `Bytes.slice`, the assembly readers `_readBytes2`/`_readBytes2Calldata` and calldata slicing are
  modelled by their results on in-bounds arguments (`List.drop`/`List.take`); every use in the
  source is in bounds after the length checks that precede it.
* `bytes32(b)` / `bytes20(b)` of a `bytes` value: left-aligned, zero-padded on the right, truncated
  (`bytesNOf`). The shift `>> (256 - 8·len)` is transcribed as written; that it yields the
  big-endian value of the reference is a theorem (`ParseEvmReadsBigEndianValues`).
-/

namespace Contracts.InteroperableAddress

open AttackVectors.BundleHashEncoding Contracts.DataEncoding

/-- `ERC7930_V1_MIN_LENGTH = 0x06` (`interop/InteropConstants.sol:7`): two version bytes, two
chain-type bytes and the two length bytes. -/
def ERC7930_V1_MIN_LENGTH : ℕ := 6

/-! ## Formatting -/

/-- The bytes `formatV1` returns when it does not revert (:34-41):
`abi.encodePacked(bytes2(0x0001), chainType, uint8(chainReference.length), chainReference,
uint8(addr.length), addr)`. -/
def formatV1Bytes (chainType : ℕ) (chainReference addr : List UInt8) : List UInt8 :=
  be 2 1 ++ (be 2 chainType ++ (UInt8.ofNat chainReference.length ::
    (chainReference ++ (UInt8.ofNat addr.length :: addr))))

/-- `formatV1(chainType, chainReference, addr)` (:27-42). Reverts (`none`) when both the chain
reference and the address are empty (:32), and when either length does not fit a `uint8`
(`SafeCast.toUint8`, :37 and :39). -/
def formatV1 (chainType : ℕ) (chainReference addr : List UInt8) : Option (List UInt8) :=
  if ¬ (0 < chainReference.length ∨ 0 < addr.length) then none
  else if 255 < chainReference.length then none
  else if 255 < addr.length then none
  else some (formatV1Bytes chainType chainReference addr)

/-- `Math.log256(n)`: `⌊log₂₅₆ n⌋`, and `0` at `n = 0` (model boundary, see the header). -/
def log256 (n : ℕ) : ℕ := Nat.log 256 n

/-- `_toChainReference(chainid)` (:215-221): `length = Math.log256(chainid) + 1` (:218), then
`abi.encodePacked(chainid).slice(32 - length)` (:219): the last `length` bytes of the 32-byte word. -/
def toChainReference (chainid : ℕ) : List UInt8 :=
  (word chainid).drop (32 - (log256 chainid + 1))

/-- `formatEvmV1(chainid, addr)` (:48-51): `abi.encodePacked(bytes4(0x00010000),
uint8(chainReference.length), chainReference, uint8(20), addr)`. -/
def formatEvmV1 (chainid addr : ℕ) : List UInt8 :=
  be 4 0x00010000 ++ (UInt8.ofNat (toChainReference chainid).length ::
    (toChainReference chainid ++ (UInt8.ofNat 20 :: be 20 addr)))

/-- `formatEvmV1(chainid)` (:56-59): a chain with no address. The address length byte is `0`. -/
def formatEvmV1Chain (chainid : ℕ) : List UInt8 :=
  be 4 0x00010000 ++ (UInt8.ofNat (toChainReference chainid).length ::
    (toChainReference chainid ++ [UInt8.ofNat 0]))

/-- `formatEvmV1(addr)` (:64-66): an address with no chain reference,
`abi.encodePacked(bytes6(0x000100000014), addr)`. -/
def formatEvmV1Addr (addr : ℕ) : List UInt8 :=
  be 6 0x000100000014 ++ be 20 addr

/-! ## Parsing -/

/-- `tryParseV1(self)` (:95-119), checks in source order; `none` is `success == false`.

* `self.length < 6` (:100);
* the version, bytes `0..2`, is not `0x0001` (:102-103);
* the chain type is bytes `2..4` (:104); the reference length is byte `4` (:106);
* `self.length < 6 + chainReferenceLength` (:107-108);
* the reference is bytes `5 .. 5 + chainReferenceLength` (:109);
* the address length is the byte after the reference (:111);
* `self.length != 6 + chainReferenceLength + addrLength` (:112-113);
* the address is the last `addrLength` bytes (:114-117).

Returns `(chainType, chainReference, addr)`. -/
def tryParseV1 (self : List UInt8) : Option (ℕ × List UInt8 × List UInt8) :=
  if self.length < ERC7930_V1_MIN_LENGTH then none
  else if fromBytesBE (self.take 2) ≠ 1 then none
  else if self.length < ERC7930_V1_MIN_LENGTH + (self.getD 4 0).toNat then none
  else if self.length ≠ ERC7930_V1_MIN_LENGTH + (self.getD 4 0).toNat
      + (self.getD (5 + (self.getD 4 0).toNat) 0).toNat then none
  else some (fromBytesBE ((self.drop 2).take 2),
    (self.drop 5).take (self.getD 4 0).toNat,
    (self.drop (ERC7930_V1_MIN_LENGTH + (self.getD 4 0).toNat)).take
      (self.getD (5 + (self.getD 4 0).toNat) 0).toNat)

/-- **Ablation, not source.** `tryParseV1` with the exact-length check (:112-113) weakened from
`!=` to `<`, so that bytes after the address are tolerated. Used to show the exact check is
load-bearing. -/
def tryParseV1Lenient (self : List UInt8) : Option (ℕ × List UInt8 × List UInt8) :=
  if self.length < ERC7930_V1_MIN_LENGTH then none
  else if fromBytesBE (self.take 2) ≠ 1 then none
  else if self.length < ERC7930_V1_MIN_LENGTH + (self.getD 4 0).toNat then none
  else if self.length < ERC7930_V1_MIN_LENGTH + (self.getD 4 0).toNat
      + (self.getD (5 + (self.getD 4 0).toNat) 0).toNat then none
  else some (fromBytesBE ((self.drop 2).take 2),
    (self.drop 5).take (self.getD 4 0).toNat,
    (self.drop (ERC7930_V1_MIN_LENGTH + (self.getD 4 0).toNat)).take
      (self.getD (5 + (self.getD 4 0).toNat) 0).toNat)

/-- `bytesN(b)` for a `bytes` value `b`, as a number: the first `n` bytes of `b` right-padded
with zeros. -/
def bytesNOf (n : ℕ) (b : List UInt8) : ℕ := fromBytesBE ((b ++ List.replicate n 0).take n)

/-- `tryParseEvmV1(self)` (:178-191); `none` is `success == false`. Succeeds when `tryParseV1`
does, the chain type is `0x0000` (eip-155), the reference is shorter than 33 bytes and the address
has 0 or 20 bytes (:181-184). Then `chainId = uint256(bytes32(chainReference)) >> (256 - 8 ·
chainReference.length)` (:187) and `addr = address(bytes20(addr))` (:188). -/
def tryParseEvmV1 (self : List UInt8) : Option (ℕ × ℕ) :=
  match tryParseV1 self with
  | none => none
  | some (chainType, chainReference, addr) =>
    if chainType = 0 ∧ chainReference.length < 33 ∧ (addr.length = 0 ∨ addr.length = 20) then
      some (bytesNOf 32 chainReference >>> (256 - 8 * chainReference.length), bytesNOf 20 addr)
    else none

end Contracts.InteroperableAddress
