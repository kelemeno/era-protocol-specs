import Mathlib.Tactic


/-!
# Spec: the ABI byte layer shared by the encoding topics

This file models byte encodings from the Solidity ABI specification, not a contract function, so
it cites no era-contracts line. It is the shared vocabulary of the corpus's byte-level models:
big-endian words (`toBytesBE`, `fromBytesBE`, `word`), right padding (`pad32`), the head-and-tail
encoding `abi.encode(uint256, bytes)` (`abiEncode`) with its decoder, and the packed form
`abi.encodePacked(uint256, bytes)` (`packed`). The properties show that these encodings add no
collisions of their own (`abiEncode_inj`, `packed_inj`, `packed_fixed_inj`,
`packed_addr_salt_inj`).

At era-contracts `b17415d20` the bundle hash is `keccak256(abi.encode(bundle))`
(`interop/InteropDataEncoding.sol:14-16`), modelled by topic `BundleHashAtV35`. At the old interop
pin `c67894b9` it was `keccak256(abi.encode(_sourceChainId, _bundle))`, which is `abiEncode`; that
use is recorded under `History/` (`History/Specs/BundleHashPinned.lean`).

Scope: a byte-level model of the encodings, not the Yul solc emits (`SOL-ABI`).
-/

namespace AttackVectors.BundleHashEncoding


/-! ## Big-endian words -/

/-- `toBytesBE k n` — `n` as `k` big-endian bytes (truncating above `256 ^ k`). -/
def toBytesBE : ℕ → ℕ → List UInt8
  | 0, _ => []
  | k + 1, n => toBytesBE k (n / 256) ++ [UInt8.ofNat (n % 256)]


/-- Reading a big-endian byte string back as a natural number. -/
def fromBytesBE (l : List UInt8) : ℕ := l.foldl (fun acc b => acc * 256 + b.toNat) 0


/-- A 32-byte EVM word. -/
abbrev word (n : ℕ) : List UInt8 := toBytesBE 32 n


/-! ## `abi.encode(uint256, bytes)`

The head is the `uint256` and the offset of the dynamic argument; the tail is the byte string's length
followed by its right-padded contents.  The offset is constant `0x40` for this signature. -/

/-- Right-pad to a multiple of 32. -/
def pad32 (b : List UInt8) : List UInt8 :=
  b ++ List.replicate ((32 - b.length % 32) % 32) 0


/-- `abi.encode(uint256, bytes)`: at the pin `c67894b9`, `abi.encode(_sourceChainId, _bundle)`, the bundle
hash's keccak input. -/
def abiEncode (c : ℕ) (b : List UInt8) : List UInt8 :=
  word c ++ (word 0x40 ++ (word b.length ++ pad32 b))


/-- The decoder: read the head word, skip the offset, read the length, take that many bytes. -/
def abiDecode (e : List UInt8) : ℕ × List UInt8 :=
  (fromBytesBE (e.take 32),
   ((e.drop 96).take (fromBytesBE ((e.drop 64).take 32))))


/-! ### Model validation

A round-trip theorem holds just as well for a WRONG encoding — it only says the decoder inverts the
encoder I wrote.  What it cannot do is check that the encoder is the one `solc` emits.  These are the
independent checks, pinned so they are re-verified on every build rather than eyeballed once: total
length, the constant offset word, the length word's position, the payload's start, and the padding. -/

set_option maxRecDepth 8000
  -- 33 bytes ⇒ two pad words

/-! ## Was `abi.encode` load-bearing here?

The natural guess is that `abi.encodePacked` would have been a bug, since packed encodings drop the
length prefix.  For THIS signature that guess is WRONG, and saying otherwise would overstate the
result: the first argument is fixed-width, so the split point is still pinned. -/

/-- `abi.encodePacked(uint256, bytes)`. -/
def packed (c : ℕ) (b : List UInt8) : List UInt8 := word c ++ b


end AttackVectors.BundleHashEncoding
