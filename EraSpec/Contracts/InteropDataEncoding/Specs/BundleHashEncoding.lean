import Mathlib.Tactic


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/BundleHashEncoding.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  THE BUNDLE-HASH ENCODING — no ambiguity below keccak.

  Every binding result in this corpus that keys off a bundle hash assumes the hash DETERMINES the pair
  it was built from.  The deployed derivation is a single library function, and all four call sites go
  through it:

      library InteropDataEncoding {
          function encodeInteropBundleHash(uint256 _sourceChainId, bytes memory _bundle)
              internal pure returns (bytes32)
          {
              return keccak256(abi.encode(_sourceChainId, _bundle));
          }
      }

      InteropCenter.sol:644                encodeInteropBundleHash(block.chainid, interopBundleBytes)
      InteropHandlerBase.sol:249           encodeInteropBundleHash(interopBundle.sourceChainId, _bundle)
      AtomicFlowManager.sol:167            encodeInteropBundleHash(bundle.sourceChainId, _bundle)

  That assumption has two halves.  Keccak injectivity is the half this corpus already tracks (see
  `KeccakDeterminism` and the derived-counterparts note).  The OTHER half is that the ARGUMENT of
  keccak determines the pair — i.e. that the encoding step contributes no collisions of its own.  A
  collision there would need no hash break at all, so it is the cheaper attack, and nothing in the
  corpus checked it.

  This file closes that half, by exhibiting a DECODER and proving round-trip.  A left inverse gives
  injectivity and says more besides: the pair is recoverable, not merely determined.

  Scope: this is a byte-level model of `abi.encode(uint256, bytes)`, not the deployed Yul.  It shows the
  ENCODING SHAPE is unambiguous; that the compiler emits this shape is the standard ABI spec, and the
  concrete `abi_encode_*` specs under `specs/L1AssetRouter/` are where the emitted memory is checked.
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


/-- `abi.encode(_sourceChainId, _bundle)`. -/
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
