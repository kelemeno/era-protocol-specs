import EraSpec.Contracts.InteroperableAddress.Specs.Erc7930

/-!
# Properties: ERC-7930 formatting and parsing

Statements about `EraSpec.Contracts.InteroperableAddress.Specs.Erc7930`; proofs in
`EraSpec.Contracts.InteroperableAddress.Proofs.Erc7930`.

Valid domain: a `bytes2` chain type (below `2^16`), a chain reference and an address of at most 255
bytes each (their lengths are single bytes); for the EVM forms a `uint256` chain id and an
`address` (below `2^160`).

Groups:

* generic V1: `FormatV1Defined`, `ParseFormatV1RoundTrip`, `ParseV1Canonical`,
  `FormatV1Injective`: `tryParseV1` and `formatV1Bytes` are mutually inverse, so the accepted byte
  strings and the triples correspond one to one;
* a formatter/parser mismatch: `ParseV1AcceptsWhatFormatV1Rejects`;
* the EVM chain reference: `ChainReferenceIsMinimalBigEndian`;
* EVM forms: `FormatEvmIsFormatV1`, `ParseFormatEvmRoundTrip`, `FormatEvmInjective`,
  `ParseEvmReadsBigEndianValues`;
* what `parseEvmV1` does not distinguish: `ParseEvmNotInjective`,
  `ParseEvmCannotTellChainZeroFromNoChain`;
* a load-bearing check: `ExactLengthCheckLoadBearing`.
-/

namespace Contracts.InteroperableAddress

open AttackVectors.BundleHashEncoding Contracts.DataEncoding

/-! ## Generic version 1 -/

/-- **WHEN `formatV1` SUCCEEDS, AND WHAT IT RETURNS.** `formatV1` returns bytes exactly when the
reference and the address are not both empty and each has at most 255 bytes; the bytes are then
`formatV1Bytes`. -/
def Properties.FormatV1Defined : Prop :=
  ∀ (ct : ℕ) (ref addr d : List UInt8),
    formatV1 ct ref addr = some d ↔
      (0 < ref.length ∨ 0 < addr.length) ∧ ref.length ≤ 255 ∧ addr.length ≤ 255 ∧
        d = formatV1Bytes ct ref addr

/-- **PARSE ∘ FORMAT (V1).** `tryParseV1` reads back the chain type, reference and address of
every version-1 byte string with lengths at most 255, including the one with both parts empty
(which `formatV1` itself refuses to produce). -/
def Properties.ParseFormatV1RoundTrip : Prop :=
  ∀ (ct : ℕ) (ref addr : List UInt8), ct < 2 ^ 16 → ref.length ≤ 255 → addr.length ≤ 255 →
    tryParseV1 (formatV1Bytes ct ref addr) = some (ct, ref, addr)

/-- **FORMAT ∘ PARSE (V1): PARSING IS CANONICAL.** Whatever `tryParseV1` accepts is exactly the
version-1 byte string of the components it returns, and those components are in the valid domain.
So two accepted byte strings with the same parsed components are equal. -/
def Properties.ParseV1Canonical : Prop :=
  ∀ (d : List UInt8) (ct : ℕ) (ref addr : List UInt8), tryParseV1 d = some (ct, ref, addr) →
    d = formatV1Bytes ct ref addr ∧ ct < 2 ^ 16 ∧ ref.length ≤ 255 ∧ addr.length ≤ 255

/-- **`formatV1` BYTES ARE INJECTIVE** on the valid domain, as a statement about byte lists. -/
def Properties.FormatV1Injective : Prop :=
  ∀ (ct ct' : ℕ) (ref addr ref' addr' : List UInt8),
    ct < 2 ^ 16 → ref.length ≤ 255 → addr.length ≤ 255 →
    ct' < 2 ^ 16 → ref'.length ≤ 255 → addr'.length ≤ 255 →
    formatV1Bytes ct ref addr = formatV1Bytes ct' ref' addr' → (ct, ref, addr) = (ct', ref', addr')

/-- **THE PARSER ACCEPTS A STRING THE FORMATTER REFUSES.** `0x000100000000` (version 1, chain type
eip-155, empty reference, empty address) parses successfully with `tryParseV1`, and as
`(chainId, addr) = (0, address(0))` with `tryParseEvmV1`, yet no call of `formatV1` returns it:
`formatV1` reverts with `InteroperableAddressEmptyReferenceAndAddress` (:32). The NatSpec of
`tryParseV1` (:92-93) says it returns `false` "when the input does not follow version 1 of
ERC-7930"; under the formatter's own rule (reference and address not both empty) this input does
not, and it is accepted. -/
def Properties.ParseV1AcceptsWhatFormatV1Rejects : Prop :=
  ∃ d : List UInt8,
    tryParseV1 d = some (0, [], []) ∧ tryParseEvmV1 d = some (0, 0) ∧
    ∀ (ct : ℕ) (ref addr : List UInt8), formatV1 ct ref addr ≠ some d

/-! ## The EVM chain reference -/

/-- **`_toChainReference` IS THE MINIMAL BIG-ENDIAN ENCODING.** For a `uint256` chain id the
reference is the big-endian bytes of the chain id in `log256(chainid) + 1` bytes: between 1 and 32
bytes, reading back to the chain id, with no leading zero byte unless the chain id is `0` (whose
reference is the single byte `0x00`). -/
def Properties.ChainReferenceIsMinimalBigEndian : Prop :=
  ∀ c : ℕ, c < 2 ^ 256 →
    toChainReference c = be (log256 c + 1) c ∧
    1 ≤ (toChainReference c).length ∧ (toChainReference c).length ≤ 32 ∧
    fromBytesBE (toChainReference c) = c ∧
    (c ≠ 0 → (toChainReference c).head? ≠ some 0)

/-! ## EVM forms -/

/-- **THE EVM FORMATTERS ARE INSTANCES OF `formatV1`.** Each of the three `formatEvmV1` overloads
returns what `formatV1` returns for chain type `0x0000` and the corresponding reference and
address, and `formatV1` does not revert there. -/
def Properties.FormatEvmIsFormatV1 : Prop :=
  ∀ c a : ℕ, c < 2 ^ 256 →
    formatV1 0 (toChainReference c) (be 20 a) = some (formatEvmV1 c a) ∧
    formatV1 0 (toChainReference c) [] = some (formatEvmV1Chain c) ∧
    formatV1 0 [] (be 20 a) = some (formatEvmV1Addr a)

/-- **PARSE ∘ FORMAT (EVM).** `parseEvmV1` reads back `(chainid, addr)` from
`formatEvmV1(chainid, addr)`; `(chainid, address(0))` from the chain-only form; and `(0, addr)`
from the address-only form. -/
def Properties.ParseFormatEvmRoundTrip : Prop :=
  ∀ c a : ℕ, c < 2 ^ 256 → a < 2 ^ 160 →
    tryParseEvmV1 (formatEvmV1 c a) = some (c, a) ∧
    tryParseEvmV1 (formatEvmV1Chain c) = some (c, 0) ∧
    tryParseEvmV1 (formatEvmV1Addr a) = some (0, a)

/-- **THE EVM FORMATTERS ARE INJECTIVE** on the valid domain, as statements about byte lists. -/
def Properties.FormatEvmInjective : Prop :=
  ∀ c a c' a' : ℕ, c < 2 ^ 256 → a < 2 ^ 160 → c' < 2 ^ 256 → a' < 2 ^ 160 →
    (formatEvmV1 c a = formatEvmV1 c' a' → c = c' ∧ a = a') ∧
    (formatEvmV1Chain c = formatEvmV1Chain c' → c = c') ∧
    (formatEvmV1Addr a = formatEvmV1Addr a' → a = a')

/-- **WHAT `parseEvmV1` RETURNS.** It succeeds with `(c, a)` exactly when `tryParseV1` succeeds
with chain type `0x0000`, a reference of at most 32 bytes and an address of 0 or 20 bytes, and then
`c` is the big-endian value of the reference and `a` that of the address (`0` for an empty one).
So the shift expression at :187 computes the reference's numeric value, and the results are a
`uint256` and an `address`. -/
def Properties.ParseEvmReadsBigEndianValues : Prop :=
  ∀ (d : List UInt8) (c a : ℕ),
    (tryParseEvmV1 d = some (c, a) ↔
      ∃ ref addr : List UInt8, tryParseV1 d = some (0, ref, addr) ∧ ref.length ≤ 32 ∧
        (addr.length = 0 ∨ addr.length = 20) ∧ c = fromBytesBE ref ∧ a = fromBytesBE addr) ∧
    (tryParseEvmV1 d = some (c, a) → c < 2 ^ 256 ∧ a < 2 ^ 160)

/-! ## What `parseEvmV1` does not distinguish -/

/-- **`parseEvmV1` IS NOT INJECTIVE: LEADING ZEROS IN THE REFERENCE.** For every address and every
chain id below `2^248` there is a byte string other than `formatEvmV1(chainid, addr)` that
`parseEvmV1` accepts with the same result (the reference with one more leading zero byte). So
equality of parsed `(chainId, address)` pairs is strictly coarser than equality of the ERC-7930
bytes: a check on the parsed pair accepts encodings whose bytes, and therefore whose hashes,
differ from the canonical one. -/
def Properties.ParseEvmNotInjective : Prop :=
  ∀ c a : ℕ, c < 2 ^ 248 → a < 2 ^ 160 →
    ∃ d : List UInt8, d ≠ formatEvmV1 c a ∧ tryParseEvmV1 d = some (c, a)

/-- **`parseEvmV1` CANNOT TELL CHAIN ID ZERO FROM "NO CHAIN".** `formatEvmV1(0, addr)` (an explicit
one-byte reference `0x00`) and `formatEvmV1(addr)` (no reference) are different byte strings that
parse to the same `(0, addr)`. Callers that read `chainId == 0` as "any chain"
(`InteropHandlerBase.sol:124`) or as "no chain given" therefore also accept an explicit chain id
zero. -/
def Properties.ParseEvmCannotTellChainZeroFromNoChain : Prop :=
  ∀ a : ℕ, a < 2 ^ 160 →
    formatEvmV1 0 a ≠ formatEvmV1Addr a ∧
    tryParseEvmV1 (formatEvmV1 0 a) = some (0, a) ∧ tryParseEvmV1 (formatEvmV1Addr a) = some (0, a)

/-! ## A load-bearing check -/

/-- **COUNTERMODEL: THE EXACT-LENGTH CHECK IS LOAD-BEARING FOR CANONICITY** (:112-113). With `!=`
weakened to `<`, a version-1 byte string followed by any further bytes parses to the same
components, so parsing is no longer canonical; the source parser rejects every such extension. -/
def Properties.ExactLengthCheckLoadBearing : Prop :=
  ∀ (ct : ℕ) (ref addr rest : List UInt8), ct < 2 ^ 16 → ref.length ≤ 255 → addr.length ≤ 255 →
    rest ≠ [] →
    tryParseV1Lenient (formatV1Bytes ct ref addr ++ rest) = some (ct, ref, addr) ∧
    tryParseV1Lenient (formatV1Bytes ct ref addr) = some (ct, ref, addr) ∧
    tryParseV1 (formatV1Bytes ct ref addr ++ rest) = none

end Contracts.InteroperableAddress
