import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashEncoding

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false


/-! The ABI byte layer: statements and proofs for `Specs/BundleHashEncoding.lean`, whose header
describes the scope. -/

namespace AttackVectors.BundleHashEncoding


abbrev Properties.length_toBytesBE (k n : ℕ) :=
  (toBytesBE k n).length = k


abbrev Properties.fromBytesBE_append_singleton (l : List UInt8) (x : UInt8) :=
  fromBytesBE (l ++ [x]) = fromBytesBE l * 256 + x.toNat


/-- **WORDS ARE RECOVERABLE.**  Below `256 ^ k`, reading back `k` big-endian bytes returns the value. -/
abbrev Properties.fromBytesBE_toBytesBE {k n : ℕ} (h : n < 256 ^ k) :=
  fromBytesBE (toBytesBE k n) = n


/-- **ROUND TRIP.**  The encoding of a bundle determines — indeed yields back — the pair it was built
from, with no assumption about keccak.  Both side conditions are EVM word bounds. -/
abbrev Properties.abiDecode_abiEncode {c : ℕ} {b : List UInt8}
    (hc : c < 256 ^ 32) (hb : b.length < 256 ^ 32) :=
  abiDecode (abiEncode c b) = (c, b)


/-- **INJECTIVITY**: equal encodings force equal pairs, so a keccak of this encoding collides across
distinct `(uint256, bytes)` pairs only by a KECCAK collision. There is no cheaper encoding-level
route. (At the pin `c67894b9` this was the bundle hash's preimage.) -/
abbrev Properties.abiEncode_inj {c c' : ℕ} {b b' : List UInt8}
    (hc : c < 256 ^ 32) (hb : b.length < 256 ^ 32)
    (hc' : c' < 256 ^ 32) (hb' : b'.length < 256 ^ 32)
    (h : abiEncode c b = abiEncode c' b') :=
  c = c' ∧ b = b'


/-! ### Model validation

A round-trip theorem holds just as well for a WRONG encoding — it only says the decoder inverts the
encoder I wrote.  What it cannot do is check that the encoder is the one `solc` emits.  These are the
independent checks, pinned so they are re-verified on every build rather than eyeballed once: total
length, the constant offset word, the length word's position, the payload's start, and the padding. -/

set_option maxRecDepth 8000


/-- **THE PACKED FORM IS ALSO INJECTIVE HERE.**  A fixed-width leading argument pins the split, so at
this call site `abi.encode` is defensive rather than load-bearing. -/
abbrev Properties.packed_inj {c c' : ℕ} {b b' : List UInt8}
    (hc : c < 256 ^ 32) (hc' : c' < 256 ^ 32)
    (h : packed c b = packed c' b') :=
  c = c' ∧ b = b'


/-- **WHERE THE LENGTH PREFIX ACTUALLY EARNS ITS KEEP.**  With TWO dynamic arguments the packed form
collides outright — no hash break, no word bound, just a different split of the same bytes.  This is
why the pattern must not be copied to a two-`bytes` signature, and it is the concrete reason the
library exists rather than each call site rolling its own. -/
abbrev Properties.packedPair_not_inj :=
  ∃ (b₁ b₂ b₁' b₂' : List UInt8),
        (b₁, b₂) ≠ (b₁', b₂') ∧ b₁ ++ b₂ = b₁' ++ b₂'


/-! ## A second call site: the salt derivation, and why bundle hashes are unique

`InteropCenter` keeps bundle hashes distinct by construction:

    require(!isInteropBundleSaltUsed[msg.sender][_bundleAttributes.salt], ...);
    isInteropBundleSaltUsed[msg.sender][_bundleAttributes.salt] = true;
    ...
    interopBundleSalt: keccak256(abi.encodePacked(msg.sender, _bundleAttributes.salt)),

This matters beyond hygiene: `bundleHash` keys the leg state (`_state[flowId][bundleHash]`), the bundle
status, and the per-call status.  Two distinct sends sharing a hash would let one bundle's state stand
in for another's — a delivered bundle could block a fresh one, or a fresh one inherit `FullyExecuted`.

`abi.encodePacked` again, and again the question is whether the split is pinned.  Here BOTH operands
are fixed-width — `address` is 20 bytes, `salt` is `bytes32` — so it is, and the general fact is worth
stating once rather than re-deriving per site. -/

/-- **A FIXED-WIDTH PREFIX PINS THE SPLIT.**  Packing is injective whenever the leading field has known
width, regardless of what follows.  `packedPair_not_inj` above is the contrast: with two DYNAMIC fields
there is no such pin. -/
abbrev Properties.packed_fixed_inj {k m : ℕ} {a a' : ℕ} {b b' : List UInt8}
    (ha : a < 256 ^ k) (ha' : a' < 256 ^ k)
    (hb : b.length = m) (hb' : b'.length = m)
    (h : toBytesBE k a ++ b = toBytesBE k a' ++ b') :=
  a = a' ∧ b = b'


/-- The deployed instance: `abi.encodePacked(address, bytes32)` determines the pair.  So distinct
`(sender, salt)` pairs give distinct salt preimages, and — with keccak injectivity on those preimages —
distinct `interopBundleSalt` values. -/
abbrev Properties.packed_addr_salt_inj {a a' : ℕ} {s s' : List UInt8}
    (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20)
    (hs : s.length = 32) (hs' : s'.length = 32)
    (h : toBytesBE 20 a ++ s = toBytesBE 20 a' ++ s') :=
  a = a' ∧ s = s'


/-- **DISTINCT SENDS, DISTINCT BUNDLE HASHES.**  The composition, with the two hash steps as
hypotheses since keccak is idealized here: the salt guard makes `(sender, salt)` unique per send, the
packed encoding turns that into a unique salt preimage, and the salt is a field of the bundle whose
`abi.encode` preimage the bundle hash commits to.

Stated over abstract `saltHash` / `bundleHashOf` so the arithmetic content — that neither ENCODING
step loses information — is separated from the cryptographic assumption. -/
abbrev Properties.distinct_sends_distinct_hashes {Bundle Hash : Type*}
    (saltHash : List UInt8 → Hash) (bundleHashOf : Bundle → Hash) (saltField : Bundle → Hash)
    (hsalt_inj : Function.Injective saltHash)
    (hbundle_inj : Function.Injective bundleHashOf)
    {a a' : ℕ} {s s' : List UInt8} {b b' : Bundle}
    (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20) (hs : s.length = 32) (hs' : s'.length = 32)
    (hb : saltField b = saltHash (toBytesBE 20 a ++ s))
    (hb' : saltField b' = saltHash (toBytesBE 20 a' ++ s'))
    (hne : ¬ (a = a' ∧ s = s')) :=
  bundleHashOf b ≠ bundleHashOf b'


end AttackVectors.BundleHashEncoding
