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

@[simp] theorem length_toBytesBE (k n : ℕ) : (toBytesBE k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [toBytesBE, ih]

theorem fromBytesBE_append_singleton (l : List UInt8) (x : UInt8) :
    fromBytesBE (l ++ [x]) = fromBytesBE l * 256 + x.toNat := by
  simp [fromBytesBE, List.foldl_append]

/-- **WORDS ARE RECOVERABLE.**  Below `256 ^ k`, reading back `k` big-endian bytes returns the value. -/
theorem fromBytesBE_toBytesBE {k n : ℕ} (h : n < 256 ^ k) :
    fromBytesBE (toBytesBE k n) = n := by
  induction k generalizing n with
  | zero => simpa [toBytesBE, fromBytesBE] using (Nat.lt_one_iff.mp (by simpa using h)).symm
  | succ k ih =>
    have hdiv : n / 256 < 256 ^ k := by
      apply Nat.div_lt_of_lt_mul
      calc n < 256 ^ (k + 1) := h
        _ = 256 * 256 ^ k := by ring
    have hmod : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      unfold UInt8.toNat UInt8.ofNat
      simp [Fin.ofNat]
    rw [toBytesBE, fromBytesBE_append_singleton, ih hdiv, hmod]
    omega

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

/-- **ROUND TRIP.**  The encoding of a bundle determines — indeed yields back — the pair it was built
from, with no assumption about keccak.  Both side conditions are EVM word bounds. -/
theorem abiDecode_abiEncode {c : ℕ} {b : List UInt8}
    (hc : c < 256 ^ 32) (hb : b.length < 256 ^ 32) :
    abiDecode (abiEncode c b) = (c, b) := by
  have hlen : (word c).length = 32 := length_toBytesBE 32 c
  have hlen2 : (word c ++ word 0x40).length = 64 := by
    simp [List.length_append, length_toBytesBE]
  have hlen3 : (word c ++ word 0x40 ++ word b.length).length = 96 := by
    simp [List.length_append, length_toBytesBE]
  -- peel the three head words off with `take_left'` / `drop_left'`
  have h1 : (abiEncode c b).take 32 = word c := by
    rw [abiEncode]; exact List.take_left' hlen
  have h2 : (abiEncode c b).drop 64 = word b.length ++ pad32 b := by
    have : abiEncode c b = (word c ++ word 0x40) ++ (word b.length ++ pad32 b) := by
      simp [abiEncode, List.append_assoc]
    rw [this]; exact List.drop_left' hlen2
  have h3 : (abiEncode c b).drop 96 = pad32 b := by
    have : abiEncode c b = (word c ++ word 0x40 ++ word b.length) ++ pad32 b := by
      simp [abiEncode, List.append_assoc]
    rw [this]; exact List.drop_left' hlen3
  have h4 : ((abiEncode c b).drop 64).take 32 = word b.length := by
    rw [h2]; exact List.take_left' (length_toBytesBE 32 b.length)
  -- and the padding is dropped by taking exactly `b.length` bytes
  have h5 : (pad32 b).take b.length = b := by
    rw [pad32]; exact List.take_left' rfl
  simp only [abiDecode, h1, h3, h4, h5, fromBytesBE_toBytesBE hc, fromBytesBE_toBytesBE hb]

/-- **INJECTIVITY**, the form the binding results use: equal encodings force equal pairs, so a bundle
hash collision across distinct `(sourceChainId, bundle)` pairs requires a KECCAK collision.  There is
no cheaper encoding-level route. -/
theorem abiEncode_inj {c c' : ℕ} {b b' : List UInt8}
    (hc : c < 256 ^ 32) (hb : b.length < 256 ^ 32)
    (hc' : c' < 256 ^ 32) (hb' : b'.length < 256 ^ 32)
    (h : abiEncode c b = abiEncode c' b') : c = c' ∧ b = b' := by
  have := abiDecode_abiEncode hc hb
  rw [h, abiDecode_abiEncode hc' hb'] at this
  exact ⟨(Prod.mk.injEq .. ▸ this).1.symm, (Prod.mk.injEq .. ▸ this).2.symm⟩

/-! ### Model validation

A round-trip theorem holds just as well for a WRONG encoding — it only says the decoder inverts the
encoder I wrote.  What it cannot do is check that the encoder is the one `solc` emits.  These are the
independent checks, pinned so they are re-verified on every build rather than eyeballed once: total
length, the constant offset word, the length word's position, the payload's start, and the padding. -/

set_option maxRecDepth 8000

example : (abiEncode 1 [0xaa]).length = 128 := by decide          -- four words
example : (abiEncode 1 [0xaa]).get! 31 = 1 := by decide           -- chainId, low byte of word 0
example : (abiEncode 1 [0xaa]).get! 63 = 0x40 := by decide        -- offset word = 0x40
example : (abiEncode 1 [0xaa]).get! 95 = 1 := by decide           -- length word
example : (abiEncode 1 [0xaa]).get! 96 = 0xaa := by decide        -- payload starts at 96
example : (abiEncode 1 [0xaa]).get! 97 = 0 := by decide           -- right-padded with zeros
example : (abiEncode 7 (List.replicate 33 9)).length = 160 := by decide  -- 33 bytes ⇒ two pad words

/-! ## Was `abi.encode` load-bearing here?

The natural guess is that `abi.encodePacked` would have been a bug, since packed encodings drop the
length prefix.  For THIS signature that guess is WRONG, and saying otherwise would overstate the
result: the first argument is fixed-width, so the split point is still pinned. -/

/-- `abi.encodePacked(uint256, bytes)`. -/
def packed (c : ℕ) (b : List UInt8) : List UInt8 := word c ++ b

/-- **THE PACKED FORM IS ALSO INJECTIVE HERE.**  A fixed-width leading argument pins the split, so at
this call site `abi.encode` is defensive rather than load-bearing. -/
theorem packed_inj {c c' : ℕ} {b b' : List UInt8}
    (hc : c < 256 ^ 32) (hc' : c' < 256 ^ 32)
    (h : packed c b = packed c' b') : c = c' ∧ b = b' := by
  have hw : word c = word c' ∧ b = b' := by
    constructor
    · have := congrArg (List.take 32) h
      simpa [packed, List.take_left' (length_toBytesBE 32 c),
        List.take_left' (length_toBytesBE 32 c')] using this
    · have := congrArg (List.drop 32) h
      simpa [packed, List.drop_left' (length_toBytesBE 32 c),
        List.drop_left' (length_toBytesBE 32 c')] using this
  refine ⟨?_, hw.2⟩
  have := congrArg fromBytesBE hw.1
  rwa [fromBytesBE_toBytesBE hc, fromBytesBE_toBytesBE hc'] at this

/-- **WHERE THE LENGTH PREFIX ACTUALLY EARNS ITS KEEP.**  With TWO dynamic arguments the packed form
collides outright — no hash break, no word bound, just a different split of the same bytes.  This is
why the pattern must not be copied to a two-`bytes` signature, and it is the concrete reason the
library exists rather than each call site rolling its own. -/
theorem packedPair_not_inj :
    ∃ (b₁ b₂ b₁' b₂' : List UInt8),
      (b₁, b₂) ≠ (b₁', b₂') ∧ b₁ ++ b₂ = b₁' ++ b₂' := by
  refine ⟨[1], [2, 3], [1, 2], [3], ?_, rfl⟩
  simp

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
theorem packed_fixed_inj {k m : ℕ} {a a' : ℕ} {b b' : List UInt8}
    (ha : a < 256 ^ k) (ha' : a' < 256 ^ k)
    (hb : b.length = m) (hb' : b'.length = m)
    (h : toBytesBE k a ++ b = toBytesBE k a' ++ b') : a = a' ∧ b = b' := by
  have hlen : (toBytesBE k a).length = k := length_toBytesBE k a
  have hlen' : (toBytesBE k a').length = k := length_toBytesBE k a'
  constructor
  · have hw : toBytesBE k a = toBytesBE k a' := by
      have := congrArg (List.take k) h
      rwa [List.take_left' hlen, List.take_left' hlen'] at this
    have := congrArg fromBytesBE hw
    rwa [fromBytesBE_toBytesBE ha, fromBytesBE_toBytesBE ha'] at this
  · have := congrArg (List.drop k) h
    rwa [List.drop_left' hlen, List.drop_left' hlen'] at this

/-- The deployed instance: `abi.encodePacked(address, bytes32)` determines the pair.  So distinct
`(sender, salt)` pairs give distinct salt preimages, and — with keccak injectivity on those preimages —
distinct `interopBundleSalt` values. -/
theorem packed_addr_salt_inj {a a' : ℕ} {s s' : List UInt8}
    (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20)
    (hs : s.length = 32) (hs' : s'.length = 32)
    (h : toBytesBE 20 a ++ s = toBytesBE 20 a' ++ s') : a = a' ∧ s = s' :=
  packed_fixed_inj ha ha' hs hs' h

/-- **DISTINCT SENDS, DISTINCT BUNDLE HASHES.**  The composition, with the two hash steps as
hypotheses since keccak is idealized here: the salt guard makes `(sender, salt)` unique per send, the
packed encoding turns that into a unique salt preimage, and the salt is a field of the bundle whose
`abi.encode` preimage the bundle hash commits to.

Stated over abstract `saltHash` / `bundleHashOf` so the arithmetic content — that neither ENCODING
step loses information — is separated from the cryptographic assumption. -/
theorem distinct_sends_distinct_hashes
    {Bundle Hash : Type*}
    (saltHash : List UInt8 → Hash) (bundleHashOf : Bundle → Hash) (saltField : Bundle → Hash)
    (hsalt_inj : Function.Injective saltHash)
    (hbundle_inj : Function.Injective bundleHashOf)
    {a a' : ℕ} {s s' : List UInt8} {b b' : Bundle}
    (ha : a < 256 ^ 20) (ha' : a' < 256 ^ 20) (hs : s.length = 32) (hs' : s'.length = 32)
    (hb : saltField b = saltHash (toBytesBE 20 a ++ s))
    (hb' : saltField b' = saltHash (toBytesBE 20 a' ++ s'))
    (hne : ¬ (a = a' ∧ s = s')) :
    bundleHashOf b ≠ bundleHashOf b' := by
  intro hcollide
  -- a hash collision would make the bundles equal, hence their salt fields equal
  have hbb : b = b' := hbundle_inj hcollide
  subst hbb
  -- `hb ▸ hb'` would make Lean search for a motive here and time out; compose explicitly
  have heq : saltHash (toBytesBE 20 a ++ s) = saltHash (toBytesBE 20 a' ++ s') := hb.symm.trans hb'
  exact hne (packed_addr_salt_inj ha ha' hs hs' (hsalt_inj heq))

end AttackVectors.BundleHashEncoding
