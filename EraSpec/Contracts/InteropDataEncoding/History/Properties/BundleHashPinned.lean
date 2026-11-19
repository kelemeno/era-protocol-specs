import EraSpec.Contracts.InteropDataEncoding.History.Specs.BundleHashPinned

/-!
# History properties: the keccak layer of `BundleHashPinned` at the interop pin `c67894b9`

**A record of an older commit, not a claim about era-contracts `b17415d20`.** The bundle hash here is
the pin's `keccak(abi.encode(chainId, abi.encode(bundle)))` (`History/Specs/BundleHashPinned.lean`).
The `b17415d20` statements are topic `BundleHashAtV35`: `SendsDistinctBundleHashesOrKeccakCollisionV35`,
`SendsDistinctBundleHashesOnV35`, `SendsDistinctBundleHashesAcrossChainsOrKeccakCollisionV35`, their
witnesses `SendsDistinctBundleHashesWitnessV35`, `SendsAcrossChainsWitnessV35`, and the countermodel
`PreimageCollisionDisjunctNeededV35`; `PreimageCarriesSalt`'s counterpart is
`SaltSlotOfBundleEncoding`, since at `b17415d20` the keccak input is the bundle bytes themselves.
Proofs are in `History/Proofs/BundleHashPinned.lean`. Line numbers below are at `c67894b9`.
-/

namespace AttackVectors.BundleHashEncoding.History

/-- **THE BUNDLE HASH'S PREIMAGE CARRIES THE SALT.** In `abi.encode(chainId, abi.encode(bundle))`,
the keccak input of the bundle hash, the bundle's salt word sits at bytes 256..288
(`preimageSaltSlot`). So two equal preimages carry equal salts. -/
def Properties.PreimageCarriesSalt : Prop :=
  ∀ (c : ℕ) (version : UInt8) (sourceChainId destinationChainId baseTokenAssetId salt callsOffset
      attributesOffset : ℕ) (tail : List UInt8),
    preimageSaltSlot (abiEncode c (bundleEncoding version sourceChainId destinationChainId
      baseTokenAssetId salt callsOffset attributesOffset tail)) = word salt

/-- **DISTINCT SENDS, DISTINCT BUNDLE HASHES, OR A KECCAK COLLISION ON NAMED BYTES.** This is the
headline at the level of the code.

Each send is given by:

* a chain id `c`;
* a sender `a` and a user salt `s`;
* bundle bytes `B` whose salt slot holds the word `keccak(abi.encodePacked(a, s))`
  (`InteropCenter.sol:507`, laid out by `abi.encode(_bundle)` at `:643`).

The bundle hashes `keccak(abi.encode(c, B))` (`:644`) of two sends with distinct `(sender, salt)`
pairs differ, unless one of these holds:

* keccak collides on the two keccak preimages `abiEncode c B`, `abiEncode c' B'`;
* keccak collides on the two packed preimages `packedSalt a s`, `packedSalt a' s'`.

Nothing is assumed about `keccak`, and `B` is any byte string with that slot, so non-canonical
encodings are covered too. -/
def Properties.SendsDistinctBundleHashesOrKeccakCollision : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (c c' a a' : ℕ) (s s' B B' : List UInt8),
    a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 →
    bundleSaltSlot B = word (keccak (packedSalt a s)).val →
    bundleSaltSlot B' = word (keccak (packedSalt a' s')).val →
    ¬ (a = a' ∧ s = s') →
      bundleHashOfBytes keccak c B ≠ bundleHashOfBytes keccak c' B'
      ∨ HashCollision keccak (abiEncode c B) (abiEncode c' B')
      ∨ HashCollision keccak (packedSalt a s) (packedSalt a' s')

/-- **DISTINCT SENDS, DISTINCT BUNDLE HASHES, BOUNDED.** The keccak headline with its two collision
disjuncts turned into premises: keccak is injective on the two named keccak preimages and on the two
named packed preimages. This is the "explicitly bounded no-collision premise for the values the
proof compares" that ASSUMPTIONS.md asks for. -/
def Properties.SendsDistinctBundleHashesOn : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (c c' a a' : ℕ) (s s' B B' : List UInt8),
    a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 →
    bundleSaltSlot B = word (keccak (packedSalt a s)).val →
    bundleSaltSlot B' = word (keccak (packedSalt a' s')).val →
    ¬ (a = a' ∧ s = s') →
    Set.InjOn keccak {abiEncode c B, abiEncode c' B'} →
    Set.InjOn keccak {packedSalt a s, packedSalt a' s'} →
      bundleHashOfBytes keccak c B ≠ bundleHashOfBytes keccak c' B'

/-- **ACROSS CHAINS TOO: THE CHAIN ID KEEPS A REUSED SALT APART.** Every chain runs its own
`InteropCenter` with its own salt guard. So one sender may use one salt on two chains, and both
bundles then carry the same `interopBundleSalt`. The salt cannot separate those two bundles. The
chain id does: `encodeInteropBundleHash` hashes `abi.encode(block.chainid, B)`
(`InteropCenter.sol:644`).

For two sends whose `(chain, sender, salt)` triples differ, the bundle hashes differ, unless keccak
collides on the two named keccak preimages, or on the two named packed preimages. A destination
needs this form, because it keys `bundleStatus` by the bundle hash alone, whatever the source chain
(`InteropHandlerBase.sol:249-250`).

The chain-id bounds are the `uint256` width of `block.chainid`. The premise treats two chains with
one chain id as one chain; that chain ids are unique is a registry fact outside this model. -/
def Properties.SendsDistinctBundleHashesAcrossChainsOrKeccakCollision : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (c c' a a' : ℕ) (s s' B B' : List UInt8),
    c < 256 ^ 32 → c' < 256 ^ 32 →
    a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 →
    bundleSaltSlot B = word (keccak (packedSalt a s)).val →
    bundleSaltSlot B' = word (keccak (packedSalt a' s')).val →
    ¬ (c = c' ∧ a = a' ∧ s = s') →
      bundleHashOfBytes keccak c B ≠ bundleHashOfBytes keccak c' B'
      ∨ HashCollision keccak (abiEncode c B) (abiEncode c' B')
      ∨ HashCollision keccak (packedSalt a s) (packedSalt a' s')

/-- **THE CROSS-CHAIN PREMISES ARE SATISFIABLE WITH ONE SENDER AND ONE SALT ON TWO CHAINS.** This is
the case the salt guard cannot separate. One sender uses one salt on two chains, so the two packed
preimages are the same and the salt-collision disjunct is false. The two bundles differ only in
their source chain id. The keccak-preimage disjunct is false too, and the bundle hashes differ. -/
def Properties.SendsAcrossChainsWitness : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (c c' a : ℕ) (s B B' : List UInt8),
    c < 256 ^ 32 ∧ c' < 256 ^ 32 ∧ a < 256 ^ 20 ∧ s.length = 32
    ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
    ∧ bundleSaltSlot B' = word (keccak (packedSalt a s)).val
    ∧ c ≠ c'
    ∧ (∃ (v : UInt8) (dst base oc oa : ℕ) (tail : List UInt8),
        B = bundleEncoding v c dst base (keccak (packedSalt a s)).val oc oa tail
        ∧ B' = bundleEncoding v c' dst base (keccak (packedSalt a s)).val oc oa tail)
    ∧ ¬ HashCollision keccak (abiEncode c B) (abiEncode c' B')
    ∧ bundleHashOfBytes keccak c B ≠ bundleHashOfBytes keccak c' B'

/-- **THE KECCAK-LAYER PREMISES ARE SATISFIABLE, AND ITS DISJUNCTS ARE NOT TAUTOLOGIES.** One
instance satisfies every premise of the two properties above, with both sends on the same chain `c`.
In it:

* the bundle bytes of both sends are `bundleEncoding` layouts;
* the bounded injectivity premises hold;
* neither collision disjunct holds;
* the two bundle hashes differ. -/
def Properties.SendsDistinctBundleHashesWitness : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (c a a' : ℕ) (s s' B B' : List UInt8),
    a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
    ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
    ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
    ∧ ¬ (a = a' ∧ s = s')
    ∧ (∃ (v : UInt8) (dst base oc oa : ℕ) (tail : List UInt8),
        B = bundleEncoding v c dst base (keccak (packedSalt a s)).val oc oa tail
        ∧ B' = bundleEncoding v c dst base (keccak (packedSalt a' s')).val oc oa tail)
    ∧ Set.InjOn keccak {abiEncode c B, abiEncode c B'}
    ∧ Set.InjOn keccak {packedSalt a s, packedSalt a' s'}
    ∧ ¬ HashCollision keccak (abiEncode c B) (abiEncode c B')
    ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a' s')
    ∧ bundleHashOfBytes keccak c B ≠ bundleHashOfBytes keccak c B'

/-- **THE PREIMAGE DISJUNCT CANNOT BE DROPPED.** There is an instance with both sends on one chain
satisfying every premise of `SendsDistinctBundleHashesOrKeccakCollision`, in which:

* the bundle hashes are equal;
* keccak does not collide on the two packed preimages.

So only the keccak-preimage disjunct holds. -/
def Properties.PreimageCollisionDisjunctNeeded : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (c a a' : ℕ) (s s' B B' : List UInt8),
    a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
    ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
    ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
    ∧ ¬ (a = a' ∧ s = s')
    ∧ bundleHashOfBytes keccak c B = bundleHashOfBytes keccak c B'
    ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a' s')


end AttackVectors.BundleHashEncoding.History
