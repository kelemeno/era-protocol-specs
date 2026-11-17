import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashAtV35

/-!
# Properties at draft/v0.35.0: distinct sends give distinct bundle hashes, or a named collision

Statements about `EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashAtV35` (era-contracts
`draft/v0.35.0`, `d9f678900e1bc8286412b78f56d4a9f443983c29`). Proofs are in
`EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashAtV35`. Names end in `V35`; the pin's
statements (`Properties/BundleHashPinned.lean`) are untouched and still describe the pin.

None of these takes an injectivity premise on a hash function. The `…On` form takes injectivity
on exactly the two compared inputs, which is `¬ HashCollision` on them
(`Properties.InjOnPairIffNoCollision`, pin topic `BundleHashPinned`).

What changed from the pin, and what did not:

* The register (`SaltHashInjUnsatisfiable`, `SaltHashNotInjOnPackedPreimages`,
  `BundleHashInjUnsatisfiable`) and the abstract layer (`DistinctSendsDistinctHashesOrCollision`,
  `DistinctSendsDistinctBundlesOrSaltCollision`, `DistinctSendsDistinctHashesOn`) are about arbitrary
  hash functions. They apply to v35 verbatim, with `bundleHashOf := keccak ∘ abi.encode`.
* The keccak layer changes. The keccak preimage of the bundle hash is now the bundle bytes `B`
  themselves, so the preimage-collision disjunct names `(B, B')` instead of
  `(abi.encode(c, B), abi.encode(c', B'))`. Across chains, the separating word is `B`'s own
  `sourceChainId` slot (bytes 64..96) instead of the pin's outer chain-id word, which no longer
  exists. The cross-chain headline therefore needs no link between a chain id and `B` other than
  `B`'s own slot.
* `PinAndV35PreimagesCoincideOnSourcedBytesV35` relates the two: on bytes whose source slot holds
  the chain id (every bundle the center builds, `InteropCenter.sol:634`), two pin preimages are
  equal exactly when the two v35 preimages are. So the change re-keys keccak but separates exactly
  the same pairs of bundles.
-/

namespace AttackVectors.BundleHashEncoding.AtV35

open AttackVectors.BundleHashEncoding

/-! ## Layout: what the v35 keccak preimage carries -/

/-- **THE v35 PREIMAGE CARRIES THE SOURCE, THE DESTINATION AND THE SALT.** At v35 the bundle hash's
keccak preimage is the bundle bytes. In any `InteropBundle` encoding laid out as `bundleEncoding`,
whatever the other fields and the dynamic tail, the source chain id is at bytes 64..96, the
destination at 96..128, and the salt at 160..192. This checks the offsets of `bundleSourceSlot`,
`bundleDestSlot` and `bundleSaltSlot` against the head layout of `Messaging.sol:268-276`. -/
def Properties.PreimageCarriesSourceDestinationSaltV35 : Prop :=
  ∀ (version : UInt8) (sourceChainId destinationChainId baseTokenAssetId salt callsOffset
      attributesOffset : ℕ) (tail : List UInt8),
    bundleSourceSlot (bundleEncoding version sourceChainId destinationChainId baseTokenAssetId salt
        callsOffset attributesOffset tail) = word sourceChainId
    ∧ bundleDestSlot (bundleEncoding version sourceChainId destinationChainId baseTokenAssetId salt
        callsOffset attributesOffset tail) = word destinationChainId
    ∧ bundleSaltSlot (bundleEncoding version sourceChainId destinationChainId baseTokenAssetId salt
        callsOffset attributesOffset tail) = word salt

/-! ## The keccak layer at v35 -/

/-- **HEADLINE: DISTINCT SENDS, DISTINCT BUNDLE HASHES, OR A KECCAK COLLISION ON NAMED BYTES.**

Each send is given by a sender `a`, a user salt `s` and bundle bytes `B` whose salt slot holds the
word `keccak(abi.encodePacked(a, s))` (`InteropCenter.sol:638`, laid out by `abi.encode(_bundle)` at
`:691`). The v35 bundle hashes `keccak(B)` (`InteropDataEncoding.sol:14-16`) of two sends with
distinct `(sender, salt)` pairs differ, unless one of these holds:

* keccak collides on the two bundle byte strings `B`, `B'`;
* keccak collides on the two packed salt preimages `packedSalt a s`, `packedSalt a' s'`.

No chain id appears: the statement holds on one chain and across chains alike. Nothing is assumed
about `keccak`, and `B` is any byte string with that slot. -/
def Properties.SendsDistinctBundleHashesOrKeccakCollisionV35 : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B B' : List UInt8),
    a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 →
    bundleSaltSlot B = word (keccak (packedSalt a s)).val →
    bundleSaltSlot B' = word (keccak (packedSalt a' s')).val →
    ¬ (a = a' ∧ s = s') →
      bundleHashV35 keccak B ≠ bundleHashV35 keccak B'
      ∨ HashCollision keccak B B'
      ∨ HashCollision keccak (packedSalt a s) (packedSalt a' s')

/-- **DISTINCT SENDS, DISTINCT BUNDLE HASHES, BOUNDED.** The headline with its two collision
disjuncts turned into premises: keccak is injective on the two named bundle byte strings and on the
two named packed preimages. -/
def Properties.SendsDistinctBundleHashesOnV35 : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B B' : List UInt8),
    a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 →
    bundleSaltSlot B = word (keccak (packedSalt a s)).val →
    bundleSaltSlot B' = word (keccak (packedSalt a' s')).val →
    ¬ (a = a' ∧ s = s') →
    Set.InjOn keccak {B, B'} →
    Set.InjOn keccak {packedSalt a s, packedSalt a' s'} →
      bundleHashV35 keccak B ≠ bundleHashV35 keccak B'

/-- **ACROSS CHAINS: THE BUNDLE'S OWN SOURCE SLOT KEEPS A REUSED SALT APART.** Every chain runs its
own `InteropCenter` with its own salt guard (`InteropCenter.sol:128`, `:562-566`), so one sender may
use one salt on two chains. The salt cannot separate those bundles. At the pin, the outer chain-id
word of `abi.encode(block.chainid, B)` did. At v35 that word is gone, and the bundle's own
`sourceChainId` field does it: `_buildInteropBundle` sets it to `block.chainid`
(`InteropCenter.sol:634`), at bytes 64..96 of `B`.

For two sends whose `(chain, sender, salt)` triples differ, where each `B` carries its chain id in
its source slot, the bundle hashes differ unless keccak collides on the two named byte strings or on
the two named packed preimages. A destination needs this form: it keys `bundleStatus` by the hash of
the raw bytes alone (`InteropHandlerBase.sol:231-232`).

The chain-id bounds are the `uint256` width of `block.chainid`. Two chains with one chain id count as
one chain; that chain ids are unique is a registry fact outside this model. -/
def Properties.SendsDistinctBundleHashesAcrossChainsOrKeccakCollisionV35 : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (c c' a a' : ℕ) (s s' B B' : List UInt8),
    c < 256 ^ 32 → c' < 256 ^ 32 →
    a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 →
    bundleSourceSlot B = word c → bundleSourceSlot B' = word c' →
    bundleSaltSlot B = word (keccak (packedSalt a s)).val →
    bundleSaltSlot B' = word (keccak (packedSalt a' s')).val →
    ¬ (c = c' ∧ a = a' ∧ s = s') →
      bundleHashV35 keccak B ≠ bundleHashV35 keccak B'
      ∨ HashCollision keccak B B'
      ∨ HashCollision keccak (packedSalt a s) (packedSalt a' s')

/-- **A RECEIVER THAT FINDS THE SOURCE'S HASH HOLDS THE SOURCE'S BYTES, OR A NAMED COLLISION.** The
center hashes `B = abi.encode(bundle)` (`InteropCenter.sol:691`). The handler
(`InteropHandlerBase.sol:231`) and `claimRefund` (`AtomicFlowManager.sol:252`) hash the raw bytes `x`
they are given, with the same function. So if a receiver's hash equals the source's, then `x = B` or
keccak collides on the named pair `(x, B)`. At the pin this needed the right-injectivity of
`abi.encode(uint256, bytes)` and the receiver's decoded `sourceChainId`; at v35 it needs neither. -/
def Properties.SourceAndDestinationAgreeOrCollisionV35 : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (B x : List UInt8),
    bundleHashV35 keccak x = bundleHashV35 keccak B → x = B ∨ HashCollision keccak x B

/-! ## Relating v35 to the pin -/

/-- **A PIN PREIMAGE DROPS TO THE v35 PREIMAGE.** For bundle bytes whose length is a multiple of 32
(every ABI encoding), the pin's keccak preimage `abi.encode(c, B)` is `B` after its 96-byte prefix
(the chain id, the offset `0x40` and `B`'s length). So the pin's salt slot at bytes 256..288 of the
preimage is the v35 salt slot at bytes 160..192, shifted by 96. -/
def Properties.PinPreimageDropsToV35PreimageV35 : Prop :=
  ∀ (c : ℕ) (B : List UInt8), B.length % 32 = 0 → (pinPreimage c B).drop 96 = B

/-- **ON BYTES THAT CARRY THEIR CHAIN, THE PIN AND v35 SEPARATE THE SAME BUNDLES.** If each byte
string's source slot holds its chain id (as for every bundle the center builds), then the two pin
preimages `abi.encode(c, B)`, `abi.encode(c', B')` are equal exactly when `B = B'`. So the pin's
outer chain-id word was redundant on such bytes, and the pin's preimage-collision disjunct and the
v35 one name collisions on the same pairs of bundles. The pin's route through
`chain_eq_of_abiEncode_eq` is replaced by the source slot. -/
def Properties.PinAndV35PreimagesCoincideOnSourcedBytesV35 : Prop :=
  ∀ (c c' : ℕ) (B B' : List UInt8), c < 256 ^ 32 → c' < 256 ^ 32 →
    bundleSourceSlot B = word c → bundleSourceSlot B' = word c' →
      (pinPreimage c B = pinPreimage c' B' ↔ B = B')

/-! ## Witnesses and countermodels -/

/-- **THE HEADLINE'S PREMISES ARE SATISFIABLE, AND ITS DISJUNCTS ARE NOT TAUTOLOGIES.** Two senders on
chain `324` with the zero user salt. Their bundle bytes are canonical `bundleEncoding` layouts for a
bundle with no calls, whose unbundler is each sender's default `formatEvmV1(324, sender)`. The
bounded injectivity premises hold, neither collision disjunct holds, and the hashes differ. -/
def Properties.SendsDistinctBundleHashesWitnessV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B B' : List UInt8),
    a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
    ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
    ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
    ∧ ¬ (a = a' ∧ s = s')
    ∧ B = bundleEncoding 1 324 325 1 (keccak (packedSalt a s)).val 224 256
        (bundleTailV35 (formatEvmV1 chainRef324 a) 0)
    ∧ B' = bundleEncoding 1 324 325 1 (keccak (packedSalt a' s')).val 224 256
        (bundleTailV35 (formatEvmV1 chainRef324 a') 0)
    ∧ Set.InjOn keccak {B, B'}
    ∧ Set.InjOn keccak {packedSalt a s, packedSalt a' s'}
    ∧ ¬ HashCollision keccak B B'
    ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a' s')
    ∧ bundleHashV35 keccak B ≠ bundleHashV35 keccak B'

/-- **THE CROSS-CHAIN PREMISES ARE SATISFIABLE WITH ONE SENDER AND ONE SALT ON TWO CHAINS.** This is
the case the salt guard cannot separate. The two packed preimages are the same, so the salt disjunct
is false. The bundles (chains `324` and `326`, each with its default unbundler) differ in their
source slot and their unbundler's chain reference. The bytes disjunct is false, and the hashes
differ. -/
def Properties.SendsAcrossChainsWitnessV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (c c' a : ℕ) (s B B' : List UInt8),
    c < 256 ^ 32 ∧ c' < 256 ^ 32 ∧ a < 256 ^ 20 ∧ s.length = 32
    ∧ bundleSourceSlot B = word c ∧ bundleSourceSlot B' = word c'
    ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
    ∧ bundleSaltSlot B' = word (keccak (packedSalt a s)).val
    ∧ c ≠ c'
    ∧ B = bundleEncoding 1 c 325 1 (keccak (packedSalt a s)).val 224 256
        (bundleTailV35 (formatEvmV1 chainRef324 a) 0)
    ∧ B' = bundleEncoding 1 c' 325 1 (keccak (packedSalt a s)).val 224 256
        (bundleTailV35 (formatEvmV1 chainRef326 a) 0)
    ∧ ¬ HashCollision keccak B B'
    ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a s)
    ∧ bundleHashV35 keccak B ≠ bundleHashV35 keccak B'

/-- **THE SALT DISJUNCT CANNOT BE DROPPED.** Under a keccak that collides on the two packed
preimages, two senders with the same explicitly set unbundler build the same bundle bytes. The
hashes are equal, keccak does not collide on the two (equal) byte strings, and only the salt
disjunct holds. -/
def Properties.SaltCollisionDisjunctNeededV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B B' : List UInt8),
    a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
    ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
    ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
    ∧ ¬ (a = a' ∧ s = s')
    ∧ bundleHashV35 keccak B = bundleHashV35 keccak B'
    ∧ ¬ HashCollision keccak B B'
    ∧ HashCollision keccak (packedSalt a s) (packedSalt a' s')

/-- **THE BYTES DISJUNCT CANNOT BE DROPPED.** An instance on one chain satisfying every premise of the
headline, in which the hashes are equal and keccak separates the two packed preimages. Only the
bytes disjunct holds. -/
def Properties.PreimageCollisionDisjunctNeededV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B B' : List UInt8),
    a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
    ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
    ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
    ∧ ¬ (a = a' ∧ s = s')
    ∧ bundleHashV35 keccak B = bundleHashV35 keccak B'
    ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a' s')
    ∧ HashCollision keccak B B'

/-- **ACROSS CHAINS, ONLY A BYTES COLLISION EQUATES A REUSED SALT.** One sender, one salt, two chains:
the salt disjunct is false (one packed preimage), and under a keccak that maps both bundles to one
value only the bytes disjunct holds. -/
def Properties.AcrossChainsPreimageDisjunctNeededV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (c c' a : ℕ) (s B B' : List UInt8),
    c < 256 ^ 32 ∧ c' < 256 ^ 32 ∧ a < 256 ^ 20 ∧ s.length = 32
    ∧ bundleSourceSlot B = word c ∧ bundleSourceSlot B' = word c'
    ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
    ∧ bundleSaltSlot B' = word (keccak (packedSalt a s)).val
    ∧ c ≠ c'
    ∧ bundleHashV35 keccak B = bundleHashV35 keccak B'
    ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a s)
    ∧ HashCollision keccak B B'

/-- **THE RECEIVER'S COLLISION DISJUNCT IS NOT A TAUTOLOGY.** For any two byte strings there is a
keccak that does not collide on them. -/
def Properties.SourceAndDestinationCollisionNotTautologyV35 : Prop :=
  ∀ (B x : List UInt8), ∃ keccak : List UInt8 → UInt256, ¬ HashCollision keccak x B

/-- **…AND IT IS NEEDED.** Under a colliding keccak, bytes other than the source's carry the source's
hash. -/
def Properties.SourceAndDestinationCollisionNeededV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (B x : List UInt8),
    bundleHashV35 keccak x = bundleHashV35 keccak B ∧ x ≠ B

end AttackVectors.BundleHashEncoding.AtV35
