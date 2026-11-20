import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned
import EraSpec.Core.Headline

/-!
# Properties: distinct sends give distinct bundle hashes, or a collision on named inputs

Statements about `EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned`. Proofs are in
`EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashPinned`.

None of these takes an injectivity premise on a hash function. The `…On` forms take injectivity on
exactly the two inputs being compared (`Set.InjOn f {x, y}`, which is `¬ HashCollision f x y` by
`Properties.InjOnPairIffNoCollision`). That premise is satisfiable at `UInt256`, as the witnesses
show.

Groups, in order:

* The register facts. The two premises of `distinct_sends_distinct_hashes` cannot hold at
  `Hash = UInt256`.
* The abstract layer, with the original's signature.
* Two byte-level facts about `abi.encode(InteropBundle)`: where its salt sits, and that a salt
  collision lets two sends emit the same bytes.

The keccak layer over the pin's bundle hash `keccak(abi.encode(chainId, B))` is History
(`History/Properties/BundleHashPinned.lean`); its `b17415d20` form is topic `BundleHashAtV35`.

Where the content lies. Given equal bundle hashes, a collision disjunct on the two bundles only
restates that those inputs differ. The content is in the salt
disjunct. Equal bundles force a salt-hash collision on two distinct packed
preimages: the salt is a field of the bundle (a fixed slot of its bytes), and
`abi.encodePacked(address, bytes32)` is injective. `Properties.DistinctSendsDistinctBundlesOrSaltCollision`
states that content on its own.

The countermodels `…DisjunctNeeded` and `SaltCollisionMakesBundlesIdentical` show that neither
disjunct can be dropped.
-/

namespace AttackVectors.BundleHashEncoding

universe u v

/-! ## The register: the original premises cannot hold at `UInt256` -/

/-- **NO SALT HASH INTO `bytes32` IS INJECTIVE.** `distinct_sends_distinct_hashes` assumes
`Function.Injective saltHash` with `saltHash : List UInt8 → Hash`. At `Hash = UInt256` no such map
exists, because `List UInt8` is infinite. So that property is vacuous at the deployed hash type. -/
def Properties.SaltHashInjUnsatisfiable : Prop :=
  ∀ saltHash : List UInt8 → UInt256, ¬ Function.Injective saltHash

/-- **NOT EVEN ON THE WELL-FORMED PREIMAGES.** Injectivity cannot be rescued by restricting it to
the preimages that actually occur, `abi.encodePacked(address, bytes32)` for a 160-bit sender and a
32-byte salt. There are `2^416` of them and only `2^256` hash values. The proof needs only `2^257`
of them: two senders, every salt. So the repair has to name the two compared preimages, as
`HashCollision` does. -/
def Properties.SaltHashNotInjOnPackedPreimages : Prop :=
  ∀ saltHash : List UInt8 → UInt256, ¬ Set.InjOn saltHash packedPreimages

/-- **NO BUNDLE HASH INTO `bytes32` IS INJECTIVE** on a bundle type with infinitely many values.
The deployed `InteropBundle` is such a type: its `calls` array and each call's `data` are dynamic. So
`distinct_sends_distinct_hashes`'s other premise, `hbundle_inj`, cannot hold either. -/
def Properties.BundleHashInjUnsatisfiable : Prop :=
  ∀ (Bundle : Type u) [Infinite Bundle] (bundleHashOf : Bundle → UInt256),
    ¬ Function.Injective bundleHashOf

/-- **INJECTIVITY ON TWO NAMED INPUTS IS THE ABSENCE OF A COLLISION ON THEM.** This links the `…On`
forms to the `…OrCollision` forms below. -/
def Properties.InjOnPairIffNoCollision : Prop :=
  ∀ {α : Type u} {β : Type v} (f : α → β) (x y : α), Set.InjOn f {x, y} ↔ ¬ HashCollision f x y

/-! ## The abstract layer: the original's signature, with no injectivity premise -/

/-- **DISTINCT SENDS GIVE DISTINCT BUNDLES, OR THE SALT HASH COLLIDES ON THE TWO NAMED PREIMAGES.**
This is the content of the repair, and it involves no bundle hash. If the two bundles were equal,
their salt fields would be equal. Then `saltHash` would agree on `packedSalt a s` and
`packedSalt a' s'`, and these differ: the packed encoding is injective (`packed_addr_salt_inj`) and
the pairs differ.

Premises: the EVM width bounds for an address and a `bytes32`; each bundle's salt field is the salt
hash of its own sender and salt (`InteropCenter.sol:638` at `b17415d20`); and the two `(sender, salt)`
pairs differ, which is what the salt guard at `InteropCenter.sol:562-566` provides for two sends. -/
def Properties.DistinctSendsDistinctBundlesOrSaltCollision : Prop :=
  ∀ {Bundle : Type u} {Hash : Type v} (saltHash : List UInt8 → Hash) (saltField : Bundle → Hash)
    (a a' : ℕ) (s s' : List UInt8) (b b' : Bundle),
    a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 →
    saltField b = saltHash (packedSalt a s) →
    saltField b' = saltHash (packedSalt a' s') →
    ¬ (a = a' ∧ s = s') →
      b ≠ b' ∨ HashCollision saltHash (packedSalt a s) (packedSalt a' s')

/-- **DISTINCT SENDS, DISTINCT BUNDLE HASHES, OR A NAMED COLLISION.** This is the pinned form of
`distinct_sends_distinct_hashes`, with the same functions and premises except for its two global
injectivity premises, which are dropped. The two bundle hashes differ, or `bundleHashOf` collides
on the two named bundles `b`, `b'`, or `saltHash` collides on the two named packed preimages.

When both functions are injective the two collision disjuncts are false, so this implies the
original. -/
def Properties.DistinctSendsDistinctHashesOrCollision : Prop :=
  ∀ {Bundle : Type u} {Hash : Type v}
    (saltHash : List UInt8 → Hash) (bundleHashOf : Bundle → Hash) (saltField : Bundle → Hash)
    (a a' : ℕ) (s s' : List UInt8) (b b' : Bundle),
    a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 →
    saltField b = saltHash (packedSalt a s) →
    saltField b' = saltHash (packedSalt a' s') →
    ¬ (a = a' ∧ s = s') →
      bundleHashOf b ≠ bundleHashOf b'
      ∨ HashCollision bundleHashOf b b'
      ∨ HashCollision saltHash (packedSalt a s) (packedSalt a' s')

/-- **DISTINCT SENDS, DISTINCT BUNDLE HASHES, BOUNDED.** This is `distinct_sends_distinct_hashes`
with each global injectivity premise replaced by injectivity on the two values compared: `saltHash`
on the two packed preimages, and `bundleHashOf` on the two bundles. -/
def Properties.DistinctSendsDistinctHashesOn : Prop :=
  ∀ {Bundle : Type u} {Hash : Type v}
    (saltHash : List UInt8 → Hash) (bundleHashOf : Bundle → Hash) (saltField : Bundle → Hash)
    (a a' : ℕ) (s s' : List UInt8) (b b' : Bundle),
    a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 →
    saltField b = saltHash (packedSalt a s) →
    saltField b' = saltHash (packedSalt a' s') →
    ¬ (a = a' ∧ s = s') →
    Set.InjOn saltHash {packedSalt a s, packedSalt a' s'} →
    Set.InjOn bundleHashOf {b, b'} →
      bundleHashOf b ≠ bundleHashOf b'

/-- **THE ABSTRACT PREMISES ARE SATISFIABLE AT `bytes32`, AND THE DISJUNCTS ARE NOT TAUTOLOGIES.**
One instance with `Hash = UInt256` satisfies every premise of the three properties above, including
both bounded injectivity premises. On it, neither collision disjunct holds and the hashes differ.

The instance is the `b17415d20` composition with a stand-in for keccak:

* a bundle is its ABI bytes;
* `bundleHashOf` is that stand-in applied to the bytes, as `encodeInteropBundleHash` applies keccak
  at `b17415d20` (`InteropDataEncoding.sol:14-16`);
* `saltField` reads the salt slot.

Sender 1 and sender 2 both use the zero salt. -/
def Properties.DistinctSendsDistinctHashesOnSatisfiable : Prop :=
  ∃ (saltHash : List UInt8 → UInt256) (bundleHashOf saltField : List UInt8 → UInt256)
    (a a' : ℕ) (s s' : List UInt8) (b b' : List UInt8),
    a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
    ∧ saltField b = saltHash (packedSalt a s) ∧ saltField b' = saltHash (packedSalt a' s')
    ∧ ¬ (a = a' ∧ s = s')
    ∧ Set.InjOn saltHash {packedSalt a s, packedSalt a' s'} ∧ Set.InjOn bundleHashOf {b, b'}
    ∧ ¬ HashCollision bundleHashOf b b'
    ∧ ¬ HashCollision saltHash (packedSalt a s) (packedSalt a' s')
    ∧ bundleHashOf b ≠ bundleHashOf b'

/-- **NO CHOICE OF SENDS FORCES A COLLISION DISJUNCT.** For every two well-formed sends with distinct
`(sender, salt)` pairs, there is an instance at `Hash = UInt256` with bundles carrying the right
salts on which both collision disjuncts are false. So only the hash functions can make a disjunct
true, never the sends themselves. -/
def Properties.DistinctSendsCollisionNotTautology : Prop :=
  ∀ (a a' : ℕ) (s s' : List UInt8),
    a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 → ¬ (a = a' ∧ s = s') →
    ∃ (saltHash : List UInt8 → UInt256) (bundleHashOf saltField : List UInt8 → UInt256)
      (b b' : List UInt8),
      saltField b = saltHash (packedSalt a s) ∧ saltField b' = saltHash (packedSalt a' s')
      ∧ ¬ HashCollision bundleHashOf b b'
      ∧ ¬ HashCollision saltHash (packedSalt a s) (packedSalt a' s')

/-- **THE SALT DISJUNCT CANNOT BE DROPPED.** There is an instance at `Hash = UInt256` satisfying
every premise in which the bundle hashes are equal and `bundleHashOf` does not collide on the two
bundles, because they are the same bundle. So only the salt-collision disjunct holds, and without
it the statement is false. -/
def Properties.SaltCollisionDisjunctNeeded : Prop :=
  ∃ (saltHash : List UInt8 → UInt256) (bundleHashOf saltField : List UInt8 → UInt256)
    (a a' : ℕ) (s s' : List UInt8) (b b' : List UInt8),
    a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
    ∧ saltField b = saltHash (packedSalt a s) ∧ saltField b' = saltHash (packedSalt a' s')
    ∧ ¬ (a = a' ∧ s = s')
    ∧ bundleHashOf b = bundleHashOf b'
    ∧ ¬ HashCollision bundleHashOf b b'

/-- **THE BUNDLE DISJUNCT CANNOT BE DROPPED.** There is an instance at `Hash = UInt256` satisfying
every premise in which the bundle hashes are equal and `saltHash` does not collide on the two packed
preimages. So only the bundle-collision disjunct holds. -/
def Properties.BundleCollisionDisjunctNeeded : Prop :=
  ∃ (saltHash : List UInt8 → UInt256) (bundleHashOf saltField : List UInt8 → UInt256)
    (a a' : ℕ) (s s' : List UInt8) (b b' : List UInt8),
    a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
    ∧ saltField b = saltHash (packedSalt a s) ∧ saltField b' = saltHash (packedSalt a' s')
    ∧ ¬ (a = a' ∧ s = s')
    ∧ bundleHashOf b = bundleHashOf b'
    ∧ ¬ HashCollision saltHash (packedSalt a s) (packedSalt a' s')

/-! ## The bundle bytes -/

/-- **THE SALT SLOT IS WHERE `abi.encode` PUTS `interopBundleSalt`.** Whatever the other fields and
the dynamic tail are, the salt slot of an `InteropBundle` encoding laid out as `bundleEncoding`
reads back the salt word. This checks the offset 160 in `bundleSaltSlot` against the head layout. -/
def Properties.SaltSlotOfBundleEncoding : Prop :=
  ∀ (version : UInt8) (sourceChainId destinationChainId baseTokenAssetId salt callsOffset
      attributesOffset : ℕ) (tail : List UInt8),
    bundleSaltSlot (bundleEncoding version sourceChainId destinationChainId baseTokenAssetId salt
      callsOffset attributesOffset tail) = word salt

/-- **UNDER A SALT COLLISION, TWO DISTINCT SENDS CAN EMIT THE SAME BUNDLE BYTES.** There is a keccak,
two sends with distinct `(sender, salt)` pairs, and one byte string `B` whose salt slot meets the
premise of both sends. Taking `B` as the bundle bytes of both sends, any hash of the bytes (at
`b17415d20`, `keccak(B)`) gives them one bundle hash, and a collision disjunct on the two byte strings
is false. So the salt disjunct of `SendsDistinctBundleHashesOrKeccakCollisionV35` (topic
`BundleHashAtV35`) cannot be dropped, and it describes a real failure: the destination cannot tell
the two bundles apart. (In the proof, `B` is a
`bundleEncoding` layout.) -/
@[countermodel] def Properties.SaltCollisionMakesBundlesIdentical : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B : List UInt8),
    a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
    ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
    ∧ bundleSaltSlot B = word (keccak (packedSalt a' s')).val
    ∧ ¬ (a = a' ∧ s = s')
    ∧ HashCollision keccak (packedSalt a s) (packedSalt a' s')

end AttackVectors.BundleHashEncoding
