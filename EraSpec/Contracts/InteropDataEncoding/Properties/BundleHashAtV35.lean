import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashAtV35
import EraSpec.Core.Headline

/-!
# Properties at draft/v0.35.0: distinct sends give distinct bundle hashes, or a named collision

Statements about `EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashAtV35` (era-contracts
`draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`). Proofs are in
`EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashAtV35`. Names end in `V35`; the pin's
statements (`Properties/BundleHashPinned.lean`) are untouched and still describe the pin.

None of these takes an injectivity premise on a hash function. The `…On` forms take injectivity on
exactly the two compared inputs, which is `¬ HashCollision` on them
(`Properties.InjOnPairIffNoCollision`, pin topic `BundleHashPinned`).

What changed from the pin, and what did not:

* The register (`SaltHashInjUnsatisfiable`, `SaltHashNotInjOnPackedPreimages`,
  `BundleHashInjUnsatisfiable`) and the abstract layer (`DistinctSendsDistinctHashesOrCollision`,
  `DistinctSendsDistinctBundlesOrSaltCollision`, `DistinctSendsDistinctHashesOn`) quantify over
  arbitrary hash functions, so they cover v35's `bundleHashOf := keccak ∘ abi.encode` as stated.
* The keccak layer changes. The keccak preimage of the bundle hash is now the bundle bytes `B`
  themselves, so the preimage-collision disjunct names `(B, B')` instead of
  `(abi.encode(c, B), abi.encode(c', B'))`. Across chains, the separating word is `B`'s own
  `sourceChainId` slot (bytes 64..96) instead of the pin's outer chain-id word, which no longer
  exists.
* New here: for the bytes of two `sendMessage` bundles, the salt-collision disjunct is not needed.
  Those bytes carry the source chain, the sender (the call's `from`) and the user salt in clear, so
  distinct `(chain, sender, salt)` triples give distinct byte strings with no hash premise at all
  (`SendMessageBytesDetermineChainSenderSaltV35`), and the hashes differ unless keccak collides on
  the two byte strings (`SendMessagesDistinctBundleHashesOrBytesCollisionV35`). For general bytes the
  salt disjunct stays (`SaltCollisionDisjunctNeededV35`, with two bundles that have no calls).
* `PinAndV35PreimagesCoincideOnSourcedBytesV35` relates the versions: on bytes whose source slot
  holds the chain id (every bundle the center builds, `InteropCenter.sol:634`), two pin preimages are
  equal exactly when the two v35 preimages are.
-/

namespace AttackVectors.BundleHashEncoding.AtV35

open AttackVectors.BundleHashEncoding

/-! ## Layout: what the v35 keccak preimage carries -/

/-- **THE v35 PREIMAGE CARRIES THE SOURCE, THE DESTINATION AND THE SALT.** At v35 the bundle hash's
keccak preimage is the bundle bytes. In any `InteropBundle` encoding laid out as `bundleEncoding`,
whatever the other fields and the dynamic tail, the source chain id is at bytes 64..96, the
destination at 96..128, and the salt at 160..192. This checks the offsets of `bundleSourceSlotV35`,
`bundleDestSlotV35` and `bundleSaltSlot` against the head layout of `Messaging.sol:268-276`. -/
def Properties.PreimageCarriesSourceDestinationSaltV35 : Prop :=
  ∀ (version : UInt8) (sourceChainId destinationChainId baseTokenAssetId salt callsOffset
      attributesOffset : ℕ) (tail : List UInt8),
    bundleSourceSlotV35 (bundleEncoding version sourceChainId destinationChainId baseTokenAssetId
        salt callsOffset attributesOffset tail) = word sourceChainId
    ∧ bundleDestSlotV35 (bundleEncoding version sourceChainId destinationChainId baseTokenAssetId salt
        callsOffset attributesOffset tail) = word destinationChainId
    ∧ bundleSaltSlot (bundleEncoding version sourceChainId destinationChainId baseTokenAssetId salt
        callsOffset attributesOffset tail) = word salt

/-- **THE CHAIN REFERENCE IS THE CHAIN ID'S MINIMAL BIG-ENDIAN BYTES.** This checks the transcription
`toChainReferenceV35` of `_toChainReference` (`vendor/draft-InteroperableAddress.sol:215-221`): for a
chain id below `2^256` its bytes read back as the chain id, there are at most 32 of them, and for a
nonzero chain id the value is at least `256 ^ (length - 1)`, so no shorter big-endian string holds
it. For the witnesses' chain ids it gives `0x0144` (`324`) and `0x0146` (`326`). -/
def Properties.ToChainReferenceMinimalBytesV35 : Prop :=
  (∀ c : ℕ, c < 256 ^ 32 →
      fromBytesBE (toChainReferenceV35 c) = c
      ∧ (toChainReferenceV35 c).length ≤ 32
      ∧ (c ≠ 0 → 256 ^ ((toChainReferenceV35 c).length - 1) ≤ c))
  ∧ toChainReferenceV35 324 = [0x01, 0x44]
  ∧ toChainReferenceV35 326 = [0x01, 0x46]

/-- **A `sendMessage` BUNDLE'S BYTES MEET THE HEADLINES' SLOT PREMISES.** For a 32-byte user salt
`s`, the bytes `sendMessageBytesV35` carry the source chain `c` in the source slot, the destination
`d` in the destination slot and the salt word `keccak(abi.encodePacked(a, s))` in the salt slot, and
their length is a multiple of 32 (the premise of `PinPreimageDropsToV35PreimageV35`). This ties the
concrete `sendMessage` layout to the slot premises of the statements below. -/
def Properties.SendMessageBytesSlotsV35 : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (c d base a recipient value : ℕ) (s payload : List UInt8),
    s.length = 32 →
      bundleSourceSlotV35 (sendMessageBytesV35 keccak c d base a recipient value s payload) = word c
      ∧ bundleDestSlotV35 (sendMessageBytesV35 keccak c d base a recipient value s payload) = word d
      ∧ bundleSaltSlot (sendMessageBytesV35 keccak c d base a recipient value s payload)
          = word (keccak (packedSalt a s)).val
      ∧ (sendMessageBytesV35 keccak c d base a recipient value s payload).length % 32 = 0

/-- **THE BYTE MODELS AGREE WITH AN INDEPENDENT ABI ENCODER ON THREE INSTANCES.** Each right-hand
side is the output of Foundry's `cast abi-encode` for the type
`f((bytes1,uint256,uint256,bytes32,bytes32,(bytes1,bool,address,address,uint256,bytes)[],(bytes,bytes,bool,bytes32)))`,
the `InteropBundle` tuple (`Messaging.sol:224-276`), split into 32-byte words. The values encoded are:

* the witnesses' bundle: version `0x01`, source `324`, destination `325`, base-token asset id `1`,
  salt word `7`, one call `(0x01, false, 0x1234, 1, 0, 0xdeadbeef)`, attributes
  `(0x, formatEvmV1(324, 1), false, 0)`;
* the same with no call and unbundler `formatEvmV1(324, 7)` (`noCallBytesV35`);
* source `70000` (a 3-byte chain reference), base `5`, salt word `9`, sender `0xabcdef`, value `77`, a
  33-byte payload `0x0102…21` (two padded words) and user salt `3`.

Lean checks the equalities; the word lists are that tool's output, copied in. So on these instances
the layouts of `sendMessageBytesV35`, `noCallBytesV35`, `formatEvmV1V35` and `toChainReferenceV35`
are those of `abi.encode` as that encoder computes it. -/
def Properties.SendMessageBytesMatchAbiEncoderV35 : Prop :=
  sendMessageBytesV35 (fun _ => 7) 324 325 1 1 0x1234 0 (word 0) [0xde, 0xad, 0xbe, 0xef]
      = [0x20, 0x100000000000000000000000000000000000000000000000000000000000000, 0x144, 0x145,
          0x1, 0x7, 0xe0, 0x220, 0x1, 0x20,
          0x100000000000000000000000000000000000000000000000000000000000000, 0x0, 0x1234, 0x1,
          0x0, 0xc0, 0x4, 0xdeadbeef00000000000000000000000000000000000000000000000000000000,
          0x80, 0xa0, 0x0, 0x0, 0x0, 0x1c,
          0x1000002014414000000000000000000000000000000000000000100000000].flatMap word
  ∧ noCallBytesV35 (fun _ => 7) 324 325 1 1 (word 0) (formatEvmV1V35 324 7)
      = [0x20, 0x100000000000000000000000000000000000000000000000000000000000000, 0x144, 0x145,
          0x1, 0x7, 0xe0, 0x100, 0x0, 0x80, 0xa0, 0x0, 0x0, 0x0, 0x1c,
          0x1000002014414000000000000000000000000000000000000000700000000].flatMap word
  ∧ sendMessageBytesV35 (fun _ => 9) 70000 325 5 0xabcdef 0x1234 77 (word 3)
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
          26, 27, 28, 29, 30, 31, 32, 33]
      = [0x20, 0x100000000000000000000000000000000000000000000000000000000000000, 0x11170, 0x145,
          0x5, 0x9, 0xe0, 0x240, 0x1, 0x20,
          0x100000000000000000000000000000000000000000000000000000000000000, 0x0, 0x1234,
          0xabcdef, 0x4d, 0xc0, 0x21,
          0x102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20,
          0x2100000000000000000000000000000000000000000000000000000000000000, 0x80, 0xa0, 0x0, 0x3,
          0x0, 0x1d, 0x1000003011170140000000000000000000000000000000000abcdef000000].flatMap word

/-! ## The keccak layer at v35, for any bytes with the stated slots -/

/-- **HEADLINE: DISTINCT SENDS, DISTINCT BUNDLE HASHES, OR A KECCAK COLLISION ON NAMED BYTES.**

Each send is given by a sender `a`, a user salt `s` and bundle bytes `B` whose salt slot holds the
word `keccak(abi.encodePacked(a, s))` (`InteropCenter.sol:638`, laid out by `abi.encode(_bundle)` at
`:691`). The v35 bundle hashes `keccak(B)` (`InteropDataEncoding.sol:14-16`) of two sends with
distinct `(sender, salt)` pairs differ, unless one of these holds:

* keccak collides on the two bundle byte strings `B`, `B'`;
* keccak collides on the two packed salt preimages `packedSalt a s`, `packedSalt a' s'`.

No chain id appears, so the two sends may be on one chain or on two. On one chain the premise
`¬ (a = a' ∧ s = s')` is what the salt guard (`InteropCenter.sol:562-566`) provides for two sends;
across chains it is a premise about the two sends, and
`SendsDistinctBundleHashesAcrossChainsOrKeccakCollisionV35` weakens it. Nothing is assumed about
`keccak`, and `B` is any byte string with that slot. -/
@[headline] def Properties.SendsDistinctBundleHashesOrKeccakCollisionV35 : Prop :=
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
@[headline] def Properties.SendsDistinctBundleHashesAcrossChainsOrKeccakCollisionV35 : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (c c' a a' : ℕ) (s s' B B' : List UInt8),
    c < 256 ^ 32 → c' < 256 ^ 32 →
    a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 →
    bundleSourceSlotV35 B = word c → bundleSourceSlotV35 B' = word c' →
    bundleSaltSlot B = word (keccak (packedSalt a s)).val →
    bundleSaltSlot B' = word (keccak (packedSalt a' s')).val →
    ¬ (c = c' ∧ a = a' ∧ s = s') →
      bundleHashV35 keccak B ≠ bundleHashV35 keccak B'
      ∨ HashCollision keccak B B'
      ∨ HashCollision keccak (packedSalt a s) (packedSalt a' s')

/-- **A RECEIVER'S HASH EQUALS THE SOURCE'S ONLY FOR THE SOURCE'S BYTES, OR A NAMED COLLISION.** The
center hashes `B = abi.encode(bundle)` (`InteropCenter.sol:691`); the handler
(`InteropHandlerBase.sol:231`) and `claimRefund` (`AtomicFlowManager.sol:252`) hash the raw bytes `x`
they are given. If a receiver's hash equals the source's, then `x = B` or keccak collides on the
named pair `(x, B)`.

The proof is a case split on `x = B`, with no derived content. What the statement records is the
modelling fact that the center and both receivers apply the one function `bundleHashV35` to the
bytes, with no decoded field in the comparison. At the pin the receivers hashed
`abi.encode(decoded sourceChainId, x)` and the center `abi.encode(block.chainid, B)`: relating the
two needs `abiEncode_right_inj` (`InteropCenter/Proofs/Dispatch.lean`), and the collision is then
on the two `abi.encode` preimages. -/
@[headline] def Properties.SourceAndDestinationAgreeOrCollisionV35 : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (B x : List UInt8),
    bundleHashV35 keccak x = bundleHashV35 keccak B → x = B ∨ HashCollision keccak x B

/-! ## `sendMessage` bundles: the bytes alone separate distinct sends -/

/-- **A `sendMessage` BUNDLE'S BYTES DETERMINE ITS CHAIN, SENDER AND SALT.** If the
`sendMessageBytesV35` bytes of two sends are equal, the two sends have the same source chain, the
same sender and the same user salt, whatever their destinations, base-token asset ids, recipients,
values and payloads, and whatever `keccak` is. No hash premise: the source slot holds the chain id,
the call's `from` word holds the sender (`InteropCenter.sol:829`), and the attributes hold the user
salt itself (`Messaging.sol:228`), which `abi.encode` writes in clear. The proof does not use the
salt word `keccak(abi.encodePacked(a, s))`.

The bounds are the widths of `uint256`, `address` and `bytes32`. -/
def Properties.SendMessageBytesDetermineChainSenderSaltV35 : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (c c' d d' base base' a a' recipient recipient' value value' : ℕ)
    (s s' payload payload' : List UInt8),
    c < 256 ^ 32 → c' < 256 ^ 32 → a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 →
    sendMessageBytesV35 keccak c d base a recipient value s payload
      = sendMessageBytesV35 keccak c' d' base' a' recipient' value' s' payload' →
      c = c' ∧ a = a' ∧ s = s'

/-- **TWO `sendMessage` BUNDLES: DISTINCT HASHES, OR A COLLISION ON THE TWO BYTE STRINGS.** For the
bytes of two `sendMessage` bundles from distinct `(chain, sender, salt)` triples, on one chain or two,
the v35 bundle hashes differ unless keccak collides on the two named byte strings. Unlike the general
headline, there is no salt-collision disjunct: by
`SendMessageBytesDetermineChainSenderSaltV35`, the two byte strings already differ. -/
@[headline] def Properties.SendMessagesDistinctBundleHashesOrBytesCollisionV35 : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (c c' d d' base base' a a' recipient recipient' value value' : ℕ)
    (s s' payload payload' : List UInt8),
    c < 256 ^ 32 → c' < 256 ^ 32 → a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 →
    ¬ (c = c' ∧ a = a' ∧ s = s') →
      bundleHashV35 keccak (sendMessageBytesV35 keccak c d base a recipient value s payload)
        ≠ bundleHashV35 keccak (sendMessageBytesV35 keccak c' d' base' a' recipient' value' s' payload')
      ∨ HashCollision keccak (sendMessageBytesV35 keccak c d base a recipient value s payload)
          (sendMessageBytesV35 keccak c' d' base' a' recipient' value' s' payload')

/-- **TWO `sendMessage` BUNDLES, BOUNDED.** The previous statement with its one collision disjunct
turned into a premise: keccak is injective on the two named byte strings. -/
def Properties.SendMessagesDistinctBundleHashesOnV35 : Prop :=
  ∀ (keccak : List UInt8 → UInt256) (c c' d d' base base' a a' recipient recipient' value value' : ℕ)
    (s s' payload payload' : List UInt8),
    c < 256 ^ 32 → c' < 256 ^ 32 → a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 →
    ¬ (c = c' ∧ a = a' ∧ s = s') →
    Set.InjOn keccak {sendMessageBytesV35 keccak c d base a recipient value s payload,
      sendMessageBytesV35 keccak c' d' base' a' recipient' value' s' payload'} →
      bundleHashV35 keccak (sendMessageBytesV35 keccak c d base a recipient value s payload)
        ≠ bundleHashV35 keccak (sendMessageBytesV35 keccak c' d' base' a' recipient' value' s' payload')

/-! ## Relating v35 to the pin -/

/-- **A PIN PREIMAGE DROPS TO THE v35 PREIMAGE.** For bundle bytes whose length is a multiple of 32
(ABI encodings are word-aligned; for `sendMessage` bytes this is part of `SendMessageBytesSlotsV35`),
the pin's keccak preimage `abi.encode(c, B)` is `B` after its 96-byte prefix (the chain id, the
offset `0x40` and `B`'s length). So the pin's salt slot at bytes 256..288 of the preimage is the v35
salt slot at bytes 160..192, shifted by 96. -/
def Properties.PinPreimageDropsToV35PreimageV35 : Prop :=
  ∀ (c : ℕ) (B : List UInt8), B.length % 32 = 0 → (pinPreimageV35 c B).drop 96 = B

/-- **ON BYTES THAT CARRY THEIR CHAIN, THE PIN AND v35 SEPARATE THE SAME BUNDLES.** If each byte
string's source slot holds its chain id (as for every bundle the center builds), then the two pin
preimages `abi.encode(c, B)`, `abi.encode(c', B')` are equal exactly when `B = B'`. So on such bytes
the pin's outer chain-id word separates no two bundles that the bytes do not already separate, and
the preimage-collision disjuncts of the pin and of v35 both require `B ≠ B'` (they are collisions of
keccak on different inputs). The forward direction (equal pin preimages give `B = B'`) holds for
all bytes; only the reverse one (from `B = B'` to equal pin preimages, which needs `c = c'`) uses
the source-slot premise.
`PinSeparatesUnsourcedBytesV35` shows the source-slot premise is needed. -/
def Properties.PinAndV35PreimagesCoincideOnSourcedBytesV35 : Prop :=
  ∀ (c c' : ℕ) (B B' : List UInt8), c < 256 ^ 32 → c' < 256 ^ 32 →
    bundleSourceSlotV35 B = word c → bundleSourceSlotV35 B' = word c' →
      (pinPreimageV35 c B = pinPreimageV35 c' B' ↔ B = B')

/-! ## Witnesses and countermodels

The instances use senders `1` and `2` with the zero user salt (`word 0`), on chain `324`, and chain
`326` for the cross-chain cases. Unless stated otherwise the bundle bytes are `sendMessageBytesV35`:
destination `325`, base-token asset id `1`, one direct call to recipient `0x1234` with value `0` and
the 4-byte payload `0xdeadbeef`, and the sender's default unbundler. -/

/-- **THE HEADLINE'S PREMISES ARE SATISFIABLE, AND ITS DISJUNCTS ARE NOT TAUTOLOGIES.** Two senders
on chain `324` with the zero user salt, each sending one message. Their bundle bytes are the
`sendMessage` bytes. The bounded injectivity premises hold, neither collision disjunct holds, and
the hashes differ. -/
@[witness] def Properties.SendsDistinctBundleHashesWitnessV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B B' : List UInt8),
    a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
    ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
    ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
    ∧ ¬ (a = a' ∧ s = s')
    ∧ B = sendMessageBytesV35 keccak 324 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef]
    ∧ B' = sendMessageBytesV35 keccak 324 325 1 a' 0x1234 0 s' [0xde, 0xad, 0xbe, 0xef]
    ∧ Set.InjOn keccak {B, B'}
    ∧ Set.InjOn keccak {packedSalt a s, packedSalt a' s'}
    ∧ ¬ HashCollision keccak B B'
    ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a' s')
    ∧ bundleHashV35 keccak B ≠ bundleHashV35 keccak B'

/-- **THE CROSS-CHAIN PREMISES ARE SATISFIABLE WITH ONE SENDER AND ONE SALT ON TWO CHAINS.** This is
the case the salt guard cannot separate. The two packed preimages are the same, so the salt disjunct
is false. The two `sendMessage` bundles (chains `324` and `326`) differ in their source slot and in
the chain reference of their default unbundler. The bytes disjunct is false, and the hashes differ. -/
@[witness] def Properties.SendsAcrossChainsWitnessV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (c c' a : ℕ) (s B B' : List UInt8),
    c < 256 ^ 32 ∧ c' < 256 ^ 32 ∧ a < 256 ^ 20 ∧ s.length = 32
    ∧ bundleSourceSlotV35 B = word c ∧ bundleSourceSlotV35 B' = word c'
    ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
    ∧ bundleSaltSlot B' = word (keccak (packedSalt a s)).val
    ∧ c ≠ c'
    ∧ B = sendMessageBytesV35 keccak c 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef]
    ∧ B' = sendMessageBytesV35 keccak c' 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef]
    ∧ ¬ HashCollision keccak B B'
    ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a s)
    ∧ bundleHashV35 keccak B ≠ bundleHashV35 keccak B'

/-- **THE `sendMessage` STATEMENTS' PREMISES ARE SATISFIABLE, WITH THE DISJUNCT FALSE.** Two senders
on chain `324` with the zero user salt: every premise of `SendMessagesDistinctBundleHashesOnV35` holds
(including injectivity on the two byte strings), the bytes disjunct is false, and the hashes
differ. -/
@[witness] def Properties.SendMessagesWitnessV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (c a a' : ℕ) (s s' : List UInt8),
    c < 256 ^ 32 ∧ a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
    ∧ ¬ (c = c ∧ a = a' ∧ s = s')
    ∧ Set.InjOn keccak {sendMessageBytesV35 keccak c 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef],
        sendMessageBytesV35 keccak c 325 1 a' 0x1234 0 s' [0xde, 0xad, 0xbe, 0xef]}
    ∧ ¬ HashCollision keccak (sendMessageBytesV35 keccak c 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef])
        (sendMessageBytesV35 keccak c 325 1 a' 0x1234 0 s' [0xde, 0xad, 0xbe, 0xef])
    ∧ bundleHashV35 keccak (sendMessageBytesV35 keccak c 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef])
      ≠ bundleHashV35 keccak (sendMessageBytesV35 keccak c 325 1 a' 0x1234 0 s' [0xde, 0xad, 0xbe, 0xef])

/-- **NO TWO SENDS FORCE A COLLISION DISJUNCT.** For every two well-formed sends, on any chains, with
distinct `(chain, sender, salt)` triples, there is a keccak under which neither collision disjunct of
`SendsDistinctBundleHashesAcrossChainsOrKeccakCollisionV35` holds for their `sendMessage` bytes
(fixed destination, recipient, value and payload as above). So only the hash function can make a
disjunct true, never the choice of sends. -/
@[witness] def Properties.SendsCollisionNotTautologyV35 : Prop :=
  ∀ (c c' a a' : ℕ) (s s' : List UInt8),
    c < 256 ^ 32 → c' < 256 ^ 32 → a < 256 ^ 20 → a' < 256 ^ 20 → s.length = 32 → s'.length = 32 →
    ¬ (c = c' ∧ a = a' ∧ s = s') →
    ∃ keccak : List UInt8 → UInt256,
      ¬ HashCollision keccak
          (sendMessageBytesV35 keccak c 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef])
          (sendMessageBytesV35 keccak c' 325 1 a' 0x1234 0 s' [0xde, 0xad, 0xbe, 0xef])
      ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a' s')

/-- **THE SALT DISJUNCT CANNOT BE DROPPED FROM THE GENERAL HEADLINE.** Under a keccak that maps every
input to `0`, two senders whose bundles have no calls and the same explicitly set unbundler build the
same bytes (`noCallBytesV35`): the sender enters them only through the salt word. The hashes are
equal, keccak does not collide on the two (equal) byte strings, and only the salt disjunct holds. For
`sendMessage` bytes this cannot happen, since their call carries the sender in `from`
(`SendMessageBytesDetermineChainSenderSaltV35`). -/
@[countermodel] def Properties.SaltCollisionDisjunctNeededV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B B' : List UInt8),
    a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
    ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
    ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
    ∧ ¬ (a = a' ∧ s = s')
    ∧ B = noCallBytesV35 keccak 324 325 1 a s (formatEvmV1V35 324 7)
    ∧ B' = noCallBytesV35 keccak 324 325 1 a' s' (formatEvmV1V35 324 7)
    ∧ bundleHashV35 keccak B = bundleHashV35 keccak B'
    ∧ ¬ HashCollision keccak B B'
    ∧ HashCollision keccak (packedSalt a s) (packedSalt a' s')

/-- **THE BYTES DISJUNCT CANNOT BE DROPPED.** Two senders on chain `324`, each sending one message,
satisfying every premise of the headline (and, with both on chain `324`, those of
`SendMessagesDistinctBundleHashesOrBytesCollisionV35`), under a keccak that separates the two packed
preimages and maps both byte strings to one value. The hashes are equal and only the bytes disjunct
holds. -/
@[countermodel] def Properties.PreimageCollisionDisjunctNeededV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (a a' : ℕ) (s s' B B' : List UInt8),
    a < 256 ^ 20 ∧ a' < 256 ^ 20 ∧ s.length = 32 ∧ s'.length = 32
    ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
    ∧ bundleSaltSlot B' = word (keccak (packedSalt a' s')).val
    ∧ ¬ (a = a' ∧ s = s')
    ∧ B = sendMessageBytesV35 keccak 324 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef]
    ∧ B' = sendMessageBytesV35 keccak 324 325 1 a' 0x1234 0 s' [0xde, 0xad, 0xbe, 0xef]
    ∧ bundleHashV35 keccak B = bundleHashV35 keccak B'
    ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a' s')
    ∧ HashCollision keccak B B'

/-- **ACROSS CHAINS, ONLY A BYTES COLLISION EQUATES A REUSED SALT.** One sender, one salt, two chains
(`324`, `326`), each sending one message: the salt disjunct is false (one packed preimage), and under
a keccak that maps both byte strings to one value only the bytes disjunct holds. -/
@[countermodel] def Properties.AcrossChainsPreimageDisjunctNeededV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (c c' a : ℕ) (s B B' : List UInt8),
    c < 256 ^ 32 ∧ c' < 256 ^ 32 ∧ a < 256 ^ 20 ∧ s.length = 32
    ∧ bundleSourceSlotV35 B = word c ∧ bundleSourceSlotV35 B' = word c'
    ∧ bundleSaltSlot B = word (keccak (packedSalt a s)).val
    ∧ bundleSaltSlot B' = word (keccak (packedSalt a s)).val
    ∧ c ≠ c'
    ∧ B = sendMessageBytesV35 keccak c 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef]
    ∧ B' = sendMessageBytesV35 keccak c' 325 1 a 0x1234 0 s [0xde, 0xad, 0xbe, 0xef]
    ∧ bundleHashV35 keccak B = bundleHashV35 keccak B'
    ∧ ¬ HashCollision keccak (packedSalt a s) (packedSalt a s)
    ∧ HashCollision keccak B B'

/-- **THE RECEIVER'S COLLISION DISJUNCT IS NOT A TAUTOLOGY.** For any two byte strings there is a
keccak that does not collide on them. -/
@[witness] def Properties.SourceAndDestinationCollisionNotTautologyV35 : Prop :=
  ∀ (B x : List UInt8), ∃ keccak : List UInt8 → UInt256, ¬ HashCollision keccak x B

/-- **…AND IT IS NEEDED.** Under a keccak that maps every bundle byte string to one value, the
`sendMessage` bytes of a second sender carry the hash of the first sender's bytes, and differ from
them. -/
@[countermodel] def Properties.SourceAndDestinationCollisionNeededV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (B x : List UInt8),
    B = sendMessageBytesV35 keccak 324 325 1 1 0x1234 0 (word 0) [0xde, 0xad, 0xbe, 0xef]
    ∧ x = sendMessageBytesV35 keccak 324 325 1 2 0x1234 0 (word 0) [0xde, 0xad, 0xbe, 0xef]
    ∧ bundleHashV35 keccak x = bundleHashV35 keccak B ∧ x ≠ B

/-- **THE PIN RELATION'S PREMISES ARE SATISFIABLE ACROSS CHAINS.** The `sendMessage` bytes of one
sender on chains `324` and `326` have lengths that are multiples of 32 and carry their chain ids in
their source slots. Their pin preimages differ, and so do the bytes. -/
def Properties.PinRelationWitnessV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (c c' : ℕ) (B B' : List UInt8),
    c < 256 ^ 32 ∧ c' < 256 ^ 32 ∧ c ≠ c'
    ∧ B = sendMessageBytesV35 keccak c 325 1 1 0x1234 0 (word 0) [0xde, 0xad, 0xbe, 0xef]
    ∧ B' = sendMessageBytesV35 keccak c' 325 1 1 0x1234 0 (word 0) [0xde, 0xad, 0xbe, 0xef]
    ∧ B.length % 32 = 0 ∧ B'.length % 32 = 0
    ∧ bundleSourceSlotV35 B = word c ∧ bundleSourceSlotV35 B' = word c'
    ∧ pinPreimageV35 c B ≠ pinPreimageV35 c' B' ∧ B ≠ B'

/-- **WITHOUT THE SOURCE-SLOT PREMISE, THE PIN SEPARATES WHAT v35 DOES NOT.** One byte string `B`
(the `sendMessage` bytes from chain `324`), paired with the chain ids `324` and `326`: the v35
preimages are the same `B`, while the pin preimages `abi.encode(324, B)` and `abi.encode(326, B)`
differ, and `B`'s source slot does not hold `326`. So the source-slot premise of
`PinAndV35PreimagesCoincideOnSourcedBytesV35` cannot be dropped. At v35 no hash pairs bytes with a
separate chain id, so this only marks where the two hash definitions differ. -/
def Properties.PinSeparatesUnsourcedBytesV35 : Prop :=
  ∃ (keccak : List UInt8 → UInt256) (c c' : ℕ) (B : List UInt8),
    c < 256 ^ 32 ∧ c' < 256 ^ 32 ∧ c ≠ c'
    ∧ B = sendMessageBytesV35 keccak c 325 1 1 0x1234 0 (word 0) [0xde, 0xad, 0xbe, 0xef]
    ∧ bundleSourceSlotV35 B ≠ word c'
    ∧ pinPreimageV35 c B ≠ pinPreimageV35 c' B

end AttackVectors.BundleHashEncoding.AtV35
