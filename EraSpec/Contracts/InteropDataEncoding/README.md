# InteropDataEncoding

## Headline guarantees

About the bundle hash at era-contracts `draft/v0.35.0` head `b17415d20`:
`encodeInteropBundleHash(_bundle) = keccak256(_bundle)` (`interop/InteropDataEncoding.sol:14-16`), which
the center applies to `abi.encode(bundle)` (`InteropCenter.sol:690-692`) and both receivers to the raw
bytes they get (`InteropHandlerBase.sol:231`, `AtomicFlowManager.sol:252`). No headline takes a
premise on keccak; every collision is on two named byte strings.

| Guarantee | Premises | Lean name |
|---|---|---|
| Two sends with distinct `(sender, salt)` pairs get distinct bundle hashes, or keccak collides on the two bundle byte strings, or on the two packed salt preimages `abi.encodePacked(sender, salt)` | the senders fit 160 bits and the user salts are 32 bytes; each byte string's salt slot (bytes 160..192) holds `keccak(abi.encodePacked(sender, salt))`, as `InteropCenter.sol:638` writes it; the two pairs differ (what the salt guard `InteropCenter.sol:562-566` gives two sends on one chain) | `AttackVectors.BundleHashEncoding.AtV35.Properties.SendsDistinctBundleHashesOrKeccakCollisionV35` |
| The same across chains: distinct `(chain, sender, salt)` triples suffice, so one sender reusing a salt on another chain still gets a distinct hash, up to the same two named collisions | as above, plus: the chain ids fit 256 bits and each byte string carries its chain id in its `sourceChainId` slot (bytes 64..96), as `_buildInteropBundle` writes `block.chainid` (`InteropCenter.sol:634`) | `Properties.SendsDistinctBundleHashesAcrossChainsOrKeccakCollisionV35` |
| A receiver's hash equals the source's only for the source's bytes, or keccak collides on the two named byte strings | the two hashes are equal | `Properties.SourceAndDestinationAgreeOrCollisionV35` |
| Two `sendMessage` bundles (one direct call, default unbundler) from distinct `(chain, sender, salt)` triples get distinct hashes unless keccak collides on their two byte strings: no salt disjunct | chain ids fit 256 bits, senders 160 bits, salts are 32 bytes | `Properties.SendMessagesDistinctBundleHashesOrBytesCollisionV35` |

Witnesses (`@[witness]`): `SendsDistinctBundleHashesWitnessV35`, `SendsAcrossChainsWitnessV35`,
`SendMessagesWitnessV35`, `SendsCollisionNotTautologyV35`,
`SourceAndDestinationCollisionNotTautologyV35`. Countermodels (`@[countermodel]`):
`SaltCollisionDisjunctNeededV35`, `PreimageCollisionDisjunctNeededV35`,
`AcrossChainsPreimageDisjunctNeededV35`, `SourceAndDestinationCollisionNeededV35`, and
`SaltCollisionMakesBundlesIdentical` (topic `BundleHashPinned`: under a salt collision two
distinct sends emit the same bytes).

`sendMessageBytesV35` is written from the ABI specification and checked against `cast abi-encode`
output on three instances (`SendMessageBytesMatchAbiEncoderV35`); that is evidence on those
instances, not a proof that solc's encoder emits it.

## Topics

Review `Specs/` for the byte layouts, `Properties/` for the statements and `Proofs/` for the
checked evidence.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| BundleHashAtV35 | [Specs/BundleHashAtV35.lean](Specs/BundleHashAtV35.lean) | [Properties/BundleHashAtV35.lean](Properties/BundleHashAtV35.lean) | [Proofs/BundleHashAtV35.lean](Proofs/BundleHashAtV35.lean) |
| BundleHashPinned | [Specs/BundleHashPinned.lean](Specs/BundleHashPinned.lean) | [Properties/BundleHashPinned.lean](Properties/BundleHashPinned.lean) | [Proofs/BundleHashPinned.lean](Proofs/BundleHashPinned.lean) |
| BundleHashEncoding | [Specs/BundleHashEncoding.lean](Specs/BundleHashEncoding.lean) | [Properties/BundleHashEncoding.lean](Properties/BundleHashEncoding.lean) | [Proofs/BundleHashEncoding.lean](Proofs/BundleHashEncoding.lean) |

- **BundleHashAtV35** (namespace `AttackVectors.BundleHashEncoding.AtV35`) is the contract's topic:
  the headlines above, the byte model of a `sendMessage` bundle, and the slots of
  `abi.encode(bundle)`. Its `Pin…V35` statements relate the old pin's preimage
  `abi.encode(chainId, B)` to the bytes `B` (on bytes that carry their chain id, the two separate the
  same bundles; `PinSeparatesUnsourcedBytesV35` shows the premise is needed).
- **BundleHashPinned** ("pinned" means a collision on two named inputs, not the source pin) holds
  the shared definitions `HashCollision`, `packedSalt`, `bundleEncoding` and `bundleSaltSlot`, the
  layout fact `SaltSlotOfBundleEncoding` (the salt sits at bytes 160..192 of `abi.encode(bundle)`,
  `Messaging.sol:268-276`), and the hash-agnostic form of the uniqueness claim: distinct pairs give
  distinct bundles or a salt-hash collision on the two named packed preimages
  (`DistinctSendsDistinctBundlesOrSaltCollision`), for any bundle-hash function
  (`DistinctSendsDistinctHashesOrCollision`, bounded `DistinctSendsDistinctHashesOn`). Its register
  facts show why the old form could not be used: no map into `bytes32` is injective on the salt
  preimages or on bundles (`SaltHashInjUnsatisfiable`, `SaltHashNotInjOnPackedPreimages`,
  `BundleHashInjUnsatisfiable`).
- **BundleHashEncoding** is the shared ABI byte layer (big-endian words, `pad32`,
  `abi.encode(uint256, bytes)` with its decoder, packed forms); it models the ABI specification,
  not contract code. `distinct_sends_distinct_hashes` there takes global injectivity of both hash
  functions, which cannot hold at `bytes32`, so it is vacuous at the deployed hash type; it is kept
  for comparison.

These proofs do not establish that solc's emitted memory-copying encoder implements the
modelled byte encoding; the concrete `mcopy` limitation is recorded in `../../Refinement.lean`.

## History

`History/` is a record of an older commit, not a claim about `b17415d20`.

- **BundleHashPinned, keccak layer** (`c67894b9`, namespace
  `AttackVectors.BundleHashEncoding.History`): at the old interop pin the bundle hash was
  `keccak256(abi.encode(chainId, abi.encode(bundle)))`. `preimageSaltSlot`, `bundleHashOfBytes` and
  the seven statements over them (`SendsDistinctBundleHashesOrKeccakCollision`,
  `SendsDistinctBundleHashesOn`, `SendsDistinctBundleHashesAcrossChainsOrKeccakCollision`,
  `PreimageCarriesSalt`, their witnesses and `PreimageCollisionDisjunctNeeded`) are there; each has
  a `…V35` counterpart above. [Specs](History/Specs/BundleHashPinned.lean),
  [Properties](History/Properties/BundleHashPinned.lean), [Proofs](History/Proofs/BundleHashPinned.lean).
