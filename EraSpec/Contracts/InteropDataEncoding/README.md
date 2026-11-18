# InteropDataEncoding

Source: `contracts/interop/InteropDataEncoding.sol` in the pinned era-contracts tree.
Topics named `…AtHead` or `…AtV35` are pinned to a later era-contracts commit instead, as
their sections say.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| BundleHashEncoding | [Specs/BundleHashEncoding.lean](Specs/BundleHashEncoding.lean) | [Properties/BundleHashEncoding.lean](Properties/BundleHashEncoding.lean) | [Proofs/BundleHashEncoding.lean](Proofs/BundleHashEncoding.lean) |
| BundleHashPinned | [Specs/BundleHashPinned.lean](Specs/BundleHashPinned.lean) | [Properties/BundleHashPinned.lean](Properties/BundleHashPinned.lean) | [Proofs/BundleHashPinned.lean](Proofs/BundleHashPinned.lean) |
| BundleHashAtV35 | [Specs/BundleHashAtV35.lean](Specs/BundleHashAtV35.lean) | [Properties/BundleHashAtV35.lean](Properties/BundleHashAtV35.lean) | [Proofs/BundleHashAtV35.lean](Proofs/BundleHashAtV35.lean) |

`distinct_sends_distinct_hashes` (BundleHashEncoding) takes global injectivity of
`saltHash` and `bundleHashOf`. That cannot hold at `Hash = UInt256`
(`SaltHashInjUnsatisfiable`; `SaltHashNotInjOnPackedPreimages`, even on the well-formed
`abi.encodePacked(address, bytes32)` preimages; `BundleHashInjUnsatisfiable`), so the
property is vacuous at the deployed hash type. It is kept for comparison.

`BundleHashPinned` (namespace `AttackVectors.BundleHashEncoding`) restates it with no hash
premise. Two sends with distinct `(sender, salt)` pairs get distinct bundle hashes, or
keccak collides on one of two named pairs: the packed salt preimages, or the bundle-hash
preimages `abi.encode(chainId, B)` (`SendsDistinctBundleHashesOrKeccakCollision`). The
content is `DistinctSendsDistinctBundlesOrSaltCollision`: the bundles differ, or the salt
hash collides. `SendsDistinctBundleHashesAcrossChainsOrKeccakCollision` needs only
distinct `(chain, sender, salt)` triples, so it covers one sender reusing a salt on
another chain, where the per-chain salt guard does not apply and `block.chainid` in the
preimage separates the hashes. At the abstract layer:
`DistinctSendsDistinctHashesOrCollision` and the bounded `DistinctSendsDistinctHashesOn`.
- The bundle is its ABI bytes. The only layout fact used is that `interopBundleSalt` sits
  at bytes 160..192 of `abi.encode(bundle)`, checked against the head layout of
  `InteropBundle` (`SaltSlotOfBundleEncoding`, `PreimageCarriesSalt`).
- Witnesses with both collision disjuncts false: `SendsDistinctBundleHashesWitness`,
  `SendsAcrossChainsWitness`, `DistinctSendsDistinctHashesOnSatisfiable`,
  `DistinctSendsCollisionNotTautology`. Countermodels show each disjunct is needed
  (`SaltCollisionDisjunctNeeded`, `BundleCollisionDisjunctNeeded`,
  `SaltCollisionMakesBundlesIdentical`, `PreimageCollisionDisjunctNeeded`).
- The salt guard as a run is not modelled here; the distinctness premise stands for it.
  The run-level form is `../InteropCenter/` topic `Dispatch`.

`BundleHashAtV35` (namespace `AttackVectors.BundleHashEncoding.AtV35`) is the same keccak layer
at `draft/v0.35.0` `b17415d20` (the hashing code is the same at `main` `70096e2`, at shifted
lines). There `encodeInteropBundleHash(_bundle) = keccak256(_bundle)`: the center hashes
`abi.encode(bundle)` and both receivers hash the raw bytes, with no outer chain-id word.
- Distinct `(sender, salt)` pairs give distinct bundle hashes, or keccak collides on the two
  named bundle byte strings or on the two named packed salt preimages
  (`SendsDistinctBundleHashesOrKeccakCollisionV35`, bounded `SendsDistinctBundleHashesOnV35`).
  Across chains, distinct `(chain, sender, salt)` triples suffice when each byte string carries
  its chain id in the `sourceChainId` slot, bytes 64..96
  (`SendsDistinctBundleHashesAcrossChainsOrKeccakCollisionV35`).
- `sendMessageBytesV35` writes out `abi.encode(bundle)` for a `sendMessage` with one direct call
  and the default unbundler, from the ABI specification; `SendMessageBytesMatchAbiEncoderV35`
  checks it against `cast abi-encode` output on three instances. Those bytes carry the chain,
  the sender (the call's `from`) and the user salt in clear, so they determine them with no hash
  premise (`SendMessageBytesDetermineChainSenderSaltV35`), and two such sends get distinct hashes
  unless keccak collides on the two byte strings: no salt disjunct
  (`SendMessagesDistinctBundleHashesOrBytesCollisionV35`, bounded
  `SendMessagesDistinctBundleHashesOnV35`). For general bytes the salt disjunct stays:
  `SaltCollisionDisjunctNeededV35` uses two bundles with no calls.
- Witnesses use `sendMessage` bytes (`SendsDistinctBundleHashesWitnessV35`,
  `SendsAcrossChainsWitnessV35`, `SendMessagesWitnessV35`), and `SendsCollisionNotTautologyV35`
  shows that no two sends force a collision disjunct. Countermodels
  `PreimageCollisionDisjunctNeededV35`, `AcrossChainsPreimageDisjunctNeededV35`.
- Relation to the pin: on bytes that carry their chain id, two pin preimages
  `abi.encode(c, B)` are equal exactly when the bytes are
  (`PinAndV35PreimagesCoincideOnSourcedBytesV35`; `PinSeparatesUnsourcedBytesV35` shows the
  premise is needed).

These proofs do not establish that solc's emitted memory-copying encoder implements the
modeled byte encoding; the concrete `mcopy` limitation is recorded in
`../../Refinement.lean`.
The results support the center, handlers, and manager, which all use bundle hashes.
