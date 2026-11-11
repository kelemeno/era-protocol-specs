# InteropDataEncoding

Source: `contracts/interop/InteropDataEncoding.sol` in the pinned era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| BundleHashEncoding | [Specs/BundleHashEncoding.lean](Specs/BundleHashEncoding.lean) | [Properties/BundleHashEncoding.lean](Properties/BundleHashEncoding.lean) | [Proofs/BundleHashEncoding.lean](Proofs/BundleHashEncoding.lean) |
| BundleHashPinned | [Specs/BundleHashPinned.lean](Specs/BundleHashPinned.lean) | [Properties/BundleHashPinned.lean](Properties/BundleHashPinned.lean) | [Proofs/BundleHashPinned.lean](Proofs/BundleHashPinned.lean) |

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

These proofs do not establish that solc's emitted memory-copying encoder implements the
modeled byte encoding; the concrete `mcopy` limitation is recorded in
`../../Refinement.lean`.
The results support the center, handlers, and manager, which all use bundle hashes.
