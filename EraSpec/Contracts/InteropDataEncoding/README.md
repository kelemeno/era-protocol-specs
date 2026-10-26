# InteropDataEncoding

Source: `contracts/interop/InteropDataEncoding.sol` in the pinned era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| BundleHashEncoding | [Specs/BundleHashEncoding.lean](Specs/BundleHashEncoding.lean) | [Properties/BundleHashEncoding.lean](Properties/BundleHashEncoding.lean) | [Proofs/BundleHashEncoding.lean](Proofs/BundleHashEncoding.lean) |

Hash injectivity is an explicit assumption where used. These proofs do not
establish that solc's emitted memory-copying encoder implements the modeled byte
encoding; the concrete `mcopy` limitation is recorded in `../../Refinement.lean`.
The results support the center, handlers, and manager, which all use bundle hashes.
