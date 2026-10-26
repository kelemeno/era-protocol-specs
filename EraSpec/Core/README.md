# Shared foundations

Core contains only foundations with no corresponding Solidity contract or library.
A contract/library model belongs under `../Contracts/<SolidityName>/`, even when
it is pure mathematics, EVM-free, or shared by many callers.

- `Word.lean`: the vendored 256-bit word type and arithmetic. `uint256` is a
  language primitive, not a separate Solidity contract/library. The fidelity
  checker compares the retained declarations with the local
  `scripts/word-baseline.json`; no older checkout is required. Historical source
  comparison is optional and does not prove correctness.
- `FinBits.lean`: generic word/bit/index arithmetic used by contract proofs.
- `PreparedApplication.lean`: generic preparation, interference, readiness, and
  intended-effect obligations for applications; no matching Solidity implementation.
- `Simulation.lean`: generic forward-simulation composition and reachable-state
  safety transfer, with explicit related initial states. It supplies no concrete
  VM, Solidity, or compiler instance and does not establish progress.

See the [assumption layers](../../ASSUMPTIONS.md) for the distinction between
logical axioms, theorem premises, model boundaries, and concrete correspondence.

Indexed-Merkle list/order theory is in `../Contracts/IndexedMerkleTree/Specs/Model.lean`.
The tree/root model is in `../Contracts/FullMerkle/Specs/Model.lean`, and verification
soundness is in `../Contracts/Merkle/Properties/ProofSound.lean`.
