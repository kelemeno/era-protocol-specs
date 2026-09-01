# Provenance, and the migration that is not done yet

## What was extracted

26 modules came out of `contracts-formal-verification` unchanged except for their
`import` lines. They were selected mechanically, not by taste: a transitive
classification of that repo's `specs/` tree found exactly these to be reachable
without importing `generated.*` (solc output) or any `Clear.*` module other than
`Clear.UInt256`. Of ~2,700 spec modules, these 26 are the Clear-free subset.

| new module | came from |
|---|---|
| `EraSpec/Core/FinBits.lean` | `specs/FinBits.lean` |
| `EraSpec/Core/Merkle.lean` | `specs/MerkleSpec.lean` |
| `EraSpec/Core/MerkleProofSound.lean` | `specs/MerkleProofSound.lean` |
| `EraSpec/Core/MerkleCachedInj.lean` | `specs/MerkleCachedInj.lean` |
| `EraSpec/Core/IMT.lean` | `specs/IMTAbstract.lean` |
| `EraSpec/Properties/*.lean` (21) | `specs/AttackVectors/*.lean` |

Namespaces were left alone (`IMTAbstract`, `AttackVectors.*`), so only module paths
changed. That keeps the eventual migration a one-line-per-file edit.

`EraSpec/Word.lean` is a separate case: a **trimmed copy** of
`Clear/Clear/UInt256.lean`, keeping the word type and its arithmetic and dropping
the EVM opcodes and byte serialization. It is vendored rather than imported so this
package stays Clear-free. `scripts/check-word-fidelity.sh` diffs the 23 kept
declarations against the Clear submodule and fails on any divergence.

Newly written here, not extracted: `EraSpec/Contracts/*` and
`EraSpec/Refinement.lean`.

## The drift hazard — read this before relying on either repo

**Right now the 26 modules exist twice.** `contracts-formal-verification` still
builds against its own `specs/` copies; nothing connects them to these.

That is the dangerous state, and it is worth being precise about why. The value of
that repo over a pencil-and-paper spec is the *mechanized seam* between the abstract
operations and the compiled code — results `#40`–`#42`, which carry the
`GapSound`/`KeyInj`/`RepKeyInj` invariants through the real storage writes. Those
theorems are stated in terms of `IMTAbstract`. If this copy of `IMTAbstract` and
that one drift, the bridge keeps building and keeps being a theorem — but about a
*different* specification than the one anyone is reading here. Nothing in either
repo's checkers would notice: both builds stay green, both audits stay clean.

So the copies are a temporary state, not a design.

## The migration

1. Add to `contracts-formal-verification/lakefile.lean`:

   ```lean
   require «era-protocol-specs» from git
     "<url>" @ "<rev>"
   ```

2. Rewrite the imports in that repo (26 modules plus their dependents):
   `specs.IMTAbstract` → `EraSpec.Core.IMT`, `specs.MerkleSpec` →
   `EraSpec.Core.Merkle`, `specs.AttackVectors.X` → `EraSpec.Properties.X`.
   Namespaces are unchanged, so `open IMTAbstract` and every use site still
   resolve.

3. Delete the 26 files from `specs/`.

4. Rebuild and re-run that repo's checkers — `audit-count.sh` above all. The axiom
   profiles must be identical before and after; a change means an import rewrite
   picked up something different.

5. Update `Specs.lean` and `AttackVectors/Audit.lean` so nothing becomes an orphan
   (`orphan-specs.sh` catches files nothing imports, which are outside the reach of
   every other check).

After that, "contracts-formal-verification builds against era-protocol-specs @ rev
X" becomes the machine-checked fidelity statement, and drift becomes a build
failure instead of a silent divergence.

### Why it was not done in the same pass

It touches a 2,700-module corpus that takes a long cold build, and step 4 is the
part that matters: the migration is only correct if the axiom profiles come out
unchanged, and that has to be *measured*, not assumed. Doing it as a separate,
verifiable change keeps this extraction reviewable on its own.

Until it is done, treat `contracts-formal-verification/specs/IMTAbstract.lean` and
`EraSpec/Core/IMT.lean` as one file that happens to be stored twice, and edit only
the copy here.

## Pinned versions

* Lean `v4.9.1`, Mathlib `09d33efc68d3ad52db77b731d7253675395a14aa` — the same
  revisions `contracts-formal-verification` pins, so it can take this as a
  dependency without a toolchain conflict.
* The extraction was taken from era-contracts at
  `c67894b970a0dac6fe9144d8ebf4b0806e15a9af` (that repo's submodule pin at the
  time), and the contract specs in `EraSpec/Contracts/` were written against the
  Solidity at that commit: `contracts/common/libraries/IndexedMerkleTree.sol`,
  `contracts/atomic-interop/{L2InteropCommitmentTree,AtomicFlowManager}.sol`, and
  `contracts/atomic-interop/libraries/AtomicInteropProof.sol`.

  Unlike the compiled-code proofs, nothing here breaks when that pin moves — but
  the contract specs can become *stale* rather than wrong, which is harder to
  notice. When the pin moves, re-read those five files against
  `EraSpec/Contracts/` and check that the guards still transcribe.
