# era-protocol-specs

Lean 4 specifications and proofs for ZKsync contracts and their cross-chain
protocols, depending on Mathlib and nothing else. The first comprehensive
verification scope is **asset bridging**; the existing checked developments
primarily cover atomic interop abstractions and a reference bridge application.

No EVM semantics. No compiler output. The theorems here concern abstract states
and operations. The environment audit checks every theorem for dependencies beyond
Lean's three standard axioms and rejects `sorry` or declared project axioms.
That audit does not eliminate theorem premises or modeling assumptions. The
[assumption register](ASSUMPTIONS.md) separates VM, Solidity, compiler/artifact,
contract representation, dependency, and operational boundaries, and maps the
current bridge claims to them. It also explains how checked safety refinements
can compose without claiming a concrete VM/compiler proof.

Start with the [asset bridging verification plan](ASSET_BRIDGING_VERIFICATION_PLAN.md)
for scope, main guarantees, contract responsibilities, proof order, and completion
criteria. [REVIEW.md](REVIEW.md) records the earlier atomicity/preparation review
and first application proofs. The reference bridge is not a verified transcription
of the deployed asset router or token vault.
See [PROVENANCE.md](PROVENANCE.md) for the origin of copied material and
[REUSE.md](REUSE.md) for historical reference material and open implementation
correspondence work.

```bash
lake build                      # ~2 min with a warm Mathlib
./scripts/audit-axioms.sh       # what every theorem actually rests on
./scripts/check-word-fidelity.sh
```

## Why this repo exists separately

This repository is an independent Mathlib-only development. Its abstract theorems
concern the models defined here. They do not establish that deployed Solidity
implements those models; source-level correspondence remains a separate open
obligation.

The 26 historically copied modules are owned locally and build here without
importing the older repository or its compiled proofs. The older repository is a
historical reference only; it is not a dependency or evidence of implementation
correspondence.

## Layout and manual review

Every modeled Solidity contract/library has three real Lean module folders:

```text
EraSpec/
  Contracts/
    AtomicFlowManager/
      Specs/          Model.lean, FlowCanonical.lean, RecoveryLimits.lean
      Properties/     Model.lean, FlowCanonical.lean, RecoveryLimits.lean
      Proofs/         Model.lean, FlowCanonical.lean, RecoveryLimits.lean
      README.md
    AtomicInteropProof/       Specs/, Properties/, Proofs/
    BridgedStandardERC20/      Specs/, Properties/, Proofs/
    FullMerkle/               Specs/, Properties/, Proofs/
    IndexedMerkleTree/        Specs/, Properties/, Proofs/
    InteropDataEncoding/      Specs/, Properties/, Proofs/
    InteropHandlerBase/       Specs/, Properties/, Proofs/
    L2InteropCommitmentTree/   Specs/, Properties/, Proofs/
    L2InteropHandler/         Specs/, Properties/, Proofs/
    Merkle/                  Specs/, Properties/, Proofs/
    NativeTokenVaultBase/     Specs/, Properties/, Proofs/
  Core/                      words, arithmetic, preparation, safety simulation
  Protocol/                  cross-contract and multi-chain composition
  Examples/BurnMintBridge/   illustrative model and conditional composition
  Refinement.lean            compiled-code implementation obligations
```

1. **Review `Specs/`** against the intended behavior and Solidity: state, operation
   definitions, guards, inputs, and permitted transitions. These modules import
   other specifications and shared foundations, not the security proofs.
2. **Review `Properties/`** for the exact guarantees and their assumptions.
   Each target is a named transparent proposition (`abbrev Properties.<name>`),
   without a proof body. Helpers and negative countermodels have statements too.
3. **Consult `Proofs/`** for the checked derivations. Each public theorem references
   its authoritative proposition in `Properties/`; it does not restate a second
   independently editable conclusion. Private helper lemmas remain with the proof.
4. **Review implementation correspondence** in `Refinement.lean`. Correct abstract
   statements and proofs do not by themselves verify the deployed contracts.
   Use [ASSUMPTIONS.md](ASSUMPTIONS.md) to distinguish proved component laws from
   trust and remaining correspondence work.

Start with [AtomicFlowManager's review table](EraSpec/Contracts/AtomicFlowManager/README.md),
then [L2InteropCommitmentTree](EraSpec/Contracts/L2InteropCommitmentTree/README.md)
and its [IndexedMerkleTree library](EraSpec/Contracts/IndexedMerkleTree/README.md).
The initial bridged-token model is in
[BridgedStandardERC20/Specs/Model.lean](EraSpec/Contracts/BridgedStandardERC20/Specs/Model.lean),
with its property and proof modules alongside it. Continue with
[NativeTokenVaultBase preparation](EraSpec/Contracts/NativeTokenVaultBase/README.md)
and the [preparation trace](EraSpec/Protocol/AssetBridgePreparation/README.md),
which accounts for multiple in-flight transfers and interleaved spending.
For the initialization base case, review
[token initialization](EraSpec/Contracts/BridgedStandardERC20/Properties/Initialization.lean),
[vault registration](EraSpec/Contracts/NativeTokenVaultBase/Properties/Initialization.lean),
and the [initialization-to-preparation statement](EraSpec/Protocol/AssetBridgePreparation/Properties/Initialization.lean).
The vault's ledger invariant and representation consistency are named separately;
the new registration proof establishes them rather than assuming agreement.

Proofs can be authored with assistant/tactic support and are checked by Lean.
This directory structure does not introduce an automatic Solidity-to-security-proof
pipeline. The package entry point imports all proofs, and the environment audit
rejects properties whose named theorem is missing, proves only a special case,
or does not reference the property statement.

The proposed [Lean-to-Solidity generation route](CODE_GENERATION.md) describes
restricted executable contract definitions, preservation proofs, and one shared
test suite plus differential sequences for existing/generated Solidity. There is
no generator or second Solidity implementation in this package yet.

### What belongs in Core

`Core/` contains only foundations without a corresponding Solidity contract or
library: vendored words, generic bit/arithmetic lemmas, and the application
preparation interface. Sharing a module between contracts does not make it Core
material. Generic safety-simulation composition also belongs here; it has no
Solidity owner or concrete VM semantics. The IMT theory is in
`Contracts/IndexedMerkleTree/Specs/Model.lean`;
the Merkle tree model is in `Contracts/FullMerkle/Specs/Model.lean`.

### Cross-contract results and reference examples

`Protocol/` retains the cross-contract no-theft, flow, destination, and multi-chain
composition results. The wrong-chain absence countermodel and positive bound-gate
result remain in `Protocol/Spec.lean`. These files are outside the per-contract
three-folder split. The new `Protocol/AssetBridgePreparation/` topic uses the
same `Specs/`, `Properties/`, `Proofs/` review split as contracts.

`Examples/BurnMintBridge/` remains visibly illustrative: it does not specify the
actual asset router or vault. Its full recovery behavior is stronger than the
manager's best-effort recovery. Intended real-contract properties and open gaps
are tracked in [REVIEW.md](REVIEW.md); no placeholder proofs are created for
contracts that have not been modeled.

## What is NOT here

Deliberately, so the boundary stays legible:

- **Implementation correspondence.** Storage layout, ABI and memory bytes, revert
  paths, and external-call behavior remain open obligations.
- **Stored-root correspondence.** The commitment-tree model carries list state;
  `Contracts/FullMerkle/Specs/Model.lean` supplies the abstract hash-tree fold. Tying
  actual stored roots to those leaves remains an implementation correspondence
  obligation.
- **Full source access-control correspondence.** The token model includes explicit
  caller/vault guards; several earlier interop models omit callers. Relating all
  these paths to actual source callers remains obligation O5.
- **Concrete events, memory copies, and external-call results.** Their
  correspondence must be addressed for claims that depend on them.

`Refinement.lean` records local, open source-correspondence obligations O1–O7.
They include tree state and updates, insertion guards, bounded search, flow-manager
transitions, caller authority, cross-chain source binding, and Merkle-root
correspondence. It also records the open source correspondence for the initial
nonlegacy `BridgedStandardERC20` model, including uint256 arithmetic, authority,
and call semantics.

## Verification hygiene

Two checkers, both self-tested in the failing direction, because a checker that has
never failed has never been tested:

- **`scripts/audit-axioms.sh`** → `scripts/Audit.lean`. Enumerates the Lean
  *environment*, not source text. An earlier regex version found 327 theorems and
  called them all clean; the environment found 471 at that point — it was silently missing 144,
  every `private lemma` among them. It also asserts EraSpec declares no axioms and checks that every separated
  property has a named theorem proving its full universally quantified statement.
- **`scripts/check-word-fidelity.sh`** checks the local word declarations against
  `scripts/word-baseline.json`. It needs no older checkout. Changes to word
  definitions require review and a deliberate baseline update; the fingerprint
  check does not prove their mathematical correctness. An explicit source-file
  argument enables an optional historical provenance comparison.

The environment audit checks logical dependencies and full named-property proof
coverage. It does not check model adequacy, assumption discharge, or deployed-code
correspondence; use the assumption register and manual specification review for
those boundaries.

## Provenance

Twenty-six modules were selectively copied from an older formal-verification
repository and are maintained locally. See [PROVENANCE.md](PROVENANCE.md). Their
historical origin does not supply a link to deployed Solidity; see
[REUSE.md](REUSE.md) for the separate, open correspondence obligation.
