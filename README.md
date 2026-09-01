# era-protocol-specs

Machine-checked specification of ZKsync Era's atomic interop **protocol**, in Lean 4,
depending on Mathlib and nothing else.

No EVM semantics. No compiler output. Every theorem here is about abstract states
and operations, and every one is fully proved — 471 theorems, 0 depending on
anything beyond Lean's three standard axioms, 0 `sorry`, 0 axioms declared.

```bash
lake build                      # ~2 min with a warm Mathlib
./scripts/audit-axioms.sh       # what every theorem actually rests on
./scripts/check-word-fidelity.sh
```

## Why this repo exists separately

`contracts-formal-verification` verifies the **compiled code**: solc-generated Yul,
via Nethermind's Clear framework, over keccak-derived storage slots. That is the
right and hard thing to do, and it is where real bridge bugs live. But it costs a
lot, and it drags in a trusted base — an EVM model, keccak idealization axioms, an
unmodelled `mcopy` — that has nothing to do with whether the protocol's *design* is
sound.

Those are two different questions:

| question | answered by | trusts |
|---|---|---|
| Is the design sound? | **this repo** | Mathlib, Lean kernel |
| Does the deployed code implement that design? | `contracts-formal-verification` | + solc's Yul→EVM backend, Clear's EVM model, keccak idealization |

Splitting them buys three things. The design-level results become readable and
auditable without a 2,700-module corpus or a 30-minute cold build. They survive
era-contracts pin bumps untouched — content-hashed block ids and solc helper
specialization cannot reach them. And, most usefully, **they can state things the
compiled-code proofs structurally cannot** — see `EraSpec/Contracts/Protocol.lean`.

## Layout

```
EraSpec/
  Word.lean            256-bit machine word (vendored from Clear; see its header)
  Core/                the mathematics: Merkle fold, indexed Merkle tree order theory
  Contracts/           one abstract state machine per deployed contract
  Properties/          security theorems and attack countermodels
  Refinement.lean      what the compiled-code proofs must supply, named
```

### `Core/` — inherited mathematics

Extracted from `contracts-formal-verification`, unchanged except for imports.
`Core/IMT.lean` is the indexed-Merkle-tree order theory: the `GapSound`/`KeyInj`
invariants, insert preservation, and the exclusivity theorem the whole refund story
rests on.

### `Contracts/` — the new layer

`Core/` models the tree as a `Finset AbsLeaf`, which erases exactly the parts of
the contract that do the work on chain. `Contracts/` puts them back:

- **`InteropCommitmentTree.lean`** — the indexed state machine: leaf indices,
  `nextIndex` links, the `valueToIndex` map, and the bounded search loop. The
  load-bearing results are `dedup_gate_sound` (the contract's *storage* dedup gate
  implies the *set-level* freshness the order theory assumes — a step nothing
  previously bridged), `insert_projects` (the three-write index manipulation and
  `imtInsert` are the same operation), `insert_preserves_valid`, and
  `run_isGuardedEvolution`, which lifts a real contract run into the history shape
  `Core/IMT` reasons about, so the entire security corpus applies to it.

- **`AtomicFlowManager.lean`** — the per-leg lifecycle
  `Unset → Committed → Revertable → Reverted`. Every refund guarantee falls out of
  one observation: each operation guards on the exact predecessor state, so rank is
  monotone and `Reverted` is absorbing. No-double-refund is then a corollary, as is
  the formal content of the source's "no `nonReentrant` needed" comment.

- **`Protocol.lean`** — the multi-chain composition, **and the reason the split
  earns its keep.** `Core/IMT`'s exclusivity is about one tree and mentions no
  chain id, so a reader of it alone would conclude the multi-chain case was handled.
  It was not. `commitValue = keccak(TAG, flowId, specHash)` contains no chain id:
  membership self-binds (a value is only ever *found* in the tree it was inserted
  into) but **absence does not** — the same number is truthfully absent from every
  other chain's tree. So a delivered leg can be refunded by pointing the gate at an
  unrelated chain, unless `authorizeRefund` compares the proof's `sourceChainId`
  against the leg's declared one.

  `unbound_gate_refunds_delivered_leg` is an explicit two-chain countermodel with
  both trees sound, so it cannot be dismissed as a degenerate state;
  `bound_gate_excludes_delivered` shows the comparison suffices. Together they make
  that one line's necessity a theorem instead of a comment. The concrete repo
  cannot express this — its proofs are per-deployment, and a cross-chain statement
  has nowhere to live there.

### `Properties/` — security theorems

Extracted. Delivered-XOR-reclaimed over arbitrary append-only histories, timeout
soundness, flow canonicity, bundle status machine, recovery limits, and the attack
countermodels (`InsertGuard` shows each insert-guard conjunct is load-bearing, with
concrete states where dropping one breaks an invariant).

## What is NOT here

Deliberately, so the boundary stays legible:

- **Anything about compiled code.** Storage layout, ABI encoding, revert paths, gas.
- **The hash tree.** `Contracts/` carries list state only; `Core/Merkle.lean` has the
  fold, but tying a stored root to these leaves is `#31`/`#32` in the sibling repo.
- **Access control.** Caller identity constrains *who* may step, not what a step
  does; recorded as obligation O5 in `Refinement.lean`.
- **Events, memory copies, external call results.** Not modelled on either side —
  see the "model boundaries" section of `Refinement.lean`.

`Refinement.lean` lists all seven obligations with their current status, including
the ones that are **open**: the compiled search loop is not yet tied to `lowSearch`
(O3), the flow manager's concrete side is blocked upstream by a Clear/generator
mismatch (O4), and the multi-chain binding is source-inspected only (O6 — the one
most worth mechanizing next, since its failure mode is a live double-spend).

## Verification hygiene

Two checkers, both self-tested in the failing direction, because a checker that has
never failed has never been tested:

- **`scripts/audit-axioms.sh`** → `scripts/Audit.lean`. Enumerates the Lean
  *environment*, not source text. An earlier regex version found 327 theorems and
  called them all clean; the environment finds 471 — it was silently missing 144,
  every `private lemma` among them. It also asserts EraSpec declares no axioms.
- **`scripts/check-word-fidelity.sh`**. `Word.lean` is a trimmed copy of Clear's
  `UInt256.lean`; a copy is only worth having while it is still a copy. Diffs all 23
  vendored declarations against the Clear submodule.

Neither a green build nor a `sorry`-free grep is a progress metric. Believe the
audit.

## Provenance and the pending migration

The 26 extracted modules are currently **copies**. `contracts-formal-verification`
still builds against its own `specs/` versions, so the two can drift — and if they
do, that repo's bridge theorems would quietly certify an implementation of an
outdated spec. See [PROVENANCE.md](PROVENANCE.md) for the migration that closes
this and why it has not been done yet.
