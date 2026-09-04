# era-protocol-specs

Machine-checked specification of ZKsync Era's atomic interop **protocol**, in Lean 4,
depending on Mathlib and nothing else.

No EVM semantics. No compiler output. Every theorem here is about abstract states
and operations, and every one is fully proved — 637 theorems, 0 depending on
anything beyond Lean's three standard axioms, 0 `sorry`, 0 axioms declared. The
guarantees themselves are catalogued as 60 named properties, 59 proved and 1 open.

```bash
lake build                      # ~2 min with a warm Mathlib
./scripts/check-properties.sh   # every stated property: PROVED (by which theorem) or OPEN
./scripts/audit-axioms.sh       # what every theorem actually rests on
./scripts/check-word-fidelity.sh
```

## How to review this without reading proofs

The package is split into three layers, one folder each, with the same four files
in every folder:

```
EraSpec/
  Contracts/     MODEL       — state, guards, operations. Definitions only.
  Properties/    STATEMENTS  — one `def … : Prop` per guarantee. No proofs.
  Proofs/        PROOFS      — the proofs, plus one certificate theorem per property.
    ├─ InteropCommitmentTree   the indexed Merkle tree contract
    ├─ AtomicFlowManager       the per-leg refund state machine
    ├─ Protocol                the multi-chain composition
    ├─ TreeRoot                the hash-tree root and the two proof verifiers
    └─ Atomicity               the flow gate: partial atomicity, none-or-all
```

A review is two readings and one script:

1. **Read `Contracts/` against the Solidity.** Is `InsertGuard` the guard `insert`
   enforces? Is `NonInclusionAccepted` what `verifyNonInclusion` returns `true` on?
   These files contain nothing but transcribed definitions, so a mismatch is
   visible on the page.
2. **Read `Properties/`.** Each declaration is a `Prop` with a docstring saying what
   it means in protocol terms. Does `ProofsExclusive` say what you want "no double
   spend at the root" to mean? Nothing in these files is trusted either — a
   mis-stated property is caught by reading it.
3. **Run `./scripts/check-properties.sh`.** It lists every property and the theorem
   that certifies it. A *certificate* is a theorem whose type is *exactly* the
   property constant, e.g.

   ```lean
   theorem Proofs.TreeRoot.ProofsExclusive : Properties.TreeRoot.ProofsExclusive := @proofs_exclusive
   ```

   so the kernel, not a reviewer, checks that the proof proves the statement as
   written. `./scripts/audit-axioms.sh` then confirms no theorem rests on `sorry`
   or a declared axiom.

Nobody has to read `Proofs/`. `OPEN` properties are statements written down before
being proved; they carry no `sorry` and the checker keeps the list honest.
`EraSpec/Properties.lean` is the catalogue, with the open items and the roadmap
of properties that still need a model extension before they can be stated.

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
era-contracts pin bumps untouched. And they can state things the compiled-code
proofs structurally cannot — cross-chain statements (`Protocol`), and statements
about what the verifier accepts for *any* index and path length (`TreeRoot`).

## What is proved, by file

### `InteropCommitmentTree` — the indexed Merkle tree

`Core/IMT.lean` models the tree as a `Finset AbsLeaf`, which erases exactly the
parts of the contract that do the work on chain: leaf indices, `nextIndex` links,
the `valueToIndex` map, and the bounded search loop. The model puts them back and
the properties discharge them into the `Finset` layer. The load-bearing ones:
`DedupGateSound` (the contract's *storage* dedup gate implies the *set-level*
freshness the order theory assumes — a step nothing previously bridged),
`InsertProjects` (the three-write index manipulation and `imtInsert` are the same
operation), `SearchYieldsGuard` (the actual `insert` flow — three reverts, then the
walk from the caller's hint — establishes the guard), and
`RunIsGuardedEvolution`, which lifts a real contract run into the history shape
`Core/IMT` reasons about, so the entire security corpus applies to it. The headline
is `GenesisRunReclaimableIffAbsent`: at every step of every run from `setup`, a
value is reclaimable exactly when it was never delivered.

### `AtomicFlowManager` — the per-leg lifecycle

`Unset → Committed → Revertable → Reverted`. Every refund guarantee falls out of one
observation: each operation guards on the exact predecessor state, so rank is
monotone and `Reverted` is absorbing. `NoDoubleClaim` is a corollary, as is
`ClaimClosesGateBeforeInteraction`, the formal content of the source's
"no `nonReentrant` needed" comment.

### `Protocol` — the multi-chain composition

`Core/IMT`'s exclusivity is about one tree and mentions no chain id, so a reader of
it alone would conclude the multi-chain case was handled. It was not.
`commitValue = keccak(TAG, flowId, specHash)` contains no chain id: membership
self-binds (a value is only ever *found* in the tree it was inserted into) but
**absence does not** — the same number is truthfully absent from every other
chain's tree. So a delivered leg can be refunded by pointing the gate at an
unrelated chain, unless `authorizeRefund` compares the proof's `sourceChainId`
against the leg's declared one. `UnboundGateRefundsDeliveredLeg` is an explicit
two-chain countermodel with both trees sound; `ChainsNoDoubleSpend` shows the
comparison suffices for real per-chain deployments.

### `TreeRoot` — the hash side

The root `FullMerkle` publishes over the list state, and the verifiers
`verifyInclusion` / `verifyNonInclusion` exactly as they consume an
attacker-supplied proof. The verifier is a pure function of a 32-byte root: it
checks neither that the index is occupied nor that the path is as long as the tree
is high, because it cannot know either. `AcceptedPathPinsLeaf` handles both — for
*any* index and path length the prover chose, an accepted path names an occupied
index whose stored leaf is the presented one. So `NonInclusionSound` lands a
witness `W ∈ toAbs T`, the hypothesis `IMTAbstract.forged_padding_witness_breaks_exclusivity`
proves cannot be dropped, and `ProofsExclusive` is delivered-XOR-refundable as the
deployed verifiers see it. `RootAfterInsert` fixes what "the root after `insert`"
means (the `pushNewLeaf` walk over the post-`updateLeaf` list), which is the
list-level target the compiled-code correspondence must hit.

The hypotheses are bundled in `HashAssumptions`, and one of them is **false at the
extraction pin**: `padNotLeaf`, that the padding constant is not a leaf hash. The
pinned `setup` pads with `hashLeaf({0,0,0})`, so an empty slot verifies as the
`{0,0,0}` leaf, whose window `(0, ∞)` excludes nothing.
`PaddingCollisionRefundsDeliveredLeg` runs the real contract (`setup`, two guarded
inserts, three leaves at height 2) and exhibits an accepted non-inclusion proof
for the delivered value — with no hash assumption at all, because the proof is
honest. Later era-contracts revisions pad with a dedicated `IMT_EMPTY_LEAF_HASH`;
this theorem is what that constant buys.

### `Atomicity` — partial atomicity (none-or-all)

The property: **if any leg of a flow is executed, every leg of that flow can be
finalized** — provided the source chains' data is available. Equivalently, either
all legs are finalizable or none executes. Never one leg delivered and a sibling
stranded.

`AttackVectors.FlowAtomicity` proves the set-level version and then records that
"whatever forces same-outcome (if anything) must live in the higher-level
bundle/executor logic, not in the commitment tree". It does, and this is it:
`requireFlowFinalized` loops over **every** leg and demands an inclusion proof for
each before the executing bundle runs. So mixed *tree states* are reachable — that
countermodel stands — but a mixed *outcome* is not, because in such a state no leg
executes at all.

The model adds what `TreeRoot` does not carry: a tree per chain **per batch** (a
batch applies any number of `append`s, hence `Reaches` rather than one `insert`), a
settlement timestamp per batch, and `Access` — what a prover can actually present.
That last one is where data availability enters. The verifier is a pure function
and will accept any well-formed proof, but someone has to *build* it, and that
needs the leaf preimage and the sibling path. `DataAvailable` is that assumption,
named rather than hidden.

The argument is four steps: the gate is over all legs (definitional, and the thing
to check against the Solidity), an accepted proof means real membership
(`FinalitySignalMeansMembership`), membership is permanent because the tree is
append-only across batches (`FinalitySignalPersists`), and a member plus DA yields
a presentable accepted proof (`MemberIsFinalizable`). `ExecutedExcludesAnyRefund`
is the other half: once any leg executes, no leg of the flow can pass the timeout
gate on either branch — a late batch comes after every on-time one, and so does the
last on-time batch.

Both hypotheses are load-bearing, each with a countermodel.
`SelfOnlyGateAdmitsMixedOutcome` builds a well-formed two-chain system in which a
gate checking only the executing leg lets one leg execute while its sibling is
refundable; `FullGateBlocksMixedOutcome` shows the real gate refuses in that same
state. `WithoutDaCommittedLegIsStuck` shows that without DA a committed leg is
neither finalizable (no proof is presentable) nor refundable (it really is in the
tree), so the failure mode there is stranded funds rather than a double spend — and
it is not a contract defect, which is why DA is an assumption and not an obligation.

### `Core/` — the mathematics

Extracted from `contracts-formal-verification`, unchanged except for imports:
`IMT.lean` (the `GapSound`/`KeyInj` order theory and the exclusivity theorem the
whole refund story rests on), `Merkle.lean` (the `FullMerkle` fold, M-A–M-D),
`MerkleProofSound.lean`, `MerkleCachedInj.lean`, `FinBits.lean`. One module is new:
`MerkleVerifier.lean` removes `MerkleProofSound`'s two range hypotheses — occupied
index, path length equal to the height — so that an accepted path pins the level-0
entry at *any* index, padding included, and the path length is forced to be the
tree's height under domain separation.

### `AttackVectors/` — the extracted security corpus

21 files, extracted verbatim: delivered-XOR-reclaimed over arbitrary append-only
histories, timeout soundness, flow canonicity, bundle status machine, recovery
limits, and the attack countermodels. These predate the three-layer split and mix
statements with proofs; they stay as they are until the migration in
[PROVENANCE.md](PROVENANCE.md) is done, after which splitting them is its own change.

## What is NOT here

Deliberately, so the boundary stays legible:

- **Anything about compiled code.** Storage layout, ABI encoding, revert paths, gas.
- **The compiled hash-tree writes.** That `FullMerkle.updateLeaf`/`pushNewLeaf`
  compute the root `TreeRoot` defines is `#31`/`#32` in the sibling repo (O7).
- **Access control.** Caller identity constrains *who* may step, not what a step
  does; recorded as obligation O5 in `Refinement.lean`.
- **Events, memory copies, external call results.** Not modelled on either side —
  see the "model boundaries" section of `Refinement.lean`.

`Refinement.lean` lists all seven obligations with their current status, including
the ones that are **open**: the compiled search loop is not yet tied to `lowSearch`
(O3), the flow manager's concrete side is blocked upstream by a Clear/generator
mismatch (O4), and the multi-chain binding is source-inspected only (O6).

## Verification hygiene

Three checkers, each reading the Lean *environment* rather than source text, and
each self-tested in the failing direction, because a checker that has never failed
has never been tested:

- **`scripts/check-properties.sh`** → `scripts/Properties.lean`. Every
  `Prop`-valued `def` under `EraSpec.Properties` is a stated property; every
  theorem whose type is exactly that constant is its certificate. Prints `PROVED`
  or `OPEN` per property. Failing direction: a planted `def Bogus : Prop := False`
  shows as `OPEN`.
- **`scripts/audit-axioms.sh`** → `scripts/Audit.lean`. Enumerates every theorem and
  the axioms it depends on. An earlier regex version found 327 theorems and called
  them all clean; the environment found 471 (637 now) — it was silently missing
  144, every `private lemma` among them. It also asserts EraSpec declares no axioms.
- **`scripts/check-word-fidelity.sh`**. `Word.lean` is a trimmed copy of Clear's
  `UInt256.lean`; a copy is only worth having while it is still a copy. Diffs all 23
  vendored declarations against the Clear submodule.

Neither a green build nor a `sorry`-free grep is a progress metric. Believe the
checkers.

## Provenance and the pending migration

The 26 extracted modules are currently **copies**. `contracts-formal-verification`
still builds against its own `specs/` versions, so the two can drift — and if they
do, that repo's bridge theorems would quietly certify an implementation of an
outdated spec. See [PROVENANCE.md](PROVENANCE.md) for the migration that closes
this and why it has not been done yet.
