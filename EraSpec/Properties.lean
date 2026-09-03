import EraSpec.Properties.InteropCommitmentTree
import EraSpec.Properties.AtomicFlowManager
import EraSpec.Properties.Protocol
import EraSpec.Properties.TreeRoot

/-!
# The property catalogue

This package is organised in three layers, one folder each, with parallel files:

| folder | contains | you read it to check |
|---|---|---|
| `Contracts/` | the MODEL: state, guards, operations — definitions only | that the model is the Solidity |
| `Properties/` | the STATEMENTS: one `def … : Prop` per claim, no proofs | that the claims say what you want |
| `Proofs/` | the PROOFS, plus one *certificate* theorem per property | nothing — the kernel does |

A certificate is a theorem whose type is exactly a property constant, e.g.

    theorem Proofs.InteropCommitmentTree.DedupGateSound :
        Properties.InteropCommitmentTree.DedupGateSound := @dedup_gate_sound

`scripts/check-properties.sh` enumerates every `Prop`-valued `def` under
`EraSpec.Properties` and every theorem whose type is one of them, and prints
`PROVED` or `OPEN` per property.  Open properties are a roadmap, not a defect: a
statement can be written down before it is proved without putting a `sorry`
anywhere, and the checker keeps the list honest.

## What is proved (by file)

* `InteropCommitmentTree` — `setup` valid; the guarded `insert` preserves the
  invariant; the storage dedup gate is exactly set-level freshness; the search
  loop is sound and its exit establishes the guard; runs are `GuardedEvolution`s;
  **delivered-XOR-reclaimable at every step of every run from genesis**.
* `AtomicFlowManager` — rank monotone; `Reverted` absorbing; no double claim; no
  double append; claim needs authorization; the CEI order closes the gate before
  the external calls.
* `Protocol` — the bound refund gate is safe system-wide; the unbound gate refunds
  a delivered leg on a sound two-chain configuration; real per-chain deployments
  inherit the guarantee.
* `TreeRoot` — the root after `insert` is the `pushNewLeaf` walk; an accepted
  proof (any index, any path length) pins an occupied leaf; **inclusion and
  non-inclusion proofs are mutually exclusive at a valid root**; honest proofs
  are accepted; and the padding countermodel.

## Open (stated in Lean, no certificate yet)

* `InteropCommitmentTree.LowSearchTerminates` — with `leafCount` fuel the search
  from any occupied hint returns.  Provable now: values strictly increase along
  `nextIndex` links and there are finitely many leaves.

## Roadmap — properties worth stating next, and what the model needs first

These are the high-level guarantees the protocol is *for*, in rough order of
value.  Each needs a model extension before it can be a `def` here; the pieces
that already exist are named.

1. **Composed refund soundness** (manager × tree × time).  *A leg the manager
   marks `Reverted` was never delivered on time on its source chain, and a leg
   delivered on time never becomes `Revertable`.*  This is what `authorizeRefund`
   is for, end to end.  Needs: a composed state — per-chain `Run`s with
   settlement timestamps, plus the `Manager` — and the `authorize` step guarded by
   `NonInclusionAccepted` against the deadline-pinned root.  Pieces:
   `AttackVectors.NoTheft` (set level, temporal), `Properties.TreeRoot`
   (root level, atemporal), `Properties.AtomicFlowManager` (state machine).

2. **Once-per-leg across contracts.**  *A commit value enters its source tree at
   most once in any composed run.*  `NoDoubleAppend` (manager) composed with
   `DedupGateSound` (tree).  Needs the composed state of (1).

3. **Height and capacity.**  Model `FullMerkle._height` in `Tree`, prove
   `leafCount ≤ 2^height` along runs, and discharge the `hcap` hypotheses of the
   completeness properties instead of assuming them.  Small model change.

4. **Atomicity in the sanctioned sense, at root level.**  *Once all legs of a
   flow are delivered, every leg's inclusion proof verifies against every later
   root.*  `AttackVectors.FlowAtomicity` has it at set level; lifting it through
   `InclusionComplete` and key-set monotonicity is mostly bookkeeping.  Needs (3)
   for the capacity hypothesis.

5. **The END-branch timeout** (`AttackVectors.LastBatchInRoot`) composed with the
   IMT.  Needs a model of the aggregation tree; the largest extension here.

What is deliberately NOT on this list: anything about compiled code (obligations
O1–O7 in `EraSpec.Refinement`), which belongs to the sibling repo.
-/
