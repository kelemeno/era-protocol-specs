import EraSpec.Properties.InteropCommitmentTree
import EraSpec.Properties.AtomicFlowManager
import EraSpec.Properties.Protocol
import EraSpec.Properties.TreeRoot
import EraSpec.Properties.Atomicity

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
* `Atomicity` — **partial atomicity, none-or-all**: if any leg of a flow is
  executed then every leg can be finalized, given data availability; equivalently,
  either all legs are finalizable or none executes.  Also: execution excludes every
  refund in the flow, on both timeout branches; finalizability does not decay; and
  two countermodels showing the all-legs gate and the DA assumption are each
  load-bearing.  This answers the question `AttackVectors.FlowAtomicity`'s header
  leaves open — same-outcome *is* forced, by `requireFlowFinalized`'s loop.

## Open (stated in Lean, no certificate yet)

* `InteropCommitmentTree.LowSearchTerminates` — with `leafCount` fuel the search
  from any occupied hint returns.  Provable now: values strictly increase along
  `nextIndex` links and there are finitely many leaves.

## Roadmap — properties worth stating next, and what the model needs first

These are the high-level guarantees the protocol is *for*, in rough order of
value.  Each needs a model extension before it can be a `def` here; the pieces
that already exist are named.

1. **Composed refund soundness** (manager × tree × time).  `Atomicity` has the
   half that matters most — an executed leg is unrefundable, system-wide
   (`ExecutedExcludesAnyRefund`) — but it says nothing about the manager's own
   state.  The missing statement is *a leg the manager marks `Reverted` was never
   delivered on time*: `AtomicFlowManager.Step.authorize` guarded by
   `LegRefundable`, composed with `Atomicity.System`.  Needs the two models joined
   into one state; both halves already exist.

2. **Once-per-leg across contracts.**  *A commit value enters its source tree at
   most once in any composed run.*  `NoDoubleAppend` (manager) composed with
   `DedupGateSound` (tree).  Needs the composed state of (1).

3. **Height and capacity.**  Model `FullMerkle._height` in `Tree` and prove
   `leafCount ≤ 2^height` along runs, discharging `TreeRoot`'s `hcap` hypotheses
   and `Atomicity.Wf.capacity` instead of assuming them.  Small model change, and
   it is now load-bearing in two files rather than one.

4. **`IsLastOnTime` from the aggregation tree.**  `Atomicity` assumes the END-root
   timeout branch really identifies the chain's last in-time batch; that is what
   `_verifyLastBatchInRoot` plus a post-deadline settlement-layer root establish.
   `AttackVectors.LastBatchInRoot` has the path argument. Composing them needs a
   model of the aggregation tree — the largest extension here, and the last
   assumption in the refund story that is not either a hash idealization or DA.

5. **The flow-id binding** (obligation O8 in `EraSpec.Refinement`).  `Atomicity`
   takes the flow as given.  What stops a prover from presenting a *subset* flow
   containing only the committed legs is `_checkFlowId` recomputing
   `keccak(legBundleHashes, legSourceChainIds, deadline, settlementLayerChainId)`.
   Stating that here needs the flow-hash injectivity assumption
   (`AttackVectors.BundleHashEncoding` is the encoding half).

What is deliberately NOT on this list: anything about compiled code (obligations
O1–O7 in `EraSpec.Refinement`), which belongs to the sibling repo.
-/
