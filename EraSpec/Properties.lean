import EraSpec.Properties.InteropCommitmentTree
import EraSpec.Properties.AtomicFlowManager
import EraSpec.Properties.Protocol
import EraSpec.Properties.TreeRoot
import EraSpec.Properties.Atomicity
import EraSpec.Properties.Timeout
import EraSpec.Properties.Refund
import EraSpec.Properties.NativeTokenVault
import EraSpec.Properties.AssetRouter

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
  refund in the flow, on both timeout branches; finalizability does not decay; the
  flow-id check pins which leg list "the flow" means; and three countermodels
  showing the all-legs loop, the flow-id check and the DA assumption are each
  load-bearing.  This answers the question `AttackVectors.FlowAtomicity`'s header
  leaves open — same-outcome *is* forced, by `requireFlowFinalized`'s loop.
* `NativeTokenVault` — the bridge vault: the registry invariant the source states
  as a comment, **solvency** (`bridgedOut` never exceeds what the vault holds) along
  every run, no inflation for this chain's native assets, and the surplus never
  shrinking.  Two boundaries: the `InsufficientChainBalance` check is load-bearing,
  and **per-chain isolation does not hold** — the ledger carries no chain index, so
  one chain can withdraw against another's deposit.  That is the design (the source
  says correctness of minted amounts rests on the sending chain's ZK proofs), stated
  so `Solvency` is not read as more than it is.
* `AssetRouter` — who may point an asset at a handler.  `NoHijack` is structural:
  the asset id is hashed from the caller, so a caller cannot even name an id
  encoding somebody else, guard or no guard.  `OnlyTrackerOrNtvWrites` is the guard.
  `FreshIdNeedsNtv` is the consequence — a non-vault caller cannot make the first
  registration even for its own id, so custom deployment trackers must be
  bootstrapped through the vault or the counterpart path.
* `Timeout` — **the timeout decision is justified, not assumed.**  From the three
  comparisons `verifyTimeoutAbsence` makes against an imported aggregation root,
  `IsLastOnTimeDerived` produces the "last in-time batch" fact that
  `Contracts.Atomicity` used to take as a branch condition with nothing behind it.
  `TimeoutMeansMissedDeadline` is the positive form: a leg with a verified timeout
  was absent from its own chain at **every** batch that settled by the deadline —
  the refund is deserved, not merely permitted.  What is left is one named property
  of the settlement layer (`Aggregates`), with `StaleRootRefundsDeliveredLeg` as the
  countermodel showing it is load-bearing.
* `Refund` — **one outcome per obligation, system-wide.**  An `Obligation` is the
  triple `(flowId, bundleHash, chain)` that ties the manager's key, the tree's
  commit value and the escrowing chain together, so "delivered and refunded" is a
  statement about one economic commitment.  `ExecutedObligationNeverRefunded`: an
  executed obligation never gets past `Committed` in **any** interleaving of **any**
  chains' calls.  `RefundImpliesOwnFlowTimeout` is the binding — another flow's
  timeout, however genuine, refunds nothing here — and
  `CrossFlowRefundYieldsCollision` states it in the form that assumes nothing: a
  violation exhibits a keccak collision.

## Open (stated in Lean, no certificate yet)

None.  Every stated property has a certificate; `scripts/check-properties.sh`
reports `open: 0`.  That is a fact about the catalogue, not about the protocol —
what is *not stated* is the roadmap below, and the checker cannot see it.  The
`OPEN` path stays exercised by the checker's own self-test (plant a
`def Bogus : Prop := False` in any `Properties/` file and it must report it).

## Roadmap — properties worth stating next, and what the model needs first

These are the high-level guarantees the protocol is *for*, in rough order of
value.  Each needs a model extension before it can be a `def` here; the pieces
that already exist are named.

1. **Conservation across the bridge.**  `Properties.NativeTokenVault` shows the
   vault's own books balance; it does not connect native escrow, a remote chain's
   token supply, and the transfers in flight.  The statement worth having is that
   every mint or release consumes a matching authorized transfer, so neither replay
   nor refund can create a second payout.  Needs `BridgedStandardERC20` and the
   counterpart chain in one model, and is the largest remaining piece.

2. **When funds can get stuck.**  Everything proved so far is safety.  The liveness
   question is whether every committed obligation eventually executes or refunds,
   under explicit progress assumptions, and which exceptions are unavoidable.  The
   distinction to keep sharp is between "every leg has valid commitment evidence"
   (`Properties.Atomicity.ExecutedImpliesAllFinalizable`, proved) and "every
   destination call can actually execute", which nothing here addresses.

3. **The aggregation path.**  `Contracts.Timeout.EndBranchVerified.lastInRoot` is
   `_verifyLastBatchInRoot`'s conclusion, taken as given.  The Merkle-path argument
   behind it is `AttackVectors.LastBatchInRoot`; composing them would remove the
   last structural gap in the timeout story.

4. **Once-per-leg across contracts.**  `Contracts.Refund.Obligation` now ties the
   manager key to the tree value through `legValue`, so what remains is
   `commitValue` injectivity: distinct `(flowId, bundleHash)` pairs must get
   distinct tree values for `NoDoubleAppend` and `DedupGateSound` to compose.

5. **Height and capacity.**  Model `FullMerkle._height` in `Tree` and prove
   `leafCount ≤ 2^height` along runs, discharging `TreeRoot`'s `hcap` hypotheses
   and `Atomicity.Wf.capacity` instead of assuming them.

6. **The compiled side of O8 and O9.**  Source inspection, recorded in
   `EraSpec.Refinement`.

What is deliberately NOT on this list: anything about compiled code (obligations
O1–O8 in `EraSpec.Refinement`), which belongs to the sibling repo.
-/
