import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Model
import EraSpec.Contracts.AtomicFlowManager.Proofs.Model
import EraSpec.Protocol.Spec
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.TreeRoot
import EraSpec.Protocol.InteropAtomicity.Proofs.Atomicity
import EraSpec.Protocol.InteropAtomicity.Proofs.Timeout
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund

/-!
# Refinement obligations

The theorems in this package describe local abstract models. They do not establish
that Solidity source or deployed bytecode implements those models. The following
nine source-correspondence obligations are open work for this repository. They
are recorded as prose rather than Lean theorems because this package has no EVM or
Solidity semantics; placeholder theorem bodies would not discharge them. The older
`contracts-formal-verification` repository is not a dependency, and its proofs are
not evidence for these obligations.

`ASSUMPTIONS.md` is the layer register: VM execution, Solidity constructs,
compiler/artifact identity, contract representation, dependency behavior,
cryptographic/protocol evidence, and operational conditions are distinct.
O1–O9 below are contract correspondence obligations, not VM or Solidity axioms.
`Core/Simulation.lean` proves generic safety-refinement composition; no concrete
VM/Solidity/compiler instance has been supplied. `CODE_GENERATION.md` records the
proposed restricted Lean-to-Solidity route and shared/differential tests, with a
separate translation-preservation obligation.

## O1 — commitment-tree state and updates

Relate `Contracts.InteropCommitmentTree.Tree` to the selected source's stored
`leafCount`, indexed leaves, and `valueToIndex` map. Establish the effect of every
tree write and connect the full source-level call path, including dispatcher and
insert glue, to `Tree.insert`.

## O2 — insertion guards

Show that a successful source `insert` call implies every condition in
`Contracts.InteropCommitmentTree.InsertGuard`, with the right inputs and ordering
before writes. Also rule out model conditions that source does not enforce; an
always-reverting implementation must not satisfy the intended behavior vacuously.

## O3 — bounded search

Relate `lowSearch` to the source search loop, including its fuel bound,
termination/revert behavior, and the `none` case corresponding to
`IMTLowLeafNextTooSmall`.

## O4 — flow-manager state transitions

Show that the modeled `Contracts.AtomicFlowManager.Step` transitions correspond to
the source updates of `_state[flowId][bundleHash]`: all relevant transitions are
represented, guards precede writes, and success and failure effects match.

## O5 — caller authority

Establish the caller restrictions for append, finalized-flow checks, insert, and
initialization, along with the authority used by each modeled transition. Caller
identity is not currently part of every abstract transition, so this remains an
explicit source-correspondence obligation.

## O6 — cross-chain source binding

Relate `Contracts.Protocol.BoundGate` to the selected source's refund path. In
particular, establish that the absence proof's `sourceChainId` is checked against
the missing leg's declared source chain before it can authorize a refund. The local
countermodel `unbound_gate_refunds_delivered_leg` records why this condition
matters; it does not establish that source code enforces it.

## O7 — Merkle root correspondence

Relate the abstract Merkle fold and proof checks to the source's leaf hashing,
stored-root updates, and inclusion/non-inclusion verification. Establish that the
root used by the source authenticates exactly the leaves represented by the local
tree model, under explicit hash and encoding assumptions.

The protocol-level part of root binding is now stated locally, but its soundness
results are vacuous until restated (see `HashAssumptionsUnsatisfiable` below).
`Contracts.InteropCommitmentTree` (topic `TreeRoot`, under
`Contracts/L2InteropCommitmentTree/`) defines the root over the list state,
`root h z0 hl T height = rootOf h z0 (leafHashes hl T) height`, and states the two
verifiers complete (`InclusionComplete`, `NonInclusionComplete`, no hash premise)
and sound (`AcceptedPathPinsLeaf`, `ProofsExclusive`, under the `HashAssumptions`
bundle, so vacuous for now) against it, for prover-chosen indices and path lengths. The deployed
verifier's missing range and height checks are handled in
`Contracts/Merkle/Properties/Verifier.lean`. So the source side of O7 narrows to
one statement: `FullMerkle.updateLeaf` followed by `pushNewLeaf` computes `rootOf`
over `leafHashes` of the new state. `RootAfterInsert` fixes that target exactly.

*A hypothesis that is false at the pin.* `HashAssumptions.padNotLeaf` says the
`FullMerkle` padding constant is not a leaf hash. The pinned
`IndexedMerkleTree.setup` pads with `hashLeaf({0,0,0})`, so it is one, and
`Contracts.InteropCommitmentTree.Properties.PaddingCollisionRefundsDeliveredLeg`
shows the consequence on a real contract run: an accepted `verifyNonInclusion` for
a delivered value. Later era-contracts revisions pad with `IMT_EMPTY_LEAF_HASH`.
When the pin moves, re-check this first.

## O8 — the atomicity gate covers every leg, and the flow is pinned

`Contracts.Atomicity.FlowFinalized` is a conjunction over all legs, and the
none-or-all results in `Protocol/InteropAtomicity/` are exactly as strong as that
conjunction. Two source facts are needed for them to apply to
`requireFlowFinalized`:

1. **The loop covers every leg and reverts on any failure.** `n =
   flow.legBundleHashes.length`, `_finality.proofs.length != n` reverts
   (`ManagerProofCountMismatch`), the loop runs `i = 0 .. n-1`, and
   `verifyInclusion` reverts rather than returning a flag. An off-by-one bound or a
   swallowed failure leaves one leg unchecked, which is the mixed outcome
   `SelfOnlyGateAdmitsMixedOutcome` exhibits.
2. **`flowId` pins which legs those are.** The model takes the flow as given. On
   chain, `_checkFlowId` recomputes `keccak256(abi.encode(legBundleHashes,
   legSourceChainIds, deadline, settlementLayerChainId))` and compares; the
   ascending-order check makes the preimage canonical. Locally,
   `SubsetFlowPassesUncheckedGate` is the attack without the check (it takes no hash
   premise). `FlowIdCheckPinsLegList` and `SubsetFlowRejectedByCheck` take
   `FlowHashInj`, which `FlowHashInjUnsatisfiable` shows cannot hold, so the check's
   sufficiency is not yet proved; `Contracts.Refund.Properties.CrossFlowIdClashIsPinnedCollision`
   (a collision on the two flows' own preimages) is the form to build on. The source side must show `_checkFlowId`
   recomputes that hash and reverts on mismatch.

Item 1 is a reading task rather than a proof task, but an edit can break it while
every local proof stays green.

## O9 — the bridge models are the source bridge

`Contracts.NativeTokenVault.Vault` must correspond to `NativeTokenVaultBase`'s
storage (`originChainId`, `tokenAddress`, `assetId`, and L1's `bridgedOut`), and
`Contracts.AssetRouter.Router` to `AssetRouterBase`'s `assetHandlerAddress` /
`assetDeploymentTracker`. Two parts of those models are not storage and carry their
own obligations:

* `Vault.escrowed` is the token contract's balance of the vault. Modelling it as an
  exact counter is what `_depositFunds`' balance comparison
  (`TokensWithFeesNotSupported`) and `require(_depositAmount == msg.value)` buy;
  a fee-on-transfer or rebasing token is outside both the model and the contract's
  support.
* `Vault.originToken` is `tokenAddress[assetId]` for a native asset and an external
  call (`IBridgedStandardToken.originToken()`) for a bridged one. The invariant
  `idShape` is about it, so the source side must agree that a bridged token reports
  the origin token its asset id was checked against.

These two models overlap the separately written `Contracts.NativeTokenVaultBase`
model; relating or unifying them is open.

## Data availability is an assumption, not an obligation

The none-or-all result carries a data-availability hypothesis (`DataAvailable`), and
`WithoutDaCommittedLegIsStuck` shows it cannot be dropped: with a chain's data
unavailable, a committed leg can be neither finalized nor refunded. That countermodel
uses `HashAssumptions` in its proof, so it is vacuous until restated. No source
correspondence can discharge it. Likewise the timeout results carry the settlement
layer's `Aggregates` invariant, and `StaleRootRefundsDeliveredLeg` (no hash premise)
shows that one is load-bearing too.

`DataAvailable` is source-chain data only, and the none-or-all results conclude
finalizability against the true root. The destination's own gate needs two more world
assumptions, stated in `Contracts.RootImport`: `ImportAvailable` (the destination has
imported a settlement-layer root covering the batch) and `SettlementDataAvailable` (the
multi-hop settlement proof is presentable). `WithoutImportFlowSitsHalfExecuted` (no
hash premise) shows the first is load-bearing. Without it, one leg executes on its
destination while a sibling's destination cannot pass, and no leg is refundable.

## Additional bridge correspondence

The first `BridgedStandardERC20` slice models the nonlegacy token branch.
Its source correspondence remains open: connect the actual token balance/supply
effects to the abstract transition, and establish uint256 arithmetic, caller
authority, external-call results, and revert/rollback behavior. Legacy fallback,
configuration changes, and other asset branches need separate coverage.

The registered representation branch of `NativeTokenVaultBase` now composes that
token operation with local registry checks, pre-burn accounting, and post-burn
origin/metadata validation. Its typed returned data is not an ABI proof. Relating
the parametric hooks, token getter, selected-token assumptions, and atomic commit
interface to real calls and rollback remains open. The preparation trace's
pending list is ghost accounting, not vault storage or proof of publication.

Initialization now establishes the local ledger and representation invariants
from a fresh-proxy allocation model and the projected deployment/registry-install
sequence. The separate representation proof retains independent stored fields;
it does not identify them by construction. Source correspondence must still
justify fresh proxy storage, the actual vault caller, outer metadata decoding,
resolved origin-chain inputs, CREATE2/asset-ID behavior, hook frames, and the
omitted registry origin/index/count writes. The modeled initializer is public
until initialized; the intended atomic deployment call order is essential.

More broadly, source correspondence must state its treatment of storage layout,
ABI and memory bytes, events, arithmetic, external calls, and transaction rollback.
Any semantics or environmental behavior omitted from the concrete model must
remain an explicit assumption or excluded claim.
-/

namespace EraSpec.Refinement

/-! ## Machine-checkable summary of local abstract results

The statements below summarize results proved about the local models. They do not
discharge the source-correspondence obligations above. They are `abbrev`s rather
than restatements so there is exactly one proof of each, and `#print axioms` on
them reports the real profile. -/

/-- The commitment tree: every run from `setup` keeps the reclaim gate firing on
exactly the never-delivered legs. -/
abbrev tree_guarantee := @Contracts.InteropCommitmentTree.genesis_run_reclaimable_iff_absent

/-- The flow manager: a refunded leg stays refunded, so no leg is refunded twice. -/
abbrev manager_guarantee := @Contracts.AtomicFlowManager.no_double_claim

/-- The multi-chain protocol: with the source-chain binding, delivery and refund
are mutually exclusive system-wide; without it, they are not. -/
abbrev protocol_guarantee := @Contracts.Protocol.chains_no_double_spend

/-- The countermodel that makes O6 necessary rather than advisory. -/
abbrev binding_necessity := @Contracts.Protocol.unbound_gate_refunds_delivered_leg

/-! **Read the next block with the unsatisfiability theorems in mind.**
`root_guarantee`, `atomicity_guarantee`, `atomicity_no_refund`, `da_necessity`,
`all_or_nothing` and `timeout_justified` take `HashAssumptions` and, for
`all_or_nothing`, also `FlowHashInj`; neither can hold
(`HashAssumptionsUnsatisfiable`, `FlowHashInjUnsatisfiable`), so they are vacuous as
stated and name what the collision-form restatement must recover.
`padding_necessity`, `all_legs_gate_necessity`, `flowid_necessity` and
`aggregation_necessity` take no hash premise and stand. -/

/-- The hash side: against a valid tree's root, no value has both an accepted
inclusion proof and an accepted non-inclusion proof, for any indices and path
lengths the provers choose. -/
abbrev root_guarantee := @Contracts.InteropCommitmentTree.ProofsExclusive

/-- The countermodel that makes `HashAssumptions.padNotLeaf` load-bearing: with
`hashLeaf({0,0,0})` as the padding constant, a delivered leg has an accepted
absence proof. -/
abbrev padding_necessity := @Contracts.InteropCommitmentTree.PaddingCollisionRefundsDeliveredLeg

/-- The hash side, with no hash premise: if one value has both an accepted inclusion
proof and an accepted non-inclusion proof against a valid tree's root, a located
`TreeRootBreak` exists on one of the two paths. -/
abbrev root_guarantee_or_break := @Contracts.InteropCommitmentTree.ProofsExclusiveOrBreak

/-- The interop headlines, with no hash premise: an executed flow's legs are never
refunded, unless a break is located on a named submitted proof. -/
abbrev atomicity_no_refund_or_break := @Contracts.Atomicity.ExecutedExcludesAnyRefundOrBreak

/-- One outcome per obligation over every interleaving, unless a logged call that
marked it carries a located break. -/
abbrev all_or_nothing_or_break := @Contracts.Refund.ExecutedObligationNeverRefundedOrBreak

/-- The timeout decision, with no hash premise. -/
abbrev timeout_justified_or_break := @Contracts.Timeout.TimeoutMeansMissedDeadlineOrBreak

/-- Partial atomicity, IMT half: if any leg of a flow is executed, every leg has a
presentable IMT proof accepted against the true root, given source data availability.
That every leg's destination can pass its gate also needs the destination's imported
settlement-layer root and a settlement proof:
`Contracts.RootImport.ExecutedAtImpliesAllFinalizableAtOrBreak`. -/
abbrev atomicity_guarantee := @Contracts.Atomicity.ExecutedImpliesAllFinalizable

/-- …and no leg of that flow can be refunded, on either timeout branch. -/
abbrev atomicity_no_refund := @Contracts.Atomicity.ExecutedExcludesAnyRefund

/-- The countermodel that makes O8's all-legs loop load-bearing. -/
abbrev all_legs_gate_necessity := @Contracts.Atomicity.SelfOnlyGateAdmitsMixedOutcome

/-- The countermodel that makes the DA hypothesis load-bearing. -/
abbrev da_necessity := @Contracts.Atomicity.WithoutDaCommittedLegIsStuck

/-- The countermodel that makes O8's flow-id recomputation load-bearing: without
it, a truncated flow passes the gate. -/
abbrev flowid_necessity := @Contracts.Atomicity.SubsetFlowPassesUncheckedGate

/-- One outcome per obligation: an executed obligation is never refunded, in any
interleaving of any chains' calls. -/
abbrev all_or_nothing := @Contracts.Refund.ExecutedObligationNeverRefunded

/-- The timeout decision is justified rather than assumed: a leg with a verified
timeout was absent from its source chain at every batch that settled in time. -/
abbrev timeout_justified := @Contracts.Timeout.TimeoutMeansMissedDeadline

/-- The countermodel that makes the settlement layer's aggregation guarantee
load-bearing. -/
abbrev aggregation_necessity := @Contracts.Timeout.StaleRootRefundsDeliveredLeg

end EraSpec.Refinement
