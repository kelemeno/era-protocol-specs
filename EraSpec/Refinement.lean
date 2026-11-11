import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Model
import EraSpec.Contracts.AtomicFlowManager.Proofs.Model
import EraSpec.Protocol.Spec

/-!
# Refinement obligations

The theorems in this package describe local abstract models. They do not establish
that Solidity source or deployed bytecode implements those models. The following
seven source-correspondence obligations are open work for this repository. They
are recorded as prose rather than Lean theorems because this package has no EVM or
Solidity semantics; placeholder theorem bodies would not discharge them. The older
`contracts-formal-verification` repository is not a dependency, and its proofs are
not evidence for these obligations.

`ASSUMPTIONS.md` is the layer register: VM execution, Solidity constructs,
compiler/artifact identity, contract representation, dependency behavior,
cryptographic/protocol evidence, and operational conditions are distinct.
O1–O7 below are contract correspondence obligations, not VM or Solidity axioms.
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

end EraSpec.Refinement
