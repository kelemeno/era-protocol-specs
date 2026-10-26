# Manual review: what atomic interop must guarantee

Working specification from the manual review on 2026-10-21. Statements below are
review targets, not a claim that every deployed contract already satisfies them.
This records the initial atomic interop discussion. The current first complete
verification scope is **asset bridging**, including its registration, deployment,
and migration paths. Use the
[asset bridging verification plan](ASSET_BRIDGING_VERIFICATION_PLAN.md) for the
broader route inventory and proof milestones. Other contract families follow
later; bridge-facing settlement and governance dependencies remain explicit.

Source inspected: era-contracts commit
`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`, under
`l1-contracts/contracts/`. This is the pin recorded in [PROVENANCE.md](PROVENANCE.md).

## Where to review

Every contract/library now has `Specs/`, `Properties/`, and `Proofs/` folders.
Read the spec for state/operations and the property for the desired guarantee;
the proof file references that same named proposition. Start with:

- [AtomicFlowManager specification](EraSpec/Contracts/AtomicFlowManager/Specs/Model.lean)
- [AtomicFlowManager property statements](EraSpec/Contracts/AtomicFlowManager/Properties/Model.lean)
- [AtomicFlowManager checked proofs](EraSpec/Contracts/AtomicFlowManager/Proofs/Model.lean)

The per-contract README tables link all matching topics. The environment audit
checks proof coverage as well as axioms. Implementation correspondence remains
separate in [Refinement.lean](EraSpec/Refinement.lean).
Review the [assumption layers](ASSUMPTIONS.md) alongside these files: the axiom
audit does not classify model choices or establish EVM/Solidity correspondence.
The proposed [Lean-to-Solidity route and shared tests](CODE_GENERATION.md) is a
separate way to establish selected implementation boundaries for future code.

The first local asset-contract slice is now
[BridgedStandardERC20](EraSpec/Contracts/BridgedStandardERC20/README.md).
Review its exact mint/burn and ledger properties for the initialized-vault branch;
the [vault preparation slice](EraSpec/Contracts/NativeTokenVaultBase/README.md)
now composes that burn with source-side request and returned-data checks.
[Preparation traces](EraSpec/Protocol/AssetBridgePreparation/README.md) account
for multiple pending transfers while ordinary spending continues. Publication,
destination execution, and full recovery remain open.

The representation review now separates `LedgerInvariant` (token accounting)
from `RepresentationConsistent` (independently stored identities and registry
entries agreeing). `WellFormed` bundles the same five conditions as before.
[Fresh registration properties](EraSpec/Contracts/NativeTokenVaultBase/Properties/Initialization.lean)
establish these invariants from modeled deployment, token initialization, and map
installation, with no prior agreement assumption. Initialization preserves existing
balances; a zero ledger comes from modeled fresh proxy storage. The wrong-caller
countermodel explains why the vault must perform the initialization call itself.

[Initialization-to-preparation composition](EraSpec/Protocol/AssetBridgePreparation/Properties/Initialization.lean)
starts from a successful new-token branch, admits a token mint/burn/transfer phase,
then proves the invariants and pending-value conservation for subsequent
preparation/spending traces. Funding authorization during that token phase and
the concrete source/deployer correspondence remain separate obligations.

## The intended atomicity promise

If a flow executes on one participating destination, every other destination has
sufficient authenticated commitment evidence for its part. Applications that
prepare and preserve their execution conditions can successfully execute their
parts when that evidence is submitted through an authorized execution path.

Preparation can burn tokens, escrow assets, reserve a balance, or lock some other
application state. It must fix the obligation and prevent permitted intervening
transactions from invalidating the intended operation. It need not freeze the
whole contract or make its entire post-state a function of the input.

Three distinct states matter: ordinary source state, an in-flight obligation,
and fulfilled destination state. For a token transfer, burning removes spendable
source value and creates an obligation to mint at the destination or restore at
the source. The in-flight amount is a liability, not necessarily an escrow balance.

Eventual execution, proof availability, and complete recovery require additional
assumptions; they do not follow from the existence of a commitment.

## Statements and the first proofs

### P1. Preparation establishes an executable obligation

For an application `A`, input `i`, and successful preparation `s → p`, the
prepared state satisfies `A.ready p i`.

This is an application author's local obligation in
[`Prepared.Laws`](EraSpec/Core/PreparedApplication.lean), discharged for the reference
burn/mint bridge by `BurnMintBridge.application_laws`. Connecting successful
protocol commitment publication to this preparation is still an implementation
obligation; the protocol cannot establish readiness for arbitrary application code.

### P2. Waiting cannot invalidate the prepared operation

If every permitted unrelated step preserves readiness, then every finite sequence
of those steps preserves an execution with the committed effect:

```text
prepare(s, i, p) ∧ interferenceRun(p, t)
  ⇒ ∃ u, execute(t, i, intendedEffect(i), u)
```

Proved as `Prepared.prepared_execution_survives`. The concrete reference bridge
admits ordinary spending from both remaining endpoint balances while the burned
amount is pending. `prepared_mint_survives_spending` proves this spending cannot
prevent minting. The result does not silently include upgrades, pausing, changed
mint permissions, changed routing, or arbitrary third-party token behavior.
Every additional permitted transition must satisfy the preservation obligation.

For the reference bridge, `prepared_execution_remains_possible` is stronger:
under sound finalization evidence, every full permitted run leaves the transfer
either already executed or still executable, and never refunded.

### P3. Resolution uses the committed input

Waiting cannot replace the recorded obligation. Execution produces its intended
effect and credits the exact committed amount.

Proved as `committed_effect_unique`, `run_preserves_committed_input`, and
`execution_credits_committed_amount`. The reference input carries flow ID, leg ID,
and amount. Token identity, endpoint chains, and endpoint accounts are fixed by
the model instance. Binding all these to actual calldata, hashes, and deployment
addresses is OPEN; the reference model does not prove an encoding theorem.

### P4. Flow execution and flow recovery evidence are incompatible

Execution requires on-time commitment evidence for **all** prerequisites of the
same flow. Recovery requires a deadline-pinned absence witness for **one** of
those prerequisites. The missing prerequisite may be on a different chain from
the prepared obligation being recovered. Each prerequisite fixes its source
chain, commitment key, and deadline.

For valid append-only histories from genesis with monotone settlement times,
these authorizations cannot both exist, including at different proof snapshots.
Proved as `PreparedBridge.evidence_sound`, reusing the existing IMT history theorem.

The adapter currently covers the successor-pinned timeout form. The halted-chain
last-batch branch is not composed into this application theorem yet; see the
existing `TimeoutSoundness` and `LastBatchInRoot` modules. Authenticating roots,
binding settlement-layer clocks, and relating the real gates to this evidence
remain implementation obligations.

### P5. Fulfillment and recovery are exclusive and cannot repeat

The source recovery operation checks its own replay flag; destination minting
checks its own replay flag. Neither operation reads the remote chain's flag.
With sound protocol evidence, no reachable reference state has both effects.

Proved as `reachable_resolution_exclusive`, `no_second_execution`, and
`no_second_recovery`. Composed with the tree histories as
`PreparedBridge.prepared_bridge_no_double_payment`.

`conflicting_evidence_double_pays` proves the negative case: if both certificates
are allowed, both local operations succeed and one burned unit produces two
spendable units. Exclusivity is not assumed by a shared cross-chain status flag.

### P6. Value remains accounted for throughout the transfer

For every reference run with sound evidence:

```text
source spendable + destination spendable + spent elsewhere + in-flight liability
  = initial source spendable + initial destination spendable
```

Proved as `reachable_value_conserved` and composed with commitment histories as
`PreparedBridge.prepared_bridge_value_conserved`. The reference model uses
unbounded natural amounts, one obligation, no fees, and exact full mint/recovery.
It does not model arbitrary token supply, rebases, fee-on-transfer tokens, token
caps, external call failures, or actual EVM rollback.

### P7. First execution supplies evidence for other prepared destinations

A successful reference `AuthorizedExecution` includes the complete flow gate.
For other prepared destinations bound to that same flow specification, the gate
and the application laws yield enabled executions after permitted interference.

Proved as `execution_enables_other_prepared_legs`. Commitment membership persists
on each prerequisite's source history by `accepted_flow_evidence_persists`.
The specification explicitly requires the same flow on every destination; proving
that hash/encoding binding and refining actual execution to `AuthorizedExecution`
are OPEN. The theorem proves enabled local transitions, not simultaneous execution,
cross-application independence, or inevitable execution.

### P8. Recovery completion and progress need their own promises

Candidate target: every recoverable prepared obligation can eventually be fully
restored if a flow cannot finalize, under stated chain progress, evidence
availability, permissions, application behavior, and transaction scheduling.

OPEN as a system guarantee. The reference bridge admits full recovery, but the
real manager's best-effort recovery can accept partial results or be blocked by
one reverting target; see `RecoveryLimits`. This difference must be resolved in
the application requirements, not hidden by the stronger reference model.

## Contract-by-contract property map

These are candidate review statements, not completed per-contract audits. Each
row needs agreement on intended behavior, an inventory of permitted transitions,
and a precise connection to the source and compiled-code proofs.

| Contract or component | State or responsibility | Properties to review |
|---|---|---|
| `InteropCenter` | Sender salts, prepared calls, fee balances, bundle publication | All required preparation succeeds before commitment; failure rolls back source effects and salt/fee updates; the published bundle matches preparation; sender and destination identities are fixed; sender salts cannot replay; atomic calls carry no unsupported native value; fee claims cannot take another party's balance. |
| `L2AssetRouter` / `AssetRouterBase` | Routes assets and constructs indirect bridge calls | Source initiation really burns or escrows before returning the mint call; asset, original depositor, amount, destination, and recipient remain bound; only authenticated counterpart/self paths finalize; only the manager invokes atomic recovery; recovery restores the depositor rather than the remote recipient; routing changes cannot invalidate pending obligations without an explicit exception. |
| `NativeTokenVaultBase` / `L2NativeTokenVault` / `L1NativeTokenVault` | Asset identity, origin chain, escrow/burn/mint, chain accounting | Every outgoing obligation is funded; native escrow and representation burns are distinguished; mint/recovery use matching asset and chain accounting; exact recipient and amount are preserved; asset registration cannot substitute a token; identify which pause, metadata, deployment, token, and balance conditions can block pending execution or recovery. |
| `BridgedStandardERC20` | Representation balances, total supply, mint/burn authority | Only the authorized vault mints/burns; amounts and total supply change exactly; a committed mint remains possible under permitted changes; initialization/reinitialization cannot change the asset represented by pending obligations; fixed-width arithmetic guards are sufficient. |
| `AtomicFlowManager` | Per-flow/per-bundle lifecycle and flow gates | Only the center commits; only the handler checks execution finality; execution authenticates every declared leg and includes the executing bundle; one genuinely missing leg authorizes recovery only for that same flow; source chains and settlement layer are bound; recovery is at most once and closes its gate before callbacks; state terminality must not be mistaken for full asset restoration. |
| `L2InteropCommitmentTree` | Stored commitment keys and indexed links | Authorized insertions only; no duplicate/zero commitment insertion; guards preserve order, links, capacity, and root fidelity; no ordinary operation removes commitments; initialization cannot reset live history. |
| `IndexedMerkleTree`, `FullMerkle`, `Merkle`, `ChainBatchRootTree` | Tree algorithms and proof structure | A root authenticates exactly the intended leaves and indices; unused padding cannot impersonate a leaf; depth/capacity/index bounds hold; begin/end roots are distinct authenticated positions; hash/domain assumptions are explicit. |
| `AtomicInteropProof` | Inclusion and both timeout branches | Prove correct source chain, commitment, settlement layer, and clock; on-time end-root inclusion permits finalization; late begin-root absence or last-in-time end-root absence excludes finalization; stale roots, wrong branches, and non-last batches cannot authorize recovery; halted-chain recovery has a usable witness under explicit publication assumptions. |
| `L2InteropHandler` / `InteropHandlerBase` / `L1InteropHandler` | Bundle/call replay state and external execution context | Successful atomic execution passed the complete flow gate; bytes executed equal committed bytes; destination/source/sender and execution permissions are authenticated; each effect runs at most once; reentrancy cannot reopen execution; failing calls roll back the bundle; public verify/unbundle routes cannot consume atomic bundles; L1 restrictions are preserved. |
| `L2InteropRootStorage` | Imported `(chain, batch/block, root, timestamp)` tuples | Only the bootloader imports; a key is immutable; zero denotes absence unambiguously; root and timestamp match the same authenticated settlement snapshot. Local insertion guards alone do not prove settlement authenticity or timestamp order. |
| `MessageVerification` / `L2MessageVerification` / `MessageRootBase` and variants | Recursive root authentication and settlement history | Every accepted leaf belongs to the claimed chain and snapshot; root history and timestamps are authentic; malformed recursion and cross-chain substitution fail; imported-root dependencies match settled roots; chain genesis and last-batch structure support the timeout promises. |
| `BaseTokenHolder` | Native value collection and release | Release is backed by collected/bridged value with correct chain accounting; only authorized entry points collect/release; callbacks cannot duplicate payment. This is principally the public value path: native call value is excluded from atomic bundles. |
| `L1AssetRouter` / `L1Nullifier` | L1 finalization, failed-transfer recovery, consumed transfer records | Authenticated transfer results bind all identifying data; a transfer cannot be claimed twice or both finalized and refunded; local/transient context is cleared or consumed before callbacks; native and representation paths preserve accounting. These paths need separate models from the atomic reference bridge. |
| `BridgehubBase` and variants / registration / deployment trackers | Chain and asset identity, base tokens, counterpart configuration | Chain/asset IDs cannot alias unauthorized counterparts; interop destinations satisfy required genesis/registration conditions; changing settlement layer, handler, or token mappings cannot silently change the meaning of pending obligations. |
| Settlement facets, bootloader, validators, upgrades, governance | Supplies authenticated execution and changes the environment | Inventory who can publish/settle roots, change configuration, pause, or upgrade. Decide which actions must preserve pending obligations and which are explicitly trusted exceptions. Expand to concrete per-contract statements in the next review pass. |

The `Contracts/<SolidityName>/` directories group each source owner's models and
properties; `Protocol/` holds cross-contract results. Shared preparation
requirements live in `Core/PreparedApplication.lean`; the reference asset
lifecycle lives in `Examples/BurnMintBridge/`. Neither is evidence that the entire source inventory above is verified.
The implementation seams remain listed in [EraSpec/Refinement.lean](EraSpec/Refinement.lean).

## Review procedure for each contract

1. Describe the user-visible promise and one concrete failure scenario.
2. List the state the contract owns, the pending obligations, and what is locked.
3. Enumerate every transition, including callbacks, cancellation, pause, configuration,
   migration, and upgrade paths. Say which may occur while an obligation is pending.
4. State local preparation, preservation, effect, replay, and recovery properties.
5. Name each dependency and the exact guarantee needed from it. A caller's
   assumption must become another component's proved obligation or an explicit trust assumption.
6. Agree on the plain-language statement, formalize it, prove its local invariant,
   and construct counterexamples when a required guard/assumption is removed.
7. Connect the abstract transition to all actual source/compiled entry points;
   record remaining gaps without treating a green abstract build as deployment verification.

Suggested first concrete path: `InteropCenter._processCallStarter` →
`L2AssetRouter.initiateIndirectCall` → `NativeTokenVaultBase.bridgeBurn` →
`InteropCenter._dispatchBundle` / `AtomicFlowManager.append`. The question to
settle first is exactly what a successfully published bridge commitment guarantees
has already happened to the sender's assets and the returned destination calldata.
