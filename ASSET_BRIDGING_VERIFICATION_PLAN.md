# Asset bridging verification plan

## 1. Purpose, source, and boundary

The first comprehensive production scope is ZKsync Era asset bridging. This
repository owns its abstract specifications and proofs locally and depends on
Mathlib. An abstract theorem proves a property of its stated model and assumptions;
it does not establish that Solidity source or deployed bytecode implements that
model. Implementation correspondence is a separate, open obligation.

The initial source context is era-contracts commit
`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`. Re-read the relevant source at every
source-pin change. The older `contracts-formal-verification` repository is a
historical reference only; its code and proofs are not a dependency and do not
supply correspondence evidence here.

The current checked developments cover atomic interop abstractions, an
illustrative bridge application, and the first local token-ledger slice in
[BridgedStandardERC20](EraSpec/Contracts/BridgedStandardERC20/README.md). They do
not yet establish whole-route or deployed-contract verification. See [REVIEW.md](REVIEW.md) for
local review evidence, [PROVENANCE.md](PROVENANCE.md) for copied-module history,
and [REUSE.md](REUSE.md) for historical reference artifacts.

## 2. Route and asset coverage

Track each route against each relevant asset behavior and VM configuration. The
initial route register must include:

- **L1 → L2:** deposits and destination mint/release, including native-token,
  bridged ERC20, base-token, and wrapped-token paths where supported.
- **L2 → L1:** withdrawals, source burn/escrow, authenticated finalization, and
  destination release, including replay and failed-call behavior.
- **Public L2 → L2:** direct public interop transfers and their source preparation,
  destination execution, and recovery behavior.
- **Atomic L2 → L2:** multi-leg flows, shared preparation, all-leg publication,
  per-leg execution, timeout/recovery evidence, and partial or best-effort recovery.

For each route, record supported token class, chain/VM, entry points, callers,
asset identity, amount and recipient binding, state owner, failure behavior,
configuration, and explicit dependencies. Do not infer that a route is covered
because a similarly named interop abstraction has been proved.

### Value and the pending obligation

Model three economically distinct stages: ordinary source value, a prepared
in-flight obligation, and delivered destination value. Preparation burns,
escrows, or reserves the needed resource; resolution either delivers that same
obligation or restores the source depositor. An in-flight liability is not
necessarily an actual escrow balance.

The obligation fixes origin asset, source/destination chains, depositor,
recipient, amount, and authenticated transaction/bundle/call identity, including
call position. It is a specification ledger, not a globally shared status flag.
Prove how local replay state and exclusive evidence enforce its resolution.

For a fixed-issuance asset across a closed set of modeled chains, the intended
accounting shape is:

```text
origin-native value outside bridge backing
  + spendable representations + unresolved economic obligations
  = initial economic units
```

Do not count escrow and its backed representation twice. Wrapped assets need a
separate backing relation, and external issuance/destruction, fees, donations,
and migrations need explicit terms or restrictions. Custody solvency is distinct
from conservation; unsolicited funds can make exact custody equality unsuitable.

Prepared determinism means a fixed intended effect that stays enabled under
specified interference. It does not imply unconditional mint success: recipient
checks, supply bounds, authority, deployment, pause state, and callbacks must be
accounted for.

## 3. Named bridge targets

Use the following target names when recording specifications, proofs, assumptions,
and implementation correspondence. Each target may need distinct statements per
route and asset class.

| Target | Guarantee to establish |
|---|---|
| **B1 — Correct identity and authorization** | Every transition uses the intended caller, source/destination chain, asset, amount, recipient, route, and counterpart. Registration and handler selection cannot alias another asset or route. |
| **B2 — Backed outgoing movement** | Every published obligation corresponds to the required token burn, escrow, reserve movement, or other route-specific backing action. A message alone does not prove funding. |
| **B3 — Preparation and publication binding** | The prepared token/vault data is bound to the exact published bytes and later execution parameters. Ordinary permitted interference cannot silently change the prepared effect. |
| **B4 — No unbacked delivery** | Every successful destination credit or custody release consumes an authorized funded obligation. The required source-preparation guarantee is proved or stated as an explicit trust assumption. |
| **B5 — Unique resolution** | An obligation delivers at most once, refunds at most once, and never both. Prove local replay protection and cross-chain evidence incompatibility separately before composition; retries after revert cannot duplicate a successful effect. |
| **B6 — Conservation and solvency** | Every reachable trace preserves asset-specific accounting. Pending value remains accounted for; redeemable liabilities stay backed under the stated token laws. Exclude cross-asset substitution and spending another liability's backing. |
| **B7 — Stable preparation** | Once prepared, permitted spending, transfers, shared-vault activity, supply limits, chain accounting, deployment, and routing cannot invalidate readiness, or are explicit execution preconditions. |
| **B8 — Atomic rollback and callback safety** | Failure has the specified transaction-wide rollback effect on balances, supply, tracker state, salts, records, and publication. Reentrancy cannot reopen consumed obligations, reuse authority/context, or invalidate accounting. Model successful and failed external calls. |
| **B9 — Correct registration and migration** | Asset IDs, origin data, local tokens, handlers, beacons, and counterparts remain consistent and cannot alias. Initialization, reinitialization, and legacy migration preserve balances, backing, and pending obligations. |
| **B10 — Arithmetic and implementation fidelity** | Abstract updates correspond to checked/unchecked uint256 arithmetic, storage, calldata/encoding, hashing, external calls, and revert behavior. Natural-number conservation alone is insufficient. |
| **B11 — Conditional deliverability** | Given valid evidence, available dependencies, sufficient execution resources, and stated configuration, delivery remains possible after permitted interference. Eventual delivery additionally states fair submission/inclusion and chain-progress assumptions. |
| **B12 — Conditional recoverability** | Where the route permits recovery and valid evidence exists, the remaining obligation can be restored under explicit progress and dependency assumptions. Identify partial/best-effort recovery and terminal-but-unpaid states; manager terminality does not prove full restoration. |

B1–B10 are safety and correspondence targets. B11 and B12 distinguish an enabled
transition from eventual progress. Each theorem must identify token and environment
laws it assumes. In particular, arbitrary custom handlers or external ERC20s do
not automatically satisfy standard-token behavior; VM-controlled balances,
callbacks, and chain accounting need explicit semantics.

## 4. Contract ownership map

| Contract family | Initial model and proof responsibilities |
|---|---|
| `BridgedStandardERC20` | Exact transfer, mint, and burn balance/supply effects; authority; zero-address/amount behavior; arithmetic invariants; initialization, legacy vault fallback, and metadata behavior. |
| `NativeTokenVaultBase` | Asset/origin registry; preparation and returned mint data; native/representation/base-token branches; deployment and metadata failures; mint/refund accounting; external-token laws. |
| `L1NativeTokenVault` | ERC20/ETH custody and release; aggregate `bridgedOut` liability; failed-transfer restoration; representation deployment; recipient callback failure. |
| `L2NativeTokenVault`, `L2NativeTokenVaultZKOS` | Tracker composition; representation mint/burn and native escrow; counterpart/deployment/address correspondence; Era/OS differences and legacy paths. |
| `AssetRouterBase`, `L1AssetRouter`, `L2AssetRouter` | Handler selection; preparation-to-calldata binding; base/non-base separation; counterpart/self authorization; exact deposit, withdrawal, indirect-call, and recovery paths. |
| `L1Nullifier` | Deposit transaction/data-hash binding; authenticated status; one-time consumption before callback; rollback on callback failure; dependency configuration and pause behavior. |
| `L2AssetTracker` | Chain-accounting interpretation; permitted debits/credits; origin-native sentinel; supply snapshots; legacy registration and migration/backfill invariants. |
| `BaseTokenHolder`, `L2BaseTokenBase`, `L2BaseTokenEra`, `L2BaseTokenZKOS` | Collection/release authority and reserves; tracker notification; native-value failures; VM-controlled balances and migration; separate fund safety from reported supply accuracy. |
| `L2WrappedBaseToken`, `L2WrappedBaseTokenStore` | Deposit/withdraw collateralization; bridge burn then native release; rollback; reverting `bridgeMint`; initialization, configured asset, address/admin changes. |
| Helpers and inherited dependencies | `BridgeHelper`, beacon/proxy deployment, modifiers, encoding, and inherited token behavior: establish required metadata, encoding, uniqueness, initialization, caller guards, and storage context at their callers. |

Observed source details that affect the statements: withdrawal replay protection
is in the interop handler's `bundleStatus`; the old `L1Nullifier` withdrawal
mapping is deprecated. L1 `bridgedOut` is aggregate accounting, and L2 tracker
sentinel balances are not literal custody balances. Base-token holder operations
can move value into or out of a reserve; VM balance changes need their own
semantics. Native deposit balance-delta checks and arbitrary outgoing transfer
behavior require separate treatment.

## 5. Assumptions and dependency closure

For every dependency, record its provider, required guarantee, evidence, and
remaining trust. Bridge-facing assumptions must be explicit even when broader
verification is later scope.

Use the layered [assumption register](ASSUMPTIONS.md) for stable dependency IDs
and current claim mappings. Keep VM rules, Solidity constructs, compiler/artifact
identity, contract representation, external dependencies, cryptography/evidence,
and operational progress separate. A model choice such as `Option` rollback or
fresh zero storage is not a discharged concrete execution obligation. The
[code-generation proposal](CODE_GENERATION.md) records the alternative of emitting
Solidity from a restricted Lean contract language, with shared/differential tests
and a separate translation-preservation obligation.

| Dependency | Required bridge guarantee |
|---|---|
| Interop center, flow manager, handlers | Preparation precedes publication; committed bytes equal executed bytes; caller/source/destination identities and replay gates are authentic; rollback and execution/recovery evidence are exclusive. |
| Bridgehub, message/root verification, settlement, clocks | Accepted messages and statuses are authentic for the stated chain and transaction; roots, history, and deadlines support the selected evidence branch. State source-chain execution and chain-admission assumptions. |
| Tokens and custom handlers | Exact supported balance/custody semantics, failure behavior, supply rules, and callback model. Prove standard implementations; classify other assets by required interface laws. |
| Governance, proxies, upgrades, pause, registration | Identify transitions that preserve pending obligations. Make trusted exceptions explicit; arbitrary code replacement cannot support unconditional fund-safety claims. |
| Execution environment | Revert/call semantics, native balances, available gas, and VM behavior. Separate safety under failed calls from progress requiring successful calls. |

Commitment authenticity does not prove honest execution on an arbitrary malicious
registered source chain. State whether a result assumes correct source execution,
proves local damage containment, or relies on chain-admission trust. A pause may
preserve funds while preventing progress. Settlement, governance, generic message
passing, and unrelated contracts may remain later scope, but their bridge-facing
assumptions must already be visible.

## 6. Local proof structure and evidence

Use the contract-centered layout:

```text
EraSpec/Contracts/<SolidityName>/
  Specs/          states, guards, transitions, dependency interfaces
  Properties/     authoritative named propositions
  Proofs/         checked proofs of those same propositions
  README.md       source and entry-point map, assumptions, status
EraSpec/Core/     foundations without a corresponding Solidity owner
EraSpec/Protocol/ cross-contract and multi-chain composition
EraSpec/Examples/ illustrative models, separate from production models
```

Create a contract module when there is a real modeled and proved slice. Keep
planned statements in this plan and review notes; do not create placeholder proofs.
For each slice, maintain three forms of evidence:

1. **Reviewed specification:** source pin, entry points, owned state, permitted
   interference, dependency laws, and intended behavior.
2. **Abstract proof:** checked proof of the full named property, with each
   undischarged dependency visible as an assumption.
3. **Implementation correspondence:** evidence that the pinned source implements
   the same model, including relevant success/failure paths, state representation,
   external calls, and configuration.

Implementation correspondence remains open until established locally. Neither
historical theorem counts nor an abstract proof imply it. Review specification
statements before proofs: identify the excluded failure, inputs and callers,
permitted interference, dependency assumptions, a successful execution witness,
and a counterexample when a key guard is removed. A green build checks proof
integrity, not route completeness or model adequacy.

## 7. M0–M7 roadmap

| Milestone | Concrete deliverable | Review checkpoint |
|---|---|---|
| **M0 — Scope and source inventory** | Pin sources and tools; create route × asset × VM register; map entry points, state owners, and dependencies; identify reusable local results. | Are any fund-moving or configuration paths missing? |
| **M1 — First backed outgoing transfer** | `BridgedStandardERC20.bridgeBurn` effects → vault representation preparation/data → router indirect call → center/manager publication. Start with the initialized nonlegacy branch and prove the first B1/B2 chain, including rollback and unique backing. | Does a published bridge call certify the matching burn? |
| **M2 — Destination delivery** | Authorized router/vault mint path, exact amount/recipient/asset, replay consumption, and external-call/revert semantics. Compose one real bridged-ERC20 transfer. | Can a path mint without funded obligation or mint twice? |
| **M3 — Recovery and atomic evidence** | Source refund, local replay, failure/timeout evidence, execution/refund exclusivity across snapshots, supported timeout branches, and partial-recovery limits. | Can delivery and refund both succeed, or funds become terminal but unpaid? |
| **M4 — Native custody and L1 routes** | Native ERC20 escrow/release, `bridgedOut`, L1 deposit/result/failure records, withdrawals, token-delta assumptions, and tracker composition. | Does every route preserve actual backing? |
| **M5 — Base and wrapped assets** | Reserve/native-value accounting, holder/tracker and base-token implementations, wrapping/unwrapping, route restrictions, and failure behavior. | Are reserves and wrappers counted exactly once? |
| **M6 — Configuration and legacy coverage** | Registry/deployment/init/reinit, beacon/proxy assumptions, legacy fallback, Era/OS variants, migration/backfill, and pause/admin transitions. | Are pending obligations preserved across every permitted transition? |
| **M7 — Whole-bridge composition** | Arbitrary interleavings, repeated/multi-hop transfers, multiple assets/chains, conservation/solvency, conditional delivery/recovery, and closed dependency register. | Which exact deployed configurations and trust assumptions does the result cover? |

The dependency register starts in M0 and expands as source paths are modeled. M1
is the first selected slice; its initialized nonlegacy branch must remain labeled
as such until legacy fallback and configuration transitions are covered.

The token-ledger substep of M1 now has local specifications and proofs:
exact mint/burn effects and authority, accounting and uint256 bounds over arbitrary
allowed traces, self-transfer behavior, failure guards, and an executable mint/burn
witness. The registered representation branch of vault preparation now has exact
burn, asset/returned-data binding, guard, dependency, and modeled rollback proofs.
The preparation trace also proves supply plus pending-value conservation and
prepared-data persistence across repeated preparations and ordinary transfers.
Its pending list is ghost bookkeeping, not vault storage. Router/publication
binding, protection against reuse of returned data, and source correspondence
remain open; the complete M1 guarantee is not yet proved.

The initialization base case now projects the fresh-proxy initializer and the
vault's checked deployment/registry-install sequence. It proves ledger validity
and agreement of the tracked representations without assuming prior agreement.
Ledger validity and representation consistency are also preserved independently
by preparation. The initialization-to-preparation theorem carries them through a
local token-operation phase and preparation/spending traces. Proxy freshness,
resolved origin-chain input, encoder/deployer/tracker dependencies, source
correspondence, and global no-alias properties remain explicit boundaries.
