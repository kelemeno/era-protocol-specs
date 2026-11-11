# Assumption layers and proof boundaries

We prove contract and protocol properties against explicit lower-layer
interfaces. We must distinguish the rules of execution, the correctness of a
particular contract, and the conditions under which that contract can make
progress. This register starts with the current asset-bridge slices; it is not
yet an exhaustive classification of every historical theorem.

**No project axioms does not mean no assumptions.** The axiom audit checks logical
dependencies. Theorem hypotheses, restricted transition systems, abstract data
representations, and unproved connections to deployed code need separate review.

## Layers

| Layer | Responsibility | Current evidence here |
|---|---|---|
| Logic | Lean's kernel and the admitted logical principles | Checked proofs; the audit permits only `propext`, `Quot.sound`, and `Classical.choice`. Lean and Mathlib revisions are pinned. |
| VM | Storage, call frames, caller identity, value, rollback, deployment, and execution resources for a specific VM/version | No concrete VM semantics or VM-to-model proof in this package. |
| Solidity | Meaning of source constructs: arithmetic, ABI, modifiers, calls, exceptions, and evaluation order | Source-review obligations; no formal Solidity interpreter here. Library code, including OpenZeppelin initializers, is contract code to verify. |
| Build and artifact | The selected compiler preserves source behavior, and the deployed artifact/configuration is the one reviewed | Source pin recorded; compiler preservation and deployment identity remain open. |
| Contract representation | Actual storage and entry-point executions correspond to the local contract model | Local model proofs exist. Concrete correspondence remains open. |
| Contract composition | A dependency supplies precisely the behavior required by its caller | Some local components compose; real external-call/frame behavior remains open. |
| Protocol and environment | Authenticated cross-chain evidence, cryptographic binding, permitted configuration changes, and progress | Conditional abstract results and explicit open obligations; no whole-bridge closure. |

These are a dependency graph. A balance-update lemma does not require chain
finality or compiler correctness to be true about its Lean definition. Applying
that lemma to a deployed bridge requires the particular paths connecting that
artifact to that definition. Each chain can select a different VM profile.

## How to record a dependency

Use the IDs below in the contract README and relevant specification comments.
For each claim, record the provider, exact required law, scope/version, evidence,
and remaining obligation. Classify each item as one of:

- **Trusted foundation:** accepted outside this proof, such as the selected
  platform executing its specified semantics. State the trust explicitly.
- **Theorem premise:** a visible Lean hypothesis, with a provider theorem when
  discharged by another component. A success equation is a premise about that
  call, not an assumption that every call succeeds.
- **Model boundary:** behavior fixed or omitted by the definitions. It requires
  correspondence or an explicitly restricted claim when applied to real code.
- **Open correspondence:** a precise implementation obligation still to prove
  or review. Do not silently treat it as an established fact.
- **Proved:** a locally checked result with a reference to its theorem and scope.

An obligation may be proved at one level while its connection to deployment is
open. For example, initialization proves representation consistency in the local
model; it does not establish that an actual proxy starts in that model's state.

## Layer register

### VM, language, and build

| ID | Required law / evidence to supply | Status |
|---|---|---|
| `VM-STORAGE` | Storage words, fresh allocation, address separation, and persistent-state effects match the chosen execution profile. | Open concrete connection. `freshProxy` is currently a model definition. |
| `VM-CALL` | Caller, execution address, storage context, value, static calls, and proxy/delegate execution have the modeled meanings. | Open; track per call path. |
| `VM-REVERT` | A failed frame restores its state-changing effects, including those of its subcalls. Establish which caller frames also revert and which catch/continue. | Open concrete connection. The model's `Option` commit rule is separate. |
| `VM-DEPLOY` | Freshness, deployment success, resulting code, and address derivation for the selected VM. | Open; no generic Ethereum CREATE2 formula assumed for all chains. |
| `SOL-ARITH` | Each operation uses the intended width, conversion, checked/unchecked behavior, and established range bounds. | Token bounds are proved in the abstract model; source-operation correspondence is open. |
| `SOL-ABI` | Input/output decoding, byte layout, hashing preimages, and decoding failures match typed model values. | Open. `MintData` and `List UInt8` do not prove an ABI layout. |
| `SOL-CONTROL` | Modifiers, evaluation order, high/low-level call results, and try/catch follow the chosen source semantics. | Open source correspondence; initializer guards are library behavior, not a language guarantee. |
| `BUILD-PRESERVATION` | Exact solc/zksolc versions, optimizer, target, libraries, and relevant flags preserve the source semantics used. | Not proved here; pin and explicitly trust or discharge this boundary for a concrete claim. |
| `GEN-EMIT` | Solidity printed by `EraSpec/Codegen/Emit.lean` behaves as `Codegen.call`/`Codegen.deploy` say: one construct, one line (the table in `Emit.lean`), with mixed checked/unchecked statements and panicking error arguments refused. | **Trusted**, not proved — no Solidity semantics here. Evidence: `solc` type-checks every output, `scripts/emit-solidity.sh --check`, and Lean-interpreter-generated vectors replayed in `solidity/` (960 calls, all agreeing). |
| `BUILD-IDENTITY` | Full source/dependency pins and build inputs identify the runtime code, proxy/beacon implementation, initialization data, and configuration being verified. | Source context pinned at `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`; no deployed-artifact claim yet. |

Solidity's documented distinction between propagated exceptions and caught or
low-level failures is essential to `VM-REVERT`/`SOL-CONTROL`: a failed subcall
does not by itself imply that its caller's earlier writes disappear.
See [Solidity error handling and arithmetic](https://docs.soliditylang.org/en/v0.8.28/control-structures.html).
This documentation version is a reference, not a claim about the compiler used
by a particular deployment.

Choose an explicit VM and protocol version before discharging these laws.
Native EraVM deployment and address derivation differ from Ethereum; the EVM
interpreter is another execution profile. See
[ZKsync's VM differences](https://docs.zksync.io/zksync-protocol/era-vm/differences/evm-instructions).

### Model choices and contract correspondence

| ID | Existing model boundary | Obligation for a concrete claim |
|---|---|---|
| `MODEL-LEDGER` | Token balances are `Address → Nat`, with a finite mathematical sum over all 160-bit addresses and a supply bound. | Relate these values to actual mapping slots and uint256 operations; the sum is a ghost invariant, not a runtime loop. |
| `MODEL-FRESH` | `freshProxy` has version 0 and an empty token ledger; the implementation has disabled version 255. | Justify the allocated proxy's relevant initial storage and the modeled initializer context. |
| `MODEL-COMMIT` | `transact` commits only `some`; on `none` it returns the original projected state. | Connect each modeled failure to the correct concrete reverting/caught frame. |
| `MODEL-TRACE` | Preparation appends one ghost obligation; ordinary transfer preserves pending entries. These are the only trace steps. | Show production publication creates that same obligation once; include or frame every other permitted action. No delivery/refund theorem follows from this trace alone. |
| `REP-TOKEN` | The initialized nonlegacy token branch has modeled mint/burn/transfer behavior. | Per-entry-point state/input/output correspondence, authority, arithmetic, inherited hooks, and failure paths. Allowance, legacy, and upgrade paths need their own coverage. |
| `REP-INIT` | Vault registration allocates, initializes with the vault caller, checks the address, installs both registry maps, then calls the tracker. | Match the actual allocation/caller/control flow, resolved origin, independently stored fields, and omitted origin/index/count writes. |
| `REP-VAULT` | Preparation selects the tracked token, checks the reverse map, accounts before burn, and reads origin/metadata after burn. | Match the real branch, exact calls and ordering, concrete payload bytes, state frame, and propagated failures. |
| `REP-PUBLISH` | Pending entries pair the returned mint tuple with outer destination/asset context. | Match router/center publication, authentication, and replay identity; these are not fields of the returned tuple. |
| `MODEL-ESCROW` | `Contracts.NativeTokenVault` treats `escrowed` (the token's balance of the vault) as an exact counter. A fee-on-transfer or rebasing token is outside the model. The aggregate `bridgedOut` ledger has no chain index. | Relate `escrowed` to the token's actual balance; `_depositFunds` rejecting fee tokens is part of that. `PerChainIsolationFails` states the aggregate-only boundary. |
| `MODEL-ROWS` | `Contracts.ProxyUpgrade` models a revert as the absence of a step. Admin ownership is fixed configuration. The live implementation is one mapping, read as if each row names the admin that actually administers its proxy. `callInitializeUpgrade` and events have no effect. The source is a snapshot of a moving branch outside the source pin (PROVENANCE.md). | Re-check the snapshot against the current library before use. Connect the mapping to `getProxyImplementation` reads and the revert to the actual call frames. |

`EraSpec/Refinement.lean` retains the existing O1–O7 obligation names. Their
primary representation owners are: O1 tree storage/updates, O2 insertion guards,
O3 bounded search, O4 manager transitions, O5 caller authority, O6 source-chain
binding, and O7 root correspondence. They require the applicable VM, language,
build, dependency, and cryptographic laws above; naming an obligation does not
discharge it.

### Dependencies, evidence, and operations

| ID | Required law | Current boundary |
|---|---|---|
| `DEP-FRAME` | A dependency's calls/callbacks can change only the modeled state, or all further effects are represented and preserved. | Hook types restrict writes to `Accounting`; that restriction is not a proof about real callbacks or reentrancy. The token getter is a local field read. |
| `DEP-RESULTS` | The particular dependency results required for enabledness are available. Concrete tokens, deployers, metadata, encoders, and trackers meet their declared interfaces. | Success equations are explicit premises of enabledness results. Safety conditional on successful preparation does not assume every hook succeeds or has correct economic accounting. |
| `CRYPTO-BINDING` | Encodings are unambiguous and the hashes used by the claim bind the relevant inputs/domains. | Conditional mathematical results exist. Concrete cryptographic interpretation remains separate. |
| `CRYPTO-ID` | `IdAssumptions` in `Contracts.NativeTokenVault` and `Contracts.AssetRouter` is a theorem premise. It asserts that the asset-id encoding is injective on all 256-bit (chain, token) pairs or (chain, sender, data) triples, and never zero. | **Unsatisfiable as stated.** No function from pairs of 256-bit words to 256-bit words is injective, so every property taking this premise holds vacuously. That is twelve vault properties, including both countermodels, and the router's `NoHijack` and `NtvTouchesOnlyItsOwnIds`. Restating them with a bounded or reduction-style premise is open. |
| `PROTO-EVIDENCE` | Evidence authenticates the correct source/destination, commitment, settlement layer, history, deadline, and finality. A source chain supplies the funded preparation being authenticated. | Abstract interop results are conditional. An authenticated commitment alone does not establish honest execution on an arbitrary admitted chain. |
| `OPS-CONFIG` | Actual initialization, upgrades, registry changes, pause/admin actions, and dependency selection stay within the verified transition system or preserve its invariants. | Most such transitions are outside the current trace. Fixed config is a model boundary, not a theorem about arbitrary upgrades. |
| `OPS-PROGRESS` | Required gas/resources, usable dependencies, submissions, inclusion, and chain progress are available. | Needed for deliverability/eventual completion, not silently assumed by a safety proof conditional on success. |

Some historical Merkle results assume *global* pair-injectivity of a
`UInt256 × UInt256 → UInt256` hash. That premise cannot hold for a concrete
256-bit hash on its full domain. A checked implication with that premise is not
by itself a concrete security guarantee. Prefer the existing restricted-pair
results where applicable, and ultimately state a collision-finding reduction or
an explicitly bounded no-collision premise for the values the proof compares.
Do not relabel global injectivity as a proved property of Keccak. The ported
vault and router models carry the same kind of premise: see `CRYPTO-ID`.

## Current bridge claims and their dependencies

These rows distinguish what is proved *inside the model* from the additional
work needed to apply it to a deployed artifact. They are a manual register;
the axiom checker does not infer or validate this mapping.

| Claim | Visible premises and model scope | Additional concrete connection |
|---|---|---|
| Token `burn_exact` | Successful modeled burn plus `WellFormed`; ledger bounds and exact debit/supply effect are derived. | `MODEL-LEDGER`, `REP-TOKEN`, relevant `VM-*`, `SOL-*`, and `BUILD-*`. |
| Vault `registration_establishes_representation` / `registration_establishes_ledger` | Successful modeled registration; no prior ledger/registry agreement premise. Uses `MODEL-FRESH` and the projected install sequence. | `REP-INIT`, `VM-STORAGE/CALL/DEPLOY`, `SOL-CONTROL/ABI`, dependency frames, and build identity/preservation. |
| Vault `preparation_backed` | `WellFormed` and successful modeled preparation. Universally quantified over the hook functions of the stated type. | `REP-TOKEN`, `REP-VAULT`, `DEP-FRAME`, ledger representation, call/ABI/arithmetic/build connections. |
| Vault `failed_preparation_atomic` | `prepare = none`; result follows from the definition of `transact`. | `MODEL-COMMIT`, `VM-REVERT`, `SOL-CONTROL`, and actual call/frame coverage. |
| Vault `preparation_enabled` | Named guards, sufficient balance, valid identity/origin, and explicit successful account/metadata equations. | The same representation/call connections plus `DEP-RESULTS` and execution resources. It does not prove eventual submission. |
| `Codegen.BridgedTokenSlice.mint_refines` / `burn_refines` / `transfer_refines` | `WellFormed` model state, `Rel` between interpreter storage and it, ABI-valid arguments. Both directions: model rejection iff revert; acceptance gives a related state, exact logs and return value. | `GEN-EMIT` for the generated contract; then `BUILD-*`, `VM-*`. Says nothing about the original contract (`REP-TOKEN` stays open; see `solidity/README.md` for test evidence). |
| `Codegen.BridgedTokenSlice.reachable_ledger` | A nonzero-vault deployment; any sequence of successful ABI-valid calls. Transferred from the model by `safety_transfer`. | As above. |
| `initialized_preparation_trace` | Successful registration, a local token-operation funding phase, and the closed preparation/spending trace. Derives both invariants and supply-plus-pending conservation. | All participating representation obligations, `MODEL-TRACE`, `REP-PUBLISH`, and `OPS-CONFIG`. Funding authorization/backing for the initial mint phase remains separate. |
| `Contracts.NativeTokenVault.Solvency` / `RunValid` / `NoInflation` | Any run of the registry-and-escrow model from fresh storage, with `IdAssumptions` and a nonzero chain id. | Vacuous as stated (`CRYPTO-ID`). Otherwise `MODEL-ESCROW`, registry and ledger representation, and `OPS-CONFIG`. Separate from the `NativeTokenVaultBase` preparation model. |
| `Contracts.AssetRouter.NoHijack` | One modelled `_setAssetHandlerAddressThisChain` call by a non-vault caller, with `IdAssumptions`. | Vacuous as stated (`CRYPTO-ID`). `OnlyTrackerOrNtvWrites`, `FreshIdNeedsNtv`, and `RunValid` do not use the premise. Router storage and call correspondence are open. |
| `Contracts.ProxyUpgrade.AppliedGatePasses` | `validateRows` holds, no row is left to a foreign admin, and there is an explicit frame premise that nothing moved the rows' proxies between apply and check. | `MODEL-ROWS`. The frame premise is `OPS-CONFIG`: any `ProxyAdmin` owner can break it. The model describes a snapshot of a moving branch. |

Read the authoritative statements in
[token properties](EraSpec/Contracts/BridgedStandardERC20/Properties/Model.lean),
[vault registration properties](EraSpec/Contracts/NativeTokenVaultBase/Properties/Initialization.lean),
[vault preparation properties](EraSpec/Contracts/NativeTokenVaultBase/Properties/RepresentationPreparation.lean),
and [initialization-to-preparation composition](EraSpec/Protocol/AssetBridgePreparation/Properties/Initialization.lean).

## Composing proved boundaries

[Core/Simulation.lean](EraSpec/Core/Simulation.lean) supplies generic checked
composition, with no VM or Solidity dependency:

1. A relation connects a concrete state to an abstract state.
2. Each concrete step is matched by zero or more abstract steps.
3. `Simulation.comp` composes two such boundaries.
4. `safety_transfer` transfers a reachable-state predicate, given related initial
   states, an abstract safety proof, and a relation that reflects that predicate.

There are currently **no concrete VM, Solidity, or compiler simulation instances**.
The one concrete instance is one level up: `Codegen.BridgedTokenSlice.simulation`
relates the `Codegen` *interpreter* to the token model. Its connection to
Solidity is `GEN-EMIT`, which is trusted.
An actual instance must prove the per-step obligation; there is no global
`EVMCorrect` or `SolidityCorrect` axiom. Explicit initial-state witnesses prevent
an empty relation from establishing a deployment claim.

Forward simulation alone permits an always-reverting implementation and abstract
stuttering. Enabledness, liveness, and preservation of observable calls/returns
need further obligations. History-dependent claims require traces/ghost history
in the states or a richer observation relation. Do not use this state-only
foundation to claim byte-for-byte ABI/event equivalence.

The proposed [Lean-to-Solidity generation and shared tests](CODE_GENERATION.md)
would be another way to discharge specific correspondence boundaries. It would
not remove the VM, artifact, dependency, or environmental layers.
