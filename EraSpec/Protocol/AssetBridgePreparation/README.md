# Asset bridge preparation trace

This protocol slice composes the local
[NativeTokenVaultBase preparation model](../../Contracts/NativeTokenVaultBase/README.md)
with ordinary source-token transfers. Its `pending` list is ghost trace bookkeeping:
it is not vault storage and does not prove that any router or interop center
published the prepared data.

The [assumption register](../../../ASSUMPTIONS.md) distinguishes `MODEL-TRACE`
and `REP-PUBLISH` from the token/vault laws being composed. `OPS-CONFIG` records
the need to include or frame other production transitions; progress has the
separate `OPS-PROGRESS` boundary.

| Review | File |
|---|---|
| Trace state, preparation/spend steps, reachability, and pending-value fold | [Specs/Model.lean](Specs/Model.lean) |
| Reachable conservation, initial backing, and persistence properties | [Properties/Model.lean](Properties/Model.lean) |
| Checked trace-property derivations | [Proofs/Model.lean](Proofs/Model.lean) |
| Initialization-to-preparation composition statement | [Properties/Initialization.lean](Properties/Initialization.lean) |
| Checked initialization composition | [Proofs/Initialization.lean](Proofs/Initialization.lean) |
| Trace with token version and metadata, reinitialization steps, `PendingNamesToken` | [Specs/Reinitialization.lean](Specs/Reinitialization.lean) |
| Conservation, persistence, pending-asset binding, registration-to-trace composition | [Properties/Reinitialization.lean](Properties/Reinitialization.lean) |
| Checked reinitialization derivations and concrete witness | [Proofs/Reinitialization.lean](Proofs/Reinitialization.lean) |
| Per-destination pending total | [Specs/RegistryCorrespondence.lean](Specs/RegistryCorrespondence.lean) |
| The trace against the registry model's flow audit | [Properties/RegistryCorrespondence.lean](Properties/RegistryCorrespondence.lean) |
| Checked registry-correspondence derivation and witness | [Proofs/RegistryCorrespondence.lean](Proofs/RegistryCorrespondence.lean) |
| Two-chain trace: source and destination vaults, delivery and refund steps, the two local records, the evidence gate, accounting sums | [Specs/Resolution.lean](Specs/Resolution.lean) |
| Per-chain books, exact accounting, at most once, never both, conservation, refund enabledness, commutation, two countermodels | [Properties/Resolution.lean](Properties/Resolution.lean) |
| Checked two-chain derivations and concrete runs | [Proofs/Resolution.lean](Proofs/Resolution.lean) |
| The evidence gate instantiated with the atomic-interop gate and refund path, and with the multichain gate | [Specs/ResolutionEvidence.lean](Specs/ResolutionEvidence.lean) |
| Conservation or a located break under the atomic-interop evidence; the bound and unbound multichain gate | [Properties/ResolutionEvidence.lean](Properties/ResolutionEvidence.lean) |
| Checked instantiations and witnesses | [Proofs/ResolutionEvidence.lean](Proofs/ResolutionEvidence.lean) |
| Full recovery: `AssetRouterBase` `AtomicRecovery`'s refund model with the local token model as the vault's hooks; deposit bundles, credit and tracker runs, `CreditsCovered`, `ExactCredits`, `PendingSound` | [Specs/FullRecovery.lean](Specs/FullRecovery.lean) |
| Terminality against full restoration, exact refund, enabledness, pause, the prepared-bundle headline, three countermodels | [Properties/FullRecovery.lean](Properties/FullRecovery.lean) |
| Checked full-recovery derivations and witnesses | [Proofs/FullRecovery.lean](Proofs/FullRecovery.lean) |

## Pin and headline guarantees

The area composes contract models at two pins:

- **`b17415d20`.** [Model](Specs/Model.lean), [Initialization](Properties/Initialization.lean),
  [RegistryCorrespondence](Specs/RegistryCorrespondence.lean) and
  [Reinitialization](Specs/Reinitialization.lean) compose the `NativeTokenVaultBase` and
  `BridgedStandardERC20` models, which are at `b17415d20`.
- **`c67894b9` records.** [Resolution](Specs/Resolution.lean) cites the `c67894b9` delivery and
  refund paths (`L2InteropHandler.executeAtomicBundle`, `AtomicFlowManager.claimRefund`) for the two
  local records it models. [ResolutionEvidence](Specs/ResolutionEvidence.lean) instantiates the gate
  with `Protocol/InteropAtomicity` and `Protocol/MultichainGate`, and
  [FullRecovery](Specs/FullRecovery.lean) builds on `AssetRouterBase` `AtomicRecovery` /
  `RecoveryLimits`; all of these model `c67894b9`. `b17415d20`'s `AtomicFlowManager` differs, and
  these files have not been re-modelled against it. Their results build on `c67894b9` records and
  are not claims about `b17415d20`, so none is a headline.

These are the area's `@[headline]` statements (see [CONSOLIDATION.md](../../../CONSOLIDATION.md)).
A run is any sequence of successful vault preparations of the tracked token (the `bridgeBurn`
branch), ordinary token transfers and `reinitializeToken` calls by the beacon owner, for any
accounting and metadata hooks. "Well-formed" (`WellFormed`): the token's ledger is well formed
(balances sum to the supply, the supply is below `2^256`, the zero address holds nothing), and the
token's vault and asset id and the vault's registry entries for it agree with the vault's
configuration. The pending list is ghost trace bookkeeping, not vault storage.

| Guarantee | Premises | Statement |
|---|---|---|
| Along any run the vault stays well-formed, supply plus pending value is constant, and neither the vault's configuration nor the token's identity changes | The vault is well-formed at the start | `ReinitTraceConservation` |
| The pending list only grows at its end: nothing replaces prepared data | None | `ReinitTracePreparedDataPersists` |
| Every pending obligation keeps naming the token's starting asset id and origin token | The vault is well-formed and every pending obligation names the token's asset id and origin token at the start | `PendingObligationsKeepTheirAsset` |

Witness (`@[witness]`): `ReinitTraceWitness` (a registration, funding, two preparations and a
reinitialization between them). The [Model](Properties/Model.lean) statements
`reachable_conservation`, `pending_backed_by_initial_supply` and `prepared_data_persists` are the
same facts without reinitialization and stay untagged.

## Allowed trace and context

A trace step either performs a successful vault preparation and appends its exact
returned mint data once, or performs an ordinary successful source-token transfer
while leaving pending entries unchanged. Thus later source transfers are allowed
between preparations. This closed transition system has no independent mint,
refund, destination delivery, router publication, or external-call step.
`Resolution` (below) adds destination delivery and source refund on a second chain;
this closed trace is its source-side fragment (`TwoChainExtendsPreparationTrace`).

Each pending record pairs the returned mint-data tuple with the outer request's
asset ID and destination chain. Those outer fields are trace context; they are not
fields of the mint-data tuple and the trace does not prove they are encoded or
published by production code.

## Proven local targets

- **Local exact burn:** every successful preparation contributes the exact amount
  debited from the depositor and removed from token total supply, by the vault
  preparation property.
- **Pending-value conservation:** from a well-formed starting vault state,
  circulating token supply plus the total pending amount stays constant through
  every reachable preparation and ordinary transfer.
- **Pending value remains initially backed:** when the initial trace has no pending
  records, total pending value never exceeds the initial source-token supply.
- **Prefix persistence:** later preparations and ordinary transfers only append to
  the pending list; previously prepared data is retained unchanged.
- **Reinitialization:** the trace extended with `reinitializeToken` steps by any
  caller (`ReinitReach`) keeps `WellFormed`, circulating supply plus pending value,
  the vault configuration, the token identity, and all previously prepared data
  (`ReinitTraceConservation`, `ReinitTracePreparedDataPersists`; step cases
  `ReinitStepCases`). Every pending obligation keeps naming the token's original asset
  id and origin token (`PendingObligationsKeepTheirAsset`). The existing trace embeds
  unchanged (`TraceRunsEmbed`). Witness: `ReinitTraceWitness`.

These conclusions rely on the vault's `WellFormed` registry and token-ledger
assumptions, and on its modeled accounting hook and `Option` commit behavior. The
trace's conservation proof is a theorem about these abstract transitions, not about
vault storage, EVM rollback, actual publication, or a destination's readiness.

The initialization composition derives the starting ledger and representation
invariants from the successful fresh-registration branch. It then permits a local
token-operation phase to establish nonzero balances before the preparation trace;
otherwise a freshly created zero-supply token could only yield an empty trace.
This theorem has no input `WellFormed` or `RepresentationConsistent` hypothesis.
The token phase permits mint/burn/transfer under the existing token guards; it
does not prove the cross-chain authorization or economic backing of those mints.
`InitializedTraceWithReinitialization` composes the same registration with a funding
phase and a trace that both include reinitializations, again with no input invariant.

## Against the registry model

`TightTraceIsRegistryOutflow` runs the initialization composition starting from the
tightened registration (`registerFreshBranch'`, see the
[NativeTokenVaultBase README](../../Contracts/NativeTokenVaultBase/README.md)). A
bounded registry-model run simulates it:

- the registry vault is the registration's write throughout, and it corresponds to
  the final ledger;
- `Valid` and `WellFormed` hold;
- during the trace the registry records no inflow of the asset, and records exactly
  the pending total as outflow, per destination chain (`pendingAmountTo`).

The registry run is the matching run the simulation builds, so the pending list and
that run's flow audit agree. Other registry runs are not constrained: the registry
model does not bound a bridged asset's flows
(`Contracts.NativeTokenVaultBase.Properties.LifecycleIdentityNotRegistryInvariant`). Token-model
mints and burns carry no chain id, so per-destination outflow is claimed only for
preparations. Neither ghost record is evidence of publication. Witness:
`TightTraceIsRegistryOutflowSatisfiable`.

## Resolution across two chains (`Resolution`, `ResolutionEvidence`)

`Specs/Resolution.lean` keeps a source vault, a destination vault and the trace's
entries in one state (`TwoChainLedger`) and adds two steps. `deliver i wd` is the
destination vault's `bridgeMint` of entry `i`'s data, called by the destination router
(`twoChainDeliveryCall`). `refund i wr` is the source vault's `bridgeRecoverFailedTransfer`
of the same data, called by the source router (`twoChainRefundCall`; for an entry made by
`prepare` it is `NativeTokenVaultBase.recoveryCall`, `TwoChainRefundCallIsRecoveryCall`).
Both are the registered bridged branch of the vault's `Resolution` model. Each step is
guarded only by its own chain's record and by the evidence it consumes:

- `delivered` stands for the handler's `bundleStatus` (`L2InteropHandler.sol:79, 86`);
- `refunded` stands for the manager's `Revertable → Reverted` (`AtomicFlowManager.sol:169-175`);
- `ResolutionGate` is the cross-chain evidence, a lifetime predicate on the witness each
  step consumes. `Sound` says no entry has both a passing delivery witness and a passing
  refund witness; `SoundOrBreak Brk` says `Brk` holds on the two witnesses whenever both
  pass.

Neither step reads the other chain's record. Every result quantifies over the hooks and
the evidence, and none takes a hash premise. `Sound` is a premise of some results below; it
is not a fact about any gate. `ResolutionEvidence` supplies the gate from two existing models.

| Result | Statement |
|---|---|
| `TwoChainSourceBooks`, `TwoChainDestinationBooks` | No evidence premise; the records name existing entries. Source supply plus the amount burned and not refunded is constant (from a `WellFormed` source); destination supply grows by exactly the amount delivered. Each uses only its own chain's record. |
| `TwoChainLedgerExact` | No evidence premise. From a `WellFormed` source whose records name existing entries, circulating supply on both chains plus value in flight changes by exactly the change in `doublePaid`, the amount of the entries both delivered and refunded. |
| `TwoChainReplayCounts` | No premise. In every run the deliveries (refunds) of an entry are counted exactly by the destination's (source's) record, so a run delivers an entry at most once and refunds it at most once, whatever the evidence. |
| `TwoChainConservation`, `TwoChainExclusive`, `TwoChainResolvesOnce` | `Sound` evidence and both records empty at the start (entries may already be pending); conservation also needs a `WellFormed` source. Supplies plus value in flight are constant and `doublePaid = 0`; no entry is both delivered and refunded; each entry is resolved at most once across both chains. |
| `TwoChainDoubleResolutionLocated`, `TwoChainConservedOrBreak`, `TwoChainResolvesOnceOrBreak` | `SoundOrBreak Brk`, records empty at the start: the same conclusions, or the run's own labels deliver an entry with some `wd` and refund it with some `wr`, and `Brk` holds on exactly those two. |
| `TwoChainRefundAvailable` | From a fresh trace (no entries, no records) on a `WellFormed` source: for an entry not yet refunded, a passing refund witness and a returning source hook make the refund step enabled, and it credits the depositor exactly the entry's amount. No step of the trace can block it. This is enabledness in the model; the omitted reject-only checks (below) must pass too. |
| `TwoChainEntriesFromRequests`, `TwoChainResolutionPaysEntry`, `TwoChainEntriesPersist` | From an empty entry list on a `WellFormed` source, every entry records a logged request's destination, asset, depositor, receiver and nonzero amount. Entries are append-only and records only grow. A delivery credits the entry's receiver, and a refund its depositor, exactly its amount, each on its own chain only. |
| `TwoChainResolutionsCommute` | A delivery and a refund enabled at one state stay enabled after each other and commute, also for the same entry: the two records share no lock. |
| `TwoChainExtendsPreparationTrace` | The closed trace above is the source-side fragment of this one, in both directions. |
| `TwoChainConflictingGateDoublePays` | Countermodel: with evidence that accepts both sides (not `Sound`), one entry is delivered and refunded, and the books end its nonzero amount above their start. |
| `TwoChainWithoutRecordsPaysTwice` | Countermodel: with `Sound` evidence but without the two local replay guards, one entry is delivered twice and another refunded twice. Both ingredients are needed. |
| `InteropGateSoundOrBreak`, `InteropTwoChainConservedOrBreak`, `InteropTwoChainResolvesOnceOrBreak` | The atomic-interop evidence (`interopResolutionGate`). A delivery passes when the entry's leg executed through the gate on that evidence (`Contracts.Atomicity.ExecutedViaBy`, the IMT half of `requireFlowFinalized`, over a fixed history `S`). A refund passes on a logged manager run from fresh storage (`Contracts.Refund.ReachLog`) that lifted the leg's obligation past `Committed`. On a `Wf` history, with no hash premise, the gate is sound up to `Contracts.Refund.RefundBreak` on that run's own log: a logged `authorizeRefund` that marked the obligation, with a `FlowIdClash` against the executed flow, or a located tree break on the executed flow's inclusion proof or on the call's own absence proof. So the books balance (and each entry is resolved at most once), or the run delivered and refunded some entry with such a break. Which leg carries which entry is the parameter `route`; the results hold for every binding. |
| `MultichainGateSound`, `MultichainTwoChainConserved` | The multichain snapshot gate with `authorizeRefund`'s source-chain check, every chain's tree `Valid`: sound outright, so the books balance and each entry is resolved at most once. Its absence witness is a genuine leaf (`Contracts.Protocol.AbsenceWitnessAt`). At `c67894b9` the checked `verifyNonInclusion` also accepts the padding sentinel at an empty slot, which this gate does not cover (Correction (StaleSnapshotFaithful) in `Specs/ResolutionEvidence.lean`); the atomic-interop form above locates that case as a break. |
| `MultichainUnboundGateDoublePays` | Countermodel: without the source-chain check, over valid trees, one entry is delivered and refunded, and the books end its nonzero amount above their start. |

Witnesses:
- `TwoChainSatisfiable`: under the sound `splitResolutionGate 0 1`, two nonzero
  preparations, spending on both chains, entry 0 delivered, and entry 1 refunded from a
  state that meets every premise of `TwoChainRefundAvailable`.
  `TwoChainResolutionsCommuteSatisfiable` meets the commutation's premises.
- `InteropTwoChainSatisfiable`: on the `Wf` `mixedSystem 1`, entry 0 is delivered on honest
  inclusion proofs and entry 1 refunded through a nonempty logged manager run. The books
  balance and the break is false for entry 0, because no logged call marks entry 0's
  obligation (by `InteropGateSoundOrBreak` that is the only way it can be false for a
  delivered entry).
- `InteropTwoChainPaddingDoublePayLocated`: with the pin's padding constant on
  `paddedSystem`, one entry is delivered and then refunded on the forged padding absence
  proof. The books end its amount too high, and the located break is exactly that proof's
  `AbsenceBreak`, with no flow-id clash and no inclusion break.
- `MultichainTwoChainSatisfiable`: over the valid trees of `attackChains v`, one entry
  delivered and another refunded.

Model boundaries (`MODEL-RESOLVE` in `ASSUMPTIONS.md`):
- Records are keyed by entry position. That each burn is published as exactly one bundle
  leg is `REP-PUBLISH`.
- Only the registered bridged branch, on both chains, with the destination router's handler
  for the asset taken to be the vault. Native escrow, the first-bridge deploy, legacy and
  base-token paths and custom handlers are not steps. There is one destination chain.
- Omitted reject-only checks: the handler's pause, source-chain, destination-chain,
  base-token and execution-address checks; the router's sender, selector and base-token
  asset checks (`AssetRouterBase.sol:220-244`; `L2AssetRouter.sol:269, 270, 284-287`); the
  manager's `recovered != 0`. They only remove runs, so the safety results hold with them.
- No other writers: pause, admin and registration actions, other assets, and the
  destination's other mint routes (an L1→L2 deposit finalized through the aliased L1 router,
  `L2AssetRouter.sol:265-274`, or other bundles) are not steps. Destination supply in the
  books moves only by this trace's deliveries.
- The atomic-interop evidence is the fixed-history `System`; a refund witness may be any
  logged manager run, which only adds runs. The multichain evidence is one snapshot.
- Liveness: only refund enabledness is proved. Delivery enabledness and progress
  (`OPS-PROGRESS`) are not.

## Full recovery of router-deposit bundles (`FullRecovery`)

Namespace `AssetBridgePreparation.FullRecovery`. It adds no trace step. It evaluates
`AssetRouterBase` `AtomicRecovery`'s `claimRefund` (the manager's loop, the router's
`recoverAtomicCall`, the vault's `bridgeRecoverFailedTransfer`, unchanged) with the vault's
external effects given by the local token model (`localHooks`): a re-mint is
`BridgedStandardERC20.mint` with the vault as caller; a native release is the base-asset
check followed by `transfer` from the vault; the tracker hook (`_handleBridgeFromChain`) and
the first-bridge deploy hook are parameters. Every result starts from a `Revertable` leg;
how the leg got there (`authorizeRefund` and its timeout evidence) is not composed here. No
result takes a hash premise.

| Result | Statement |
|---|---|
| `TerminalIsFullIffNoDecline`, `FullAcceptanceIffAllRecovered` | For any per-call behaviour, a successful claim (the leg is then `Reverted`) recovered every call iff no call returned `false`. |
| `DepositBundleNeverDeclines`, `DepositBundleClaimIsFull` | No premise on hooks, assets or data. A bundle whose calls all target the router with `finalizeDeposit` data never declines, so each successful claim of it recovers every call. |
| `DepositRefundIsCredits`, `DepositClaimIffCredits` | Vault unpaused, every deposit's asset in the registry, local token model: the loop is exactly the tracker run and the credit run in bundle order. The claim succeeds iff the bundle is nonempty and both runs succeed, and its world is exactly the credited one. |
| `CreditsCoveredSucceedExactly`, `CreditsPreserveLedgers`, `TrackerAlwaysReturnsRuns` | Under `CreditsCovered` (nonzero vault and original callers, the base-asset exclusion, escrow covering each native token's releases, the vault as minter of each bridged token with headroom for the bundle's total on it), the credit run succeeds with exact per-token and per-account totals (`ExactCredits`). Every credit run keeps ledgers well-formed. A tracker that returns on every deposit makes the tracker run return. |
| `RegisteredDepositBundleFullyRecovered` | World-level headline, native and bridged assets. Premises: a nonempty deposit bundle on registered assets, an unpaused vault, a returning tracker run, `CreditsCovered`. The claim succeeds with `recovered = callsLen`; the ledgers are exactly `ExactCredits` and stay well-formed; the router's maps, the registry and the pause flag are unchanged. |
| `PausedVaultBlocksDepositClaim`, `PauseOnlyDelaysFullRecovery` | While the vault is paused, every claim of a nonempty router-deposit bundle reverts, whatever the hooks, so the leg stays `Revertable`. Under the headline's premises the same world unpaused recovers in full. |
| `PendingObligationsSound`, `PreparedBundleFullyRecovered` | Trace headline, bridged representation only. A preparation trace (`Specs/Model.lean`) from a `WellFormed` vault with nothing pending; router-deposit calls carrying a nonempty sub-multiset of its pending obligations; a world whose registry is `Corr`-related to the trace's vault, whose ledger of the tracked token is the trace's token, with the vault unpaused and a returning tracker run. The claim recovers every call, each depositor gains exactly what the bundle owes it, supply rises by the bundle's pending total, and supply plus what is still pending equals the supply before the trace. The supply headroom is derived from the trace's conservation, not assumed. |
| `DecliningCallMakesTerminalPartial`, `NonStandardTokenCountedButNotCredited`, `JointHeadroomNeeded` | Countermodels: a call to another target that returns `false` leaves a terminal leg with one call of two unrestored; a mint hook that is not the token model's counts a call as recovered while crediting nothing; per-call supply headroom is not enough for a bundle. |

Witnesses: `FullRecoverySatisfiable` (a two-call atomic bundle, one native and one bridged
deposit with nonzero amounts, a tracker that changes state, and the paused copy of the same
world) and `PreparedBundleFullyRecoveredSatisfiable` (two preparations by two depositors,
both carried by the bundle).

Boundaries (`MODEL-FULL-RECOVERY`):
- A deposit call targets the router, which a router-produced call does only for a
  destination other than L1 (`AtomicRecoveryFaithful`).
- Only the tracker run's returning is used; its accounting is not claimed to be restored.
  The hook reads only the tracker's state, while the pin's first-touch legacy registration
  also reads token `balanceOf`/`totalSupply` (`L2AssetTracker.sol:327, 336`); the tracker
  part of the resulting world is a model abstraction.
- `onlyNTV`'s lazy initialization of an unset `nativeTokenVault` is not modelled, so such
  tokens are outside `CreditsCovered`. Native tokens are read as standard ERC20 tokens
  (`MODEL-ESCROW`).
- The trace headline takes `Corr` as a premise; its composition with registration
  (`TightTraceIsRegistryOutflow`) is not written. Native escrow preparation has no model.
- At-most-once refund rests on the leg state and is not re-proved here. Custom-handler
  assets and direct calls are outside the premises (`AtomicRecovery`).

## What remains open

Unique resolution and delivery/refund exclusion are proved for the two-chain trace in
`Resolution`, from the two local records and sound (or located-break) evidence. Router
correspondence, publication of each burn as exactly one leg, several destination chains,
and completion of M1 remain open. Nothing here shows that a production router cannot
publish the same data twice. See the [refinement obligations](../../Refinement.lean) and
the [full asset-bridging plan](../../../ASSET_BRIDGING_VERIFICATION_PLAN.md) for the
separate open work.
