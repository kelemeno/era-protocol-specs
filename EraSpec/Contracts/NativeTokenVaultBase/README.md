# NativeTokenVaultBase

These local models cover a fresh representation-token registration projection,
one `NativeTokenVaultBase.bridgeBurn` case (one already registered token on the
non-base, non-native branch), the destination `bridgeMint` and
`bridgeRecoverFailedTransfer` on the registered bridged and first-bridge branches,
the legacy zero-vault token, and the tracked token's `reinitializeToken`. They build
on the local [BridgedStandardERC20 models](../BridgedStandardERC20/README.md).
They are abstract specifications and do not establish Solidity correspondence.

Review the [layered assumption register](../../../ASSUMPTIONS.md) alongside these
models: `REP-INIT`/`MODEL-FRESH` for registration, `REP-VAULT`/`DEP-FRAME` for
preparation, `MODEL-COMMIT`/`VM-REVERT`/`SOL-CONTROL` for rollback, and
`DEP-RESULTS` for enabledness. Generic safety-refinement composition does not
discharge these concrete obligations.

| Review | File |
|---|---|
| Fresh deployment, initializer, registry installation, and tracker-hook sequence | [Specs/Initialization.lean](Specs/Initialization.lean) |
| Registration invariants, fields, map frame, and hook properties | [Properties/Initialization.lean](Properties/Initialization.lean) |
| Checked registration derivations | [Proofs/Initialization.lean](Proofs/Initialization.lean) |
| Request/state, registry maps, hooks, branch selection, and preparation order | [Specs/RepresentationPreparation.lean](Specs/RepresentationPreparation.lean) |
| Preparation payload, accounting, ledger, and failure properties | [Properties/RepresentationPreparation.lean](Properties/RepresentationPreparation.lean) |
| Router, pause, amount, and asset guard properties | [Properties/PreparationGuards.lean](Properties/PreparationGuards.lean) |
| Checked preparation derivations | [Proofs/RepresentationPreparation.lean](Proofs/RepresentationPreparation.lean) |
| Checked guard derivations | [Proofs/PreparationGuards.lean](Proofs/PreparationGuards.lean) |
| Registry-wide asset registry and escrow ledger (separate model, namespace `Contracts.NativeTokenVault`) | [Specs/RegistryAndEscrow.lean](Specs/RegistryAndEscrow.lean) |
| Registry coherence, solvency, net-flow, and two boundary countermodels | [Properties/RegistryAndEscrow.lean](Properties/RegistryAndEscrow.lean) |
| Checked registry and ledger derivations | [Proofs/RegistryAndEscrow.lean](Proofs/RegistryAndEscrow.lean) |
| Correspondence relation between the two models (no new transitions) | [Specs/ModelCorrespondence.lean](Specs/ModelCorrespondence.lean) |
| Agreement, guard gap, invariant agreement, four disagreement countermodels | [Properties/ModelCorrespondence.lean](Properties/ModelCorrespondence.lean) |
| Checked correspondence derivations and witnesses | [Proofs/ModelCorrespondence.lean](Proofs/ModelCorrespondence.lean) |
| Tightened registration (`registerRepresentation'`, `registerFreshBranch'`), source-input premises (`SourceRegistrationInput`, `DeployFresh`), tightened registry model (`RegisterBridgedGuard'`, `Step'`), post-registration runs (`RepStep`), `LifecycleRel` | [Specs/RegistrationUnified.lean](Specs/RegistrationUnified.lean) |
| Guard gap closed: source-input reduction, registry step and `Valid`, exact guard agreement, the four disagreements ruled out, lifecycle simulation and its scope | [Properties/RegistrationUnified.lean](Properties/RegistrationUnified.lean) |
| Checked derivations; `lifecycleSimulation` (a `LayeredVerification.Simulation`) | [Proofs/RegistrationUnified.lean](Proofs/RegistrationUnified.lean) |
| Destination `bridgeMint` and `bridgeRecoverFailedTransfer`: call, hook, branch selection, commit, spending, first bridge | [Specs/Resolution.lean](Specs/Resolution.lean) |
| Exact credit, unread fields, round trip, spending, guards, rollback, limits, first bridge | [Properties/Resolution.lean](Properties/Resolution.lean) |
| Checked resolution derivations and witnesses | [Proofs/Resolution.lean](Proofs/Resolution.lean) |
| Resolution as a registry-model `bridgeIn` (no new transitions) | [Properties/ResolutionCorrespondence.lean](Properties/ResolutionCorrespondence.lean) |
| Checked correspondence derivation and witness | [Proofs/ResolutionCorrespondence.lean](Proofs/ResolutionCorrespondence.lean) |
| The legacy fallback's asset id against the registry model; the deployed preparation of a legacy token (`prepareLegacy`) | [Specs/LegacyFallback.lean](Specs/LegacyFallback.lean) |
| Agreement iff (bounded on two pairs), pinned-break form, countermodel, permanence, native misregistration, preparation reduction | [Properties/LegacyFallback.lean](Properties/LegacyFallback.lean) |
| Checked legacy derivations and witnesses | [Proofs/LegacyFallback.lean](Proofs/LegacyFallback.lean) |
| Tracked token's full storage, metadata-aware preparation hooks, witness vault | [Specs/Reinitialization.lean](Specs/Reinitialization.lean) |
| Reinitialization leaves the vault state and invariants alone; only prepared metadata bytes can change | [Properties/Reinitialization.lean](Properties/Reinitialization.lean) |
| Checked reinitialization derivations and witness | [Proofs/Reinitialization.lean](Proofs/Reinitialization.lean) |

## Two overlapping models

`RegistryAndEscrow` is a separate, older model in its own namespace,
`Contracts.NativeTokenVault`. It is not built on the `Contracts.NativeTokenVaultBase`
models above. It covers the whole registry (`originChainId`, `tokenAddress`,
`assetId` written by `_setNewTokenStorage`), both registration paths, and the
aggregate `bridgedOut` escrow ledger. The ledger hooks themselves are in
`L1NativeTokenVault.sol` at the same pin. The two models overlap on registration
and the registry maps and use different state types. `ModelCorrespondence` relates them on that
overlap (see [below](#how-the-two-models-relate)); results transfer only through
the statements proved there.

Twelve of its fourteen properties take `IdAssumptions e`, whose `inj` field
asserts that `encodeNTVAssetId` is injective on all (chain, token) pairs of 256-bit
words. No function into 256-bit words can satisfy that, so as stated those twelve
hold vacuously, including the two countermodels. Only `EmptyValid` and
`GuardedInflowIsBacked` are free of it. See `CRYPTO-ID` in the
[assumption register](../../../ASSUMPTIONS.md). The model also treats the vault's
token balance as an exact counter (`MODEL-ESCROW`).

The non-vacuous replacements are the `…On` forms, which assume injectivity and
non-zeroness only on an explicit pair set `S`. `LoggedRunSound` supplies `S` for an
arbitrary run. It logs the run (`ReachLog`, with the same reachable states as
`Reach`), takes `S := registeredPairs thisChain log` (the pairs the log's
registrations hash, at most one per step), and concludes `Valid`, `Audited`,
solvency and no-inflation at the end. `LoggedRunSoundSatisfiable` and
`LogAssumptionWeakerThanGlobal` show that the premise holds on a nontrivial run,
including for an encoding that collides off the log.

## Invariants and initialization

The vault state separates `LedgerInvariant` from `RepresentationConsistent`.
`LedgerInvariant` is the token's balance-sum, bounded-supply, and zero-address
condition. `RepresentationConsistent` records agreement of the token's vault and
asset identity with the vault config, plus both directions of the registry maps.
`WellFormed` remains a compatibility bundle of the same five top-level conditions:
the ledger invariant and those four representation relationships. Preparation
assumes this bundle; it does not add a production guard for global consistency.

The registration projection establishes both invariants from a fresh deployment
without assuming prior `WellFormed` state or prior agreement with entries being
installed. Fresh proxy storage starts at initializer version 0; the implementation
is modeled at disabled version 255. Token initialization records its caller as the
vault and has no owner/vault caller guard, so the real vault's internal atomic
deployment sequence must supply the intended caller. Initialization preserves
balances and supply; it does not reset the ledger. The zero ledger follows from
fresh storage. The model proves agreement for this newly installed representation,
not a global no-alias property across all assets and tokens.

Registration's asset encoder and deployer are explicit dependencies. The model
checks the deployed address against the expected configured token address after
token initialization. It installs the forward asset-to-token and reverse
token-to-asset maps before calling the tracker hook. The metadata flag represents
success of outer metadata decoding/setup, not truth of every caught name, symbol,
or decimals getter result. The hook is parametric: this development does not prove
tracker registration, tracker migration, or tracker accounting behavior.

This initialization is a projection, not a proof of the full Solidity deployment
mechanism. The vault's origin-chain mapping, token enumeration/index/count, and
metadata contents remain unmodeled. There is no actual ABI encoding, asset-ID hash,
CREATE2/address derivation, transaction rollback, or proxy execution proof here.
It starts with the resolved origin-chain input to the inner helper; earlier
metadata decoding and chain-ID normalization are not proved. The deploy dependency
supplies a genuinely fresh proxy in the model. Equality of identities alone does
not establish nonzero vault/token addresses or all preparation guards.

## Preparation branch and assumptions

Reviewed source context is era-contracts commit
`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`. `InScope` selects the configured
representation-token case for this model; it is not an additional production
requirement that rejects other routes. The preparation model contains one
registered token. Its forward `tokenForAsset` and reverse `assetForToken` maps are
assumed consistent for that token, and the selected token is assumed to have the
genuine standard-token behavior modeled locally.

Preparation calls the accounting hook before burning. The hook receives the
pre-burn token snapshot together with destination chain, asset, and amount. The
origin-token getter and origin chain are checked after burn; the getter is assumed
to return the genuine standard-token field. Metadata is then read from the burned
token snapshot and remains opaque `List UInt8`, with no ABI/byte correspondence
claim.

The returned mint-data tuple contains original caller, remote receiver, origin
token, amount, and metadata. It does not contain asset ID or destination chain;
those remain outer request context in the separate protocol trace model. The source
does not reject a zero receiver in this branch. Successful preparation therefore
does not establish unconditional destination readiness or any later delivery: no
modelled destination mint accepts receiver `0`, and only recovery can resolve such
a transfer (`ZeroReceiverOnlyRecoverable`).

`prepare` returns `Option`, and `transact` commits only a successful result.
Failure and rollback statements are laws of this abstract interface, including
failures after a tentative accounting update or token burn. They are not a proof
of EVM atomicity, external-call behavior, or concrete tracker semantics.

## Proven local properties and remaining work

The preparation proofs establish exact source-token debit and supply reduction,
payload-field relationships, preservation of other token balances, use of the
pre-burn accounting snapshot, and the modeled failure law. Guard proofs reject a
wrong router, paused preparation, zero amount, and an asset inconsistent with the
assumed well-formed registry. Registration proofs establish ledger and
representation consistency, initial fields, registry map framing, and the tracker
hook snapshot for a successful modeled registration.
The wrong-initializer-caller countermodel produces an inconsistent representation
from a successful public initializer call, showing why the intended vault caller
is essential. Preparation separately preserves `LedgerInvariant` and
`RepresentationConsistent`, without using one as a premise to prove the other.

A `reinitializeToken` of the tracked token changes no slot of the vault model
(`ReinitLeavesVaultStateUnchanged`), so `LedgerInvariant`, `RepresentationConsistent`
and `WellFormed` are kept (`ReinitPreservesVaultInvariants`). The source's metadata
read calls the token's getters, so `MetaHooks` lets preparation see the token's
metadata. A request that prepared before a reinitialization prepares after it to the
same vault state and the same mint data except the metadata bytes
(`ReinitKeepsPreparationExceptMetadata`, `ReinitChangesOnlyPreparedMetadata`;
`VaultReinitWitness`).

Destination execution and refund at the vault, on the registered bridged and
first-bridge branches, are in `Resolution` (below); `VaultHasNoReplayGuard` shows the
vault itself has no replay protection. Router publication, replay protection and
unique resolution across chains, and completion of the first end-to-end bridge
milestone remain open. See the
[asset-bridging verification plan](../../../ASSET_BRIDGING_VERIFICATION_PLAN.md)
and [refinement obligations](../../Refinement.lean) for the broader open work.

## How the two models relate

`Specs/ModelCorrespondence.lean` defines `Corr`: same chain id, the two shared maps
agree pointwise (`tokenAddress[assetId]`, `assetId[token]`, with 160-bit addresses
zero-extended by `widen` and non-address words unset), and, once the registry model
has the tracked asset registered, the same origin chain and origin token for it.
The representation model has no `originChainId` map, so origin data of other
assets is unconstrained.

Proved agreement:

* `RegistrationEffectCorresponds`: a successful `registerRepresentation` writes the
  overlap exactly as the registry model's `registerBridged` does.
* `RegistrationGuardGap`: after a successful `registerFreshBranch` on a
  corresponding state, `RegisterBridgedGuard` holds iff three conditions the
  representation model does not check hold (`RegistryOnlyGuards`: token address
  nonzero, token address not yet mapped, origin chain nonzero). The other three
  registry guards follow from the representation model's checks, given that its
  asset encoder agrees with `e` at the one pair it checks.
* `RegistrationIsRegistryStep`, `RegistrationPreservesValidOn`: with those three
  conditions, the registration is a registry `Step` and carries `Valid` under the
  bounded hash premise `IdAssumptionsOn`.
* `PreparationIsForeignBridgeOut`: under `RepresentationConsistent`, a successful
  `prepare` is a registry `bridgeOut` of a non-native asset, which leaves the vault
  unchanged. Correspondence persists.
* `ValidRegistryHalvesAgree`: under `Valid`, the forward and reverse map conjuncts
  of `RepresentationConsistent` imply each other for nonzero entries.

Disagreements (countermodels, each on a `Valid` corresponding vault with the hash
premise on every pair involved):

| Result | Representation model | Registry model | Source at the pin |
|---|---|---|---|
| `RepRegistrationRebindsLiveToken` | registers at an address already mapped to a live asset; `WellFormed` holds after | `freshToken` guard rejects; the corresponding write breaks `Valid.inverse` | no explicit check in `_ensureAndSaveTokenDeployedInner`; freshness rests on CREATE2 reverting at an occupied address. The representation header says the deploy hook allocates a new proxy, but its type does not enforce it. |
| `RepRegistrationAcceptsZeroOriginChain` | registers with origin chain `0` | `originNonzero` guard rejects; the write breaks `Valid.originIff` | `tokenDataOriginChainId` replaces `0` with `_l1ChainId()` before the inner helper, so the registry model matches when `_l1ChainId() ≠ 0`. |
| `RepRegistrationAcceptsZeroToken` | registers with deployed address `0` | `tokenNonzero` guard rejects; the write breaks `Valid.zeroTokenFree` | CREATE2 deployment never yields address `0` (`Create2.deploy` reverts on it on L1). |
| `RegistryBridgedAcceptsZeroOriginToken` | never registers origin token `0` | accepts it and stays `Valid` | `bridgeInitialize` requires `_originToken != address(0)`, so the representation model matches. |

So each model lacks a condition the source implies. `RegistrationUnified` adds these
conditions alongside the unchanged models, and shows that this closes the gap:

* **The added checks are what the source supplies.** `registerRepresentation'` is
  `registerRepresentation` guarded by the three `RegistryOnlyGuards`
  (`UnifiedIsGuardedRestriction`). On a `SourceRegistrationInput` (`_l1ChainId() ≠ 0`,
  the origin chain resolved by `tokenDataOriginChainId`, and the `VM-DEPLOY` premise
  `DeployFresh`) every successful original registration already satisfies them
  (`SourceInputGivesRegistryOnlyGuards`), so the two registrations coincide
  (`UnifiedAgreesOnSourceInputs`). Each premise is needed
  (`SourceInputPremisesLoadBearing`). `RegisterBridgedGuard'` adds `ot ≠ 0`, which
  `bridgeInitialize` requires.
* **Registration.** A successful `registerFreshBranch'` is a tightened registry step
  and carries `Valid` (under `IdAssumptionsOn`) and `WellFormed`, with no
  `RegistryOnlyGuards` premise (`UnifiedRegistrationIsRegistryStep`,
  `UnifiedRegistrationPreservesValidOn`). Given the dependency results it succeeds iff
  `RegisterBridgedGuard'` holds (`UnifiedRegistrationGuardsAgree`). Without the
  callers' `token == address(0)` test the inner helper can overwrite a live asset
  (`InnerRegistrationNeedsFreshSlot`).
* **The four disagreements.** None has an instance with the primed definitions
  (`UnifiedRegistrationCannotRebindLiveToken`, `UnifiedRegistrationRejectsZeroOriginChain`,
  `UnifiedRegistrationRejectsZeroToken`, `TightRegistryRejectsZeroOriginToken`). No
  tightened registry run records origin token `0` (`TightRunOriginTokensNonzero`, no
  hash premise); an untightened run can (`RunCanRecordZeroOriginToken`).
* **The tracked token's life.** Under `LifecycleRel` (correspondence, `WellFormed`, the
  asset registered and not native, supply + recorded outflow = recorded inflow), each
  preparation or token operation is matched by at most one registry flow step
  (`LifecycleRelIsSimulation`, packaged as `lifecycleSimulation`); registration
  establishes the relation (`RegistrationEstablishesLifecycleRel`), and
  `UnifiedLifecycleCorresponds` extends it to whole runs after a bounded registry run
  from fresh storage. The registry run is the matching run the simulation builds; the
  supply identity is not a registry invariant (`LifecycleIdentityNotRegistryInvariant`).

Model boundaries: `DeployFresh` packages two facts, that CREATE2 reverts at an
occupied address and that every mapped token address is occupied. The second fails
for L1's ETH sentinel `address(1)`, which `registerEthToken`
(`L1NativeTokenVault.sol:135-138`) maps with no code check; for that address the
premise rests on CREATE2 addresses being keccak outputs. That mapped addresses keep
their code is part of the premise. `_l1ChainId() ≠ 0` is configuration on L2
(`OPS-CONFIG`). Interleaving the tracked token's life with registry operations on
other assets, and native registration, are not covered.

## Resolution: destination mint and failed-transfer recovery

`Specs/Resolution.lean` models `bridgeMint` and `bridgeRecoverFailedTransfer`
(`NativeTokenVaultBase.sol:193-233`) on two branches. The registered bridged branch:
entry checks, the chain-balance hook on the pre-mint token, then the token's
`bridgeMint`. The first-bridge deploy branch of `bridgeMint`: `registerFreshBranch`
applied to the data's origin token, then hook, then mint. `RegisteredBridged` selects
a branch; it is not a guard. The hook `_handleBridgeFromChain` is a parameter;
`HooksCancel` is the inverse law a round trip needs, stated as a premise and not
proved of the deployed trackers.

| Result | Statement |
|---|---|
| `BridgeMintExact`, `RecoverExact` | A successful call credits exactly `amount` to `remoteReceiver` (mint) or `originalCaller` (recovery) and raises supply by `amount`. The hook saw the pre-mint token. Nothing else changes. No invariant premise. |
| `BridgeMintIgnoresUnreadFields`, `RecoverIgnoresReceiver` | The registered-branch result does not depend on unread data fields: mint ignores `originalCaller`, `originToken` and metadata; recovery ignores `remoteReceiver`, `originToken` and metadata. |
| `BridgeMintEnabled`, `RecoverEnabled`, `BridgeMintPreservesWellFormed`, `RecoverPreservesWellFormed`, `BridgeMintAssetBinding` | The exact success conditions. `WellFormed` is preserved. The credited token is the registry's token for `_assetId`. |
| `PrepareThenRecoverRestoresToken` | With no hook premise, recovering a preparation's returned data restores the token ledger exactly. |
| `PrepareThenRecoverEnabled` | Only the hook can block that recovery; the deploy branch is not taken. |
| `PrepareThenRecoverRoundTrip` | Under `HooksCancel`, prepare-then-recover returns exactly the original state. |
| `RoundTripNeedsCancellingHooks` | Countermodel: with hooks that count outflow and inflow separately, the token is restored and the state is not. |
| `RecoverAfterSpending` | Ordinary transfers between preparation and recovery cannot block the refund or change its amount. Supply returns to its starting value. |
| `PrepareThenDeliverConserves` | One transfer across two chains: the destination credit equals the source debit, and the sum of supplies is unchanged. |
| Guards and rollback | `ResolutionWrongRouterRejected`, `ResolutionPausedRejected`, `ResolutionValueRejected`, `ResolutionFailureAtomic`, `ResolutionHookFailureAtomic`, `MintRejectionRollsBackHook`, `ZeroReceiverMintRejected`, `MintSupplyOverflowRejected`. |
| Limits | `ZeroReceiverOnlyRecoverable`: preparation accepts receiver 0, no modelled destination can mint it, recovery restores the source. `VaultHasNoReplayGuard`: the same recovery and the same mint each succeed twice. |
| First bridge | `FirstBridgeMintExact` (asset id checked against the data's origin token; the fresh token holds exactly `amount`), `FirstBridgeChecksOriginToken`, `FirstBridgeRejected`, `FirstBridgeEnabled`, `FirstBridgeEstablishesRegistered`. |
| `ResolutionIsForeignBridgeIn` | On `Corr`-related states, both entry points are a registry-model `bridgeIn` of a foreign asset (vault unchanged), and `Corr` persists. |

Witnesses: `ResolutionSatisfiable` (non-identity hooks satisfying `HooksCancel`),
`SpendingAndDeliverySatisfiable`, `ResolutionRejectionsSatisfiable`,
`FirstBridgeSatisfiable`, `ResolutionCorrespondenceSatisfiable`. No result takes a
hash premise. Native escrow release, legacy-token and base-token branches, and
recovery's own deploy branch are not modelled; trace-level conservation and single
resolution remain open.

Source observations, reported to the maintainer of this repo, not yet confirmed
upstream. Both verifiers classify the first as a NatSpec error and the second as a
low-severity bug:

- `NativeTokenVaultBase.sol:186-187` says an asset-id check "must be performed" in
  `bridgeMint`; on the registered branch none is (`BridgeMintIgnoresUnreadFields`
  against `FirstBridgeChecksOriginToken`). The minted token is still fixed by
  `tokenAddress[_assetId]`.
- A zero receiver is accepted at the source and rejected at every modelled
  destination (`ZeroReceiverOnlyRecoverable`). On routes without a refund path the
  burned value may be unrecoverable; that is not modelled.

## Legacy tokens

The token's zero-vault fallback (see the
[BridgedStandardERC20 README](../BridgedStandardERC20/README.md)) does not read the
registry. On a `Valid` vault, after the fallback, the token's `assetId` equals the
vault's `assetId[T]` iff the vault records exactly `(L1_CHAIN_ID, originToken)` for
`T` (`LegacyAssetIdAgreesIffRecordedOn`, under `IdAssumptionsOn` on those two pairs).
`LegacyAssetIdAgreementOrBreak` is the same with no hash premise and a pinned
`LegacyIdBreak`; `LegacyAssetIdAgreesIffL1OriginOn` is its corollary when the recorded
origin token is the token's own. `LegacyAssetIdMismatch` is the countermodel: a vault
that records another origin chain.

Agreement or disagreement is permanent (`LegacyAgreementPermanent`): no vault
operation changes a nonzero `assetId[T]` (`RegisteredTokenIdFrozen`, which needs neither `Valid` nor a hash
premise).

`prepare` refuses every legacy token. `prepareLegacy`, which uses the deployed
`bridgeBurn`, fires the fallback and burns exactly the amount (`LegacyFirstPreparation`),
and reduces to `prepare` of the fallback-configured token under
`HookIgnoresTokenConfig` (`LegacyPreparationIsPreparation`), so the preparation
results apply. It keeps `RepresentationConsistent` exactly when the tracked id is the
fallback's (`LegacyFallbackRepresentationIff`, `LegacyPreparationMismatch`).

Possible finding, conditional (both verifiers classify it as likely a bug that needs
deployment context; reported to the maintainer of this repo, not yet confirmed
upstream): `registerToken` has no legacy check, so a legacy token left without a
registry entry can be registered as native by anyone, permanently
(`UnregisteredLegacyTokenRegistersNative`, `RegisteredTokenIdFrozen`). Whether such
tokens exist depends on migrations before the pin, which this repo cannot check. The
comments at `NativeTokenVaultBase.sol:200` and `:439` cite `setLegacyTokenAssetId`,
which is not in the pinned source (both verifiers: NatSpec error).

Model boundaries: the registry entry of a legacy token is taken as a given `Valid`
state; the registry and token models are compared, not interleaved; destination mint
and recovery of a legacy token are covered only on the token side.

