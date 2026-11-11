# BridgedStandardERC20

Locally authored token-ledger and fresh-proxy initialization projections. The
operational model covers the initialized, nonzero configured-vault branch; the
initializer model explains how that configuration and a fresh zero ledger are
represented here. `LegacyFallback` adds the zero-vault branch of `onlyNTV`, and
`Reinitialization` adds `reinitializeToken` on the full proxy storage. None of these
models establishes Solidity correspondence.

| Review | File |
|---|---|
| State, successful-call guards, ledger operations, and allowed traces | [Specs/Model.lean](Specs/Model.lean) |
| Exact security/accounting statements | [Properties/Model.lean](Properties/Model.lean) |
| Checked ledger derivations | [Proofs/Model.lean](Proofs/Model.lean) |
| Fresh-proxy initializer projection | [Specs/Initialization.lean](Specs/Initialization.lean) |
| Initialization input, ledger, once-only, and failure properties | [Properties/Initialization.lean](Properties/Initialization.lean) |
| Checked initialization derivations | [Proofs/Initialization.lean](Proofs/Initialization.lean) |
| Legacy zero-vault fallback in `onlyNTV`: prologue, both-branch bridge calls, runs | [Specs/LegacyFallback.lean](Specs/LegacyFallback.lean) |
| Conservativity, first-call exactness and authority, at-most-once write, run characterization, ledger | [Properties/LegacyFallback.lean](Properties/LegacyFallback.lean) |
| Checked legacy-fallback derivations and witness | [Proofs/LegacyFallback.lean](Proofs/LegacyFallback.lean) |
| `reinitializeToken` on the full proxy storage, every modelled entry point, labelled runs | [Specs/Reinitialization.lean](Specs/Reinitialization.lean) |
| Reinitialization guards and effect, version counter, identity for life, countermodels | [Properties/Reinitialization.lean](Properties/Reinitialization.lean) |
| Checked reinitialization derivations | [Proofs/Reinitialization.lean](Proofs/Reinitialization.lean) |

## Source and scope

Reviewed source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`,
`l1-contracts/contracts/bridge/BridgedStandardERC20.sol`, and its OpenZeppelin v4
`ERC20Upgradeable` `_mint`, `_burn`, `_transfer`, and initializer behavior. The
inherited before/after transfer hooks are empty. These are local abstract models;
source and compiled-code correspondence has not been established.

Assumption IDs: `MODEL-LEDGER`, `MODEL-FRESH`, `REP-TOKEN`, `REP-INIT`, and the
applicable VM/language/build laws in [the layer register](../../../ASSUMPTIONS.md).
Ledger/initialization theorems are proved locally; the concrete storage, caller,
proxy, and compilation connections are separate open obligations.

The initialization projection distinguishes a fresh proxy at initializer version
0 from a disabled implementation at version 255. It models the initializer as
callable by any caller and records that caller as the configured vault; it has no
owner or vault caller guard. The real deployment sequence must therefore supply
the intended caller through the vault's internal atomic deployment flow. The
initializer preserves balances and total supply rather than resetting them. A
zero ledger follows from fresh proxy storage, not from a ledger-reset operation.
Fresh allocation is an explicit model boundary; no BeaconProxy/deployer storage
semantics have been proved here. Nonzero caller identity in the intended flow
comes from the deployed-vault context, rather than a new initializer guard.

The metadata input is represented by a flag for success of the outer metadata
decode/setup path. It does not assert that each caught name, symbol, or decimals
getter decode succeeds. Constructor-only/nested initializer cases, metadata
contents, events, permit/allowance fields, and proxy execution semantics are not
modeled. `Reinitialization` models the metadata and EIP-712 slots as storage only.

Balances and total supply are natural numbers with an explicit uint256 bound.
`WellFormed` requires the sum of every account's balance to equal total supply,
bounded supply, and a zero balance at the zero address. This accounts for all
160-bit addresses and justifies the nonwrapping arithmetic in the operational
slice.

| Operation | Successful-call conditions | Ledger effect |
|---|---|---|
| `burn` | Nonzero configured vault; caller is that vault; nonzero account; enough balance | Decrease that balance and total supply by exactly the input amount. |
| `mint` | Nonzero configured vault; caller is that vault; nonzero recipient; resulting supply fits uint256 | Increase that balance and total supply by exactly the input amount. |
| `transfer` | Nonzero sender/recipient; enough balance | Debit then credit, preserving supply. Self-transfers leave the ledger unchanged. |

Zero amounts are permitted. `burn` has no allowance requirement. Mint/burn leave
other account balances and vault/origin/asset identity unchanged. Ledger bounds
and accounting are preserved through arbitrary interleavings of these operations.
A one-unit mint/burn roundtrip supplies a non-vacuous execution witness.

## Legacy zero-vault fallback

`onlyNTV` (`BridgedStandardERC20.sol:50-64`) runs a prologue when the vault slot is
zero. It writes the vault slot to `L2_NATIVE_TOKEN_VAULT_ADDR` and the asset-id slot to
`encodeNTVAssetId(L1_CHAIN_ID(), originToken)`, before `require(msg.sender == ntv)`.
`Specs/LegacyFallback.lean` models this prologue as `legacyFallback`, followed by the
nonlegacy `mint`/`burn`. A failure commits nothing, so the prologue's writes are rolled
back with the call.

- The extension is conservative: from a nonzero vault the runs are those of the
  nonlegacy model (`nonlegacy_runs_agree`, `nonlegacy_bridge_calls_unchanged`).
- On a legacy token only the L2 vault can make a bridge call
  (`legacy_unauthorized_bridge_calls`).
- The first such call installs exactly `fallbackConfig` and has exactly the
  nonlegacy ledger effect (`legacy_bridge_mint_exact`, `legacy_bridge_burn_exact`).
- The asset-id slot is written at most once, from the starting origin token
  (`legacy_run_config`, `legacy_run_fallback_fired`).
- `legacy_runs_characterized` characterizes the runs from a legacy token exactly: a
  transfer-only prefix, one nonlegacy mint or burn on the fallback-configured state,
  then a nonlegacy run.

`LegacyEnv` fixes the value `L1_CHAIN_ID()` returns for a run and assumes the call does
not revert (`DEP-RESULTS`). The deprecated `l2Bridge` has no authority.
`bridgeInitialize`, `reinitializeToken`, allowances/permit and upgrades are not steps
of these runs. Whether the written id is the vault's id is answered in the
[NativeTokenVaultBase README](../NativeTokenVaultBase/README.md#legacy-tokens).

Source documentation (both verifiers classify it as a NatSpec error; reported to the
maintainer of this repo, not yet confirmed upstream): the NatSpec at
`BridgedStandardERC20.sol:50-51` says only that the modifier sets the vault to its
default; it does not say that it also overwrites the asset-id slot.

## Reinitialization

`reinitializeToken` (`:141-164`) is modelled on `TokenStorage`: the ledger-and-identity
`State`, OpenZeppelin's `_initialized` slot, and the metadata slots (name, symbol,
`decimals_`, getter flags, EIP-712 name/version/caches). OpenZeppelin lines are cited
from a v4.9.6 copy; the pinned submodules are not checked out.

One call:

- succeeds exactly when the requested version is the current one plus one and the
  caller is the owner the beacon reports (`ReinitSucceedsIff`), so there are no version
  jumps (`VersionJumpHasNoStep`), no step after 255, and no reinitialization of the
  implementation (`ImplementationNeverReinitialized`);
- writes only the version and that metadata, including the EIP-712 name and version
  and zeroed caches (`ReinitExactEffect`);
- leaves balances, supply, vault, asset id, origin token and `decimals_` untouched,
  whoever calls and whatever the beacon answers (`ReinitKeepsLedgerAndIdentity`);
  `WellFormed` and every later mint, burn or transfer are as before
  (`ReinitPreservesWellFormed`, `ReinitLeavesLedgerCallsUnchanged`,
  `ReinitIndependentOfLedger`).

Only the step from 254 leaves no further reinitialization possible
(`OnlyTheStepFrom254DisablesReinitialization`). Without `onlyNextVersion`, a single
1 -> 255 call would (`WithoutNextVersionAJumpDisablesReinitialization`).

Along runs of every modelled entry point (`StorageReach`; labelled `StorageRun`,
`StorageRunsAreReach`):

- the identity is fixed once the version is nonzero (`InitializedIdentityIsFixed`);
  from a fresh proxy it is the one `bridgeInitialize` bound (`FreshProxyLifecycle`);
- the version counts the version-writing calls exactly
  (`VersionCountsInitializations`): at most 255 in a proxy's life
  (`LifetimeVersionCallBound`), a bound that is reached (`LifetimeBoundIsTight`), and
  `bridgeInitialize` succeeds at most once (`BridgeInitializeAtMostOnce`).

The version counter is shared with `bridgeInitialize`. A reinitialization at version 1
on a fresh proxy locks initialization out for ever
(`ReinitializeOnFreshProxyBlocksBridgeInitialize`). The token's guards do not prevent
this; the vault's atomic deploy-and-initialize (`NativeTokenVaultBase.sol:629-630`)
does, and both verifiers classify it as not an issue in the deployed flows.

Source documentation (both verifiers classify it as a NatSpec error; reported to the
maintainer of this repo, not yet confirmed upstream): the NatSpec at `:141-147` says
only "update the token's metadata"; the call also rewrites the EIP-712 domain
(`__ERC20Permit_init(_newName)`), which `ReinitExactEffect` makes explicit.

`_initializing` is not modelled (nested and constructor-context initializer calls are
outside the model). The beacon's `owner()` is an arbitrary per-call answer.

## Remaining work

- Constructor-only/nested initializer behavior, metadata contents (the reinitializer
  is modelled in `Reinitialization`), allowances/permit, permit signatures under a
  changed EIP-712 domain, events, proxy execution, and upgrades (beacon `upgradeTo`
  code swaps).
- Vault authorization linked to actual funded obligations: an authorized mint
  alone does not prove backing or one-time delivery.
- The burn's connection to vault preparation, calldata, publication, and later
  delivery or refund. This slice does not create a cross-chain obligation record.
- Concrete uint256 storage/call/revert behavior, initializer caller flow, and
  transaction rollback corresponding to these local transitions.

Continue review with [Properties/Initialization.lean](Properties/Initialization.lean)
and `Properties.burn_exact`, then the
[native token vault registration and preparation models](../NativeTokenVaultBase/README.md).
