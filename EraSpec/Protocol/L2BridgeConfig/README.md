# L2 bridge configuration consistency

Source: era-contracts `draft/v0.35.0` head `b17415d20`, under `l1-contracts/contracts/`.
Namespace `Contracts.L2BridgeConfig`; statements are `Contracts.L2BridgeConfig.Properties.*`
and each proof has the same name without the `Properties` segment.

Nine L2 built-ins keep their own copy of the L1 chain id (message root, bridgehub, asset
router, native token vault, chain asset handler, asset tracker, interop center, ZKsync OS base
token, atomic flow manager). Four keep their own copy of the base-token asset id (router,
vault, tracker, WETH). The bridgehub and the chain asset handler also store an ETH asset id
derived from their L1 chain id. Each contract decides from its own copy: the router rejects
`finalizeDeposit` for its base id, the vault routes base-token burns through `BaseTokenHolder`
by its base id, the interop center reads the vault's base id, and the tracker books base-token
flows under its own. This topic models those words, every writer of them at the pin, the
genesis and default upgrade transactions of `L2GenesisForceDeploymentsHelper`, and the vault's
and router's other writers of the base id's registry entry and route.

| Review | File |
|---|---|
| The words, the writers (with the grep), the two upgrade programs, the one-shot guards, the model boundary `MODEL-L2-CONFIG`, every entry point, runs, `ConfigConsistent`, run premises | [Specs/Consistency.lean](Specs/Consistency.lean) |
| Genesis, preservation, writers, runs, the origin-data repair, four countermodels, three witnesses | [Properties/Consistency.lean](Properties/Consistency.lean) |
| Per-call characterizations, the two upgrade normal forms, the checked derivations and witnesses | [Proofs/Consistency.lean](Proofs/Consistency.lean) |

## The invariant

`ConfigConsistent E l1 a weth w`: the nine L1 chain id words are `l1 ≠ 0`; the four base id
copies are `a ≠ 0`; both ETH ids are `encodeNTVAssetId(l1, ETH_TOKEN_ADDRESS)`; the vault's
`WETH_TOKEN` is `weth ≠ 0`; the vault maps `a` to `L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR` and back;
every built-in is initialized; the router's recorded deployment trackers are zero or the vault.
It does not constrain the base token's origin data (`BaseOriginIs`).

| Result | Statement |
|---|---|
| `GenesisEstablishesConfigConsistent` | A successful genesis from all-zero storage leaves `ConfigConsistent` with the input's ids and the created WETH, the base id routed to the vault, and the input's origin data in the vault. The ids are nonzero because `AtomicFlowManager.initL2` refuses a zero L1 chain id and WETH's `initializeV3` a zero base id. Witness: `GenesisEstablishesConfigConsistentWitness`. |
| `StepPreservesConfigConsistent` | Every successful call preserves it, under `ConfigCall.Admissible`: no direct `initL2`/`updateL2` by the upgrader, and no logged vault registration of a token whose vault id on this chain is `a`. |
| `DefaultUpgradeKeepsL1AndBaseIds` | From a consistent state a default upgrade succeeds only with the stored L1 chain id and base id. The vault's freezes (`NTV/L2NativeTokenVault.sol:148, 152-155`) are the checks that refuse anything else. |
| `DefaultUpgradeAdoptsAnyBaseOrigin` | With the stored ids it succeeds whatever origin chain and origin token it carries, and the vault takes them (`:160, :167`, no check). |
| `GenesisRevertsOnConsistentState` | A second genesis reverts. |
| `BaseRouteMovesOnlyByCounterpart` | The base id stays routed to the vault under every call except the counterpart's `setAssetHandlerAddress` at that id. Any sender, no run premise. |
| `OnlyUpgraderWritesScalarConfig` | From any state, the scalar words change only in an upgrade transaction sent by `L2_FORCE_DEPLOYER_ADDR` or in a direct call by `L2_COMPLEX_UPGRADER_ADDR`. |
| `BaseEntriesWritersFromConsistent` | From a consistent state, `tokenAddress[a]`, `assetId[L2_BASE_TOKEN_SYSTEM_CONTRACT_ADDR]`, `originChainId[a]` and the route of `a` change only by a default upgrade, a direct vault `updateL2` by the upgrader, a vault registration whose vault id is `a`, or the counterpart's write at `a`. |
| `ConfigConsistentAlongRuns` | After genesis, along every admissible run: consistent with the genesis ids and WETH, every logged default upgrade carries those ids, and without a counterpart write at `a` the base id stays routed to the vault. Witness: `ConfigRunWitness` (a default upgrade that changes the L1 asset router, a vault registration, a bridged-token deployment, a counterpart write, a fallback write: every kind of writer that can succeed admissibly from a consistent state; `routerRegister` cannot). |
| `BaseOriginPinnedAlongRuns` | Repaired form for the origin data: if also every logged default upgrade carries the genesis origin chain and origin token, the vault keeps them and its native test for the base token gives the genesis answer. |

The run premises are model boundaries, not checks in the code. The first is `MODEL-L2-CONFIG`
(the complex upgrader's delegate targets are the genesis and default upgrades). The second is
a premise on each logged registration's own input, not on the hash function. With a
collision-free encoding it binds only when the base token's origin chain is this L2 and the
registered token is the base token's origin token (`NativeTokenVaultBase.sol:131-140, 492-499`);
the registration would then overwrite `tokenAddress[a]` and the route of `a`. The L2 code takes
the base token never to be native on L2 (`NativeTokenVaultBase.sol:442`,
`L2AssetTracker.sol:180`). No countermodel here shows the premise is load-bearing.

The model also has the router's non-vault `setAssetHandlerAddressThisChain` (`routerRegister`).
From a consistent state it never succeeds: `ConfigConsistent` keeps the router's recorded
deployment trackers at zero or the vault, so the tracker check fails (`routerRegister_none` in
the Proofs file), and its case of `StepPreservesConfigConsistent` holds vacuously. The direct
calls left in the model either revert (sender not the upgrader) or are excluded by the first
run premise (sender the upgrader).

## Countermodels

| Result | Statement |
|---|---|
| `NoBaseFreezeLeavesTrackerOnOldBase` | Without the vault's base-id freeze, a default upgrade with a new base id succeeds from every consistent state; the tracker and WETH keep the old id and the state is consistent for no ids. The deployed vault refuses that upgrade. |
| `NoL1FreezeLeavesTrackerOnOldL1` | The same for the L1 chain id freeze: the tracker, interop center, base token and flow manager keep the old id. |
| `SameBaseOriginRewriteFlipsNativeTest` | With the stored ids and origin chain `block.chainid`, a default upgrade succeeds from every consistent state whose base token is not native, stays consistent, and makes the vault's native test for the base token true (the tracker reads the same word). |
| `RouterUpdateOutsideHelperDivergesBase` | `L2AssetRouter.updateL2` called by the upgrader outside the helper with a new base id succeeds from every consistent state and leaves the router's id different from the vault's: the router has no freeze of its own. |
| `ConfigCountermodelWitness` | A consistent state reached by genesis, base token not native, on which the flip and the divergence happen, and the flip changes the base id's registry entries. |

## Boundaries

`MODEL-L2-CONFIG` in the [assumption register](../../../ASSUMPTIONS.md) and the Specs header
list them. In short: the delegate targets are the two upgrade programs; the built-ins run the
`b17415d20` code (force-deployment rows, proxy upgrades and WETH's proxy admin are not
modelled); decoding, keccak, CREATE2 and the address alias are abstract; steps that write no
modelled word are omitted and treated as succeeding; owners, metadata words and events are not
modelled. The witnesses use the deployed addresses and a toy asset-id encoding.

Which data a default upgrade carries is decided on L1: at the pin,
`upgrades/ZKChainSpecificForceDeploymentsLib.sol:28-56` reads the base id from the Bridgehub
and the origin chain and origin token from the L1 vault, for genesis and upgrades alike. That
L1 side is not modelled here; `BaseOriginPinnedAlongRuns` states what the L2 side needs from it.
For chains created before `v0.35`, entering this model at a `ConfigConsistent` state is an
assumption (`StepPreservesConfigConsistent` does not assume genesis; the results stated from a
consistent state need it). Besides the configuration-word equalities it includes the built-ins' initialized flags and
`trackersVaultOnly`, the router's recorded deployment trackers being zero or the vault. The `main` branch (`70096e2ea`) is
not modelled; its helper also initializes the tree and flow manager on the upgrade path.
