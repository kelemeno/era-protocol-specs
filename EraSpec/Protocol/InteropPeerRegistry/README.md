# Interop-peer registry: the whitelist mirror and the `baseTokenAssetId` entries

Source: era-contracts `draft/v0.35.0` at **`b17415d20`** (the v35 head), under
`l1-contracts/contracts/`:

- `core/chain-registration/ChainRegistrationSender.sol` (the sender)
- `core/bridgehub/L2Bridgehub.sol`, `core/bridgehub/BridgehubBase.sol`,
  `core/bridgehub/L1Bridgehub.sol`
- `core/chain-asset-handler/ChainAssetHandlerBase.sol`,
  `core/chain-asset-handler/L1ChainAssetHandler.sol`
- `state-transition/chain-deps/facets/Mailbox.sol`,
  `state-transition/chain-deps/facets/ZKChainBase.sol`
- `core/message-root/L1MessageRoot.sol` (`isInteropEnabled`)

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| PeerMirror | [Specs/PeerMirror.lean](Specs/PeerMirror.lean) | [Properties/PeerMirror.lean](Properties/PeerMirror.lean) | [Proofs/PeerMirror.lean](Proofs/PeerMirror.lean) |

Namespace `Contracts.InteropPeerRegistry`. Statements are
`Contracts.InteropPeerRegistry.Properties.*`; each certificate has the same name without the
`Properties` segment. No result takes a hash premise.

## What is modelled

One state for the ecosystem: the sender's `interopPeerAllowed`; the L1 Bridgehub's registration,
`baseTokenAssetId` and `settlementLayer`; the message root's `isInteropEnabled` and
`chainTreeLeafCount != 0`; and, on every chain, its `L2Bridgehub`'s `isPeerAllowed`,
`baseTokenAssetId` and `settlementLayer`, and its priority queue as one FIFO list. The steps are
chain creation, `enableInterop`, batches, `allowInteropPeer`, `deregisterInteropPairs`, the
re-submission (`requestL2TransactionTwoBridges` with the sender as second bridge, which does not
run `_checkPeerPair`), the retired consent-free registration, other requests, the execution of a
queue's head with success or failure, and the migration path (out to a settlement layer, arrival,
start back, finalization on L1, confirmation of a failed arrival). Migrations are disabled at
`b17415d20` (`CHAIN_MIGRATIONS_ENABLED = false`); the model keeps them, so the presence results
are about that latent path. Runs start from fresh storage, and every step kind is enabled for the
whole run. Two mechanisms are switches: FIFO execution, and the `settlementLayer(p) == c` clause
of `_checkPeerPair` in `deregisterInteropPairs`. Boundary: `MODEL-PEER-MIRROR` in
[ASSUMPTIONS.md](../../../ASSUMPTIONS.md).

## What to check

**(a) `isPeerAllowed` mirrors `interopPeerAllowed`.**

- On chain `c`, `isPeerAllowed[p]` equals the sender's `interopPeerAllowed[c][p]` whenever no
  entry writing it is pending in `c`'s queue and the last executed one succeeded
  (`PeerFlagMirrorsWhenLastEntrySucceeded`). If every executed service entry succeeded, the flags
  agree whenever none is pending, however many re-submissions failed
  (`PeerFlagMirrorsWhenServiceEntriesSucceed`).
- The success premise is needed: after a failed `allowInteropPeer` service transaction the queue
  can be empty with the flags disagreeing (`FailedServiceEntryLeavesPeerFlagBehind`;
  `FailedServiceEntryLeavesPeerFlagBehindLogged` also states the failed entry on the log). The
  re-submission is then enabled and repairs it (`ResubmissionRestoresPeerFlag`). FIFO execution is
  needed too (`WithoutFifoPeerFlagDesyncs`).
- A failed `deregisterChainForInterop` service transaction leaves the flags disagreeing the other
  way: the sender's flag is `false` and the chain's `isPeerAllowed[p]` is `true`
  (`FailedDeregLeavesPeerFlagOn`). Nothing re-sends a deregistration. The repair is a repeated
  `deregisterInteropPairs(c, [p])`, which has no `require(interopPeerAllowed)`: wherever
  `_checkPeerPair` passes and `c`'s queue is empty, it is enabled and its successful execution
  leaves both flags `false` (`DeregistrationRepeatClearsPeerFlag`).
- While L1 records `p` as settling on `c`, that repair is not available: `_checkPeerPair` rejects
  it and `allowInteropPeer(c, p)`, and the re-submission needs the sender's flag
  (`FailedDeregRepairBlockedWhileSettled`). From a state where L1 records `p` on `c`, the sender's
  flag is `false` and no entry writing `c`'s flag is pending, no step changes `c`'s flag, and the
  last two conditions persist (`DisallowedPeerFlagFrozenWhileOnLayer`). Applied step by step, the
  chain's flag keeps its value for as long as L1 records `p` on `c` (an informal consequence:
  only the one-step result is proved). That window needs a migration, which is disabled at
  `b17415d20`.
- The model lets any queued execution fail. For a deregistration entry, the failure cause the
  protocol docs name is an L2 that is not yet upgraded (`protocol-docs/interop-gating.md:172-173`);
  an earlier successful allow on the same chain shows that its L2 was upgraded (source note, not
  modelled).
- Neither flag is ever set for the chain itself or for L1, although the re-submission skips
  `_checkPeerPair` (`PeerFlagsOnlyForProperPeers`).

**(b) A chain's `baseTokenAssetId[p]` is `0` or L1's.**

- On every chain the entry is `0` or the L1 Bridgehub's current `baseTokenAssetId[p]`
  (`L2BaseTokenEntryIsZeroOrL1Value`).
- L1's entry never changes once nonzero, including through a round trip of `p` to a settlement
  layer, whose finalization copies the layer's entry into L1 without comparing
  (`L1BaseTokenFixedOnceSet`). This is proved, not assumed. So after `p` is created with asset id
  `a`, every chain's entry for `p` stays `0` or `a` (`L2BaseTokenEntryIsZeroOrCreationValue`).

**(c) Presence while `p` settles on `c` (latent).**

- While `c`'s `L2Bridgehub` records `p` as settling on `c`, its entry for `p` is L1's, which is
  nonzero (`SettledChainEntryIsL1Value`). While `p`'s withdrawal from `c` is in flight, `c`'s entry
  and the carried asset id are L1's (`ReturningChainEntryIsL1Value`, `ReturnCarriesL1BaseToken`).
- While `p`'s arrival on `c` is still queued, the queued data carries L1's value and no
  deregistration of `p` on `c` is queued after it (`PendingArrivalCarriesL1Value`). The entry on
  `c` itself may still be `0` in that window (`PendingArrivalEntryMayBeZero`), so presence does
  not hold "while in flight to `c`". By the reader inventory below (not modelled), no reader on
  `c` needs the entry for `p`'s migration before the arrival writes it.
- `_checkPeerPair`'s NatSpec says the entry of a chain settling on `c` must never change. Its
  `baseTokenAssetId` does not change in any step, the re-submission included, and a `true`
  `isPeerAllowed` stays `true` (`SettledEntryNeverChanges`). A `false` `isPeerAllowed` can turn on:
  after a failed service entry, the re-submission sets it while `p` settles on `c`
  (`SettledPeerFlagCanTurnOn`; `SettledPeerFlagTurnsOnByResubmission` also states that the step
  executes a queued re-submission after a failed service entry).
- Both mechanisms are load-bearing. Without the settlement clause in `deregisterInteropPairs`, a
  settled chain's entry is cleared (`WithoutDeregSettlementCheckSettledEntryCleared`) and its
  return then writes `0` into L1's `baseTokenAssetId[p]`
  (`WithoutDeregSettlementCheckL1BaseTokenRewritten`). Without FIFO execution, a deregistration
  queued before the arrival runs after it (`WithoutFifoSettledEntryCleared`).

**(d) Deregistering `(c, p)` after `p` returned from `c`.** It is accepted
(`ReturnedPeerDeregistrationAccepted`) and clears `c`'s entry (`ReturnedPeerEntryCanBeCleared`).

### Readers of a chain's `baseTokenAssetId[p]` (source inventory at `b17415d20`, not modelled)

1. `InteropCenter._getDestinationBaseTokenAssetId` (`interop/InteropCenter.sol:696-704`), for every
   bundle to a non-L1 destination (`:629-631`): reverts `DestinationChainNotRegistered` on `0`, then
   requires `isPeerAllowed`; the value becomes the bundle's `destinationBaseTokenAssetId`.
2. `AtomicFlowManager.append` (`atomic-interop/AtomicFlowManager.sol:150-160`): every other leg's
   source must have a nonzero entry (`ManagerLegSourceChainNotRegistered`).
3. `AssetRouterBase._bridgehubDepositNonBaseTokenAsset` (`bridge/asset-router/AssetRouterBase.sol:150`),
   reached on L2 from `L2AssetRouter.initiateIndirectCall` (`bridge/asset-router/L2AssetRouter.sol:331-339`)
   after reader 1: refuses the destination's base token as an ordinary asset.
4. `BridgehubBase.baseToken` (`core/bridgehub/BridgehubBase.sol:314-324`, a view), also behind
   `Getters.getBaseToken` of a diamond the chain hosts (`state-transition/chain-deps/facets/Getters.sol:69-71`).
5. On a settlement layer, `ChainAssetHandlerBase._buildBridgehubMintData`
   (`core/chain-asset-handler/ChainAssetHandlerBase.sol:322`), in `p`'s return; reached only after
   `forwardedBridgeBurnSetSettlementLayer` required `settlementLayer[p] == block.chainid`
   (`BridgehubBase.sol:411-413`).
6. On a settlement layer, `DiamondInit` (`state-transition/chain-deps/DiamondInit.sol:62`), when
   `p`'s diamond is deployed there during its arrival, after `forwardedBridgeMint` wrote the entry
   (`ChainAssetHandlerBase.sol:391-399`).
7. `ZKChainSpecificForceDeploymentsLib.build` (`upgrades/ZKChainSpecificForceDeploymentsLib.sol:33-34`),
   which reads the Bridgehub it is passed (from `upgrades/L2DefaultDelegateCalldataComposer.sol:29`
   and `upgrades/L1GenesisUpgrade.sol:89`).

After `p` returned from `c`, `c` records `settlementLayer[p] = L1`, so reader 5 cannot run for `p`
on `c`, and reader 6 runs only in an arrival, which writes the entry first; a chain that has
returned cannot migrate again (`MAX_ALLOWED_NUMBER_OF_MIGRATIONS = 2`,
`ChainAssetHandlerBase.sol:274-279`). Readers 1 and 2 treat `0` as "not registered" and revert,
and reader 3 is reached only after reader 1. Reader 7 reads the entry of the chain being upgraded
(`_chainId = s.chainId`) from the Bridgehub of the layer that chain's diamond lives on
(`s.bridgehub`, set from the deploying CTM's `BRIDGE_HUB` at
`state-transition/chain-deps/DiamondInit.sol:54`, `:90`; read at
`upgrades/L1GenesisUpgrade.sol:35-40` and `upgrades/DefaultUpgrade.sol:76-82`). Genesis runs only
in chain creation on L1 (`state-transition/ChainTypeManager.sol:703-711`, called only from
`core/bridgehub/L1Bridgehub.sol:124`), after L1's entry is written (`L1Bridgehub.sol:118`). In an
upgrade of `p`'s diamond on a settlement layer `c`, the entry read is `c`'s, which is L1's nonzero
value while `c` records `p` as settling on `c` (`SettledChainEntryIsL1Value`). Whether an upgrade
can run on `p`'s diamond on `c` after `p` left `c` is not analysed. The view functions that compose
the same transactions (`L1GenesisUpgrade.genesisUpgradeTx`, `DefaultUpgrade.l2UpgradeTx`,
`RegistryBootstrapMigration.l2UpgradeTx`) write nothing.

## Boundaries

- Only the modelled queue entries reach `L2Bridgehub.allowInteropPeer` and
  `deregisterChainForInterop`: the L2 `chainRegistrationSender` slot holds the aliased sender
  (`OPS-CONFIG`), and no other L1 path produces a transaction from `SERVICE_TRANSACTION_SENDER` or
  the aliased sender. Each queue is executed in order, also across a settlement-layer relay.
- In-flight migration messages are a ghost status per chain; the L1 steps that consume them are
  guarded by it (`PROTO-EVIDENCE`). Every other guard is a deployed check; reject-only checks
  (authorization, pauses, fees, migration numbers, CTM and asset-handler checks) are omitted.
- Upgrades of the sender or the Bridgehubs, and the pre-v35 history beyond what the model's steps
  produce from fresh storage, are outside the model.
- Not modelled: the readers listed above; the readers of `isPeerAllowed`, which are the send-side
  check (`interop/InteropCenter.sol:699-702`) and the receive filter
  (`atomic-interop/AtomicFlowManager.sol:338-344`, used at `:201` and `:231`); and whitelisting of
  settlement layers beyond `c ≠ p`.
