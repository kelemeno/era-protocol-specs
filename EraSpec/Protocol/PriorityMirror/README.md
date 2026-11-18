# PriorityMirror

One chain's priority queue on L1 and on its gateway, across a migration out and back. Source:
era-contracts branch `draft/v0.35.0` at **`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`**: the
Mailbox facet's request and gateway paths, `InteropCenter.forwardTransactionOnGateway`, the
`Migrator` facet (deposit pauses, `forwardedBridgeBurn`, `forwardedBridgeMint`,
`forwardedBridgeConfirmTransferResult`), `L1ChainAssetHandler.isMigrationInProgress`, the
`DiamondProxy` freeze check and `freezeDiamond`/`unfreezeDiamond`. The model of the
`PriorityTree` and `DynamicIncrementalMerkle` libraries is
[`../../Contracts/MailboxFacet/Specs/PriorityTree.lean`](../../Contracts/MailboxFacet/Specs/PriorityTree.lean),
copied from branch `origin/cov/mailbox` (commit `212f846`, pinned `d9f678900`; both libraries are
byte-identical at `b17415d20`). That branch's statements and proofs about the library are not part
of this topic.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Mirror | [Specs/Mirror.lean](Specs/Mirror.lean) | [Properties/Mirror.lean](Properties/Mirror.lean) | [Proofs/Mirror.lean](Proofs/Mirror.lean) |

Namespace `Protocol.PriorityMirror`. Statements are `Protocol.PriorityMirror.Properties.*`; each
certificate has the same name without the `Properties` segment. No statement has a hash premise.

The model is chain `C`'s L1 diamond and, once migrated, its gateway diamond (each with its priority
tree, settlement-layer field, pause timestamp, frozen flag, batch counters and hashes), the chain
asset handler's `isMigrationInProgress[C]`, the queue of `C`'s relay leaves in the gateway's L1
tree that the gateway has not executed, a migration phase, and ghost logs: `log1` (the L1 leaves),
`leaves2` (the gateway leaves), `executed` (the leaves a `processBatch` of either copy advanced
over) and `dropped` (the relays that failed on the gateway). Steps: L1 requests (pushed on L1 and
relayed while `C` is away), in-order relay execution on the gateway, each copy's batch pipeline,
the L1 burn, the gateway mint (or its failure), the confirmation, the gateway burn, the L1 mint,
deposit pauses, freezes of either copy, and time. Two run premises appear:
`ConsistentProcessing` (a batch processes only leaves its copy holds, the reliance
`PriorityTree.sol:77-82` states) and FREEZE-ORDER (until the L1 mint, no relay executes on the
gateway while the gateway copy is frozen). `Honest` is both.

- **The L1 copy during the move out.** `isMigrationInProgress[C]` is set exactly between an L1
  burn and its confirmation (`InProgressIffInFlight`). In that window every L1 request reverts, no
  relay is queued, and the L1 copy's tree, batch counters and hashes and pause timestamp are those
  just before the burn (`L1SnapshotFrozen`). A failure confirmation restores the L1 diamond from
  just before the burn, except that the pause timestamp is cleared and the frozen flag is the
  current one (`FailureRestoresL1`).
- **Relays, without FREEZE-ORDER.** Before the L1 mint a relay is dropped exactly when the
  gateway copy is frozen; otherwise its push into the gateway tree succeeds (`RelayDropsIffFrozen`,
  consistent runs). In every run, from the gateway copy's creation until the L1 mint, the gateway
  leaves, pending relays and dropped relays are together as many as the L1 leaves, and the gateway
  leaves followed by the pending relays are the L1 leaves exactly when nothing was dropped
  (`MirrorIffNoDrop`); after a drop that equality fails until the L1 mint
  (`MirrorBreakPermanent`).
- **Mirror, in honest runs.** From the gateway copy's creation until the L1 mint, the gateway copy
  has the L1 tree's start index, its leaves followed by the pending relays are the L1 leaves, and
  both trees' storage is what pushing their leaves from the setup state gives (`MirrorPrefix`). No
  relay is dropped before the L1 mint (`NoRelayDroppedBeforeReturn`).
- **No operation lost or repeated, in honest runs (headline).** The leaves processed by either
  copy, in processing order, are a prefix of the L1 leaves; whenever the L1 copy settles they are
  exactly the L1 leaves below its unprocessed index (`ExecutedIsL1Prefix`). With migrations enabled
  and a nonzero L1 pause timestamp, the return mint's modelled checks pass, and the L1 mint step
  sets the L1 unprocessed index to the number of processed operations (`ReturnMintChecksPass`).
- **Without FREEZE-ORDER.** A relay executed on the frozen gateway copy is dropped and the next
  operation takes its index on the gateway; after the gateway burn the processed sequence
  `[11, 1, 3]` is not a prefix of the L1 leaves `[11, 1, 2, 3]`, and the L1 mint step reverts on
  its historical-root check (`DroppedRelayCountermodel`). In every consistent run the commitment's
  root is the root of the processed sequence and the check passes exactly when some L1 prefix has
  that root (`ReturnRootCheckIffRootMatch`), so with a broken prefix it passes only through a root
  collision between two named leaf lists (`BrokenReturnNeedsRootCollision`). A processed sequence
  that is not an L1 prefix stays so (`ExecutedDivergencePermanent`). Whenever the processed
  sequence is still an L1 prefix at the return, the return goes through as in honest runs
  (`ReturnMintPassesOnPrefix`); in its witness a relay is dropped, no later relay reaches the
  gateway copy before its burn, and the dropped operation is processed on L1 after the return.
- **At the pin.** `CHAIN_MIGRATIONS_ENABLED = false` (`common/Config.sol:320`; also at `main`
  `70096e2ea`): with migrations disabled the chain always settles on L1, with no migration in
  progress, no gateway copy and no relay (`MigrationsDisabledKeepL1Settling`). The other results are
  about the kept migration machinery with the switch on. At `main` the migration steps the model
  reads behave the same (`Migrator.sol` differs in the precommitment field and error names). There
  the gateway push `bridgehubRequestL2TransactionOnGateway` is `onlyBridgehubOrInteropCenter`
  (`Mailbox.sol:143-150` at `main`), and `L2Bridgehub.forwardTransactionOnGateway`
  (`core/bridgehub/L2Bridgehub.sol:131-141` at `main`) is a second relay entry, gated by the same
  relay sender and reverting on L1. The model is not re-checked line by line at `main`.

Witnesses: `InProgressIffInFlightWitness`, `L1SnapshotFrozenWitness` (the L1 copy frozen during a
failed move), `FailureRestoresL1Witness`, `MirrorPrefixWitness` (the gateway copy frozen with a
relay pending, then unfrozen before it executes), `NoRelayDroppedBeforeReturnWitness`,
`ExecutedIsL1PrefixWitness` (a round trip in which a relay still pending at the gateway burn
executes on the idle gateway copy, L1 deposits are open during the return window, and after the
return a relay is dropped on the frozen idle copy), `ReturnMintChecksPassWitness` (the same run
just before the L1 mint), `RelayDropsIffFrozenWitness`, `MirrorIffNoDropWitness`,
`MirrorBreakPermanentWitness`, `ReturnMintPassesOnPrefixWitness`,
`ReturnRootCheckIffRootMatchWitness`, `BrokenReturnNeedsRootCollisionWitness` (with a node hash
that maps everything to `0`, the broken return passes and the L1 unprocessed index lands on an
operation already processed on the gateway), `ExecutedDivergencePermanentWitness`,
`MigrationsDisabledKeepL1SettlingWitness`.

Model boundaries (`MODEL-PRIORITY-MIRROR`): reject-only checks are omitted (callers and admins,
protocol versions, permanent rollup, priority mode, the settlement layer's CTM, the chain asset
handler's pauses and readiness, the gateway's whitelisting and relay caller checks, fees, gas,
the filterer; listed in the Specs header). Relays into the gateway copy come only from `C`'s L1
diamond, and no L1 account is at `L2_INTEROP_CENTER_ADDR`. The gateway executes `C`'s relays in
order; other chains' leaves do not touch `C`'s copies. The gateway pause is a free step. One clock
serves both layers. Pipeline steps set batch counters and hashes to arbitrary values. L2 execution
is not modelled: "processed" means advanced over by `processBatch`, and the binding of a batch's
items to the tree (`calculateRootPaths`, the validity proof) is outside the model, which is what
`ConsistentProcessing` stands in for. Upgrades and diamond cuts are not steps. One round trip
(`MAX_ALLOWED_NUMBER_OF_MIGRATIONS = 2`).
