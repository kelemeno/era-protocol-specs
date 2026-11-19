# L1NativeTokenVault

## Headline guarantees

About era-contracts `draft/v0.35.0` head `b17415d20`. Statements are `….Properties.<Name>`, proofs
`….<Name>`, in the namespaces `Contracts.L1NativeTokenVault.InteropPool` (`InteropPool`) and
`Contracts.L1NativeTokenVault.Bulkhead` (`Bulkhead`). "The post-upgrade state" is any state reached by
a successful `initializeUpgrade` from a state in which no chain is enabled, no pair is in the pool,
pending chains are registered, the pool's key is unregistered and its totals, backfill and ghost are
zero. A run is any sequence of successful calls of the modelled entry points. No statement takes a
hash premise.

- `InteropPool.FlagsAfterUpgrade`: along every run from the post-upgrade state, an enabled chain is
  never pending, a moved pair's chain is enabled, and the pool's key is never registered, pending
  or enabled and has no backfill. Premise: the run starts at the post-upgrade state.
- `InteropPool.PoolDepositIdentity`: along such a run, the pool's deposits of each asset are the
  deposits credited to the pool's key plus, over the moved chains, `max(0, deposited + backfill -
  withdrawn)` at the current backfill. Same premise.
- `InteropPool.PoolWithdrawalsCovered`: along such a run the pool's withdrawals of each asset are at
  most its deposits. Same premise.
- `InteropPool.MoveBackfillCommute`: `moveChainBalanceToInteropPool` and a backfill entry for one
  pair give the same result in either order, reverts included. No premise.
- `Bulkhead.BulkheadDisabledChainReleaseBound`: over any run, what is released for a chain `c` and
  an asset `a` totals at most the growth of `deposited + backfill` plus the starting headroom if it
  is positive, whatever the other calls are. Premises: the run starts after the upgrade with `c` not
  pending, `c` is disabled at the end and is not the pool's key, and `a`'s origin is not `c` at the
  start or the end.
- `Bulkhead.BulkheadEnabledSetReleaseBound`: the chains enabled at the time of their withdrawals
  jointly release at most the pool's deposits (moves and pool backfill credits included) less the
  pool's starting `withdrawn`. Premise: the run starts after the upgrade.
- `Bulkhead.BulkheadEscrowBacksHeadroom`: from the upgrade state, for an L1-native asset, if the
  backfills fit the escrow and no moved chain is in deficit, `bridgedOut` covers the unmoved chains'
  and the pool's headrooms. Premises: those two (`OPS-CONFIG` for the owner's backfill amounts).
- `Bulkhead.BulkheadHonestWithdrawalSucceeds`: a registered, disabled, non-pending chain's
  withdrawal of an L1-native asset within its headroom passes both hooks' checks. Premises: the
  deployed constants, a run from the upgrade state, the backfills fit the starting `bridgedOut` plus
  the populated amounts, no key is in deficit, and the pair's `deposited + backfill` is below
  `2^256`.

The refinement lemmas `Bulkhead.BulkheadRunsArePoolRuns` (the two transcriptions agree) and
`LedgerRefinement` (every successful `b17415d20` hook is the `bridgedOut`-only hook of the older
vault models) tie these to the other vault models.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the guarantees
and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact named
propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| InteropPool | [Specs/InteropPool.lean](Specs/InteropPool.lean) | [Properties/InteropPool.lean](Properties/InteropPool.lean) | [Proofs/InteropPool.lean](Proofs/InteropPool.lean) |
| BulkheadIsolation | [Specs/BulkheadIsolation.lean](Specs/BulkheadIsolation.lean) | [Properties/BulkheadIsolation.lean](Properties/BulkheadIsolation.lean) | [Proofs/BulkheadIsolation.lean](Proofs/BulkheadIsolation.lean), step lemmas in [Proofs/BulkheadIsolationSteps.lean](Proofs/BulkheadIsolationSteps.lean) |
| BulkheadPoolSimulation | [Specs/BulkheadPoolSimulation.lean](Specs/BulkheadPoolSimulation.lean) | [Properties/BulkheadPoolSimulation.lean](Properties/BulkheadPoolSimulation.lean) | [Proofs/BulkheadPoolSimulation.lean](Proofs/BulkheadPoolSimulation.lean) |
| LedgerRefinement | [Specs/LedgerRefinement.lean](Specs/LedgerRefinement.lean) | [Properties/LedgerRefinement.lean](Properties/LedgerRefinement.lean) | [Proofs/LedgerRefinement.lean](Proofs/LedgerRefinement.lean) |

Namespace `Contracts.L1NativeTokenVault.InteropPool`. Statements are
`Contracts.L1NativeTokenVault.InteropPool.Properties.*`; each certificate has the same name
without the `Properties` segment. No statement takes a hash premise; the only fact about
`INTEROP_POOL_CHAIN_ID` used is that it is at least `2^48`, checked by `decide` on the constant.

## The model

`PoolSys` holds `bridgedOut`, `chainTotalDeposited`, `chainTotalWithdrawn`,
`chainBalanceBackfill`, `chainBalanceInInteropPool`, `chainBalanceBackfillPending`, the vault's
initializer version, the message root's `interopEnabled` flags, the Bridgehub's registered chain
ids, and a ghost `directToPool`. A `PoolRun` is a sequence of successful calls of nine kinds:
the two accounting hooks (`toChain`, `fromChain`), one entry of `setChainBalanceBackfill`,
`markBackfilled`, `moveChainBalanceToInteropPool`, `enableInterop`, `initializeUpgrade`,
chain registration, and one entry of `populateBridgedOut`. A revert is no step and arithmetic is
checked. The hooks read the interop flags from the state, so the keying of every deposit and
withdrawal follows the message root's actual flags.

The function shapes were re-checked line by line against `b17415d20`.

Most results start from the **post-upgrade state**: `initializeUpgrade` succeeding on a
`PreUpgrade` state, in which no chain is enabled yet and the pool's slots are zero.

## Results

- **Flags (I1–I6).** Along every run from the post-upgrade state, an enabled chain is never
  pending, a moved pair belongs to an enabled chain, and the pool's key is never registered,
  pending or enabled and has no backfill (`FlagsAfterUpgrade`). The interop and moved flags only
  go one way, and from version 2 on the pending flag only clears (`FlagsMonotone`).
  `initializeUpgrade` succeeds at most once (`InitializeUpgradeAtMostOnce`). Only chains registered
  before the upgrade are ever pending (`LaterChainNeverPending`). A chain registered later starts
  with the slots it had at the upgrade (zero, as the mappings are new), provided no call named it
  first (`RegisteredLaterStartsAtUpgradeSlots`, from the frame `UnnamedUnregisteredChainUntouched`).
  The owner's `setChainBalanceBackfill` does not check registration, so a backfill set on a chain
  id before its registration is still there when it registers (`BackfillAcceptsUnregisteredChain`).
- **The ordering premise.** If `enableInterop` runs before `initializeUpgrade`, a chain is enabled
  and pending at once and `moveChainBalanceToInteropPool` reverts for it until `markBackfilled`
  (`EnableBeforeUpgradeBlocksMove`).
- **Ledger.** Once a chain is enabled, nothing writes its own totals
  (`EnabledChainTotalsFrozen`). The pool's deposits of each asset are the deposits credited to the
  pool's key (the ghost) plus, over the moved chains, `max(0, deposited + backfill - withdrawn)` at
  the current backfill (`PoolDepositIdentity`), and the pool's withdrawals are at most that sum
  (`PoolWithdrawalsCovered`). The ghost grows exactly by the pool-keyed `toChain` amounts
  (`DirectToPoolIsPoolKeyedDeposits`), which for a chain id other than the pool's are the deposits
  to enabled chains of assets whose origin is not enabled (`PoolKeyedMeansEnabledDestination`).
- **Move and late backfill.** `moveChainBalanceToInteropPool` and a backfill entry for one pair
  give the same result in either order, reverts included, from any state
  (`MoveBackfillCommute`): the claim of the comment at `L1NativeTokenVault.sol:231-232`.
  `PoolDepositIdentity` covers any calls in between.
- **Once only.** A pair moves at most once in any run (`MoveAtMostOncePerPair`), a nonzero backfill
  is never rewritten (`NonzeroBackfillNeverRewritten`), and every total only grows
  (`TotalsOnlyGrow`), from any state.
- **Inductive form.** `PostUpgradeEstablishesInvariants` and `CallPreservesInvariants`:
  `PoolFlagInv`, `PoolIdentity` and `PoolCovered` hold after the upgrade and every call keeps them.

Witnesses: `PostUpgradeRunWitness` (a 17-call run with deposits and uncapped withdrawals while
pending, a backfill, enabling, both moves, a late backfill in deficit, a later chain, and pool
withdrawals; the pool ends at `165 = 45 + (100 + 50 - 30)` of one asset and `4 = 0 + (20 + 9 - 25)`
of the other), `LaterChainWitness`, `InvariantStepWitness`, `PoolKeyedWitness`,
`MoveBackfillCommuteWitness`.

## Model boundaries

- The hooks are steps for any chain argument, asset, amount and value of `originChainId[asset]`;
  their callers' restrictions (deposits only to registered chains, withdrawal and failed-deposit
  proofs) are not modelled. Caller checks (`onlyOwner`, the proxy-admin check, the Bridgehub
  owner), the second-proof-system checks of `enableInterop`, the Bridgehub's other
  `_validateChainParams` checks and pauses are dropped: each only rejects. So the model admits
  more runs than the contracts.
- Chain registration is the Bridgehub's validated path. The chain asset handler's
  `registerNewZKChain` skips `_validateChainParams`; on L1 it runs only for a chain returning from
  a settlement layer, which is already registered. That is argued from source, not modelled.
- The vault's message root and the message root's vault are the modelled ones (`OPS-CONFIG`).
- `initialize()` is not a step; it only moves the version from 0 to 1.
- Not modelled: the token registry (`originChainId` is a per-call input), events, the escrowed
  balances themselves, and whether the backfill amounts governance sets are right.
- Implementation correspondence (storage layout, `uint256` arithmetic, call frames) is open, as
  for every model here.

## BulkheadIsolation and BulkheadPoolSimulation

Namespace `Contracts.L1NativeTokenVault.Bulkhead`. Statements are
`Contracts.L1NativeTokenVault.Bulkhead.Properties.*`; each proof has the same name without the
`Properties` segment. No statement takes a hash premise. Read them with the
[assumption register](../../../ASSUMPTIONS.md): `MODEL-BULKHEAD-CAP` for what the model keeps and
drops, `MODEL-ESCROW` for `bridgedOut` against the vault's token balance, and `OPS-CONFIG` for the
owner's backfill amounts.

`BulkheadIsolation` transcribes the same code as InteropPool, for a different question: what one
chain can release from the vault when its proofs are not trusted. The model has both accounting
hooks, the owner's backfill calls, the permissionless move to the interop pool,
`initializeUpgrade`, `populateBridgedOut`, `L1MessageRoot.enableInterop`, chain registration and
the write-once origin map. A withdrawal or failed-deposit claim (`fromChain c a x`) may be any asset
and any `uint256` amount for any registered chain. The two transcriptions were written separately;
`BulkheadPoolSimulation` proves that they agree. A third transcription of the cap's writers,
`Codegen.VaultPreparationSlice` topic `L1PerChainCapAtV35`
([Specs/L1PerChainCapAtV35.lean](../../Codegen/VaultPreparationSlice/Specs/L1PerChainCapAtV35.lean)),
lets the interop flags and the origin map change freely at every step; it is not connected to these
two.

- Release bounds. Over any run that starts after the upgrade with chain `c` not pending, in which
  `c` stays disabled and the asset is not native to `c`, what is released for `(c, a)` is at most
  `deposited + backfill` at the end less `withdrawn` at the start
  (`BulkheadDisabledChainReleaseBound`; per key, `BulkheadKeyReleaseBound`). The chains enabled at
  the time of their withdrawals jointly release at most the pool's deposits, moves and pool backfill
  credits included, less the pool's starting `withdrawn` (`BulkheadEnabledSetReleaseBound`). A capped
  call ends within the limit (`BulkheadCappedWithdrawalWithinLimit`), and no call for one chain
  changes another chain's counters (`BulkheadCrossChainFrame`).
- The shared escrow. From the upgrade state, for an L1-native asset, `bridgedOut` plus the
  backfills plus the deficits of moved chains equals the starting `bridgedOut`, the populated legacy
  amounts, the unmoved chains' headrooms and the pool's headroom (`BulkheadLedgerIdentity`). If the
  backfills fit the escrow and no moved chain is in deficit, `bridgedOut` covers those headrooms
  (`BulkheadEscrowBacksHeadroom`). With no key in deficit, a disabled chain's withdrawal within its
  headroom passes both checks, provided the pair's `deposited + backfill` is a `uint256`
  (`BulkheadHonestWithdrawalSucceeds`; for assets not native to L1, from any state,
  `BulkheadBridgedWithdrawalSucceeds`). No deficit, once reached with no chain pending, persists
  (`BulkheadNoDeficitPersists`).
- Countermodels, on the deployed constants from the upgrade state. A pending chain is uncapped: it
  can withdraw `bridgedOut` past its headroom so another chain's withdrawal within its own headroom
  reverts, and in an asset not native to L1 any amount (`BulkheadPendingChainUncapped`).
  `markBackfilled` reads no counter, so it can close a window with `withdrawn > deposited + backfill`;
  the chain's withdrawals of that asset then revert until deposits cover the difference
  (`BulkheadMarkBackfilledKeepsDeficit`).
- The same code as InteropPool. On `uint256` arguments, every successful call of the bulkhead model
  is the matching successful InteropPool call, with the same effect on the storage both models keep
  (`BulkheadStepIsPoolCall`; `registerAsset`, which writes only the origin map, has no
  counterpart). A bulkhead upgrade state is an InteropPool post-upgrade state
  (`BulkheadUpgradeStateIsPostUpgrade`). So every bulkhead run from its upgrade state is an
  InteropPool run from its post-upgrade state (`BulkheadRunsArePoolRuns`; from any corresponding
  state, `BulkheadRunIsPoolRun`), and the InteropPool results above hold of it.

The witnesses `BulkheadCapWitness` and `BulkheadLedgerWitness` instantiate the premises with
nonzero values and show the release bounds and the escrow bound tight.
`BulkheadPoolSimulationWitness` meets the simulation's premises with a fifteen-call run.

Model boundaries of the bulkhead model (InteropPool's boundaries on caller checks, registration,
contract wiring and implementation correspondence apply to it too):

- A withdrawal's chain is a registered chain (the guard `registered c` on both hooks). That L1
  accepts no withdrawal or claim for an unregistered chain id is argued from
  `L1AssetRouter.sol:264-269` and `L1MessageRoot.sol:96-120`, not proved. For an L1-native asset
  the guard matters for L1's own chain id (such a withdrawal would not be tracked), for
  `INTEROP_POOL_CHAIN_ID` (it would draw on the pool) and for an unregistered id the owner
  backfilled; any other unregistered id would be capped at zero.
- That a disabled chain's token transfers all go through the vault
  (`L1AssetRouter._checkAssetHandlerAllowed`, `:271-288`) is argued, not proved. Enabled chains'
  transfers through other handlers are not counted under the pool key.
- The token transfer or mint after a hook is not modelled, so "a withdrawal passes" means the
  vault's hook passes. Whether the owner's backfills fit the escrow is a premise (`OPS-CONFIG`).
- The ledger results start at the post-`initializeUpgrade` state; a vault whose `initializeUpgrade`
  runs late is covered only by the release bounds.

## LedgerRefinement: the `bridgedOut`-only models

Namespace `Contracts.L1NativeTokenVault.LedgerRefinement`. Three older models keep `bridgedOut`
alone: NativeTokenVaultBase's `L1Ledger` hooks (`TrackerHooks`), the registry-and-escrow model
`Contracts.NativeTokenVault`, and its `populateBridgedOut` extension `EscrowLedgerAtHead`. On agreeing
`bridgedOut` maps, a successful `InteropPool` deposit or inbound hook is the `L1Ledger` hook
(`PoolToChainIsL1ToChain`, `PoolFromChainIsL1FromChain`) and moves `bridgedOut` as the registry
model's `bridgeOut`/`bridgeIn`, meeting its `InsufficientChainBalance` guard
(`PoolHooksAreRegistryLedgerSteps`); a population entry is `populateAtHead`
(`PoolPopulateIsPopulateAtHead`); no other call writes `bridgedOut` (`PoolOtherCallsKeepBridgedOut`).
The converse fails: the per-chain cap rejects an inbound transfer the `L1Ledger` hook accepts
(`PerChainCapIsStricterThanL1Ledger`). `LedgerRefinementWitness` meets the outbound premises with a
nonzero native deposit.
