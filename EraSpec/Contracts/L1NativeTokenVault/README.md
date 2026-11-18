# L1NativeTokenVault

Source: era-contracts `draft/v0.35.0` at `b17415d20`, `l1-contracts/contracts/bridge/ntv/L1NativeTokenVault.sol`
(the per-chain ledger and the interop pool, `:90-108`, `:219-298`, `:424-493`), with
`core/message-root/L1MessageRoot.sol` (`enableInterop`, `:72-94`) and the Bridgehub's chain
registration (`core/bridgehub/BridgehubBase.sol:301-347, :491-537`). `main` at `70096e2ea` has none
of this code. The vault's other models (registry, escrow, preparation, resolution) are under
[NativeTokenVaultBase](../NativeTokenVaultBase/README.md) at the older pin `c67894b9`.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the guarantees
and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact named
propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| InteropPool | [Specs/InteropPool.lean](Specs/InteropPool.lean) | [Properties/InteropPool.lean](Properties/InteropPool.lean) | [Proofs/InteropPool.lean](Proofs/InteropPool.lean) |

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
