import EraSpec.Contracts.L1NativeTokenVault.Specs.InteropPool
import EraSpec.Core.Headline

/-!
# Properties: the L1 vault's per-chain ledger and the interop pool

Statements about `EraSpec.Contracts.L1NativeTokenVault.Specs.InteropPool` (era-contracts
`draft/v0.35.0` at `b17415d20`); proofs in `EraSpec.Contracts.L1NativeTokenVault.Proofs.InteropPool`.
No hash premise anywhere. The one fact about `INTEROP_POOL_CHAIN_ID` that is used, that it is at
least `2^48`, is checked by `decide` on the constant.

Most results start from the **post-upgrade state**: `initializeUpgrade` succeeds on a
`PreUpgrade` state (below version 2, no chain enabled, no pair moved, pending chains registered,
the pool's key unregistered, the pool's slots and the ghost zero). Its "no chain enabled" is the
premise "the vault's `initializeUpgrade` ran before any `enableInterop`";
`EnableBeforeUpgradeBlocksMove` shows what happens without it.

## Flag layer

* `FlagsAfterUpgrade` (I1–I3): along every run from the post-upgrade state, an enabled chain is
  never pending, a moved pair's chain is enabled, and the pool's key is never registered, pending
  or enabled and never has a backfill. The last two are why `handleBridgeFromChain` runs the cap
  check for the pool's key with limit `chainTotalDeposited[POOL][a]`; `PoolWithdrawalsCovered`
  states the resulting bound.
* `FlagsMonotone` (I4): along every run from any state, `interopEnabled` and
  `chainBalanceInInteropPool` never go back to false; from version 2 on, the pending flag never
  goes from false to true.
* `InitializeUpgradeAtMostOnce` (I5): every run has at most one successful `initializeUpgrade`, and
  none from version 2 on.
* `LaterChainNeverPending` (I6, flags): along every run from the post-upgrade state, only a chain
  registered before the upgrade can be pending.
* `UnnamedUnregisteredChainUntouched` and `RegisteredLaterStartsAtUpgradeSlots` (I6, totals): a
  chain registered after the upgrade starts with the totals, backfill and flags it had at the
  upgrade, provided no call before its registration names it. The five mappings are new at v35, so
  at the real upgrade those values are zero. The vault does not check registration itself:
  `BackfillAcceptsUnregisteredChain` shows the owner's `setChainBalanceBackfill` accepts a chain id
  before it is registered. The hooks do not check it either; their callers do, which the model
  does not include (see the Specs header).
* `EnableBeforeUpgradeBlocksMove`: with `enableInterop` before `initializeUpgrade`, a chain ends up
  enabled and pending at once, and `moveChainBalanceToInteropPool` reverts for it until the owner's
  `markBackfilled`.

## Ledger layer

* `EnabledChainTotalsFrozen` (i): once a chain is enabled, no call writes its
  `chainTotalDeposited` or `chainTotalWithdrawn`.
* `PoolDepositIdentity` (ii): the pool's deposits of each asset equal the ghost `directToPool` plus,
  over the moved chains, `max(0, deposited + backfill - withdrawn)` at the current backfill.
  `DirectToPoolIsPoolKeyedDeposits` says what the ghost is: each call adds to it exactly the amount
  of a `toChain` credited to the pool's key, and `PoolKeyedMeansEnabledDestination` says when that
  happens: for a chain id other than the pool's, when the destination is enabled and the asset's
  origin is not. `PoolWithdrawalsCovered`: the pool's withdrawals are at most that sum.
* `MoveBackfillCommute` (iii): a move and a backfill of one pair, in either order, give the same
  result, revert included. This is the claim of the comment at `L1NativeTokenVault.sol:231-232` for
  two consecutive calls; `PoolDepositIdentity` covers any calls in between.
* `MoveAtMostOncePerPair` and `NonzeroBackfillNeverRewritten` (iv), `TotalsOnlyGrow` (v): from any
  state.

## Invariants and witnesses

`PostUpgradeEstablishesInvariants` and `CallPreservesInvariants` are the inductive form: the flag
invariant `PoolFlagInv`, `PoolIdentity` and `PoolCovered` hold after the upgrade and every call
keeps them. `PostUpgradeRunWitness`, `LaterChainWitness`, `InvariantStepWitness`,
`PoolKeyedWitness` and `MoveBackfillCommuteWitness` meet the premises with nonzero values.
`PostUpgradeRunWitness` covers the run premises of `FlagsAfterUpgrade`, `FlagsMonotone`,
`InitializeUpgradeAtMostOnce`, `LaterChainNeverPending`, `EnabledChainTotalsFrozen`,
`PoolDepositIdentity`, `PoolWithdrawalsCovered`, `DirectToPoolIsPoolKeyedDeposits`,
`MoveAtMostOncePerPair`, `NonzeroBackfillNeverRewritten` and `TotalsOnlyGrow`; `LaterChainWitness`
those of `UnnamedUnregisteredChainUntouched` and `RegisteredLaterStartsAtUpgradeSlots`.
-/

namespace Contracts.L1NativeTokenVault.InteropPool

/-! ## Invariants -/

/-- **`initializeUpgrade` ESTABLISHES THE THREE INVARIANTS.** From a `PreUpgrade` state, a
successful `initializeUpgrade` leaves a state with `PoolFlagInv`, `PoolIdentity` and
`PoolCovered`. -/
def Properties.PostUpgradeEstablishesInvariants : Prop :=
  ∀ (pre s₀ : PoolSys), PreUpgrade pre → initializeUpgrade pre = some s₀ →
    PoolFlagInv s₀ ∧ PoolIdentity s₀ ∧ PoolCovered s₀

/-- **EVERY CALL KEEPS THE THREE INVARIANTS.** From a state with `PoolFlagInv`, `PoolIdentity` and
`PoolCovered`, every successful call, of any of the nine kinds, leaves a state with all three. -/
def Properties.CallPreservesInvariants : Prop :=
  ∀ (l1 : ChainId) (call : PoolCall) (s t : PoolSys),
    PoolFlagInv s → PoolIdentity s → PoolCovered s → poolCall l1 call s = some t →
      PoolFlagInv t ∧ PoolIdentity t ∧ PoolCovered t

/-- The premises of `CallPreservesInvariants` with nonzero values: a state with the three
invariants, chain `10` enabled and 40 of asset `7` in the pool's deposits, from which
`moveChainBalanceToInteropPool(10, 7)` succeeds and brings the pool's deposits to 160 (in the
proof, the move adds `100 + 50 - 30 = 120`). -/
def Properties.InvariantStepWitness : Prop :=
  ∃ (l1 : ChainId) (s t : PoolSys),
    PoolFlagInv s ∧ PoolIdentity s ∧ PoolCovered s
      ∧ poolCall l1 (.move 10 7) s = some t
      ∧ s.interop 10 = true ∧ s.deposited interopPoolChainId 7 = 40
      ∧ t.deposited interopPoolChainId 7 = 160 ∧ t.inPool 10 7 = true

/-! ## Flag layer -/

/-- **HEADLINE (I1–I3): THE FLAGS AFTER THE UPGRADE.** For every run from the post-upgrade state
(`initializeUpgrade` on a `PreUpgrade` state), at its end:

* an enabled chain is not pending (I1);
* a pair in the pool belongs to an enabled chain (I2);
* the pool's key is not registered, not pending and not enabled, and has no backfill (I3). The
  last two are the conditions under which the cap check of `handleBridgeFromChain`
  (`L1NativeTokenVault.sol:450-456`) runs for the pool's key with limit
  `chainTotalDeposited[POOL][a] + 0`; `PoolWithdrawalsCovered` is the bound that results. -/
@[headline] def Properties.FlagsAfterUpgrade : Prop :=
  ∀ (l1 : ChainId) (pre s₀ t : PoolSys) (L : List PoolCall),
    PreUpgrade pre → initializeUpgrade pre = some s₀ → PoolRun l1 s₀ L t →
      (∀ c, t.interop c = true → t.pending c = false)
      ∧ (∀ c a, t.inPool c a = true → t.interop c = true)
      ∧ t.registered interopPoolChainId = false ∧ t.pending interopPoolChainId = false
      ∧ t.interop interopPoolChainId = false ∧ (∀ a, t.backfill interopPoolChainId a = 0)

/-- **I4: THE FLAGS ONLY MOVE ONE WAY.** Along every run, from any state: an enabled chain stays
enabled, a moved pair stays moved, and if the version is at least 2 at the start, a chain pending
at the end was pending at the start. -/
def Properties.FlagsMonotone : Prop :=
  ∀ (l1 : ChainId) (s t : PoolSys) (L : List PoolCall), PoolRun l1 s L t →
    (∀ c, s.interop c = true → t.interop c = true)
    ∧ (∀ c a, s.inPool c a = true → t.inPool c a = true)
    ∧ (2 ≤ s.initVersion → ∀ c, t.pending c = true → s.pending c = true)

/-- **I5: `initializeUpgrade` SUCCEEDS AT MOST ONCE.** Every run, from any state, has at most one
successful `initializeUpgrade`, and none if the version is at least 2 at the start
(`reinitializer(2)`). -/
def Properties.InitializeUpgradeAtMostOnce : Prop :=
  ∀ (l1 : ChainId) (s t : PoolSys) (L : List PoolCall), PoolRun l1 s L t →
    L.count PoolCall.initializeUpgrade ≤ 1
    ∧ (2 ≤ s.initVersion → L.count PoolCall.initializeUpgrade = 0)

/-- **I6, FLAGS: A CHAIN REGISTERED AFTER THE UPGRADE IS NEVER PENDING.** Along every run from the
post-upgrade state, a chain pending at the end was registered in the `PreUpgrade` state. -/
def Properties.LaterChainNeverPending : Prop :=
  ∀ (l1 : ChainId) (pre s₀ t : PoolSys) (L : List PoolCall) (c : ChainId),
    PreUpgrade pre → initializeUpgrade pre = some s₀ → PoolRun l1 s₀ L t →
      t.pending c = true → pre.registered c = true

/-- **A CALL WRITES ONLY THE CHAIN IT NAMES, AND THE POOL.** Along every run, from any state: if
`c` is not the pool's key, is not registered at the start, and no call of the run names it
(`PoolCall.chainArg`), then at the end `c` is still not registered and its pending and interop
flags, and for every asset its moved flag, totals and backfill, are as at the start. -/
def Properties.UnnamedUnregisteredChainUntouched : Prop :=
  ∀ (l1 : ChainId) (s t : PoolSys) (L : List PoolCall) (c : ChainId),
    PoolRun l1 s L t → c ≠ interopPoolChainId → s.registered c = false →
    (∀ call ∈ L, call.chainArg ≠ some c) →
      t.registered c = false ∧ t.pending c = s.pending c ∧ t.interop c = s.interop c
      ∧ ∀ a, t.inPool c a = s.inPool c a ∧ t.deposited c a = s.deposited c a
        ∧ t.withdrawn c a = s.withdrawn c a ∧ t.backfill c a = s.backfill c a

/-- **I6, TOTALS: A CHAIN REGISTERED AFTER THE UPGRADE STARTS WHERE THE UPGRADE LEFT IT.** Take a
chain `c` not registered in the `PreUpgrade` state, a run from the post-upgrade state in which no
call names `c`, and then `c`'s registration. Right after it, `c` is registered, not pending, not
enabled, has no moved pair, and its totals and backfill are those of the `PreUpgrade` state (zero
at the real upgrade, where the mappings are new). -/
def Properties.RegisteredLaterStartsAtUpgradeSlots : Prop :=
  ∀ (l1 : ChainId) (pre s₀ m t : PoolSys) (L : List PoolCall) (c : ChainId),
    PreUpgrade pre → initializeUpgrade pre = some s₀ → pre.registered c = false →
    PoolRun l1 s₀ L m → (∀ call ∈ L, call.chainArg ≠ some c) →
    poolCall l1 (.register c) m = some t →
      t.registered c = true ∧ t.pending c = false ∧ t.interop c = false
      ∧ ∀ a, t.inPool c a = false ∧ t.deposited c a = pre.deposited c a
        ∧ t.withdrawn c a = pre.withdrawn c a ∧ t.backfill c a = pre.backfill c a

/-- **THE OWNER CAN SET A BACKFILL BEFORE A CHAIN IS REGISTERED.** `setChainBalanceBackfill` has no
registration check: from a post-upgrade state, a nonzero backfill entry for a chain not
registered succeeds, and after that chain's registration it starts with that backfill, not
pending (in the proof: chain `20`, asset `7`, amount 9). So the naming premise of
`RegisteredLaterStartsAtUpgradeSlots` is needed for the backfill. -/
def Properties.BackfillAcceptsUnregisteredChain : Prop :=
  ∃ (l1 : ChainId) (pre s₀ t : PoolSys) (c a : ChainId) (x : UInt256),
    PreUpgrade pre ∧ initializeUpgrade pre = some s₀ ∧ pre.registered c = false
      ∧ pre.backfill c a = 0
      ∧ PoolRun l1 s₀ [.setBackfill c a x, .register c] t
      ∧ t.registered c = true ∧ t.pending c = false ∧ t.backfill c a = x.val ∧ x.val ≠ 0

/-- **THE ORDERING PREMISE IS NEEDED.** From a `PreUpgrade` state, the run `enableInterop(c)` then
`initializeUpgrade()` succeeds and leaves `c` enabled and pending at once, so I1 fails. In that
state `moveChainBalanceToInteropPool(c, a)` reverts for every asset. After the owner's
`markBackfilled(c)` it succeeds for every asset (in the proof: chain `10`, registered before the
upgrade, with zero totals). -/
def Properties.EnableBeforeUpgradeBlocksMove : Prop :=
  ∃ (l1 : ChainId) (pre t : PoolSys) (c : ChainId),
    PreUpgrade pre ∧ PoolRun l1 pre [.enableInterop c, .initializeUpgrade] t
      ∧ t.interop c = true ∧ t.pending c = true
      ∧ (∀ a, poolCall l1 (.move c a) t = none)
      ∧ ∃ u, poolCall l1 (.markBackfilled c) t = some u
        ∧ ∀ a, ∃ v, poolCall l1 (.move c a) u = some v

/-! ## Ledger layer -/

/-- **(i) AN ENABLED CHAIN'S TOTALS ARE FROZEN.** Along every run from the post-upgrade state: if
chain `c` is enabled at some state `s`, then no later call changes `chainTotalDeposited[c][a]` or
`chainTotalWithdrawn[c][a]`, for any asset. -/
def Properties.EnabledChainTotalsFrozen : Prop :=
  ∀ (l1 : ChainId) (pre s₀ s t : PoolSys) (L₁ L₂ : List PoolCall) (c a : ChainId),
    PreUpgrade pre → initializeUpgrade pre = some s₀ → PoolRun l1 s₀ L₁ s →
    s.interop c = true → PoolRun l1 s L₂ t →
      t.deposited c a = s.deposited c a ∧ t.withdrawn c a = s.withdrawn c a

/-- **HEADLINE (ii): THE POOL IDENTITY.** Along every run from the post-upgrade state, for every
asset `a`, `chainTotalDeposited[POOL][a]` is the ghost `directToPool a` (what `toChain` calls
credited to the pool's key; `DirectToPoolIsPoolKeyedDeposits`) plus, over every chain `c` with
`chainBalanceInInteropPool[c][a]`, `max(0, chainTotalDeposited[c][a] + chainBalanceBackfill[c][a]
- chainTotalWithdrawn[c][a])`, with the backfill as it is now. The ghost also absorbs hook calls
whose chain argument is the pool id itself, which the model allows (the hooks take any chain) and
the hooks' callers rule out (not modelled); `PoolKeyedMeansEnabledDestination` is stated for a
chain id other than the pool's. The ghost is pinned step by step (`DirectToPoolIsPoolKeyedDeposits`);
no run-level statement sums it over the run's calls. -/
@[headline] def Properties.PoolDepositIdentity : Prop :=
  ∀ (l1 : ChainId) (pre s₀ t : PoolSys) (L : List PoolCall),
    PreUpgrade pre → initializeUpgrade pre = some s₀ → PoolRun l1 s₀ L t →
      ∀ a, t.deposited interopPoolChainId a = t.directToPool a
        + ∑ c : ChainId, (if t.inPool c a = true
            then t.deposited c a + t.backfill c a - t.withdrawn c a else 0)

/-- **THE POOL'S WITHDRAWALS ARE COVERED.** Along every run from the post-upgrade state, for every
asset, `chainTotalWithdrawn[POOL][a]` is at most the right-hand side of `PoolDepositIdentity`. -/
@[headline] def Properties.PoolWithdrawalsCovered : Prop :=
  ∀ (l1 : ChainId) (pre s₀ t : PoolSys) (L : List PoolCall),
    PreUpgrade pre → initializeUpgrade pre = some s₀ → PoolRun l1 s₀ L t →
      ∀ a, t.withdrawn interopPoolChainId a ≤ t.directToPool a
        + ∑ c : ChainId, (if t.inPool c a = true
            then t.deposited c a + t.backfill c a - t.withdrawn c a else 0)

/-- **WHAT THE GHOST COUNTS.** Every successful call adds to `directToPool a` exactly
`poolKeyedDeposit s call a`: the amount of a `toChain` call for asset `a` whose balance is tracked
under the pool's key (`trackedBalance s chain origin = (true, POOL)`), and nothing for any other
call. -/
def Properties.DirectToPoolIsPoolKeyedDeposits : Prop :=
  ∀ (l1 : ChainId) (call : PoolCall) (s t : PoolSys) (a : AssetId),
    poolCall l1 call s = some t → t.directToPool a = s.directToPool a + poolKeyedDeposit s call a

/-- **WHAT "CREDITED TO THE POOL" MEANS.** For every state and every chain id `c` other than the
pool's key, `_trackedBalance(c, origin)` returns `(true, POOL)` exactly when `c` is enabled and
`origin` is not. With `DirectToPoolIsPoolKeyedDeposits`: a `toChain` call whose chain is not the
pool's key adds to the ghost exactly when its destination is enabled and its asset's origin is
not. -/
def Properties.PoolKeyedMeansEnabledDestination : Prop :=
  ∀ (s : PoolSys) (c o : ChainId), c ≠ interopPoolChainId →
    (trackedBalance s c o = (true, interopPoolChainId) ↔ s.interop c = true ∧ s.interop o = false)

/-- Both sides of `PoolKeyedMeansEnabledDestination` occur: at the end state of
`PostUpgradeRunWitness`, chains `10` and `20` are enabled, so a deposit to `10` of an asset from
L1 (chain `1`) is credited to the pool, and one of an asset from `20` is not tracked. -/
def Properties.PoolKeyedWitness : Prop :=
  ∃ (s : PoolSys) (c o o' : ChainId), c ≠ interopPoolChainId
    ∧ s.interop c = true ∧ s.interop o = false ∧ s.interop o' = true
    ∧ trackedBalance s c o = (true, interopPoolChainId)
    ∧ trackedBalance s c o' = (false, interopPoolChainId)

/-- **(iii) MOVE AND BACKFILL COMMUTE.** For every state, chain, asset and amount,
`moveChainBalanceToInteropPool(c, a)` then the backfill entry `(c, a, x)` gives the same result as
the backfill entry then the move: the same state, or a revert on both sides. No premise is
needed: if `c` is not enabled, or the pair already has a nonzero backfill, both orders revert. -/
@[headline] def Properties.MoveBackfillCommute : Prop :=
  ∀ (s : PoolSys) (c a : ChainId) (x : UInt256),
    (moveChainBalanceToInteropPool s c a).bind (fun m => setChainBalanceBackfill m c a x)
      = (setChainBalanceBackfill s c a x).bind (fun m => moveChainBalanceToInteropPool m c a)

/-- Both orders succeed with nonzero values, and the late backfill credits the pool less than its
amount: chain `10` enabled, with `chainTotalDeposited = 20`, `chainTotalWithdrawn = 25` and no
backfill for asset `8`. Moving, then backfilling 9, adds `0 + (20 + 9 - 25) = 4` to the pool,
which is what the other order adds. -/
def Properties.MoveBackfillCommuteWitness : Prop :=
  ∃ (s u : PoolSys),
    s.interop 10 = true ∧ s.backfill 10 8 = 0 ∧ s.deposited 10 8 = 20 ∧ s.withdrawn 10 8 = 25
      ∧ (moveChainBalanceToInteropPool s 10 8).bind (fun m => setChainBalanceBackfill m 10 8 9)
          = some u
      ∧ (setChainBalanceBackfill s 10 8 9).bind (fun m => moveChainBalanceToInteropPool m 10 8)
          = some u
      ∧ u.deposited interopPoolChainId 8 = s.deposited interopPoolChainId 8 + 4
      ∧ u.backfill 10 8 = 9 ∧ u.inPool 10 8 = true

/-- **(iv) A PAIR MOVES AT MOST ONCE.** Every run, from any state, has at most one successful
`moveChainBalanceToInteropPool(c, a)` for each pair, and none if the pair is already in the pool at
the start. -/
def Properties.MoveAtMostOncePerPair : Prop :=
  ∀ (l1 : ChainId) (s t : PoolSys) (L : List PoolCall) (c a : ChainId), PoolRun l1 s L t →
    L.count (PoolCall.move c a) ≤ 1 ∧ (s.inPool c a = true → L.count (PoolCall.move c a) = 0)

/-- **(iv) A NONZERO BACKFILL IS NEVER REWRITTEN.** Along every run, from any state, a nonzero
`chainBalanceBackfill[c][a]` at the start is the same at the end. -/
def Properties.NonzeroBackfillNeverRewritten : Prop :=
  ∀ (l1 : ChainId) (s t : PoolSys) (L : List PoolCall) (c a : ChainId), PoolRun l1 s L t →
    s.backfill c a ≠ 0 → t.backfill c a = s.backfill c a

/-- **(v) THE TOTALS ONLY GROW.** Along every run, from any state, every
`chainTotalDeposited[k][a]` and `chainTotalWithdrawn[k][a]`, the pool's included, is at least its
value at the start. -/
def Properties.TotalsOnlyGrow : Prop :=
  ∀ (l1 : ChainId) (s t : PoolSys) (L : List PoolCall), PoolRun l1 s L t →
    ∀ k a, s.deposited k a ≤ t.deposited k a ∧ s.withdrawn k a ≤ t.withdrawn k a

/-! ## Witnesses -/

/-- **THE RUN PREMISES, MET WITH NONZERO VALUES.** What the statement records: a `PreUpgrade` state,
its post-upgrade state `s₀` with chain `10` pending, a run `L₁` to a state `s` where `10` is enabled
with totals 100 and 30 and backfill 50 for asset `7`, and a run `L₂` from `s` that contains a
deposit of 40 and a withdrawal of 10 for chain `10` and ends in `t`. At `t`: `10`'s totals for `7`
are still 100 and 30; the pool's deposits of `7` are 165, with ghost 45, and its withdrawals 70;
for asset `8`, `10` has totals 20 and 25 and backfill 9, and the pool's deposits are 4 with ghost
0; chain `20`, not registered before the upgrade, is registered and enabled; `L₂` moves `(10, 7)`
once, and the whole run from the `PreUpgrade` state has one `initializeUpgrade`. The deposit of 40
succeeds from `s` and is credited to the pool.

The instantiation (L1 is chain `1`; asset `7` is L1-native, asset `8` comes from chain `30`): `L₁`
deposits 100 of `7` and 20 of `8` to `10`, withdraws 30 and 25 while `10` is pending, sets the
backfill of `7` to 50, marks `10` backfilled and enables it. `L₂` deposits 40 of `7` to `10`, moves
both pairs, backfills `8` with 9 after its move, registers and enables `20`, deposits 5 of `7` to
it, and withdraws 60 to `20` and 10 to `10`. So `165 = 45 + (100 + 50 - 30)` and
`4 = 0 + (20 + 9 - 25)`. -/
def Properties.PostUpgradeRunWitness : Prop :=
  ∃ (l1 : ChainId) (pre s₀ s t : PoolSys) (L₁ L₂ : List PoolCall),
    PreUpgrade pre ∧ initializeUpgrade pre = some s₀ ∧ PoolRun l1 s₀ L₁ s ∧ PoolRun l1 s L₂ t
      ∧ PoolRun l1 pre (PoolCall.initializeUpgrade :: (L₁ ++ L₂)) t
      ∧ s₀.pending 10 = true ∧ s.interop 10 = true ∧ s.pending 10 = false
      ∧ s.deposited 10 7 = 100 ∧ s.withdrawn 10 7 = 30 ∧ s.backfill 10 7 = 50
      ∧ PoolCall.toChain 10 7 40 l1 ∈ L₂ ∧ PoolCall.fromChain 10 7 10 l1 ∈ L₂
      ∧ t.deposited 10 7 = 100 ∧ t.withdrawn 10 7 = 30 ∧ t.backfill 10 7 = 50
      ∧ t.inPool 10 7 = true ∧ t.inPool 10 8 = true
      ∧ t.directToPool 7 = 45 ∧ t.deposited interopPoolChainId 7 = 165
      ∧ t.withdrawn interopPoolChainId 7 = 70
      ∧ t.deposited 10 8 = 20 ∧ t.withdrawn 10 8 = 25 ∧ t.backfill 10 8 = 9
      ∧ t.directToPool 8 = 0 ∧ t.deposited interopPoolChainId 8 = 4
      ∧ pre.registered 20 = false ∧ t.registered 20 = true ∧ t.interop 20 = true
      ∧ (L₂.count (PoolCall.move 10 7) = 1)
      ∧ (PoolCall.initializeUpgrade :: (L₁ ++ L₂)).count PoolCall.initializeUpgrade = 1
      ∧ ∃ s', poolCall l1 (.toChain 10 7 40 l1) s = some s'
        ∧ poolKeyedDeposit s (.toChain 10 7 40 l1) 7 = 40

/-- **THE I6 PREMISES, MET.** A `PreUpgrade` state in which chain `20` is not registered, a run of
eleven calls from its post-upgrade state, none naming `20` and one of them
`moveChainBalanceToInteropPool(10, 7)`, then `20`'s registration: `20` is registered, not pending,
not enabled, with zero total deposited and zero backfill for asset `7`. -/
def Properties.LaterChainWitness : Prop :=
  ∃ (l1 : ChainId) (pre s₀ m t : PoolSys) (L : List PoolCall),
    PreUpgrade pre ∧ initializeUpgrade pre = some s₀ ∧ pre.registered 20 = false
      ∧ PoolRun l1 s₀ L m ∧ L.length = 11 ∧ (∀ call ∈ L, call.chainArg ≠ some 20)
      ∧ PoolCall.move 10 7 ∈ L
      ∧ poolCall l1 (.register 20) m = some t
      ∧ t.registered 20 = true ∧ t.pending 20 = false ∧ t.interop 20 = false
      ∧ pre.deposited 20 7 = 0 ∧ t.deposited 20 7 = 0 ∧ t.backfill 20 7 = 0

end Contracts.L1NativeTokenVault.InteropPool
