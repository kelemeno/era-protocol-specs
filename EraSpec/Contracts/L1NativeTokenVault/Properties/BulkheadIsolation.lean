import EraSpec.Contracts.L1NativeTokenVault.Specs.BulkheadIsolation
import EraSpec.Core.Headline

/-!
# Properties: what one chain can release from the L1 vault under the v35 per-chain cap

Statements about `EraSpec.Contracts.L1NativeTokenVault.Specs.BulkheadIsolation` (source
`b17415d20`).  Proofs are in `EraSpec.Contracts.L1NativeTokenVault.Proofs.BulkheadIsolation`.

`releasedFrom c a ls` is the sum of the amounts of the run's `fromChain c a ·` calls, whose
amounts and assets the model leaves free (a chain whose proofs are not trusted chooses them);
`capHeadroom s k a` is `deposited + backfill - withdrawn`.

* `BulkheadCappedWithdrawalWithinLimit`: a successful withdrawal counted under a non-pending key
  ends with `withdrawn ≤ deposited + backfill` there.
* `BulkheadCrossChainFrame`: a call for chain `c` leaves the counters, backfill and flags of every
  chain id `d ≠ c` other than the pool key unchanged (the pending flag except under
  `initializeUpgrade`); a call for no chain leaves those of every id other than the pool key.
* `BulkheadKeyReleaseBound`: over any run from a state where the upgrade has run and a key is not
  pending, the withdrawals counted under that key total exactly the growth of its `withdrawn`, and
  at most `deposited + backfill` at the end less `withdrawn` at the start.
* `BulkheadDisabledChainReleaseBound` (headline, part (b)): over any run that starts after the
  upgrade with chain `c` not pending and ends with `c` still disabled, for an asset whose origin is
  not `c` at the start or the end, the amounts released for `(c, a)` total at most the growth of
  `deposited + backfill` plus the starting headroom if it is positive, whatever the other calls,
  chains and amounts are.
* `BulkheadEnabledSetReleaseBound`: the same for every chain that is enabled at the time of its
  withdrawal, jointly, under the pool key, counting moves and pool backfill credits as deposits.
* `BulkheadLedgerIdentity` (part (d)): from the upgrade state, for an L1-native asset, an exact
  identity between `bridgedOut`, the backfills, the deficits of moved chains, the headroom of every
  chain whose balance has not moved, and the pool's headroom.
* `BulkheadEscrowBacksHeadroom`: if the backfills fit in the pre-upgrade `bridgedOut` plus the
  populated legacy amounts, and no moved chain is in deficit, `bridgedOut` covers the sum of the
  unmoved chains' headrooms and the pool's.
* `BulkheadHonestWithdrawalSucceeds`: under those premises and no deficit anywhere, a registered,
  disabled, non-pending chain's withdrawal within its headroom passes `_handleBridgeFromChain`,
  provided `deposited + backfill` is a `uint256`.  `BulkheadBridgedWithdrawalSucceeds` is the same
  for an asset not native to L1, from any state, with no condition on other chains.
* `BulkheadNoDeficitPersists`: once no chain is pending and no key is in deficit, both stay so.
* `BulkheadRunsStayWellFormed`: runs from the upgrade state keep `CapWF`.

Countermodels, each a concrete run from the upgrade state on the deployed constants:

* `BulkheadPendingChainUncapped`: a pending chain withdraws more than its headroom in an L1-native
  asset, after which another chain's withdrawal within its own unchanged headroom reverts on
  `bridgedOut`; in an asset not native to L1 the pending chain's withdrawals have no bound at all.
* `BulkheadMarkBackfilledKeepsDeficit`: `markBackfilled` reads no counter, so it closes a window
  with `withdrawn > deposited + backfill`; then every withdrawal of that `(chain, asset)` reverts,
  and along any later run in which the chain stays disabled, what is released for it is at most
  `deposited + backfill` at the end less that withdrawn total, the (nonzero) backfill never
  changing.

Witnesses: `BulkheadCapWitness` and `BulkheadLedgerWitness` instantiate the premises of the
positive statements with nonzero values, and show the release bounds and the escrow bound tight.
-/

namespace Contracts.L1NativeTokenVault.Bulkhead

open Finset

/-- **RUNS FROM THE UPGRADE STATE KEEP THE INVARIANT.**  On constants satisfying `CapConfig.Ok`,
every state reachable from the upgrade state satisfies `CapWF`: registered ids pass the Bridgehub's
checks, interop is enabled only on registered non-pending chains, only enabled chains have moved
balances, the pool key is never pending and has no backfill, and every stored value is a
`uint256`. -/
def Properties.BulkheadRunsStayWellFormed : Prop :=
  ∀ (cfg : CapConfig) (s0 s : CapState) (ls : List CapLabel),
    cfg.Ok → CapUpgradeState cfg s0 → CapRun cfg s0 ls s → CapWF cfg s

/-- **(a) A CAPPED WITHDRAWAL STAYS WITHIN THE LIMIT.**  A successful `_handleBridgeFromChain`
whose call is tracked under key `k`, with `k` not pending, adds exactly the amount to `withdrawn`
at `k`, leaves `deposited` and `backfill` there, and ends with `withdrawn ≤ deposited + backfill`
at `k`. -/
def Properties.BulkheadCappedWithdrawalWithinLimit : Prop :=
  ∀ (cfg : CapConfig) (s t : CapState) (c a x k : ℕ),
    capStep cfg (.fromChain c a x) s = some t →
    capTrackedKey cfg s c (s.origin a) = some k → s.pending k = false →
      t.withdrawn k a = s.withdrawn k a + x ∧ t.deposited k a = s.deposited k a ∧
        t.backfill k a = s.backfill k a ∧ t.withdrawn k a ≤ t.deposited k a + t.backfill k a

/-- **(c) CROSS-CHAIN FRAME.**  A successful call leaves all of `deposited`, `withdrawn`,
`backfill`, `inPool`, the interop flag and the registration of every chain id `d` that is not the
pool key and not the call's own chain unchanged, for every asset; so does its pending flag, except
under `initializeUpgrade`.  A call with no chain (`initializeUpgrade`, `registerAsset`, `populate`)
satisfies this for every `d` other than the pool key. -/
def Properties.BulkheadCrossChainFrame : Prop :=
  ∀ (cfg : CapConfig) (s t : CapState) (l : CapLabel) (d : ℕ),
    capStep cfg l s = some t → d ≠ cfg.pool → l.chain? ≠ some d →
      t.deposited d = s.deposited d ∧ t.withdrawn d = s.withdrawn d ∧
        t.backfill d = s.backfill d ∧ t.inPool d = s.inPool d ∧ t.interop d = s.interop d ∧
        t.registered d = s.registered d ∧ (l ≠ .initializeUpgrade → t.pending d = s.pending d)

/-- **(b) RELEASE BOUND PER KEY.**  For any run from a state where the upgrade has run and key `k`
is not pending, and any asset: the amounts of the run's withdrawals counted under `k` total exactly
`withdrawn` at the end less at the start; and they are at most `deposited + backfill` at the end
less `withdrawn` at the start, hence at most the growth of `deposited + backfill` plus the starting
headroom when it is positive (all in truncated `ℕ` subtraction). -/
def Properties.BulkheadKeyReleaseBound : Prop :=
  ∀ (cfg : CapConfig) (s t : CapState) (ls : List CapLabel) (k a : ℕ),
    CapRun cfg s ls t → s.upgraded = true → s.pending k = false →
      releasedUnderKey cfg k a s ls = t.withdrawn k a - s.withdrawn k a ∧
        s.withdrawn k a ≤ t.withdrawn k a ∧
        releasedUnderKey cfg k a s ls ≤ t.deposited k a + t.backfill k a - s.withdrawn k a ∧
        releasedUnderKey cfg k a s ls ≤
          (t.deposited k a + t.backfill k a - (s.deposited k a + s.backfill k a)) +
            (s.deposited k a + s.backfill k a - s.withdrawn k a)

/-- **HEADLINE (b): A DISABLED CHAIN RELEASES AT MOST ITS OWN HEADROOM.**  Take any run from a
state where the upgrade has run and chain `c` (not the pool key) is not pending, with `c` still
disabled at the end, and an asset whose origin is not `c` at the start or the end.  Whatever calls
the run contains, for any chains and amounts, the amounts of its `fromChain c a ·` calls total
exactly the growth of `withdrawn[c][a]`, and at most `deposited + backfill` of `(c, a)` at the end
less `withdrawn` at the start: the growth of `deposited + backfill` plus the starting headroom when
it is positive. -/
@[headline] def Properties.BulkheadDisabledChainReleaseBound : Prop :=
  ∀ (cfg : CapConfig) (s t : CapState) (ls : List CapLabel) (c a : ℕ),
    CapRun cfg s ls t → s.upgraded = true → s.pending c = false → t.interop c = false →
    c ≠ cfg.pool → s.origin a ≠ c → t.origin a ≠ c →
      releasedFrom c a ls = t.withdrawn c a - s.withdrawn c a ∧
        releasedFrom c a ls ≤ t.deposited c a + t.backfill c a - s.withdrawn c a ∧
        releasedFrom c a ls ≤
          (t.deposited c a + t.backfill c a - (s.deposited c a + s.backfill c a)) +
            (s.deposited c a + s.backfill c a - s.withdrawn c a)

/-- **(b) THE ENABLED CHAINS JOINTLY RELEASE AT MOST THE POOL.**  From a `CapWF` state on
constants satisfying `CapConfig.Ok`, for an asset whose origin chain is not enabled at the end of
the run: the amounts of the run's withdrawals by chains that were enabled when they ran total
exactly the growth of the pool key's `withdrawn`, and at most the pool's `deposited` at the end less
its `withdrawn` at the start, i.e. the growth of the pool's deposits (moves and pool backfill
credits included) plus the pool's starting headroom when it is positive. -/
@[headline] def Properties.BulkheadEnabledSetReleaseBound : Prop :=
  ∀ (cfg : CapConfig) (s t : CapState) (ls : List CapLabel) (a : ℕ),
    cfg.Ok → CapWF cfg s → CapRun cfg s ls t → t.interop (t.origin a) = false →
      releasedByEnabled cfg a s ls = t.withdrawn cfg.pool a - s.withdrawn cfg.pool a ∧
        releasedByEnabled cfg a s ls ≤ t.deposited cfg.pool a - s.withdrawn cfg.pool a ∧
        releasedByEnabled cfg a s ls ≤
          (t.deposited cfg.pool a - s.deposited cfg.pool a) +
            (s.deposited cfg.pool a - s.withdrawn cfg.pool a)

/-- **(d) THE ESCROW LEDGER IDENTITY.**  For a run from the upgrade state `s0` on constants
satisfying `CapConfig.Ok`, and an asset native to L1 at `s0`, in integers, with sums over all chain
ids below `2^48` (every registered id):

    bridgedOut + Σ backfill + Σ_{moved} deficit
      = bridgedOut at s0 + populated amounts + Σ_{not moved} headroom + headroom of the pool key

where a chain is moved for the asset when `inPool` is set. -/
def Properties.BulkheadLedgerIdentity : Prop :=
  ∀ (cfg : CapConfig) (s0 s : CapState) (ls : List CapLabel) (a : ℕ),
    cfg.Ok → CapUpgradeState cfg s0 → CapRun cfg s0 ls s → s0.origin a = cfg.l1 →
      (s.bridgedOut a : ℤ) + ∑ c ∈ range chainIdCap, (s.backfill c a : ℤ)
          + ∑ c ∈ range chainIdCap, (if s.inPool c a = true then (capDeficit s c a : ℤ) else 0)
        = (s0.bridgedOut a : ℤ) + (populatedIn a ls : ℤ)
          + ∑ c ∈ range chainIdCap, (if s.inPool c a = true then 0 else capHeadroom s c a)
          + capHeadroom s cfg.pool a

/-- **(d) THE ESCROW BACKS EVERY HEADROOM.**  In the setting of `BulkheadLedgerIdentity`, if the
backfills of the asset fit in its `bridgedOut` at the upgrade plus the legacy amounts populated
since, and no chain whose balance moved to the pool is in deficit, then `bridgedOut` is at least
the sum of the headrooms of the chains whose balance has not moved plus the pool's headroom. -/
@[headline] def Properties.BulkheadEscrowBacksHeadroom : Prop :=
  ∀ (cfg : CapConfig) (s0 s : CapState) (ls : List CapLabel) (a : ℕ),
    cfg.Ok → CapUpgradeState cfg s0 → CapRun cfg s0 ls s → s0.origin a = cfg.l1 →
    ∑ c ∈ range chainIdCap, s.backfill c a ≤ s0.bridgedOut a + populatedIn a ls →
    (∀ c, s.inPool c a = true → 0 ≤ capHeadroom s c a) →
      ∑ c ∈ range chainIdCap, (if s.inPool c a = true then 0 else capHeadroom s c a)
          + capHeadroom s cfg.pool a ≤ (s.bridgedOut a : ℤ)

/-- **(d) A WITHDRAWAL WITHIN HEADROOM PASSES WHILE NO KEY IS IN DEFICIT.**  In the setting of
`BulkheadEscrowBacksHeadroom`, with no key in deficit for the asset: for a registered chain `c`
that is disabled and not pending, every amount up to its headroom passes `_handleBridgeFromChain`
(both the `bridgedOut` check and the cap), provided `deposited + backfill` of `(c, a)` is below
`2^256`. -/
@[headline] def Properties.BulkheadHonestWithdrawalSucceeds : Prop :=
  ∀ (cfg : CapConfig) (s0 s : CapState) (ls : List CapLabel) (a c x : ℕ),
    cfg.Ok → CapUpgradeState cfg s0 → CapRun cfg s0 ls s → s0.origin a = cfg.l1 →
    ∑ k ∈ range chainIdCap, s.backfill k a ≤ s0.bridgedOut a + populatedIn a ls →
    (∀ k, 0 ≤ capHeadroom s k a) →
    s.registered c = true → s.interop c = false → s.pending c = false →
    s.deposited c a + s.backfill c a < capWordBound → (x : ℤ) ≤ capHeadroom s c a →
      ∃ t, capStep cfg (.fromChain c a x) s = some t

/-- **…AND FOR AN ASSET NOT NATIVE TO L1, WITH NO CONDITION ON OTHER CHAINS.**  In any state, for
a registered chain `c` that is disabled and not pending, and an asset whose origin is neither L1 nor `c`, every
amount up to `c`'s headroom passes `_handleBridgeFromChain`, provided `deposited + backfill` of
`(c, a)` is below `2^256`. -/
def Properties.BulkheadBridgedWithdrawalSucceeds : Prop :=
  ∀ (cfg : CapConfig) (s : CapState) (a c x : ℕ),
    s.origin a ≠ cfg.l1 → s.origin a ≠ c →
    s.registered c = true → s.interop c = false → s.pending c = false →
    s.deposited c a + s.backfill c a < capWordBound → (x : ℤ) ≤ capHeadroom s c a →
      ∃ t, capStep cfg (.fromChain c a x) s = some t

/-- **NO DEFICIT, ONCE REACHED, PERSISTS.**  From a `CapWF` state on constants satisfying
`CapConfig.Ok` where no chain is pending and no key is in deficit for an asset, every run keeps
both: no chain pending, and every key's headroom in that asset nonnegative. -/
def Properties.BulkheadNoDeficitPersists : Prop :=
  ∀ (cfg : CapConfig) (s t : CapState) (ls : List CapLabel) (a : ℕ),
    cfg.Ok → CapWF cfg s → CapRun cfg s ls t →
    (∀ c, s.pending c = false) → (∀ k, 0 ≤ capHeadroom s k a) →
      (∀ c, t.pending c = false) ∧ ∀ k, 0 ≤ capHeadroom t k a

/-- **COUNTERMODEL (1): A PENDING CHAIN IS UNCAPPED.**  On the deployed constants, a run from the
upgrade state reaches a state `s` where the backfills fit the escrow, chain `c` is registered,
disabled, not pending, with headroom at least 1 in the L1-native asset `a` and can withdraw 1, while
chain `d` is still pending.  `d` then withdraws more than its own headroom in `a`; `c`'s counters
and flag are unchanged, yet `c`'s withdrawal of 1 reverts.  In an asset `b` not native to L1, where
`d` has no deposits and no backfill, every `uint256` amount `d` withdraws passes. -/
@[countermodel] def Properties.BulkheadPendingChainUncapped : Prop :=
  ∃ (s0 s t : CapState) (ls : List CapLabel) (c d a b x : ℕ),
    CapUpgradeState deployedCapConfig s0 ∧ CapRun deployedCapConfig s0 ls s ∧
    s.origin a = deployedCapConfig.l1 ∧ s.origin b ≠ deployedCapConfig.l1 ∧
    ∑ k ∈ range chainIdCap, s.backfill k a ≤ s0.bridgedOut a + populatedIn a ls ∧
    s.registered c = true ∧ s.interop c = false ∧ s.pending c = false ∧
    1 ≤ capHeadroom s c a ∧ s.deposited c a + s.backfill c a < capWordBound ∧
    (∃ u, capStep deployedCapConfig (.fromChain c a 1) s = some u) ∧
    s.pending d = true ∧ capHeadroom s d a < x ∧
    capStep deployedCapConfig (.fromChain d a x) s = some t ∧
    t.deposited c a = s.deposited c a ∧ t.withdrawn c a = s.withdrawn c a ∧
    t.backfill c a = s.backfill c a ∧ t.pending c = false ∧
    capStep deployedCapConfig (.fromChain c a 1) t = none ∧
    s.deposited d b + s.backfill d b = 0 ∧
    ∀ y, y < capWordBound → ∃ u, capStep deployedCapConfig (.fromChain d b y) s = some u

/-- **COUNTERMODEL (2): `markBackfilled` KEEPS A DEFICIT.**  First, `markBackfilled` succeeds on
every pending chain and only clears its flag: it reads no counter.  Second, on the deployed
constants a run from the upgrade state reaches a pending, registered, disabled chain `c` with a
nonzero backfill and `withdrawn > deposited + backfill` in an asset not native to `c`; after
`markBackfilled c`, every withdrawal of `(c, a)` reverts, and along any later run in which `c`
stays disabled (and the asset's origin is not `c`) the amounts released for `(c, a)` are at most
`deposited + backfill` at the end less the `withdrawn` total at `markBackfilled`, with the backfill
unchanged. -/
@[countermodel] def Properties.BulkheadMarkBackfilledKeepsDeficit : Prop :=
  (∀ (cfg : CapConfig) (s : CapState) (c : ℕ), s.pending c = true →
    capStep cfg (.markBackfilled c) s = some { s with pending := Function.update s.pending c false })
  ∧ ∃ (s0 s t : CapState) (ls : List CapLabel) (c a : ℕ),
    CapUpgradeState deployedCapConfig s0 ∧ CapRun deployedCapConfig s0 ls s ∧
    s.pending c = true ∧ s.registered c = true ∧ s.interop c = false ∧ s.origin a ≠ c ∧
    0 < s.backfill c a ∧ s.deposited c a + s.backfill c a < s.withdrawn c a ∧
    capStep deployedCapConfig (.markBackfilled c) s = some t ∧
    (∀ x, capStep deployedCapConfig (.fromChain c a x) t = none) ∧
    ∀ (ls' : List CapLabel) (t' : CapState), CapRun deployedCapConfig t ls' t' →
      t'.interop c = false → t'.origin a ≠ c →
        releasedFrom c a ls' ≤ t'.deposited c a + t'.backfill c a - t.withdrawn c a ∧
          t'.backfill c a = t.backfill c a

/-- **THE CAP STATEMENTS' PREMISES ARE SATISFIABLE, NONTRIVIALLY.**  On the deployed constants, a
run from the upgrade state reaches `s`, from which a run reaches `t`:

* along `s → t`, chain `c` (not pending at `s`, disabled at `t`, the asset `a` native to L1)
  receives a deposit and withdraws, and the amounts released for `(c, a)` are positive and equal
  `deposited + backfill` at `t` less `withdrawn` at `s` (the bound is tight);
* the run's last call is a capped withdrawal of a positive amount under key `c`, ending with
  `withdrawn = deposited + backfill` there, and it leaves the backfill (nonzero) and the deposits
  of another chain `d` unchanged;
* chains enabled during `s → t` release a positive amount equal to the pool's `deposited` at `t`
  less its `withdrawn` at `s`;
* at `t`, for an asset `b` whose origin `d'` is neither L1 nor `c`, the registered, disabled,
  non-pending chain `c` has positive headroom, below `2^256` with its counters, and can withdraw
  all of it. -/
@[witness] def Properties.BulkheadCapWitness : Prop :=
  ∃ (s0 s u t : CapState) (ls ls' : List CapLabel) (c d d' a b x : ℕ),
    CapUpgradeState deployedCapConfig s0 ∧ CapRun deployedCapConfig s0 ls s ∧
    CapRun deployedCapConfig s (ls' ++ [.fromChain c a x]) t ∧
    CapRun deployedCapConfig s ls' u ∧ capStep deployedCapConfig (.fromChain c a x) u = some t ∧
    s.upgraded = true ∧ s.pending c = false ∧ t.interop c = false ∧ c ≠ deployedCapConfig.pool ∧
    s.origin a = deployedCapConfig.l1 ∧ t.origin a = deployedCapConfig.l1 ∧
    0 < releasedFrom c a (ls' ++ [.fromChain c a x]) ∧
    releasedFrom c a (ls' ++ [.fromChain c a x]) =
      t.deposited c a + t.backfill c a - s.withdrawn c a ∧
    0 < s.deposited c a + s.backfill c a ∧ s.deposited c a < t.deposited c a ∧
    capTrackedKey deployedCapConfig u c (u.origin a) = some c ∧ u.pending c = false ∧ 0 < x ∧
    t.withdrawn c a = t.deposited c a + t.backfill c a ∧
    d ≠ c ∧ d ≠ deployedCapConfig.pool ∧ 0 < t.withdrawn deployedCapConfig.pool a ∧
    0 < u.backfill d a ∧ t.backfill d = u.backfill d ∧ t.deposited d = u.deposited d ∧
    CapWF deployedCapConfig s ∧ t.interop (t.origin a) = false ∧
    0 < releasedByEnabled deployedCapConfig a s (ls' ++ [.fromChain c a x]) ∧
    releasedByEnabled deployedCapConfig a s (ls' ++ [.fromChain c a x]) =
      t.deposited deployedCapConfig.pool a - s.withdrawn deployedCapConfig.pool a ∧
    t.origin b = d' ∧ d' ≠ deployedCapConfig.l1 ∧ d' ≠ c ∧ t.registered c = true ∧
    t.pending c = false ∧ t.deposited c b + t.backfill c b < capWordBound ∧
    0 < capHeadroom t c b ∧
    ∃ t', capStep deployedCapConfig (.fromChain c b (capHeadroom t c b).toNat) t = some t'

/-- **THE LEDGER STATEMENTS' PREMISES ARE SATISFIABLE, NONTRIVIALLY.**  On the deployed constants,
a run from an upgrade state with a positive `bridgedOut` in the L1-native asset `a` reaches `s`
where: the run's populated amount and the backfill sum are positive and the backfills fit the
escrow; one chain's balance is in the pool with positive headroom, and the pool's headroom is
positive; no chain is pending and no key is in deficit; the unmoved headrooms plus the pool's
equal `bridgedOut` exactly (the escrow bound is tight); and a registered, disabled, non-pending
chain `c` with positive headroom can withdraw all of it. -/
@[witness] def Properties.BulkheadLedgerWitness : Prop :=
  ∃ (s0 s : CapState) (ls : List CapLabel) (a c m : ℕ),
    CapUpgradeState deployedCapConfig s0 ∧ CapRun deployedCapConfig s0 ls s ∧
    s0.origin a = deployedCapConfig.l1 ∧ 0 < s0.bridgedOut a ∧ 0 < populatedIn a ls ∧
    0 < ∑ k ∈ range chainIdCap, s.backfill k a ∧
    ∑ k ∈ range chainIdCap, s.backfill k a ≤ s0.bridgedOut a + populatedIn a ls ∧
    s.inPool m a = true ∧ 0 < capHeadroom s m a ∧ 0 < capHeadroom s deployedCapConfig.pool a ∧
    (∀ k, s.pending k = false) ∧ (∀ k, 0 ≤ capHeadroom s k a) ∧
    ∑ k ∈ range chainIdCap, (if s.inPool k a = true then 0 else capHeadroom s k a)
        + capHeadroom s deployedCapConfig.pool a = (s.bridgedOut a : ℤ) ∧
    s.registered c = true ∧ s.interop c = false ∧ s.pending c = false ∧
    s.deposited c a + s.backfill c a < capWordBound ∧ 0 < capHeadroom s c a ∧
    ∃ t, capStep deployedCapConfig (.fromChain c a (capHeadroom s c a).toNat) s = some t

end Contracts.L1NativeTokenVault.Bulkhead
