import EraSpec.Contracts.L1NativeTokenVault.Specs.BulkheadPoolSimulation

/-!
# Properties: the bulkhead model's runs are `InteropPool` runs

Statements about `EraSpec.Contracts.L1NativeTokenVault.Specs.BulkheadPoolSimulation`, which reads
the bulkhead model (`Specs/BulkheadIsolation.lean`) in the `InteropPool` model
(`Specs/InteropPool.lean`).  Both transcribe `L1NativeTokenVault.sol` at `draft/v0.35.0`
`b17415d20`.  Proofs are in `EraSpec.Contracts.L1NativeTokenVault.Proofs.BulkheadPoolSimulation`.

* `BulkheadStepIsPoolCall`: on matching constants, from corresponding states, every successful
  bulkhead call whose numbers are words is the matching successful `InteropPool` call, and the two
  results correspond.  `registerAsset` is no `InteropPool` call and leaves the correspondence.
* `BulkheadRunIsPoolRun`: hence every bulkhead run on word labels from a corresponding state is an
  `InteropPool` run (of `capPoolCalls`) to a corresponding state.
* `BulkheadUpgradeStateIsPostUpgrade`: a bulkhead upgrade state with word origin values
  corresponds to an `InteropPool` post-upgrade state (`initializeUpgrade` on a `PreUpgrade` state).
* `BulkheadRunsArePoolRuns` (headline): so every bulkhead run on word labels from its upgrade state
  is an `InteropPool` run from a post-upgrade state to a corresponding state, to which the
  `InteropPool` statements about such runs (`FlagsAfterUpgrade`, `PoolDepositIdentity`,
  `PoolWithdrawalsCovered`, `EnabledChainTotalsFrozen`, …) apply.
* `BulkheadPoolSimulationWitness`: the premises met by a nonempty run with nonzero values.
-/

namespace Contracts.L1NativeTokenVault.Bulkhead

/-- **EVERY BULKHEAD CALL IS AN `InteropPool` CALL.**  Take constants matching `InteropPool`'s (L1's
chain id `l1`, the same pool key), states `s` and `p` that correspond, and a label whose numbers are
all `uint256` words.  If the call succeeds in the bulkhead model with result `t`, then the
`InteropPool` call it is (`l.toPoolCall s`) succeeds from `p` with a result corresponding to `t`;
for `registerAsset`, which is no `InteropPool` call, `p` itself corresponds to `t`. -/
def Properties.BulkheadStepIsPoolCall : Prop :=
  ∀ (cfg : CapConfig) (l1 : UInt256) (s t : CapState) (p : InteropPool.PoolSys) (l : CapLabel),
    cfg.MatchesPool l1 → CapPoolCorr s p → l.Words → capStep cfg l s = some t →
      (∀ call, l.toPoolCall s = some call →
        ∃ p', InteropPool.poolCall l1 call p = some p' ∧ CapPoolCorr t p') ∧
      (l.toPoolCall s = none → CapPoolCorr t p)

/-- **EVERY BULKHEAD RUN IS AN `InteropPool` RUN.**  On matching constants, from corresponding
states, a bulkhead run whose labels' numbers are all words is an `InteropPool` run of the calls
`capPoolCalls cfg s ls` (each label read in the state it runs in, `registerAsset` dropped) to a
state corresponding to the bulkhead run's end. -/
def Properties.BulkheadRunIsPoolRun : Prop :=
  ∀ (cfg : CapConfig) (l1 : UInt256) (s t : CapState) (p : InteropPool.PoolSys)
    (ls : List CapLabel),
    cfg.MatchesPool l1 → CapPoolCorr s p → (∀ l ∈ ls, l.Words) → CapRun cfg s ls t →
      ∃ p', InteropPool.PoolRun l1 p (capPoolCalls cfg s ls) p' ∧ CapPoolCorr t p'

/-- **THE BULKHEAD UPGRADE STATE IS AN `InteropPool` POST-UPGRADE STATE.**  For any constants and
any `CapUpgradeState` whose origin values are words, there is an `InteropPool` `PreUpgrade` state
on which `initializeUpgrade` succeeds with a state corresponding to it. -/
def Properties.BulkheadUpgradeStateIsPostUpgrade : Prop :=
  ∀ (cfg : CapConfig) (s0 : CapState),
    CapUpgradeState cfg s0 → (∀ a, s0.origin a < capWordBound) →
      ∃ pre p0 : InteropPool.PoolSys, InteropPool.PreUpgrade pre ∧
        InteropPool.initializeUpgrade pre = some p0 ∧ CapPoolCorr s0 p0

/-- **HEADLINE: BULKHEAD RUNS FROM THE UPGRADE STATE ARE `InteropPool` RUNS FROM ITS POST-UPGRADE
STATE.**  On matching constants, for a `CapUpgradeState` `s0` whose origin values are words and a
bulkhead run from it whose labels' numbers are all words, ending in `s`: there are an `InteropPool`
`PreUpgrade` state `pre`, the state `p0` that `initializeUpgrade` leaves on it, and a state `p` at
the end of the `InteropPool` run of `capPoolCalls cfg s0 ls` from `p0`, with `p` corresponding to
`s`.  So the `InteropPool` statements about runs from the post-upgrade state apply to `p`. -/
def Properties.BulkheadRunsArePoolRuns : Prop :=
  ∀ (cfg : CapConfig) (l1 : UInt256) (s0 s : CapState) (ls : List CapLabel),
    cfg.MatchesPool l1 → CapUpgradeState cfg s0 → (∀ a, s0.origin a < capWordBound) →
    (∀ l ∈ ls, l.Words) → CapRun cfg s0 ls s →
      ∃ pre p0 p : InteropPool.PoolSys, InteropPool.PreUpgrade pre ∧
        InteropPool.initializeUpgrade pre = some p0 ∧
        InteropPool.PoolRun l1 p0 (capPoolCalls cfg s0 ls) p ∧ CapPoolCorr s p

/-- **THE PREMISES ARE MET, NONTRIVIALLY.**  On the deployed constants and `l1 = 1`: an upgrade
state `s0` with `bridgedOut` 100 of the L1-native asset `10` and two registered, pending chains,
whose origin values are words, and an `InteropPool` state corresponding to it; and a bulkhead run
of fifteen word labels from it, which registers a chain and an asset, populates, backfills and marks
both chains, enables interop on one and moves its balance, and deposits and withdraws.  Its first
call meets the premises of `BulkheadStepIsPoolCall`.  Its end `s` has nonzero values: the pool
holds 40 of asset `10` and has paid out 40, and chain `3`'s `deposited + backfill` is `65`.  The
`InteropPool` calls of the run are its labels less the one `registerAsset`. -/
def Properties.BulkheadPoolSimulationWitness : Prop :=
  ∃ (s0 s : CapState) (ls : List CapLabel),
    deployedCapConfig.MatchesPool 1 ∧ CapUpgradeState deployedCapConfig s0 ∧
    (∀ a, s0.origin a < capWordBound) ∧ (∀ l ∈ ls, l.Words) ∧
    (∃ p0 : InteropPool.PoolSys, CapPoolCorr s0 p0) ∧
    CapRun deployedCapConfig s0 ls s ∧ ls.length = 15 ∧
    (capPoolCalls deployedCapConfig s0 ls).length = 14 ∧
    0 < s0.bridgedOut 10 ∧ s0.registered 2 = true ∧ s0.registered 3 = true ∧
    s.deposited deployedCapConfig.pool 10 = 40 ∧ s.withdrawn deployedCapConfig.pool 10 = 40 ∧
    s.deposited 3 10 + s.backfill 3 10 = 65 ∧ s.registered 4 = true ∧ s.origin 13 = 4

end Contracts.L1NativeTokenVault.Bulkhead
