# AdminFacet

The chain diamond's `AdminFacet` at era-contracts `draft/v0.35.0` `b17415d20`: access control, the
freeze switch, priority mode, protocol upgrades and fee inputs.

## Headline guarantees

The folder's `@[headline]` statements (see [CONSOLIDATION.md](../../../CONSOLIDATION.md)). "A run"
is any interleaving of calls (any sender, any block time), environment changes and writes by the
other facets; "without cuts" excludes the three entries that run a diamond cut
(`upgradeChainFromVersion`, `executeUpgrade`, `genesisUpgrade`), whose effect is arbitrary code.

| Guarantee | Premises | Statement |
|---|---|---|
| A successful call to any of the 25 state-changing entries came from an address in that entry's role (admin, pending admin, CTM, validator, or the Bridgehub owner for disabling a required second proof system); `activatePriorityMode` has none | None | `EveryEntryChecksItsRole` |
| A validator's `upgradeChainFromVersion(_, v)` waits for the `ServerNotifier` timestamp of `v`, which is set and reached | The caller is neither the admin nor the CTM | `ValidatorUpgradeWaitsForSchedule` |
| A changed admin sent `acceptAdmin` itself and was pending at the start or nominated by `setPendingAdmin` in the run | A run without cuts; no call from the zero address | `AdminChangesOnlyByAcceptance` |
| Every changed validator bit was written to its final value by the CTM's `setValidator`; the CTM address is fixed | A run without cuts | `ValidatorsChangeOnlyByCTM` |
| `freezeDiamond` succeeds iff the caller is the CTM and the diamond is unfrozen; `unfreezeDiamond` iff the caller is the CTM, the diamond is frozen and its selector is not freezable; each writes only the flag | None | `FreezeUnfreezeExact` |
| `Stage1Inv` (active priority mode implies allowed and permanent rollup; allowed implies L1-transaction filtering off and the governance-set filterer) holds on every chain where priority mode is neither allowed nor active, and every run keeps it | A run without cuts | `Stage1InvHoldsAlongRuns` |
| Once `activatePriorityMode` succeeds at `τ`, no later call undoes it: priority mode is active, or activation succeeds for every caller at every `τ' ≥ τ` | A run without cuts; the other facets' writes keep the chain on its settlement layer, keep the first unprocessed priority transaction stamped at `t ≠ 0` with `t + 4 days ≤ τ`, and keep executed ≤ committed; the selector is not freezable or the CTM sends none of the run's calls | `NoFacetCallBlocksDueActivation` |
| Permanent rollup, required second proof system and allowed priority mode are never cleared; once priority mode is allowed the pricing mode and three capacity fields never change | A run without cuts | `OneWayFlagsAlongRuns` |
| `activatePriorityMode` succeeds exactly under its eight conditions and reverts all unexecuted batches | The model omits `nonReentrant` and overflow reverts, which only remove successes | `ActivatePriorityModeExact` |
| `upgradeChainFromVersion(_, v)` succeeds iff the caller has the role, the chain is at `v`, the validator schedule passes, running the cut the CTM returns for `v` succeeds, the second-proof recheck passes and the version rises; the caller supplies no cut | The cut is the CTM's `upgradeCutForVersion` answer (an oracle here) | `UpgradeRunsExactlyTheCommittedCut` |
| The final version is at least the initial version plus the number of `upgradeChainFromVersion` calls | The CTM's genesis address holds the genuine `L1GenesisUpgrade`; no `executeUpgrade` in the run (cuts otherwise allowed) | `VersionRisesAlongRuns` |
| After a successful `genesisUpgrade`, no later `genesisUpgrade` succeeds | Genuine genesis code; its transaction hash is nonzero; no later foreign write clears the L2 upgrade transaction hash; no `upgradeChainFromVersion` or `executeUpgrade` later | `GenesisRunsOnce` |
| Fee updates (`changeFeeParams`, `setTokenMultiplier`) are at least `PRICE_UPDATE_INTERVAL` (1 day) apart | The first update was at a nonzero time; a run without cuts | `FeeUpdatesAtLeastADayApart` |
| A fee update keeps the derived L2 gas price within a factor 13/10 of the price before | Priority mode is allowed; not the exempt case of price 0 with no unprocessed priority transaction | `StageOneFeeUpdateWithinPriceBound` |

Witnesses (`@[witness]`): `EveryEntrySucceedsSomewhere`, `ValidatorUpgradeWitness`,
`AdminHandoverWitness`, `ValidatorChangeWitness`, `FreezeWitness`, `StrandedChainWitness`,
`PriorityModeWitness`, `PriorityModeActivationRevertsBatchesWitness`,
`PriorityModeDeactivationWitness`, `OneWayFlagsWitness`, `DueActivationSurvivesWitness`,
`UpgradeWitness`, `GenesisRunsOnceWitness`, `PricingModeChangeWitness`, `FeeUpdatesWitness`,
`StageOneFeeUpdateWitness`, `StageOneFeeInputsWitness`. Countermodels (`@[countermodel]`):
`CTMFreezeBlocksActivation`, `ActivationNeedsPermanentRollup`, `UnguardedFiltererBreaksStage1`,
`UnguardedL1FilteringBreaksStage1`, `ExecuteUpgradeCanLowerVersion`,
`UpgradePostCheckIsLoadBearing`, `GenesisRerunsAfterFinalization`, `FeeUpdateAtTimeZeroNotSpaced`,
`PriceBoundNeedsPriorityModeAllowed`, `PricingModeMovesPriceWithoutPriorityMode`. The other
statements are supporting lemmas.

## Source

era-contracts `draft/v0.35.0` at commit **`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`**, under
`l1-contracts/contracts/`; every `file:line` is at that commit.

- `state-transition/chain-deps/facets/Admin.sol` (the facet, all 709 lines);
- `state-transition/chain-deps/facets/ZKChainBase.sol` (modifiers `:46-146`, `_getProofMode`
  `:188-190`, `_deriveL2GasPriceFromParams` `:276-300`, `_setDAValidatorPair` `:307-313`,
  `_revertBatches` `:317-337`);
- read for context: `state-transition/chain-deps/DiamondProxy.sol:25-36` (the freeze check),
  `state-transition/libraries/Diamond.sol:109-137, 310-340` (`diamondCut`, its initializer call),
  `state-transition/libraries/PriorityTree.sol:37-49`, `common/Config.sol`,
  `common/ReentrancyGuard.sol:72-98`, `state-transition/chain-deps/ZKChainStorage.sol:46-66`,
  `state-transition/chain-deps/DiamondInit.sol:52, 128`, `upgrades/L1GenesisUpgrade.sol:31-104`,
  `upgrades/BaseZkSyncUpgrade.sol:72-108, 162-202`, `upgrades/BaseZkSyncUpgradeGenesis.sol:25-82`,
  `state-transition/ChainTypeManager.sol:322-325, 601-607, 703-707`, and the storage writes of
  `Committer.sol`, `Executor.sol`, `Mailbox.sol`, `Migrator.sol`.

Namespace: `Contracts.AdminFacet`. Statements are `Contracts.AdminFacet.Properties.*`; each
certificate has the same name without the `Properties` segment.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Access | [Specs/AdminFacet.lean](Specs/AdminFacet.lean) | [Properties/Access.lean](Properties/Access.lean) | [Proofs/Access.lean](Proofs/Access.lean) |
| PriorityMode | [Specs/AdminFacet.lean](Specs/AdminFacet.lean), [Specs/Mutants.lean](Specs/Mutants.lean) | [Properties/PriorityMode.lean](Properties/PriorityMode.lean) | [Proofs/PriorityMode.lean](Proofs/PriorityMode.lean) |
| Upgrade | [Specs/AdminFacet.lean](Specs/AdminFacet.lean), [Specs/Mutants.lean](Specs/Mutants.lean) | [Properties/Upgrade.lean](Properties/Upgrade.lean) | [Proofs/Upgrade.lean](Proofs/Upgrade.lean) |
| Fees | [Specs/AdminFacet.lean](Specs/AdminFacet.lean) | [Properties/Fees.lean](Properties/Fees.lean) | [Proofs/Fees.lean](Proofs/Fees.lean) |

`Proofs/Basic.lean` holds auxiliary frame lemmas only (which entry can change which field).

## What is modelled

- **`State`**: the 34 fields of `ZKChainStorage` the facet reads or writes (the priority tree's
  three counters counted separately), plus the diamond's `isFrozen` flag and the per-selector
  `isFreezable` bit.
- **`Entry`/`exec`**: all 25 state-changing external functions, each with its modifiers and
  guards in source order. A revert is `none`. The 25 selectors are the ones `selectors()` lists
  (`Admin.sol:646-702`), minus the two views.
- **`call`**: the proxy's `require(!isFrozen || !facet.isFreezable)` (`DiamondProxy.sol:36`),
  then `exec`.
- **`Env`**: what the facet reads from other contracts during a call. This covers the CTM's
  `upgradeCutForVersion` and `l1GenesisUpgrade`, the `ServerNotifier` schedule, the hash of the
  genesis transaction the CTM's release composes, the Bridgehub owner,
  `RollupDAManager.isPairAllowed`, the verifier's `getProofMode`, and `cutContext` (whatever
  else a cut's initializer reads). It is fixed during a call and may change arbitrarily between
  calls (`Label.env`). A change to state the model does not track (another contract's storage,
  this diamond's selector routing table) is an environment step.
- **`Config.runCut`**: the effect of `Diamond.diamondCut` on this storage, including the
  delegatecalled initializer, as a function of the environment, the call's `block.timestamp`,
  the cut and the storage. It is an **arbitrary** partial function: a cut is code chosen by the
  CTM. It does not see `msg.sender` (no initializer under `upgrades/` reads it at this commit).
  `genesisEffect` transcribes the one initializer the facet names itself
  (`L1GenesisUpgrade.genesisUpgrade`).
- **`Foreign`**: a write by another facet. It leaves the `Owned` fields alone and never clears
  `isPermanentRollup` (`Migrator.sol:234-236, 241`). Everything else (batch counters, priority
  tree, request timestamps, `pausedDepositsTimestamp`, `settlementLayer`, the DA pair, the L2
  upgrade transaction's hash and batch number) may change arbitrarily. The split was checked by
  a search for every `s.<field>` write in the four other facets at this commit.
- **`Step`/`Run`**: any interleaving of calls (any sender, any block time), environment changes
  and foreign writes.

## What is not modelled

- **Routing.** The diamond is assumed to send the facet's selectors to this facet's code. Which
  code a cut installs is the `ChainRouting`/`LiveRouting` model of `../ChainTypeManager/` (at
  `e561b9cc2`); it is not duplicated here. At this commit `upgradeChainFromVersion` takes no cut
  argument and asks the CTM for it; here that read is the oracle `Env.upgradeCutForVersion`.
- **What a cut does.** `runCut` is arbitrary, so the run-level results other than
  `VersionRisesAlongRuns`, `GenesisRunsOnce` and `FreezableUnfreezeStrandsTheChain` are stated
  for runs that run no cut. Nothing is claimed about what `DefaultUpgrade` or a transition's
  engine writes.
- **`nonReentrant`** on `activatePriorityMode` (`ReentrancyGuard.sol:72-98`). It reverts unless
  the lock slot holds `_NOT_ENTERED`, its value between calls on a diamond whose initializer ran
  `reentrancyGuardInitializer` (`DiamondInit.sol:52`); the body makes no external call.
- **Events, gas, ABI widths, `msg.value`.** Addresses, hashes and enum indices are `ℕ` compared
  for equality. `uint` fields are `ℕ`, so checked-arithmetic reverts are omitted; the one
  underflow the source can hit (`PriorityTree.getSize`) reads as size `0`. ABI-decoding reverts
  (enum ranges, integer widths) are omitted. The model admits more successful calls than the
  source, never fewer, and each "succeeds iff" statement is exact for the model and an upper
  bound on success for the source.
- **Inside the genesis upgrade:** `TransactionValidator`'s checks and the external reads that
  compose the L2 transaction. They only reject. `GenuineGenesis` is one-directional (a successful
  genesis cut does what `genesisEffect` does), so the results hold with those rejections present.
- **Monotone block time.** A run's calls carry arbitrary timestamps; no result assumes time moves
  forward. `FeeUpdatesAtLeastADayApart` bounds the timestamps of later fee updates whatever their
  order.
- No connection to compiled bytecode (`VM-CALL`, `VM-REVERT`, `BUILD-PRESERVATION`).

## What to check

**Access control**

- `EveryEntryChecksItsRole`: a successful call to any of the 25 entries came from an address in
  that entry's `Role`. Read `Role` against the modifiers; it is the whole access table.
  `activatePriorityMode` has no caller check.
- `CallerMattersOnlyThroughRole`: the caller affects nothing else. The same call from another
  address with the role gives the same result (for `upgradeChainFromVersion` the other address
  must be admin or CTM, which skip the schedule gate). This uses that `runCut` does not see the
  caller.
- `ValidatorUpgradeWaitsForSchedule`: a caller of `upgradeChainFromVersion` that is neither
  admin nor CTM is a validator, and the notifier's timestamp for that version is set and reached.
  `../ChainTypeManager/` topic `UpgradeTiming` states the same notifier gate at `e561b9cc2`
  (`AdminAndCtmSkipTheNotifier`, `OtherCallersNeedTheNotifier`); this topic states it at
  `b17415d20`.
- `AdminHandoverIsTwoStep`: `setPendingAdmin` and `acceptAdmin` as exact functions of the state.
- `AdminChangesOnlyByAcceptance` (run, no cuts): if the admin changed, the final admin sent
  `acceptAdmin`, and it was pending at the start or named by a `setPendingAdmin` in the run.
  Premise: no call from the zero address (otherwise the zero address could accept an empty
  nomination).
- `ValidatorsChangeOnlyByCTM` (run, no cuts): the CTM address is fixed, and each changed
  validator bit was written by the CTM's `setValidator` with its final value.
- `FreezeUnfreezeExact`: `freezeDiamond` succeeds iff the caller is the CTM and the diamond is
  unfrozen. `unfreezeDiamond` succeeds iff the caller is the CTM, the diamond is frozen and the
  `unfreezeDiamond` selector is not marked freezable.
- `FreezeOnlyByCTM` (run, no cuts): the flag moves only by the CTM's two calls.
- `FreezableUnfreezeStrandsTheChain` (run, **all** steps, cuts included): if `unfreezeDiamond`
  and the three cut entries are marked freezable, a frozen diamond stays frozen forever.

**Priority mode**

- `Stage1InvHoldsAlongRuns` (run, no cuts, headline): `Stage1Inv` holds on a chain where
  priority mode is neither allowed nor active, and every run keeps it. `Stage1Inv` says two
  things. Active implies allowed and permanent rollup. Allowed implies operator L1-tx filtering
  is off and the transaction filterer is the one governance set for priority mode.
- `NoFacetCallBlocksDueActivation` (run, no cuts, headline): once `activatePriorityMode` succeeds
  at `τ`, after any further run whose foreign writes keep `ActivationQueueReady` at `τ` (on the
  settlement layer, the first unprocessed priority transaction requested at `t ≠ 0` with
  `t + 4 days ≤ τ`, executed ≤ committed), priority mode is active or activation succeeds for
  every caller at every `τ' ≥ τ`, provided the selector is not freezable or the CTM sends none of
  the run's calls.
- `OneWayFlagsAlongRuns` (run, no cuts): `isPermanentRollup`, `secondProofSystemRequired` and
  `canBeActivated` are never cleared. Once priority mode is allowed, the pricing mode and the
  three capacity fields of the fee parameters never change.
- `ActivatePriorityModeExact`: success iff not blocked by a freeze, on the settlement layer, on
  L1, not active, allowed, permanent rollup, the first unprocessed priority transaction has a
  request time `t ≠ 0` with `t + 4 days ≤ block.timestamp`, and `executed ≤ committed`. The
  result is given as an explicit state: priority mode active and all unexecuted batches reverted.
- `PriorityModeTogglesOnlyByItsEntries` (run, no cuts): on only by `activatePriorityMode`, off
  only by the CTM's `deactivatePriorityMode`.

**Upgrades**

- `UpgradeRunsExactlyTheCommittedCut`: `upgradeChainFromVersion(_, v)` succeeds with result `s'`
  iff the caller has the role, the CTM returns a cut for `v`, the chain is at `v`, the schedule
  gate passes for a validator, running **that** cut gives `s'`, the second-proof-system recheck
  passes, and `s'` has a version strictly above `v`. The caller supplies no cut.
- `VersionRisesAlongRuns` (run, cuts included): under `GenuineGenesis`, along a run with no
  `executeUpgrade`, `final version ≥ initial version + number of upgradeChainFromVersion calls`.
- `GenesisRunsOnce` (run): under `GenuineGenesis`, after a successful `genesisUpgrade` whose
  transaction hash is nonzero, no `genesisUpgrade` succeeds along a later run with no other cut
  entry and no foreign write zeroing that hash.

**Fee inputs**

- `SetPubdataPricingModeExact`: when not blocked by a freeze, `setPubdataPricingMode` succeeds
  iff the caller is the admin, the chain is on L1 and priority mode is not allowed, and writes
  only the pricing mode.
- `FeeUpdatesAtLeastADayApart` (run, no cuts): after a successful `changeFeeParams` or
  `setTokenMultiplier` at a nonzero time `τ₁`, every later one in the run has time at least
  `τ₁ + 1 day`.
- `StageOneFeeUpdateWithinPriceBound`: with priority mode allowed, a successful
  `changeFeeParams` or `setTokenMultiplier` keeps the derived L2 gas price `p'` within
  `p * 10 / 13 ≤ p' ≤ p * 13 / 10` of the price `p` before the call, unless `p = 0` and no
  priority transaction is unprocessed.
- `StageOneFeeInputsMoveOnlyByFeeUpdates` (run, no cuts): with priority mode allowed, a run
  without `changeFeeParams` and `setTokenMultiplier` leaves the fee parameters, the multiplier
  and the derived price unchanged. With the two results above: on such a chain the price moves
  only by fee updates, each within the bound (or under its exemption), and each at least a day
  after any earlier one made at a nonzero time.

**Countermodels** (a check or premise is load-bearing)

- `UnguardedFiltererBreaksStage1`: delete `Admin.sol:369-371` and the admin breaks `Stage1Inv`
  in one call.
- `UnguardedL1FilteringBreaksStage1`: the same for `Admin.sol:191-193`.
- `CTMFreezeBlocksActivation`: with the activation selector freezable, the CTM's calls can stop
  a due activation, so the last premise of `NoFacetCallBlocksDueActivation` is needed.
- `ActivationNeedsPermanentRollup`: a reachable state meets every activation condition except
  the permanent-rollup one, and activation reverts there.
- `UpgradePostCheckIsLoadBearing`: delete `Admin.sol:587-589` and an upgrade that does not raise
  the version succeeds.
- `ExecuteUpgradeCanLowerVersion`: the no-`executeUpgrade` premise of `VersionRisesAlongRuns`
  is needed.
- `GenesisRerunsAfterFinalization`: the no-zeroing premise of `GenesisRunsOnce` is needed. After
  a foreign write clears the hash (the Executor's finalization does), a second `genesisUpgrade`
  succeeds.
- `FeeUpdateAtTimeZeroNotSpaced`: the nonzero-time premise of `FeeUpdatesAtLeastADayApart` is
  needed (a zero stamp reads as "never updated", `Admin.sol:304`).
- `PriceBoundNeedsPriorityModeAllowed`: without priority mode allowed, a fee update can raise the
  derived price above the bound.
- `PricingModeMovesPriceWithoutPriorityMode`: without priority mode allowed,
  `setPubdataPricingMode` moves the derived price with no fee update.

**Witnesses** (premises are satisfiable, non-trivially)

- Access: `EveryEntrySucceedsSomewhere` (each of the 25 entries succeeds somewhere),
  `ValidatorUpgradeWitness`, `AdminHandoverWitness`, `ValidatorChangeWitness`, `FreezeWitness`,
  `StrandedChainWitness`.
- Priority mode: `PriorityModeWitness` (from a chain with priority mode not allowed and no
  permanent rollup to active priority mode, activated by an address that is neither the admin
  nor the CTM),
  `PriorityModeDeactivationWitness`, `OneWayFlagsWitness`, `DueActivationSurvivesWitness`,
  `PriorityModeActivationRevertsBatchesWitness` (the CTM sets a nonzero priority-mode filterer
  that allowing installs, and activation lowers the committed and verified counts to the
  executed one and clears the upgrade batch number).
- Upgrades: `UpgradeWitness` (a genesis upgrade and a scheduled upgrade, by a caller that is
  initially neither the admin, the CTM nor a validator, in one run; the config satisfies
  `GenuineGenesis`), `GenesisRunsOnceWitness`.
- Fee inputs: `PricingModeChangeWitness`, `FeeUpdatesWitness`, `StageOneFeeUpdateWitness`,
  `StageOneFeeInputsWitness`.

## Scope notes

- **Genesis once-only.** The facet blocks a second `genesisUpgrade` only while the L2 upgrade
  transaction it stored is pending (`GenesisRunsOnce`, `GenesisRerunsAfterFinalization`).
  Beyond that, once-only rests on the CTM calling it only from `createNewChain`
  (`ChainTypeManager.sol:703-707`; a source search finds no other call).
- **Freezability is configuration.** `unfreezeDiamond` works only if its selector is not
  freezable (`FreezeUnfreezeExact`); with it and the three cut entries freezable, one freeze is
  permanent (`FreezableUnfreezeStrandsTheChain`). The CTM deployment scripts register the facet
  non-freezable (`l1-contracts/deploy-scripts/ctm/DeployCTMUtils.s.sol:103`,
  `l1-contracts/deploy-scripts/gateway/GatewayCTMDeployerHelper.sol:358`); freezability is
  release configuration (`OPS-CONFIG`).

## Open

- Nothing is proved about runs that contain arbitrary cuts, except the version bound, the
  genesis bound and the freeze-strand result. Stronger statements need a model of the transition
  engines at this commit (`DefaultUpgrade`, `CTMTransition`); `../ChainTypeManager/` has them at
  `e561b9cc2`.
- "Runs only the CTM-committed cut" is proved up to the oracle `Env.upgradeCutForVersion`. That
  the CTM's answer is derived from the transition committed for the edge is the CTM's code
  (`ChainTypeManager.sol:601-607`), not modelled here.
- `GenuineGenesis` is a premise: that the CTM's `l1GenesisUpgrade()` address holds this commit's
  `L1GenesisUpgrade`. The nonzero genesis transaction hash in `GenesisRunsOnce` is also a
  premise (a keccak output, pinned to the one transaction).
- The price bound is stated per call, and the run-level pieces separately
  (`StageOneFeeInputsMoveOnlyByFeeUpdates`, `FeeUpdatesAtLeastADayApart`). No single theorem
  bounds the price over a run in closed form (the integer rounding compounds), and foreign writes
  to the priority tree can move a chain in and out of the bound's exemption.

## Review order

1. `Specs/AdminFacet.lean` against `Admin.sol` and `ZKChainBase.sol`: `State`, then `exec` entry
   by entry, then `Role`, `Foreign`, `genesisEffect`, `ActivationQueueReady`.
2. `Specs/Mutants.lean`: each mutant deletes exactly one check.
3. `Properties/Access.lean`, `Properties/PriorityMode.lean`, `Properties/Upgrade.lean`,
   `Properties/Fees.lean`: each statement and its docstring.
4. `Proofs/` only if needed. The audit checks that every property has its full named theorem.
