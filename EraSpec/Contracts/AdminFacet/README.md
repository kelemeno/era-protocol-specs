# AdminFacet

Source: era-contracts `draft/v0.35.0` at commit
**`d9f678900e1bc8286412b78f56d4a9f443983c29`**, under `l1-contracts/contracts/`:

- `state-transition/chain-deps/facets/Admin.sol` (the facet, all 709 lines);
- `state-transition/chain-deps/facets/ZKChainBase.sol` (modifiers `:46-146`, `_getProofMode`
  `:188-190`, `_deriveL2GasPriceFromParams` `:276-300`, `_setDAValidatorPair` `:307-313`,
  `_revertBatches` `:317-337`);
- read for context: `state-transition/chain-deps/DiamondProxy.sol:25-36` (the freeze check),
  `state-transition/libraries/Diamond.sol:109-137, 310-330`,
  `state-transition/libraries/PriorityTree.sol:37-49`, `common/Config.sol`,
  `state-transition/chain-deps/ZKChainStorage.sol:46-66`,
  `upgrades/L1GenesisUpgrade.sol:31-104`, `upgrades/BaseZkSyncUpgrade.sol:72-108, 162-202`,
  `upgrades/BaseZkSyncUpgradeGenesis.sol:25-82`,
  `state-transition/ChainTypeManager.sol:322-325, 601-607, 703-707`, and the storage writes of
  `Committer.sol`, `Executor.sol`, `Mailbox.sol`, `Migrator.sol`.

Every `file:line` in the specs is at that commit.

Namespace: `Contracts.AdminFacet`. Statements are `Contracts.AdminFacet.Properties.*`; each
certificate has the same name without the `Properties` segment.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Access | [Specs/AdminFacet.lean](Specs/AdminFacet.lean) | [Properties/Access.lean](Properties/Access.lean) | [Proofs/Access.lean](Proofs/Access.lean) |
| PriorityMode | [Specs/AdminFacet.lean](Specs/AdminFacet.lean), [Specs/Mutants.lean](Specs/Mutants.lean) | [Properties/PriorityMode.lean](Properties/PriorityMode.lean) | [Proofs/PriorityMode.lean](Proofs/PriorityMode.lean) |
| Upgrade | [Specs/AdminFacet.lean](Specs/AdminFacet.lean), [Specs/Mutants.lean](Specs/Mutants.lean) | [Properties/Upgrade.lean](Properties/Upgrade.lean) | [Proofs/Upgrade.lean](Proofs/Upgrade.lean) |
| NatSpec | [Specs/AdminFacet.lean](Specs/AdminFacet.lean) | [Properties/NatSpec.lean](Properties/NatSpec.lean) | [Proofs/NatSpec.lean](Proofs/NatSpec.lean) |

`Proofs/Basic.lean` holds auxiliary frame lemmas only (which entry can change which field).

## What is modelled

- **`State`**: the 34 fields of `ZKChainStorage` the facet reads or writes, plus the diamond's
  `isFrozen` flag and the per-selector `isFreezable` bit.
- **`Entry`/`exec`**: all 25 state-changing external functions, each with its modifiers and
  guards in source order. A revert is `none`. The 25 selectors are the ones `selectors()` lists
  (`Admin.sol:646-702`), minus the two views.
- **`call`**: the proxy's `require(!isFrozen || !facet.isFreezable)` (`DiamondProxy.sol:36`),
  then `exec`.
- **`Env`**: what the facet reads from other contracts during a call. This covers the CTM's
  `upgradeCutForVersion` and `l1GenesisUpgrade`, the `ServerNotifier` schedule, the Bridgehub
  owner, `RollupDAManager.isPairAllowed`, and the verifier's `getProofMode`. It may change
  arbitrarily between calls (`Label.env`).
- **`Config.runCut`**: the effect of `Diamond.diamondCut` on this storage, including the
  delegatecalled initializer. It is an **arbitrary** partial function: a cut is code chosen by
  the CTM. `genesisEffect` transcribes the one initializer the facet names itself
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
  `e561b9cc2`); it is not duplicated here. At `d9f6789` `upgradeChainFromVersion` takes no cut
  argument and asks the CTM for it; here that read is the oracle `Env.upgradeCutForVersion`.
- **What a cut does.** `runCut` is arbitrary, so the run-level results other than
  `VersionRisesAlongRuns`, `GenesisRunsOnce` and `FreezableUnfreezeStrandsTheChain` are stated
  for runs that run no cut. Nothing is claimed about what `DefaultUpgrade` or a transition's
  engine writes.
- **`nonReentrant`** on `activatePriorityMode` (the body makes no call that could re-enter).
- **Events, gas, ABI widths.** Addresses, hashes and enum indices are `ℕ` compared for equality.
  `uint` fields are `ℕ`, so checked-arithmetic overflow reverts are omitted. The one underflow
  the source can hit (`PriorityTree.getSize`) reads as size `0`. The model admits more successful
  calls than the source, never fewer.
- **Inside the genesis upgrade:** `TransactionValidator`'s checks and the external reads that
  compose the L2 transaction. They only reject. `GenuineGenesis` is one-directional (a successful
  genesis cut does what `genesisEffect` does), so the results hold with those rejections present.
- **Monotone block time.** A run's calls carry arbitrary timestamps. No result here depends on
  time moving forward, and none states a rate limit across calls.
- No connection to compiled bytecode (`VM-CALL`, `VM-REVERT`, `BUILD-PRESERVATION`).

## What to check

**Access control**

- `EveryEntryChecksItsRole`: a successful call to any of the 25 entries came from an address in
  that entry's `Role`. Read `Role` against the modifiers; it is the whole access table.
  `activatePriorityMode` has no caller check.
- `CallerMattersOnlyThroughRole`: the caller affects nothing else. The same call from another
  address with the role gives the same result (for `upgradeChainFromVersion` the other address
  must be admin or CTM, which skip the schedule gate).
- `ValidatorUpgradeWaitsForSchedule`: a caller of `upgradeChainFromVersion` that is neither
  admin nor CTM is a validator, and the notifier's timestamp for that version is set and reached.
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
  transaction hash is nonzero, no `genesisUpgrade` succeeds while that hash stays pending (no
  other cut entry, no foreign write clearing it).

**Countermodels** (a check or premise is load-bearing)

- `UnguardedFiltererBreaksStage1`: delete `Admin.sol:369-371` and the admin breaks `Stage1Inv`
  in one call.
- `UnguardedL1FilteringBreaksStage1`: the same for `Admin.sol:191-193`.
- `UpgradePostCheckIsLoadBearing`: delete `Admin.sol:587-589` and an upgrade that leaves the
  version unchanged succeeds.
- `ExecuteUpgradeCanLowerVersion`: the no-`executeUpgrade` premise of `VersionRisesAlongRuns`
  is needed.
- `GenesisRerunsAfterFinalization`: the pending-hash premise of `GenesisRunsOnce` is needed.
  After the Executor finalizes the genesis transaction, a second `genesisUpgrade` by the CTM
  succeeds.

**Witnesses** (concrete runs; premises are satisfiable)

- `AdminHandoverWitness`: nominate, accept.
- `PriorityModeWitness`: a priority transaction, `makePermanentRollup`,
  `permanentlyAllowPriorityMode`, then an outsider's `activatePriorityMode` four days later.
- `UpgradeWitness`: genesis, finalization, the CTM adds a validator, that validator upgrades once
  the schedule is reached. The config used satisfies `GenuineGenesis`.

## Findings (internal, not published)

- **NatSpec, `IAdmin.sol:56`:** `setPubdataPricingMode` is documented as "before the first batch
  is processed". The batch check was removed in `fd7e4cd6e3` ("Fix audittens L03"). The code
  reads no batch counter (`PricingModeIgnoresBatches`), and the admin can change the mode on a
  live chain (`PricingModeChangesAfterFirstBatch`). The remaining guard is the priority-mode one.
- **NatSpec, `IAdmin.sol:78-80`:** the two listed conditions for `activatePriorityMode` are not
  sufficient. The code also requires a permanent rollup (`Admin.sol:528-530`), and
  `permanentlyAllowPriorityMode` does not require one.
  `ActivationNatSpecConditionsInsufficient` reaches a state that meets both listed conditions and
  on which activation reverts. This is a wording issue; the code is the stricter side.
- **Scope of "genesis runs once":** the facet does not enforce it. `genesisUpgrade` is
  `onlyChainTypeManager` and is blocked only while an L2 upgrade transaction is pending
  (`GenesisRerunsAfterFinalization`). Once-only rests on the CTM calling it only from
  `createNewChain` (`ChainTypeManager.sol:703-707`; a source search finds no other call).
- **Configuration obligation:** `unfreezeDiamond` works only if its selector is not freezable
  (`FreezeUnfreezeExact`). If the admin facet were registered freezable, one freeze would be
  permanent (`FreezableUnfreezeStrandsTheChain`). Freezability is release configuration
  (`OPS-CONFIG`).

## Open

- Nothing is proved about runs that contain arbitrary cuts, except the version bound and the
  freeze-strand result. Stronger statements need a model of the transition engines at this
  commit (`DefaultUpgrade`, `CTMTransition`); `../ChainTypeManager/` has them at `e561b9cc2`.
- "Runs only the CTM-committed cut" is proved up to the oracle `Env.upgradeCutForVersion`. That
  the CTM's answer is derived from the transition committed for the edge is the CTM's code
  (`ChainTypeManager.sol:601-607`), not modelled here.
- `GenuineGenesis` is a premise: that the CTM's `l1GenesisUpgrade()` address holds this commit's
  `L1GenesisUpgrade`. The nonzero genesis transaction hash in `GenesisRunsOnce` is also a
  premise (a keccak output).
- The fee-parameter checks (the price-change bound, the one-day update interval) are transcribed
  in `exec`, but no property is stated about them beyond the fields frozen by priority mode.
- Reverts from arithmetic overflow are omitted, so each "succeeds iff" statement is exact for the
  model and an upper bound on success for the source.

## Review order

1. `Specs/AdminFacet.lean` against `Admin.sol` and `ZKChainBase.sol`: `State`, then `exec` entry
   by entry, then `Role`, `Foreign`, `genesisEffect`.
2. `Specs/Mutants.lean`: each mutant deletes exactly one check.
3. `Properties/Access.lean`, `Properties/PriorityMode.lean`, `Properties/Upgrade.lean`,
   `Properties/NatSpec.lean`: each statement and its docstring.
4. `Proofs/` only if needed. The audit checks that every property has its full named theorem.
