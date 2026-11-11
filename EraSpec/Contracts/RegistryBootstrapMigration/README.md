# RegistryBootstrapMigration

Source: `l1-contracts/contracts/upgrades/registry/bootstrap/RegistryBootstrapMigration.sol`,
with `RegistryBootstrapSequence.sol` (the governance bundle it derives) and
`libraries/RegistryAuthorityLib.sol` (the authority checks). The code is **not** in the pinned
era-contracts tree. It lives on branch `feat/upgrade-simplification` of the zksync-era
`contracts` repository, and this model was written against commit **`e561b9cc2`**
(2026-10-19), the same commit as `../ChainTypeManager/`. **The branch moves**: every
`file:line` quoted in the spec is at that commit.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact
named propositions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Authority | [Specs/Authority.lean](Specs/Authority.lean) | [Properties/Authority.lean](Properties/Authority.lean) | [Proofs/Authority.lean](Proofs/Authority.lean) |

Namespace: `Contracts.RegistryBootstrapMigration`. Statements are
`Contracts.RegistryBootstrapMigration.Properties.*`; each certificate has the same name
without the `Properties` segment.

## The claim, and what "parked" means

The contract says (`RegistryBootstrapMigration.sol:48-50`) "Authority is never parked:
`migrate()` acquires nothing it does not hand onward in the same transaction". The model reads
**parked** as `ParkedOnMigration`: the spent migration owns the CTM, is the CTM's
`Ownable2Step` nominee, or owns the CTM-domain `ProxyAdmin`. The migration has no entry point
left that could use that authority. `validateApplied()` also requires that no CTM nomination is
outstanding, so the model tracks `ctmPending` separately.

## What to check

- `MigrateLeavesNothingParked`: with a genuine `CTMUpgradeExecutor`, a successful `migrate()`
  leaves the CTM and the `ProxyAdmin` with the executor and no nomination outstanding, and
  `validateApplied()` passes. `MigrateWitness` fires it from governance's hand-over, through the
  claim at :271-273.
- `BundleNeverParks`: the bundle's last four calls, run in one transaction, park nothing,
  whatever the executor's code. Its last call is `validateApplied()`, and
  `ValidateAppliedExcludesParking` holds. `BundleWitness` shows a bundle that commits.
- `MigrateIsOneShot`, `NoReparkingAfterMigrate`: once spent, the migration never acts again.
  Nothing is re-parked unless a transaction hands authority back to it.
- **Countermodel** `NonGenuineExecutorParksTheCTM`: `validate()` checks the executor's getters,
  not its code. Take an executor that answers the getters correctly but whose
  `acceptCTMOwnership()` does nothing. Then `migrate()` succeeds and leaves the CTM owned by the
  spent migration, with the executor nominated. The bundle reverts at `validateApplied()`.
  `ParkedCTMLeavesOnlyByNomineeAccept`: after that, only the nominee's own accept moves the CTM.
- **Countermodel** `SplitBundleParksProxyAdmin`: here the bundle's calls are sent as separate
  transactions, and the CTM's version has drifted. The `ProxyAdmin` (plain `Ownable`) then
  belongs to the migration and `migrate()` reverts. `ProxyAdminLeavesMigrationOnlyByMigrate`:
  only a later successful `migrate()` moves it. Atomic bundle execution is what rules this out.
- `ParkedFramesFire` shows that both frames have content. In the parked CTM state, the
  nominee's accept fires. In the parked `ProxyAdmin` state, a transfer back to governance is
  refused.

## Model boundaries

- A revert is the absence of a step. Reject-only code, bytecode and release checks are
  omitted, which only adds runs.
- Executors are their getters plus one bit for `acceptCTMOwnership()`: genuine logic, or no
  effect. An executor that reverts there makes `migrate()` revert, which means there is no step.
- The core domain, the ServerNotifier handover and the executors' own ownership are fixed
  configuration (`coreHeld`, `notifierOk`, `ExecView`). They are not state.
- Other actors are over-approximated. Any owner other than the migration may nominate, transfer
  the `ProxyAdmin`, or move the CTM's version, and any nominee other than the migration may
  accept.
- The CTM implementation swap applied by the bootstrap rows is assumed to keep the
  `Ownable2Step` storage.

## The CTM executor's `forward`

Not modelled as its own step here. What a genuine executor's `forward` can do to the
authorities this model tracks is a sequence of steps the model already admits for any owner
other than the migration: nominate on the CTM, transfer the `ProxyAdmin`, accept a
nomination, move the CTM's version. The results that hold "along any run" therefore cover
those forwarded calls (this is an argument about the label set, not a separate theorem).
One forwarded call is outside the label set: `CTM_PROXY_ADMIN.upgradeAndCall` on the CTM
proxy, which can rewrite the CTM's owner slot directly; `ParkedCTMLeavesOnlyByNomineeAccept`
states that omission. Its effect on the CTM's version state is in
`../ChainTypeManager/` (`ExecutorForward`, `ForwardCtmSwapBreaksInvariants`).
