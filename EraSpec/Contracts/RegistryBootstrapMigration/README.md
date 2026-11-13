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
| Forward | [Specs/Forward.lean](Specs/Forward.lean) | [Properties/Forward.lean](Properties/Forward.lean) | [Proofs/Forward.lean](Proofs/Forward.lean) |
| AuthorityStrong | [Specs/AuthorityStrong.lean](Specs/AuthorityStrong.lean) | [Properties/AuthorityStrong.lean](Properties/AuthorityStrong.lean) | [Proofs/AuthorityStrong.lean](Proofs/AuthorityStrong.lean) |

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
  `ParkedCTMLeavesOnlyByNomineeAccept`: after that, within the label model (no CTM code
  swaps), only the nominee's own accept moves the CTM. With code swaps there is a second exit,
  and the `ProxyAdmin`'s owner who can take it need not be the nominee (AuthorityStrong below).
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
  accept. The list omits `renounceOwnership` on the CTM and the `ProxyAdmin` (see Forward:
  outside the label set, parks nothing, strands authority).
- The CTM implementation swap applied by the bootstrap rows is assumed to keep the
  `Ownable2Step` storage.

## The CTM executor's `forward` (topic Forward)

`UpgradeExecutorBase.forward` (`governance/UpgradeExecutorBase.sol:32-46`) is modelled as a
list of calls, each with its own `msg.sender`: the calls `forward` makes, sent by the
executor, and the calls their targets make in turn, sent by those targets. The entry points
are the writers of the tracked slots: the CTM's `transferOwnership`, `acceptOwnership`,
`renounceOwnership` and owner-only version writers; the `ProxyAdmin`'s `transferOwnership` and
`renounceOwnership`, and `upgrade`/`upgradeAndCall` on the CTM proxy; `migrate()`; plus a call
that writes nothing tracked. No premise is made on the executor's code.

- `ForwardIsARun`: a successful forward is a run of this model's labels if none of its calls
  is sent by the migration or the zero address, renounces an ownership, or replaces the CTM's
  code. Each call becomes its other-actor label, or `migrate`. The labels hand authority to
  the migration only where the calls do.
- `RunsWithForwardsAreRuns` lifts this to runs mixing forwards with the model's transactions,
  so the "along any run" results (`NoReparkingAfterMigrate`, ...) apply to them. Conversely,
  from nonzero owners, each label other than the bundle is one covered call
  (`LabelsAreCoveredCalls`).
- Stronger direct forms: `NoReparkingAcrossForwards` (no premise on senders, and renounces
  allowed); `ForwardMovesParkedCTMOnlyByNomineeAccept` (the accept must be the start state's
  nominee's); `ForwardMovesParkedProxyAdminOnlyByMigrate` (holds even with code swaps).
- **The label set misses `renounceOwnership`.** The CTM (`Ownable2StepUpgradeable`) and the
  CTM-domain `ProxyAdmin` (OpenZeppelin `Ownable`) both keep it, and a forward can call it.
  - No run of the labels reaches the state it leaves, because those runs keep both owners
    nonzero (`LabelRunsKeepOwnersNonzero`, `ForwardedRenounceLeavesTheLabelSet`).
  - It parks nothing, but it strands authority (`RenouncedAuthorityIsStranded`,
    `RenounceStrandsWitness`): an ownerless `ProxyAdmin` never gets an owner again; an
    ownerless CTM with no nominee gets an owner back only through a code swap by the
    `ProxyAdmin`'s owner.
- **Excluded: replacing the CTM's code** (`upgrade`/`upgradeAndCall` on the CTM proxy). It can
  re-park the CTM on the spent migration with no ownership call naming it
  (`ForwardCtmSwapReparks`), and move a parked CTM without the nominee's accept
  (`ForwardCtmSwapMovesParkedCTM`). On the version state it voids the CTM's invariants
  (`../ChainTypeManager/`, `ForwardCtmSwapBreaksInvariants`).
- Witnesses: `ForwardWitness` (the bundle, then executor succession through `forward`, with
  the successor's accept as a nested call); `ParkedForwardFramesFire` (a forwarded
  `acceptOwnership()` recovers the CTM that the non-genuine executor left parked, and a
  forwarded `migrate()` moves the `ProxyAdmin`).
- Not modelled: `ProxyAdmin.changeProxyAdmin` on the CTM proxy (who administers the CTM proxy
  is configuration), ETH, events. The mapping from a real forward, nested calls included, to
  the list of calls is a model boundary. This authority model and `../ChainTypeManager/`'s
  version model are separate; they are linked only by documentation.

## Who can move a parked CTM (topic AuthorityStrong)

AuthorityStrong uses the Authority and Forward models unchanged and adds witness data.

- **Countermodel** `ParkedPAOwnerNeedNotBeNominee`: from the state the non-genuine executor's
  `migrate()` leaves, one ordinary `transferPA 7` by the `ProxyAdmin`'s owner `3` reaches a
  parked state where the `ProxyAdmin`'s owner is `7`, not the nominee `3`. A code swap by `7`
  then moves the CTM off the migration with no accept. This refutes the earlier docstring of
  `ParkedCTMLeavesOnlyByNomineeAccept` ("that owner is the nominee too"), now corrected.
- `ParkedCTMLeavesByAcceptOrCodeSwap`: with every call included and none sent by the migration,
  one call from a parked state keeps the owner and the nominee, or is the nominee's
  `acceptOwnership()`, or is a CTM code swap sent by the `ProxyAdmin`'s owner of that state.
- `ParkedCTMFirstExit`: along any sequence of such calls, the CTM stays parked with its nominee,
  or the run splits at a call before which every state is parked with the start's nominee (so
  it is the first call that moves the CTM), and that call is the start nominee's accept or a
  code swap by the `ProxyAdmin`'s owner of that moment. `SpentProxyAdminCustody`: once the edge is spent, that
  owner is the start's, zero, or named by a `ProxyAdmin` transfer in the sequence.
- `SpentLabelRunsAreCalls`: from a spent edge, every label run is a run of calls none sent by
  the migration, so the results above cover the label model.
- `AuthorityStrongWitness` fires both exits from `wParked`.

## Source findings

Reported to the maintainer of this repo, not yet confirmed upstream. Each was checked by two
independent verifiers; only findings both upheld are listed, with the classification both
gave. Paths are under `l1-contracts/contracts/` at `e561b9cc2`.

- *real-bug.* `ChainTypeManager` (`state-transition/ChainTypeManager.sol:58`,
  `Ownable2StepUpgradeable`) does not disable `renounceOwnership`, so one forwarded call
  leaves the CTM with neither owner nor nominee (`RenouncedAuthorityIsStranded`). This
  conflicts with `governance/UpgradeExecutorBase.sol:14-17` and :48-53, which disable it on
  the executor so that its authority is never stranded. Only the executor's owner (governance)
  can send the call; recovery is a CTM code swap by the `ProxyAdmin`'s owner. The same call on
  the CTM-domain `ProxyAdmin` was classified not-an-issue by both: governance can strand it
  through `forward` in other ways a renounce guard would not stop.
- *repo-doc-stale, low.* This README's earlier argument that forwarded calls are covered by
  the label set omitted `renounceOwnership` (`ForwardedRenounceLeavesTheLabelSet`). Corrected
  above.
