# RegistryBootstrapMigration

Source: `l1-contracts/contracts/upgrades/registry/bootstrap/RegistryBootstrapMigration.sol`,
with `RegistryBootstrapSequence.sol` (the governance bundle it derives) and
`libraries/RegistryAuthorityLib.sol` (the authority checks). The code is **not** in the pinned
era-contracts tree. It lives on branch `feat/upgrade-simplification` of the zksync-era
`contracts` repository, and this model was written against commit **`e561b9cc2`**
(2026-10-19), the same commit as `../ChainTypeManager/`. **The branch moves**: every
`file:line` quoted in the spec is at that commit. The exception is topic AuthorityEngineV35,
pinned to era-contracts `draft/v0.35.0` at **`b17415d20`** (see its section below).

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact
named propositions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Authority | [Specs/Authority.lean](Specs/Authority.lean) | [Properties/Authority.lean](Properties/Authority.lean) | [Proofs/Authority.lean](Proofs/Authority.lean) |
| Forward | [Specs/Forward.lean](Specs/Forward.lean) | [Properties/Forward.lean](Properties/Forward.lean) | [Proofs/Forward.lean](Proofs/Forward.lean) |
| AuthorityStrong | [Specs/AuthorityStrong.lean](Specs/AuthorityStrong.lean) | [Properties/AuthorityStrong.lean](Properties/AuthorityStrong.lean) | [Proofs/AuthorityStrong.lean](Proofs/AuthorityStrong.lean) |
| AuthorityEngineV35 | [Specs/AuthorityEngineV35.lean](Specs/AuthorityEngineV35.lean) | [Properties/AuthorityEngineV35.lean](Properties/AuthorityEngineV35.lean) | [Proofs/AuthorityEngineV35.lean](Proofs/AuthorityEngineV35.lean) |

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

## Engine legs at draft/v0.35.0 (topic AuthorityEngineV35)

Pinned to era-contracts `draft/v0.35.0` at `b17415d20`; paths under `l1-contracts/contracts/`.
There both domain executors apply a transition through an **engine leg**
(`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:51-104`): they delegatecall the
engine the transition pins, so it runs with the executor's address and storage. Before it runs,
a CTM leg refuses a CTM whose `admin()` is the `ProxyAdmin` (:75-77). After it returns, the leg
compares the executor's owner and nominee with their start values (:93-95), and a hash of the
domain's holders (`_domainHolders`, :118-148) with its start value (:96-98). The bootstrap
bundle itself runs a core leg (`upgrades/registry/bootstrap/RegistryBootstrapSequence.sol:100-108`).
The model summarises that leg: the bundle is `Authority`'s bundle step (`VLabel.tx`), which
leaves the new fields alone, and is not run as a `VLabel.engineLeg`.
The model reuses `Authority`'s `MigrateStep` and `Forward`'s `OpStep`; at `b17415d20`, `migrate()`
(`upgrades/registry/bootstrap/RegistryBootstrapMigration.sol:265-307`) makes the calls those
models quote.

- The model (`VState`) adds the executors' ownership, the ecosystem `ProxyAdmin`'s owner, the
  CTM's `admin()`, private `pendingAdmin` and notifier address, a notifier state per address,
  and what the CTM's code answers to the ownership reads. A leg is a call trace run in its
  executor's storage (`EngineLeg`). `holdersHash` is an arbitrary function: every result about
  a leg carries a collision on the leg's own logged `(before, after)` pair as a disjunct.
- A leg can neither park nor unpark: `EngineLegKeepsItsExecutor` (exactly),
  `EngineLegOwnDomainFrameOrCollision`, `EngineLegOtherDomainFrame` (exactly, when the other
  domain's holders send no call and a core leg calls no `migrate()`), `EngineLegFrameOrCollision`,
  `EngineLegNeitherParksNorUnparks`. For a CTM leg these need the CTM to answer its ownership
  reads from its slots. `EngineLegKeepsCtmBindingsOrCollision`: the CTM's admin, its notifier
  and that notifier's owner, nominee, CTM and proxy-admin read are kept, or the hash collides.
  `EngineLegRefusesCtmAdminProxyAdmin` is the pre-check.
- `LegCannotRecoverParkedCTM`: from the state `NonGenuineExecutorParksTheCTM` leaves, a CTM leg
  keeps the CTM parked or collides; the nominee's accept recovers it as a call trace.
  `LegRenounceReverts`: a CTM leg (CTM answering from its slots) or a core leg keeps the nonzero
  owners it checks nonzero, or collides.
- Runs: `CallTracesAreForwards` and `EngineLegCallsAreAForward` project traces onto `Forward`'s
  `FRun`. `NoReparkingAcrossEngineLegs` and `MigrateLeavesNothingParkedWithEngineLegs`: nothing
  is re-parked along runs of transactions, call traces and engine legs, or the run passes a leg
  whose hash collides on that leg's pair (`RunLegCollides`; runs are deterministic,
  `EngineRunsDeterministic`). CTM legs may swap the CTM's implementation as long as the new
  code answers the ownership reads from its slots. These run results assume that swapped-in
  CTM code keeps the modelled entry points (a model boundary stated in the spec).
- `EngineReachesOnlyAcceptCTMOwnership`: calling back into its executor, the engine passes no
  caller check but `acceptCTMOwnership`'s. `ExecutorOwnerNeverZero`: with no call sent by the
  zero address, the executors' nonzero owners stay nonzero, engine legs included.
- **Countermodels**: `CollisionDisjunctNeeded`, `NoReparkingCollisionDisjunctNeeded` and
  `CtmBindingsCollisionNeeded` (each collision disjunct is load-bearing); `NoHolderCheckReparks`
  (without :96-98 a leg re-parks the CTM); `EngineCtmSwapReparks` (a CTM code swap whose new
  code answers the old holders re-parks unseen, the case the upstream docs place outside the
  check, `docs/registry-driven-upgrades.md:287-290` from the repository root);
  `CoreLegMayRunMigrate` and
  `OtherDomainQuietNeeded` (both clauses of `OtherDomainQuiet` are needed);
  `UnnamedNotifierIsUnchecked`; `EngineCtmAdminNominationUnseen` (the CTM's `pendingAdmin` is
  not hashed, as `ProxyUpgradeExecutorBase.sol:114-117` states); `EngineGatePremisesNeeded`.
- Witnesses: `EngineLegTransientWitness` (a leg that hands the CTM to `7` and back succeeds for
  every hash: the checks see net effects only) and `EngineLegPremisesWitness` instantiate every
  premise.
- Not modelled: `changeProxyAdmin` on the CTM proxy (its admin is fixed, so the case the
  pre-check guards is not reached; the per-leg results quantify over every start state, and for
  a CTM leg they assume the CTM proxy sits under the `ProxyAdmin`, since another admin's code
  swaps of the CTM have no step), nested legs of the other domain, the rows check, ETH and
  events. The earlier `d9f6789` version of this topic hashed fewer fields and read the notifier
  address once; the spec header lists the differences.

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
