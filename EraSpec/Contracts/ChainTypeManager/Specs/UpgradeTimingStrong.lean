import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTiming
import EraSpec.Contracts.ChainTypeManager.Specs.Enabledness

/-!
# Model: the departing version's deadline along timed runs

Source: branch `feat/upgrade-simplification` of the zksync-era `contracts` repository at
commit `e561b9cc2` (2026-10-19), as for `EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTiming`,
whose timed system this topic reads. The branch moves; every `file:line` below is at that
commit. Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.UpgradeTimingStrong` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTimingStrong`.

## Why this is modelled

`VersionEdgeLib.requireValidEdge` gives the reason for its relative schedule check
(`upgrades/registry/libraries/VersionEdgeLib.sol:58-62`):

    // The old version must stay usable at least until chains are allowed to upgrade,
    // otherwise the schedule disables the old protocol before the new one is reachable.
    if (_oldVersionDeadline < _upgradeTimestamp) {
        revert TransitionDeadlineBeforeUpgrade(_oldVersionDeadline, _upgradeTimestamp); }

`Properties.ValidEdgeHasNoDeadTime` (`UpgradeTiming`) checks this sentence on the deadline
getter only. Its CTM state is arbitrary, reachable or not. The slot's valid schedule is a
premise. Its other disjunct is the manifest's time gate, which is one gate of an upgrade
(`UpgradeChainEnabledIffTimed`). This topic adds what is needed to state the sentence about the
system: about the states timed runs reach, with "the new one is reachable" read as an upgrade
step that exists.

## Where a slot's schedule comes from

The CTM never checks that a schedule is valid. `setNewVersionUpgradeFromTransition` and
`replaceUpgradeTransition` (`state-transition/ChainTypeManager.sol:408-448`) read the object's
getters, and the transition's `validate()`, which `_requireExecutable` calls (:454-457), checks
only that its engine and composer have code (`upgrades/registry/objects/CTMTransition.sol:227-233`).
The transition is the one governance approved, and "its construction is verified off-chain, not
here" (`ChainTypeManager.sol:405-407`). Every `CTMTransition` constructor runs
`requireValidEdge` (`upgrades/registry/objects/CTMTransition.sol:91-97`), so every
`CTMTransition` object has a `ValidSchedule`. `Op.CommitsValidSchedule` says this of the
transition a writer puts in a slot: the committed transition, or the replacement. Like
`World.Genuine`, it is a premise about the objects governance commits.

## The same-deadline check

`replaceUpgradeTransition` runs `_requireSameDeadline(_expectedTransition, _replacement)` (:443,
defined at :488-494):

    uint256 deadline = _expectedTransition.oldProtocolVersionDeadline();
    uint256 replacementDeadline = _replacement.oldProtocolVersionDeadline();
    if (replacementDeadline != deadline) { revert TransitionDeadlineMismatch(deadline, replacementDeadline); }

"Deadline changes use {setProtocolVersionDeadline} explicitly" (:485). `CStep.replace` omits this
check: `Specs/VersionRegistry.lean` models no deadline. `Op.KeepsDeadline` states the check, and
it is a premise of the results that need it.

## Validated installs, for timed labels

`TimedLabel.InstallsWf` lifts `Label.InstallsWf` (`Specs/Enabledness.lean`) to timed labels: the
release a CTM writer installs passed `validate()`'s duplicate-selector check, as
`_setCurrentRelease` requires (`ChainTypeManager.sol:310`).

## Dead time

`ChainDeadTime T d s id τ` says that at block time `τ` chain `id` is stuck. Its version is not
active, so the committer refuses its batches (`state-transition/chain-deps/facets/Committer.sol:85-87`).
And no upgrade of the chain succeeds, through any entry point and by any caller. The deadline
overrides `d` are a parameter, as in `UpgradeTiming`.
-/

namespace Contracts.ChainTypeManager

/-! ## What a writer puts in a slot -/

/-- The transition a CTM writer records in `upgradeTransition` passed `requireValidEdge`'s
schedule checks (`VersionEdgeLib.sol:55-62`), as every `CTMTransition` does at construction
(`CTMTransition.sol:91-97`). A commit records its transition (`ChainTypeManager.sol:421`). A
replacement records the replacement (:447). The legacy writers record no transition. -/
def Op.CommitsValidSchedule (T : TimedConfig) : Op → Prop
  | .commit t => ValidSchedule T t
  | .replace _ r => ValidSchedule T r
  | .legacyCommit _ _ => True
  | .legacyRecut _ => True

/-- `Op.CommitsValidSchedule` for a step of the routing system. Chain steps record no
transition. -/
def Label.CommitsValidSchedule (T : TimedConfig) : Label → Prop
  | .ctm op => op.CommitsValidSchedule T
  | _ => True

/-- `Label.CommitsValidSchedule` for a timed label. An upgrade, a notifier write and a
`DiamondAux` write record no transition. -/
def TimedLabel.CommitsValidSchedule (T : TimedConfig) : TimedLabel → Prop
  | .base l => l.CommitsValidSchedule T
  | _ => True

/-- `_requireSameDeadline` (`ChainTypeManager.sol:488-494`): a replacement pins the same
`oldProtocolVersionDeadline()` as the transition it replaces. The other writers replace
nothing. -/
def Op.KeepsDeadline (T : TimedConfig) : Op → Prop
  | .replace e r => (T.sched r).deadline = (T.sched e).deadline
  | _ => True

/-- `Op.KeepsDeadline` for a step of the routing system. -/
def Label.KeepsDeadline (T : TimedConfig) : Label → Prop
  | .ctm op => op.KeepsDeadline T
  | _ => True

/-- `Label.KeepsDeadline` for a timed label. -/
def TimedLabel.KeepsDeadline (T : TimedConfig) : TimedLabel → Prop
  | .base l => l.KeepsDeadline T
  | _ => True

/-- `Label.InstallsWf` for a timed label: a base step installs what its routing step installs.
An upgrade installs no release on the CTM, and the timed model's own steps touch no release. -/
def TimedLabel.InstallsWf (W : World) : TimedLabel → Prop
  | .base l => l.InstallsWf W
  | _ => True

/-- Every committed slot holds a transition whose schedule passed `requireValidEdge`. Both
starting states (`initState`, `bootstrapState`) have no committed slot. -/
def SlotSchedulesValid (T : TimedConfig) (s : CTM) : Prop :=
  ∀ v, s.ut v ≠ 0 → ValidSchedule T (s.ut v)

/-! ## Dead time -/

/-- **Dead time** for chain `id` at block time `τ`, under the stored deadline overrides `d`.
The chain is registered. Its version is not active (`protocolVersionIsActive` is false, so
`Committer.sol:85-87` refuses its batches). And no upgrade of it succeeds at `τ`, through any
entry point and by any caller. -/
def ChainDeadTime (T : TimedConfig) (d : ℕ → ℕ) (s : TimedSys) (id : ChainId) (τ : ℕ) : Prop :=
  ∃ c, s.sys.chains id = some c ∧ ¬ ProtocolVersionActive T d s.sys.ctm c.pv τ ∧
    ∀ path caller, ¬ ∃ s', TimedStep T s (.upgrade id path caller τ) s'

/-! ## Witness data

The `UpgradeTiming` witness configuration `wTiming`, with two variants. Transition `300`
(1→2) may be crossed from time `10` and keeps version 1 usable until `20`. Its replacement
`400` has upgrade time `15` and the same deadline `20`. -/

/-- `wTiming` with transition `300`'s deadline at `5`, before its upgrade time `10`.
`requireValidEdge` refuses this schedule (`TransitionDeadlineBeforeUpgrade`,
`VersionEdgeLib.sol:60-62`). -/
def wBadSchedTiming : TimedConfig :=
  { wTiming with sched := fun a => if a = 300 then ⟨10, 5⟩ else wTimingSched a }

/-- `wTiming` with transition `400`'s schedule at upgrade time `10` and deadline `12`. That
schedule is valid. But `12` is not the deadline `20` of the transition `300` that `400`
replaces in the witness, so `_requireSameDeadline` refuses that replacement. -/
def wShortDeadlineTiming : TimedConfig :=
  { wTiming with sched := fun a => if a = 400 then ⟨10, 12⟩ else wTimingSched a }

/-- A chain's `DiamondAux` as in `wTimingAux`, but settling on a layer at version `1`, behind
the target version `2` of transition `300`. -/
def wSlBehindAux : DiamondAux := { wTimingAux with slVersion := some 1 }

/-- A chain's `DiamondAux` as in `wTimingAux`, but with one batch committed and not
executed. -/
def wPendingBatchAux : DiamondAux := { wTimingAux with committed := 1 }

end Contracts.ChainTypeManager
