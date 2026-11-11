import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTimingStrong

/-!
# Properties: no dead time along timed runs

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTimingStrong`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTimingStrong`.

## What `ValidEdgeHasNoDeadTime` says, and what this file adds

`Properties.ValidEdgeHasNoDeadTime` (`UpgradeTiming`) is arithmetic on the
`protocolVersionDeadline` getter, for an arbitrary CTM state. It assumes that slot's schedule
is valid. Its right disjunct is the manifest's time gate, which is one gate of an upgrade
(`UpgradeChainEnabledIffTimed`). This file states the claim about the system.

* **Every reachable slot has a valid schedule** (`ReachableSlotsHaveValidSchedules`). Along any
  timed run, break-glass cuts included, from a state whose committed slots have valid schedules
  (a starting state has no committed slot), every committed slot holds a transition with a
  valid schedule, provided every transition the run commits or installs as a replacement has
  one. At the source, every `CTMTransition` has one by construction.
* **Headline: no dead time, with real upgrade steps** (`ValidatedTimedRunsHaveNoDeadTime`).
  Take a timed run from an invariant state, with no break-glass cut, in which every installed
  release passes `validate()` and every committed or replacement transition has a valid
  schedule. Take a chain at the end at a version with a committed edge. Suppose there is no
  deadline override at that version, the chain has executed every committed batch, and its
  settlement layer, if it has one, is at the edge's target version. Then the chain is never in
  dead time. At every block time its version is active, or its admin can upgrade it directly
  and the CTM's owner can upgrade it through the CTM. Both upgrades land it on the arriving
  release at the edge's new version. At the edge's upgrade timestamp, both hold.
* **The two per-chain gates are needed** (`ValidScheduleAloneLeavesDeadTime`). Without them a
  valid, non-overridden schedule still leaves dead time. In the witness run, a chain whose
  settlement layer is behind the target cannot commit or cross after the deadline. Neither can
  one with an unexecuted batch. So the reading "a schedule that passed `requireValidEdge`
  leaves no instant at which chains at the departing version can neither commit batches nor
  cross the edge" is false as stated. The headline is its repaired form.
* **The other premises are needed too** (`NoDeadTimeNeedsItsOtherPremises`). A deadline
  override, a schedule `requireValidEdge` refuses, and a break-glass cut each open dead time in
  the witness. `DuplicateSelectorBricksEdge` (`Enabledness`) shows what happens without
  validated installs.
* **The deadline does not move** (`SameDeadlineReplacementsFixTheDeadline`). Suppose every
  replacement keeps the replaced transition's deadline (`_requireSameDeadline`). Then the
  deadline of a version with a committed edge is the same at the end of every timed run, and so
  is the set of block times at which the version is active. Only an owner override can move it.
  The no-dead-time headline does not need this premise: the replacement's own valid schedule is
  enough. `ReplacementDeadlineWitness` shows that the model's replacement step, which omits
  `_requireSameDeadline`, can move the deadline when the premise fails.

Witness: `NoDeadTimeWitness` is a run from a fresh CTM that meets every premise of the
headline. In it, each branch of the disjunction occurs without the other.
-/

namespace Contracts.ChainTypeManager

/-! ## Reachable slots -/

/-- **EVERY REACHABLE SLOT HAS A VALID SCHEDULE.** Start from a state whose committed slots all
hold transitions with valid schedules, for example a starting state, which has no committed
slot. Take any timed run, break-glass cuts included, in which every committed transition and
every replacement passed `requireValidEdge`'s schedule checks. At its end every committed slot
holds a transition with a valid schedule. No invariant is needed: only a commit and a
replacement write a slot, and each writes the transition it names. -/
def Properties.ReachableSlotsHaveValidSchedules : Prop :=
  ∀ (T : TimedConfig) (s s' : TimedSys) (ls : List TimedLabel),
    SlotSchedulesValid T s.sys.ctm → TimedRun T s ls s' →
    (∀ l ∈ ls, l.CommitsValidSchedule T) → SlotSchedulesValid T s'.sys.ctm

/-! ## The headline -/

/-- **HEADLINE: NO DEAD TIME ALONG VALIDATED TIMED RUNS.** Take a timed run with these
properties:
* it starts from a state satisfying `SysInv`, whose installed releases list each selector once,
  and whose committed slots have valid schedules;
* it has no break-glass cut;
* every release the CTM installs passes `validate()`'s duplicate check, as `_setCurrentRelease`
  requires;
* every transition it commits or installs as a replacement passed `requireValidEdge`'s
  schedule checks, as every `CTMTransition` does.

At its end, take a chain at a version `v` with a committed edge. Suppose the owner has not
overridden `v`'s deadline, every committed batch of the chain is executed, and the settlement
layer the chain settles on, if any, is at the edge's target version or later. Then:
* the chain is in dead time at no block time;
* at every block time `τ`, `protocolVersionIsActive(v)` holds (the committer's version check
  passes), or both of these upgrades succeed at `τ`: a direct
  `upgradeChainFromVersion(_, v)` by the chain's admin, and the CTM's
  `upgradeChainFromVersion(id, v)` by the CTM's owner. Both land the chain on the arriving
  release at the edge's new version, and change nothing else;
* at the edge's upgrade timestamp, the version is active and both upgrades succeed.

The model omits further reject-only checks of an upgrade (see `Specs/UpgradeTiming.lean`), so
at the source these upgrades also need those checks to pass. -/
def Properties.ValidatedTimedRunsHaveNoDeadTime : Prop :=
  ∀ (T : TimedConfig) (d : ℕ → ℕ) (s s' : TimedSys) (ls : List TimedLabel),
    SysInv T.X.W s.sys → RecordedReleasesWf T.X.W s.sys.ctm → SlotSchedulesValid T s.sys.ctm →
    TimedRun T s ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) → (∀ l ∈ ls, l.InstallsWf T.X.W) →
    (∀ l ∈ ls, l.CommitsValidSchedule T) →
    ∀ id c, s'.sys.chains id = some c → s'.sys.ctm.ut c.pv ≠ 0 → d c.pv = 0 →
      (s'.aux id).committed = (s'.aux id).executed →
      (∀ w, (s'.aux id).slVersion = some w → (s'.sys.edge T.X.W c.pv).new ≤ w) →
      (∀ τ, ¬ ChainDeadTime T d s' id τ) ∧
      (∀ τ, ProtocolVersionActive T d s'.sys.ctm c.pv τ ∨
        (TimedStep T s' (.upgrade id (.direct c.pv) (s'.aux id).admin τ)
            { s' with sys := s'.sys.crossEdge T.X.W id c } ∧
          TimedStep T s' (.upgrade id (.ctm c.pv) T.ctmOwner τ)
            { s' with sys := s'.sys.crossEdge T.X.W id c })) ∧
      ProtocolVersionActive T d s'.sys.ctm c.pv (T.sched (s'.sys.ctm.ut c.pv)).upgradeTimestamp ∧
      TimedStep T s' (.upgrade id (.direct c.pv) (s'.aux id).admin
          (T.sched (s'.sys.ctm.ut c.pv)).upgradeTimestamp)
        { s' with sys := s'.sys.crossEdge T.X.W id c } ∧
      TimedStep T s' (.upgrade id (.ctm c.pv) T.ctmOwner
          (T.sched (s'.sys.ctm.ut c.pv)).upgradeTimestamp)
        { s' with sys := s'.sys.crossEdge T.X.W id c }

/-! ## The premises are needed -/

/-- **A VALID SCHEDULE ALONE LEAVES DEAD TIME.** This refutes the reading "a schedule that
passed `requireValidEdge` leaves no instant at which chains at the departing version can
neither commit batches nor cross the edge". Transition `300`'s schedule is valid (time `10`,
deadline `20`), and no deadline is overridden. Each run below meets every run premise of
`ValidatedTimedRunsHaveNoDeadTime`, and its start meets the state premises
(`NoDeadTimeWitness`). Each run is `wTimingSetup` (chain `0` created at version 1, `300`
committed), then one write to chain `0`'s `DiamondAux`:
* the chain now settles on a layer at version `1`, behind `300`'s target `2`;
* or the chain now has a committed batch that is not executed.

In both end states chain `0` is in dead time at time `25`. Version 1 has expired, and no
upgrade of the chain succeeds, by any entry point and any caller. -/
def Properties.ValidScheduleAloneLeavesDeadTime : Prop :=
  ValidSchedule wTiming 300 ∧ (wTiming.sched 300).deadline < 25 ∧
    (∀ l ∈ wTimingSetup ++ [.setAux 0 wSlBehindAux],
      ¬ l.isArbitrary ∧ l.InstallsWf wTiming.X.W ∧ l.CommitsValidSchedule wTiming) ∧
    (∃ s, TimedRun wTiming wTimingSys0 (wTimingSetup ++ [.setAux 0 wSlBehindAux]) s ∧
      s.sys.ctm.ut 1 = 300 ∧ (s.aux 0).committed = (s.aux 0).executed ∧
      (s.aux 0).slVersion = some 1 ∧ (s.sys.edge wTiming.X.W 1).new = 2 ∧
      ChainDeadTime wTiming (fun _ => 0) s 0 25) ∧
    (∀ l ∈ wTimingSetup ++ [.setAux 0 wPendingBatchAux],
      ¬ l.isArbitrary ∧ l.InstallsWf wTiming.X.W ∧ l.CommitsValidSchedule wTiming) ∧
    ∃ s, TimedRun wTiming wTimingSys0 (wTimingSetup ++ [.setAux 0 wPendingBatchAux]) s ∧
      s.sys.ctm.ut 1 = 300 ∧ (s.aux 0).committed ≠ (s.aux 0).executed ∧
      (s.aux 0).slVersion = none ∧ ChainDeadTime wTiming (fun _ => 0) s 0 25

/-- **THE OTHER PREMISES OF THE HEADLINE ARE NEEDED TOO.** In the state the run `wTimingSetup`
reaches, chain `0` is at version 1 with `300` committed, has executed every batch and settles on
L1:
* **deadline override.** With version 1's deadline overridden to `1`
  (`setProtocolVersionDeadline(1, 1)`), the chain is in dead time at time `5`;
* **a schedule `requireValidEdge` refuses.** Under `wBadSchedTiming`, where `300`'s deadline
  `5` comes before its upgrade time `10`, the same run reaches the same state, and the chain is
  in dead time at time `7`;
* **break-glass.** After a break-glass cut that adds selector `9` to chain `0`'s routing, the
  chain is in dead time at time `25`: version 1 has expired, and the routing guard blocks every
  upgrade. -/
def Properties.NoDeadTimeNeedsItsOtherPremises : Prop :=
  ∃ s, TimedRun wTiming wTimingSys0 wTimingSetup s ∧
    (∃ c, s.sys.chains 0 = some c ∧ c.pv = 1) ∧ s.sys.ctm.ut 1 = 300 ∧
    (s.aux 0).committed = (s.aux 0).executed ∧ (s.aux 0).slVersion = none ∧
    ChainDeadTime wTiming (upd (fun _ => 0) 1 1) s 0 5 ∧
    (¬ ValidSchedule wBadSchedTiming 300 ∧ TimedRun wBadSchedTiming wTimingSys0 wTimingSetup s ∧
      ChainDeadTime wBadSchedTiming (fun _ => 0) s 0 7) ∧
    ∃ s', TimedStep wTiming s (.base (.arbitraryCut 0 1 bgExtra)) s' ∧
      ChainDeadTime wTiming (fun _ => 0) s' 0 25

/-! ## The deadline does not move -/

/-- **A VERSION'S DEADLINE IS FIXED ONCE ITS EDGE IS COMMITTED, IF REPLACEMENTS KEEP IT.** Start
from a state satisfying `CtmInv`. Take any timed run, break-glass cuts included, in which every
replacement pins the same deadline as the transition it replaces (`_requireSameDeadline`). Then
every slot committed at the start is still committed at the end. Whatever the overrides `d`,
`protocolVersionDeadline(v)` returns the same for it at the end, and `protocolVersionIsActive(v)`
holds at the same block times. A commit cannot rewrite a committed slot
(`CommitWritesOnlyEmptySlots`), so with the premise only an owner override moves the
deadline. -/
def Properties.SameDeadlineReplacementsFixTheDeadline : Prop :=
  ∀ (T : TimedConfig) (d : ℕ → ℕ) (s s' : TimedSys) (ls : List TimedLabel),
    CtmInv T.X.W s.sys.ctm → TimedRun T s ls s' → (∀ l ∈ ls, l.KeepsDeadline T) →
    ∀ v, s.sys.ctm.ut v ≠ 0 →
      s'.sys.ctm.ut v ≠ 0 ∧ versionDeadline T d s'.sys.ctm v = versionDeadline T d s.sys.ctm v ∧
      ∀ τ, ProtocolVersionActive T d s'.sys.ctm v τ ↔ ProtocolVersionActive T d s.sys.ctm v τ

/-- **THE PREMISE IS MET, AND IT IS NEEDED.** In the state the run `wTimingSetup` reaches, which
satisfies `CtmInv` and has `300` committed at version 1, `replaceUpgradeTransition(300, 400)`
succeeds:
* under `wTiming`, `400` pins `300`'s deadline `20`, and version 1's deadline stays `20`;
* under `wShortDeadlineTiming`, `400` pins `12`. Both schedules are valid. The model's step,
  which omits `_requireSameDeadline`, still succeeds, and it moves version 1's deadline from
  `20` to `12`: version 1 was active at time `15`, and after the replacement it is not. -/
def Properties.ReplacementDeadlineWitness : Prop :=
  ∃ s s', TimedRun wTiming wTimingSys0 wTimingSetup s ∧ CtmInv wTiming.X.W s.sys.ctm ∧
    s.sys.ctm.ut 1 = 300 ∧
    TimedStep wTiming s (.base (.ctm (.replace 300 400))) s' ∧
    (TimedLabel.base (.ctm (.replace 300 400))).KeepsDeadline wTiming ∧
    versionDeadline wTiming (fun _ => 0) s.sys.ctm 1 = some 20 ∧
    versionDeadline wTiming (fun _ => 0) s'.sys.ctm 1 = some 20 ∧
    TimedRun wShortDeadlineTiming wTimingSys0 wTimingSetup s ∧
    TimedStep wShortDeadlineTiming s (.base (.ctm (.replace 300 400))) s' ∧
    ValidSchedule wShortDeadlineTiming 300 ∧ ValidSchedule wShortDeadlineTiming 400 ∧
    ¬ (TimedLabel.base (.ctm (.replace 300 400))).KeepsDeadline wShortDeadlineTiming ∧
    versionDeadline wShortDeadlineTiming (fun _ => 0) s'.sys.ctm 1 = some 12 ∧
    ProtocolVersionActive wShortDeadlineTiming (fun _ => 0) s.sys.ctm 1 15 ∧
    ¬ ProtocolVersionActive wShortDeadlineTiming (fun _ => 0) s'.sys.ctm 1 15

/-! ## Witness -/

/-- **THE HEADLINE'S PREMISES ARE MET, AND EACH BRANCH OCCURS ALONE.** The fresh witness system
satisfies `SysInv`. Its release `100` lists each selector once, and it has no committed slot.
Every label of the run `wTimingSetup` is no break-glass cut, installs a well-formed release if
it installs one, and commits a transition with a valid schedule if it commits one. At its end,
chain `0` is at version 1 with `300` committed (time `10`, deadline `20`). It has executed every
batch and settles on L1. With no override:
* at time `5` version 1 is active, and no upgrade of the chain succeeds;
* at time `15` version 1 is active, and the chain's admin `3` can upgrade it directly;
* at time `25` version 1 has expired, and the admin can upgrade the chain directly;
* the chain is in dead time at no block time. -/
def Properties.NoDeadTimeWitness : Prop :=
  SysInv wTiming.X.W wTimingSys0.sys ∧ RecordedReleasesWf wTiming.X.W wTimingSys0.sys.ctm ∧
    SlotSchedulesValid wTiming wTimingSys0.sys.ctm ∧
    (∀ l ∈ wTimingSetup,
      ¬ l.isArbitrary ∧ l.InstallsWf wTiming.X.W ∧ l.CommitsValidSchedule wTiming) ∧
    ∃ s, TimedRun wTiming wTimingSys0 wTimingSetup s ∧
      (∃ c, s.sys.chains 0 = some c ∧ c.pv = 1 ∧ s.sys.ctm.ut 1 = 300 ∧
        (s.aux 0).admin = 3 ∧ (s.aux 0).committed = (s.aux 0).executed ∧
        (s.aux 0).slVersion = none) ∧
      (wTiming.sched 300).upgradeTimestamp = 10 ∧ (wTiming.sched 300).deadline = 20 ∧
      (ProtocolVersionActive wTiming (fun _ => 0) s.sys.ctm 1 5 ∧
        ∀ path caller, ¬ ∃ s', TimedStep wTiming s (.upgrade 0 path caller 5) s') ∧
      (ProtocolVersionActive wTiming (fun _ => 0) s.sys.ctm 1 15 ∧
        ∃ s', TimedStep wTiming s (.upgrade 0 (.direct 1) 3 15) s') ∧
      (¬ ProtocolVersionActive wTiming (fun _ => 0) s.sys.ctm 1 25 ∧
        ∃ s', TimedStep wTiming s (.upgrade 0 (.direct 1) 3 25) s') ∧
      ∀ τ, ¬ ChainDeadTime wTiming (fun _ => 0) s 0 τ

end Contracts.ChainTypeManager
