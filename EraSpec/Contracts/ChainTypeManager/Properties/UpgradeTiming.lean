import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTiming

/-!
# Properties: who may upgrade a chain, and when

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTiming`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTiming`.

## The NatSpec of `upgradeChain`, checked

`ICTMUpgradeExecutor.sol:47-54` makes two claims.

* **"The chain's own `upgradeTimestamp` gate does NOT apply here: the chain sees the CTM as
  the caller, and the CTM is exempt from it."** True, reading "the chain's own gate" as
  the `ServerNotifier` schedule, for every chain whose `s.chainTypeManager` is its CTM (a
  model boundary; see the Specs). The executor's call reaches the diamond as a call by the
  CTM (`ExecutorPathIsACtmCallByTheExecutor`, `CtmPathIsADiamondCallByTheCtm`), and whether
  it succeeds, and what it does, does not depend on the notifier at all
  (`ExecutorPathIgnoresNotifier`). The same holds for a direct call by the chain's admin
  (`AdminAndCtmSkipTheNotifier`). Any other caller, which must be a validator, needs the
  chain's entry to be set and reached (`OtherCallersNeedTheNotifier`). Only the chain's
  admin writes that entry, unless the notifier itself is replaced
  (`NotifierWrittenOnlyByItsChainAdmin`).
* **"the OWNER may upgrade any chain at any time; a CHAIN'S OWN ADMIN may upgrade that
  chain at any time".** False. The *manifest's* `upgradeTimestamp` is checked in the engine,
  so it binds every path and every caller (`ManifestTimestampGates`). With a committed edge
  whose timestamp is `10`, nobody can upgrade at time `9`, by any path; at time `10` both the
  owner and the admin can (`NotAtAnyTime`). So "if the owner can upgrade the chain at some
  time, it can at any time" is false, and likewise for the admin
  (`UpgradeChainIsNotTimeIndependent`). The gate is the timestamp of whatever the slot holds
  when the chain upgrades, so replacing the committed transition can close an open gate
  again (`ReplacementMovesTheTimeGate`). Every path also needs every committed batch to be
  executed (`EveryPathNeedsExecutedBatches`) and the settlement layer to have reached the
  target version (`EveryPathNeedsTheSettlementLayerAhead`). What the owner can do at any
  time is a break-glass cut (`executeUpgrade`, through `forward`). That is not
  `upgradeChain`; here it is the untimed `arbitraryCut`.

**The repaired statement** is `UpgradeChainEnabledIffTimed`. `upgradeChain(t, id)` succeeds
exactly when all of these hold, whatever the notifier says:
* the caller is the executor's owner or the chain's admin;
* `t` is committed at its own `oldProtocolVersion()`, and the executor owns the CTM;
* the chain is at that version;
* the block time is at least `t`'s `upgradeTimestamp`;
* every committed batch is executed;
* the settlement layer, if the chain settles elsewhere, is at `t`'s target version or later;
* the routing transition itself is enabled.

Once enabled it stays enabled as time passes (`UpgradeStaysEnabledLater`). In the source
these conditions are necessary but not sufficient, because the model omits further
reject-only checks (see the Specs).

## The model is conservative

A timed upgrade is `ChainRouting`'s transition (`UpgradeIsATransition`), and a timed run is
a `ChainRouting` run (`TimedRunIsARun`), so the routing headline holds along timed runs
(`TimedRunKeepsChainsOnTheirRelease`). An executor upgrade is `ExecutorForward`'s
`upgradeChain` step (`TimedUpgradeChainIsAnXStep`).

## The deadline

`ValidEdgeHasNoDeadTime` is arithmetic on the deadline getter, for an arbitrary CTM state,
reachable or not. Suppose the schedule in slot `v` passed `requireValidEdge` and the owner has
not overridden `v`'s deadline. Then at every instant `protocolVersionIsActive(v)` holds or the
manifest's time gate of the edge is open. That gate is one of the conditions of an upgrade
(`UpgradeChainEnabledIffTimed`), so this alone does not say that chains at `v` can cross the
edge. An override can close both at once (`DeadlineOverrideOpensDeadTime`).

The statement about the system is in `UpgradeTimingStrong`. Every reachable slot has a valid
schedule, given that every committed and replacement transition passed `requireValidEdge`, as
every `CTMTransition` does (`ReachableSlotsHaveValidSchedules`). Along validated timed runs, take a chain at a
version with a committed edge, with every batch executed and its settlement layer at the
target version. It is never in dead time: at every instant its version is active, or its admin
and the CTM's owner can upgrade it (`ValidatedTimedRunsHaveNoDeadTime`). Without those two
gates a valid schedule does leave dead time (`ValidScheduleAloneLeavesDeadTime`).

## Witnesses

`EachGateIsLoadBearing` shows each gate deciding a concrete step in both directions.
`UpgradeTimingWitness` is a run from a fresh CTM that upgrades three chains, one through
each entry point.
-/

namespace Contracts.ChainTypeManager

/-! ## The timed model refines the untimed one -/

/-- **A TIMED UPGRADE IS A TRANSITION.** Whatever the path, the caller and the time, a
successful upgrade relates the routing system exactly as `ChainRouting`'s transition step
does, and writes neither the chains' `DiamondAux` nor the notifier. -/
def Properties.UpgradeIsATransition : Prop :=
  ∀ (T : TimedConfig) (s s' : TimedSys) (id : ChainId) (path : UpgradePath) (caller : Address)
    (τ : ℕ), TimedStep T s (.upgrade id path caller τ) s' →
    Step T.X.W s.sys (.transition id) s'.sys ∧ s'.aux = s.aux ∧ s'.notifier = s.notifier

/-- **A TIMED RUN IS A ROUTING RUN.** Forgetting callers, times, the notifier and each chain's
`DiamondAux`, every timed run is a `ChainRouting` run of the labels' untimed images. -/
def Properties.TimedRunIsARun : Prop :=
  ∀ (T : TimedConfig) (s s' : TimedSys) (ls : List TimedLabel), TimedRun T s ls s' →
    Run T.X.W s.sys (ls.flatMap TimedLabel.untimed) s'.sys

/-- **THE ROUTING HEADLINE ALONG TIMED RUNS.** As `ChainsRunTheirVersionsRelease`: along any
timed run from an invariant state with no break-glass cut, every chain at a version `v` with
a release `R_v` routes exactly `R_v`, and `R_v` is a release of version `v`. -/
def Properties.TimedRunKeepsChainsOnTheirRelease : Prop :=
  ∀ (T : TimedConfig) (s s' : TimedSys) (ls : List TimedLabel), SysInv T.X.W s.sys →
    TimedRun T s ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.sys.chains id = some c → s'.sys.ctm.relAt c.pv ≠ 0 →
      T.X.W.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (T.X.W.relRows (s'.sys.ctm.relAt c.pv))

/-- **AN EXECUTOR UPGRADE IS `ExecutorForward`'S `upgradeChain` STEP**, whatever the
implementations behind the CTM domain's proxies. -/
def Properties.TimedUpgradeChainIsAnXStep : Prop :=
  ∀ (T : TimedConfig) (s s' : TimedSys) (id : ChainId) (t caller : Address) (τ : ℕ)
    (impl : ProxyUpgradeCurrent.Impl),
    TimedStep T s (.upgrade id (.executor t) caller τ) s' →
    XStep T.X ⟨s.sys, impl⟩ (.upgradeChain id) ⟨s'.sys, impl⟩

/-! ## The chain sees the CTM as the caller -/

/-- **THE CTM'S ENTRY POINT IS A DIAMOND CALL BY THE CTM.** `upgradeChainFromVersion(id, v)`
on the CTM succeeds exactly when its caller is the CTM's owner and a direct call of the
diamond by the CTM's address succeeds, with the same effect. -/
def Properties.CtmPathIsADiamondCallByTheCtm : Prop :=
  ∀ (T : TimedConfig) (s s' : TimedSys) (id : ChainId) (v : ℕ) (caller : Address) (τ : ℕ),
    TimedStep T s (.upgrade id (.ctm v) caller τ) s' ↔
      caller = T.ctmOwner ∧ TimedStep T s (.upgrade id (.direct v) T.X.ctmProxy τ) s'

/-- **THE EXECUTOR'S `upgradeChain` IS A CTM CALL BY THE EXECUTOR.** `upgradeChain(t, id)`
succeeds exactly when its caller is the executor's owner or the chain's admin, `t` is the
transition committed at `t.oldProtocolVersion()`, and the CTM's
`upgradeChainFromVersion(id, t.oldProtocolVersion())` called by the executor succeeds, with
the same effect. -/
def Properties.ExecutorPathIsACtmCallByTheExecutor : Prop :=
  ∀ (T : TimedConfig) (s s' : TimedSys) (id : ChainId) (t caller : Address) (τ : ℕ),
    TimedStep T s (.upgrade id (.executor t) caller τ) s' ↔
      (caller = T.execOwner ∨ caller = (s.aux id).admin) ∧
      s.sys.ctm.ut (T.X.W.tr t).old = t ∧
      TimedStep T s (.upgrade id (.ctm (T.X.W.tr t).old) T.X.rc.self τ) s'

/-- **THE EXECUTOR PATH IGNORES THE NOTIFIER** (`ICTMUpgradeExecutor.sol:53-54`). Replacing
the `ServerNotifier`'s whole schedule by any `n` changes neither which `upgradeChain` calls
succeed nor what they do. -/
def Properties.ExecutorPathIgnoresNotifier : Prop :=
  ∀ (T : TimedConfig) (s : TimedSys) (id : ChainId) (t caller : Address) (τ : ℕ)
    (n : ChainId → ℕ → ℕ),
    (∀ sys' : Sys, TimedStep T s (.upgrade id (.executor t) caller τ) { s with sys := sys' } ↔
      TimedStep T { s with notifier := n } (.upgrade id (.executor t) caller τ)
        { s with notifier := n, sys := sys' }) ∧
    ((∃ s', TimedStep T s (.upgrade id (.executor t) caller τ) s') ↔
      ∃ s', TimedStep T { s with notifier := n } (.upgrade id (.executor t) caller τ) s')

/-! ## The chain's own schedule -/

/-- **THE CHAIN'S ADMIN AND ITS CTM SKIP THE CHAIN'S OWN SCHEDULE.** For a direct call by
either, replacing the notifier's schedule changes nothing (`Admin.sol:546`). -/
def Properties.AdminAndCtmSkipTheNotifier : Prop :=
  ∀ (T : TimedConfig) (s : TimedSys) (id : ChainId) (v : ℕ) (caller : Address) (τ : ℕ)
    (n : ChainId → ℕ → ℕ) (sys' : Sys),
    (caller = (s.aux id).admin ∨ caller = T.X.ctmProxy) →
    (TimedStep T s (.upgrade id (.direct v) caller τ) { s with sys := sys' } ↔
      TimedStep T { s with notifier := n } (.upgrade id (.direct v) caller τ)
        { s with notifier := n, sys := sys' })

/-- **EVERY OTHER CALLER NEEDS THE CHAIN'S OWN SCHEDULE.** A direct upgrade by a caller that
is neither the chain's admin nor its CTM is by one of the chain's validators, and only once
the notifier's entry for the chain and the departing version is set and reached
(`Admin.sol:546-554`). -/
def Properties.OtherCallersNeedTheNotifier : Prop :=
  ∀ (T : TimedConfig) (s s' : TimedSys) (id : ChainId) (v : ℕ) (caller : Address) (τ : ℕ),
    TimedStep T s (.upgrade id (.direct v) caller τ) s' →
    caller ≠ (s.aux id).admin → caller ≠ T.X.ctmProxy →
    (s.aux id).validators caller = true ∧ s.notifier id v ≠ 0 ∧ s.notifier id v ≤ τ

/-- **ONLY THE CHAIN'S ADMIN SCHEDULES ITS VALIDATORS' UPGRADES.** A step that changes the
notifier's entry for chain `id` and version `v` is either the admin of `id` setting it, to a
nonzero time, while `id` is at `v` (`ServerNotifier.sol:113-131`), or a replacement of the
whole notifier. -/
def Properties.NotifierWrittenOnlyByItsChainAdmin : Prop :=
  ∀ (T : TimedConfig) (s s' : TimedSys) (l : TimedLabel) (id : ChainId) (v : ℕ),
    TimedStep T s l s' → s'.notifier id v ≠ s.notifier id v →
    (∃ caller ts c, l = .setUpgradeTimestamp id caller ts ∧ caller = (s.aux id).admin ∧
      s.sys.chains id = some c ∧ c.pv = v ∧ ts ≠ 0 ∧ s'.notifier id v = ts) ∨
    ∃ n, l = .swapNotifier n

/-! ## The engine's gates bind every path -/

/-- **THE MANIFEST'S TIMESTAMP GATES EVERY UPGRADE.** Whatever the path and the caller, a
chain at version `v` that is upgraded at time `τ` has `τ` at least the `upgradeTimestamp` of
the transition committed at `v` (`BaseZkSyncUpgrade.sol:76-78`). -/
def Properties.ManifestTimestampGates : Prop :=
  ∀ (T : TimedConfig) (s s' : TimedSys) (id : ChainId) (path : UpgradePath) (caller : Address)
    (τ : ℕ), TimedStep T s (.upgrade id path caller τ) s' →
    ∃ c, s.sys.chains id = some c ∧ (T.sched (s.sys.ctm.ut c.pv)).upgradeTimestamp ≤ τ

/-- **EVERY PATH NEEDS EVERY COMMITTED BATCH EXECUTED** (`DefaultUpgrade.sol:31`). -/
def Properties.EveryPathNeedsExecutedBatches : Prop :=
  ∀ (T : TimedConfig) (s s' : TimedSys) (id : ChainId) (path : UpgradePath) (caller : Address)
    (τ : ℕ), TimedStep T s (.upgrade id path caller τ) s' →
    (s.aux id).committed = (s.aux id).executed

/-- **EVERY PATH NEEDS THE SETTLEMENT LAYER AHEAD.** A chain that settles on a layer at version
`w` can only be upgraded to a version at most `w` (`BaseZkSyncUpgrade.sol:83-88`). -/
def Properties.EveryPathNeedsTheSettlementLayerAhead : Prop :=
  ∀ (T : TimedConfig) (s s' : TimedSys) (id : ChainId) (path : UpgradePath) (caller : Address)
    (τ w : ℕ), TimedStep T s (.upgrade id path caller τ) s' → (s.aux id).slVersion = some w →
    ∃ c, s.sys.chains id = some c ∧ (s.sys.edge T.X.W c.pv).new ≤ w

/-- **WAITING NEVER HURTS.** An upgrade that succeeds at time `τ` succeeds, with the same
effect, at every later time from the same state: both time gates are lower bounds. -/
def Properties.UpgradeStaysEnabledLater : Prop :=
  ∀ (T : TimedConfig) (s s' : TimedSys) (id : ChainId) (path : UpgradePath) (caller : Address)
    (τ τ' : ℕ), TimedStep T s (.upgrade id path caller τ) s' → τ ≤ τ' →
    TimedStep T s (.upgrade id path caller τ') s'

/-! ## The repaired NatSpec -/

/-- **EXACTLY WHEN `upgradeChain` SUCCEEDS.** `upgradeChain(t, id)` by `caller` at time `τ`
succeeds if and only if:
* the caller is the executor's owner or the chain's admin;
* `t` is committed at `t.oldProtocolVersion()`;
* the executor owns the CTM;
* the chain is at `t.oldProtocolVersion()`;
* `τ` is at least `t`'s `upgradeTimestamp`;
* every committed batch is executed;
* a settlement layer the chain settles on is at `t.newProtocolVersion()` or later;
* `ChainRouting`'s transition step for the chain is enabled.

The notifier does not appear. -/
def Properties.UpgradeChainEnabledIffTimed : Prop :=
  ∀ (T : TimedConfig) (s : TimedSys) (id : ChainId) (t caller : Address) (τ : ℕ),
    (∃ s', TimedStep T s (.upgrade id (.executor t) caller τ) s') ↔
      ((caller = T.execOwner ∨ caller = (s.aux id).admin) ∧
        s.sys.ctm.ut (T.X.W.tr t).old = t ∧ T.X.rc.self = T.ctmOwner ∧
        (∃ c, s.sys.chains id = some c ∧ c.pv = (T.X.W.tr t).old) ∧
        (T.sched t).upgradeTimestamp ≤ τ ∧
        (s.aux id).committed = (s.aux id).executed ∧
        (∀ w, (s.aux id).slVersion = some w → (T.X.W.tr t).new ≤ w) ∧
        ∃ sys', Step T.X.W s.sys (.transition id) sys')

/-! ## Not at any time -/

/-- **NOBODY CAN UPGRADE BEFORE THE MANIFEST'S TIME** (refutes `ICTMUpgradeExecutor.sol:48-49`).
From a fresh CTM: chain `0` is created at version 1 with admin `3`, the CTM commits `300`
(1→2) whose `upgradeTimestamp` is `10`, and the admin sets the chain's own upgrade time to
`12`. At time `9`, neither the executor's owner `2` nor the chain's admin `3` can upgrade
chain `0` through `upgradeChain`, whatever transition they name, and nobody can upgrade it
by any path. At time `10`, both can, through `upgradeChain(300, 0)`. -/
def Properties.NotAtAnyTime : Prop :=
  ∃ s, TimedRun wTiming wTimingSys0 wTimingSetup s ∧
    s.sys.ctm.ut 1 = 300 ∧ (wTiming.sched 300).upgradeTimestamp = 10 ∧
    (∃ c, s.sys.chains 0 = some c ∧ c.pv = 1) ∧ wTiming.execOwner = 2 ∧ (s.aux 0).admin = 3 ∧
    (∀ t, ¬ ∃ s', TimedStep wTiming s (.upgrade 0 (.executor t) 2 9) s') ∧
    (∀ t, ¬ ∃ s', TimedStep wTiming s (.upgrade 0 (.executor t) 3 9) s') ∧
    (∀ path caller, ¬ ∃ s', TimedStep wTiming s (.upgrade 0 path caller 9) s') ∧
    (∃ s', TimedStep wTiming s (.upgrade 0 (.executor 300) 2 10) s') ∧
    (∃ s', TimedStep wTiming s (.upgrade 0 (.executor 300) 3 10) s')

/-- **"AT ANY TIME" IS FALSE, FOR THE OWNER AND FOR THE CHAIN'S ADMIN.** It is not the case that
whenever the executor's owner can upgrade a chain through `upgradeChain` at some time, it can
at every time. The same fails for the chain's own admin. -/
def Properties.UpgradeChainIsNotTimeIndependent : Prop :=
  (¬ ∀ (T : TimedConfig) (s : TimedSys) (id : ChainId) (t : Address) (τ τ' : ℕ),
      (∃ s', TimedStep T s (.upgrade id (.executor t) T.execOwner τ) s') →
      ∃ s', TimedStep T s (.upgrade id (.executor t) T.execOwner τ') s') ∧
  ¬ ∀ (T : TimedConfig) (s : TimedSys) (id : ChainId) (t : Address) (τ τ' : ℕ),
      (∃ s', TimedStep T s (.upgrade id (.executor t) (s.aux id).admin τ) s') →
      ∃ s', TimedStep T s (.upgrade id (.executor t) (s.aux id).admin τ') s'

/-- **THE TIME GATE FOLLOWS THE SLOT, AND A REPLACEMENT CAN CLOSE IT AGAIN.** A replacement
must keep the departing version's deadline (`ChainTypeManager.sol:488-494`) but not the upgrade
timestamp, and the engine reads the timestamp of whatever the slot holds when the chain
upgrades. In the state of `NotAtAnyTime`, the owner can upgrade chain `0` through `300` at time
`12`. `replaceUpgradeTransition(300, 400)` succeeds; `400` has a valid schedule, the same
deadline, and upgrade time `15`. After it nobody can upgrade chain `0` at `12`, by any path,
and the owner can through `400` at `15`. -/
def Properties.ReplacementMovesTheTimeGate : Prop :=
  ∃ s s', TimedRun wTiming wTimingSys0 wTimingSetup s ∧
    TimedStep wTiming s (.base (.ctm (.replace 300 400))) s' ∧
    ValidSchedule wTiming 300 ∧ ValidSchedule wTiming 400 ∧
    (wTiming.sched 400).deadline = (wTiming.sched 300).deadline ∧
    (∃ s'', TimedStep wTiming s (.upgrade 0 (.executor 300) 2 12) s'') ∧
    (∀ path caller, ¬ ∃ s'', TimedStep wTiming s' (.upgrade 0 path caller 12) s'') ∧
    (∃ s'', TimedStep wTiming s' (.upgrade 0 (.executor 400) 2 15) s'')

/-! ## The departing version's deadline -/

/-- **A VALID SCHEDULE LEAVES NO GAP BETWEEN ITS TWO TIME WINDOWS.** This is a fact about the
`protocolVersionDeadline` getter (`versionDeadline`) for an arbitrary CTM state `s`, reachable
or not. Take the transition in slot `v`. Suppose its schedule passed `requireValidEdge` and the
owner has not overridden `v`'s deadline. Then:
* at every instant, `protocolVersionIsActive(v)` holds, or the manifest's time gate of the edge
  is open;
* at the upgrade timestamp itself, both hold.

The time gate is one of the conditions of an upgrade (`UpgradeChainEnabledIffTimed`). So this
does not say that an upgrade step exists, or that a reachable slot has a valid schedule. Those
are `ValidatedTimedRunsHaveNoDeadTime` and `ReachableSlotsHaveValidSchedules`
(`UpgradeTimingStrong`).
-/
def Properties.ValidEdgeHasNoDeadTime : Prop :=
  ∀ (T : TimedConfig) (d : ℕ → ℕ) (s : CTM) (v τ : ℕ), s.ut v ≠ 0 → d v = 0 →
    ValidSchedule T (s.ut v) →
    (ProtocolVersionActive T d s v τ ∨ (T.sched (s.ut v)).upgradeTimestamp ≤ τ) ∧
    ProtocolVersionActive T d s v (T.sched (s.ut v)).upgradeTimestamp

/-- **AN OVERRIDDEN DEADLINE CAN OPEN DEAD TIME.** On the witness CTM after committing `300`,
whose schedule is valid (time `10`, deadline `20`):
* without an override, at every instant version 1 is active or the edge's time gate is open;
* after `setProtocolVersionDeadline(1, 1)`, at time `5` chains at version 1 can no longer
  commit batches, and the edge's time gate is still closed, so they cannot yet cross the edge.

The same override on a reachable timed state, with every upgrade step ruled out, is in
`NoDeadTimeNeedsItsOtherPremises` (`UpgradeTimingStrong`).
-/
def Properties.DeadlineOverrideOpensDeadTime : Prop :=
  ∃ s, CRun wWorld (initState wWorld 100) [.commit 300] s ∧ s.ut 1 = 300 ∧
    ValidSchedule wTiming 300 ∧
    (∀ τ, ProtocolVersionActive wTiming (fun _ => 0) s 1 τ ∨
      (wTiming.sched 300).upgradeTimestamp ≤ τ) ∧
    ¬ ProtocolVersionActive wTiming (upd (fun _ => 0) 1 1) s 1 5 ∧
    5 < (wTiming.sched 300).upgradeTimestamp

/-! ## Witnesses -/

/-- **EACH GATE DECIDES A STEP.** In the state of `NotAtAnyTime` (chain `0` at version 1,
admin `3`, validator `4`, CTM `8`, the chain's own entry `12`, the manifest's time `10`):
* the chain's own schedule binds the validator: no direct upgrade by `4` at `11`, one at
  `12`, and none at `12` once the notifier's schedule is empty;
* it binds neither the executor's call nor the admin's: both succeed at `11`;
* an unexecuted batch blocks every path at every time;
* a settlement layer at version `1` (behind the target `2`) blocks every path; one at `2`
  does not.

Each modified state is one `setAux` or `swapNotifier` step away. -/
def Properties.EachGateIsLoadBearing : Prop :=
  ∃ s, TimedRun wTiming wTimingSys0 wTimingSetup s ∧
    (s.aux 0).admin = 3 ∧ (s.aux 0).validators 4 = true ∧ wTiming.X.ctmProxy = 8 ∧
    s.notifier 0 1 = 12 ∧
    (¬ ∃ s', TimedStep wTiming s (.upgrade 0 (.direct 1) 4 11) s') ∧
    (∃ s', TimedStep wTiming s (.upgrade 0 (.direct 1) 4 12) s') ∧
    (¬ ∃ s', TimedStep wTiming { s with notifier := fun _ _ => 0 }
      (.upgrade 0 (.direct 1) 4 12) s') ∧
    (∃ s', TimedStep wTiming s (.upgrade 0 (.executor 300) 2 11) s') ∧
    (∃ s', TimedStep wTiming s (.upgrade 0 (.direct 1) 3 11) s') ∧
    (∀ path caller τ, ¬ ∃ s', TimedStep wTiming
      { s with aux := upd s.aux 0 { wTimingAux with committed := 1 } }
      (.upgrade 0 path caller τ) s') ∧
    (∀ path caller τ, ¬ ∃ s', TimedStep wTiming
      { s with aux := upd s.aux 0 { wTimingAux with slVersion := some 1 } }
      (.upgrade 0 path caller τ) s') ∧
    (∃ s', TimedStep wTiming { s with aux := upd s.aux 0 { wTimingAux with slVersion := some 2 } }
      (.upgrade 0 (.executor 300) 2 10) s')

/-- **THE PREMISES ARE MET BY A REAL RUN.** From the fresh witness system, which satisfies
`SysInv`, the run `wTimingRun` has no break-glass cut. It upgrades:
* chain `0` through `upgradeChain` by its admin;
* chain `1` through the CTM's entry point called by the executor;
* chain `2` directly by its validator, at the time chain `2`'s admin scheduled.

Along it the notifier's entry for chain `2` and version 1 changes from `0` to `12`. All three
chains end at version 2 on release `200`, the CTM's release of version 2. -/
def Properties.UpgradeTimingWitness : Prop :=
  SysInv wTiming.X.W wTimingSys0.sys ∧ (∀ l ∈ wTimingRun, ¬ l.isArbitrary) ∧
    ∃ s, TimedRun wTiming wTimingSys0 wTimingRun s ∧
      wTimingSys0.notifier 2 1 = 0 ∧ s.notifier 2 1 = 12 ∧ s.sys.ctm.relAt 2 = 200 ∧
      ∀ id, id ≤ 2 → ∃ c, s.sys.chains id = some c ∧ c.pv = 2 ∧
        c.routing = rowsRouting (wRows 200)

end Contracts.ChainTypeManager
