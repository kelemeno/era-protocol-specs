import EraSpec.Contracts.ChainTypeManager.Specs.ExecutorForward

/-!
# Model: who may upgrade a chain, and when

Source: branch `feat/upgrade-simplification` of the zksync-era `contracts` repository at
commit `e561b9cc2` (2026-10-19), as for the rest of this folder. The branch moves; every
`file:line` below is at that commit. Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.UpgradeTiming` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTiming`.

## Why this is modelled

`ChainRouting`'s `Step.transition` leaves out the caller, the block time and every check
that only rejects. The executor's `upgradeChain` documents exactly those
(`upgrades/registry/executors/ICTMUpgradeExecutor.sol:47-54`):

    /// @dev Callers:
    ///      - the OWNER may upgrade any chain at any time;
    ///      - a CHAIN'S OWN ADMIN may upgrade that chain at any time — upgrading is the chain's
    ///        decision to make, ...
    ///      The chain's own `upgradeTimestamp` gate does NOT apply here: the chain sees the CTM as
    ///      the caller, and the CTM is exempt from it.

This file adds the caller, the block time `τ`, the `ServerNotifier`'s per-chain schedule
and the engine's reject-only checks to the transition step, so that those sentences can be
stated and checked.

## Three ways to upgrade a chain

1. **Directly.** Anyone calls the diamond's `Admin.upgradeChainFromVersion(_, v)`
   (`state-transition/chain-deps/facets/Admin.sol:528-559`); the modifier admits the chain's
   admin, its CTM and its validators (`onlyAdminOrChainTypeManagerOrValidator`,
   `state-transition/chain-deps/facets/ZKChainBase.sol:126-131`).
2. **Through the CTM.** The CTM's owner calls
   `ChainTypeManager.upgradeChainFromVersion(id, v)`
   (`state-transition/ChainTypeManager.sol:623-626`, `onlyOwner`), which calls the diamond,
   so the diamond sees `msg.sender` = the CTM. The
   executor's `forward` of that call is this path with the executor as caller.
3. **Through the executor.** `CTMUpgradeExecutor.upgradeChain(t, id)`
   (`upgrades/registry/executors/CTMUpgradeExecutor.sol:87-102`):

        if (msg.sender != owner() && msg.sender != CHAIN_TYPE_MANAGER.getChainAdmin(_chainId)) {
            revert Unauthorized(msg.sender); }                                           // :88-90
        uint256 oldProtocolVersion = _transition.oldProtocolVersion();                  // :91
        address committed = CHAIN_TYPE_MANAGER.upgradeTransition(oldProtocolVersion);   // :94
        if (committed != address(_transition)) { revert TransitionNotCommitted(...); }  // :95-97
        CHAIN_TYPE_MANAGER.upgradeChainFromVersion(_chainId, oldProtocolVersion);       // :100

   `getChainAdmin` is the diamond's `getAdmin()` (`ChainTypeManager.sol:265-267`), i.e.
   `s.admin`. The CTM call is path 2 with the executor as the CTM's caller.

## What the diamond checks

`Admin.upgradeChainFromVersion` (`Admin.sol:528-559`):

    Diamond.DiamondCutData memory diamondCut = IChainTypeManager(s.chainTypeManager).upgradeCutForVersion(
        _oldProtocolVersion);                                                         // :535-537
    if (s.protocolVersion != _oldProtocolVersion) { revert ProtocolIdMismatch(...); } // :539-541
    if (msg.sender != s.admin && msg.sender != s.chainTypeManager) {                  // :546
        IServerNotifier serverNotifier = IServerNotifier(
            IChainTypeManager(s.chainTypeManager).serverNotifierAddress());           // :547-549
        uint256 timestamp = serverNotifier.protocolVersionToUpgradeTimestamp(s.chainId, _oldProtocolVersion); // :550
        if (timestamp == 0 || block.timestamp < timestamp) {
            revert UpgradeTimestampNotReached(timestamp, block.timestamp); }          // :551-553
    }
    _executeDiamondCut(diamondCut);                                                   // :555
    if (s.protocolVersion <= _oldProtocolVersion) { revert ProtocolIdNotGreater(); }  // :556-558

The cut's init is the transition's engine running `DefaultUpgrade.upgradeFromTransition`
(`upgrades/DefaultUpgrade.sol:30-44`), which first requires every committed batch to be
executed (`_requireAllBatchesExecuted()`, :31, defined at `upgrades/BaseZkSyncUpgrade.sol:109-113`:
`if (s.totalBatchesCommitted != s.totalBatchesExecuted) { revert NotAllBatchesExecuted(); }`),
then runs the routing guard and the derived cuts (`ChainRouting`), and then
`_upgradeFromCommittedObject` (:66-85), which reads
`(newProtocolVersion, upgradeTimestamp, newRelease) = _object.upgradeTarget()` (:67) and
passes `_upgradeTimestamp: upgradeTimestamp` (:75) to `BaseZkSyncUpgrade._upgrade`
(`BaseZkSyncUpgrade.sol:66-102`):

    if (block.timestamp < _upgradeTimestamp) { revert TimeNotReached(...); }          // :76-78
    bool isOnSettlementLayer = s.settlementLayer == address(0);                       // :81
    if (!isOnSettlementLayer) {
        require(_newProtocolVersion <= IZKChain(s.settlementLayer).getProtocolVersion(),
            SettlementLayerUpgradeMustPrecedeChainUpgrade()); }                       // :83-88

## Two gates, both called `upgradeTimestamp`

* **The manifest's.** `CTMTransition.upgradeTarget()` returns the manifest's
  `upgradeTimestamp` (`upgrades/registry/objects/CTMTransition.sol:197-205`), "The earliest a
  chain may execute its own diamond upgrade" (`upgrades/registry/RegistryTypes.sol:139`). It
  is checked in the engine, so it applies to **every** path and caller.
* **The chain's own.** `ServerNotifier.protocolVersionToUpgradeTimestamp[chainId][v]`
  (`governance/ServerNotifier.sol:32-34`), set by the chain's admin with
  `setUpgradeTimestamp` (:113-131). It is checked in `Admin.sol:546-554` and is skipped
  when the caller is the chain's admin or its CTM.

## The schedule's deadline

The manifest also pins `oldProtocolVersionDeadline` (`CTMTransition.sol:65`, getter :193-195).
It does not gate upgrades. It gates batch commits on the departing version: the committer
requires `protocolVersionIsActive(s.protocolVersion)`
(`state-transition/chain-deps/facets/Committer.sol:85-87`), which is
`block.timestamp <= protocolVersionDeadline(v)` (`ChainTypeManager.sol:575-577`), resolved at
:550-563. Every `CTMTransition` constructor runs `VersionEdgeLib.requireValidEdge`
(`CTMTransition.sol:91-97`), which refuses a zero deadline and a deadline before the upgrade
timestamp (`upgrades/registry/libraries/VersionEdgeLib.sol:55-62`). A replacement must keep
the deadline (`_requireSameDeadline`, `ChainTypeManager.sol:488-494`) but may change the
upgrade timestamp. The owner may override the deadline with any nonzero value
(`setProtocolVersionDeadline`, :568-571; "a past one expires the version immediately", :567).

## Modelling choices

* **A revert is the absence of a step**, as in the rest of this folder.
* **The routing part is `ChainRouting`'s `Step.transition`, unchanged.** A timed upgrade
  step is that step plus the gates above (`DiamondUpgrade`). So every timed upgrade is an
  untimed transition, and every routing result carries over.
* **Transition schedules are getters** (`TimedConfig.sched`): `upgradeTimestamp()` and
  `oldProtocolVersionDeadline()` of the object at each address, fixed because the object is
  write-once (`CTMTransition.sol:48-49`). `ValidSchedule` is what the constructor's
  `requireValidEdge` establishes; it is a premise only where a result needs it. Neither it nor
  the same-deadline check of a replacement (`_requireSameDeadline`, `ChainTypeManager.sol:488-494`)
  is a condition of `CStep`, so the model's commit and replacement steps admit a transition
  with any schedule. `Specs/UpgradeTimingStrong.lean` states both as premises on a run's labels
  (`Op.CommitsValidSchedule`, `Op.KeepsDeadline`).
* **`s.chainTypeManager` is this CTM for every chain.** `DiamondInit.initialize` sets
  `s.chainTypeManager = msg.sender` (`state-transition/chain-deps/DiamondInit.sol:91`), and the
  CTM is the deployer (`ChainTypeManager.sol:693`), so `msg.sender` is the CTM. A source search
  at this commit finds no other writer. Code an engine or a break-glass init delegatecalls
  could rewrite it; such a chain reads its cut and its notifier from another contract and is
  a chain of another CTM, which `ChainRouting` already leaves out. This identification is
  what the exemption of the CTM rests on.
* **One `ServerNotifier`**, the one the CTM points at (`serverNotifierAddress`,
  `ChainTypeManager.sol:128`). Its only writer is `setUpgradeTimestamp`. The CTM owner can
  repoint the CTM at another notifier (`setServerNotifier`, :392-396), and the notifier's
  implementation can be swapped. Both are `TimedLabel.swapNotifier`, which installs an
  arbitrary schedule. The notifier's `chainTypeManager` is assumed to be this CTM.
  `upgradePreconditionChecker` (`ServerNotifier.sol:126-129`) only rejects and is omitted.
* **The rest of the diamond's state that the gates read** (`DiamondAux`): `s.admin`,
  `s.validators`, the two batch counters, and the settlement layer's version. Its writers
  are the chain's own operations (`acceptAdmin`, `Admin.sol:127-140`; the CTM's
  `setValidator`, `Admin.sol:143-146`; batch commit, execute and revert; migration,
  `Migrator.sol:238-240`), `DiamondInit` at creation (`DiamondInit.sol:119-120`), and code a
  break-glass init delegatecalls. The model makes no claim about any of them:
  `TimedLabel.setAux` rewrites a chain's `DiamondAux` arbitrarily, at any time. Genesis and
  migration in leave it unchanged, and what `DiamondInit` and the migration write is a
  `setAux` right after them. So every run of the source is a run of the model with such
  steps inserted.
* **The settlement layer's version** is `slVersion`: `none` when the diamond is on its
  settlement layer (`s.settlementLayer == address(0)`), otherwise what
  `IZKChain(s.settlementLayer).getProtocolVersion()` returns. It is another chain's state,
  read at call time; `setAux` may move it.
* **The two owners are fixed configuration**, as in `ExecutorForward`: `ctmOwner` is
  `CHAIN_TYPE_MANAGER.owner()` and `execOwner` is the executor's own `owner()`
  (`governance/UpgradeExecutorBase.sol:20-29`). The executor is `X.rc.self`, the CTM's address
  `X.ctmProxy`.
* **Block times** are labels' arguments. Nothing orders them along a run (a run may go
  back in time), which only adds runs.
* **Omitted reject-only checks**, so that enabledness results here give conditions the
  source also needs, not all it needs: the release's verifier being nonzero
  (`DefaultUpgrade.sol:68-72`), the L2 upgrade transaction's checks and the previous L2
  upgrade being finalized (`BaseZkSyncUpgrade.sol:148-188, 245-254`), the version's
  semver shape (:213-238), and the precondition checker.
* **Only registry transitions are timed.** Crossing the bootstrap edge runs pre-registry
  facets and is `ChainRouting`'s untimed `bootstrapReset`; a break-glass cut is untimed
  `arbitraryCut`.
-/

namespace Contracts.ChainTypeManager

/-! ## Configuration -/

/-- The schedule getters of a transition object. -/
structure TransitionSchedule where
  /-- `upgradeTimestamp()`, which is also the second component of `upgradeTarget()`
  (`CTMTransition.sol:197-205`): "The earliest a chain may execute its own diamond upgrade"
  (`RegistryTypes.sol:139`). -/
  upgradeTimestamp : ℕ
  /-- `oldProtocolVersionDeadline()` (`CTMTransition.sol:193-195`): "When the departing
  version stops being usable" (`RegistryTypes.sol:138`). -/
  deadline : ℕ

/-- The timed model's configuration. -/
structure TimedConfig where
  /-- The executor configuration of `ExecutorForward`: the deployed objects `X.W`, the
  executor `X.rc.self`, and the CTM's own address `X.ctmProxy`. -/
  X : XConfig
  /-- Each transition object's schedule getters. -/
  sched : Address → TransitionSchedule
  /-- `CHAIN_TYPE_MANAGER.owner()`. -/
  ctmOwner : Address
  /-- The executor's own `owner()`. -/
  execOwner : Address

/-- What `VersionEdgeLib.requireValidEdge` checks of a schedule (`VersionEdgeLib.sol:55-62`),
which every `CTMTransition` constructor runs (`CTMTransition.sol:91-97`):

    if (_oldVersionDeadline == 0) { revert TransitionDeadlineZero(); }
    if (_oldVersionDeadline < _upgradeTimestamp) { revert TransitionDeadlineBeforeUpgrade(...); }
-/
def ValidSchedule (T : TimedConfig) (t : Address) : Prop :=
  (T.sched t).deadline ≠ 0 ∧ (T.sched t).upgradeTimestamp ≤ (T.sched t).deadline

/-! ## State -/

/-- The part of a chain diamond's storage that the upgrade gates read, besides the version
and the routing. -/
structure DiamondAux where
  /-- `s.admin`. -/
  admin : Address
  /-- `s.validators`. -/
  validators : Address → Bool
  /-- `s.totalBatchesCommitted`. -/
  committed : ℕ
  /-- `s.totalBatchesExecuted`. -/
  executed : ℕ
  /-- `none` when the diamond is on its settlement layer; otherwise the protocol version of
  the settlement layer's diamond. -/
  slVersion : Option ℕ

/-- The CTM and its chains, each chain's `DiamondAux`, and the `ServerNotifier`'s schedule. -/
structure TimedSys where
  /-- The CTM's version state and the chains' versions and routing. -/
  sys : Sys
  /-- Each chain's `DiamondAux`; meaningful where a chain is registered. -/
  aux : ChainId → DiamondAux
  /-- `ServerNotifier.protocolVersionToUpgradeTimestamp[chainId][oldProtocolVersion]`;
  zero where nothing is set. -/
  notifier : ChainId → ℕ → ℕ

/-- Write one entry of the notifier's schedule. -/
def setNotifierEntry (n : ChainId → ℕ → ℕ) (id : ChainId) (v ts : ℕ) : ChainId → ℕ → ℕ :=
  upd n id (upd (n id) v ts)

/-! ## The steps -/

/-- The three entry points that upgrade a chain across a registry transition. -/
inductive UpgradePath
  /-- `Admin.upgradeChainFromVersion(_, v)`, called on the diamond itself. -/
  | direct (v : ℕ)
  /-- `ChainTypeManager.upgradeChainFromVersion(id, v)`; also the executor's `forward` of it. -/
  | ctm (v : ℕ)
  /-- `CTMUpgradeExecutor.upgradeChain(t, id)`. -/
  | executor (t : Address)

/-- What happens. -/
inductive TimedLabel
  /-- Chain `id` upgraded through `path`, by `caller`, at block time `τ`. -/
  | upgrade (id : ChainId) (path : UpgradePath) (caller : Address) (τ : ℕ)
  /-- A `ChainRouting` step other than a transition. -/
  | base (l : Label)
  /-- `ServerNotifier.setUpgradeTimestamp(id, ts)` by `caller`. -/
  | setUpgradeTimestamp (id : ChainId) (caller : Address) (ts : ℕ)
  /-- The CTM is pointed at a notifier whose schedule is `n` (`setServerNotifier`), or the
  notifier's implementation is swapped. -/
  | swapNotifier (n : ChainId → ℕ → ℕ)
  /-- Any write to chain `id`'s `DiamondAux`. -/
  | setAux (id : ChainId) (a : DiamondAux)

/-- `ChainRouting`'s transition label: crossing a registry-committed edge, which the timed
model replaces by its three entry points. -/
def Label.isRegistryTransition : Label → Prop
  | .transition _ => True
  | _ => False

/-- **One successful `Admin.upgradeChainFromVersion(_, v)` on chain `id`'s diamond**, with
`msg.sender = caller` and `block.timestamp = τ`, taking the routing system to `sys'`. The
routing part is `ChainRouting`'s transition step; the other fields are the checks that step
omits. -/
structure DiamondUpgrade (T : TimedConfig) (s : TimedSys) (id : ChainId) (v : ℕ)
    (caller : Address) (τ : ℕ) (sys' : Sys) : Prop where
  /-- `onlyAdminOrChainTypeManagerOrValidator` (`ZKChainBase.sol:126-131`). -/
  authorized : caller = (s.aux id).admin ∨ caller = T.X.ctmProxy ∨
    (s.aux id).validators caller = true
  /-- `s.protocolVersion == _oldProtocolVersion` (`Admin.sol:539-541`). -/
  atVersion : ∃ c, s.sys.chains id = some c ∧ c.pv = v
  /-- The chain's own schedule, for callers other than its admin and its CTM
  (`Admin.sol:546-554`). -/
  notifierGate : caller ≠ (s.aux id).admin → caller ≠ T.X.ctmProxy →
    s.notifier id v ≠ 0 ∧ s.notifier id v ≤ τ
  /-- `_requireAllBatchesExecuted()` (`DefaultUpgrade.sol:31`, `BaseZkSyncUpgrade.sol:109-113`). -/
  batchesExecuted : (s.aux id).committed = (s.aux id).executed
  /-- The cut lookup (`Admin.sol:535-537`), the routing guard, the derived cuts and the
  version increase: `ChainRouting`'s transition. -/
  routing : Step T.X.W s.sys (.transition id) sys'
  /-- The manifest's schedule (`BaseZkSyncUpgrade.sol:76-78`), read from the transition the
  cut names, `upgradeTransition[v]` (`ChainTypeManager.sol:606-612`). -/
  manifestTime : (T.sched (s.sys.ctm.ut v)).upgradeTimestamp ≤ τ
  /-- The settlement layer must already be at the target version
  (`BaseZkSyncUpgrade.sol:81-88`). -/
  settlementLayer : ∀ w, (s.aux id).slVersion = some w → (s.sys.edge T.X.W v).new ≤ w

/-- One successful transaction. -/
inductive TimedStep (T : TimedConfig) : TimedSys → TimedLabel → TimedSys → Prop
  /-- A direct call of the diamond. -/
  | direct {s : TimedSys} {id : ChainId} {v : ℕ} {caller : Address} {τ : ℕ} {sys' : Sys} :
      DiamondUpgrade T s id v caller τ sys' →
      TimedStep T s (.upgrade id (.direct v) caller τ) { s with sys := sys' }
  /-- `ChainTypeManager.upgradeChainFromVersion` (`ChainTypeManager.sol:623-626`): `onlyOwner`,
  then the diamond, which sees the CTM as `msg.sender`. -/
  | ctm {s : TimedSys} {id : ChainId} {v : ℕ} {caller : Address} {τ : ℕ} {sys' : Sys} :
      caller = T.ctmOwner →
      DiamondUpgrade T s id v T.X.ctmProxy τ sys' →
      TimedStep T s (.upgrade id (.ctm v) caller τ) { s with sys := sys' }
  /-- `CTMUpgradeExecutor.upgradeChain(t, id)` (`CTMUpgradeExecutor.sol:87-102`): the caller is
  the executor's owner or the chain's admin, `t` is the transition committed at its own
  `oldProtocolVersion()`, and the executor (the CTM's caller) must own the CTM. -/
  | executor {s : TimedSys} {id : ChainId} {t caller : Address} {τ : ℕ} {sys' : Sys} :
      (caller = T.execOwner ∨ caller = (s.aux id).admin) →
      s.sys.ctm.ut (T.X.W.tr t).old = t →
      T.X.rc.self = T.ctmOwner →
      DiamondUpgrade T s id (T.X.W.tr t).old T.X.ctmProxy τ sys' →
      TimedStep T s (.upgrade id (.executor t) caller τ) { s with sys := sys' }
  /-- Any other `ChainRouting` step; it reads and writes no timing state. -/
  | base {s : TimedSys} {l : Label} {sys' : Sys} :
      ¬ l.isRegistryTransition → Step T.X.W s.sys l sys' →
      TimedStep T s (.base l) { s with sys := sys' }
  /-- `ServerNotifier.setUpgradeTimestamp(id, ts)` (`ServerNotifier.sol:113-131`): only the
  chain's admin (`onlyChainAdmin`, :43-48), a nonzero time (:114-116), keyed on the chain's
  current version (:117), which must have something committed (:120-125). -/
  | setUpgradeTimestamp {s : TimedSys} {id : ChainId} {caller : Address} {ts : ℕ} {c : Chain} :
      s.sys.chains id = some c →
      caller = (s.aux id).admin →
      ts ≠ 0 →
      (s.sys.ctm.ut c.pv ≠ 0 ∨ s.sys.ctm.legacy c.pv ≠ LegacyCut.none) →
      TimedStep T s (.setUpgradeTimestamp id caller ts)
        { s with notifier := setNotifierEntry s.notifier id c.pv ts }
  /-- Another notifier, with any schedule. -/
  | swapNotifier {s : TimedSys} {n : ChainId → ℕ → ℕ} :
      TimedStep T s (.swapNotifier n) { s with notifier := n }
  /-- Any write to a chain's `DiamondAux`. -/
  | setAux {s : TimedSys} {id : ChainId} {a : DiamondAux} :
      TimedStep T s (.setAux id a) { s with aux := upd s.aux id a }

/-- A sequence of successful transactions. -/
inductive TimedRun (T : TimedConfig) : TimedSys → List TimedLabel → TimedSys → Prop
  | nil {s : TimedSys} : TimedRun T s [] s
  | cons {s s' s'' : TimedSys} {l : TimedLabel} {ls : List TimedLabel} :
      TimedStep T s l s' → TimedRun T s' ls s'' → TimedRun T s (l :: ls) s''

/-- What a timed label is in `ChainRouting`: an upgrade is a transition, a base step is
itself, and the rest are no routing step at all. -/
def TimedLabel.untimed : TimedLabel → List Label
  | .upgrade id _ _ _ => [.transition id]
  | .base l => [l]
  | .setUpgradeTimestamp _ _ _ => []
  | .swapNotifier _ => []
  | .setAux _ _ => []

/-- The break-glass steps. -/
def TimedLabel.isArbitrary : TimedLabel → Prop
  | .base l => l.isArbitrary
  | _ => False

/-! ## The departing version's deadline -/

/-- `ChainTypeManager.protocolVersionDeadline(v)` (`ChainTypeManager.sol:550-563`), with `d` the
stored overrides `protocolVersionDeadlines` (written by `setProtocolVersionDeadline`, :568-571,
and the legacy commit, :812; zero is "not set"). `none` is `type(uint256).max`: no deadline. -/
def versionDeadline (T : TimedConfig) (d : ℕ → ℕ) (s : CTM) (v : ℕ) : Option ℕ :=
  if d v ≠ 0 then some (d v)
  else if s.ut v ≠ 0 then some (T.sched (s.ut v)).deadline
  else if v = s.pv then none
  else some 0

/-- `protocolVersionIsActive(v)` at block time `τ` (`ChainTypeManager.sol:575-577`): chains at
`v` may still commit batches (`Committer.sol:85-87`). -/
def ProtocolVersionActive (T : TimedConfig) (d : ℕ → ℕ) (s : CTM) (v τ : ℕ) : Prop :=
  ∀ x, versionDeadline T d s v = some x → τ ≤ x

/-! ## Witness data

The `ExecutorForward` witness configuration: the deployed objects of `wWorld`, the executor
`1`, the CTM at `8`. The executor owns the CTM and governance `2` owns the executor.
Transition `300` (1→2) may be crossed from time `10` and keeps version 1 usable until `20`;
its genuine replacement `400` has the same deadline and may be crossed from time `15`.
Every chain's admin is `3` and `4` is its validator. -/

/-- Schedules of the witness transitions. -/
def wTimingSched : Address → TransitionSchedule := fun a =>
  if a = 300 then ⟨10, 20⟩ else if a = 400 then ⟨15, 20⟩ else ⟨0, 0⟩

/-- The witness configuration. -/
def wTiming : TimedConfig := ⟨wX, wTimingSched, 1, 2⟩

/-- A chain with admin `3` and validator `4`, nothing pending, on its settlement layer. -/
def wTimingAux : DiamondAux := ⟨3, fun a => decide (a = 4), 0, 0, none⟩

/-- A fresh CTM on release `100` with no chains, and an empty notifier. -/
def wTimingSys0 : TimedSys := ⟨wSys0, fun _ => ⟨0, fun _ => false, 0, 0, none⟩, fun _ _ => 0⟩

/-- Chain `0` is created and configured, the CTM commits `300`, and chain `0`'s admin sets
its own upgrade time for version 1 to `12`. -/
def wTimingSetup : List TimedLabel :=
  [.base (.genesis 0), .setAux 0 wTimingAux, .base (.ctm (.commit 300)),
    .setUpgradeTimestamp 0 3 12]

/-- Three chains created and configured, `300` committed, chain `2`'s admin schedules version
1 for time `12`; then chain `0` is upgraded through the executor by its admin at time `10`,
chain `1` through the CTM by the executor at `11`, and chain `2` directly by its validator
at `12`. -/
def wTimingRun : List TimedLabel :=
  [.base (.genesis 0), .setAux 0 wTimingAux, .base (.genesis 1), .setAux 1 wTimingAux,
    .base (.genesis 2), .setAux 2 wTimingAux, .base (.ctm (.commit 300)),
    .setUpgradeTimestamp 2 3 12,
    .upgrade 0 (.executor 300) 3 10, .upgrade 1 (.ctm 1) 1 11, .upgrade 2 (.direct 1) 4 12]

end Contracts.ChainTypeManager
