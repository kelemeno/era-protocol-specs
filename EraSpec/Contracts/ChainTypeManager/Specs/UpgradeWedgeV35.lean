import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTimingStrong

/-!
# Model: the pending L2 upgrade transaction, and chains that cannot move

Source: branch `draft/v0.35.0` of the zksync-era `contracts` repository at commit
`d9f678900e1bc8286412b78f56d4a9f443983c29` (`d9f6789`). Every `file:line` below is at that
commit. Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.UpgradeWedgeV35` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeWedgeV35`.

## Why this is modelled

`VersionEdgeLib` documents what its checks are for
(`upgrades/registry/libraries/VersionEdgeLib.sol:23-29`):

    /// @notice The version-shape and schedule rules every committed CTM edge obeys, checked when the
    ///         edge's object is constructed — before governance can commit an edge that would bump the
    ///         CTM and then revert on every chain. ...
    /// @notice Reverts unless the edge `_oldVersion -> _newVersion` with this schedule and L2 side
    ///         is one every chain can execute.

`UpgradeTimingStrong`'s headline `ValidatedTimedRunsHaveNoDeadTime` says that a chain at a
version with a committed, validly scheduled edge is never stuck: at every instant its version
is active or it can upgrade. That model (`Specs/UpgradeTiming.lean`, written at `e561b9cc2`)
omits the chain's pending L2 protocol upgrade transaction. This file adds it. With it, a chain
that crosses an L2-carrying edge after the next version's deadline lands on a version where it
can neither commit the batch that carries the transaction nor cross the next minor edge, which
needs that transaction finalized.

The committer's own comment describes the same state for a chain created during an upgrade
(`state-transition/chain-deps/facets/Committer.sol:82-83`):

    // 2. A chain might become out of sync if it launches while we are in the middle of a protocol upgrade. This would mean they cannot process their genesis upgrade
    // as their protocolversion would be outdated, and they also cannot process the protocol upgrade tx as they have a pending upgrade.

## The timed model at `d9f6789`

This file reuses `TimedStep` (`Specs/UpgradeTiming.lean`). Its gates were re-read at `d9f6789`
and are unchanged:

* `Admin.upgradeChainFromVersion` (`state-transition/chain-deps/facets/Admin.sol:559-590`):
  the version check (:570-572), the notifier gate for callers other than the admin and the CTM
  (:577-585), the cut (:586) and the version increase (:587-589).
* `ChainTypeManager.upgradeChainFromVersion(id, v)` (`state-transition/ChainTypeManager.sol:618-621`,
  `onlyOwner`), and `CTMUpgradeExecutor.upgradeChain`
  (`upgrades/registry/executors/CTMUpgradeExecutor.sol:92-107`).
* The engine: `DefaultUpgrade.upgradeFromTransition` requires every committed batch executed
  first (`upgrades/DefaultUpgrade.sol:30`, defined at `upgrades/BaseZkSyncUpgrade.sol:115-119`:
  `if (s.totalBatchesCommitted != s.totalBatchesExecuted) { revert NotAllBatchesExecuted(); }`),
  then the manifest's time gate (`BaseZkSyncUpgrade.sol:82-84`) and the settlement-layer order
  (:89-94).
* `ServerNotifier.setUpgradeTimestamp` (`governance/ServerNotifier.sol:113-132`).

## What this file adds

**Per chain** (`BatchAux`): `s.totalBatchesVerified`, `s.l2SystemContractsUpgradeTxHash` (the
pending transaction `h`) and `s.l2SystemContractsUpgradeBatchNumber` (the batch that carries it,
`b`; zero while none). `s.totalBatchesCommitted` and `s.totalBatchesExecuted` are already in
`DiamondAux`.

**On the CTM**: the stored deadline overrides `protocolVersionDeadlines` become state
(`PendingSys.dl`). In `UpgradeTiming` they were a parameter. Their two writers at `d9f6789` are
`setProtocolVersionDeadline` (`ChainTypeManager.sol:563-566`) and the legacy commit
`setNewVersionUpgrade`, which stores the deadline of the version it leaves (:807).

**The upgrade's L2 part** (`BaseZkSyncUpgrade._upgrade`, `BaseZkSyncUpgrade.sol:72-108`). After
the time and settlement-layer gates, `_setNewProtocolVersion` (:218-272) computes whether only
the patch component changes:

    (uint32 previousMajorVersion, uint32 previousMinorVersion, ) = SemVer.unpackSemVer(...);  // :227-229
    (newMajorVersion, newMinorVersion, ) = SemVer.unpackSemVer(...);                         // :236
    uint256 minorDelta = newMinorVersion - previousMinorVersion;                             // :243
    if (minorDelta == 0) { patchOnly = true; }                                               // :245-247

and, on the settlement layer, refuses a minor upgrade while an L2 upgrade is pending:

    if (!patchOnly && _isOnSettlementLayer) {                                                 // :259
        if (s.l2SystemContractsUpgradeTxHash != bytes32(0)) {
            revert PreviousUpgradeNotFinalized(s.l2SystemContractsUpgradeTxHash); }           // :262-264
        if (s.l2SystemContractsUpgradeBatchNumber != 0) { revert PreviousUpgradeNotCleaned(); } // :265-267
    }

Then, on the settlement layer only (:103-105), `_setL2SystemContractUpgrade` (:162-202) sets the
pending transaction when the edge carries one, and refuses one on a patch:

    if (_l2ProtocolUpgradeTx.txType == 0) { return bytes32(0); }                              // :168-170
    if (_patchOnly) { revert PatchCantSetUpgradeTxn(); }                                       // :175-177
    s.l2SystemContractsUpgradeTxHash = l2ProtocolUpgradeTxHash;                                // :199

The transaction is composed by `CTMUpgradeComposer.buildL2UpgradeTxFromPlan`
(`DefaultUpgrade.sol:76-82`), which returns the empty (`txType == 0`) transaction exactly when
the plan has no L2 side (`upgrades/registry/libraries/CTMUpgradeComposer.sol:90-94`). A
`CTMTransition` has an L2 side when its derived plan deploys something
(`upgrades/registry/objects/CTMTransition.sol:90`). The composed transaction depends on the
chain (`CTMUpgradeComposer.sol:83-89`), so its hash is per chain: `PendingConfig.l2Hash t id` is
`keccak256(abi.encode(tx))` (`BaseZkSyncUpgrade.sol:179, 197`) for transition `t` on chain `id`.
The model takes it as given. No property of keccak is assumed.

**Batches** (the `Committer` and `Executor` facets; all four entry points carry
`onlySettlementLayer`, `state-transition/chain-deps/facets/ZKChainBase.sol:141-146`):

* `commitBatchesSharedBridge` is gated on the chain's version being active
  (`Committer.sol:85-87`), commits exactly one batch (:99-101), number
  `totalBatchesCommitted + 1` (:103, :165-167, :110), and records it as the upgrade batch when
  an upgrade transaction is pending and not yet placed:

        bool processSystemUpgradeTx = systemContractsUpgradeTxHash != bytes32(0) &&
            s.l2SystemContractsUpgradeBatchNumber == 0;                                        // :105-107
        s.l2SystemContractsUpgradeBatchNumber = _newBatchesData[0].batchNumber;                // :127

* `proveBatchesSharedBridge` (`state-transition/chain-deps/facets/Executor.sol:215-251`) has no
  version gate. It raises `totalBatchesVerified`, at most to `totalBatchesCommitted` (:243-245).
* `executeBatchesSharedBridge` (`Executor.sol:170-212`) has no version gate. It raises
  `totalBatchesExecuted`, at most to `totalBatchesVerified` (:201-205), and clears the pending
  transaction once its batch is executed:

        if (batchWhenUpgradeHappened != 0 && batchWhenUpgradeHappened <= newTotalBatchesExecuted) {
            delete s.l2SystemContractsUpgradeTxHash;
            delete s.l2SystemContractsUpgradeBatchNumber; }                                    // :207-211

* `revertBatchesSharedBridge` (`Executor.sol:264-269`; also the CTM owner's `revertBatches`,
  `ChainTypeManager.sol:591-594`, and `activatePriorityMode`, `Admin.sol:524, 550`, which is
  `onlySettlementLayer` too) runs `_revertBatches` (`ZKChainBase.sol:317-337`): the new last
  batch lies between executed and committed (:318-323), verified is capped (:325-327), and the
  upgrade batch number is cleared if its batch is reverted (:332-334). The pending hash stays.

**Deadline resolution** is `versionDeadline` (`Specs/UpgradeTiming.lean`), which matches
`protocolVersionDeadline` at `d9f6789` (`ChainTypeManager.sol:545-558`): the stored override if
nonzero, else the committed transition's pinned deadline, else none for the current version,
else zero. `protocolVersionIsActive` is `block.timestamp <= protocolVersionDeadline(v)` (:570-572).

## Modelling choices

* **A revert is the absence of a step.** Reject-only checks not listed here are omitted, so the
  model has at least the source's steps. The wedge results say that no step of some kind exists,
  so they hold of the source as well. The no-dead-time result says some upgrade exists, so at the
  source it is relative to the omitted checks (see `Specs/UpgradeTiming.lean`). Omitted here: the
  major-version and minor-delta checks of `_setNewProtocolVersion` (`BaseZkSyncUpgrade.sol:230-252`)
  and `SafeCast.toUint96`, the L2 transaction's own validation (:172-174, :181-195), the verifier
  checks, every batch content check (hashes, proofs, DA, priority operations), and the callers
  of the batch steps (validators, or anyone in priority mode).
* **Semantic versions.** A packed version is `major << 64 | minor << 32 | patch`
  (`common/libraries/SemVer.sol:5-31`). `semverMinor v` is `v / 2^32`, which is the minor
  component when the major is zero (`v < 2^64`). Any other version is refused by the omitted
  major-version check.
* **The replacement's same-deadline check is a gate here.** `replaceUpgradeTransition` runs
  `_requireSameDeadline` (`ChainTypeManager.sol:438`, defined at :483-489). `CStep.replace`
  omits it, and this model adds it to its base steps as `TimedLabel.KeepsDeadline`.
* **The legacy commit's deadline write** is the step `legacyDeadline`: the legacy commit of
  `ChainRouting`, which also stores any deadline for the version the CTM leaves
  (`ChainTypeManager.sol:804, 807`). The generic `base` step also admits a legacy commit that
  leaves the stored deadlines alone. That only adds steps.
* **The bootstrap edge's L2 part** is the step `bootstrapL2`. `BootstrapUpgrade.upgradeFromBootstrap`
  ends in the same `_upgradeFromCommittedObject` (`upgrades/BootstrapUpgrade.sol:42`), so it can
  set the pending hash, and when it does the upgrade batch number was zero
  (`BaseZkSyncUpgrade.sol:259-268`; a patch cannot set one, :175-177). The step is
  `ChainRouting`'s `bootstrapReset` with any new pending hash, for a chain whose upgrade batch
  number is zero. The generic `base` step also admits a bootstrap reset that leaves the hash
  alone. As in `UpgradeTiming`, the bootstrap edge is untimed and its other gates are omitted.
* **`DiamondAux` writes are split by writer.** `UpgradeTiming`'s `setAux` rewrites a chain's
  `DiamondAux` arbitrarily. Here the batch counters move only by the batch steps, and the other
  writers are:
  - `setRoles`: `acceptAdmin` (`Admin.sol:140-152`) and the CTM's `setValidator` (:156-159);
    the admin and the validators only;
  - `slMoves`: the settlement layer's own version moves, for a chain that settles elsewhere;
  - `reinit`: a write of the whole `DiamondAux` and `BatchAux` of a registered chain that is at
    the CTM's version or settles elsewhere. This covers:
    `DiamondInit` and `genesisUpgrade` right after genesis, at the CTM's version (the genesis
    upgrade sets a pending hash, `upgrades/L1GenesisUpgrade.sol:42-47`);
    `Migrator.forwardedBridgeMint`, which requires the chain at the CTM's version
    (`state-transition/chain-deps/facets/Migrator.sol:225-229`) and copies the counters and the
    pending upgrade from the commitment (:238-240, :295-296);
    `Migrator.forwardedBridgeBurn`, which sets `s.settlementLayer` (:207) and is
    `onlyChainAssetHandler` (:158), reached after the CTM's `forwardedBridgeBurn` required the
    chain at the CTM's version (`ChainTypeManager.sol:735-738`, called at
    `core/chain-asset-handler/ChainAssetHandlerBase.sol:229`, before the diamond's at :267);
    and `forwardedBridgeConfirmTransferResult`, which requires the chain to be migrated
    (`Migrator.sol:324-326`).
    The value it writes satisfies `b ≠ 0 → h ≠ 0`, the invariant every other step keeps:
    `DiamondInit` leaves both zero, the genesis upgrade sets only `h`, and a migration copies
    them from a diamond (`Migrator.sol:343-344`). This is an assumption (`MODEL-CTM-PENDING-L2`).
* **Break-glass cuts** (`Admin.executeUpgrade`, `Admin.sol:593-595`, reached from the CTM
  owner's `executeUpgrade`, `ChainTypeManager.sol:626-628`) are `ChainRouting`'s `arbitraryCut`,
  as before. Their init can write any storage. The model only moves the version and routing.
  That is enough for the results here: every result either excludes break-glass cuts from the
  run or names them as an exit.
-/

namespace Contracts.ChainTypeManager

/-! ## Semantic versions -/

/-- `2^32`: the patch component's width (`SEMVER_MINOR_OFFSET`, `SemVer.sol:7`). -/
def semverMinorUnit : ℕ := 4294967296

/-- `2^64`: where the major component starts (`SEMVER_MAJOR_OFFSET`, `SemVer.sol:12`). -/
def semverMajorUnit : ℕ := 18446744073709551616

/-- The minor component of a packed version with major `0` (`SemVer.unpackSemVer`,
`SemVer.sol:25-31`). -/
def semverMinor (v : ℕ) : ℕ := v / semverMinorUnit

/-- `_setNewProtocolVersion`'s `patchOnly` (`BaseZkSyncUpgrade.sol:243-247`): only the patch
component changes. -/
def PatchOnly (old new : ℕ) : Prop := semverMinor old = semverMinor new

/-! ## Configuration -/

/-- The timed configuration and each transition's L2 side. -/
structure PendingConfig where
  /-- The timed model's configuration. -/
  T : TimedConfig
  /-- Whether the transition's plan has an L2 side (`CTMTransition.sol:90`), i.e. whether
  `buildL2UpgradeTxFromPlan` returns a transaction with nonzero type
  (`CTMUpgradeComposer.sol:90-94`). -/
  hasL2 : Address → Bool
  /-- `keccak256(abi.encode(tx))` of the transaction transition `t` composes for chain `id`
  (`BaseZkSyncUpgrade.sol:179, 197`). -/
  l2Hash : Address → ChainId → ℕ

/-- **Every check of `VersionEdgeLib.requireValidEdge`** (`VersionEdgeLib.sol:35-91`), for the
edge and schedule of transition `t`, as its constructor runs it (`CTMTransition.sol:91-97`):
* the version increases (:44-46);
* the schedule: a nonzero deadline, not before the upgrade timestamp (`ValidSchedule`, :55-62);
* both majors are zero (:72-77), with `SafeCast.toUint96` (:66-68): both versions below `2^64`;
* the minor moves by at most `MAX_ALLOWED_MINOR_VERSION_DELTA = 100` (:80-83,
  `common/Config.sol:73`);
* a patch carries no L2 side (:88-90). -/
def PassesRequireValidEdge (C : PendingConfig) (t : Address) : Prop :=
  (C.T.X.W.tr t).old < (C.T.X.W.tr t).new ∧ ValidSchedule C.T t ∧
    (C.T.X.W.tr t).old < semverMajorUnit ∧ (C.T.X.W.tr t).new < semverMajorUnit ∧
    semverMinor (C.T.X.W.tr t).new - semverMinor (C.T.X.W.tr t).old ≤ 100 ∧
    (PatchOnly (C.T.X.W.tr t).old (C.T.X.W.tr t).new → C.hasL2 t = false)

/-! ## State -/

/-- The batch-side storage of a chain diamond that `DiamondAux` does not hold. -/
structure BatchAux where
  /-- `s.totalBatchesVerified`. -/
  verified : ℕ
  /-- `s.l2SystemContractsUpgradeTxHash`; zero when no upgrade transaction is pending. -/
  txHash : ℕ
  /-- `s.l2SystemContractsUpgradeBatchNumber`; zero while the pending transaction is in no
  committed batch. -/
  batch : ℕ

/-- The timed system, the CTM's stored deadline overrides, and each chain's `BatchAux`. -/
structure PendingSys where
  /-- The timed system of `UpgradeTiming`. -/
  ts : TimedSys
  /-- `protocolVersionDeadlines` (`ChainTypeManager.sol:545-558`); zero is "not set". -/
  dl : ℕ → ℕ
  /-- Each chain's `BatchAux`. -/
  bx : ChainId → BatchAux

/-- Write chain `id`'s `DiamondAux`. -/
def PendingSys.withAux (s : PendingSys) (id : ChainId) (a : DiamondAux) : PendingSys :=
  { s with ts := { s.ts with aux := upd s.ts.aux id a } }

/-- Write chain `id`'s `BatchAux`. -/
def PendingSys.withBx (s : PendingSys) (id : ChainId) (x : BatchAux) : PendingSys :=
  { s with bx := upd s.bx id x }

/-- No chain has an upgrade batch number without a pending transaction. -/
def PendingInv (s : PendingSys) : Prop :=
  ∀ id, (s.bx id).batch ≠ 0 → (s.bx id).txHash ≠ 0

/-! ## Labels -/

/-- What happens. -/
inductive PendingLabel
  /-- Chain `id` upgraded through `path`, by `caller`, at block time `τ`. -/
  | upgrade (id : ChainId) (path : UpgradePath) (caller : Address) (τ : ℕ)
  /-- A `ChainRouting` step other than a transition. -/
  | base (l : Label)
  /-- `ServerNotifier.setUpgradeTimestamp(id, ts)` by `caller`. -/
  | setUpgradeTimestamp (id : ChainId) (caller : Address) (ts : ℕ)
  /-- Another notifier, with schedule `n`. -/
  | swapNotifier (n : ChainId → ℕ → ℕ)
  /-- `acceptAdmin` / `setValidator`: chain `id`'s admin and validators become these. -/
  | setRoles (id : ChainId) (admin : Address) (validators : Address → Bool)
  /-- The settlement layer of chain `id`, which settles elsewhere, is now at version `w`. -/
  | slMoves (id : ChainId) (w : ℕ)
  /-- `DiamondInit`, the genesis upgrade or a migration writes chain `id`'s `DiamondAux` and
  `BatchAux`. -/
  | reinit (id : ChainId) (a : DiamondAux) (x : BatchAux)
  /-- `commitBatchesSharedBridge` on chain `id` at block time `τ`: one batch. -/
  | commit (id : ChainId) (τ : ℕ)
  /-- `proveBatchesSharedBridge` on chain `id`: `k` batches. -/
  | prove (id : ChainId) (k : ℕ)
  /-- `executeBatchesSharedBridge` on chain `id`: `k` batches. -/
  | execute (id : ChainId) (k : ℕ)
  /-- `revertBatchesSharedBridge(_, n)` on chain `id`. -/
  | revertBatches (id : ChainId) (n : ℕ)
  /-- `setProtocolVersionDeadline(v, t)` by the CTM's owner. -/
  | setDeadline (v t : ℕ)

/-! ## The steps -/

/-- The L2 gates of chain `id`'s upgrade from chain state `c` across the edge committed at
`c.pv`. -/
structure L2Gate (C : PendingConfig) (s : PendingSys) (id : ChainId) (c : Chain) : Prop where
  /-- `PreviousUpgradeNotFinalized` / `PreviousUpgradeNotCleaned`
  (`BaseZkSyncUpgrade.sol:259-268`): on the settlement layer a minor upgrade needs no pending
  transaction and no upgrade batch. -/
  finalized : (s.ts.aux id).slVersion = none → ¬ PatchOnly c.pv (s.ts.sys.edge C.T.X.W c.pv).new →
    (s.bx id).txHash = 0 ∧ (s.bx id).batch = 0
  /-- `PatchCantSetUpgradeTxn` (`BaseZkSyncUpgrade.sol:175-177`), reached on the settlement
  layer only (:103-105). -/
  patchNoTx : (s.ts.aux id).slVersion = none → C.hasL2 (s.ts.sys.ctm.ut c.pv) = true →
    ¬ PatchOnly c.pv (s.ts.sys.edge C.T.X.W c.pv).new

/-- Chain `id`'s `BatchAux` after its upgrade from chain state `c`: on the settlement layer an
L2-carrying edge sets the pending transaction (`BaseZkSyncUpgrade.sol:103-105, 199`). -/
def l2After (C : PendingConfig) (s : PendingSys) (id : ChainId) (c : Chain) : BatchAux :=
  if (s.ts.aux id).slVersion = none ∧ C.hasL2 (s.ts.sys.ctm.ut c.pv) = true then
    { s.bx id with txHash := C.l2Hash (s.ts.sys.ctm.ut c.pv) id }
  else s.bx id

/-- One batch committed on chain `id` (`Committer.sol:105-110, 119-128`). -/
def PendingSys.afterCommit (s : PendingSys) (id : ChainId) : PendingSys :=
  (s.withAux id { s.ts.aux id with committed := (s.ts.aux id).committed + 1 }).withBx id
    (if (s.bx id).txHash ≠ 0 ∧ (s.bx id).batch = 0 then
      { s.bx id with batch := (s.ts.aux id).committed + 1 }
    else s.bx id)

/-- `k` batches executed on chain `id` (`Executor.sol:201-211`). -/
def PendingSys.afterExecute (s : PendingSys) (id : ChainId) (k : ℕ) : PendingSys :=
  (s.withAux id { s.ts.aux id with executed := (s.ts.aux id).executed + k }).withBx id
    (if (s.bx id).batch ≠ 0 ∧ (s.bx id).batch ≤ (s.ts.aux id).executed + k then
      { s.bx id with txHash := 0, batch := 0 }
    else s.bx id)

/-- Chain `id`'s batches after those above `n` are reverted (`ZKChainBase.sol:325-334`). -/
def PendingSys.afterRevert (s : PendingSys) (id : ChainId) (n : ℕ) : PendingSys :=
  (s.withAux id { s.ts.aux id with committed := n }).withBx id
    { s.bx id with verified := min (s.bx id).verified n,
                   batch := if n < (s.bx id).batch then 0 else (s.bx id).batch }

/-- One successful transaction. -/
inductive PendingStep (C : PendingConfig) : PendingSys → PendingLabel → PendingSys → Prop
  /-- An upgrade of the timed model, with its L2 gates and effect. -/
  | upgrade {s : PendingSys} {id : ChainId} {path : UpgradePath} {caller : Address} {τ : ℕ}
      {ts' : TimedSys} {c : Chain} :
      TimedStep C.T s.ts (.upgrade id path caller τ) ts' →
      s.ts.sys.chains id = some c →
      L2Gate C s id c →
      PendingStep C s (.upgrade id path caller τ)
        { s with ts := ts', bx := upd s.bx id (l2After C s id c) }
  /-- Any other `ChainRouting` step. A replacement keeps the deadline (`_requireSameDeadline`,
  `ChainTypeManager.sol:438`). -/
  | base {s : PendingSys} {l : Label} {ts' : TimedSys} :
      TimedStep C.T s.ts (.base l) ts' → (TimedLabel.base l).KeepsDeadline C.T →
      PendingStep C s (.base l) { s with ts := ts' }
  /-- The legacy commit `setNewVersionUpgrade` (`ChainTypeManager.sol:794-813`), which also
  stores the deadline `d` of the version the CTM leaves (:807). -/
  | legacyDeadline {s : PendingSys} {R : Address} {b : Bool} {ts' : TimedSys} {d : ℕ} :
      TimedStep C.T s.ts (.base (.ctm (.legacyCommit R b))) ts' →
      PendingStep C s (.base (.ctm (.legacyCommit R b)))
        { s with ts := ts', dl := upd s.dl s.ts.sys.ctm.pv d }
  /-- Crossing the bootstrap edge, whose L2 part sets a pending hash `h`
  (`BootstrapUpgrade.sol:42`). The upgrade batch number was zero (`BaseZkSyncUpgrade.sol:265-267`). -/
  | bootstrapL2 {s : PendingSys} {id : ChainId} {ts' : TimedSys} {h : ℕ} :
      TimedStep C.T s.ts (.base (.bootstrapReset id)) ts' →
      (s.bx id).batch = 0 →
      PendingStep C s (.base (.bootstrapReset id))
        { s with ts := ts', bx := upd s.bx id { s.bx id with txHash := h } }
  /-- `ServerNotifier.setUpgradeTimestamp`, as in the timed model. -/
  | setUpgradeTimestamp {s : PendingSys} {id : ChainId} {caller : Address} {t : ℕ}
      {ts' : TimedSys} :
      TimedStep C.T s.ts (.setUpgradeTimestamp id caller t) ts' →
      PendingStep C s (.setUpgradeTimestamp id caller t) { s with ts := ts' }
  /-- Another notifier. -/
  | swapNotifier {s : PendingSys} {n : ChainId → ℕ → ℕ} :
      PendingStep C s (.swapNotifier n) { s with ts := { s.ts with notifier := n } }
  /-- `acceptAdmin` or the CTM's `setValidator`. -/
  | setRoles {s : PendingSys} {id : ChainId} {admin : Address} {vs : Address → Bool} :
      PendingStep C s (.setRoles id admin vs)
        (s.withAux id { s.ts.aux id with admin := admin, validators := vs })
  /-- The settlement layer's version moves, for a chain that settles elsewhere. -/
  | slMoves {s : PendingSys} {id : ChainId} {w w0 : ℕ} :
      (s.ts.aux id).slVersion = some w0 →
      PendingStep C s (.slMoves id w) (s.withAux id { s.ts.aux id with slVersion := some w })
  /-- `DiamondInit`, the genesis upgrade or a migration (see the module docstring). -/
  | reinit {s : PendingSys} {id : ChainId} {a : DiamondAux} {x : BatchAux} {c : Chain} :
      s.ts.sys.chains id = some c →
      (c.pv = s.ts.sys.ctm.pv ∨ (s.ts.aux id).slVersion ≠ none) →
      (x.batch ≠ 0 → x.txHash ≠ 0) →
      PendingStep C s (.reinit id a x) ((s.withAux id a).withBx id x)
  /-- `commitBatchesSharedBridge` (`Committer.sol:72-111`): on the settlement layer, with the
  chain's version active at `τ`. -/
  | commit {s : PendingSys} {id : ChainId} {τ : ℕ} {c : Chain} :
      s.ts.sys.chains id = some c →
      (s.ts.aux id).slVersion = none →
      ProtocolVersionActive C.T s.dl s.ts.sys.ctm c.pv τ →
      PendingStep C s (.commit id τ) (s.afterCommit id)
  /-- `proveBatchesSharedBridge` (`Executor.sol:215-251`): no version gate. -/
  | prove {s : PendingSys} {id : ChainId} {k : ℕ} :
      (s.ts.aux id).slVersion = none →
      (s.bx id).verified + k ≤ (s.ts.aux id).committed →
      PendingStep C s (.prove id k)
        (s.withBx id { s.bx id with verified := (s.bx id).verified + k })
  /-- `executeBatchesSharedBridge` (`Executor.sol:170-212`): no version gate. -/
  | execute {s : PendingSys} {id : ChainId} {k : ℕ} :
      (s.ts.aux id).slVersion = none →
      (s.ts.aux id).executed + k ≤ (s.bx id).verified →
      PendingStep C s (.execute id k) (s.afterExecute id k)
  /-- `revertBatchesSharedBridge` (`Executor.sol:264-269`, `ZKChainBase.sol:317-337`). -/
  | revertBatches {s : PendingSys} {id : ChainId} {n : ℕ} :
      (s.ts.aux id).slVersion = none →
      n ≤ (s.ts.aux id).committed → (s.ts.aux id).executed ≤ n →
      PendingStep C s (.revertBatches id n) (s.afterRevert id n)
  /-- `setProtocolVersionDeadline(v, t)` (`ChainTypeManager.sol:563-566`): any value. -/
  | setDeadline {s : PendingSys} {v t : ℕ} :
      PendingStep C s (.setDeadline v t) { s with dl := upd s.dl v t }

/-- A sequence of successful transactions. -/
inductive PendingRun (C : PendingConfig) : PendingSys → List PendingLabel → PendingSys → Prop
  | nil {s : PendingSys} : PendingRun C s [] s
  | cons {s s' s'' : PendingSys} {l : PendingLabel} {ls : List PendingLabel} :
      PendingStep C s l s' → PendingRun C s' ls s'' → PendingRun C s (l :: ls) s''

/-! ## Label predicates -/

/-- The break-glass steps. -/
def PendingLabel.isArbitrary : PendingLabel → Prop
  | .base l => l.isArbitrary
  | _ => False

/-- `Label.InstallsWf` for a label of this model. -/
def PendingLabel.InstallsWf (W : World) : PendingLabel → Prop
  | .base l => l.InstallsWf W
  | _ => True

/-- `Label.CommitsValidSchedule` for a label of this model. -/
def PendingLabel.CommitsValidSchedule (T : TimedConfig) : PendingLabel → Prop
  | .base l => l.CommitsValidSchedule T
  | _ => True

/-- If the label is a batch commit, its block time is `τ` or later. -/
def PendingLabel.CommitsNotBefore (τ : ℕ) : PendingLabel → Prop
  | .commit _ t => τ ≤ t
  | _ => True

/-! ## Dead time and the wedge -/

/-- `ChainDeadTime` for this model: chain `id` is registered, its version is not active at
`τ` under the stored overrides, and no upgrade of it succeeds at `τ`, through any entry point
and by any caller. -/
def PendingDeadTime (C : PendingConfig) (s : PendingSys) (id : ChainId) (τ : ℕ) : Prop :=
  ∃ c, s.ts.sys.chains id = some c ∧ ¬ ProtocolVersionActive C.T s.dl s.ts.sys.ctm c.pv τ ∧
    ∀ path caller, ¬ ∃ s', PendingStep C s (.upgrade id path caller τ) s'

/-- Chain `id`, at chain state `c`, has a pending L2 upgrade transaction and the edge committed
at its version is minor. It settles here, the CTM has moved past its version, and that version
has no legacy cut. -/
structure PendingBlock (C : PendingConfig) (s : PendingSys) (id : ChainId) (c : Chain) :
    Prop where
  /-- The chain is registered, at chain state `c`. -/
  chain : s.ts.sys.chains id = some c
  /-- The CTM is past the chain's version. -/
  behind : c.pv < s.ts.sys.ctm.pv
  /-- An edge is committed at the chain's version. -/
  committed : s.ts.sys.ctm.ut c.pv ≠ 0
  /-- That edge raises the minor component. -/
  minor : semverMinor c.pv < semverMinor (s.ts.sys.edge C.T.X.W c.pv).new
  /-- No legacy cut is committed at the chain's version. -/
  noLegacy : s.ts.sys.ctm.legacy c.pv = LegacyCut.none
  /-- An L2 upgrade transaction is pending. -/
  pending : (s.bx id).txHash ≠ 0
  /-- The chain settles here. -/
  onSL : (s.ts.aux id).slVersion = none

/-- `PendingBlock`, with the pending transaction in no committed batch yet. -/
def PendingWedge (C : PendingConfig) (s : PendingSys) (id : ChainId) (c : Chain) : Prop :=
  PendingBlock C s id c ∧ (s.bx id).batch = 0

/-- Chain `id`'s state after its upgrade from chain state `c` across the edge at `c.pv`: the
routing system's `crossEdge`, and the L2 effect. -/
def PendingSys.crossed (C : PendingConfig) (s : PendingSys) (id : ChainId) (c : Chain) :
    PendingSys :=
  { s with ts := { s.ts with sys := s.ts.sys.crossEdge C.T.X.W id c },
           bx := upd s.bx id (l2After C s id c) }

/-! ## Witness data

A world like `wWorld`, with real semantic versions: releases `100`, `200`, `250` at `0.1.0`,
`0.2.0`, `0.3.0`; transitions `300` (`0.1.0 → 0.2.0`) and `600` (`0.2.0 → 0.3.0`), both minor
and both carrying an L2 upgrade transaction. Both may be crossed from time `10`, and both keep
the departing version usable until `20`. -/

/-- `0.1.0`. -/
def wWedgeV1 : ℕ := 4294967296
/-- `0.2.0`. -/
def wWedgeV2 : ℕ := 8589934592
/-- `0.3.0`. -/
def wWedgeV3 : ℕ := 12884901888

/-- Release versions. -/
def wWedgeRelVersion : Address → ℕ := fun a =>
  if a = 100 then wWedgeV1 else if a = 200 then wWedgeV2 else if a = 250 then wWedgeV3 else 0

/-- Transition getters. -/
def wWedgeTr : Address → TransitionView := fun a =>
  if a = 300 then ⟨wWedgeV1, wWedgeV2, 100, 200⟩
  else if a = 600 then ⟨wWedgeV2, wWedgeV3, 200, 250⟩
  else ⟨0, 0, 0, 0⟩

/-- The witness world; the release routing is `wWorld`'s. -/
def wWedgeWorld : World := ⟨wWedgeRelVersion, wRows, wWedgeTr⟩

/-- Schedules: both transitions at upgrade time `10`, deadline `20`. -/
def wWedgeSched : Address → TransitionSchedule := fun a =>
  if a = 300 then ⟨10, 20⟩ else if a = 600 then ⟨10, 20⟩ else ⟨0, 0⟩

/-- The timed configuration: executor `1`, which owns the CTM; governance `2` owns the
executor; the CTM at `8`. -/
def wWedgeTimed : TimedConfig :=
  ⟨⟨wWedgeWorld, ProxyUpgradeCurrent.wConfig, 8⟩, wWedgeSched, 1, 2⟩

/-- Both transitions carry an L2 side, whose hash is `7` on every chain. -/
def wWedgeConfig : PendingConfig :=
  ⟨wWedgeTimed, fun a => decide (a = 300 ∨ a = 600), fun _ _ => 7⟩

/-- A fresh CTM on release `100` with no chains, an empty notifier, no overrides, and nothing
pending anywhere. -/
def wWedgeSys0 : PendingSys :=
  ⟨⟨⟨initState wWedgeWorld 100, fun _ => none⟩, fun _ => ⟨0, fun _ => false, 0, 0, none⟩,
    fun _ _ => 0⟩, fun _ => 0, fun _ => ⟨0, 0, 0⟩⟩

/-- Chain `0` is created and initialized (admin `3`, validator `4`, on L1, nothing pending),
and the CTM commits `300` and then `600`. Chain `0` lags at `0.1.0`. -/
def wWedgeSetup : List PendingLabel :=
  [.base (.genesis 0), .reinit 0 wTimingAux ⟨0, 0, 0⟩, .base (.ctm (.commit 300)),
    .base (.ctm (.commit 600))]

/-- The CTM's owner `1` upgrades chain `0` through the CTM at time `25`, after `0.2.0`'s
deadline `20`. -/
def wWedgeLateUpgrade : PendingLabel := .upgrade 0 (.ctm wWedgeV1) 1 25

/-- The recovery: the owner moves `0.2.0`'s deadline to `100`; the chain commits the batch that
carries the upgrade transaction at `30`, proves and executes it; then the owner upgrades it
across `600` at `30`. -/
def wWedgeRecovery : List PendingLabel :=
  [.setDeadline wWedgeV2 100, .commit 0 30, .prove 0 1, .execute 0 1,
    .upgrade 0 (.ctm wWedgeV2) 1 30]

/-- The CTM's owner upgrades chain `0` at time `15`, while `0.2.0` is still active, and the
chain commits the batch that carries the upgrade transaction at `18`. -/
def wWedgePlaced : List PendingLabel := [.upgrade 0 (.ctm wWedgeV1) 1 15, .commit 0 18]

/-- Chain `0` is created with its genesis upgrade transaction pending (hash `9`) and in no
batch, and the CTM commits `300`. The chain is at `0.1.0`, the version the CTM just left. -/
def wWedgeGenesisSetup : List PendingLabel :=
  [.base (.genesis 0), .reinit 0 wTimingAux ⟨0, 9, 0⟩, .base (.ctm (.commit 300))]

end Contracts.ChainTypeManager
