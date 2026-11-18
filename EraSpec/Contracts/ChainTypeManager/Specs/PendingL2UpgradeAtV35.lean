import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTimingStrong

/-!
# Model: the pending L2 upgrade transaction, at `draft/v0.35.0`

Source: branch `draft/v0.35.0` of the zksync-era `contracts` repository at commit
`b17415d2068065a4a3e3f0e7a14a2e96f54212e5` (`b17415d`, 2026-11-16). Every `file:line` below is
at that commit, and paths are relative to `l1-contracts/contracts/`. The earlier v35 pin
`d9f6789` has the same text at the same lines in every file cited here, except
`upgrades/registry/objects/CTMTransition.sol`, which changes only after line 125, below every
line cited.

This topic reuses `ChainRouting`'s routing system and `VersionRegistry`'s CTM writers, both
pinned at `e561b9cc2`, and `UpgradeTiming`'s timed steps (also `e561b9cc2`). The gates of those
timed steps were re-read at `b17415d`; see below.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.PendingL2UpgradeAtV35` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.PendingL2UpgradeAtV35`. Namespace:
`Contracts.ChainTypeManager.PendingL2UpgradeAtV35`.

## What this adds to `UpgradeTiming`

`UpgradeTiming` omits the L2 protocol upgrade transaction's checks and the check that the
previous one is finalized (its "Omitted reject-only checks"). Its `setAux` step rewrites a
chain's batch counters at any time. `UpgradeTimingStrong`'s headline
`ValidatedTimedRunsHaveNoDeadTime` is a statement about that model. This file adds:
* per chain, the pending transaction, the batch that carries it, and the verified-batch counter
  (`BatchAux`);
* the CTM's stored deadline overrides, as state (`PendingSys.dl`);
* the upgrade's L2 gates and L2 effect (`L2Gate`, `l2After`);
* the batch steps and the other writers of a chain's `DiamondAux`, each with its own
  precondition, in place of `setAux`.

## The timed gates at `b17415d`

Each gate of `TimedStep` (the code `Specs/UpgradeTiming.lean` quotes at `e561b9cc2`) is present
at `b17415d` with the same logic, at these lines:
* `Admin.upgradeChainFromVersion` (`state-transition/chain-deps/facets/Admin.sol:559-590`): the cut
  lookup (:566-568), the version check (:570-572), the notifier gate for callers other than the
  admin and the CTM (:577-585), the cut (:586) and the version increase (:587-589). The caller
  modifier is `onlyAdminOrChainTypeManagerOrValidator`
  (`state-transition/chain-deps/facets/ZKChainBase.sol:127-132`).
* `ChainTypeManager.upgradeChainFromVersion(id, v)`
  (`state-transition/ChainTypeManager.sol:618-621`, `onlyOwner`), and
  `CTMUpgradeExecutor.upgradeChain` (`upgrades/registry/executors/CTMUpgradeExecutor.sol:92-107`).
* `DefaultUpgrade.upgradeFromTransition` (`upgrades/DefaultUpgrade.sol:29-43`) requires every
  committed batch executed first (:30; `_requireAllBatchesExecuted`,
  `upgrades/BaseZkSyncUpgrade.sol:115-119`). Then `BaseZkSyncUpgrade._upgrade` (:72-108) checks the
  manifest's time gate (:82-84) and the settlement-layer order (:87-94).
* `ServerNotifier.setUpgradeTimestamp` (`governance/ServerNotifier.sol:113-132`).

Two further reject-only checks at `b17415d` are omitted here: `Admin._executeDiamondCut` and
`BaseZkSyncUpgrade._setVerifier` refuse to leave a chain that requires its second proof system
without a multi-proof verifier (`Admin.sol:121-126`, `BaseZkSyncUpgrade.sol:143-148`).

## The upgrade's L2 part

After the two gates, `_upgrade` calls `_setNewProtocolVersion` (`BaseZkSyncUpgrade.sol:96`,
defined at :218-272). It computes whether only the patch component changes:

    (uint32 previousMajorVersion, uint32 previousMinorVersion, ) =
        SemVer.unpackSemVer(...);                                              // :227-229
    (newMajorVersion, newMinorVersion, ) = SemVer.unpackSemVer(...);           // :236
    uint256 minorDelta = newMinorVersion - previousMinorVersion;               // :243
    if (minorDelta == 0) { patchOnly = true; }                                 // :245-247

On the settlement layer it refuses a change of the minor component while an L2 upgrade is
pending:

    if (!patchOnly && _isOnSettlementLayer) {                                  // :259
        if (s.l2SystemContractsUpgradeTxHash != bytes32(0)) {
            revert PreviousUpgradeNotFinalized(s.l2SystemContractsUpgradeTxHash); }  // :262-264
        if (s.l2SystemContractsUpgradeBatchNumber != 0) {
            revert PreviousUpgradeNotCleaned(); }                              // :265-267
    }

Then, on the settlement layer only (:103-105), `_setL2SystemContractUpgrade` (:162-202) sets the
pending transaction when the edge carries one, and refuses one on a patch:

    if (_l2ProtocolUpgradeTx.txType == 0) { return bytes32(0); }              // :168-170
    if (_patchOnly) { revert PatchCantSetUpgradeTxn(); }                       // :175-177
    s.l2SystemContractsUpgradeTxHash = l2ProtocolUpgradeTxHash;                // :199

The engine composes the transaction with `CTMUpgradeComposer.buildL2UpgradeTxFromPlan`
(`DefaultUpgrade.sol:76-82`; `upgrades/registry/libraries/CTMUpgradeComposer.sol:83-113`). It
returns the empty (`txType == 0`) transaction exactly when the plan has neither deployments nor a
delegate (:90-94), and otherwise a transaction of the upgrade type
(`state-transition/libraries/L2CanonicalTransactionLib.sol:55`). A `CTMTransition` builds its plan
with `L2PlanLib.build` (`upgrades/registry/objects/CTMTransition.sol:80-86`), which counts the
delegate among the deployments (`upgrades/registry/libraries/L2PlanLib.sol:61-65`) and refuses
deployments without one (:73-75). So for such a plan "has an L2 side" (`hasL2Side`,
`CTMTransition.sol:90`) and "composes a nonempty transaction" agree. The delegate's calldata is
composed from the chain's own `bridgehub` and `chainId` (`CTMUpgradeComposer.sol:97-103`), so
the transaction, and its hash `keccak256(abi.encode(tx))` (`BaseZkSyncUpgrade.sol:179, 197`),
depend on the chain.

## Batches

The `Committer` and `Executor` facets. All four entry points below carry `onlySettlementLayer`
(`ZKChainBase.sol:141-146`).
* `commitBatchesSharedBridge` (`state-transition/chain-deps/facets/Committer.sol:72-89`) is gated
  on the chain's version being active (:85-87) and commits exactly one batch (:99-101), numbered
  one past the previous one (:165-167), and raises `totalBatchesCommitted` (:110). It records that
  batch as the upgrade batch when a transaction is pending and not yet placed:

        bool processSystemUpgradeTx = systemContractsUpgradeTxHash != bytes32(0) &&
            s.l2SystemContractsUpgradeBatchNumber == 0;                         // :105-107
        s.l2SystemContractsUpgradeBatchNumber = _newBatchesData[0].batchNumber; // :127

  The validator timelock, the multisig committer and the permissionless validator all reach
  the chain through this function, and apart from a migration it is the only writer that raises
  `totalBatchesCommitted`.
* `proveBatchesSharedBridge` (`state-transition/chain-deps/facets/Executor.sol:215-251`) has no
  version gate. It raises `totalBatchesVerified`, at most to `totalBatchesCommitted` (:243-245,
  :250).
* `executeBatchesSharedBridge` (`Executor.sol:170-212`) has no version gate. It raises
  `totalBatchesExecuted`, at most to `totalBatchesVerified` (:201-205), and clears the pending
  transaction once its batch is executed:

        if (batchWhenUpgradeHappened != 0 && batchWhenUpgradeHappened <= newTotalBatchesExecuted) {
            delete s.l2SystemContractsUpgradeTxHash;
            delete s.l2SystemContractsUpgradeBatchNumber; }                       // :207-211

* `_revertBatches` (`ZKChainBase.sol:317-337`) is reached from `revertBatchesSharedBridge`
  (`Executor.sol:264-269`), the CTM owner's `revertBatches` (`ChainTypeManager.sol:591-594`) and
  `activatePriorityMode` (`Admin.sol:550`). The new last batch lies between executed and committed
  (:318-323), verified is capped (:325-327), committed is set (:328), and the upgrade batch number
  is cleared if its batch is reverted (:332-334). The pending hash stays.

## Deadlines

`protocolVersionDeadline(v)` (`ChainTypeManager.sol:545-558`) returns the stored override if
nonzero, else the committed transition's pinned deadline, else no deadline for the current
version, else zero. This is `versionDeadline` (`Specs/UpgradeTiming.lean`).
`protocolVersionIsActive(v)` is `block.timestamp <= protocolVersionDeadline(v)` (:570-572). The
overrides `protocolVersionDeadlines` have two writers: `setProtocolVersionDeadline` (:563-566),
any value, and the legacy commit `setNewVersionUpgrade`, which stores the departing version's
deadline (:807). `_commitVersionEdge` (:523-537) makes the departing version the current one.
A replacement must keep the replaced transition's deadline (`_requireSameDeadline`, called at
:438, defined at :483-489).

## Modelling choices

* **A revert is the absence of a step.** Reject-only checks not listed here are omitted, so
  the model has at least the source's steps. A result saying that no step of some kind exists
  holds of the source as well, relative to the boundaries below. A result saying a step exists
  is relative to the omitted checks. Omitted: the major-version, minor-delta and `SafeCast`
  checks of `_setNewProtocolVersion` (`BaseZkSyncUpgrade.sol:227-239`, :250-252); the L2
  transaction's own checks (type, validation, nonce, factory deps: :172-174, :181-195); the
  verifier checks (`DefaultUpgrade.sol:67-71`, the two second-proof checks above); every batch
  content check (hashes, proofs, DA, timestamps, priority operations); `notPriorityMode` on
  `revertBatchesSharedBridge`; and the callers of the batch steps and of
  `setProtocolVersionDeadline`.
* **Semantic versions.** A packed version is `major << 64 | minor << 32 | patch`
  (`common/libraries/SemVer.sol:5-31`). `minorOf v` is `v / 2^32`. It is the minor component when
  the major is zero and `v < 2^64`; `_setNewProtocolVersion` reverts on every other version
  before it reaches the finalization check, so `PatchOnly` agrees with `patchOnly` wherever the
  source reads it.
* **The replacement's same-deadline check is a gate.** `CStep.replace` omits
  `_requireSameDeadline`; `PStep.base` adds it as `TimedLabel.KeepsDeadline`.
* **Configuration.** `PendingConfig.hasL2 t` is whether transition `t`'s plan has an L2 side,
  and `PendingConfig.l2Hash t id` is the hash of the transaction `t` composes for chain `id`.
  Both are taken as given: no property of keccak is assumed, and a statement that needs a
  transaction pending takes `txHash ≠ 0` as a premise or a concrete nonzero value.
* **Batch numbers.** A commit records batch `totalBatchesCommitted + 1` as the upgrade batch.
  At the source the number is one past the `batchNumber` of the batch info the caller supplies
  for the last committed batch (`Committer.sol:165-167`), which `_checkBatchHashMismatch`
  compares by hash with the info stored at index `totalBatchesCommitted` (:103). So the model
  reads the stored batch's number as its index. Only `OverrideClearsPendingTx` and the
  witnesses that execute the batch depend on the value.
* **`DiamondAux` writes are split by writer.** `UpgradeTiming`'s `setAux` rewrites a chain's
  `DiamondAux` arbitrarily. Here the batch counters move only by the batch steps, and the other
  writers are:
  - `setRoles`: `acceptAdmin` (`Admin.sol:140-153`) and the CTM's `setValidator`
    (`Admin.sol:156-159`), the only writers of `s.admin` and `s.validators` besides
    `DiamondInit` (`state-transition/chain-deps/DiamondInit.sol:119-120`);
  - `slMoves`: the settlement layer's own version moves, for a chain that settles elsewhere;
  - `reinit`: a write of the whole `DiamondAux` and `BatchAux` of a registered chain that is at
    the CTM's version or settles elsewhere. It covers `DiamondInit` and the genesis upgrade at
    creation, at the CTM's version; `Migrator.forwardedBridgeBurn`
    (`state-transition/chain-deps/facets/Migrator.sol:154-209`, which requires the CTM's
    version, :192-198 and `ChainTypeManager.sol:735-738`, and writes the settlement layer, :207);
    `Migrator.forwardedBridgeMint` (:213-305, which requires the CTM's version, :225-229, and
    copies the counters and the pending upgrade from the departing diamond, :238-240, :295-296);
    and `forwardedBridgeConfirmTransferResult` (:309-333, which requires the chain to settle
    elsewhere, :324-326). These are the only writers of `s.settlementLayer` (:207, :299, :332).
    The `BatchAux` it writes satisfies `batch ≠ 0 → txHash ≠ 0`: the genesis upgrade leaves the
    batch number zero, the burn and the failed-transfer confirmation keep the chain's own
    fields, and `forwardedBridgeMint` copies both fields from the departing diamond
    (`prepareChainCommitment`, :343-344), which is assumed to satisfy it too
    (`MODEL-CTM-PENDING-L2`).
* **The bootstrap crossing** is `ChainRouting`'s untimed `bootstrapReset`. At the source it runs
  the same `_upgrade` (`upgrades/BootstrapUpgrade.sol:29-44`, :42), so it may set a pending
  transaction. `BaseEffect` lets it write any hash on a chain with no upgrade batch, and leaves
  its gates out.
* **Break-glass cuts** (`Admin.executeUpgrade`, `Admin.sol:593-595`, through the CTM's
  `executeUpgrade`, `ChainTypeManager.sol:626-628`; and crossing an opaque legacy edge) are
  `ChainRouting`'s `arbitraryCut`. Their init can write any storage; the model moves only the
  version and the routing. The results here exclude them or name them as a way out.
* **Not modelled**: a swap of the CTM's implementation, which can change what
  `protocolVersionIsActive` returns; chains on other CTMs; and diamond storage written by code an
  engine or init delegatecalls, other than as above.
-/

namespace Contracts.ChainTypeManager.PendingL2UpgradeAtV35

/-! ## Semantic versions -/

/-- `2^32`: the patch component's width (`SEMVER_MINOR_OFFSET`, `SemVer.sol:7`). -/
def semverMinorUnit : ℕ := 4294967296

/-- The minor component of a packed version with major `0` below `2^64`
(`SemVer.unpackSemVer`, `SemVer.sol:25-31`). -/
def minorOf (v : ℕ) : ℕ := v / semverMinorUnit

/-- `_setNewProtocolVersion`'s `patchOnly` (`BaseZkSyncUpgrade.sol:243-247`): only the patch
component changes. -/
def PatchOnly (old new : ℕ) : Prop := minorOf old = minorOf new

/-! ## Configuration -/

/-- The timed configuration and each transition's L2 side. -/
structure PendingConfig where
  /-- The timed model's configuration. -/
  T : TimedConfig
  /-- Whether transition `t`'s plan has an L2 side (`CTMTransition.sol:90`), that is, whether
  `buildL2UpgradeTxFromPlan` composes a transaction of nonzero type
  (`CTMUpgradeComposer.sol:90-94`). -/
  hasL2 : Address → Bool
  /-- `keccak256(abi.encode(tx))` of the transaction transition `t` composes for chain `id`
  (`BaseZkSyncUpgrade.sol:179, 197`). -/
  l2Hash : Address → ChainId → ℕ

/-- What `VersionEdgeLib.requireValidEdge` (`upgrades/registry/libraries/VersionEdgeLib.sol:35-91`)
checks of a transition, except the version shape (:64-83): the schedule (`ValidSchedule`,
:55-62), the version increase (:44-46), and that a patch carries no L2 side (:88-90). Every
`CTMTransition` constructor runs it (`CTMTransition.sol:91-97`). -/
def ValidEdge (C : PendingConfig) (t : Address) : Prop :=
  ValidSchedule C.T t ∧ (C.T.X.W.tr t).old < (C.T.X.W.tr t).new ∧
    (PatchOnly (C.T.X.W.tr t).old (C.T.X.W.tr t).new → C.hasL2 t = false)

/-! ## State -/

/-- The batch-side storage of a chain diamond that `DiamondAux` does not hold. -/
structure BatchAux where
  /-- `s.totalBatchesVerified`. -/
  verified : ℕ
  /-- `s.l2SystemContractsUpgradeTxHash` (`state-transition/chain-deps/ZKChainStorage.sol:159`);
  zero when no upgrade transaction is pending. -/
  txHash : ℕ
  /-- `s.l2SystemContractsUpgradeBatchNumber` (`ZKChainStorage.sol:163`); zero while the pending
  transaction is in no committed batch. -/
  batch : ℕ

/-- The timed system, the CTM's stored deadline overrides, and each chain's `BatchAux`. -/
structure PendingSys where
  /-- The timed system of `UpgradeTiming`. -/
  ts : TimedSys
  /-- `protocolVersionDeadlines` (`ChainTypeManager.sol:545-558`); zero is "not set". -/
  dl : ℕ → ℕ
  /-- Each chain's `BatchAux`; meaningful where a chain is registered. -/
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
inductive PLabel
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
  /-- `DiamondInit` with the genesis upgrade, or a migration step, writes chain `id`'s
  `DiamondAux` and `BatchAux`. -/
  | reinit (id : ChainId) (a : DiamondAux) (x : BatchAux)
  /-- `commitBatchesSharedBridge` on chain `id` at block time `τ`: one batch. -/
  | commit (id : ChainId) (τ : ℕ)
  /-- `proveBatchesSharedBridge` on chain `id`: `k` batches. -/
  | prove (id : ChainId) (k : ℕ)
  /-- `executeBatchesSharedBridge` on chain `id`: `k` batches. -/
  | execute (id : ChainId) (k : ℕ)
  /-- `_revertBatches(n)` on chain `id`. -/
  | revertBatches (id : ChainId) (n : ℕ)
  /-- `setProtocolVersionDeadline(v, t)` by the CTM's owner. -/
  | setDeadline (v t : ℕ)

/-! ## The steps -/

/-- The L2 gates of chain `id`'s upgrade from chain state `c` across the edge committed at
`c.pv`. -/
structure L2Gate (C : PendingConfig) (s : PendingSys) (id : ChainId) (c : Chain) : Prop where
  /-- `PreviousUpgradeNotFinalized` / `PreviousUpgradeNotCleaned`
  (`BaseZkSyncUpgrade.sol:259-268`): on the settlement layer, a change of the minor component
  needs no pending transaction and no upgrade batch. -/
  finalized : (s.ts.aux id).slVersion = none → ¬ PatchOnly c.pv (s.ts.sys.edge C.T.X.W c.pv).new →
    (s.bx id).txHash = 0 ∧ (s.bx id).batch = 0
  /-- `PatchCantSetUpgradeTxn` (`BaseZkSyncUpgrade.sol:175-177`), reached on the settlement
  layer only (:103-105). -/
  patchNoTx : (s.ts.aux id).slVersion = none → C.hasL2 (s.ts.sys.ctm.ut c.pv) = true →
    ¬ PatchOnly c.pv (s.ts.sys.edge C.T.X.W c.pv).new

/-- Chain `id`'s `BatchAux` after its upgrade from chain state `c`: on the settlement layer an
edge with an L2 side sets the pending transaction (`BaseZkSyncUpgrade.sol:103-105, 199`). -/
def l2After (C : PendingConfig) (s : PendingSys) (id : ChainId) (c : Chain) : BatchAux :=
  if (s.ts.aux id).slVersion = none ∧ C.hasL2 (s.ts.sys.ctm.ut c.pv) = true then
    { s.bx id with txHash := C.l2Hash (s.ts.sys.ctm.ut c.pv) id }
  else s.bx id

/-- What a `ChainRouting` step other than a transition does to the stored deadline overrides and
to the chains' `BatchAux`:
* the legacy commit `setNewVersionUpgrade` stores any deadline at the CTM's current version
  (`ChainTypeManager.sol:807`, the departing version by `_commitVersionEdge`, :526-528);
* the bootstrap crossing runs `_upgrade` (`BootstrapUpgrade.sol:42`), so it may set a pending
  transaction. Here it may write any hash on a chain whose upgrade batch number is zero, which
  holds whenever `_upgrade` writes one (`BaseZkSyncUpgrade.sol:175-177, 259-268`);
* no other routing step writes either. -/
inductive BaseEffect (s : PendingSys) : Label → (ℕ → ℕ) → (ChainId → BatchAux) → Prop
  /-- `setNewVersionUpgrade(cut, pv, t, R)`. -/
  | legacyCommit {R : Address} {b : Bool} {t : ℕ} :
      BaseEffect s (.ctm (.legacyCommit R b)) (upd s.dl s.ts.sys.ctm.pv t) s.bx
  /-- A bootstrap crossing that sets no transaction. -/
  | bootstrapKeeps {id : ChainId} : BaseEffect s (.bootstrapReset id) s.dl s.bx
  /-- A bootstrap crossing that sets transaction hash `h`. -/
  | bootstrapSets {id : ChainId} {h : ℕ} :
      (s.bx id).batch = 0 →
      BaseEffect s (.bootstrapReset id) s.dl (upd s.bx id { s.bx id with txHash := h })
  /-- Every other routing step. -/
  | other {l : Label} :
      (∀ R b, l ≠ .ctm (.legacyCommit R b)) → (∀ id, l ≠ .bootstrapReset id) →
      BaseEffect s l s.dl s.bx

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

/-- Chain `id`'s batches after `n` are reverted (`ZKChainBase.sol:325-334`). -/
def PendingSys.afterRevert (s : PendingSys) (id : ChainId) (n : ℕ) : PendingSys :=
  (s.withAux id { s.ts.aux id with committed := n }).withBx id
    { s.bx id with verified := min (s.bx id).verified n,
                   batch := if n < (s.bx id).batch then 0 else (s.bx id).batch }

/-- One successful transaction. -/
inductive PStep (C : PendingConfig) : PendingSys → PLabel → PendingSys → Prop
  /-- An upgrade of the timed model, with its L2 gates and effect. -/
  | upgrade {s : PendingSys} {id : ChainId} {path : UpgradePath} {caller : Address} {τ : ℕ}
      {ts' : TimedSys} {c : Chain} :
      TimedStep C.T s.ts (.upgrade id path caller τ) ts' →
      s.ts.sys.chains id = some c →
      L2Gate C s id c →
      PStep C s (.upgrade id path caller τ)
        { s with ts := ts', bx := upd s.bx id (l2After C s id c) }
  /-- Any other `ChainRouting` step. A replacement keeps the deadline (`_requireSameDeadline`,
  `ChainTypeManager.sol:438`). -/
  | base {s : PendingSys} {l : Label} {ts' : TimedSys} {dl' : ℕ → ℕ} {bx' : ChainId → BatchAux} :
      TimedStep C.T s.ts (.base l) ts' → (TimedLabel.base l).KeepsDeadline C.T →
      BaseEffect s l dl' bx' →
      PStep C s (.base l) ⟨ts', dl', bx'⟩
  /-- `ServerNotifier.setUpgradeTimestamp`, as in the timed model. -/
  | setUpgradeTimestamp {s : PendingSys} {id : ChainId} {caller : Address} {t : ℕ}
      {ts' : TimedSys} :
      TimedStep C.T s.ts (.setUpgradeTimestamp id caller t) ts' →
      PStep C s (.setUpgradeTimestamp id caller t) { s with ts := ts' }
  /-- Another notifier. -/
  | swapNotifier {s : PendingSys} {n : ChainId → ℕ → ℕ} :
      PStep C s (.swapNotifier n) { s with ts := { s.ts with notifier := n } }
  /-- `acceptAdmin` or the CTM's `setValidator`. -/
  | setRoles {s : PendingSys} {id : ChainId} {admin : Address} {vs : Address → Bool} :
      PStep C s (.setRoles id admin vs)
        (s.withAux id { s.ts.aux id with admin := admin, validators := vs })
  /-- The settlement layer's version moves, for a chain that settles elsewhere. -/
  | slMoves {s : PendingSys} {id : ChainId} {w w0 : ℕ} :
      (s.ts.aux id).slVersion = some w0 →
      PStep C s (.slMoves id w) (s.withAux id { s.ts.aux id with slVersion := some w })
  /-- `DiamondInit` with the genesis upgrade, or a migration step (see the module docstring). -/
  | reinit {s : PendingSys} {id : ChainId} {a : DiamondAux} {x : BatchAux} {c : Chain} :
      s.ts.sys.chains id = some c →
      (c.pv = s.ts.sys.ctm.pv ∨ (s.ts.aux id).slVersion ≠ none) →
      (x.batch ≠ 0 → x.txHash ≠ 0) →
      PStep C s (.reinit id a x) ((s.withAux id a).withBx id x)
  /-- `commitBatchesSharedBridge` (`Committer.sol:72-111`): on the settlement layer, with the
  chain's version active at `τ`. -/
  | commit {s : PendingSys} {id : ChainId} {τ : ℕ} {c : Chain} :
      s.ts.sys.chains id = some c →
      (s.ts.aux id).slVersion = none →
      ProtocolVersionActive C.T s.dl s.ts.sys.ctm c.pv τ →
      PStep C s (.commit id τ) (s.afterCommit id)
  /-- `proveBatchesSharedBridge` (`Executor.sol:215-251`): no version gate. -/
  | prove {s : PendingSys} {id : ChainId} {k : ℕ} :
      (s.ts.aux id).slVersion = none →
      (s.bx id).verified + k ≤ (s.ts.aux id).committed →
      PStep C s (.prove id k) (s.withBx id { s.bx id with verified := (s.bx id).verified + k })
  /-- `executeBatchesSharedBridge` (`Executor.sol:170-212`): no version gate. -/
  | execute {s : PendingSys} {id : ChainId} {k : ℕ} :
      (s.ts.aux id).slVersion = none →
      (s.ts.aux id).executed + k ≤ (s.bx id).verified →
      PStep C s (.execute id k) (s.afterExecute id k)
  /-- `_revertBatches(n)` (`ZKChainBase.sol:317-337`). -/
  | revertBatches {s : PendingSys} {id : ChainId} {n : ℕ} :
      (s.ts.aux id).slVersion = none →
      n ≤ (s.ts.aux id).committed → (s.ts.aux id).executed ≤ n →
      PStep C s (.revertBatches id n) (s.afterRevert id n)
  /-- `setProtocolVersionDeadline(v, t)` (`ChainTypeManager.sol:563-566`): any value. -/
  | setDeadline {s : PendingSys} {v t : ℕ} :
      PStep C s (.setDeadline v t) { s with dl := upd s.dl v t }

/-- A sequence of successful transactions. -/
inductive PRun (C : PendingConfig) : PendingSys → List PLabel → PendingSys → Prop
  | nil {s : PendingSys} : PRun C s [] s
  | cons {s s' s'' : PendingSys} {l : PLabel} {ls : List PLabel} :
      PStep C s l s' → PRun C s' ls s'' → PRun C s (l :: ls) s''

/-! ## Label predicates -/

/-- The break-glass steps. -/
def PLabel.isArbitrary : PLabel → Prop
  | .base l => l.isArbitrary
  | _ => False

/-- `Label.InstallsWf` for a label of this model; only a routing step installs a release. -/
def PLabel.InstallsWf (W : World) : PLabel → Prop
  | .base l => l.InstallsWf W
  | _ => True

/-- `Label.CommitsValidSchedule` for a label of this model; only a routing step records a
transition. -/
def PLabel.CommitsValidSchedule (T : TimedConfig) : PLabel → Prop
  | .base l => l.CommitsValidSchedule T
  | _ => True

/-- The label's block time, if it has one in the model (an upgrade or a commit), is `τ` or
later. -/
def PLabel.NotBefore (τ : ℕ) : PLabel → Prop
  | .upgrade _ _ _ t => τ ≤ t
  | .commit _ t => τ ≤ t
  | _ => True

/-! ## Dead time -/

/-- `ChainDeadTime` for this model: chain `id` is registered, its version is not active at `τ`
under the stored overrides, so `Committer.sol:85-87` refuses its batches, and no upgrade of it
succeeds at `τ`, through any entry point and by any caller. -/
def PChainDeadTime (C : PendingConfig) (s : PendingSys) (id : ChainId) (τ : ℕ) : Prop :=
  ∃ c, s.ts.sys.chains id = some c ∧ ¬ ProtocolVersionActive C.T s.dl s.ts.sys.ctm c.pv τ ∧
    ∀ path caller, ¬ ∃ s', PStep C s (.upgrade id path caller τ) s'

/-- Chain `id`, at chain state `c`, settles here and has a pending L2 upgrade transaction, and
the edge committed at its version changes the minor component. The CTM has moved past its
version, and that version has no legacy cut. -/
structure PendingBlock (C : PendingConfig) (s : PendingSys) (id : ChainId) (c : Chain) :
    Prop where
  /-- The chain is registered, at chain state `c`. -/
  chain : s.ts.sys.chains id = some c
  /-- The CTM is past the chain's version. -/
  behind : c.pv < s.ts.sys.ctm.pv
  /-- An edge is committed at the chain's version. -/
  committed : s.ts.sys.ctm.ut c.pv ≠ 0
  /-- That edge changes the minor component. -/
  minor : minorOf c.pv < minorOf (s.ts.sys.edge C.T.X.W c.pv).new
  /-- No legacy cut is recorded at the chain's version. -/
  noLegacy : s.ts.sys.ctm.legacy c.pv = LegacyCut.none
  /-- An L2 upgrade transaction is pending. -/
  pending : (s.bx id).txHash ≠ 0
  /-- The chain settles here. -/
  onSL : (s.ts.aux id).slVersion = none

/-- `PendingBlock`, with the pending transaction in no committed batch yet. -/
def PendingUnbatched (C : PendingConfig) (s : PendingSys) (id : ChainId) (c : Chain) : Prop :=
  PendingBlock C s id c ∧ (s.bx id).batch = 0

/-- The state after chain `id`, at chain state `c`, upgrades across the edge at `c.pv`: the
routing system's `crossEdge`, and the L2 effect. -/
def PendingSys.crossed (C : PendingConfig) (s : PendingSys) (id : ChainId) (c : Chain) :
    PendingSys :=
  { s with ts := { s.ts with sys := s.ts.sys.crossEdge C.T.X.W id c },
           bx := upd s.bx id (l2After C s id c) }

/-! ## Witness data

Real semantic versions: releases `100`, `200`, `260` and `250` at `0.1.0`, `0.2.0`, `0.2.1` and
`0.3.0`, with `wRows`'s routing for `100`, `200`, `250` and facet `26` for `260`. Transitions
`300` (`0.1.0 → 0.2.0`) and `600` (`0.2.0 → 0.3.0`) change the minor component and carry an L2
side; `700` (`0.2.0 → 0.2.1`) is a patch without one. All three may be crossed from time `10`
and keep the departing version active until `20`. -/

/-- `0.1.0`. -/
def v010 : ℕ := 4294967296
/-- `0.2.0`. -/
def v020 : ℕ := 8589934592
/-- `0.2.1`. -/
def v021 : ℕ := 8589934593
/-- `0.3.0`. -/
def v030 : ℕ := 12884901888

/-- Release versions. -/
def pwRelVersion : Address → ℕ := fun a =>
  if a = 100 then v010 else if a = 200 then v020 else if a = 260 then v021
  else if a = 250 then v030 else 0

/-- Release routing: `wRows`, and release `260` on facet `26`. -/
def pwRows : Address → ReleaseRows := fun a =>
  if a = 260 then [(1, (26, false)), (2, (26, false))] else wRows a

/-- Transition getters. -/
def pwTr : Address → TransitionView := fun a =>
  if a = 300 then ⟨v010, v020, 100, 200⟩
  else if a = 600 then ⟨v020, v030, 200, 250⟩
  else if a = 700 then ⟨v020, v021, 200, 260⟩
  else ⟨0, 0, 0, 0⟩

/-- The witness world. -/
def pwWorld : World := ⟨pwRelVersion, pwRows, pwTr⟩

/-- Schedules: every transition at upgrade time `10`, deadline `20`. -/
def pwSched : Address → TransitionSchedule := fun a =>
  if a = 300 ∨ a = 600 ∨ a = 700 then ⟨10, 20⟩ else ⟨0, 0⟩

/-- The timed configuration: executor `1`, which owns the CTM; governance `2` owns the
executor; the CTM at `8`. -/
def pwTimed : TimedConfig := ⟨⟨pwWorld, ProxyUpgradeCurrent.wConfig, 8⟩, pwSched, 1, 2⟩

/-- `300` and `600` carry an L2 side, `700` does not; every composed transaction hashes to
`7`. -/
def pwConfig : PendingConfig := ⟨pwTimed, fun a => decide (a = 300 ∨ a = 600), fun _ _ => 7⟩

/-- A fresh CTM on release `100` with no chains, an empty notifier, no overrides, and nothing
pending. -/
def pwSys0 : PendingSys :=
  ⟨⟨⟨initState pwWorld 100, fun _ => none⟩, fun _ => ⟨0, fun _ => false, 0, 0, none⟩,
    fun _ _ => 0⟩, fun _ => 0, fun _ => ⟨0, 0, 0⟩⟩

/-- Chain `0` is created and initialized (admin `3`, validator `4`, on L1, nothing pending), and
the CTM commits `300` and then `600`. Chain `0` stays at `0.1.0`. -/
def pwSetup : List PLabel :=
  [.base (.genesis 0), .reinit 0 wTimingAux ⟨0, 0, 0⟩, .base (.ctm (.commit 300)),
    .base (.ctm (.commit 600))]

/-- As `pwSetup`, with the patch `700` committed at `0.2.0` instead of `600`. -/
def pwPatchSetup : List PLabel :=
  [.base (.genesis 0), .reinit 0 wTimingAux ⟨0, 0, 0⟩, .base (.ctm (.commit 300)),
    .base (.ctm (.commit 700))]

/-- The CTM's owner `1` upgrades chain `0` through the CTM at time `25`. -/
def pwLateUpgrade : PLabel := .upgrade 0 (.ctm v010) 1 25

/-- The owner moves `0.2.0`'s deadline to `100`; chain `0` commits one batch at `30`, proves
and executes it; then the owner upgrades the chain through the CTM at `30`. -/
def pwRecovery : List PLabel :=
  [.setDeadline v020 100, .commit 0 30, .prove 0 1, .execute 0 1, .upgrade 0 (.ctm v020) 1 30]

/-- Steps that do not touch chain `0`'s pending transaction: an override of `0.1.0`'s deadline,
chain `0`'s admin setting its own upgrade time, and chain `1` created, initialized and
committing a batch at `30`. -/
def pwIdle : List PLabel :=
  [.setDeadline v010 30, .setUpgradeTimestamp 0 3 30, .base (.genesis 1),
    .reinit 1 wTimingAux ⟨0, 0, 0⟩, .commit 1 30]

end Contracts.ChainTypeManager.PendingL2UpgradeAtV35
