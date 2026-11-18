import EraSpec.Contracts.ChainTypeManager.Specs.CommittedEdgeExecutable

/-!
# Model: the L2 upgrade transaction's nonce along one chain's history

Source: branch `draft/v0.35.0` of the zksync-era `contracts` repository at commit
`b17415d2068065a4a3e3f0e7a14a2e96f54212e5` (`b17415d20`), as for
`EraSpec.Contracts.ChainTypeManager.Specs.CommittedEdgeExecutable`, whose chain-side functions
this file reuses. Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.UpgradeTxNonces` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTxNonces`. Namespace
`Contracts.ChainTypeManager.EdgeChecks`.

## Why this is modelled

`_setL2SystemContractUpgrade` gives the reason for its nonce check
(`upgrades/BaseZkSyncUpgrade.sol:189-193`):

    // We want the hashes of l2 system upgrade transactions to be unique.
    // This is why we require that the `nonce` field is unique to each upgrade.
    if (_l2ProtocolUpgradeTx.nonce != _newMinorProtocolVersion) { revert L2UpgradeNonceNotEqualToNewProtocolVersion(...); }

Uniqueness is not local to that check. It rests on the chain's version moving forward across
every writer of the pending transaction, `s.l2SystemContractsUpgradeTxHash` (`h`) and its batch
number `s.l2SystemContractsUpgradeBatchNumber` (`b`), on the settlement-layer diamond and across
migration copies.

## The writers (every one at `b17415d20`)

* **Genesis** (`ChainTypeManager.createNewChain`, `state-transition/ChainTypeManager.sol:703-711`):
  `DiamondInit` sets `s.protocolVersion = ctm.protocolVersion()`
  (`state-transition/chain-deps/DiamondInit.sol:58, :110`) on fresh storage (`h = b = 0`), then
  `L1GenesisUpgrade.genesisUpgrade` (`upgrades/L1GenesisUpgrade.sol:31-53`) runs `_upgrade` with the
  chain's own version and `BaseZkSyncUpgradeGenesis._setNewProtocolVersion`
  (`upgrades/BaseZkSyncUpgradeGenesis.sol:25-82`: `<` in place of `<=` at :32, `patchOnly` always
  false at :55, settlement layer required at :62-64). `genesisStoragePart`.
* **Crossing on the settlement layer** (`DefaultUpgrade` / `BootstrapUpgrade` through
  `_upgradeFromCommittedObject`, `upgrades/DefaultUpgrade.sol:65-84`): `upgradeStoragePart` with
  `onSL = true`, which writes `h` at `BaseZkSyncUpgrade.sol:199`.
* **Crossing off the settlement layer** (`BaseZkSyncUpgrade.sol:89-94, :96, :103`): the version
  step with `onSL = false`, which checks nothing about `h`/`b` and writes neither.
* **Commit** (`state-transition/chain-deps/facets/Committer.sol:105-108, :118-128`): when `h` is
  nonzero and `b` is zero, `b` becomes the committed batch's number (positive).
* **Execute** (`state-transition/chain-deps/facets/Executor.sol:207-211`): once `b` is nonzero and
  executed, both are deleted.
* **Revert** (`state-transition/chain-deps/facets/ZKChainBase.sol:332-334`): `b` is deleted when its
  batch is reverted; `h` stays.
* **Migration** (`state-transition/chain-deps/facets/Migrator.sol`): `forwardedBridgeBurn`
  (:154-209) requires the diamond on its settlement layer (:162-164) and at the version in its
  chain data (:192-198), moves it off the settlement layer (:207) and records `(h, b)` in the
  commitment (:208, :343-344); `ChainTypeManager.forwardedBridgeBurn` requires the chain at the
  CTM's version and hands that version to the destination (`ChainTypeManager.sol:733-740`).
  `forwardedBridgeMint` (:213-305) copies `(h, b)` into the destination diamond (:295-296) and
  puts it on its settlement layer (:299). A destination deployed for the migration starts at its
  CTM's version (`DiamondInit.sol:58, :110`), which the destination CTM requires to be the version
  handed over (`ChainTypeManager.sol:752-756`). A destination that already exists must be off its
  settlement layer (`Migrator.sol:277-287`) and at its own CTM's version (:224-229); nothing
  relates that version to the source's.
  `forwardedBridgeConfirmTransferResult` on failure (:309-333) puts the source back on its
  settlement layer, if it is still at the version it left with (:327-330).

Commit, execute and revert carry `onlySettlementLayer` (`ZKChainBase.sol:141-146`).

## Modelling choices

* **One chain, several diamonds.** `NonceSys.dia d` is the chain's diamond on settlement layer `d`
  (`none` before it exists). A diamond records its version, `(h, b)`, and whether it is on its
  settlement layer (`s.settlementLayer == address(0)`). At most one migration is in flight
  (`pending`).
* **The ghost log** `NonceSys.log` lists, in order, every transaction whose hash a genesis or a
  crossing wrote to `h` (`BaseZkSyncUpgrade.sol:199`). Migration copies are not writes of a new
  transaction and are not logged.
* **The transaction a crossing carries is arbitrary.** Whatever object, engine or composer
  produced it, the chain's own checks decide; `CommittedEdgeExecutable` shows what a constructed
  edge composes. `maxPubdata` and the hash function are arbitrary as well.
* **Reject-only checks not listed are omitted** (the time gate, the settlement-layer order check,
  the verifier, batch contents, callers, the migration's other preconditions, and that migrations
  are disabled at `b17415d20`: `CHAIN_MIGRATIONS_ENABLED = false`, `common/Config.sol:320`). Omitting
  a check only adds runs, and the results here are about all runs.
* **Batch counters are not modelled**: a commit records any positive batch number, an execute may
  or may not reach `b`, and a revert may or may not reach below it.
* **Not modelled**: break-glass cuts (`Admin.executeUpgrade`), whose init code is arbitrary;
  upgrade engines older than `b17415d20`, which a chain's history before the model's start state
  ran.
-/

namespace Contracts.ChainTypeManager.EdgeChecks

/-! ## The genesis version step -/

/-- `BaseZkSyncUpgradeGenesis._setNewProtocolVersion(_newProtocolVersion, _isOnSettlementLayer)`
(`upgrades/BaseZkSyncUpgradeGenesis.sol:25-82`):

    if (_newProtocolVersion < previousProtocolVersion) { revert ProtocolVersionTooSmall(...); }  // :32-35
    ... unpack both, both majors zero ...                                                       // :37-50
    uint256 minorDelta = newMinorVersion - previousMinorVersion;                                 // :52
    patchOnly = false;                                                                           // :55
    if (minorDelta > MAX_ALLOWED_MINOR_VERSION_DELTA) { revert ProtocolVersionDeltaTooLarge(...); } // :58-60
    if (!_isOnSettlementLayer) { revert GenesisUpgradeExpectedOnSettlementLayer(); }             // :62-64
    if (!patchOnly) { h != 0 or b != 0 → revert }                                                // :69-78
    s.protocolVersion = _newProtocolVersion;                                                     // :80 -/
def setNewProtocolVersionGenesis (c : ChainUpgradeState) (newV : ℕ) (onSL : Bool) :
    Option (ℕ × Bool × ChainUpgradeState) :=
  if newV < c.pv then none else
  match unpackChecked c.pv, unpackChecked newV with
  | some (pM, pm, _), some (nM, nm, _) =>
    if pM ≠ 0 then none else
    if nM ≠ 0 then none else
    if nm < pm then none else
    if MAX_ALLOWED_MINOR_VERSION_DELTA < nm - pm then none else
    if onSL = false then none else
    if c.h ≠ 0 ∨ c.b ≠ 0 then none else
    some (nm, false, { c with pv := newV })
  | _, _ => none

/-- The storage part of `L1GenesisUpgrade.genesisUpgrade` (`upgrades/L1GenesisUpgrade.sol:31-47`):
`_upgrade(s.protocolVersion, 0, address(0), tx)` on the settlement layer, with the genesis version
step, then `_setL2SystemContractUpgrade` (`BaseZkSyncUpgrade.sol:96, :103-105`). -/
def genesisStoragePart (H : L2Tx → ℕ) (c : ChainUpgradeState) (maxPubdata : ℕ) (tx : L2Tx) :
    Option (ℕ × ChainUpgradeState) :=
  match setNewProtocolVersionGenesis c c.pv true with
  | none => none
  | some (m, p, c1) => setL2SystemContractUpgrade H c1 maxPubdata tx m p

/-! ## State -/

/-- One diamond of the chain. -/
structure NonceDiamond where
  /-- `s.protocolVersion`, `s.l2SystemContractsUpgradeTxHash`, `s.l2SystemContractsUpgradeBatchNumber`. -/
  st : ChainUpgradeState
  /-- `s.settlementLayer == address(0)`. -/
  onSL : Bool
deriving DecidableEq

/-- A migration in flight: the source diamond and the commitment `forwardedBridgeBurn` recorded,
with the version it was at (`Migrator.sol:192-198, :208, :343-344`). -/
structure NonceMigration where
  /-- The source diamond. -/
  src : ℕ
  /-- The recorded `l2SystemContractsUpgradeTxHash`. -/
  h : ℕ
  /-- The recorded `l2SystemContractsUpgradeBatchNumber`. -/
  b : ℕ
  /-- The source's version at the burn. -/
  pv : ℕ
deriving DecidableEq

/-- One chain: its diamonds by settlement layer, the migration in flight, and the ghost log of
transactions whose hash was written to `h`. -/
structure NonceSys where
  /-- The chain's diamond on each settlement layer. -/
  dia : ℕ → Option NonceDiamond
  /-- The migration in flight. -/
  pending : Option NonceMigration
  /-- Ghost: every transaction written to `h` by a genesis or a crossing, in order. -/
  log : List L2Tx

/-- A chain before `createNewChain`: no diamond, nothing in flight, nothing written. -/
def nonceInit : NonceSys := ⟨fun _ => none, none, []⟩

/-! ## Steps -/

/-- The writers of a chain's pending upgrade transaction. -/
inductive NonceLabel
  /-- `createNewChain` at version `v0` on settlement layer `d`, with genesis transaction `tx`. -/
  | genesis (d v0 maxPubdata : ℕ) (tx : L2Tx)
  /-- A crossing to `newV` on the diamond on its settlement layer `d`, carrying `tx`. -/
  | cross (d newV maxPubdata : ℕ) (tx : L2Tx)
  /-- A crossing to `newV` on a diamond `d` off its settlement layer. -/
  | crossOff (d newV : ℕ)
  /-- `commitBatchesSharedBridge` of batch `n` on `d`. -/
  | commitBatch (d n : ℕ)
  /-- `executeBatchesSharedBridge` on `d` up to `e` executed batches. -/
  | executeBatches (d e : ℕ)
  /-- `revertBatchesSharedBridge` on `d` to new last batch `k`. -/
  | revertBatches (d k : ℕ)
  /-- `forwardedBridgeBurn` on `d`. -/
  | burn (d : ℕ)
  /-- `forwardedBridgeMint` onto settlement layer `d`. -/
  | mint (d : ℕ)
  /-- `forwardedBridgeConfirmTransferResult` with a failure. -/
  | restore

/-- The batch-side writes, on `(h, b)`:

    bool processSystemUpgradeTx = systemContractsUpgradeTxHash != bytes32(0) &&
        s.l2SystemContractsUpgradeBatchNumber == 0;                                // Committer.sol:105-107
    s.l2SystemContractsUpgradeBatchNumber = _newBatchesData[0].batchNumber;        // Committer.sol:127 -/
def commitBatchState (c : ChainUpgradeState) (n : ℕ) : ChainUpgradeState :=
  if c.h ≠ 0 ∧ c.b = 0 then { c with b := n } else c

/-- `if (batchWhenUpgradeHappened != 0 && batchWhenUpgradeHappened <= newTotalBatchesExecuted)
{ delete s.l2SystemContractsUpgradeTxHash; delete s.l2SystemContractsUpgradeBatchNumber; }`
(`Executor.sol:206-211`). -/
def executeBatchesState (c : ChainUpgradeState) (e : ℕ) : ChainUpgradeState :=
  if c.b ≠ 0 ∧ c.b ≤ e then { c with h := 0, b := 0 } else c

/-- `if (s.l2SystemContractsUpgradeBatchNumber > _newLastBatch) { delete
s.l2SystemContractsUpgradeBatchNumber; }` (`ZKChainBase.sol:332-334`). -/
def revertBatchesState (c : ChainUpgradeState) (k : ℕ) : ChainUpgradeState :=
  if k < c.b then { c with b := 0 } else c

/-- The log after a step that ran `_setL2SystemContractUpgrade` with `tx`: the transaction is
logged exactly when it was written (`txType != 0`, `BaseZkSyncUpgrade.sol:168-170, :199`). -/
def logWrite (log : List L2Tx) (tx : L2Tx) : List L2Tx :=
  if tx.txType = 0 then log else log ++ [tx]

/-- One successful step. `H` is `keccak256(abi.encode(tx))`. -/
inductive NonceStep (H : L2Tx → ℕ) : NonceSys → NonceLabel → NonceSys → Prop
  /-- Genesis on a chain with no diamond: `DiamondInit` at `v0` on fresh storage, then the genesis
  storage part. -/
  | genesis {s : NonceSys} {d v0 maxPubdata : ℕ} {tx : L2Tx} {hsh : ℕ} {c' : ChainUpgradeState} :
      (∀ d', s.dia d' = none) → s.pending = none →
      genesisStoragePart H ⟨v0, 0, 0⟩ maxPubdata tx = some (hsh, c') →
      NonceStep H s (.genesis d v0 maxPubdata tx)
        { s with dia := upd s.dia d (some ⟨c', true⟩), log := logWrite s.log tx }
  /-- A crossing on the settlement layer: the storage part of `_upgrade` with `onSL = true`. -/
  | cross {s : NonceSys} {d newV maxPubdata : ℕ} {tx : L2Tx} {c c' : ChainUpgradeState} {hsh : ℕ} :
      s.dia d = some ⟨c, true⟩ →
      upgradeStoragePart H c maxPubdata newV tx true = some (hsh, c') →
      NonceStep H s (.cross d newV maxPubdata tx)
        { s with dia := upd s.dia d (some ⟨c', true⟩), log := logWrite s.log tx }
  /-- A crossing off the settlement layer: the version step with `onSL = false`. -/
  | crossOff {s : NonceSys} {d newV : ℕ} {c c' : ChainUpgradeState} {m : ℕ} {p : Bool} :
      s.dia d = some ⟨c, false⟩ →
      setNewProtocolVersion c newV false = some (m, p, c') →
      NonceStep H s (.crossOff d newV) { s with dia := upd s.dia d (some ⟨c', false⟩) }
  /-- A commit (`Committer.sol:105-108, :118-128`) of batch `n > 0`. -/
  | commitBatch {s : NonceSys} {d n : ℕ} {c : ChainUpgradeState} :
      s.dia d = some ⟨c, true⟩ → n ≠ 0 →
      NonceStep H s (.commitBatch d n)
        { s with dia := upd s.dia d (some ⟨commitBatchState c n, true⟩) }
  /-- An execution (`Executor.sol:207-211`) reaching `e` executed batches. -/
  | executeBatches {s : NonceSys} {d e : ℕ} {c : ChainUpgradeState} :
      s.dia d = some ⟨c, true⟩ →
      NonceStep H s (.executeBatches d e)
        { s with dia := upd s.dia d (some ⟨executeBatchesState c e, true⟩) }
  /-- A revert (`ZKChainBase.sol:332-334`) to new last batch `k`. -/
  | revertBatches {s : NonceSys} {d k : ℕ} {c : ChainUpgradeState} :
      s.dia d = some ⟨c, true⟩ →
      NonceStep H s (.revertBatches d k)
        { s with dia := upd s.dia d (some ⟨revertBatchesState c k, true⟩) }
  /-- `forwardedBridgeBurn` on the diamond on its settlement layer. -/
  | burn {s : NonceSys} {d : ℕ} {c : ChainUpgradeState} :
      s.dia d = some ⟨c, true⟩ → s.pending = none →
      NonceStep H s (.burn d)
        { s with dia := upd s.dia d (some ⟨c, false⟩), pending := some ⟨d, c.h, c.b, c.pv⟩ }
  /-- `forwardedBridgeMint` onto a diamond deployed for it, at the version handed over. -/
  | mintFresh {s : NonceSys} {d : ℕ} {p : NonceMigration} :
      s.pending = some p → s.dia d = none →
      NonceStep H s (.mint d)
        { s with dia := upd s.dia d (some ⟨⟨p.pv, p.h, p.b⟩, true⟩), pending := none }
  /-- `forwardedBridgeMint` onto an existing diamond off its settlement layer, at its own version. -/
  | mintExisting {s : NonceSys} {d : ℕ} {p : NonceMigration} {c : ChainUpgradeState} :
      s.pending = some p → d ≠ p.src → s.dia d = some ⟨c, false⟩ →
      NonceStep H s (.mint d)
        { s with dia := upd s.dia d (some ⟨{ c with h := p.h, b := p.b }, true⟩), pending := none }
  /-- `forwardedBridgeConfirmTransferResult` with a failure: the source returns to its settlement
  layer if it is at the version it left with. -/
  | restore {s : NonceSys} {p : NonceMigration} {c : ChainUpgradeState} :
      s.pending = some p → s.dia p.src = some ⟨c, false⟩ → c.pv = p.pv →
      NonceStep H s .restore
        { s with dia := upd s.dia p.src (some ⟨c, true⟩), pending := none }

/-- A run whose every step satisfies `P` at the state it leaves. -/
inductive NonceRunWith (H : L2Tx → ℕ) (P : NonceSys → NonceLabel → Prop) :
    NonceSys → List NonceLabel → NonceSys → Prop
  | nil {s : NonceSys} : NonceRunWith H P s [] s
  | cons {s s' s'' : NonceSys} {l : NonceLabel} {ls : List NonceLabel} :
      P s l → NonceStep H s l s' → NonceRunWith H P s' ls s'' → NonceRunWith H P s (l :: ls) s''

/-- Any run. -/
def NonceRun (H : L2Tx → ℕ) : NonceSys → List NonceLabel → NonceSys → Prop :=
  NonceRunWith H (fun _ _ => True)

/-- A migration onto an existing diamond lands at a version no lower than the source's: the
destination CTM's version is not behind the source CTM's. The fresh-destination path enforces
equality (`ChainTypeManager.sol:733-740, :752-756`); for an existing destination this is a
premise. -/
def MintLandsNotBehind (s : NonceSys) : NonceLabel → Prop
  | .mint d => ∀ p c, s.pending = some p → s.dia d = some ⟨c, false⟩ → p.pv ≤ c.pv
  | _ => True

/-- A migration onto an existing diamond lands at exactly the version it left with. -/
def MintLandsExactly (s : NonceSys) : NonceLabel → Prop
  | .mint d => ∀ p c, s.pending = some p → s.dia d = some ⟨c, false⟩ → p.pv = c.pv
  | _ => True

/-- The labels other than a genesis and a crossing on the settlement layer. -/
def NonceLabel.KeepsVersionLabel : NonceLabel → Prop
  | .genesis _ _ _ _ => False
  | .cross _ _ _ _ => False
  | _ => True

/-- `v` is the chain's live version: the version of a diamond on its settlement layer, or the
version a migration in flight left with. A name for the results. -/
def ActiveVersion (s : NonceSys) (v : ℕ) : Prop :=
  (∃ d c, s.dia d = some ⟨c, true⟩ ∧ c.pv = v) ∨ (∃ p, s.pending = some p ∧ p.pv = v)

/-! ## The invariant -/

/-- What every reachable state keeps. -/
structure NonceInv (s : NonceSys) : Prop where
  /-- Every diamond's version is well formed. -/
  wf : ∀ d x, s.dia d = some x → VersionWf x.st.pv
  /-- The migration in flight recorded a well-formed version. -/
  pendingWf : ∀ p, s.pending = some p → VersionWf p.pv
  /-- Every logged nonce is at most the minor of the diamond on its settlement layer. -/
  slBound : ∀ d c, s.dia d = some ⟨c, true⟩ → ∀ tx ∈ s.log, tx.nonce ≤ minorOf c.pv
  /-- Every logged nonce is at most the minor of the version a migration in flight left with. -/
  pendingBound : ∀ p, s.pending = some p → ∀ tx ∈ s.log, tx.nonce ≤ minorOf p.pv
  /-- At most one diamond is on its settlement layer. -/
  slUnique : ∀ d d' c c', s.dia d = some ⟨c, true⟩ → s.dia d' = some ⟨c', true⟩ → d = d'
  /-- While a migration is in flight no diamond is on its settlement layer. -/
  pendingNoSL : ∀ p, s.pending = some p → ∀ d c, s.dia d ≠ some ⟨c, true⟩
  /-- Before any diamond exists nothing is logged. -/
  emptyNoLog : (∀ d, s.dia d = none) → s.log = []
  /-- The logged nonces strictly increase. -/
  sorted : s.log.Pairwise (fun a b => a.nonce < b.nonce)

/-- Two logged transactions with the same `keccak256(abi.encode(tx))` that are different
transactions: a collision of the hash on two inputs the run itself names. -/
def TxHashCollision (H : L2Tx → ℕ) (a b : L2Tx) : Prop := a ≠ b ∧ H a = H b

/-! ## Witness data -/

/-- A transaction with the upgrade envelope, nonce `n` and the given calldata, as
`L2CanonicalTransactionLib.upgradeTransaction` composes it for version `0.n.0`
(`L2CanonicalTransactionLib.sol:50-62`). -/
def wUpgradeTx (n : ℕ) (calldata : Bytes) : L2Tx := upgradeTransaction (n * 2 ^ 32) calldata

/-- `0.31.0`. -/
def v31 : ℕ := 31 * 2 ^ 32

/-- The witness run: genesis at `0.29.0` on layer `0`; the batch carrying the genesis transaction
is committed and executed; a migration to a fresh diamond on layer `1`; a crossing there to
`0.30.0` with an L2 transaction; the layer-`0` diamond crosses off its settlement layer to
`0.30.0` and to `0.30.1`; a patch crossing to `0.30.1` on layer `1` while the transaction is
pending; a commit, a revert of that batch, a recommit and an execution; a migration back onto the
existing layer-`0` diamond, at the same version; a crossing to `0.31.0`; a commit and an execution;
a burn and a failed migration's restore. -/
def wNonceRun : List NonceLabel :=
  [.genesis 0 v29 99000 (wUpgradeTx 29 [9]),
   .commitBatch 0 1, .executeBatches 0 1,
   .burn 0, .mint 1,
   .cross 1 v30 99000 (wUpgradeTx 30 [1]),
   .crossOff 0 v30, .crossOff 0 v30p1,
   .cross 1 v30p1 99000 emptyL2CanonicalTransaction,
   .commitBatch 1 5, .revertBatches 1 4, .commitBatch 1 6, .executeBatches 1 6,
   .burn 1, .mint 0,
   .cross 0 v31 99000 (wUpgradeTx 31 [2]),
   .commitBatch 0 7, .executeBatches 0 7,
   .burn 0, .restore]

/-- The skip run: genesis at `0.29.0` on layer `0`, its batch committed and executed, a migration
to a fresh diamond on layer `1`, the layer-`0` diamond crossing to `0.30.0` off its settlement
layer, and a migration back onto it. -/
def wSkipRun : List NonceLabel :=
  [.genesis 0 v29 99000 (wUpgradeTx 29 [9]),
   .commitBatch 0 1, .executeBatches 0 1,
   .burn 0, .mint 1,
   .crossOff 0 v30,
   .burn 1, .mint 0]

/-- A run from the state after genesis at `0.29.0` with no genesis and no crossing on the
settlement layer: the genesis transaction's batch committed, reverted, committed again and
executed; a migration to a fresh diamond on layer `1`; a migration back onto the existing layer-`0`
diamond, at the version it left with; a burn and a failed migration's restore. -/
def wExactRun : List NonceLabel :=
  [.commitBatch 0 1, .revertBatches 0 0, .commitBatch 0 2, .executeBatches 0 2,
   .burn 0, .mint 1,
   .burn 1, .mint 0,
   .burn 0, .restore]

/-- The countermodel run: genesis at `0.29.0` on layer `0`, its batch committed and executed, a
migration to a fresh diamond on layer `1`, a crossing there to `0.30.0` with transaction
`wUpgradeTx 30 [1]`, its batch committed and executed, and a migration back onto the layer-`0`
diamond, still at `0.29.0`, which then crosses to `0.30.0` with the same transaction. -/
def wLaggingRun : List NonceLabel :=
  [.genesis 0 v29 99000 (wUpgradeTx 29 [9]),
   .commitBatch 0 1, .executeBatches 0 1,
   .burn 0, .mint 1,
   .cross 1 v30 99000 (wUpgradeTx 30 [1]),
   .commitBatch 1 2, .executeBatches 1 2,
   .burn 1, .mint 0,
   .cross 0 v30 99000 (wUpgradeTx 30 [1])]

end Contracts.ChainTypeManager.EdgeChecks
