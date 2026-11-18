import EraSpec.Contracts.ChainTypeManager.Specs.CommittedEdgeExecutable

/-!
# Properties: the commit-time edge checks imply the chain-side upgrade checks

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.CommittedEdgeExecutable` (pin
`b17415d20`). Proofs are in `EraSpec.Contracts.ChainTypeManager.Proofs.CommittedEdgeExecutable`.
Namespace `Contracts.ChainTypeManager.EdgeChecks`.

## The two copies agree

* **Version shape.** `requireValidEdge` returns exactly when the edge has `EdgeVersionShape`, a
  nonzero deadline no earlier than the upgrade time, and no L2 side on a patch.
  `_setNewProtocolVersion` succeeds exactly when the edge from the chain's version has
  `EdgeVersionShape` and, on the settlement layer for a minor change, nothing is pending; its
  `patchOnly` is "the minors are equal" (`EdgeShapeIsTheChainVersionCheck`).
* **The L2 side.** For a plan `build` returned, the composer returns the empty transaction, and a
  transaction of type `0`, exactly when the plan deploys nothing, which is the constructor's
  `hasL2Side` test; such a plan has no delegate (`ComposerEmptinessIsHasL2Side`). No hash premise.
* **The composed transaction.** For a constructed edge with an L2 side the edge is not a patch, and
  the composed transaction has the upgrade type, nonce `minor(new)`, the plan's factory
  dependencies (at most `MAX_NEW_FACTORY_DEPS`), the canonical envelope
  `validateUpgradeTransaction` accepts, gas limit `UPGRADE_TX_MAX_GAS_LIMIT` and gas per pubdata
  `REQUIRED_L2_GAS_PRICE_PER_PUBDATA` (`ConstructedEdgeChainFacts`).

## Headline

* `ConstructedEdgePassesChainChecks`: a constructed edge, on a chain at its departing version on
  its settlement layer, with nothing pending if the minor changes, a `priorityTxMaxPubdata` of at
  least `72_000_000 / 800 = 90_000`, and composed calldata within the intrinsic-gas bound, passes
  `_setNewProtocolVersion` and `_setL2SystemContractUpgrade`, with the results stated exactly.
* `CommittedSlotEdgePassesChainChecks`: the same for whatever a CTM run leaves in slot `v`, on a
  chain at `v`, when the run's replacements are genuine (they report their departing release's
  version, as every `CTMTransition` does) and the slot's object is a constructed edge whose
  getters report its construction.
* `ConstructedEdgePassesOffLayerVersionStep`: a chain at the departing version off its settlement
  layer passes the version step whatever is pending, and writes no transaction.
* `PublishedFactoryDepsStayPublished`: what `requirePublished` checked at commit stays published
  along any run of supplier publications.

## The premises are needed

* `PubdataLimitThresholdIsExact`: with `priorityTxMaxPubdata = 89_999` the witness edge's L2 step
  reverts; with `90_000` it passes.
* `CalldataBoundIsExact`: the witness edge's L2 step passes with composer output of `1_799_375`
  bytes and reverts with `1_799_376` (the encoding adds 100 bytes; the bound is `1_799_475`).
  Nothing at commit time bounds this length.
* `NonGenuineSlotEdgeRevertsOnChain`: a CTM run whose replacement reports a departure other than
  its slot leaves a constructed edge in slot `0.29.0` on which every chain at `0.29.0` reverts, on
  or off its settlement layer (minor delta 101).
* `UnbuiltPlanBreaksEmptinessAgreement`: for a plan `build` never returns (no deployments, a
  nonzero `delegateTo`) the constructor's `hasL2Side` is false, so a patch edge passes
  `requireValidEdge`, but the composer's transaction is not empty and the chain reverts.
* `SupplierSwapClearsPublication`: an implementation swap of the supplier proxy can clear a
  publication that `requirePublished` checked.
-/

namespace Contracts.ChainTypeManager.EdgeChecks

/-! ## The two copies agree -/

/-- **THE EDGE'S VERSION CHECK IS THE CHAIN'S VERSION CHECK.** `requireValidEdge` returns exactly
when the edge has `EdgeVersionShape` (the version increases, both versions fit a `uint96` with
major `0`, and the minor moves forward by at most 100), the deadline is nonzero and not before the
upgrade time, and a patch (equal minors) has no L2 side. `_setNewProtocolVersion` succeeds exactly
when the edge from the chain's current version has `EdgeVersionShape` and, for a minor change on
the settlement layer, no L2 upgrade is pending (`h = b = 0`); it then returns the new minor,
`patchOnly` = "the minors are equal", and the state with the new version. -/
def Properties.EdgeShapeIsTheChainVersionCheck : Prop :=
  (∀ (old new deadline upgradeTs : ℕ) (hasL2Side : Bool),
    requireValidEdge old new deadline upgradeTs hasL2Side = some () ↔
      EdgeVersionShape old new ∧ deadline ≠ 0 ∧ upgradeTs ≤ deadline ∧
        ¬ (minorOf old = minorOf new ∧ hasL2Side = true)) ∧
  (∀ (c : ChainUpgradeState) (newV : ℕ) (onSL : Bool) (r : ℕ × Bool × ChainUpgradeState),
    setNewProtocolVersion c newV onSL = some r ↔
      EdgeVersionShape c.pv newV ∧
        (minorOf newV ≠ minorOf c.pv → onSL = true → c.h = 0 ∧ c.b = 0) ∧
        r = (minorOf newV, decide (minorOf newV = minorOf c.pv), { c with pv := newV }))

/-- **THE COMPOSER'S EMPTINESS TEST IS THE CONSTRUCTOR'S `hasL2Side`.** For any plan `build`
returned and any version and composer answer, `buildL2UpgradeTxFromPlan` returns the empty
transaction exactly when the plan deploys nothing, and likewise a transaction of type `0`; a plan
that deploys nothing has `delegateTo = 0`. No hash premise. -/
def Properties.ComposerEmptinessIsHasL2Side : Prop :=
  ∀ (E : PlanEnv) (derived : List Deployment) (a : AuthoredL2Plan) (plan : L2UpgradePlan)
    (v : ℕ) (composed : Bytes),
    planBuild E derived a = some plan →
      (buildL2UpgradeTxFromPlan E plan v composed = emptyL2CanonicalTransaction ↔
        plan.deployments = []) ∧
      ((buildL2UpgradeTxFromPlan E plan v composed).txType = 0 ↔ plan.deployments = []) ∧
      (plan.deployments = [] → plan.delegateTo = 0)

/-- **WHAT A CONSTRUCTED EDGE FIXES FOR EVERY CHAIN.** For a constructed edge `o` with stored plan
`plan` and any composer answer: the edge has `EdgeVersionShape`; the composed transaction is empty
(and of type `0`) exactly when the plan deploys nothing; and when the plan deploys something the
edge is not a patch and the composed transaction has type `ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE`,
nonce `minor(new)`, factory dependencies `plan.factoryDepHashes` with at most
`MAX_NEW_FACTORY_DEPS` entries, an envelope `validateUpgradeTransaction` accepts, gas limit
`UPGRADE_TX_MAX_GAS_LIMIT`, and gas per pubdata `REQUIRED_L2_GAS_PRICE_PER_PUBDATA`. -/
def Properties.ConstructedEdgeChainFacts : Prop :=
  ∀ (E : PlanEnv) (o : EdgeObject) (plan : L2UpgradePlan) (composed : Bytes),
    Constructed E o plan →
      EdgeVersionShape o.old o.new ∧
      ((composedTx E o plan composed).txType = 0 ↔ plan.deployments = []) ∧
      (composedTx E o plan composed = emptyL2CanonicalTransaction ↔ plan.deployments = []) ∧
      (plan.deployments ≠ [] →
        minorOf o.new ≠ minorOf o.old ∧
        (composedTx E o plan composed).txType = ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE ∧
        (composedTx E o plan composed).nonce = minorOf o.new ∧
        (composedTx E o plan composed).factoryDeps = plan.factoryDepHashes ∧
        plan.factoryDepHashes.length ≤ MAX_NEW_FACTORY_DEPS ∧
        validateUpgradeTransaction (composedTx E o plan composed) = true ∧
        (composedTx E o plan composed).gasLimit = UPGRADE_TX_MAX_GAS_LIMIT ∧
        (composedTx E o plan composed).gasPerPubdataByteLimit = REQUIRED_L2_GAS_PRICE_PER_PUBDATA)

/-! ## Headline -/

/-- **A CONSTRUCTED EDGE PASSES BOTH CHAIN-SIDE STEPS.** Let `o` be a constructed edge with stored
plan `plan`, and let a chain on its settlement layer be at `o`'s departing version, with no L2
upgrade pending if the edge changes the minor version, with `priorityTxMaxPubdata` at least
`UPGRADE_TX_MAX_GAS_LIMIT / REQUIRED_L2_GAS_PRICE_PER_PUBDATA` (`90_000`), and with the composed
calldata within `UpgradeCalldataFits`. Then `_setNewProtocolVersion(new, true)` returns
`(minor(new), patchOnly, state at new)` with `patchOnly` = "the minors are equal", and
`_setL2SystemContractUpgrade(tx, minor(new), patchOnly)` returns `(0, unchanged)` when the plan
deploys nothing and otherwise writes and returns `keccak256(abi.encode(tx))`. The time gate, the
settlement-layer order check and the verifier of `_upgrade` are not covered. -/
def Properties.ConstructedEdgePassesChainChecks : Prop :=
  ∀ (E : PlanEnv) (o : EdgeObject) (plan : L2UpgradePlan) (c : ChainUpgradeState)
    (maxPubdata : ℕ) (composed : Bytes),
    Constructed E o plan → c.pv = o.old →
    (minorOf o.new ≠ minorOf o.old → c.h = 0 ∧ c.b = 0) →
    UPGRADE_TX_MAX_GAS_LIMIT / REQUIRED_L2_GAS_PRICE_PER_PUBDATA ≤ maxPubdata →
    UpgradeCalldataFits (composedTx E o plan composed) →
      setNewProtocolVersion c o.new true =
          some (minorOf o.new, decide (minorOf o.new = minorOf o.old), { c with pv := o.new }) ∧
      setL2SystemContractUpgrade E.txHash { c with pv := o.new } maxPubdata
          (composedTx E o plan composed) (minorOf o.new) (decide (minorOf o.new = minorOf o.old)) =
        some (if plan.deployments = [] then (0, { c with pv := o.new })
              else (E.txHash (composedTx E o plan composed),
                { c with pv := o.new, h := E.txHash (composedTx E o plan composed) })) ∧
      upgradeStoragePart E.txHash c maxPubdata o.new (composedTx E o plan composed) true =
        some (if plan.deployments = [] then (0, { c with pv := o.new })
              else (E.txHash (composedTx E o plan composed),
                { c with pv := o.new, h := E.txHash (composedTx E o plan composed) }))

/-- **OFF ITS SETTLEMENT LAYER, A CHAIN AT THE DEPARTURE PASSES THE VERSION STEP WHATEVER IS
PENDING.** For a constructed edge and a chain at its departing version off its settlement layer,
`_setNewProtocolVersion(new, false)` returns `(minor(new), patchOnly, state at new)` and the
storage part of `_upgrade` writes no transaction, for any pending `(h, b)`, any
`priorityTxMaxPubdata` and any transaction. (`_upgrade`'s settlement-layer order check, which
reads the settlement layer's version, is not covered.) -/
def Properties.ConstructedEdgePassesOffLayerVersionStep : Prop :=
  ∀ (E : PlanEnv) (o : EdgeObject) (plan : L2UpgradePlan) (c : ChainUpgradeState)
    (maxPubdata : ℕ) (tx : L2Tx),
    Constructed E o plan → c.pv = o.old →
      setNewProtocolVersion c o.new false =
          some (minorOf o.new, decide (minorOf o.new = minorOf o.old), { c with pv := o.new }) ∧
      upgradeStoragePart E.txHash c maxPubdata o.new tx false = some (0, { c with pv := o.new })

/-- **WHATEVER A CTM RUN COMMITS TO SLOT `v` PASSES BOTH CHAIN-SIDE STEPS ON A CHAIN AT `v`.** Take
a CTM run (`Specs/VersionRegistry.lean`'s `CRun`) from a state satisfying `CtmInv` whose committed
slots report their own version as departure, in which every replacement reports its departing
release's version (as every `CTMTransition` does, `CTMTransition.sol:61-64`). Let slot `v` hold
`t` at the end, whose object is a constructed edge with stored plan, and whose
`oldProtocolVersion()`/`newProtocolVersion()` getters report that construction. Then on a chain at
`v` on its settlement layer, with nothing pending if the minor changes, `priorityTxMaxPubdata` at
least `90_000` and composed calldata within `UpgradeCalldataFits`, the storage part of `_upgrade`
succeeds and lands the chain on `t`'s target version. -/
def Properties.CommittedSlotEdgePassesChainChecks : Prop :=
  ∀ (W : World) (E : PlanEnv) (EW : EdgeWorld) (s s' : CTM) (ops : List Op),
    CtmInv W s → (∀ v, s.ut v ≠ 0 → (W.tr (s.ut v)).old = v) →
    (∀ e r, Op.replace e r ∈ ops → (W.tr r).old = W.relVersion (W.tr r).fromRel) →
    CRun W s ops s' →
    ∀ v, s'.ut v ≠ 0 →
      Constructed E (EW.obj (s'.ut v)) (EW.plan (s'.ut v)) → EW.Reports W (s'.ut v) →
    ∀ (c : ChainUpgradeState) (maxPubdata : ℕ) (composed : Bytes), c.pv = v →
      (minorOf (W.tr (s'.ut v)).new ≠ minorOf v → c.h = 0 ∧ c.b = 0) →
      UPGRADE_TX_MAX_GAS_LIMIT / REQUIRED_L2_GAS_PRICE_PER_PUBDATA ≤ maxPubdata →
      UpgradeCalldataFits (composedTx E (EW.obj (s'.ut v)) (EW.plan (s'.ut v)) composed) →
      ∃ hsh c', upgradeStoragePart E.txHash c maxPubdata (W.tr (s'.ut v)).new
          (composedTx E (EW.obj (s'.ut v)) (EW.plan (s'.ut v)) composed) true = some (hsh, c') ∧
        c'.pv = (W.tr (s'.ut v)).new

/-- **A CHECKED PUBLICATION STAYS PUBLISHED WHILE THE SUPPLIER'S CODE STAYS.** If every hash of a
list is published (`requirePublished`, as the commit checked), it still is after any run of
supplier steps that are all publications. -/
def Properties.PublishedFactoryDepsStayPublished : Prop :=
  ∀ (s s' : Supplier) (ops : List SupplierOp) (hashes : List ℕ),
    requirePublished s hashes → SupplierRun s ops s' → (∀ op ∈ ops, op.IsPublish) →
      requirePublished s' hashes

/-! ## The premises are needed -/

/-- **THE PUBDATA PREMISE IS EXACT.** The witness edge `wEdge` (`0.29.0 → 0.30.0`, with an L2
side) is constructed with plan `wPlan`, and its composed transaction for an empty composer answer
fits the calldata bound. On the clean chain at `0.29.0`, the storage part of `_upgrade` reverts
when `priorityTxMaxPubdata = 89_999` (`PubdataGreaterThanLimit`) and succeeds when it is
`90_000`. -/
def Properties.PubdataLimitThresholdIsExact : Prop :=
  Constructed wEnv wEdge wPlan ∧ UpgradeCalldataFits (composedTx wEnv wEdge wPlan []) ∧
    upgradeStoragePart wEnv.txHash ⟨v29, 0, 0⟩ 89999 v30 (composedTx wEnv wEdge wPlan []) true =
      none ∧
    ∃ r, upgradeStoragePart wEnv.txHash ⟨v29, 0, 0⟩ 90000 v30 (composedTx wEnv wEdge wPlan [])
      true = some r

/-- **THE CALLDATA PREMISE IS EXACT, AND NOTHING AT COMMIT TIME CHECKS IT.** The witness edge
`wEdge` is constructed with plan `wPlan`; its composed calldata is 100 bytes plus the composer's
answer. On the clean chain at `0.29.0` with `priorityTxMaxPubdata = 99_000` (the default,
`common/Config.sol:291`), the storage part of `_upgrade` succeeds for a 1_799_375-byte composer
answer and reverts for a 1_799_376-byte one (`ValidateTxnNotEnoughGas`), whose transaction is
not `UpgradeCalldataFits`. -/
def Properties.CalldataBoundIsExact : Prop :=
  Constructed wEnv wEdge wPlan ∧
    UpgradeCalldataFits (composedTx wEnv wEdge wPlan (List.replicate 1799375 0)) ∧
    (∃ r, upgradeStoragePart wEnv.txHash ⟨v29, 0, 0⟩ 99000 v30
      (composedTx wEnv wEdge wPlan (List.replicate 1799375 0)) true = some r) ∧
    ¬ UpgradeCalldataFits (composedTx wEnv wEdge wPlan (List.replicate 1799376 0)) ∧
    upgradeStoragePart wEnv.txHash ⟨v29, 0, 0⟩ 99000 v30
      (composedTx wEnv wEdge wPlan (List.replicate 1799376 0)) true = none

/-- **WITHOUT GENUINE REPLACEMENTS, A COMMITTED SLOT CAN REVERT ON EVERY CHAIN AT ITS VERSION.** In
`wEdgeWorld`, the CTM run "commit `300` (`0.29.0 → 0.30.0`), commit `600` (`0.30.0 → 0.130.0`),
replace `300` by `500`" succeeds from `initialize` with release `100`. Transition `500` departs
from release `100` (version `0.29.0`) but reports `oldProtocolVersion() = 0.100.0`. Its object
`wFarEdge` (`0.100.0 → 0.130.0`, no L2 side) is constructed, and its getters report it. Slot
`0.29.0` now holds `500`, and for every chain at `0.29.0`, on or off its settlement layer, with any
pending state, `priorityTxMaxPubdata` and transaction, the storage part of `_upgrade` towards
`500`'s target reverts: the minor moves by 101. -/
def Properties.NonGenuineSlotEdgeRevertsOnChain : Prop :=
  ∃ s', CRun wEdgeWorld (initState wEdgeWorld 100) [.commit 300, .commit 600, .replace 300 500] s' ∧
    s'.ut v29 = 500 ∧
    Constructed wEnv (wEdgeObjs.obj 500) (wEdgeObjs.plan 500) ∧
    EdgeWorld.Reports wEdgeWorld wEdgeObjs 500 ∧
    (wEdgeWorld.tr 500).old ≠ wEdgeWorld.relVersion (wEdgeWorld.tr 500).fromRel ∧
    ∀ (c : ChainUpgradeState) (maxPubdata : ℕ) (tx : L2Tx) (onSL : Bool), c.pv = v29 →
      upgradeStoragePart wEnv.txHash c maxPubdata (wEdgeWorld.tr 500).new tx onSL = none

/-- **THE EMPTINESS AGREEMENT NEEDS `build`'S SHAPE CHECKS.** No `build` call returns
`wUnbuiltPlan` (no deployments, `delegateTo = 0x1234`). For it the constructor's `hasL2Side` is
false, so the patch edge `0.30.0 → 0.30.1` passes `requireValidEdge`; but the composer's
transaction has the upgrade type, and on a clean chain at `0.30.0` the storage part of `_upgrade`
reverts (`PatchCantSetUpgradeTxn`). -/
def Properties.UnbuiltPlanBreaksEmptinessAgreement : Prop :=
  (∀ (E : PlanEnv) (derived : List Deployment) (a : AuthoredL2Plan),
    planBuild E derived a ≠ some wUnbuiltPlan) ∧
    requireValidEdge v30 v30p1 100 50 (decide (wUnbuiltPlan.deployments.length ≠ 0)) = some () ∧
    (buildL2UpgradeTxFromPlan wEnv wUnbuiltPlan v30p1 []).txType =
      ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE ∧
    upgradeStoragePart wEnv.txHash ⟨v30, 0, 0⟩ 99000 v30p1
      (buildL2UpgradeTxFromPlan wEnv wUnbuiltPlan v30p1 []) true = none

/-- **A SUPPLIER IMPLEMENTATION SWAP CAN CLEAR A CHECKED PUBLICATION.** A supplier on which
`wPlan`'s factory dependencies `[7, 8]` are published, followed by one implementation swap whose
code reads every hash as unpublished, ends with `requirePublished` false for that list. This holds
by the model's definition: `implementationSwap` is an arbitrary new reading of `evmPublishingBlock`
(new code, or a different storage layout). The source fact behind it is that the supplier is a
CTM-domain proxy that the registry can upgrade
(`upgrades/registry/libraries/ContractIdentifiers.sol:56-58` at `b17415d20`). -/
def Properties.SupplierSwapClearsPublication : Prop :=
  ∃ s s', requirePublished s wPlan.factoryDepHashes ∧ wPlan.factoryDepHashes ≠ [] ∧
    SupplierRun s [.implementationSwap (fun _ => 0)] s' ∧
    ¬ requirePublished s' wPlan.factoryDepHashes

/-! ## Witnesses -/

/-- **THE HEADLINE'S PREMISES ARE MET.** `wEdge` (`0.29.0 → 0.30.0`) is constructed with `wPlan`,
which deploys a table-derived row and the delegate and has factory dependencies `[7, 8]`. With the
composer answer `[1, 2, 3]` its calldata fits. On the clean chain at `0.29.0` with
`priorityTxMaxPubdata = 99_000` the storage part of `_upgrade` lands on `0.30.0` and writes the
transaction hash `31` (`nonce 30 + 1` in `wEnv`). With an L2 upgrade pending (`h = 31`, `b = 5`)
the same chain reverts on its settlement layer and, off it, lands on `0.30.0` keeping the pending
upgrade. The patch edge `wPatchEdge` (`0.30.0 → 0.30.1`) is constructed with the empty plan, and
on a chain at `0.30.0` with an L2 upgrade pending it lands on `0.30.1` and leaves the pending
upgrade as it was. -/
def Properties.ConstructedEdgeWitness : Prop :=
  Constructed wEnv wEdge wPlan ∧ wPlan.deployments ≠ [] ∧ minorOf v30 ≠ minorOf v29 ∧
    UpgradeCalldataFits (composedTx wEnv wEdge wPlan [1, 2, 3]) ∧
    upgradeStoragePart wEnv.txHash ⟨v29, 0, 0⟩ 99000 v30 (composedTx wEnv wEdge wPlan [1, 2, 3])
      true = some (31, ⟨v30, 31, 0⟩) ∧
    upgradeStoragePart wEnv.txHash ⟨v29, 31, 5⟩ 99000 v30 (composedTx wEnv wEdge wPlan [1, 2, 3])
      true = none ∧
    upgradeStoragePart wEnv.txHash ⟨v29, 31, 5⟩ 99000 v30 (composedTx wEnv wEdge wPlan [1, 2, 3])
      false = some (0, ⟨v30, 31, 5⟩) ∧
    Constructed wEnv wPatchEdge wEmptyPlan ∧ minorOf v30p1 = minorOf v30 ∧
    upgradeStoragePart wEnv.txHash ⟨v30, 31, 5⟩ 99000 v30p1
      (composedTx wEnv wPatchEdge wEmptyPlan []) true = some (0, ⟨v30p1, 31, 5⟩)

/-- **THE REGISTRY HEADLINE'S PREMISES ARE MET.** From `initialize` with release `100`, the run
"commit `300`, replace `300` by its genuine replacement `400`" succeeds; the start satisfies
`CtmInv` and has no committed slot; the replacement reports its departing release's version. Slot
`0.29.0` holds `400`, whose object `wEdge` is constructed and reported by its getters, and on the
clean chain at `0.29.0` with `priorityTxMaxPubdata = 99_000` and composer answer `[1, 2, 3]` the
storage part of `_upgrade` lands on `0.30.0`. -/
def Properties.CommittedSlotWitness : Prop :=
  ∃ s', CRun wEdgeWorld (initState wEdgeWorld 100) [.commit 300, .replace 300 400] s' ∧
    CtmInv wEdgeWorld (initState wEdgeWorld 100) ∧
    (wEdgeWorld.tr 400).old = wEdgeWorld.relVersion (wEdgeWorld.tr 400).fromRel ∧
    s'.ut v29 = 400 ∧ Constructed wEnv (wEdgeObjs.obj 400) (wEdgeObjs.plan 400) ∧
    EdgeWorld.Reports wEdgeWorld wEdgeObjs 400 ∧
    UpgradeCalldataFits (composedTx wEnv (wEdgeObjs.obj 400) (wEdgeObjs.plan 400) [1, 2, 3]) ∧
    ∃ hsh c', upgradeStoragePart wEnv.txHash ⟨v29, 0, 0⟩ 99000 (wEdgeWorld.tr 400).new
        (composedTx wEnv (wEdgeObjs.obj 400) (wEdgeObjs.plan 400) [1, 2, 3]) true = some (hsh, c') ∧
      c'.pv = v30

/-- **THE WITNESS RUN MEETS THE SLOT HEADLINE'S PREMISES.** For `CommittedSlotWitness`'s run from
`initState wEdgeWorld 100`: the start has no committed slot, so its slots report their own
version; the run's one replacement reports its departing release's version; and the conclusion of
`CommittedSlotEdgePassesChainChecks` at slot `0.29.0`, on the clean chain at `0.29.0` with
`priorityTxMaxPubdata = 99_000` and composer answer `[1, 2, 3]`, is obtained from that theorem. -/
def Properties.CommittedSlotWitnessMeetsHeadline : Prop :=
  (∀ v, (initState wEdgeWorld 100).ut v ≠ 0 →
      (wEdgeWorld.tr ((initState wEdgeWorld 100).ut v)).old = v) ∧
  (∀ e r, Op.replace e r ∈ ([.commit 300, .replace 300 400] : List Op) →
      (wEdgeWorld.tr r).old = wEdgeWorld.relVersion (wEdgeWorld.tr r).fromRel) ∧
  ∃ s', CRun wEdgeWorld (initState wEdgeWorld 100) [.commit 300, .replace 300 400] s' ∧
    s'.ut v29 = 400 ∧
    ∃ hsh c', upgradeStoragePart wEnv.txHash ⟨v29, 0, 0⟩ 99000 (wEdgeWorld.tr 400).new
        (composedTx wEnv (wEdgeObjs.obj 400) (wEdgeObjs.plan 400) [1, 2, 3]) true = some (hsh, c') ∧
      c'.pv = (wEdgeWorld.tr 400).new

/-- **THE SUPPLIER PREMISE IS MET BY A RUN THAT PUBLISHES MORE.** On a supplier where `wPlan`'s
factory dependencies `[7, 8]` are published, two further publications (hashes `9` and `11`) run,
and `[7, 8]` are still published. -/
def Properties.SupplierWitness : Prop :=
  ∃ s s', requirePublished s wPlan.factoryDepHashes ∧
    SupplierRun s [.publish 9 10, .publish 11 12] s' ∧
    (∀ op ∈ [SupplierOp.publish 9 10, .publish 11 12], op.IsPublish) ∧
    requirePublished s' wPlan.factoryDepHashes ∧ s'.pub 9 = 10

end Contracts.ChainTypeManager.EdgeChecks
