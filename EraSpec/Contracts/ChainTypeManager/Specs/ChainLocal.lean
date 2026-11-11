import EraSpec.Contracts.ChainTypeManager.Specs.ChainMigration

/-!
# Model: one chain at a time, and the break-glass repair

Source: branch `feat/upgrade-simplification` at `e561b9cc2`, as for
`EraSpec.Contracts.ChainTypeManager.Specs.ChainRouting` and
`EraSpec.Contracts.ChainTypeManager.Specs.ChainMigration`. This file adds **no step and no
state**: it reuses `Step`/`Run` and `MStep`/`MRun` unchanged and only names which steps
write a given chain, the repair cut, and witness data. Paths are relative to
`l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.ChainLocal` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.ChainLocal`.

## Why a per-chain statement

`Properties.ChainsRunTheirVersionsRelease` assumes the run has no break-glass cut at all. A
break-glass cut writes one chain. The CTM owner names the chain, and the CTM forwards the cut
to that chain's diamond only:

    function executeUpgrade(uint256 _chainId, Diamond.DiamondCutData calldata _diamondCut) external onlyOwner {
        IZKChain(getZKChain(_chainId)).executeUpgrade(_diamondCut);          // state-transition/ChainTypeManager.sol:631-633

The diamond runs it on its own storage (`state-transition/chain-deps/facets/Admin.sol:562-564`,
`onlyChainTypeManager` at `chain-deps/facets/ZKChainBase.sol:84-89`):

    function executeUpgrade(Diamond.DiamondCutData calldata _diamondCut) external onlyChainTypeManager {
        _executeDiamondCut(_diamondCut);                                     // → Diamond.diamondCut, Admin.sol:112-115

`Diamond.diamondCut` (`state-transition/libraries/Diamond.sol:109-133`) edits that diamond's
routing and then delegatecalls the cut's init in that diamond's context (:310-318).
`Step.arbitraryCut` already models exactly this: it writes chain `id`'s version and routing,
and leaves the CTM and every other chain alone. Code the init calls acts as that diamond,
which is neither another diamond's `chainTypeManager` nor the CTM's owner, so it cannot issue
another chain's break-glass cut (`onlyChainTypeManager`) or a CTM writer (`onlyOwner`).
Anything else such code might do is the existing engine boundary of `ChainRouting`, unchanged
here.

So a break-glass cut of one chain says nothing about another, and the routing headline can
be stated chain by chain, with a premise about that chain's own history only:
`LastWriteNotBreakGlass id ls` says the last step of `ls` that writes chain `id`
(`Label.writesChain id`) is not a break-glass cut.

## The repair

`DefaultUpgrade.upgradeFromTransition` checks the live routing before applying the derived
cuts (`upgrades/DefaultUpgrade.sol:33-37`):

    // The derived cuts remove the departing RELEASE's routing, not the live one: a chain whose
    // routing drifted from it (a CTM-owner `executeUpgrade` recovery cut) would keep the drift
    // under the new release, or fail mid-cut. Restoring the release's routing is the last
    // step of such a recovery.
    LiveRoutingReader.requireReleaseRouting(ICTMRelease(transition.fromRelease()));

The design document says the same ("Such a recovery ends by restoring the release's
routing", `docs/registry-driven-upgrades.md:680-682` at the repository root).
`repairCut W s id v` is that last step: a break-glass cut of chain `id` that leaves it at
version `v` routing exactly `R_v = relAt v`, the release the CTM installed when it reached
`v`. In the source it is one `executeUpgrade` whose facet cuts remove every live selector
and add `R_v`'s rows, with an init that writes `s.protocolVersion = v` if the drift moved the
version. The model gives it as one `Label.arbitraryCut`, which exists for every registered
chain.

## Modelling choices

* **Writes.** The steps that write chain `id`'s diamond are those of `ChainRouting` that
  name `id`: creation (`createNewChain`), deployment on arrival (`forwardedBridgeMint`), a
  transition, the bootstrap reset, and a break-glass cut. A CTM writer writes no diamond.
  This matches `Properties.OnlyUpgradesAndCutsWriteADiamond` for a chain that is already
  registered (creation and arrival need the chain id to be free).
* **Migration-model runs** are related to routing runs by dropping the steps that are not
  routing steps (`MLabel.base?`): leaving, returning and a failed-transfer recovery do not
  touch the routing system (`Properties.MigrationLeavesRoutingAlone`).
* **Inherited boundaries.** Every result here inherits the boundaries of `ChainRouting`: the
  guard `requireReleaseRouting` is modelled by its documented meaning (its counting
  implementation is not re-proved), every engine runs `DefaultUpgrade`'s logic, and checks
  that only reject are omitted. Omitting those checks is sound for the safety results; for the
  enabledness results (`Properties.RepairEnablesTransition` and the witnesses that cross an
  edge after a repair) it means only a revert caused by the routing is ruled out.
-/

namespace Contracts.ChainTypeManager

/-! ## Which steps write a chain -/

/-- The steps that write chain `id`'s diamond: creating it (`createNewChain`), deploying it on
arrival (`forwardedBridgeMint`), a transition, the bootstrap reset, and a break-glass cut of
`id`. A CTM writer writes no diamond; every other step writes another chain's. -/
def Label.writesChain (id : ChainId) : Label → Prop
  | .ctm _ => False
  | .genesis id' => id' = id
  | .migrateIn id' => id' = id
  | .transition id' => id' = id
  | .bootstrapReset id' => id' = id
  | .arbitraryCut id' _ _ => id' = id

/-- **The last write of chain `id` in `ls` is not a break-glass cut.** Whenever a step `l` of
`ls` writes `id`'s diamond and no later step does, `l` is not a break-glass cut.

It holds when no step of `ls` writes `id`, and whenever `ls` has no break-glass cut at all.
It allows break-glass cuts of other chains anywhere, and break-glass cuts of `id` that are
followed, later in `ls`, by a write of `id` that is not a cut. -/
def LastWriteNotBreakGlass (id : ChainId) (ls : List Label) : Prop :=
  ∀ pre l post, ls = pre ++ l :: post → l.writesChain id → (∀ l' ∈ post, ¬ l'.writesChain id) →
    ¬ l.isArbitrary

/-- **The repair cut** of chain `id` to version `v`, as the CTM owner would issue it in state
`s`: a break-glass cut that leaves the chain at version `v` routing exactly `R_v`, the release
`s.ctm.relAt v` the CTM installed when it reached `v` (the "last step of such a recovery" of
`DefaultUpgrade.sol:33-36`). -/
def repairCut (W : World) (s : Sys) (id : ChainId) (v : ℕ) : Label :=
  .arbitraryCut id v (rowsRouting (W.relRows (s.ctm.relAt v)))

/-- The routing step a migration-model step is, if any: `none` for leaving, returning and a
failed-transfer recovery, which do not touch the routing system. -/
def MLabel.base? : MLabel → Option Label
  | .base l => some l
  | _ => none

/-! ## Witness data

On the witness world of `VersionRegistry`/`ChainRouting`: releases `100` and `200` at versions
`1` and `2`, transition `300` (1→2); `bgExtra` is release `100`'s routing plus selector `9`. -/

/-- The run of `Properties.ChainLocalWitness`, from the fresh witness system `wSys0`: chains
`0` and `1` are created at version 1 on release `100`; a break-glass cut drifts each to
`bgExtra`; a second break-glass cut repairs chain `0` to release `100`'s routing; the CTM
commits `300` (1→2); chain `0` crosses it. -/
def wLocalRun : List Label :=
  [.genesis 0, .genesis 1, .arbitraryCut 0 1 bgExtra, .arbitraryCut 1 1 bgExtra,
    .arbitraryCut 0 1 (rowsRouting (wRows 100)), .ctm (.commit 300), .transition 0]

/-- The run of `Properties.DriftedReturnerIsStuck`, from `wMSys0`: chain `0` is created at
version 1, drifted to `bgExtra` by a break-glass cut, leaves and returns, and the CTM commits
`300` (1→2). -/
def wStuckRun : List MLabel :=
  [.base (.genesis 0), .base (.arbitraryCut 0 1 bgExtra), .migrateOut 0, .migrateReturn 0,
    .base (.ctm (.commit 300))]

/-- What `Properties.RepairUnsticksDriftedReturner` runs after `wStuckRun`: the repair cut of
chain `0` to version 1 on release `100`'s routing, the transition across `300`, and leaving
again. -/
def wUnstickRun : List MLabel :=
  [.base (.arbitraryCut 0 1 (rowsRouting (wRows 100))), .base (.transition 0), .migrateOut 0]

/-! ### A release that lists a selector twice

`CTMRelease.validate()` refuses a release whose facets list a selector twice
(`upgrades/registry/objects/CTMRelease.sol:128`, `:190-213`), and the CTM calls it whenever it
installs a release (`state-transition/ChainTypeManager.sol:310`). The model omits `validate()`,
so such a release can be committed in the model. This world has one: releases `100`, `700`,
`200` at versions 1, 2, 3, where `700` lists selector `1` twice, and transitions `800`
(1→2, onto `700`) and `900` (2→3, leaving `700`). -/

/-- Release versions of the repeated-selector world. -/
def dRelVersion : Address → ℕ := fun a =>
  if a = 100 then 1 else if a = 700 then 2 else if a = 200 then 3 else 0

/-- Release routing of the repeated-selector world: `700` lists selector `1` twice. -/
def dRows : Address → ReleaseRows := fun a =>
  if a = 100 then [(1, (11, false)), (2, (11, false))]
  else if a = 700 then [(1, (71, false)), (1, (71, false))]
  else if a = 200 then [(1, (21, false)), (2, (21, false))]
  else []

/-- Transition getters of the repeated-selector world. -/
def dTr : Address → TransitionView := fun a =>
  if a = 800 then ⟨1, 2, 100, 700⟩ else if a = 900 then ⟨2, 3, 700, 200⟩ else ⟨0, 0, 0, 0⟩

/-- The repeated-selector world. -/
def wDupWorld : World := ⟨dRelVersion, dRows, dTr⟩

/-- A freshly initialized CTM on release `100` of the repeated-selector world, no chains. -/
def wDupSys0 : Sys := ⟨initState wDupWorld 100, fun _ => none⟩

end Contracts.ChainTypeManager
