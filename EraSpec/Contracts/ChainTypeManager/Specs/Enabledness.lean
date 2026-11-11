import EraSpec.Contracts.ChainTypeManager.Specs.ChainRouting

/-!
# Model: when a chain can upgrade, be deployed, or cross the bootstrap edge

Source: branch `feat/upgrade-simplification` at `e561b9cc2`, as for
`EraSpec.Contracts.ChainTypeManager.Specs.ChainRouting`, whose system this topic reads.
Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.Enabledness` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.Enabledness`.

`ChainRouting`'s steps are partial: a step exists only when every check the model keeps on
that path passes. The safety results say what a step does *if* it happens. This topic says
*when* it can happen: the liveness side of the upgrade system.

## What makes a modelled step revert

A **transition** of chain `id` at version `v` (`Step.transition`) reverts in the model exactly
when one of these holds:

1. nothing is committed for `v`: `upgradeCutForVersion` reverts
   `NoCommittedUpgradeCutForVersion` (`state-transition/ChainTypeManager.sol:607-610`);
2. the live routing is not the departing release's: `requireReleaseRouting` reverts
   `LiveRoutingDiverged` (`upgrades/DefaultUpgrade.sol:37`,
   `upgrades/registry/libraries/LiveRoutingReader.sol:38-59`);
3. a derived cut fails: a `Remove` of an unrouted selector (`RemoveFunctionFacetAddressZero`,
   `state-transition/libraries/Diamond.sol:209-211`) or an `Add` of a routed one
   (`FacetExists`, `Diamond.sol:158-160`), applied by `DefaultUpgrade.sol:41`;
4. the version would not increase: `ProtocolIdNotGreater` (`Admin.sol:556-558`).

A **genesis** (`createNewChain`, `ChainTypeManager.sol:708-716`) or **migration in**
(`forwardedBridgeMint`, :751-763) reverts in the model when the id is taken
(`ChainAlreadyLive`, :680-683) or when `DiamondInit`'s `Add` of the current release's rows
fails (`DiamondInit.sol:82-87`). A migration in must also carry the CTM's version
(`OutdatedProtocolVersion`, :759-761). The label `migrateIn id` does not name the carried
version, and the step takes it to be the CTM's, so the results below are about a migration
that carries the CTM's version. A **bootstrap reset** (`BootstrapUpgrade.sol:29-44`) reverts
when no bootstrap cut is recorded for the chain's version or the `Add` of the genesis
release's rows fails (:41). Its version check always passes under `CtmInv`.

For a chain that routes its departing release, (3) happens exactly when the two releases
route differently and one of them lists a selector twice. (When they route identically the
derived cut is empty, `TransitionDerivationLib.sol:56-58`.) An `Add` list that lists a
selector twice always reverts, whatever the routing it starts from, and so does a `Remove`
list. That is the one property of release objects these paths depend on.

## Well-formed releases

`CTMRelease.validate()` (`upgrades/registry/objects/CTMRelease.sol:105-129`) refuses a release
whose facets' self-described selectors repeat: `_requireNoDuplicateSelectors(routing)` (:128,
defined at :190-213, revert `RegistryDuplicateSelector` at :205-207). The source gives the
reason (:125-127):

    // Same reason: the installing paths add every facet's routing, and `Diamond.diamondCut`
    // rejects a selector added twice. ...

`validate()` runs where a release is installed, `_setCurrentRelease` (`ChainTypeManager.sol:310`),
which `initialize` (:297), the registry commit (:422) and the legacy commit (:817) all call.
It also runs on both releases of every `CTMTransition` at construction
(`CTMTransition.sol:74-75`), which the derivation relies on
(`TransitionDerivationLib.sol:59-60`: "Both releases passed `validate()` ... none is routed
twice"). The model omits `validate()` (a reject-only check; see `Specs/VersionRegistry.lean`),
so its duplicate-selector content is stated here as `ReleaseWf`, and it is a premise wherever
a result needs it. `Op.InstallsWf` says that the release a CTM writer installs passed that
check. Every successful source call does, but the model's `CStep` admits calls that do not.

`_requireNoDuplicateSelectors` is an open-addressing set over `selector + 1`.
`Specs/DuplicateSelectorCheck.lean` transcribes it, and its results prove that it returns
exactly when `ReleaseWf` holds (`ReleaseWfIsTheDuplicateCheck`).

## What enabledness means here

Omitting a reject-only check is sound for **safety**: it only adds runs. For **liveness** it
goes the other way: a step the model has may still revert at the source on an omitted check.
So a positive result below means *no check the model keeps can block this step*. A
source-level liveness claim needs, besides the premises stated here, every check the model
omits on that path to pass:

* **all paths**: the caller checks (`onlyBridgehub`, `onlyChainAssetHandler`,
  `onlyAdminOrChainTypeManagerOrValidator`); facet code existence (`AddressHasNoCode`,
  `Diamond.sol:147-149`); nonempty selector lists per cut row (`NoFunctionsForDiamondCut`,
  :120-122, refused for releases by `CTMRelease.sol:121-123`); one freezability per facet
  (`SelectorsMustAllHaveSameFreezability`, :243-248, which unique facet rows give,
  `CTMRelease.sol:171-184`);
* **transition**: for a validator caller, the chain's `ServerNotifier` timestamp
  (`Admin.sol:546-554`); `_requireAllBatchesExecuted` (`DefaultUpgrade.sol:31`); a nonzero
  target verifier (:68-72); the manifest's upgrade timestamp (`TimeNotReached`,
  `BaseZkSyncUpgrade.sol:76-78`); the settlement layer being upgraded first (:83-88); the
  version-shape and L2-upgrade checks of `_setNewProtocolVersion` and
  `_setL2SystemContractUpgrade`;
* **genesis and migration in**: the rest of `DiamondInit.initialize`'s checks
  (`DiamondInit.sol:52-150`: bridgehub, admin, validator timelock, base token, verifier,
  stored batch zero); for genesis, `genesisUpgrade` (`ChainTypeManager.sol:712`), which the
  model does not run.

Results that say a step does **not** exist need no such premise. The model keeps only checks
the source makes, so a missing model step is a missing source step. This holds within the
model boundaries of `MODEL-CTM-ROUTING`, in particular the reading of `requireReleaseRouting`
by its documented meaning.
-/

namespace Contracts.ChainTypeManager

/-! ## Well-formed releases -/

/-- **`CTMRelease.validate()`'s duplicate-selector check**, as a predicate
(`_requireNoDuplicateSelectors`, `CTMRelease.sol:190-213`): no selector appears twice in the
release's flattened routing, across all of its facets. -/
def ReleaseWf (W : World) (r : Address) : Prop :=
  ((W.relRows r).map Prod.fst).Nodup

/-- Every release the CTM has installed (the ghost `relAt`) passed `validate()`'s duplicate
check. -/
def RecordedReleasesWf (W : World) (s : CTM) : Prop :=
  ∀ v, s.relAt v ≠ 0 → ReleaseWf W (s.relAt v)

/-- Every chain at a version with a release is at a well-formed release. Under `SysInv` the
chain routes that release, so this says each chain's routing came from a release that
lists each selector once. -/
def ChainsOnWfReleases (W : World) (s : Sys) : Prop :=
  ∀ id c, s.chains id = some c → s.ctm.relAt c.pv ≠ 0 → ReleaseWf W (s.ctm.relAt c.pv)

/-- The release a CTM writer installs passed `validate()`, as `_setCurrentRelease` requires
(`ChainTypeManager.sol:310`): the commit installs its transition's `newRelease()` (:422), the
legacy commit its `_newRelease` (:817). A replacement installs no release: its departing
release is the replaced one's (`_requireSameDeparture`, :442) and its landing release is
already installed (`_requireOnwardDestination`, :444). `setUpgradeDiamondCut` installs none. -/
def Op.InstallsWf (W : World) : Op → Prop
  | .commit t => ReleaseWf W (W.tr t).newRel
  | .legacyCommit R _ => ReleaseWf W R
  | .replace _ _ => True
  | .legacyRecut _ => True

/-- `Op.InstallsWf` for a step of the routing system; chain steps install no release. -/
def Label.InstallsWf (W : World) : Label → Prop
  | .ctm op => op.InstallsWf W
  | _ => True

/-! ## Which versions the CTM has left

A chain behind its CTM can move on only along what the CTM recorded when it left the chain's
version: a registry transition in `upgradeTransition[v]`, or a legacy cut in
`__LEGACY_upgradeCutHash[v]` (the bootstrap's, or an opaque one). The CTM leaves a version only
through the two version edges, and each records one or the other for the version it leaves:
the registry commit writes `upgradeTransition[protocolVersion]` (`_recordTransition`,
`ChainTypeManager.sol:421`, :469), and the legacy commit writes the cut for
`_oldProtocolVersion` (`setUpgradeDiamondCutInner`, :814). -/

/-- Every reached version below the CTM's own was left by a registry commit (its slot is
filled) or by a legacy commit (a legacy cut is recorded). -/
def DepartedBelow (s : CTM) : Prop :=
  ∀ v, s.relAt v ≠ 0 → v < s.pv → s.ut v ≠ 0 ∨ s.legacy v ≠ LegacyCut.none

/-- Every chain behind its CTM is at a version the CTM recorded a way out of. -/
def ChainsAtDepartedVersions (s : Sys) : Prop :=
  ∀ id c, s.chains id = some c → c.pv < s.ctm.pv →
    s.ctm.ut c.pv ≠ 0 ∨ s.ctm.legacy c.pv ≠ LegacyCut.none

/-! ## Where an enabled step lands -/

/-- The system after chain `id`, at chain state `c`, crosses the edge committed at `c.pv`
and lands on the arriving release's routing at the edge's new version. -/
def Sys.crossEdge (W : World) (s : Sys) (id : ChainId) (c : Chain) : Sys :=
  { s with
    chains := upd s.chains id
      (some ⟨(s.edge W c.pv).new, rowsRouting (W.relRows (s.edge W c.pv).newRel)⟩) }

/-- The system after a fresh diamond for `id` is deployed (`_deployNewChain`, for genesis and
migration in alike): at the CTM's version, routing exactly the current release. -/
def Sys.deployNew (W : World) (s : Sys) (id : ChainId) : Sys :=
  { s with chains := upd s.chains id (some ⟨s.ctm.pv, rowsRouting (W.relRows s.ctm.cur)⟩) }

/-! ## Witness data: releases that list a selector twice

`wEnDupWorld` is the witness world `wWorld` (releases `100`, `200`, `250`; transitions `300`,
`400`, `500`, `600`) with two ill-formed releases and one transition for each:

* release `260` at version 2. Facet `26` routes selectors `1` and `2`, and facet `27` also
  claims selector `1`, so the flattened routing lists `1` twice. `validate()` refuses this
  with `RegistryDuplicateSelector`.
* release `150` at version 1, whose facets `15` and `16` both claim selector `1`.
* transition `700`, from version 1 to 2 and from release `100` to `260`.
* transition `800`, from version 1 to 2 and from release `150` to `200`.

Both transitions are genuine (`World.Genuine`): their versions are their releases' versions.
The two countermodels check this. -/

/-- Release versions: `wWorld`'s, plus `150` at version 1 and `260` at version 2. -/
def wDupRelVersion : Address → ℕ := fun a =>
  if a = 260 then 2 else if a = 150 then 1 else wRelVersion a

/-- Release routing: `wWorld`'s, plus the two ill-formed releases. -/
def wDupRows : Address → ReleaseRows := fun a =>
  if a = 260 then [(1, (26, false)), (2, (26, false)), (1, (27, false))]
  else if a = 150 then [(1, (15, false)), (1, (16, false))]
  else wRows a

/-- Transition getters: `wWorld`'s, plus `700` (`100 → 260`) and `800` (`150 → 200`). -/
def wDupTr : Address → TransitionView := fun a =>
  if a = 700 then ⟨1, 2, 100, 260⟩ else if a = 800 then ⟨1, 2, 150, 200⟩ else wTr a

/-- The witness world with the two ill-formed releases. -/
def wEnDupWorld : World := ⟨wDupRelVersion, wDupRows, wDupTr⟩

/-- A freshly initialized CTM on release `100` in `wEnDupWorld`, with no chains. -/
def wEnDupSys0 : Sys := ⟨initState wEnDupWorld 100, fun _ => none⟩

/-- A CTM initialized on the ill-formed release `150`, with chain `0` at version 1 routing
exactly that release. It satisfies `SysInv`, but no run from a starting state reaches it
without a break-glass cut: no chain can be deployed on `150`. -/
def wDupDepSys : Sys :=
  ⟨initState wEnDupWorld 150, upd (fun _ => none) 0 (some ⟨1, rowsRouting (wDupRows 150)⟩)⟩

/-! ## Witness data: chains left behind at three kinds of version

On `wWorld`: the bootstrap moved a legacy CTM from version 1 to release `200` at version 2, so
the bootstrap cut is recorded at version 1 and version 0 carries an opaque pre-registry cut.
Pre-registry chain `5` is at version 0 and chain `6` at version 1. -/

/-- The just-bootstrapped system with two pre-registry chains behind the CTM. -/
def wLagSys : Sys :=
  ⟨bootstrapState wWorld 1 200,
    upd (upd (fun _ => none) 5 (some ⟨0, upd emptyRouting 7 (some (77, true))⟩)) 6
      (some ⟨1, upd emptyRouting 8 (some (88, false))⟩)⟩

end Contracts.ChainTypeManager
