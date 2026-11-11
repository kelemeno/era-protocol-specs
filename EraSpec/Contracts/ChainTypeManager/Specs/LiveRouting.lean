import EraSpec.Contracts.ChainTypeManager.Specs.DiamondStorage

/-!
# Model: `requireReleaseRouting`'s counting check, and the routing system that runs it

Source: branch `feat/upgrade-simplification` at `e561b9cc2`, as for the rest of this folder.
Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.LiveRouting` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.LiveRouting`.

## The check

`DefaultUpgrade.upgradeFromTransition` refuses to cross an edge unless the chain's live
routing is its departing release's (`upgrades/DefaultUpgrade.sol:37`). The check
(`upgrades/registry/libraries/LiveRoutingReader.sol:32-59`):

    /// @notice Reverts unless the live routing is exactly `_release`'s: the same facets, each
    ///         routing exactly the selectors it self-describes, with its row's freezability.
    /// @dev Counting is enough for equality. Every row's selectors route to its facet, so the
    ///      facet is live and routes at least those; it routes no others when the counts match,
    ///      and there is no other live facet when the facet counts match. Rows and selectors are
    ///      unique, which the release's `validate()` holds.
    function requireReleaseRouting(ICTMRelease _release) internal view {
        GenesisFacet[] memory facets = _release.genesisFacets();
        if (ds.facets.length != facetsLength) { revert LiveRoutingDiverged(); }
        for (uint256 i = 0; i < facetsLength; ++i) {
            address facet = facets[i].facet;
            bytes4[] memory selectors = ISelfDescribingFacet(facet).selectors();
            if (ds.facetToSelectors[facet].selectors.length != selectorsLength) { revert LiveRoutingDiverged(); }
            for (uint256 j = 0; j < selectorsLength; ++j) {
                Diamond.SelectorToFacet memory info = ds.selectorToFacet[selectors[j]];
                if (info.facetAddress != facet || info.isFreezable != facets[i].isFreezable) {
                    revert LiveRoutingDiverged();
                }
            }
        }
    }

`ChainRouting` models this check by the first sentence (`Step.transition`'s guard
`c.routing = rowsRouting …`). This file models it **by its code** (`CountCheck`), over the
diamond storage of `DiamondStorage`, and rebuilds the routing system on that storage.

## What a release is here

`ChainRouting`'s `World.relRows` is a release's routing flattened to one entry per selector.
Here a release is what its contract returns: `genesisFacets()`, a list of rows
`(facet, isFreezable)` (`upgrades/registry/RegistryTypes.sol:22-25`), and each facet's
`ISelfDescribingFacet(facet).selectors()`. `DWorld.toWorld` flattens it back to a `World`, so
every `ChainRouting` definition applies to it.

What `CTMRelease.validate()` checks of the rows (`upgrades/registry/objects/CTMRelease.sol:105-129`)
is `ReleaseValid`: every facet has code (in particular is nonzero, :117), every facet's
selector list is nonempty (:121-123), and no selector appears twice across the rows
(`_requireNoDuplicateSelectors`, :128, :190-213). It does not check that facet rows are
distinct; that follows (`Properties.ValidRowsHaveDistinctFacets`), because a repeated facet
repeats its nonempty selector list.

## Modelling choices

* **`selectors()` is a fixed function of the facet address** (`DWorld.selectors`). Every
  facet in the tree declares it `public pure` (e.g. `state-transition/chain-deps/facets/Admin.sol:615`,
  `Executor.sol:276`, `Getters.sol:356`) and the interface declares it `pure`
  (`state-transition/chain-interfaces/ISelfDescribingFacet.sol:24`). This matters because
  `validate()` runs when a release is installed (`ChainTypeManager.sol:310`) and when a
  transition is built from it (`CTMTransition.sol:74-75`), while the check re-reads
  `selectors()` when a chain upgrades. A facet whose answer changes over time (a call through
  a `pure` interface is a `STATICCALL`, which may still read state) is outside the model.
  This is an assumption about the facet code governance approves; genuine release and
  transition objects do not discharge it. Topic `MutableSelectors` models such a facet
  (`MutableSelectorsSplitRouting`, `MutableSelectorsBlockNextEdge`) and re-derives the headline
  with stable answers as an explicit premise (`ChainsRunTheirVersionsReleaseStable`).
* **`validate()` is checked when a release is installed** (`DStep.ctm`, through
  `_setCurrentRelease`, `ChainTypeManager.sol:305-323`), and by the starting states; it is
  the only check of the facet rows in the system. The duplicate-selector scan is an
  open-addressing set (`CTMRelease.sol:190-213`), modelled here by its meaning: no selector
  twice. The `DuplicateSelectorScan` topic transcribes the scan and proves it checks exactly
  that for 4-byte selectors (`Properties.DuplicateScanIffNodup`, `ValidateRowsIffRowsWf`).
* **The transition's cuts** are `TransitionDerivationLib.deriveFacetCuts(fromRelease,
  newRelease)` (`TransitionDerivationLib.sol:47-80`), which `CTMTransition` freezes at
  construction (`CTMTransition.sol:114-121`); with fixed `selectors()` that is the same as
  deriving them now (`MutableSelectors` keeps the stored cuts apart from the derivation). The
  shortcut compares `keccak256(abi.encode(fromFacets))` with
  `keccak256(abi.encode(newFacets))` (:56); the model compares the two row lists, as
  `ChainRouting.applyDerived` does.
* **The rest of the engine and the omitted checks** are as in `ChainRouting`: reject-only
  checks are omitted, a transition lands on `newProtocolVersion()`, and every engine runs
  `DefaultUpgrade` / `BootstrapUpgrade` logic. In that logic the only writer of diamond
  storage is `_applyDerivedFacetCuts` (`BaseZkSyncUpgrade.sol:118-123`), a `diamondCut` with
  init zero; `_upgrade` writes the chain's own storage, not the diamond's.
* **A break-glass cut leaves any storage** (`DLabel.arbitraryCut`): its init can
  `delegatecall` code that writes diamond storage directly, so even the storage invariant
  may fail after it. A break-glass cut made only of facet cuts keeps the invariant
  (`Properties.DiamondCutPreservesOk`).
-/

namespace Contracts.ChainTypeManager

/-! ## Releases as facet rows -/

/-- `GenesisFacet` (`RegistryTypes.sol:22-25`): a facet and its freezability. -/
abbrev FacetRow := Address × Bool

/-- A release's routing flattened to one entry per selector, in row order, each selector read
from its facet's self-description `sel`. -/
def flattenRows (sel : Address → List Selector) (rows : List FacetRow) : ReleaseRows :=
  rows.flatMap fun fb => (sel fb.1).map fun x => (x, fb)

/-- The deployed objects, read through their getters, with releases as facet rows. -/
structure DWorld where
  /-- `ICTMRelease(R).protocolVersion()`. -/
  relVersion : Address → ℕ
  /-- `ICTMRelease(R).genesisFacets()`. -/
  genesisFacets : Address → List FacetRow
  /-- `ISelfDescribingFacet(f).selectors()`. -/
  selectors : Address → List Selector
  /-- A transition's getters. -/
  tr : Address → TransitionView

/-- The same objects as a `ChainRouting` world: a release's rows flattened. -/
def DWorld.toWorld (D : DWorld) : World :=
  ⟨D.relVersion, fun R => flattenRows D.selectors (D.genesisFacets R), D.tr⟩

/-- A release's flattened routing. -/
abbrev DWorld.rows (D : DWorld) (R : Address) : ReleaseRows := D.toWorld.relRows R

/-- What the count check needs of a release's rows: every row self-describes at least one
selector, and no selector appears twice across the rows. -/
structure RowsWf (sel : Address → List Selector) (rows : List FacetRow) : Prop where
  /-- `if (routing[i].length == 0) { revert RegistryEmptySelectors(facet); }` (`CTMRelease.sol:121-123`). -/
  nonempty : ∀ fb ∈ rows, sel fb.1 ≠ []
  /-- `_requireNoDuplicateSelectors(routing)` (`CTMRelease.sol:128`). -/
  nodup : (rows.flatMap fun fb => sel fb.1).Nodup

/-- What `CTMRelease.validate()` checks of a release's facet rows (`CTMRelease.sol:105-129`). -/
structure ReleaseValid (D : DWorld) (R : Address) : Prop where
  /-- `ObjectAnchorLib.requireCode(facet)` (:117); address zero has no code. -/
  facetsNonzero : ∀ fb ∈ D.genesisFacets R, fb.1 ≠ 0
  /-- Nonempty and duplicate-free selector lists. -/
  rows : RowsWf D.selectors (D.genesisFacets R)

/-! ## The check -/

/-- **`LiveRoutingReader.requireReleaseRouting`**, as the code does it
(`LiveRoutingReader.sol:38-59`): the facet count matches; for each row, the facet's live
selector count matches its self-description; and each self-described selector routes to that
facet with the row's freezability. The check passes exactly when no `LiveRoutingDiverged`
revert fires. -/
def CountCheck (sel : Address → List Selector) (ds : DiamondStorage) (rows : List FacetRow) :
    Prop :=
  ds.facets.length = rows.length ∧
    ∀ fb ∈ rows, (ds.facetToSelectors fb.1).selectors.length = (sel fb.1).length ∧
      ∀ x ∈ sel fb.1, (ds.selectorToFacet x).facetAddress = fb.1 ∧
        (ds.selectorToFacet x).isFreezable = fb.2

/-- The check is decidable by running its loops (`List.decidableBAll`); the instance is spelled
out because `Address × Bool` is a `Fintype`, and instance search would otherwise decide the
row loop by enumerating every pair. -/
instance (sel : Address → List Selector) (ds : DiamondStorage) (rows : List FacetRow) :
    Decidable (CountCheck sel ds rows) :=
  @instDecidableAnd _ _ inferInstance
    (@List.decidableBAll _ _ (fun fb => @instDecidableAnd _ _ inferInstance
      (@List.decidableBAll _ _ (fun _ => inferInstance) (sel fb.1))) rows)

/-! ## The cuts the system applies -/

/-- `ReleaseFacetReader.newChainInstallations` (`upgrades/registry/libraries/ReleaseFacetReader.sol:14-26`):
one `Add` cut per row, with the facet's self-described selectors. -/
def newChainInstallations (D : DWorld) (R : Address) : List FacetCut :=
  (D.genesisFacets R).map fun fb => ⟨fb.1, .add, fb.2, D.selectors fb.1⟩

/-- `TransitionDerivationLib.deriveFacetCuts` (`TransitionDerivationLib.sol:47-80`): nothing
if the two releases' rows with their routing are equal (:56-58); otherwise one `Remove` cut
per departing row (facet zero, :64-71) and then one `Add` cut per arriving row (:72-79). -/
def deriveFacetCuts (D : DWorld) (A B : Address) : List FacetCut :=
  if (D.genesisFacets A).map (fun fb => (fb, D.selectors fb.1)) =
      (D.genesisFacets B).map (fun fb => (fb, D.selectors fb.1)) then []
  else (D.genesisFacets A).map (fun fb => ⟨0, .remove, false, D.selectors fb.1⟩) ++
    newChainInstallations D B

/-- `LiveRoutingReader.removeAllCuts` (`LiveRoutingReader.sol:18-30`): one `Remove` cut per
live facet, covering its selector list, snapshotted before any is applied. -/
def removeAllCuts (ds : DiamondStorage) : List FacetCut :=
  ds.facets.map fun f => ⟨0, .remove, false, (ds.facetToSelectors f).selectors⟩

/-! ## The routing system on diamond storage -/

/-- A chain diamond: its version and its diamond storage. -/
structure DChain where
  /-- `s.protocolVersion`. -/
  pv : ℕ
  /-- The diamond's storage. -/
  ds : DiamondStorage

/-- The CTM and its chains, each with its diamond storage. -/
structure DSys where
  /-- The CTM's version state. -/
  ctm : CTM
  /-- The chains, `none` where no diamond is registered. -/
  chains : ChainId → Option DChain

/-- What happens; as `Label`, with a break-glass cut leaving any storage. -/
inductive DLabel
  /-- A CTM writer. -/
  | ctm (op : Op)
  /-- `createNewChain`. -/
  | genesis (id : ChainId)
  /-- `forwardedBridgeMint`. -/
  | migrateIn (id : ChainId)
  /-- `upgradeChainFromVersion` across a registry transition. -/
  | transition (id : ChainId)
  /-- Crossing the bootstrap edge. -/
  | bootstrapReset (id : ChainId)
  /-- `executeUpgrade`, or crossing an opaque legacy edge: any version, any storage. -/
  | arbitraryCut (id : ChainId) (pv : ℕ) (ds : DiamondStorage)

/-- The break-glass steps. -/
def DLabel.isArbitrary : DLabel → Prop
  | .arbitraryCut _ _ _ => True
  | _ => False

/-- The release a CTM writer installs through `_setCurrentRelease`, which runs
`release.validate()` (`ChainTypeManager.sol:310`): the commit's new release (:422) and the
legacy commit's release (:817). -/
def Op.installs (W : World) : Op → Option Address
  | .commit t => some (W.tr t).newRel
  | .legacyCommit R _ => some R
  | _ => none

/-- The transition the CTM commits for a chain at version `v`. -/
abbrev DSys.edge (D : DWorld) (s : DSys) (v : ℕ) : TransitionView := D.tr (s.ctm.ut v)

/-- One step, as `Step`, with the routing written by the diamond's own code. -/
inductive DStep (D : DWorld) : DSys → DLabel → DSys → Prop
  /-- A CTM writer; a release it installs passes `validate()`. -/
  | ctm {s : DSys} {op : Op} {c' : CTM} :
      CStep D.toWorld s.ctm op c' →
      (∀ R, op.installs D.toWorld = some R → ReleaseValid D R) →
      DStep D s (.ctm op) { s with ctm := c' }
  /-- `createNewChain`: a fresh diamond whose `DiamondInit` cuts in the current release's
  facets (`DiamondInit.sol:77-87`) and records the CTM's version (:58, :110). -/
  | genesis {s : DSys} {id : ChainId} {ds : DiamondStorage} :
      s.chains id = none →
      diamondCut DiamondStorage.fresh (newChainInstallations D s.ctm.cur) = some ds →
      DStep D s (.genesis id) { s with chains := upd s.chains id (some ⟨s.ctm.pv, ds⟩) }
  /-- `forwardedBridgeMint`: the arriving chain is at the CTM's version; deployed as at
  genesis. -/
  | migrateIn {s : DSys} {id : ChainId} {ds : DiamondStorage} (v : ℕ) :
      v = s.ctm.pv →
      s.chains id = none →
      diamondCut DiamondStorage.fresh (newChainInstallations D s.ctm.cur) = some ds →
      DStep D s (.migrateIn id) { s with chains := upd s.chains id (some ⟨v, ds⟩) }
  /-- `upgradeChainFromVersion` across `upgradeTransition[c.pv]`: the count check against the
  departing release (`DefaultUpgrade.sol:37`), then the derived cuts (:41). -/
  | transition {s : DSys} {id : ChainId} {c : DChain} {ds : DiamondStorage} :
      s.chains id = some c →
      s.ctm.ut c.pv ≠ 0 →
      CountCheck D.selectors c.ds (D.genesisFacets (s.edge D c.pv).fromRel) →
      diamondCut c.ds (deriveFacetCuts D (s.edge D c.pv).fromRel (s.edge D c.pv).newRel) =
        some ds →
      c.pv < (s.edge D c.pv).new →
      DStep D s (.transition id)
        { s with chains := upd s.chains id (some ⟨(s.edge D c.pv).new, ds⟩) }
  /-- Crossing the bootstrap edge (`BootstrapUpgrade.sol:29-44`): remove the whole live
  routing (:40), install the migration's release (:41), move to its version. -/
  | bootstrapReset {s : DSys} {id : ChainId} {c : DChain} {R : Address}
      {ds₁ ds₂ : DiamondStorage} :
      s.chains id = some c →
      s.ctm.legacy c.pv = LegacyCut.bootstrap R →
      diamondCut c.ds (removeAllCuts c.ds) = some ds₁ →
      diamondCut ds₁ (newChainInstallations D R) = some ds₂ →
      c.pv < D.relVersion R →
      DStep D s (.bootstrapReset id) { s with chains := upd s.chains id (some ⟨D.relVersion R, ds₂⟩) }
  /-- Break-glass: any version, any storage. -/
  | arbitraryCut {s : DSys} {id : ChainId} {c : DChain} (v : ℕ) (ds : DiamondStorage) :
      s.chains id = some c →
      DStep D s (.arbitraryCut id v ds) { s with chains := upd s.chains id (some ⟨v, ds⟩) }

/-- A sequence of steps. -/
inductive DRun (D : DWorld) : DSys → List DLabel → DSys → Prop
  | nil {s : DSys} : DRun D s [] s
  | cons {s s' s'' : DSys} {l : DLabel} {ls : List DLabel} :
      DStep D s l s' → DRun D s' ls s'' → DRun D s (l :: ls) s''

/-! ## The routing a system shows -/

/-- What a chain routes: its version and the routing its storage implements. -/
def DChain.view (c : DChain) : Chain := ⟨c.pv, c.ds.routing⟩

/-- The `ChainRouting` system this one implements. -/
def DSys.view (s : DSys) : Sys := ⟨s.ctm, fun id => (s.chains id).map DChain.view⟩

/-- The `ChainRouting` label of a step. -/
def DLabel.view : DLabel → Label
  | .ctm op => .ctm op
  | .genesis id => .genesis id
  | .migrateIn id => .migrateIn id
  | .transition id => .transition id
  | .bootstrapReset id => .bootstrapReset id
  | .arbitraryCut id v ds => .arbitraryCut id v ds.routing

/-! ## The invariant -/

/-- What the system keeps besides `ChainRouting`'s invariant: every release it installed
passed `validate()`, and every chain's storage is consistent. -/
structure StoreInv (D : DWorld) (s : DSys) : Prop where
  /-- Every release recorded at a version passed `validate()`. -/
  releases : ∀ v, s.ctm.relAt v ≠ 0 → ReleaseValid D (s.ctm.relAt v)
  /-- Every chain's diamond storage satisfies `DiamondOk`. -/
  storage : ∀ id c, s.chains id = some c → DiamondOk c.ds

/-- The invariant of the count-checked system: `ChainRouting`'s invariant of what it routes,
and `StoreInv`. -/
def DSysInv (D : DWorld) (s : DSys) : Prop := SysInv D.toWorld s.view ∧ StoreInv D s

/-! ## Witness data

The `ChainRouting` witness world with each release as one facet row: release `100` is facet
`11`, `200` is `21`, `250` is `31`, and every one of these facets self-describes selectors
`1` and `2` (so `wDWorld.toWorld` routes exactly as `wWorld`). -/

/-- Release rows of the witness world. -/
def wGenesisFacets : Address → List FacetRow := fun a =>
  if a = 100 then [(11, false)] else if a = 200 then [(21, false)]
  else if a = 250 then [(31, false)] else []

/-- Facet self-descriptions of the witness world. -/
def wSelectors : Address → List Selector := fun f =>
  if f = 11 ∨ f = 21 ∨ f = 31 then [1, 2] else []

/-- The witness world. -/
def wDWorld : DWorld := ⟨wRelVersion, wGenesisFacets, wSelectors, wTr⟩

/-- A freshly initialized CTM on release `100`, no chains. -/
def wDSys0 : DSys := ⟨initState wDWorld.toWorld 100, fun _ => none⟩

/-- The diamond a chain created on release `100` gets. -/
def wStore100 : DiamondStorage :=
  (diamondCut DiamondStorage.fresh (newChainInstallations wDWorld 100)).getD DiamondStorage.fresh

/-- That diamond after a break-glass cut made of one facet cut: facet `99` with selector `9`,
which neither release routes. -/
def wBgStore : DiamondStorage :=
  (diamondCut wStore100 [⟨99, .add, false, [9]⟩]).getD DiamondStorage.fresh

/-- A pre-registry diamond: facet `77` routing only selector `7`. -/
def wPreStore : DiamondStorage :=
  (diamondCut DiamondStorage.fresh [⟨77, .add, true, [7]⟩]).getD DiamondStorage.fresh

/-- The bootstrap from version `0` to release `100` has just run, and chain `5` is a
pre-registry chain at version `0` on that diamond (`ChainRouting.wBootSys` on storage). -/
def wBootDSys : DSys :=
  ⟨bootstrapState wDWorld.toWorld 0 100, upd (fun _ => none) 5 (some ⟨0, wPreStore⟩)⟩

/-- **Countermodel data.** Facet `11` self-describes selector `1`, facet `13` selector `2`, and
facet `12` nothing. -/
def cmSelectors : Address → List Selector := fun f =>
  if f = 11 then [1] else if f = 13 then [2] else []

/-- A release whose second row is the selector-less facet `12`. -/
def cmRows : List FacetRow := [(11, false), (12, false)]

/-- A release that lists facet `11` twice (which `CTMRelease`'s constructor refuses,
`CTMRelease.sol:171-184`, and `validate()` refuses through the repeated selector). -/
def cmRepeatedRows : List FacetRow := [(11, false), (11, false)]

/-- The cuts that build the live diamond of the countermodel: facet `11` with selector `1`,
then facet `13` with selector `2`. -/
def cmCuts : List FacetCut := [⟨11, .add, false, [1]⟩, ⟨13, .add, false, [2]⟩]

/-- The diamond those cuts leave on a fresh proxy. -/
def cmStore : DiamondStorage := (diamondCut DiamondStorage.fresh cmCuts).getD DiamondStorage.fresh

/-- A world with that release twice: `700` at version 1 and `710` at version 2, with the same
rows, and the transition `720` from one to the other. -/
def cmWorld : DWorld :=
  ⟨fun a => if a = 700 then 1 else if a = 710 then 2 else 0,
   fun a => if a = 700 ∨ a = 710 then cmRows else [],
   cmSelectors,
   fun a => if a = 720 then ⟨1, 2, 700, 710⟩ else ⟨0, 0, 0, 0⟩⟩

/-- The CTM after `initialize(700)` and the commit of `720`, were `validate()` skipped: at
version 2 on release `710`, with `720` in slot 1. -/
def cmCtm : CTM :=
  ⟨2, 710, upd (fun _ => 0) 1 720, fun _ => LegacyCut.none, upd (upd (fun _ => 0) 1 700) 2 710⟩

/-- That CTM with chain `0` at version 1 on the countermodel's diamond. -/
def cmSys : DSys := ⟨cmCtm, upd (fun _ => none) 0 (some ⟨1, cmStore⟩)⟩

/-- A store a delegatecalled init could leave: release `100`'s storage, plus selector `3`
routed to facet `99`, which no list records. -/
def corruptStore : DiamondStorage :=
  ⟨upd (upd (upd (fun _ => SelectorToFacet.zero) 1 ⟨11, 0, false⟩) 2 ⟨11, 1, false⟩) 3
      ⟨99, 0, false⟩,
    upd (fun _ => ⟨[], 0⟩) 11 ⟨[1, 2], 0⟩, [11]⟩

end Contracts.ChainTypeManager
