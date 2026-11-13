import EraSpec.Contracts.ChainTypeManager.Specs.LiveRouting

/-!
# Model: facets whose `selectors()` answer can change

Source: branch `feat/upgrade-simplification` at `e561b9cc2`, as for the rest of this folder.
Paths are relative to `l1-contracts/contracts/`. The code this file reads is unchanged at
`draft/v0.35.0` commit `d9f6789`: `CTMRelease.sol`, `TransitionDerivationLib.sol`,
`ReleaseFacetReader.sol`, `LiveRoutingReader.sol`, `BootstrapUpgrade.sol`, `DiamondInit.sol`,
`ISelfDescribingFacet.sol` and `MockSelfDescribingFacet.sol` are byte-identical there;
`CTMTransition.sol` only renames `upgradeEngine` to `chainUpgradeEngine`; `DefaultUpgrade.sol`'s
guard and cut move to :36 and :40.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.MutableSelectors` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.MutableSelectors`.

## Why this is modelled

A release stores its facet rows, not their selectors: "The facet's selector routing is NOT
stored: every facet is self-describing" (`upgrades/registry/RegistryTypes.sol:17-21`). Every
reader asks the facet when it runs (paths under `upgrades/registry/`):

    // objects/CTMRelease.sol:118, in validate()
    routing[i] = ISelfDescribingFacet(facet).selectors();
    // libraries/TransitionDerivationLib.sol:180, in _loadRouting (the derivation)
    selectors: ISelfDescribingFacet(facets[i].facet).selectors()
    // libraries/ReleaseFacetReader.sol:23, in newChainInstallations (genesis, bootstrap)
    selectors: ISelfDescribingFacet(facets[i].facet).selectors()
    // libraries/LiveRoutingReader.sol:47, in requireReleaseRouting (the guard)
    bytes4[] memory selectors = ISelfDescribingFacet(facet).selectors();

The four reads run at different times:

* `validate()` (the first) runs when a transition is built
  (`upgrades/registry/objects/CTMTransition.sol:74-75`) and when the CTM installs a release
  (`state-transition/ChainTypeManager.sol:310`).
* The derivation (the second) runs once, in `CTMTransition`'s constructor, which stores the
  derived cuts (`CTMTransition.sol:113-121`). `DefaultUpgrade` applies the stored cuts as they are
  (`transition.facetCuts()`, `upgrades/DefaultUpgrade.sol:41`).
* The installation (the third) runs when a chain is created or migrates in
  (`state-transition/chain-deps/DiamondInit.sol:82`) and at the bootstrap reinstall
  (`upgrades/BootstrapUpgrade.sol:41`).
* The guard (the fourth) runs when a chain crosses a registry edge (`DefaultUpgrade.sol:37`).

`VersionRegistry`'s `World.relRows` and `LiveRouting`'s `DWorld.selectors` fix every answer for a
whole run. Write-once release storage gives only half of that, the rows. The other half is an
assumption about facet code: every facet answers with the same list at every read, whoever asks.
Every facet in the tree is `public pure` with a hard-coded list
(`state-transition/chain-deps/facets/Admin.sol:615`, `Executor.sol:276`, `Getters.sol:356`,
`Mailbox.sol:385`, `Committer.sol:335`, `Migrator.sol:382`), and the interface declares the
function `pure` (`state-transition/chain-interfaces/ISelfDescribingFacet.sol:24`). The call site
does not enforce that: the call is a `STATICCALL`, and the callee may read state. The repository's
own test facet answers from storage through the same ABI
(`dev-contracts/test/MockSelfDescribingFacet.sol:19`). This file drops the assumption.

## The model

* **The answers are state** (`MutSys.sel`): what each facet's `selectors()` returns now. The step
  `MutLabel.setSelectors f xs` changes facet `f`'s answer. Whoever controls the facet's storage
  can take it; it is neither a CTM call nor a cut.
* **A transition's cuts are stored data** (`MutWorld.cuts`), written once when the transition is
  built. `MutWorld.GenuineUnder` is what `CTMTransition`'s constructor establishes when the facets
  answered `σ` while it ran. Construction is not a step, so a transition may have been built under
  answers other than the ones a run sees.
* **Every other read is live.** A step that is not a registry crossing is `LiveRouting`'s `DStep`
  in the world whose facets answer `s.sel` now (`MutWorld.at`): `validate()` when the CTM installs
  a release, genesis, migration in and the bootstrap reinstall. A crossing runs the guard against
  the answers now and applies the stored cuts.
* **One answer per instant.** In a given state every reader gets the same list. A facet that
  answers by caller is not modelled: the four reads run in different contracts (a release, a
  transition under construction, a diamond), so such a facet could also give different readers
  different lists. That half of the base model's premise (context-independence) stays a model
  boundary here; this file makes the other half (constancy) explicit as `StableSelectors`, and
  as `StableSelectorsOn` when asked only of the transitions a run can cross.
* **Everything else is as in `LiveRouting`.** Reject-only checks are omitted. A transition lands on
  `newProtocolVersion()`. Every engine runs `DefaultUpgrade` / `BootstrapUpgrade` logic. A
  break-glass cut leaves any storage.
-/

namespace Contracts.ChainTypeManager

/-! ## The objects -/

-- `Diamond.FacetCut` equality is decidable, so that stored cuts can be compared with derived ones.
deriving instance DecidableEq for FacetCut

/-- The deployed write-once objects, read through their getters, with the facets' answers left
out: releases as facet rows, and each transition with the cuts it stored. -/
structure MutWorld where
  /-- `ICTMRelease(R).protocolVersion()`. -/
  relVersion : Address → ℕ
  /-- `ICTMRelease(R).genesisFacets()`. -/
  genesisFacets : Address → List FacetRow
  /-- A transition's version and release getters. -/
  tr : Address → TransitionView
  /-- `ICTMTransition(t).facetCuts()`: the cuts its constructor stored (`CTMTransition.sol:35`,
  :113-121, :207-209). -/
  cuts : Address → List FacetCut

/-- The same objects, read while every facet `f` answers `σ f`: a `LiveRouting` world. -/
def MutWorld.at (M : MutWorld) (σ : Address → List Selector) : DWorld :=
  ⟨M.relVersion, M.genesisFacets, σ, M.tr⟩

/-- Transition `t` stored the cuts `TransitionDerivationLib.deriveFacetCuts` derives while every
facet answers `σ` (`CTMTransition.sol:113-121`). -/
def MutWorld.FrozenUnder (M : MutWorld) (σ : Address → List Selector) (t : Address) : Prop :=
  M.cuts t = deriveFacetCuts (M.at σ) (M.tr t).fromRel (M.tr t).newRel

/-- What `CTMTransition`'s constructor (`CTMTransition.sol:50-122`) establishes about `t` when
every facet answered `σ` while it ran:

    if (_manifest.fromRelease == address(0) || _manifest.newRelease == address(0) || ...) {
        revert ZeroAddress();                                                      // :54-60
    }
    uint256 oldVersion = ICTMRelease(_manifest.fromRelease).protocolVersion();     // :61
    uint256 newVersion = ICTMRelease(_manifest.newRelease).protocolVersion();      // :62
    ICTMRelease(_manifest.newRelease).validate();                                  // :74
    ICTMRelease(_manifest.fromRelease).validate();                                 // :75
    Diamond.FacetCut[] memory facetCutsMemory =
        TransitionDerivationLib.deriveFacetCuts(fromRelease, newRelease);          // :114-117
    for (uint256 i = 0; i < length; ++i) { derivedFacetCuts.push(facetCutsMemory[i]); } // :119-121

Nothing in it, and nothing later, fixes what the facets answer afterwards. -/
structure MutWorld.GenuineUnder (M : MutWorld) (σ : Address → List Selector) (t : Address) :
    Prop where
  /-- Both releases are nonzero (:54-60). -/
  nonzero : (M.tr t).fromRel ≠ 0 ∧ (M.tr t).newRel ≠ 0
  /-- The versions are the releases' versions (:61-64). -/
  versions : (M.at σ).toWorld.Genuine t
  /-- `validate()` of the departing release (:75), under the answers then. -/
  fromValid : ReleaseValid (M.at σ) (M.tr t).fromRel
  /-- `validate()` of the arriving release (:74), under the answers then. -/
  newValid : ReleaseValid (M.at σ) (M.tr t).newRel
  /-- The stored cuts (:113-121). -/
  frozen : M.FrozenUnder σ t

/-- A `LiveRouting` world as one whose transitions stored their cuts while the facets gave `D`'s
answers. `LiveRouting` derives a transition's cuts when a chain crosses; with answers that never
change that is the same. -/
def MutWorld.ofDWorld (D : DWorld) : MutWorld :=
  ⟨D.relVersion, D.genesisFacets, D.tr, fun t => deriveFacetCuts D (D.tr t).fromRel (D.tr t).newRel⟩

/-! ## The system -/

/-- The CTM and its chains, and every facet's answer now. -/
structure MutSys where
  /-- The CTM and its chains, as in `LiveRouting`. -/
  sys : DSys
  /-- `ISelfDescribingFacet(f).selectors()`, as `f` answers now. -/
  sel : Address → List Selector

/-- What happens. -/
inductive MutLabel
  /-- A step of `LiveRouting`'s system. -/
  | sys (l : DLabel)
  /-- Facet `f` starts answering `xs`: a write to its own state, by whoever controls it. -/
  | setSelectors (f : Address) (xs : List Selector)

/-- The break-glass steps. -/
def MutLabel.isArbitrary : MutLabel → Prop
  | .sys l => l.isArbitrary
  | .setSelectors _ _ => False

/-- The steps that change an answer. -/
def MutLabel.isSelectorChange : MutLabel → Prop
  | .sys _ => False
  | .setSelectors _ _ => True

/-- A registry crossing: the one step whose cuts were computed before it runs. -/
def DLabel.isCrossing : DLabel → Bool
  | .transition _ => true
  | _ => false

/-- The `LiveRouting` labels of a run, with the answer changes dropped. -/
def MutLabel.toDLabels : List MutLabel → List DLabel
  | [] => []
  | .sys l :: ls => l :: MutLabel.toDLabels ls
  | .setSelectors _ _ :: ls => MutLabel.toDLabels ls

/-- One step. -/
inductive MutStep (M : MutWorld) : MutSys → MutLabel → MutSys → Prop
  /-- Every step but a registry crossing: `LiveRouting`'s step, with the facets giving the answers
  they give now. A CTM writer's install runs `validate()` (`ChainTypeManager.sol:310`); genesis and
  migration in install the release (`DiamondInit.sol:82`); so does the bootstrap reset
  (`BootstrapUpgrade.sol:41`). -/
  | live {s : MutSys} {l : DLabel} {sys' : DSys} :
      l.isCrossing = false →
      DStep (M.at s.sel) s.sys l sys' →
      MutStep M s (.sys l) { s with sys := sys' }
  /-- `upgradeChainFromVersion` across `upgradeTransition[c.pv]` (`DefaultUpgrade.sol:30-44`). The
  guard reads the departing release's facets now (:37 → `LiveRoutingReader.sol:47`); the cut is
  the one the transition stored (`transition.facetCuts()`, :41). -/
  | transition {s : MutSys} {id : ChainId} {c : DChain} {ds : DiamondStorage} :
      s.sys.chains id = some c →
      s.sys.ctm.ut c.pv ≠ 0 →
      CountCheck s.sel c.ds (M.genesisFacets (s.sys.edge (M.at s.sel) c.pv).fromRel) →
      diamondCut c.ds (M.cuts (s.sys.ctm.ut c.pv)) = some ds →
      c.pv < (s.sys.edge (M.at s.sel) c.pv).new →
      MutStep M s (.sys (.transition id))
        { s with
          sys := { s.sys with
            chains := upd s.sys.chains id (some ⟨(s.sys.edge (M.at s.sel) c.pv).new, ds⟩) } }
  /-- Facet `f` starts answering `xs`; nothing else changes. -/
  | setSelectors {s : MutSys} {f : Address} {xs : List Selector} :
      MutStep M s (.setSelectors f xs) { s with sel := upd s.sel f xs }

/-- A sequence of steps. -/
inductive MutRun (M : MutWorld) : MutSys → List MutLabel → MutSys → Prop
  | nil {s : MutSys} : MutRun M s [] s
  | cons {s s' s'' : MutSys} {l : MutLabel} {ls : List MutLabel} :
      MutStep M s l s' → MutRun M s' ls s'' → MutRun M s (l :: ls) s''

/-! ## The premise the base model makes -/

/-- **Stable answers.** Every facet answers `σ` when the run starts, no step of the run changes an
answer, and every transition stored the cuts derived under the same `σ`. This is what fixing
`World.relRows` and `DWorld.selectors` for a whole run assumes of the facets. -/
structure StableSelectors (M : MutWorld) (σ : Address → List Selector) (s : MutSys)
    (ls : List MutLabel) : Prop where
  /-- The answers when the run starts. -/
  start : s.sel = σ
  /-- No step changes an answer. -/
  constant : ∀ l ∈ ls, ¬ l.isSelectorChange
  /-- Every transition was built while the facets answered `σ`. This is asked of every address
  `t`, committed or not; `StableSelectorsOn` asks it only of the transitions a crossing of the run
  can read. -/
  frozen : ∀ t, M.FrozenUnder σ t

/-- The transition a CTM writer records in an `upgradeTransition` slot, if the step is such a
writer: `setNewVersionUpgradeFromTransition(t)` records `t` and `replaceUpgradeTransition(e, r)`
records `r` (`_recordTransition`, `state-transition/ChainTypeManager.sol:421`, :447, :469). No
other step writes a slot. -/
def MutLabel.records : MutLabel → Option Address
  | .sys (.ctm (.commit t)) => some t
  | .sys (.ctm (.replace _ r)) => some r
  | _ => none

/-- **Stable answers, for the transitions the run can cross.** As `StableSelectors`, except that
the stored cuts are constrained only where a crossing of the run can read them: for the
transitions in an `upgradeTransition` slot when the run starts, and for those a commit or a
replacement of the run records. A transition object that is never in a slot may have been built
under any answers. `StableSelectors` is the case where every address meets the constraint. -/
structure StableSelectorsOn (M : MutWorld) (σ : Address → List Selector) (s : MutSys)
    (ls : List MutLabel) : Prop where
  /-- The answers when the run starts. -/
  start : s.sel = σ
  /-- No step changes an answer. -/
  constant : ∀ l ∈ ls, ¬ l.isSelectorChange
  /-- Every transition committed when the run starts was built while the facets answered `σ`. -/
  slots : ∀ v, s.sys.ctm.ut v ≠ 0 → M.FrozenUnder σ (s.sys.ctm.ut v)
  /-- So was every transition the run commits or installs as a replacement. -/
  recorded : ∀ l ∈ ls, ∀ t, l.records = some t → M.FrozenUnder σ t

/-! ## Witness data

`LiveRouting`'s witness world `wDWorld`, with every transition's cuts stored as derived under its
answers `wSelectors`: facets `11`, `21` and `31` (releases `100`, `200`, `250`) each answer
`[1, 2]`. So transition `300` (1→2, release `100` to `200`) stored `Remove [1, 2]` and then
`Add 21 [1, 2]`. -/

/-- The answers when the runs start. -/
def mutSelA : Address → List Selector := wSelectors

/-- The answers after facet `21`, release `200`'s only facet, starts answering `[1, 3]`. Every
release still passes `validate()`. -/
def mutSelB : Address → List Selector := upd mutSelA 21 [1, 3]

/-- The countermodels' objects: `wDWorld`, every transition built while the facets answered
`mutSelA`. -/
def mutWorld : MutWorld := MutWorld.ofDWorld wDWorld

/-- The same objects, except that transition `600` (2→3, release `200` to `250`) was built after
facet `21` started answering `[1, 3]`. -/
def mutLateWorld : MutWorld :=
  { mutWorld with cuts := upd mutWorld.cuts 600 (deriveFacetCuts (mutWorld.at mutSelB) 200 250) }

/-- A freshly initialized CTM on release `100`, no chains, the facets answering `mutSelA`. -/
def mutSys0 : MutSys := ⟨wDSys0, mutSelA⟩

/-- The same CTM, with facet `21` already answering `[1, 3]`. -/
def mutStaleSys0 : MutSys := ⟨wDSys0, mutSelB⟩

/-- The diamond of a chain created on release `100` (`wStore100`) after it crosses `300` with
`300`'s stored cuts. -/
def mutCrossedStore : DiamondStorage :=
  (diamondCut wStore100 (mutWorld.cuts 300)).getD DiamondStorage.fresh

/-- The diamond a chain created on release `200` gets while facet `21` answers `[1, 3]`. -/
def mutFreshStore : DiamondStorage :=
  (diamondCut DiamondStorage.fresh (newChainInstallations (mutWorld.at mutSelB) 200)).getD
    DiamondStorage.fresh

/-- The diamond a chain created on release `200` gets while facet `21` still answers `[1, 2]`. -/
def mutStableStore : DiamondStorage :=
  (diamondCut DiamondStorage.fresh (newChainInstallations (mutWorld.at mutSelA) 200)).getD
    DiamondStorage.fresh

end Contracts.ChainTypeManager
