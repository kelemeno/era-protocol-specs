import EraSpec.Contracts.ChainTypeManager.Specs.VersionRegistry

/-!
# Model: the facet routing of the chains on a `ChainTypeManager`

Source: branch `feat/upgrade-simplification` at `e561b9cc2`, as for
`EraSpec.Contracts.ChainTypeManager.Specs.VersionRegistry`, whose CTM state this model
extends. Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.ChainRouting` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.ChainRouting`.

The routing lives in each chain's diamond, not in the CTM, but every way it changes
except the break-glass cut reads its target from the CTM, so the model is the CTM's
version state together with its chains.

## The ways a chain's routing changes

1. **Genesis.** `createNewChain` (`state-transition/ChainTypeManager.sol:708-716`) deploys
   a diamond whose init is `DiamondInit.initialize` (:679-697). That init reads the CTM's
   `protocolVersion` and installs the CTM's `currentRelease`'s facets:

        uint256 protocolVersion = ctm.protocolVersion();                         // DiamondInit.sol:58
        address currentRelease = ctm.currentRelease();                            // :77
        Diamond.FacetCut[] memory facetCuts = ReleaseFacetReader.newChainInstallations(release); // :82
        if (facetCuts.length != 0) { Diamond.diamondCut(...); }                   // :83-87
        s.protocolVersion = protocolVersion;                                      // :110

   The chain id must be free: `if (getZKChain(_chainId) != address(0)) { revert ChainAlreadyLive(); }`
   (`ChainTypeManager.sol:680-683`).
2. **Migration in.** `forwardedBridgeMint` (:751-763) checks
   `if (_protocolVersion != protocolVersion) { revert OutdatedProtocolVersion(...); }` (:759-761)
   and then deploys exactly as genesis does (:762).
3. **Bootstrap reset.** A pre-registry chain crosses the bootstrap edge through the legacy
   cut, whose engine (`upgrades/BootstrapUpgrade.sol:29-44`) removes the whole live
   routing and installs the release the committed migration names:

        (, , address genesisRelease) = migration.upgradeTarget();                   // :36
        _applyDerivedFacetCuts(LiveRoutingReader.removeAllCuts());                  // :40
        _applyDerivedFacetCuts(ReleaseFacetReader.newChainInstallations(ICTMRelease(genesisRelease))); // :41

4. **Transition.** The chain's `Admin.upgradeChainFromVersion(_, old)`
   (`state-transition/chain-deps/facets/Admin.sol:528-559`) reads the cut its CTM derives
   from `upgradeTransition[old]` (:535-537, `ChainTypeManager.sol:606-612`), requires
   `s.protocolVersion == old` (:539-541), executes it (:555), and requires the version to
   have increased (:556-558). The cut's init is `DefaultUpgrade.upgradeFromTransition`
   (`upgrades/DefaultUpgrade.sol:30-44`):

        LiveRoutingReader.requireReleaseRouting(ICTMRelease(transition.fromRelease())); // :37
        _applyDerivedFacetCuts(transition.facetCuts());                                  // :41

   and `transition.facetCuts()` are `TransitionDerivationLib.deriveFacetCuts(fromRelease,
   newRelease)` frozen at construction (`CTMTransition.sol:114-121`): nothing if the two
   routings are byte-identical (`TransitionDerivationLib.sol:56-58`), otherwise one
   `Remove` per departing row and one `Add` per arriving row (:64-79) — a full reinstall.
5. **Break-glass.** The CTM owner's `executeUpgrade(chainId, cut)` (`ChainTypeManager.sol:631-633`)
   runs an arbitrary cut, with an arbitrary init. Crossing an opaque legacy edge is the
   same from the chain's point of view. Both are `Label.arbitraryCut`.

## Modelling choices

* **Routing is `selectorToFacet`**: a map from selector to `(facet, isFreezable)`,
  `none` for an unrouted selector (`facetAddress == address(0)`). The facet list and
  `facetToSelectors` are views of it under the diamond's own storage invariant.
* **The guard is modelled by its documented meaning**: `requireReleaseRouting` "Reverts
  unless the live routing is exactly `_release`'s" (`LiveRoutingReader.sol:32`). It
  establishes that by counting (:34-37), which is exact when the release has unique
  facet rows and selectors (`CTMRelease.validate()`) and the diamond's storage is
  consistent. That counting argument is not re-proved here.
* **Cuts are flattened** to one entry per selector, removals then additions, in row
  order — the order `Diamond.diamondCut` processes them (`Diamond.sol:110-133`). `Remove`
  of an unrouted selector reverts (`RemoveFunctionFacetAddressZero`, :209-211) and `Add`
  of a routed one reverts (`FacetExists`, :158-160). The empty-cut shortcut is taken
  exactly when the flattened lists are equal; with unique facet rows (checked by
  `CTMRelease`'s constructor) that is when the encoded rows are equal.
* **A transition's cuts are its derived cuts**, and the version `upgradeTarget()` lands a
  chain on is `newProtocolVersion()`. Both are what `CTMTransition` returns
  (`CTMTransition.sol:202-209`); a non-`CTMTransition` object could return anything.
* **The engine is `DefaultUpgrade` / `BootstrapUpgrade`.** The committed cut delegatecalls
  `transition.upgradeEngine()` (`CTMUpgradeComposer.sol:37-43`), which governance names
  in the manifest. The model gives every engine the logic of `DefaultUpgrade.upgradeFromTransition`
  (and `BootstrapUpgrade.upgradeFromBootstrap` for the bootstrap cut). A versioned engine
  that overrides those functions is outside the model.
* **The only routing writers** at this commit are the ones above: `Admin.sol:555`
  (transition), `:563` (`executeUpgrade`), `:577` (`genesisUpgrade`, whose cut has no
  facet cuts), and the `DiamondProxy` constructor running `DiamondInit`. Code delegatecalled
  by an engine or an init could write diamond storage too; that is the engine boundary
  above.
* **Checks that only reject are omitted** (facet code existence, empty selector lists,
  `_requireAllBatchesExecuted`, the upgrade timestamp, the settlement-layer order, the
  caller checks). Omitting a rejecting check only adds runs.
* **Migration out** changes neither the leaving diamond's routing nor its version, so it
  is no step. Chains on other CTMs are not modelled.
-/

namespace Contracts.ChainTypeManager

open Clear

/-! ## Routing and the diamond cut -/

/-- A diamond's `selectorToFacet`: `none` for an unrouted selector. -/
abbrev Routing := Selector → Option Route

/-- The routing a release describes. -/
def rowsRouting : ReleaseRows → Routing
  | [] => fun _ => none
  | (x, r) :: rs => fun y => if y = x then some r else rowsRouting rs y

/-- A fresh diamond routes nothing. -/
def emptyRouting : Routing := fun _ => none

/-- `Remove` of one selector (`Diamond._removeFunctions`, `Diamond.sol:196-215`): reverts
unless the selector is routed. -/
def removeSel (ρ : Routing) (x : Selector) : Option Routing :=
  if ρ x = none then none else some (upd ρ x none)

/-- `Add` of one selector (`Diamond._addFunctions`, `Diamond.sol:141-164`): reverts if the
selector is already routed. -/
def addSel (ρ : Routing) (x : Selector) (r : Route) : Option Routing :=
  if ρ x = none then some (upd ρ x (some r)) else none

/-- `Remove` cuts over a list of selectors, in order; `none` is a revert. -/
def removeAll : Routing → List Selector → Option Routing
  | ρ, [] => some ρ
  | ρ, x :: xs => (removeSel ρ x).bind (fun ρ' => removeAll ρ' xs)

/-- `Add` cuts over a release's rows, in order; `none` is a revert. -/
def addAll : Routing → ReleaseRows → Option Routing
  | ρ, [] => some ρ
  | ρ, (x, r) :: rs => (addSel ρ x r).bind (fun ρ' => addAll ρ' rs)

/-- Applying a transition's derived cuts (`TransitionDerivationLib.deriveFacetCuts`,
`TransitionDerivationLib.sol:47-80`, applied by `_applyDerivedFacetCuts`): nothing when
the two releases route identically, otherwise remove every departing selector and add
every arriving one. This is the cut **without** the guard. -/
def applyDerived (ρ : Routing) (A B : ReleaseRows) : Option Routing :=
  if A = B then some ρ else (removeAll ρ (A.map Prod.fst)).bind (fun σ => addAll σ B)

/-! ## Chains -/

/-- A chain diamond's version and routing. -/
structure Chain where
  /-- `s.protocolVersion`. -/
  pv : ℕ
  /-- The diamond's routing. -/
  routing : Routing

/-- Chain ids; only equality matters. -/
abbrev ChainId := ℕ

/-- The CTM and its chains (`Bridgehub.getZKChain`, restricted to this CTM). -/
structure Sys where
  /-- The CTM's version state. -/
  ctm : CTM
  /-- The chains, `none` where no diamond is registered. -/
  chains : ChainId → Option Chain

/-- What happens. -/
inductive Label
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
  /-- `executeUpgrade`, or crossing an opaque legacy edge: any version, any routing. -/
  | arbitraryCut (id : ChainId) (pv : ℕ) (ρ : Routing)

/-- The break-glass steps. -/
def Label.isArbitrary : Label → Prop
  | .arbitraryCut _ _ _ => True
  | _ => False

/-- The transition the CTM commits for a chain at version `v`. -/
abbrev Sys.edge (W : World) (s : Sys) (v : ℕ) : TransitionView := W.tr (s.ctm.ut v)

/-- One step of the CTM and its chains. -/
inductive Step (W : World) : Sys → Label → Sys → Prop
  /-- A CTM writer; the chains are untouched. -/
  | ctm {s : Sys} {op : Op} {c' : CTM} :
      CStep W s.ctm op c' → Step W s (.ctm op) { s with ctm := c' }
  /-- `createNewChain`: a fresh diamond at the CTM's version with its current release. -/
  | genesis {s : Sys} {id : ChainId} {ρ : Routing} :
      s.chains id = none →
      addAll emptyRouting (W.relRows s.ctm.cur) = some ρ →
      Step W s (.genesis id) { s with chains := upd s.chains id (some ⟨s.ctm.pv, ρ⟩) }
  /-- `forwardedBridgeMint`: the arriving chain must be at the CTM's version `v`; the new
  diamond is deployed as at genesis. -/
  | migrateIn {s : Sys} {id : ChainId} {ρ : Routing} (v : ℕ) :
      v = s.ctm.pv →
      s.chains id = none →
      addAll emptyRouting (W.relRows s.ctm.cur) = some ρ →
      Step W s (.migrateIn id) { s with chains := upd s.chains id (some ⟨v, ρ⟩) }
  /-- `upgradeChainFromVersion` across `upgradeTransition[c.pv]`, with the guard. -/
  | transition {s : Sys} {id : ChainId} {c : Chain} {ρ : Routing} :
      s.chains id = some c →
      s.ctm.ut c.pv ≠ 0 →
      c.routing = rowsRouting (W.relRows (s.edge W c.pv).fromRel) →
      applyDerived c.routing (W.relRows (s.edge W c.pv).fromRel)
        (W.relRows (s.edge W c.pv).newRel) = some ρ →
      c.pv < (s.edge W c.pv).new →
      Step W s (.transition id)
        { s with chains := upd s.chains id (some ⟨(s.edge W c.pv).new, ρ⟩) }
  /-- Crossing the bootstrap edge committed at the chain's version: remove everything,
  install the migration's release, move to its version. -/
  | bootstrapReset {s : Sys} {id : ChainId} {c : Chain} {R : Address} {ρ : Routing} :
      s.chains id = some c →
      s.ctm.legacy c.pv = LegacyCut.bootstrap R →
      addAll emptyRouting (W.relRows R) = some ρ →
      c.pv < W.relVersion R →
      Step W s (.bootstrapReset id) { s with chains := upd s.chains id (some ⟨W.relVersion R, ρ⟩) }
  /-- Break-glass: any version, any routing. -/
  | arbitraryCut {s : Sys} {id : ChainId} {c : Chain} (v : ℕ) (ρ : Routing) :
      s.chains id = some c →
      Step W s (.arbitraryCut id v ρ) { s with chains := upd s.chains id (some ⟨v, ρ⟩) }

/-- A sequence of steps. -/
inductive Run (W : World) : Sys → List Label → Sys → Prop
  | nil {s : Sys} : Run W s [] s
  | cons {s s' s'' : Sys} {l : Label} {ls : List Label} :
      Step W s l s' → Run W s' ls s'' → Run W s (l :: ls) s''

/-- The transition step **without** the guard of `DefaultUpgrade.sol:37`: the engine as it
would be if it applied the derived cuts to whatever routing it finds. -/
def UnguardedCrossing (W : World) (s : Sys) (id : ChainId) (ρ : Routing) : Prop :=
  ∃ c, s.chains id = some c ∧ s.ctm.ut c.pv ≠ 0 ∧
    applyDerived c.routing (W.relRows (s.edge W c.pv).fromRel)
      (W.relRows (s.edge W c.pv).newRel) = some ρ ∧
    c.pv < (s.edge W c.pv).new

/-- A chain is consistent with its CTM: not ahead of it, and if the CTM has a release for
the chain's version, the chain routes exactly that release. -/
def ChainOk (W : World) (s : Sys) (c : Chain) : Prop :=
  c.pv ≤ s.ctm.pv ∧
    (s.ctm.relAt c.pv ≠ 0 → c.routing = rowsRouting (W.relRows (s.ctm.relAt c.pv)))

/-- The system invariant. -/
def SysInv (W : World) (s : Sys) : Prop :=
  CtmInv W s.ctm ∧ ∀ id c, s.chains id = some c → ChainOk W s c

/-! ## Witness data

Chain `0` on the witness world: created at version 1 on release `100`, then the CTM
commits `300` (1→2). -/

/-- The break-glass routing: release `100`'s plus selector `9`, routed to facet `99`. -/
def bgExtra : Routing := upd (rowsRouting (wRows 100)) 9 (some (99, false))

/-- The break-glass routing: release `100`'s without its selector `2`. -/
def bgMissing : Routing := upd (rowsRouting (wRows 100)) 2 none

/-- The starting system: a freshly initialized CTM on release `100`, no chains. -/
def wSys0 : Sys := ⟨initState wWorld 100, fun _ => none⟩

/-- The starting system for the bootstrap witness: the bootstrap from version `0` to
release `100` has just run, and chain `5` is a pre-registry chain at version `0` routing
only selector `7`. -/
def wBootSys : Sys :=
  ⟨bootstrapState wWorld 0 100, upd (fun _ => none) 5 (some ⟨0, upd emptyRouting 7 (some (77, true))⟩)⟩

end Contracts.ChainTypeManager
