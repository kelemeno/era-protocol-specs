import EraSpec.Contracts.ChainTypeManager.Specs.ExecutorUpgradeChain
import EraSpec.Contracts.ChainTypeManager.Specs.ChainLocalExecutor

/-!
# Model: the getters the chain-side engine reads, apart from the ones the CTM checks

Source: branch `feat/upgrade-simplification` at `e561b9cc2`, as for the rest of this folder. Paths
are relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.EngineGettersFaithful` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.EngineGettersFaithful`. Everything here is in the
sub-namespace `Contracts.ChainTypeManager.EngineGetters`. It edits no existing definition.

## Two values merged

In `VersionRegistry` a transition object is the four getters the CTM reads (`TransitionView`):
`oldProtocolVersion()`, `newProtocolVersion()`, `fromRelease()`, `newRelease()`. `ChainRouting`'s
`Step.transition` then applies the cuts derived from `(fromRelease, newRelease)` and lands the chain
on `newProtocolVersion()`. The engine the chain runs reads two other getters
(`upgrades/DefaultUpgrade.sol:30-44, 66-67`):

    _applyDerivedFacetCuts(transition.facetCuts());                                       // :41
    (uint256 newProtocolVersion, uint256 upgradeTimestamp, address newRelease) = _object.upgradeTarget(); // :67

`_applyDerivedFacetCuts` runs whatever cuts it is handed through `Diamond.diamondCut`
(`upgrades/BaseZkSyncUpgrade.sol:118-123`). `_setNewProtocolVersion` checks only that the version
increases, plus semver bounds (`BaseZkSyncUpgrade.sol:204-238`). Nothing ties either value to the
CTM's checks. Only `CTMTransition` does: `facetCuts()` returns the cuts derived at construction,
and `upgradeTarget()` returns `derivedNewProtocolVersion` (`upgrades/registry/objects/CTMTransition.sol:114-121,
202-209`). `replaceUpgradeTransition` checks the replacement's `validate()` and `l2Plan()`
(`_requireExecutable`), `fromRelease()`, `oldProtocolVersionDeadline()`, `newProtocolVersion()` and
`newRelease()` (`state-transition/ChainTypeManager.sol:429-448, 454-457, 477-523`). It does not check
`facetCuts()` or `upgradeTarget()`.

`ChainRouting` records this as a model boundary ("A transition's cuts are its derived cuts ... a
non-`CTMTransition` object could return anything", `Specs/ChainRouting.lean`), and so does the
README. This file makes the two values separate fields of the model (`Engine`). The boundary then
becomes an explicit premise (`EngineDerived`) of the re-proved headline, and its failure becomes a
countermodel.

## Modelling choices

* **`facetCuts()` is a list of per-selector actions** (`SelCut`), applied in order with
  `Diamond.sol`'s semantics on the routing (`state-transition/libraries/Diamond.sol:109-215`):
  * `Add` reverts if the selector is routed (`FacetExists`);
  * `Replace` reverts if it is unrouted (`ReplaceFunctionFacetAddressZero`), and otherwise reroutes
    it;
  * `Remove` reverts if it is unrouted (`RemoveFunctionFacetAddressZero`).
  A `FacetCut` naming several selectors is the same as one entry per selector. Checks that only
  reject (facet code, an empty selector list, the zero facet of a `Remove`) are omitted.
* **`upgradeTarget()` is the version it returns** (`Engine.target`). Its timestamp and release
  affect the timing gate and the verifier, which this routing model does not track.
* **Everything else is `ExecutorUpgradeChain`'s model.** Only the transition step changes
  (`EStep.transition`). The guard still reads `fromRelease()`, the engine applies `G.cuts t`, and
  the chain lands on `G.target t`, which must exceed its version (`Admin.sol:556-558`, and
  `BaseZkSyncUpgrade.sol:209-211`). The step is used everywhere the original model crosses an edge:
  * the executor's `upgradeChain` (`EUStep.upgradeChain`);
  * the chain admin's direct call (`EUStep.adminUpgrade`);
  * a forwarded `CTM.upgradeChainFromVersion` (`EFStep.sys`).
  The other `ExecutorForward` transactions never cross an edge and are taken from `XStep`
  unchanged (`EUStep.x`).
* **Which objects reach a slot.** A slot is written by a commit (`applyCTMUpgrade`, or a forwarded
  `setNewVersionUpgradeFromTransition`) and by a forwarded `replaceUpgradeTransition`. `Installs t u`
  says that transaction `u` writes `t` into a slot. A CTM code swap could write anything, and the
  results exclude it (`XLabel.KeepsCtmCode`).
-/

namespace Contracts.ChainTypeManager.EngineGetters

/-! ## The engine's cut list -/

/-- One selector of a `Diamond.FacetCut` entry, with its action. -/
inductive SelCut
  /-- `Action.Add` of selector `x`, routed to `r`. -/
  | add (x : Selector) (r : Route)
  /-- `Action.Replace` of selector `x`, rerouted to `r`. -/
  | replace (x : Selector) (r : Route)
  /-- `Action.Remove` of selector `x`. -/
  | remove (x : Selector)
deriving DecidableEq

/-- One selector's action on the routing (`Diamond._addFunctions`, `_replaceFunctions`,
`_removeFunctions`, `Diamond.sol:141-215`); `none` is a revert. -/
def applySel (ρ : Routing) : SelCut → Option Routing
  | .add x r => addSel ρ x r
  | .replace x r => if ρ x = none then none else some (upd ρ x (some r))
  | .remove x => removeSel ρ x

/-- `Diamond.diamondCut`'s facet cuts, in order (`Diamond.sol:109-133`); `none` is a revert. -/
def applyCuts : Routing → List SelCut → Option Routing
  | ρ, [] => some ρ
  | ρ, c :: cs => (applySel ρ c).bind (fun σ => applyCuts σ cs)

/-- What `TransitionDerivationLib.deriveFacetCuts(fromRelease, newRelease)` returns, flattened
(`libraries/TransitionDerivationLib.sol:47-80`): nothing when the two releases route identically,
otherwise one `Remove` per departing row and one `Add` per arriving row. -/
def derivedCuts (A B : ReleaseRows) : List SelCut :=
  if A = B then [] else A.map (fun p => SelCut.remove p.1) ++ B.map (fun p => SelCut.add p.1 p.2)

/-! ## Transition objects, as the engine reads them -/

/-- The getters of a transition object that the chain-side engine reads and the CTM never checks. -/
structure Engine where
  /-- `facetCuts()`. -/
  cuts : Address → List SelCut
  /-- The version `upgradeTarget()` returns. -/
  target : Address → ℕ

/-- **Transition `t` returns what a `CTMTransition` returns** (`CTMTransition.sol:114-121,
202-209`): its cuts are derived from its `fromRelease()` and `newRelease()`, and `upgradeTarget()`
lands on `newProtocolVersion()`. -/
def EngineDerived (W : World) (G : Engine) (t : Address) : Prop :=
  G.cuts t = derivedCuts (W.relRows (W.tr t).fromRel) (W.relRows (W.tr t).newRel) ∧
    G.target t = (W.tr t).new

/-- Every committed slot holds an object that returns what a `CTMTransition` returns. -/
def SlotsDerived (W : World) (G : Engine) (c : CTM) : Prop :=
  ∀ v, c.ut v ≠ 0 → EngineDerived W G (c.ut v)

/-! ## Steps -/

/-- One step of the CTM and its chains, with the transition run by the engine's own getters.
Every other step is `ChainRouting`'s. -/
inductive EStep (W : World) (G : Engine) : Sys → Label → Sys → Prop
  /-- A step that crosses no edge, exactly as in `ChainRouting`. -/
  | base {s : Sys} {l : Label} {s' : Sys} :
      (∀ id, l ≠ .transition id) → Step W s l s' → EStep W G s l s'
  /-- `Admin.upgradeChainFromVersion` across `upgradeTransition[c.pv]`, run by `DefaultUpgrade`
  (`upgrades/DefaultUpgrade.sol:30-44`). The guard reads `fromRelease()` (:37), the cuts are
  `facetCuts()` (:41), and the chain lands on the version `upgradeTarget()` returns (:67), which
  must exceed the chain's version (`Admin.sol:556-558`). -/
  | transition {s : Sys} {id : ChainId} {c : Chain} {ρ : Routing} :
      s.chains id = some c →
      s.ctm.ut c.pv ≠ 0 →
      c.routing = rowsRouting (W.relRows (s.edge W c.pv).fromRel) →
      applyCuts c.routing (G.cuts (s.ctm.ut c.pv)) = some ρ →
      c.pv < G.target (s.ctm.ut c.pv) →
      EStep W G s (.transition id)
        { s with chains := upd s.chains id (some ⟨G.target (s.ctm.ut c.pv), ρ⟩) }

/-- One forwarded call that succeeds; as `FStep`, with a forwarded CTM call an `EStep`. -/
inductive EFStep (X : XConfig) (G : Engine) : XState → FCall → XState → Prop
  | sys {s : XState} {l : Label} {sys' : Sys} :
      EStep X.W G s.sys l sys' → EFStep X G s (.sys l) { s with sys := sys' }
  | upgradeProxy {s : XState} {p x : Address} :
      X.rc.adminOwner = X.rc.self → X.rc.hasCode x → p ≠ X.ctmProxy →
      EFStep X G s (.upgradeProxy p x) { s with impl := ProxyUpgradeCurrent.upd s.impl p x }
  | swapCtm {s : XState} {x : Address} {c' : CTM} :
      X.rc.adminOwner = X.rc.self → X.rc.hasCode x →
      EFStep X G s (.swapCtm x c')
        ⟨{ s.sys with ctm := c' }, ProxyUpgradeCurrent.upd s.impl X.ctmProxy x⟩

/-- The calls of one `forward`, in order. -/
inductive EFRun (X : XConfig) (G : Engine) : XState → List FCall → XState → Prop
  | nil {s : XState} : EFRun X G s [] s
  | cons {s s' s'' : XState} {c : FCall} {cs : List FCall} :
      EFStep X G s c s' → EFRun X G s' cs s'' → EFRun X G s (c :: cs) s''

/-- One successful transaction of `ExecutorUpgradeChain`'s model, with every edge crossing run by
the engine's own getters. -/
inductive EUStep (X : XConfig) (G : Engine) : XState → ULabel → XState → Prop
  /-- `applyInfrastructureUpgrade`, `applyCTMUpgrade` and other actors' steps, none of which
  crosses an edge: exactly as in `ExecutorForward`. -/
  | x {s s' : XState} {l : XLabel} :
      ¬ l.IsUpgradeChain → (∀ calls, l ≠ .forward calls) → XStep X s l s' → EUStep X G s (.x l) s'
  /-- `forward(calls)`. -/
  | forward {s s' : XState} {calls : List FCall} :
      EFRun X G s calls s' → EUStep X G s (.x (.forward calls)) s'
  /-- `CTMUpgradeExecutor.upgradeChain(t, id)`, as in `ExecutorUpgradeChain`. -/
  | upgradeChain {s : XState} {t : Address} {id : ChainId} {c : Chain} {sys' : Sys} :
      t ≠ 0 →
      s.sys.ctm.ut (X.W.tr t).old = t →
      s.sys.chains id = some c →
      c.pv = (X.W.tr t).old →
      EStep X.W G s.sys (.transition id) sys' →
      EUStep X G s (.upgradeChain t id) { s with sys := sys' }
  /-- The chain admin's `Admin.upgradeChainFromVersion(_, old)`, as in `ExecutorUpgradeChain`. -/
  | adminUpgrade {s : XState} {id : ChainId} {old : ℕ} {c : Chain} {sys' : Sys} :
      s.sys.chains id = some c →
      c.pv = old →
      EStep X.W G s.sys (.transition id) sys' →
      EUStep X G s (.adminUpgrade id old) { s with sys := sys' }

/-- A sequence of successful transactions. -/
inductive EURun (X : XConfig) (G : Engine) : XState → List ULabel → XState → Prop
  | nil {s : XState} : EURun X G s [] s
  | cons {s s' s'' : XState} {u : ULabel} {us : List ULabel} :
      EUStep X G s u s' → EURun X G s' us s'' → EURun X G s (u :: us) s''

/-! ## Which objects a transaction writes into a slot -/

/-- A forwarded call writes `t` into a slot: a forwarded `setNewVersionUpgradeFromTransition(t)`,
or a forwarded `replaceUpgradeTransition(_, t)`. -/
def FInstalls (t : Address) : FCall → Prop
  | .sys (.ctm (.commit t')) => t' = t
  | .sys (.ctm (.replace _ r)) => r = t
  | _ => False

/-- A transaction writes `t` into a slot: `applyCTMUpgrade(t)`, or a `forward` that commits `t` or
installs it as a replacement. -/
def Installs (t : Address) : ULabel → Prop
  | .x (.commit t') => t' = t
  | .x (.forward calls) => ∃ f ∈ calls, FInstalls t f
  | _ => False

/-! ## Witness data

The witness executor `wX` of `ExecutorForward` (the witness world `wWorld`), from the fresh state
`wX0`. -/

/-- Every object returns what a `CTMTransition` returns. -/
def wGenuineEngine : Engine :=
  ⟨fun t => derivedCuts (wWorld.relRows (wWorld.tr t).fromRel) (wWorld.relRows (wWorld.tr t).newRel),
    fun t => (wWorld.tr t).new⟩

/-- As `wGenuineEngine`, except that transition `400` adds selector `9` (routed to facet `99`) after
its derived cuts. `400` reports the same four CTM-read getters as the genuine replacement of
`VersionRegistry`'s witness world: `1 → 2`, release `100` to `200`. -/
def wForeignCuts : Engine :=
  { wGenuineEngine with
    cuts := fun t => if t = 400 then
      derivedCuts (wWorld.relRows 100) (wWorld.relRows 200) ++ [SelCut.add 9 (99, false)]
      else wGenuineEngine.cuts t }

/-- As `wGenuineEngine`, except that transition `400`'s `upgradeTarget()` lands on version 3, not on
its `newProtocolVersion()`, 2. -/
def wForeignTarget : Engine :=
  { wGenuineEngine with target := fun t => if t = 400 then 3 else wGenuineEngine.target t }

/-- The run of both countermodels: create chain `0`, commit `300` (1→2) through `applyCTMUpgrade`,
`forward` its replacement by `400`, then `upgradeChain(400, 0)`, the argument the NatSpec prescribes
after a replacement (`ICTMUpgradeExecutor.sol:55-56`). The same transactions are
`ExecutorUpgradeChainWitness`'s run in `ExecutorUpgradeChain`. -/
def wReplaceRun : List ULabel :=
  [.x (.env (.genesis 0)), .x (.commit 300), .x (.forward [.sys (.ctm (.replace 300 400))]),
    .upgradeChain 400 0]

end Contracts.ChainTypeManager.EngineGetters
