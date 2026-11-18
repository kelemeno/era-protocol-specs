import EraSpec.Contracts.ChainTypeManager.Specs.ChainRouting
import EraSpec.Contracts.ChainTypeManager.Specs.L2Derivation

/-!
# Model: the L2 implementations of the chains on a `ChainTypeManager`, along registry runs

Source: era-contracts branch `draft/v0.35.0` at commit `b17415d20`, as for
`Specs/L2Derivation.lean`, whose derivation this model runs. Paths are relative to
`l1-contracts/contracts/`. Chain ids are `Specs/ChainRouting.lean`'s `ChainId`; nothing else of
that topic is used.

**This file is definitions only.** Statements: `Properties/L2Convergence.lean`; proofs:
`Proofs/L2Convergence.lean`.

## The L2 state of a chain

A ghost, `L2State`: for each L2 address, the system proxy there as the pair (the shell it was
deployed with, the implementation row it was last upgraded to); `none` where no system proxy
has been deployed. It is what `L2GenesisForceDeploymentsHelper.upgradeSystemContractProxy`
writes for one table-derived deployment (`l2-upgrades/L2GenesisForceDeploymentsHelper.sol:113-154`):

    address implAddress = generateRandomAddress(bytecodeInfo);                                 // :124
    ... deploys bytecodeInfo at implAddress unless that address already holds it ...        // :126-142
    if (_newAddress.code.length == 0) { forceDeployOnAddress(bytecodeInfoSystemProxy, _newAddress); ... } // :145-148
    SystemContractProxyAdmin(L2_SYSTEM_CONTRACT_PROXY_ADMIN_ADDR).upgrade(_newAddress, implAddress); // :150-153

The ghost records the row itself where the proxy records `generateRandomAddress(row)`, and the
shell only when the address had no code (`applyProxy`).

## The ways a chain's L2 state changes

1. **Genesis.** `createNewChain` (`state-transition/ChainTypeManager.sol:703-711`) creates the
   diamond at the CTM's `protocolVersion` and runs `genesisUpgrade`, whose L2 transaction is a
   plain `upgrade` delegatecall with no deployment plan (`upgrades/L1GenesisUpgrade.sol:77-104`,
   :92-94). The L2 code a new chain starts with is the genesis state its release's
   `genesisBatchHash` commits to. That state is not computed on L1; it is `L2World.image R`,
   and whether it holds the release's table is the premise `GenesisImageHolds`, which
   `protocol-ops` checks off chain (`protocol-ops/src/upgrade_verification/registry/genesis.rs:311-371`).
2. **Crossing a registry transition** `t` at the chain's version (`Admin.upgradeChainFromVersion`,
   `state-transition/chain-deps/facets/Admin.sol:559-590`, running
   `DefaultUpgrade.upgradeFromTransition`, `upgrades/DefaultUpgrade.sol:29-43`). The engine reads
   the object's own `l2Plan()` and `upgradeTarget()` (`DefaultUpgrade.sol:65-84`), composes the L2
   transaction from that plan (`upgrades/registry/libraries/CTMUpgradeComposer.sol:83-113`), and
   sets it (`upgrades/BaseZkSyncUpgrade.sol:103-105`). On L2, `L2ComplexUpgrader.forceDeployAndUpgradeUniversal`
   runs every deployment in order, then the delegatecall (`l2-upgrades/L2ComplexUpgrader.sol:35-50`).
   The model applies the plan's system-proxy deployments (`applyPlan`).
3. **Crossing the bootstrap edge** committed at the chain's version (`upgrades/BootstrapUpgrade.sol:29-44`):
   the migration's plan installs every nonempty row of its genesis release
   (`RegistryBootstrapMigration.sol:229-241`).
4. **Break-glass**: the CTM owner's `executeUpgrade` (`ChainTypeManager.sol:626-628`) with any cut
   and init, which can set any version and any L2 transaction; or a pre-registry chain crossing
   an opaque legacy cut (`LegacyCut.opaque`, through the old Admin facet's `upgradeCutHash`
   check), which includes a bootstrap version re-cut by `setUpgradeDiamondCut`
   (`Op.legacyRecut`). `L2Step` has no other step for such a crossing. Any version, any L2
   state. So "no break-glass step" in the headline also excludes opaque legacy crossings.

## Modelling choices

* **The CTM is `Specs/VersionRegistry.lean`'s `CTM` and `CStep`**, written at `e561b9cc2`. The
  writers it models are unchanged in what that model reads at `b17415d20`:
  `setNewVersionUpgradeFromTransition` (`ChainTypeManager.sol:403-418`), `replaceUpgradeTransition`
  (:424-443, with `_requireSameDeparture` :472-478 and `_requireOnwardDestination` :498-518;
  `_requireSameDeadline` :483-489 and `_requireExecutable` :449-452 only reject and stay
  omitted), `_commitVersionEdge` (:523-537), `_setCurrentRelease` (:300-318), `initialize`
  (:270-293), `setNewVersionUpgrade` (:794-813) and `setUpgradeDiamondCut` (:837-850).
* **The world.** `L2World` adds to that model's `World` each release's L2 getters (`rel`), each
  object's `l2Plan()` (`plan`), and each release's genesis image (`image`). A transition is
  **L2-genuine** (`L2Genuine`) when its version getters are its releases' versions and its
  `l2Plan()` is what `CTMTransition`'s constructor stores for its two releases and some authored
  input (`ctmTransitionL2`). The CTM checks neither: `_requireExecutable` reads the plan only for
  publication (`ChainTypeManager.sol:449-452`).
* **The authored part of a plan is assumed not to touch a member's system proxy** (`applyPlan`
  ignores `Unsafe` deployments): the delegate's and extras' deployments land at
  `generateRandomAddress(info)`, and the delegatecall runs governance-reviewed code
  (`CTMTransition.sol:24-31`, `TransitionDerivationLib.sol:23-26`). This is a model boundary,
  not a theorem.
* **An L2 upgrade transaction is executed at its crossing, or never** (`L2Label.cross … exec`):
  `exec = true` means it ran to completion with the modelled effect. On the settlement layer a non-patch upgrade requires the previous L2 upgrade transaction to be
  finalized (`BaseZkSyncUpgrade.sol:259-268`), and a patch carries none
  (`VersionEdgeLib.sol:88-90`), so executing each one at its crossing gives the same sequence of
  writes to the L2 state. The diamond modelled for each chain is the one on its settlement layer
  (`BaseZkSyncUpgrade.sol:86-105`); another instance's crossing sets no L2 transaction and is
  not modelled.
* **The bootstrap crossing's plan is the genuine migration's.** `L2Step.bootstrapCross` installs
  `deriveL2DeploymentsFromTable` of the genesis release, which is the genuine
  `RegistryBootstrapMigration`'s `_buildL2Plan`. It inherits `VersionRegistry`'s
  `LegacyCut.bootstrap` abstraction: a legacy commit with `bootstrapForm = true` is taken to be
  that migration's cut. So the bootstrap crossing has no `L2Genuine`-style premise; the
  genuineness of the migration object is an assumption of the model.
* **Not modelled**: the facet routing (topic `ChainRouting`; the guard
  `requireReleaseRouting` is omitted, which only adds runs), callers and timing (topic
  `UpgradeTiming`), migration between settlement layers, the verifier, and the `Unsafe`
  deployments' code.
-/

namespace Contracts.ChainTypeManager.L2Tables

/-! ## The L2 state and the plan's effect -/

/-- A chain's L2 system proxies: at each address, `(shell, implementation row)`, or `none`. -/
abbrev L2State := L2Addr → Option (Bytes × Bytes)

/-- One table-derived deployment executed on L2 (`L2GenesisForceDeploymentsHelper.sol:113-154`):
the proxy at `d.addr` now points at `d.impl`; its shell is `d.shell` if no proxy was there. -/
def applyProxy (σ : L2State) (d : ProxyDeployment) : L2State :=
  fun a => if a = d.addr then some ((σ a).elim d.shell Prod.fst, d.impl) else σ a

/-- A list of them, in order (`L2ComplexUpgrader.sol:41-47`). -/
def applyProxies (ds : List ProxyDeployment) (σ : L2State) : L2State :=
  ds.foldl applyProxy σ

/-- A plan's effect on the system proxies: its system-proxy deployments, in order. -/
def applyPlan (p : L2Plan) (σ : L2State) : L2State :=
  applyProxies (p.deployments.filterMap Deployment.proxyPart) σ

/-- The L2 state of a chain whose genesis installed exactly release `R`'s table: every nonempty
row at its member's fixed address, behind `R`'s shell. Used for witness genesis images. -/
def fullInstall (R : ReleaseL2) : L2State :=
  applyProxies (deriveOut R.table R.shell) (fun _ => none)

/-! ## The world and the system -/

/-- The objects the CTM and the chains read. -/
structure L2World where
  /-- Release versions, routing and transition getters (`Specs/VersionRegistry.lean`). -/
  base : World
  /-- Each release's L2 getters. -/
  rel : Address → ReleaseL2
  /-- Each transition object's `l2Plan()`. -/
  plan : Address → L2Plan
  /-- The L2 state a chain created at release `R` starts with. -/
  image : Address → L2State

/-- A chain: the diamond's `s.protocolVersion` and the L2 state. -/
structure L2Chain where
  /-- `s.protocolVersion`. -/
  pv : ℕ
  /-- The chain's L2 system proxies. -/
  l2 : L2State

/-- The CTM and its chains. -/
structure L2Sys where
  /-- The CTM's version state. -/
  ctm : CTM
  /-- The chains, `none` where no diamond is registered. -/
  chains : ChainId → Option L2Chain

/-- What happens. -/
inductive L2Label
  /-- A CTM writer. -/
  | ctm (op : Op)
  /-- `createNewChain`. -/
  | genesis (id : ChainId)
  /-- Crossing the registry transition `t` committed at the chain's version; `exec` says
  whether the L2 upgrade transaction it sets is executed. -/
  | cross (id : ChainId) (t : Address) (exec : Bool)
  /-- Crossing the bootstrap edge committed at the chain's version. -/
  | bootstrapCross (id : ChainId) (exec : Bool)
  /-- `executeUpgrade` with any cut, or crossing an opaque legacy cut: any version, any L2
  state. -/
  | breakGlass (id : ChainId) (v : ℕ) (σ : L2State)

/-- Put chain `id` in state `c`. -/
def L2Sys.setChain (s : L2Sys) (id : ChainId) (c : L2Chain) : L2Sys :=
  { s with chains := upd s.chains id (some c) }

/-- The break-glass steps. -/
def L2Label.IsBreakGlass : L2Label → Prop
  | .breakGlass _ _ _ => True
  | _ => False

/-- The step executes its L2 upgrade transaction, if it sets one. -/
def L2Label.L2Executed : L2Label → Prop
  | .cross _ _ b => b = true
  | .bootstrapCross _ b => b = true
  | _ => True

instance (l : L2Label) : Decidable l.IsBreakGlass := by
  cases l <;> unfold L2Label.IsBreakGlass <;> infer_instance

instance (l : L2Label) : Decidable l.L2Executed := by
  cases l <;> unfold L2Label.L2Executed <;> infer_instance

/-- One step. -/
inductive L2Step (W : L2World) : L2Sys → L2Label → L2Sys → Prop
  /-- A CTM writer; the chains are untouched. -/
  | ctm {s : L2Sys} {op : Op} {c' : CTM} :
      CStep W.base s.ctm op c' → L2Step W s (.ctm op) { s with ctm := c' }
  /-- `createNewChain`: a fresh chain at the CTM's version, starting from the current release's
  genesis image. -/
  | genesis {s : L2Sys} {id : ChainId} :
      s.chains id = none →
      L2Step W s (.genesis id) (s.setChain id ⟨s.ctm.pv, W.image s.ctm.cur⟩)
  /-- `upgradeChainFromVersion` across `upgradeTransition[c.pv]`: the cut exists only for a
  committed slot (`ChainTypeManager.sol:601-607`), the chain must be at its departing version
  (`Admin.sol:570-572`) and end strictly above it (:587-589); it lands on `newProtocolVersion()`
  and, if `exec`, its L2 state takes the plan's deployments. -/
  | cross {s : L2Sys} {id : ChainId} {c : L2Chain} {t : Address} {b : Bool} :
      s.chains id = some c →
      s.ctm.ut c.pv = t → t ≠ 0 →
      c.pv < (W.base.tr t).new →
      L2Step W s (.cross id t b)
        (s.setChain id ⟨(W.base.tr t).new, if b then applyPlan (W.plan t) c.l2 else c.l2⟩)
  /-- Crossing the bootstrap edge onto genesis release `R`: the migration's plan installs `R`'s
  whole table, which requires `deriveL2DeploymentsFromTable` not to revert (else the migration
  could not be constructed, `RegistryBootstrapMigration.sol:83`). -/
  | bootstrapCross {s : L2Sys} {id : ChainId} {c : L2Chain} {R : Address}
      {ds : List ProxyDeployment} {b : Bool} :
      s.chains id = some c →
      s.ctm.legacy c.pv = LegacyCut.bootstrap R →
      c.pv < W.base.relVersion R →
      deriveL2DeploymentsFromTable (W.rel R).table (W.rel R).shell = some ds →
      L2Step W s (.bootstrapCross id b)
        (s.setChain id ⟨W.base.relVersion R, if b then applyProxies ds c.l2 else c.l2⟩)
  /-- Break-glass: any version, any L2 state. -/
  | breakGlass {s : L2Sys} {id : ChainId} {c : L2Chain} (v : ℕ) (σ : L2State) :
      s.chains id = some c →
      L2Step W s (.breakGlass id v σ) (s.setChain id ⟨v, σ⟩)

/-- A sequence of steps. -/
inductive L2Run (W : L2World) : L2Sys → List L2Label → L2Sys → Prop
  | nil {s : L2Sys} : L2Run W s [] s
  | cons {s s' s'' : L2Sys} {l : L2Label} {ls : List L2Label} :
      L2Step W s l s' → L2Run W s' ls s'' → L2Run W s (l :: ls) s''

/-! ## Predicates -/

/-- **`t` is an L2-genuine `CTMTransition`**: its version getters are its releases' versions,
and its `l2Plan()` is the plan `CTMTransition`'s constructor stores for its two releases and some
authored input. -/
def L2Genuine {H : Type} [DecidableEq H] (kec : Bytes → H) (rnd : Bytes → L2Addr) (W : L2World)
    (t : Address) : Prop :=
  W.base.Genuine t ∧
    ∃ e, ctmTransitionL2 kec rnd (W.base.relVersion (W.base.tr t).fromRel)
      (W.base.relVersion (W.base.tr t).newRel) (W.rel (W.base.tr t).fromRel)
      (W.rel (W.base.tr t).newRel) e = some (W.plan t)

/-- **`σ` runs release `R`'s L2 implementations**: at every member with a fixed address and a
nonempty row in `R`'s table, a system proxy points at that row. -/
def RunsReleaseL2 (W : L2World) (R : Address) (σ : L2State) : Prop :=
  ∀ i a, fixedAddress i = some a → rowAt (W.rel R).table i ≠ [] →
    ∃ sh, σ a = some (sh, rowAt (W.rel R).table i)

/-- **Release `R`'s genesis image holds its table**: at every member with a fixed address and a
nonempty row, the release's shell over that row (what `judge_genesis_image` checks off chain). -/
def GenesisImageHolds (W : L2World) (R : Address) : Prop :=
  ∀ i a, fixedAddress i = some a → rowAt (W.rel R).table i ≠ [] →
    W.image R a = some ((W.rel R).shell, rowAt (W.rel R).table i)

/-- The invariant: the CTM's (`CtmInv`), and every chain is at most at the CTM's version and, if
the CTM has a release for its version, runs that release's L2 implementations. -/
def L2Inv (W : L2World) (s : L2Sys) : Prop :=
  CtmInv W.base s.ctm ∧
    ∀ id c, s.chains id = some c →
      c.pv ≤ s.ctm.pv ∧ (s.ctm.relAt c.pv ≠ 0 → RunsReleaseL2 W (s.ctm.relAt c.pv) c.l2)

/-- **A row clash on transition `t`'s pair**: some member's rows in `t`'s departing and target
releases are distinct with equal hashes. -/
def CrossClash {H : Type} (kec : Bytes → H) (W : L2World) (t : Address) : Prop :=
  ∃ i, KeccakClash kec (rowAt (W.rel (W.base.tr t).fromRel).table i)
    (rowAt (W.rel (W.base.tr t).newRel).table i)

/-- The starting system after `initialize(R)`: no chains. -/
def freshL2Sys (W : L2World) (R : Address) : L2Sys := ⟨initState W.base R, fun _ => none⟩

/-- The starting system after the bootstrap from version `old` onto `R`, with pre-registry
chains `pre`. -/
def bootstrapL2Sys (W : L2World) (old : ℕ) (R : Address) (pre : ChainId → Option L2Chain) :
    L2Sys :=
  ⟨bootstrapState W.base old R, pre⟩

/-! ## Witness data: three ways onto one version

Releases `100`, `200`, `250` at versions `2^32`, `2·2^32`, `3·2^32` (minors 1, 2, 3).
`100 → 200` changes row 0; `200 → 250` changes row 1, adds row 2 and a new shell; the skip
`100 → 250` does all three. Transitions `300` (`100 → 200`), `600` (`200 → 250`) and `700`
(`100 → 250`) are L2-genuine with a delegate. Genesis images install the whole table. -/

/-- The witness versions: minor `k`. -/
def cvV (k : ℕ) : ℕ := k * 2 ^ 32

/-- Release versions. -/
def cvRelVersion : Address → ℕ := fun a =>
  if a = 100 then cvV 1 else if a = 200 then cvV 2 else if a = 250 then cvV 3 else 0

/-- Transition getters. -/
def cvTr : Address → TransitionView := fun a =>
  if a = 300 then ⟨cvV 1, cvV 2, 100, 200⟩
  else if a = 600 then ⟨cvV 2, cvV 3, 200, 250⟩
  else if a = 700 then ⟨cvV 1, cvV 3, 100, 250⟩
  else ⟨0, 0, 0, 0⟩

/-- The CTM-facing world (routing is not used here). -/
def cvBase : World := ⟨cvRelVersion, fun _ => [], cvTr⟩

/-- Release L2 getters. -/
def cvRel : Address → ReleaseL2 := fun a =>
  if a = 100 then wRel [wDesc 1, wDesc 2]
  else if a = 200 then wRel [wDesc 3, wDesc 2]
  else if a = 250 then ⟨[wDesc 3, wDesc 4, wDesc 5], wDesc 51, [7], wGenesis, fun _ => []⟩
  else wRel []

/-- What `CTMTransition`'s constructor stores for transition `t` of `base`/`rel` with the
minor-edge input, the empty plan if it reverts. -/
def genuinePlanOf (base : World) (rel : Address → ReleaseL2) (t : Address) : L2Plan :=
  (ctmTransitionL2 (id : Bytes → Bytes) wRnd (base.relVersion (base.tr t).fromRel)
    (base.relVersion (base.tr t).newRel) (rel (base.tr t).fromRel) (rel (base.tr t).newRel)
    wMinorEdge).getD ⟨[], 0, 0⟩

/-- The witness world: genuine plans, whole-table genesis images. -/
def cvWorld : L2World :=
  ⟨cvBase, cvRel, genuinePlanOf cvBase cvRel, fun R => fullInstall (cvRel R)⟩

/-- The same world, except that object `300`'s `l2Plan()` omits the derived deployment: it is
not L2-genuine. -/
def cvWorldStalePlan : L2World :=
  ⟨cvBase, cvRel,
    fun t => if t = 300 then ⟨[.unsafeForce 0x1234 (wDesc 90)], 0x1234, 77⟩
      else genuinePlanOf cvBase cvRel t,
    fun R => fullInstall (cvRel R)⟩

/-- The same world, except that release `200`'s genesis image is release `100`'s whole-table
install: a genesis state that does not hold `200`'s table. -/
def cvWorldStaleImage : L2World :=
  ⟨cvBase, cvRel, genuinePlanOf cvBase cvRel,
    fun R => if R = 200 then fullInstall (cvRel 100) else fullInstall (cvRel R)⟩

/-- A fresh CTM on release `100`, no chains. -/
def cvSys0 : L2Sys := freshL2Sys cvWorld 100

/-- One pre-registry chain, `5`, at version 0: a system proxy at member 0's fixed address with
an old shell (`wDesc 60`) over an old row (`wDesc 61`), nothing at member 1's. -/
def cvPre : ChainId → Option L2Chain :=
  upd (fun _ => none) 5 (some ⟨0, upd (fun _ => none) 0x10002 (some (wDesc 60, wDesc 61))⟩)

/-- The witness run: chains `0` and `1` are created at version 1; the CTM commits `300` and
chain `0` crosses it; the CTM commits `600` and chain `0` crosses it; `300` is replaced by the
skip `700` and chain `1` crosses that; chain `2` is created at version 3. -/
def cvLabels : List L2Label :=
  [.genesis 0, .genesis 1, .ctm (.commit 300), .cross 0 300 true, .ctm (.commit 600),
    .cross 0 600 true, .ctm (.replace 300 700), .cross 1 700 true, .genesis 2]

/-! ## Witness data: the frozen row along a CTM run

Releases `100`, `200`, `250` at versions `2^32`, `2·2^32`, `3·2^32`, all 27-row tables passing
`CTMRelease`'s table checks: `100` has rows 0 and 14 (`BeaconProxy`, no fixed address); `200`
changes row 0 and keeps row 14; `250` changes row 14. Transition `300` is `100 → 200`. -/

/-- Release versions. -/
def fzRelVersion : Address → ℕ := fun a =>
  if a = 100 then cvV 1 else if a = 200 then cvV 2 else if a = 250 then cvV 3 else 0

/-- Transition getters. -/
def fzTr : Address → TransitionView := fun a =>
  if a = 300 then ⟨cvV 1, cvV 2, 100, 200⟩ else ⟨0, 0, 0, 0⟩

/-- The CTM-facing world. -/
def fzBase : World := ⟨fzRelVersion, fun _ => [], fzTr⟩

/-- Release L2 getters. -/
def fzRel : Address → ReleaseL2 := fun a =>
  if a = 100 then wRel27 (wDesc 1) (wDesc 14)
  else if a = 200 then wRel27 (wDesc 2) (wDesc 14)
  else wRel27 (wDesc 1) (wDesc 15)

/-- The frozen-row world. -/
def fzWorld : L2World :=
  ⟨fzBase, fzRel, genuinePlanOf fzBase fzRel, fun R => fullInstall (fzRel R)⟩

end Contracts.ChainTypeManager.L2Tables
