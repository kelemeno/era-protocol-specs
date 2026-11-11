import EraSpec.Contracts.ChainTypeManager.Specs.ChainRouting
import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsCurrent

/-!
# Model: the CTM executor, including its owner-only `forward`

Source: branch `feat/upgrade-simplification` of the zksync-era `contracts` repository at
commit `e561b9cc2` (2026-10-19), as for the rest of this folder. Paths are relative to
`l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.ExecutorForward` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorForward`.

## Why this is modelled

The other topics of this folder take the CTM's writers one call at a time and admit any
caller. They leave out what the CTM's owner can do *besides* calling the CTM: the owner, a
`CTMUpgradeExecutor`, also owns the CTM domain's `ProxyAdmin`, which administers the CTM
proxy itself (`upgrades/registry/executors/CTMUpgradeExecutor.sol:38-40`). The assumption
register lists this as not modelled (`MODEL-CTM-ROUTING`: "CTM proxy implementation swaps";
`MODEL-UPGRADE-AUTHORITY`: "the CTM executor's own `forward`").

## The executor's entry points

`CTMUpgradeExecutor` (`upgrades/registry/executors/CTMUpgradeExecutor.sol`):

    function applyInfrastructureUpgrade(IProxyUpgradeTransition _infrastructureTransition) external onlyOwner {
        ProxyUpgradeRowLib.applyTransition(CTM_PROXY_ADMIN, _infrastructureTransition, ProxyUpgradeDomain.CTM);
        …                                                                          // :64-67
    function applyCTMUpgrade(ICTMTransition _transition) external onlyOwner {
        address(_transition).requireCode();
        CHAIN_TYPE_MANAGER.setNewVersionUpgradeFromTransition(_transition);
        …
        _requireTransitionApplied(_transition);                                    // :72-84
    function upgradeChain(ICTMTransition _transition, uint256 _chainId) external { // :87-102
        … CHAIN_TYPE_MANAGER.upgradeChainFromVersion(_chainId, oldProtocolVersion);

and, inherited from `governance/UpgradeExecutorBase.sol:32-46`:

    function forward(Call[] calldata _calls) external payable onlyOwner {
        for (uint256 i = 0; i < _calls.length; ++i) {
            (bool success, bytes memory returnData) = _calls[i].target.call{value: _calls[i].value}(_calls[i].data);
            if (!success) { assembly { revert(add(returnData, 0x20), mload(returnData)) } }
            emit CallForwarded(_calls[i].target, _calls[i].value, _calls[i].data);
        }
    }

The contract's own description (`CTMUpgradeExecutor.sol:25-29`): "Every other owner
operation of the CTM (freezing a chain, moving a deadline, replacing a committed
transition, ...) goes through the owner-gated, event-logged `forward`". `forward` is not
restricted to the CTM: any target, any calldata, with the executor as `msg.sender`, all
calls atomic.

## Modelling choices

* **State**: the CTM and its chains (`Sys`, from `ChainRouting`) and the live
  implementation behind each proxy (`ProxyUpgradeCurrent.Impl`). `ctmProxy` is the CTM's
  own proxy (`CHAIN_TYPE_MANAGER`).
* **A forwarded call to the CTM** is any `ChainRouting` step (`FCall.sys`). This
  over-approximates: it admits labels the executor cannot cause (`genesis`, `migrateIn`),
  and it includes the break-glass `executeUpgrade` (`ChainTypeManager.sol:631-633`,
  `onlyOwner`), which the executor has no fixed entry point for.
* **A forwarded `ProxyAdmin` call** is `upgrade`/`upgradeAndCall` on the CTM domain's
  `ProxyAdmin`. On a proxy other than the CTM (`FCall.upgradeProxy`), it sets the
  implementation with no source check; what the reinitializer does to that proxy's own
  storage is not modelled. On the CTM proxy (`FCall.swapCtm`), the CTM afterwards runs
  code the model does not know, so its version state may be anything (`c'` is
  arbitrary); the chains are left as they were.
* **`applyInfrastructureUpgrade`** is `ProxyUpgradeCurrent.ApplyTransition` on the CTM
  domain. If it moves the CTM proxy's implementation, the CTM's version state afterwards
  is arbitrary, as for `swapCtm`; if not, the CTM is untouched.
* **`applyCTMUpgrade`** is the registry commit plus the executor's post-check
  (`_requireTransitionApplied`, `:104-116`). **`upgradeChain`** is the transition step.
* **Other actors** (`XLabel.env`): `createNewChain` (Bridgehub), migration in, and
  crossing the bootstrap edge.
* **Not modelled**: ownership transfers through `forward` (of the CTM, the `ProxyAdmin`,
  the executor itself), CTM owner functions that touch no modelled state (deadlines,
  validators, fees, freezing), calls to other targets, ETH. The `ProxyAdmin`'s owner and
  `hasCode` are fixed configuration (`XConfig.rc`).
-/

namespace Contracts.ChainTypeManager

/-- The executor's bindings and the configuration its rows run under. -/
structure XConfig where
  /-- The deployed release and transition objects. -/
  W : World
  /-- The row library's configuration: `self` is the executor, `adminOwner` is
  `CTM_PROXY_ADMIN.owner()`. -/
  rc : ProxyUpgradeCurrent.Config
  /-- `CHAIN_TYPE_MANAGER`: the CTM's own proxy, administered by `CTM_PROXY_ADMIN`. -/
  ctmProxy : Address

/-- The CTM, its chains, and the implementations behind the CTM domain's proxies. -/
structure XState where
  /-- The CTM's version state and its chains. -/
  sys : Sys
  /-- `CTM_PROXY_ADMIN.getProxyImplementation(p)` for each proxy `p`. -/
  impl : ProxyUpgradeCurrent.Impl

/-- One call made by `forward`. -/
inductive FCall
  /-- A call to the CTM (any `ChainRouting` step). -/
  | sys (l : Label)
  /-- `CTM_PROXY_ADMIN.upgrade(p, x)` or `upgradeAndCall(p, x, data)` for a proxy `p` other
  than the CTM. -/
  | upgradeProxy (p x : Address)
  /-- The same on the CTM's own proxy, leaving the CTM's version state at `c'`. -/
  | swapCtm (x : Address) (c' : CTM)

/-- One forwarded call that succeeds. -/
inductive FStep (X : XConfig) : XState → FCall → XState → Prop
  | sys {s : XState} {l : Label} {sys' : Sys} :
      Step X.W s.sys l sys' → FStep X s (.sys l) { s with sys := sys' }
  /-- `ProxyAdmin.upgrade` is `onlyOwner`, and the new implementation must be code. No
  source check. -/
  | upgradeProxy {s : XState} {p x : Address} :
      X.rc.adminOwner = X.rc.self → X.rc.hasCode x → p ≠ X.ctmProxy →
      FStep X s (.upgradeProxy p x) { s with impl := ProxyUpgradeCurrent.upd s.impl p x }
  | swapCtm {s : XState} {x : Address} {c' : CTM} :
      X.rc.adminOwner = X.rc.self → X.rc.hasCode x →
      FStep X s (.swapCtm x c')
        ⟨{ s.sys with ctm := c' }, ProxyUpgradeCurrent.upd s.impl X.ctmProxy x⟩

/-- The calls of one `forward`, in order; a failing call reverts them all. -/
inductive FRun (X : XConfig) : XState → List FCall → XState → Prop
  | nil {s : XState} : FRun X s [] s
  | cons {s s' s'' : XState} {c : FCall} {cs : List FCall} :
      FStep X s c s' → FRun X s' cs s'' → FRun X s (c :: cs) s''

/-- What happens. -/
inductive XLabel
  /-- `applyInfrastructureUpgrade(T)`. -/
  | infra (T : ProxyUpgradeCurrent.Transition)
  /-- `applyCTMUpgrade(t)`. -/
  | commit (t : Address)
  /-- `upgradeChain(_, id)`. -/
  | upgradeChain (id : ChainId)
  /-- `forward(calls)`. -/
  | forward (calls : List FCall)
  /-- Another actor's step. -/
  | env (l : Label)

/-- The steps other actors take: chain creation, migration in, the bootstrap crossing. -/
def Label.isEnv : Label → Prop
  | .genesis _ => True
  | .migrateIn _ => True
  | .bootstrapReset _ => True
  | _ => False

/-- One successful transaction. -/
inductive XStep (X : XConfig) : XState → XLabel → XState → Prop
  /-- `applyInfrastructureUpgrade`: the rows through `CTM_PROXY_ADMIN`; if the CTM proxy's
  implementation moved, its version state is unknown afterwards. -/
  | infra {s : XState} {T : ProxyUpgradeCurrent.Transition} {J : ProxyUpgradeCurrent.Impl}
      {c' : CTM} :
      ProxyUpgradeCurrent.ApplyTransition X.rc .ctm T s.impl J →
      (J X.ctmProxy = s.impl X.ctmProxy → c' = s.sys.ctm) →
      XStep X s (.infra T) ⟨{ s.sys with ctm := c' }, J⟩
  /-- `applyCTMUpgrade`: the commit, then `_requireTransitionApplied`. -/
  | commit {s : XState} {t : Address} {sys' : Sys} :
      Step X.W s.sys (.ctm (.commit t)) sys' →
      sys'.ctm.ut (X.W.tr t).old = t → (X.W.tr t).new ≤ sys'.ctm.pv →
      XStep X s (.commit t) { s with sys := sys' }
  /-- `upgradeChain`. -/
  | upgradeChain {s : XState} {id : ChainId} {sys' : Sys} :
      Step X.W s.sys (.transition id) sys' → XStep X s (.upgradeChain id) { s with sys := sys' }
  /-- `forward`. -/
  | forward {s s' : XState} {calls : List FCall} :
      FRun X s calls s' → XStep X s (.forward calls) s'
  /-- Another actor. -/
  | env {s : XState} {l : Label} {sys' : Sys} :
      l.isEnv → Step X.W s.sys l sys' → XStep X s (.env l) { s with sys := sys' }

/-- A sequence of successful transactions. -/
inductive XRun (X : XConfig) : XState → List XLabel → XState → Prop
  | nil {s : XState} : XRun X s [] s
  | cons {s s' s'' : XState} {x : XLabel} {xs : List XLabel} :
      XStep X s x s' → XRun X s' xs s'' → XRun X s (x :: xs) s''

/-- A forwarded call that neither cuts a chain by break-glass nor swaps the CTM's code. -/
def FCall.Tame : FCall → Prop
  | .sys l => ¬ l.isArbitrary
  | .upgradeProxy _ _ => True
  | .swapCtm _ _ => False

/-- A transaction that neither cuts a chain by break-glass nor moves the CTM proxy: an
infrastructure transition whose rows do not name the CTM proxy, or a forward of tame
calls. -/
def XLabel.Tame (X : XConfig) : XLabel → Prop
  | .infra T => ∀ r ∈ T.rows, r.proxy ≠ X.ctmProxy
  | .forward calls => ∀ c ∈ calls, c.Tame
  | _ => True

/-- Every proxy whose implementation changed between `s` and `s'` moved along an edge of a
row of the infrastructure transition `x` applied. -/
def MovesOnlyAlongRows (s s' : XState) (x : XLabel) : Prop :=
  ∀ p, s'.impl p = s.impl p ∨
    ∃ T r, x = .infra T ∧ r ∈ T.rows ∧ r.proxy = p ∧
      s.impl p = r.expectedOldImpl ∧ s'.impl p = r.implNew

/-! ## Witness data

The `ChainRouting` witness world; the row library's witness configuration (the executor
`1` owns its admin, reinitializers inert); the CTM proxy is `8`. The domain transition
`3` carries rows `5: 10 → 11` and `6: 10 → 12`. -/

/-- The witness executor. -/
def wX : XConfig := ⟨wWorld, ProxyUpgradeCurrent.wConfig, 8⟩

/-- A fresh CTM on release `100` with no chains; every proxy at implementation `10`. -/
def wX0 : XState := ⟨wSys0, ProxyUpgradeCurrent.wImpl⟩

/-- The CTM-domain transition of the witness. -/
def wInfra : ProxyUpgradeCurrent.Transition :=
  ⟨3, .ctm, [ProxyUpgradeCurrent.rowA, ProxyUpgradeCurrent.rowB]⟩

end Contracts.ChainTypeManager
