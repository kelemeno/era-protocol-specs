import EraSpec.Contracts.ChainTypeManager.Specs.ExecutorForward

/-!
# Model: `applyInfrastructureUpgrade` at `draft/v0.35.0`, which delegatecalls the engine a transition names

Source: matter-labs/era-contracts branch `draft/v0.35.0` at commit **`d9f6789`**, which
contains the change of #2654 (commit `95b5c469d`). Paths are relative to
`l1-contracts/contracts/`; every `file:line` below is at `d9f6789`. The rest of this folder
is pinned to `feat/upgrade-simplification` at `e561b9cc2`. This file extends the
`ExecutorForward` model (`Specs/ExecutorForward.lean`, at `e561b9cc2`), which it imports
unchanged, and reuses the row library model `ProxyUpgradeCurrent` (`e561b9cc2`), whose
`applyRows` is unchanged at `d9f6789` apart from moving its second loop into
`requireRowsApplied` (`upgrades/registry/libraries/ProxyUpgradeRowLib.sol:101-123, 128-136`).

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.ExecutorEngineAtV35` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorEngineAtV35`. The namespace is
`Contracts.ChainTypeManager.ExecutorEngineAtV35`.

## What changed since `e561b9cc2`

At `e561b9cc2`, `applyInfrastructureUpgrade(T)` ran `ProxyUpgradeRowLib.applyTransition`:
code and `domain()` checks on `T`, then `applyRows(CTM_PROXY_ADMIN, T.rows())`. That
function is deleted. At `d9f6789` (`upgrades/registry/executors/CTMUpgradeExecutor.sol:64-72`):

    function applyInfrastructureUpgrade(IProxyUpgradeTransition _infrastructureTransition) external onlyOwner {
        _applyProxyUpgradeTransition(CTM_PROXY_ADMIN, _infrastructureTransition, ProxyUpgradeDomain.CTM,
            address(CHAIN_TYPE_MANAGER));
        emit CTMInfrastructureUpgradeApplied(address(_infrastructureTransition));
    }

and `_applyProxyUpgradeTransition` (`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:48-98`):

    ObjectAnchorLib.requireCode(address(_transition));                                   // :54
    ProxyUpgradeTransitionManifest memory manifest = _transition.getManifest();         // :55
    if (manifest.domain != _domain) { revert ProxyUpgradeDomainMismatch(...); }         // :56-58
    ObjectAnchorLib.requireCode(manifest.proxyUpgradeEngine);                           // :60
    ProxyUpgradeContext memory context = ProxyUpgradeContext({...});                    // :62-68
    address ownerBefore = owner();                                                      // :69
    address pendingOwnerBefore = pendingOwner();                                        // :70
    address serverNotifier = ... IChainTypeManager(_chainTypeManager).serverNotifierAddress(); // :71-73
    bytes32 domainHoldersBefore = _domainHolders(_proxyAdmin, _chainTypeManager, serverNotifier); // :74
    (bool success, bytes memory returnData) = manifest.proxyUpgradeEngine.delegatecall(
        abi.encodeCall(IProxyUpgradeEngine.executeUpgrade, (context, manifest.proxyUpgrades))); // :76-78
    if (!success) { assembly { revert(add(returnData, 0x20), mload(returnData)) } }    // :79-85
    if (owner() != ownerBefore || pendingOwner() != pendingOwnerBefore) {
        revert ProxyUpgradeEngineChangedExecutorOwnership(manifest.proxyUpgradeEngine); } // :87-89
    if (_domainHolders(_proxyAdmin, _chainTypeManager, serverNotifier) != domainHoldersBefore) {
        revert ProxyUpgradeEngineMovedDomainAuthority(manifest.proxyUpgradeEngine); }    // :90-92
    ProxyUpgradeRow[] memory rows = ProxyUpgradeRowLib.toRows(manifest.proxyUpgrades,
        ProxyUpgradeRowLib.inventoryLength(_domain));                                   // :93-96
    ProxyUpgradeRowLib.requireRowsApplied(_proxyAdmin, rows);                           // :97

`_domainHolders` (`:109-139`) is `keccak256(abi.encode(...))` of the `ProxyAdmin`'s
`owner()`, the CTM's `owner()`, `pendingOwner()` and `getProxyAdmin(ctm)`, and, with a
ServerNotifier, the same three for it.

**Which engine runs.** The transition object names it. `ProxyUpgradeTransition`'s
constructor only requires it to be nonzero
(`upgrades/registry/objects/ProxyUpgradeTransition.sol:39-41`), and the executor only
requires it to have code (`ProxyUpgradeExecutorBase.sol:60`). The only engine in the tree is
`DefaultProxyUpgradeEngine` (`upgrades/registry/engines/DefaultProxyUpgradeEngine.sol:32-46`):

    ProxyAdmin proxyAdmin = ProxyAdmin(_context.proxyAdmin);
    address proxyAdminOwner = proxyAdmin.owner();
    if (proxyAdminOwner != address(this)) { revert ProxyUpgradeEngineAuthorityMismatch(...); } // :33-37
    ProxyUpgradeRow[] memory inventory = _inventory;                                    // :38
    _beforeSwaps(_context, inventory);                                                  // :39
    ProxyUpgradeRowLib.applyRows(proxyAdmin,
        ProxyUpgradeRowLib.toRows(inventory, ProxyUpgradeRowLib.inventoryLength(_context.domain))); // :40-43
    _afterSwaps(_context, inventory);                                                   // :44
    _checkPostconditions(_context, inventory);                                          // :45

with three empty `internal virtual` hooks (`:51`, `:56`, `:62-65`) that a release's subclass
overrides with its follow-up calls. `executeUpgrade` itself is not virtual. Under the
delegatecall `address(this)` is the executor, so the first check is "the executor owns its
`ProxyAdmin`".

**What an engine can do.** It runs with the executor's storage and authority
(`IProxyUpgradeEngine.sol:10-18`; `ProxyUpgradeExecutorBase.sol:32-38`). The executor owns
the CTM (`CTMUpgradeExecutor.sol:20-22`) and the CTM domain's `ProxyAdmin` (`:38-40`), so an
engine can make every call a `forward` can make to them
(`governance/UpgradeExecutorBase.sol:34-48`), including the CTM's break-glass
`executeUpgrade` (`state-transition/ChainTypeManager.sol:626-628`, `onlyOwner`) and
`ProxyAdmin.upgrade` of any proxy the admin administers, the CTM's own included. The
repository's own documentation says so: "A release's pinned upgrade engine reaches the same
methods from inside `applyInfrastructureUpgrade` ... so every `forward` cell below holds for it
too, except the last row" (`docs/registry-driven-upgrades.md:449-453`, repository root).

**What the executor checks afterwards** is exactly the list above: its own `owner` and
`pendingOwner`, the domain-holders hash, and every row at its `implNew`. Its NatSpec says:
"Anything else the engine does is what governance reviewed when it approved the transition,
and the engine's own postconditions" (`ProxyUpgradeExecutorBase.sol:37-38`).

**The NatSpec under review.** `ICTMUpgradeExecutor.sol:33-34`, unchanged since `e561b9cc2`:
"Applies a CTM-domain transition's source-checked implementation swaps through the bound CTM
`ProxyAdmin`, and verifies every row at its `implNew` before returning." At `d9f6789` the
first half is the engine's behaviour, not the executor's.

**What governance must check** of the engine is named here as two premises. `EngineIsTame`
(the engine makes no break-glass cut and does not move the CTM proxy) is what the CTM's
invariants need. `EngineReviewed` (the engine runs `DefaultProxyUpgradeEngine`'s core, and its
hooks make only CTM calls that are not break-glass cuts) is what source-checked swaps need; for
rows that do not name the CTM proxy it implies `EngineIsTame`. `DefaultProxyUpgradeEngine`
meets both.

## Modelling choices

* **State** (`V35State`): `ExecutorForward`'s `XState` (the CTM, its chains, the CTM domain's
  implementations), plus the executor's own `owner()` and `pendingOwner()`, plus the seven
  values `_domainHolders` hashes. The latter two are **ghosts**: they are read only by the
  executor's post-checks. As in `ExecutorForward`, the `ProxyAdmin`'s owner that the row
  library reads is the fixed configuration `XConfig.rc.adminOwner`, ownership transfers
  through `forward` are not modelled, and so no other step changes them.
* **A transition object** (`V35Transition`) is its address and its manifest as
  `getManifest()` returns it (`ProxyUpgradeExecutorBase.sol:55`): domain, inventory and engine
  address. `getManifest()` is `view` and is read once, so this describes any object, genuine
  or not. Its rows are `toRows(inventory)` (`ProxyUpgradeRowLib.sol:53-61`); the length check
  in `toRows` is the step premise `inventory.length = inventoryLength(CTM)`.
* **An engine** (`EngineCode`) is what the code at an address does when the executor
  delegatecalls `executeUpgrade` on it for a given transition: a relation from start states to
  end states, with no end state for a revert. `V35Config.code` gives the code at every
  address. Nothing constrains it: every engine governance could approve is covered.
* **The engines of the witnesses** are built from `ExecutorForward`'s forwarded calls
  (`FCall`): what an engine does to the modelled state is a sequence of calls the executor
  makes. `EngineCore` is `DefaultProxyUpgradeEngine.executeUpgrade` between its hooks, with
  the CTM's version state unknown afterwards if the rows moved the CTM proxy, exactly as in
  `XStep.infra`. The engines leave the executor's storage alone. What their swaps and
  reinitializers do to the domain holders is not modelled, so the holders are left arbitrary
  and the executor's check filters.
* **The hash** `_domainHolders` compares is `V35Config.holdersHash`, an arbitrary function: no
  property of keccak is assumed. Where a result depends on the holders being unchanged, it
  says "unchanged, or a collision of `holdersHash` on the logged pair (before, after)".
* **The other entry points** (`applyCTMUpgrade`, `upgradeChain`, `forward`) and the other
  actors are `ExecutorForward`'s steps, unchanged: their bodies at `d9f6789`
  (`CTMUpgradeExecutor.sol:77-89, 92-107`, `UpgradeExecutorBase.sol:34-48`) are those of
  `e561b9cc2`.
* **Reject-only checks.** `_checkPostconditions` (a `view` hook) only rejects and is omitted.
  The `onlyOwner` caller check is omitted, as in `ExecutorForward`. Calls an engine makes that
  touch no modelled state (the ServerNotifier's setters, `setValidatorTimelockPostV29`, events)
  are not represented: in the model they are no-ops.
-/

namespace Contracts.ChainTypeManager.ExecutorEngineAtV35

open Clear

/-! ## Transition objects -/

/-- A `ProxyUpgradeTransition` as the executor reads it: its address and its manifest
(`ProxyUpgradeTransitionManifest`, `upgrades/registry/RegistryTypes.sol:203-207`), read once
through `getManifest()` (`ProxyUpgradeExecutorBase.sol:55`). -/
structure V35Transition where
  /-- The object's address. -/
  addr : Address
  /-- `manifest.domain`. -/
  domain : ProxyUpgradeCurrent.Domain
  /-- `manifest.proxyUpgrades`: the enum-indexed inventory, inert slots included. -/
  inventory : List ProxyUpgradeCurrent.Row
  /-- `manifest.proxyUpgradeEngine`: the code the executor delegatecalls. -/
  engine : Address

/-- The rows: `toRows(manifest.proxyUpgrades, inventoryLength(domain))`
(`ProxyUpgradeExecutorBase.sol:93-96`; `DefaultProxyUpgradeEngine.sol:40-43` computes the
same list). The length check is a separate step premise. -/
def V35Transition.rows (T : V35Transition) : List ProxyUpgradeCurrent.Row :=
  ProxyUpgradeCurrent.toRows T.inventory

/-- The same object as the `e561b9cc2` executor read it, through `domain()` and `rows()`. -/
def V35Transition.toCurrent (T : V35Transition) : ProxyUpgradeCurrent.Transition :=
  ⟨T.addr, T.domain, T.rows⟩

/-- **A GENUINE `ProxyUpgradeTransition`.** What its constructor establishes
(`ProxyUpgradeTransition.sol:27-42`): the inventory has the domain's length (`toRows`,
`:28-31`), at least one row participates (`:34-36`), the rows pass `validateRows` (`:37`) and
the engine is nonzero (`:39-41`). Nothing is established about the engine's code. `n` is
`inventoryLength(T.domain)`. -/
def V35Transition.Genuine (n : ℕ) (T : V35Transition) : Prop :=
  T.inventory.length = n ∧ T.rows ≠ [] ∧ ProxyUpgradeCurrent.ValidRows T.rows ∧ T.engine ≠ 0

/-! ## State -/

/-- The seven values `_domainHolders` hashes (`ProxyUpgradeExecutorBase.sol:109-139`). -/
structure DomainHolders where
  /-- `_proxyAdmin.owner()`. -/
  proxyAdminOwner : Address
  /-- The CTM's `owner()`. -/
  ctmOwner : Address
  /-- The CTM's `pendingOwner()`. -/
  ctmPendingOwner : Address
  /-- `_proxyAdmin.getProxyAdmin(ctm)`. -/
  ctmProxyAdmin : Address
  /-- The ServerNotifier's `owner()`. -/
  notifierOwner : Address
  /-- The ServerNotifier's `pendingOwner()`. -/
  notifierPendingOwner : Address
  /-- `_proxyAdmin.getProxyAdmin(serverNotifier)`. -/
  notifierProxyAdmin : Address
deriving DecidableEq

/-- The executor model's state, plus what the executor reads around the delegatecall. -/
structure V35State where
  /-- The CTM, its chains and the CTM domain's implementations (`ExecutorForward`). -/
  x : XState
  /-- Ghost: the executor's `owner()` (`Ownable2Step`, the executor's own storage). -/
  owner : Address
  /-- Ghost: the executor's `pendingOwner()`. -/
  pendingOwner : Address
  /-- Ghost: the domain holders. -/
  holders : DomainHolders

/-! ## Engines -/

/-- What code does when the executor delegatecalls `executeUpgrade(context, inventory)` on it
(`ProxyUpgradeExecutorBase.sol:76-78`) to apply a transition: the end states it can reach from
a start state. A revert has no end state. The context is built from the executor's bindings
and the transition (`:62-68`), so the transition determines it. -/
abbrev EngineCode := V35Transition → V35State → V35State → Prop

/-- `DefaultProxyUpgradeEngine.executeUpgrade` between its hooks
(`DefaultProxyUpgradeEngine.sol:33-43`): the executor must own its `ProxyAdmin`, then
`applyRows(proxyAdmin, toRows(inventory))`, which is `ProxyUpgradeCurrent.ApplyRows` (code
check, the source-checked loop and the verification pass). If the rows moved the CTM proxy,
the CTM runs other code afterwards and its version state is unknown, as in `XStep.infra`. -/
inductive EngineCore (X : XConfig) (T : V35Transition) : XState → XState → Prop
  | mk {x : XState} {J : ProxyUpgradeCurrent.Impl} {c' : CTM} :
      X.rc.adminOwner = X.rc.self →
      ProxyUpgradeCurrent.ApplyRows X.rc x.impl T.rows J →
      (J X.ctmProxy = x.impl X.ctmProxy → c' = x.sys.ctm) →
      EngineCore X T x ⟨{ x.sys with ctm := c' }, J⟩

/-- **`DefaultProxyUpgradeEngine`**, the genuine row engine: its core with the empty hooks. It
has no storage of its own and writes none of the executor's
(`DefaultProxyUpgradeEngine.sol:25-26`). What the swaps and reinitializers do to the domain
holders is not modelled: any value. -/
def defaultEngine (X : XConfig) : EngineCode := fun T s s' =>
  EngineCore X T s.x s'.x ∧ s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner

/-- A `DefaultProxyUpgradeEngine` subclass whose `_beforeSwaps` makes the calls `pre` and whose
`_afterSwaps` makes the calls `post`, each sent by the executor (the engine runs as the
executor). Holders as in `defaultEngine`. -/
def subclassEngine (X : XConfig) (pre post : List FCall) : EngineCode := fun T s s' =>
  (∃ x₁ x₂, FRun X s.x pre x₁ ∧ EngineCore X T x₁ x₂ ∧ FRun X x₂ post s'.x) ∧
    s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner

/-- An engine that is not built on `DefaultProxyUpgradeEngine`: it makes the calls `calls` and
nothing else; in particular it never runs `applyRows`. Holders as in `defaultEngine`. -/
def callingEngine (X : XConfig) (calls : List FCall) : EngineCode := fun _ s s' =>
  FRun X s.x calls s'.x ∧ s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner

/-- A hook call a release review can admit: a CTM call that is not a break-glass cut. Not
`ProxyAdmin.upgrade`/`upgradeAndCall` on any proxy (the CTM's included), and not the CTM's
`executeUpgrade`. Calls that touch no modelled state are not represented at all. -/
def ReviewedHookCall : FCall → Prop
  | .sys l => ¬ l.isArbitrary
  | _ => False

/-- A hook run: some calls the executor makes, each a `ReviewedHookCall`. -/
def HookRun (X : XConfig) (x x' : XState) : Prop :=
  ∃ cs : List FCall, (∀ c ∈ cs, ReviewedHookCall c) ∧ FRun X x cs x'

/-! ## Configuration -/

/-- The `d9f6789` executor. -/
structure V35Config where
  /-- The `ExecutorForward` executor: the world, the row library's configuration (`self` is the
  executor, `adminOwner` the `ProxyAdmin`'s owner), the CTM proxy. -/
  base : XConfig
  /-- `ProxyUpgradeRowLib.inventoryLength(domain)` (`ProxyUpgradeRowLib.sol:42-44`):
  `CTM_CONTRACT_COUNT` for the CTM domain. -/
  inventoryLength : ProxyUpgradeCurrent.Domain → ℕ
  /-- The code at every address, as an engine. -/
  code : Address → EngineCode
  /-- `keccak256(abi.encode(...))` of the domain holders: an arbitrary function. -/
  holdersHash : DomainHolders → UInt256

/-- The transition pins `DefaultProxyUpgradeEngine`: the code at its engine address is the
genuine row engine. -/
def EngineIsDefault (X : V35Config) (T : V35Transition) : Prop :=
  X.code T.engine = defaultEngine X.base

/-- **WHAT GOVERNANCE MUST CHECK OF THE ENGINE, FOR SOURCE-CHECKED SWAPS.** Every leg the
engine's code can run for this transition is, on the modelled state, a `_beforeSwaps` hook run,
then `DefaultProxyUpgradeEngine`'s core on the manifest's rows, then an `_afterSwaps` hook run,
where the hooks make only CTM calls that are not break-glass cuts. So the review must establish:

* the engine executes `DefaultProxyUpgradeEngine.executeUpgrade` (the admin-owner check and
  `applyRows` on exactly `toRows(inventory)`), not swaps of its own;
* no hook calls `ProxyAdmin.upgrade`/`upgradeAndCall`, on any proxy, the CTM's own included;
* no hook calls the CTM's `executeUpgrade` (a break-glass cut of a chain).

The executor checks none of these (`ProxyUpgradeExecutorBase.sol:86-97`). It does check its own
ownership and the domain holders; the condition says nothing about them. For a transition whose
rows do not name the CTM proxy, this condition implies `EngineIsTame` below, which is all the
CTM's invariants need; the rest of it is what replay safety needs. -/
def EngineReviewed (X : V35Config) (T : V35Transition) : Prop :=
  ∀ s s', X.code T.engine T s s' →
    ∃ x₁ x₂, HookRun X.base s.x x₁ ∧ EngineCore X.base T x₁ x₂ ∧ HookRun X.base x₂ s'.x

/-! ## Steps -/

/-- What happens at `d9f6789`. -/
inductive V35Label
  /-- `applyInfrastructureUpgrade(T)`. -/
  | infra (T : V35Transition)
  /-- `applyCTMUpgrade(t)`. -/
  | commit (t : Address)
  /-- `upgradeChain(_, id)`. -/
  | upgradeChain (id : ChainId)
  /-- `forward(calls)`. -/
  | forward (calls : List FCall)
  /-- Another actor's step. -/
  | env (l : Label)

/-- The `ExecutorForward` label of an entry point whose body is unchanged at `d9f6789`. The
infrastructure leg has none: the function it called at `e561b9cc2` is deleted. -/
def V35Label.toX? : V35Label → Option XLabel
  | .infra _ => none
  | .commit t => some (.commit t)
  | .upgradeChain id => some (.upgradeChain id)
  | .forward calls => some (.forward calls)
  | .env l => some (.env l)

/-- The executor's checks after the engine returns (`ProxyUpgradeExecutorBase.sol:86-97`). -/
structure PostChecks (X : V35Config) (T : V35Transition) (s s' : V35State) : Prop where
  /-- `owner()` unchanged (`:87-89`). -/
  owner : s'.owner = s.owner
  /-- `pendingOwner()` unchanged (`:87-89`). -/
  pendingOwner : s'.pendingOwner = s.pendingOwner
  /-- The domain-holders hash unchanged (`:90-92`). -/
  holders : X.holdersHash s'.holders = X.holdersHash s.holders
  /-- `requireRowsApplied(_proxyAdmin, rows)` (`:93-97`). -/
  rows : ProxyUpgradeCurrent.RowsApplied s'.x.impl T.rows

/-- One successful transaction at `d9f6789`. -/
inductive V35Step (X : V35Config) : V35State → V35Label → V35State → Prop
  /-- `applyInfrastructureUpgrade(T)` (`CTMUpgradeExecutor.sol:64-72`,
  `ProxyUpgradeExecutorBase.sol:48-98`): the object has code (`:54`), is of the CTM domain
  (`:56-58`), its engine has code (`:60`), its inventory has the CTM domain's length (the
  `toRows` check, `:93-96` and `ProxyUpgradeRowLib.sol:57-59`), the engine's leg succeeds
  (`:76-85`), and the post-checks pass (`:86-97`). -/
  | infra {s s' : V35State} {T : V35Transition} :
      X.base.rc.hasCode T.addr →
      T.domain = .ctm →
      X.base.rc.hasCode T.engine →
      T.inventory.length = X.inventoryLength .ctm →
      X.code T.engine T s s' →
      PostChecks X T s s' →
      V35Step X s (.infra T) s'
  /-- Every other entry point and actor: `ExecutorForward`'s step, the ghosts untouched. -/
  | other {s : V35State} {l : V35Label} {x : XLabel} {x' : XState} :
      l.toX? = some x → XStep X.base s.x x x' → V35Step X s l { s with x := x' }

/-- A sequence of successful transactions. -/
inductive V35Run (X : V35Config) : V35State → List V35Label → V35State → Prop
  | nil {s : V35State} : V35Run X s [] s
  | cons {s s' s'' : V35State} {l : V35Label} {ls : List V35Label} :
      V35Step X s l s' → V35Run X s' ls s'' → V35Run X s (l :: ls) s''

/-- `ExecutorForward`'s `XLabel.Tame`, read at `d9f6789`: an infrastructure transition whose
rows do not name the CTM proxy, or a forward of tame calls. At `e561b9cc2` this was the whole
premise of the run invariants (`Properties.TameRunPreservesSysInv`); at `d9f6789` it says
nothing about the engine. -/
def V35Label.Tame (X : V35Config) : V35Label → Prop
  | .infra T => ∀ r ∈ T.rows, r.proxy ≠ X.base.ctmProxy
  | .forward calls => ∀ c ∈ calls, c.Tame
  | _ => True

/-- **WHAT GOVERNANCE MUST CHECK OF THE ENGINE, FOR THE CTM'S INVARIANTS.** Every successful
`applyInfrastructureUpgrade(T)` is, on the modelled state, a run of tame `e561b9cc2` executor
transactions (`XLabel.Tame`): something the owner could have done by `forward`s of CTM calls that
are not break-glass cuts and of `ProxyAdmin.upgrade` on proxies other than the CTM's, and by
`applyInfrastructureUpgrade`s of rows that do not name the CTM proxy. In source terms: the
engine never calls the CTM's `executeUpgrade` and never moves the CTM proxy. The executor checks
neither. Only the engine's code varies between the legs of `T`, so this is a condition on the
engine. -/
def EngineIsTame (X : V35Config) (T : V35Transition) : Prop :=
  ∀ s s', V35Step X s (.infra T) s' →
    ∃ xs : List XLabel, XRun X.base s.x xs s'.x ∧ ∀ x ∈ xs, x.Tame X.base

/-- `ExecutorForward`'s `MovesOnlyAlongRows`, read at `d9f6789`: every proxy whose
implementation changed moved along an edge of a row of the infrastructure transition the step
applied. -/
def V35MovesOnlyAlongRows (s s' : V35State) (l : V35Label) : Prop :=
  ∀ p, s'.x.impl p = s.x.impl p ∨
    ∃ T r, l = .infra T ∧ r ∈ T.rows ∧ r.proxy = p ∧
      s.x.impl p = r.expectedOldImpl ∧ s'.x.impl p = r.implNew

/-! ## Witness data

`ExecutorForward`'s witness executor `wX`: the `ChainRouting` witness world, the row library's
witness configuration (the executor `1` owns its admin, every address has code, reinitializers
inert) and the CTM proxy `8`. Toy inventories have two slots. The engine addresses `70`-`76`
hold the engines below; every other address holds code that reverts. -/

/-- `_afterSwaps` replaces the committed transition `300` by `400` on the CTM. -/
def wHookCalls : List FCall := [.sys (.ctm (.replace 300 400))]

/-- `_afterSwaps` makes the break-glass cut of chain `0` to version 1 with `bgExtra`. -/
def wCutCalls : List FCall := [.sys (.arbitraryCut 0 1 bgExtra)]

/-- `_afterSwaps` swaps the CTM's code for code that leaves the CTM as `initialize(100)` would:
the call of `ExecutorForward`'s `ForwardCtmSwapBreaksInvariants`. -/
def wSwapCalls : List FCall := [.swapCtm 42 (initState wWorld 100)]

/-- The engine code of the witnesses. -/
def wCode : Address → EngineCode := fun a =>
  if a = 70 then defaultEngine wX
  else if a = 71 then subclassEngine wX [] wHookCalls
  else if a = 72 then subclassEngine wX [] wCutCalls
  else if a = 73 then subclassEngine wX [] wSwapCalls
  else if a = 74 then callingEngine wX [.upgradeProxy 5 11]
  else if a = 75 then subclassEngine wX [] [.upgradeProxy 7 42]
  else if a = 76 then subclassEngine wX [.upgradeProxy 5 10] []
  else fun _ _ _ => False

/-- A holders hash: the `ProxyAdmin`'s owner. -/
def wHoldersHash (h : DomainHolders) : UInt256 := h.proxyAdminOwner

/-- The witness executor at `d9f6789`. -/
def wV35 : V35Config := ⟨wX, fun _ => 2, wCode, wHoldersHash⟩

/-- The domain holders of the witness: the executor `1` owns the `ProxyAdmin` `60`, which
administers the CTM and the ServerNotifier, both owned by the executor. -/
def wHolders : DomainHolders := ⟨1, 1, 0, 60, 1, 0, 60⟩

/-- The start: `ExecutorForward`'s fresh state, the executor owned by governance `77`. -/
def wV0 : V35State := ⟨wX0, 77, 0, wHolders⟩

/-- The CTM-domain transition with rows `5: 10 → 11` and `6: 10 → 12`, pinning the engine at
`e`. -/
def wTAB (e : Address) : V35Transition :=
  ⟨3, .ctm, [ProxyUpgradeCurrent.rowA, ProxyUpgradeCurrent.rowB], e⟩

/-- The transition with the one row `5: 10 → 11` (and an inert slot), at address `a`, pinning the
engine at `e`. -/
def wTA (a e : Address) : V35Transition :=
  ⟨a, .ctm, [ProxyUpgradeCurrent.rowA, ProxyUpgradeCurrent.slotInert], e⟩

/-- The later transition with the one row `5: 11 → 12` (and an inert slot), pinning the
default engine. -/
def wTA2 : V35Transition :=
  ⟨31, .ctm, [ProxyUpgradeCurrent.rowA2, ProxyUpgradeCurrent.slotInert], 70⟩

/-- The witness run: apply `wTAB 70` (default engine), create chain `0`, commit `300` (1→2),
upgrade chain `0`, then apply `wTAB 71`, whose `_afterSwaps` replaces `300` by `400`. -/
def wReviewedRun : List V35Label :=
  [.infra (wTAB 70), .env (.genesis 0), .commit 300, .upgradeChain 0, .infra (wTAB 71)]

/-- Two default-engine legs: proxy `5` goes `10 → 11` (`wTA 30 70`), then `11 → 12` (`wTA2`). -/
def wStaleRun : List V35Label := [.infra (wTA 30 70), .infra wTA2]

end Contracts.ChainTypeManager.ExecutorEngineAtV35
