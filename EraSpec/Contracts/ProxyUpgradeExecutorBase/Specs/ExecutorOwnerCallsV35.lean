import EraSpec.Contracts.ChainTypeManager.Specs.VersionRegistry

/-!
# Model: which CTM executor frames make the CTM's owner calls, and what the executor logs (v0.35)

Source: era-contracts `draft/v0.35.0` at commit `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`
(2026-11-16). Every `file:line` below is at that commit; paths are relative to
`l1-contracts/contracts/` unless they start with `docs/` or `protocol-docs/`. The OpenZeppelin
v4 submodules are at the same commits as for `RegistryBootstrapMigration/Specs/Forward.lean`
(`lib/openzeppelin-contracts-upgradeable-v4` at `2d081f2`, `lib/openzeppelin-contracts-v4` at
`dc44c9f`).

**This file is definitions only.** The results are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.ExecutorOwnerCallsV35` and are proved
in `EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.ExecutorOwnerCallsV35`.

## Why this is modelled

The CTM's owner is its `CTMUpgradeExecutor`. The topics pinned at `e561b9cc2`
(`ChainTypeManager` `ExecutorForward`, `RegistryBootstrapMigration` `Forward`) predate the
engine: there an infrastructure leg applies its rows itself. From v0.35 an infrastructure leg
delegatecalls the engine its transition pins
(`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:82-84`; "Its one delegatecall is
into the engine an approved infrastructure transition pins",
`upgrades/registry/executors/CTMUpgradeExecutor.sol:24-25`), and the engine acts with the
executor's authority, the CTM included (`upgrades/registry/engines/IProxyUpgradeEngine.sol:10-13`;
the engine's context names the CTM, `upgrades/registry/RegistryTypes.sol:221-227`). The
documents at this commit describe the routes that result: a release's pinned engine reaches
the CTM's owner methods from inside `applyInfrastructureUpgrade`, not logged as `CallForwarded`,
and the executor's post-check refuses a change of the holders it compares
(`docs/registry-driven-upgrades.md:473-478`, `docs/upgrade-operations.md:115-119`,
`protocol-docs/ecosystem-upgrade-coordination.md:146-153`). This file models every executor
entry point, `forward` and the engine leg together, so those statements can be checked.

## What changed since `d9f6789`

This model was first written at `draft/v0.35.0` commit `d9f678900e1bc8286412b78f56d4a9f443983c29`
and is re-pinned here. Between the two commits `CTMUpgradeExecutor.sol`,
`ICTMUpgradeExecutor.sol`, `ChainTypeManager.sol` and `ObjectAnchorLib.sol` are unchanged. In
the code modelled below three things changed:

* `forward` refuses a call with calldata to an address without code
  (`governance/UpgradeExecutorBase.sol:42-44`); its loop is now :38-54, the log :53.
* Before the engine runs, the leg refuses a CTM whose `admin()` is the `ProxyAdmin`
  (`ProxyUpgradeExecutorBase.sol:72-77`).
* `_domainHolders` (:118-148) reads the ServerNotifier itself on each call (at `d9f6789` it
  was read once, before the engine ran), and it also hashes the CTM's `admin()`, the
  ServerNotifier's address and the ServerNotifier's `chainTypeManager()`.

`governance/IServerNotifier.sol` and `state-transition/IChainTypeManager.sol` gained the getters
the third change reads. The other cited files changed in comments only (`ProxyUpgradeRowLib.sol`,
`RegistryTypes.sol`, `IProxyUpgradeEngine.sol`, `governance/IUpgradeExecutorBase.sol`), or in code the model does not transcribe
(`DefaultProxyUpgradeEngine.sol`, whose acts are a list here); some of their line numbers
moved, and the citations below are the new ones.

## The code modelled

`governance/UpgradeExecutorBase.sol:35-55`:

    function forward(Call[] calldata _calls) external payable onlyOwner {
        for (uint256 i = 0; i < _calls.length; ++i) {
            if (_calls[i].data.length != 0) {
                ObjectAnchorLib.requireCode(_calls[i].target);                         // :42-44
            }
            (bool success, bytes memory returnData) = _calls[i].target.call{value: _calls[i].value}(_calls[i].data);
            if (!success) { assembly { revert(add(returnData, 0x20), mload(returnData)) } }
            emit CallForwarded(_calls[i].target, _calls[i].value, _calls[i].data);   // :53
        }
    }

`upgrades/registry/executors/CTMUpgradeExecutor.sol`:

    function acceptCTMOwnership() external {                                          // :55-61
        if (msg.sender != owner() && msg.sender != ctm.owner()) { revert Unauthorized(msg.sender); }
        ctm.acceptOwnership();
    }
    function applyInfrastructureUpgrade(IProxyUpgradeTransition _infrastructureTransition) external onlyOwner {
        _applyProxyUpgradeTransition(CTM_PROXY_ADMIN, _infrastructureTransition, ProxyUpgradeDomain.CTM,
            address(CHAIN_TYPE_MANAGER));
        emit CTMInfrastructureUpgradeApplied(address(_infrastructureTransition));      // :64-72
    }
    function applyCTMUpgrade(ICTMTransition _transition) external onlyOwner {          // :77-89
        address(_transition).requireCode();
        CHAIN_TYPE_MANAGER.setNewVersionUpgradeFromTransition(_transition);
        emit CTMUpgradeApplied(address(_transition), _transition.oldProtocolVersion(), _transition.newProtocolVersion());
        _requireTransitionApplied(_transition);
    }
    function upgradeChain(ICTMTransition _transition, uint256 _chainId) external {     // :92-107
        if (msg.sender != owner() && msg.sender != CHAIN_TYPE_MANAGER.getChainAdmin(_chainId)) {
            revert Unauthorized(msg.sender);
        }
        uint256 oldProtocolVersion = _transition.oldProtocolVersion();
        address committed = CHAIN_TYPE_MANAGER.upgradeTransition(oldProtocolVersion);
        if (committed != address(_transition)) { revert TransitionNotCommitted(address(_transition), committed); }
        CHAIN_TYPE_MANAGER.upgradeChainFromVersion(_chainId, oldProtocolVersion);
        emit ChainUpgradeApplied(_chainId, _transition.newProtocolVersion());
    }
    function _requireTransitionApplied(ICTMTransition _transition) private view {      // :109-121
        address committed = CHAIN_TYPE_MANAGER.upgradeTransition(oldProtocolVersion);
        if (committed != address(_transition)) { revert TransitionNotCommitted(...); }
        if (currentProtocolVersion < newProtocolVersion) { revert OutdatedProtocolVersion(...); }
    }

`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:51-104`, the leg:

    ObjectAnchorLib.requireCode(address(_transition));                                // :57
    ProxyUpgradeTransitionManifest memory manifest = _transition.getManifest();       // :58
    if (manifest.domain != _domain) { revert ProxyUpgradeDomainMismatch(...); }       // :59-61
    ObjectAnchorLib.requireCode(manifest.proxyUpgradeEngine);                         // :63
    if (_chainTypeManager != address(0) && IChainTypeManager(_chainTypeManager).admin() == address(_proxyAdmin)) {
        revert ProxyUpgradeCTMAdminIsProxyAdmin(_chainTypeManager);                   // :75-77
    }
    address ownerBefore = owner();                                                    // :78
    address pendingOwnerBefore = pendingOwner();                                      // :79
    bytes32 domainHoldersBefore = _domainHolders(_proxyAdmin, _chainTypeManager);     // :80
    (bool success, bytes memory returnData) = manifest.proxyUpgradeEngine.delegatecall(
        abi.encodeCall(IProxyUpgradeEngine.executeUpgrade, (context, manifest.proxyUpgrades)));  // :82-84
    if (!success) { … revert … }                                                      // :85-91
    if (owner() != ownerBefore || pendingOwner() != pendingOwnerBefore) { revert … }  // :93-95
    if (_domainHolders(_proxyAdmin, _chainTypeManager) != domainHoldersBefore) { revert … } // :96-98
    ProxyUpgradeRow[] memory rows = ProxyUpgradeRowLib.toRows(manifest.proxyUpgrades, …);    // :99-102
    ProxyUpgradeRowLib.requireRowsApplied(_proxyAdmin, rows);                         // :103

`_domainHolders` (:118-148), with a CTM:

    address serverNotifier = IChainTypeManager(_chainTypeManager).serverNotifierAddress();   // :123
    bytes32 holders = keccak256(abi.encode(_proxyAdmin.owner(), ctm.owner(), ctm.pendingOwner(),
        IChainTypeManager(_chainTypeManager).admin(),
        _proxyAdmin.getProxyAdmin(ITransparentUpgradeableProxy(_chainTypeManager)), serverNotifier));  // :124-133
    if (serverNotifier == address(0)) { return holders; }                             // :134-136
    return keccak256(abi.encode(holders, notifier.owner(), notifier.pendingOwner(),
        _proxyAdmin.getProxyAdmin(ITransparentUpgradeableProxy(serverNotifier)),
        IServerNotifier(serverNotifier).chainTypeManager()));                         // :137-147

`state-transition/ChainTypeManager.sol` (`Ownable2StepUpgradeable`, :58), the owner functions
modelled one by one:

    function setPendingAdmin(address _newPendingAdmin) external onlyOwnerOrAdmin {   // :354-360
        pendingAdmin = _newPendingAdmin; … }
    function setServerNotifier(address _serverNotifier) external onlyOwner {         // :387-391
        serverNotifierAddress = _serverNotifier; … }
    function setNewVersionUpgradeFromTransition(ICTMTransition _transition) external onlyOwner { … }  // :403-418
    function replaceUpgradeTransition(ICTMTransition _expectedTransition, ICTMTransition _replacement)
        external onlyOwner { … }                                                      // :424-443
    function setProtocolVersionDeadline(uint256 _protocolVersion, uint256 _timestamp) external onlyOwner {
        protocolVersionDeadlines[_protocolVersion] = _timestamp;                      // :564
        emit UpdateProtocolVersionDeadline(_protocolVersion, _timestamp);             // :565
    }
    function upgradeChainFromVersion(uint256 _chainId, uint256 _oldProtocolVersion) external onlyOwner { … }  // :618-621

and `transferOwnership(a)` of `Ownable2StepUpgradeable` (`onlyOwner`; `_pendingOwner = a`).

## Modelling choices

* **A frame is one successful invocation of an executor entry point**, by any caller, at any
  call depth. A revert is the absence of a frame. What the frame's own code does, the engine
  it delegatecalls included, is its trace (`List Obs`), in execution order: the CTM owner calls
  it makes, the logs at the executor's address, and the CTM's own logs for the modelled
  writers. A call the frame makes to another contract that re-enters the executor is a
  separate frame with its own caller and its own trace; its effect on this frame's state is
  covered by the arbitrary-effect calls below.
* **A CTM owner call** (`Obs.ctmCall`) is a successful call, made with the executor as
  `msg.sender`, of a CTM function whose owner gate passes because the executor is the CTM's
  owner (`CtmCall`: every constructor requires the sender to be the owner). Calls that reach
  the CTM some other way (`acceptOwnership`, `acceptAdmin`, a call by the executor as the
  CTM's `admin` only or as the Bridgehub's owner only, a reinitializer run through the
  `ProxyAdmin`) are not owner calls: they are among the arbitrary-effect calls.
* **The CTM runs `ChainTypeManager.sol` at this commit.** `CtmCall` is that code. A swap of
  the CTM proxy's implementation, or of the ServerNotifier's, is an arbitrary-effect call or
  act (`EngStep.upgradeProxy` refuses both proxies), since what their getters and owner
  functions answer afterwards is not this code's; calls to a CTM whose code was swapped, in the
  same frame or an earlier one, are arbitrary-effect calls too, never `CtmCall`s.
* **The CTM** is its owner and pending owner, its `admin` (:113) and `pendingAdmin` (:116,
  private), the version state of `Contracts.ChainTypeManager.CTM` (`protocolVersion` :90,
  `currentRelease` :161, `upgradeTransition` :167), the stored deadlines
  (`protocolVersionDeadlines` :97) and `serverNotifierAddress` (:125). The commit and the
  replacement are `Contracts.ChainTypeManager.CStep`, written at `e561b9cc2`; at this commit
  the two functions (:403-418, :424-443, with `_commitVersionEdge` :523-537,
  `_recordTransition` :459-467, `_setCurrentRelease` :300-318, `_requireSameDeparture`
  :472-478, `_requireOnwardDestination` :498-518) do the same, statement for statement, at
  other line numbers. As there, reject-only checks that read nothing modelled are omitted:
  `_requireExecutable` (:449-452), `release.validate()` (:305), the genesis batch hash
  (:311-314) and `_requireSameDeadline` (:483-489). Omitting a check only adds frames; the
  witnesses use objects that can meet those checks.
* **Every other owner function of the CTM** is `CtmOp.other`: accepted from the owner only,
  with an *arbitrary* effect on the CTM's modelled state. That covers
  `setValidatorTimelockPostV29` (:379), `revertBatches` (:591), `executeUpgrade` (:626), the
  per-chain setters (:633-665), the legacy `setNewVersionUpgrade` (:794), the cut-taking
  `upgradeChainFromVersion` (:821), `setUpgradeDiamondCut` (:837), `renounceOwnership`, and
  `freezeChain` / `unfreezeChain` (:577, :584) when the owner calls them.
  `upgradeChainFromVersion(chainId, oldVersion)` (:618-621) writes no CTM storage; what it
  does to the chain is not modelled, and it never fails here.
* **The engine is the list of things it did** (`EngAct`), carried in the entry
  `Entry.applyInfrastructureUpgrade T acts`: a CTM owner call; a `ProxyAdmin.upgrade` of a
  proxy the `ProxyAdmin` administers, other than the CTM and the ServerNotifier; a log
  (delegatecalled code logs at the executor's address, `docs/upgrade-operations.md:111-113`);
  or `EngAct.other`, anything else, with an arbitrary effect on the whole state (a write to
  the executor's own storage, its owner and nomination included, `upgradeAndCall`'s
  reinitializer, a swap of the CTM or the ServerNotifier, `changeProxyAdmin`, a call to
  another contract, a non-owner call to the CTM). Which act lists a given engine contract can
  produce is not modelled, nor is governance's approval of the transition.
* **A forwarded call** is a CTM owner call (`FwdCall.ctm`) or anything else
  (`FwdCall.other target withData tag`, arbitrary effect; `withData` says whether it carries
  calldata). `value` is not modelled.
* **The holders hash** is `Config.H`, an arbitrary function of the list of reads
  `_domainHolders` hashes (`holdersView`). The two nested `keccak256` calls are one such
  function, since the list fixes whether a ServerNotifier was read. No property assumes
  anything about `H`; where a hash collision matters, the statement names the two lists.
* **`getProxyAdmin`** is the value `CTM_PROXY_ADMIN.getProxyAdmin(p)` returns (`adminOf`): the
  `ProxyAdmin` itself for a proxy it administers, otherwise whatever the proxy's
  implementation answers to `admin()`. A read that reverts (a moved ServerNotifier) only
  removes frames.
* **Rows** are what `toRows` returns (the inventory's non-inert slots, :99-102); the length
  check inside `toRows` and each row's `expectedOldImpl` are not modelled, since the
  executor's own post-check (`requireRowsApplied`,
  `upgrades/registry/libraries/ProxyUpgradeRowLib.sol:133-141`) reads neither.
* **Objects are their getters**, as in `Contracts.ChainTypeManager`: a CTM transition by
  `World.tr` and an infrastructure transition by `Transition` (`getManifest()` is `view`,
  `upgrades/registry/objects/IProxyUpgradeTransition.sol:17`).
* **Not modelled**: `renounceOwnership` on the executor (always reverts,
  `governance/UpgradeExecutorBase.sol:60-62`) and `receive()` (:66), which make no call; the
  OpenZeppelin ownership events; `NewPendingAdmin` and `NewServerNotifier` (:359, :390) and
  `NewUpgradeCutData` (:466); ETH; the chains; callers of the CTM other than the executor
  (the Bridgehub's owner freezing directly, `_checkOwnerOrBridgehubOwner` :235-239, is not an
  executor frame).
-/

namespace Contracts.ExecutorOwnerCallsV35

open Contracts.ChainTypeManager (Address World CTM CStep upd initState wWorld)

/-! ## The CTM -/

/-- A call of an owner function of the CTM (`state-transition/ChainTypeManager.sol`). -/
inductive CtmOp
  /-- `setNewVersionUpgradeFromTransition(t)` (:403-418). -/
  | commit (t : Address)
  /-- `replaceUpgradeTransition(e, r)` (:424-443). -/
  | replace (e r : Address)
  /-- `setProtocolVersionDeadline(v, ts)` (:563-566). -/
  | setDeadline (v ts : ℕ)
  /-- `upgradeChainFromVersion(id, v)` (:618-621). -/
  | upgradeChain (id v : ℕ)
  /-- `transferOwnership(a)` (`Ownable2StepUpgradeable`). -/
  | transferOwnership (a : Address)
  /-- `setPendingAdmin(a)` (:354-360), called by the owner (`onlyOwnerOrAdmin` also admits the
  CTM's admin; that call is not an owner call). -/
  | setPendingAdmin (a : Address)
  /-- `setServerNotifier(n)` (:387-391). -/
  | setServerNotifier (n : Address)
  /-- Any other owner function; `tag` stands for its selector and arguments. -/
  | other (tag : ℕ)
deriving DecidableEq

/-- The CTM's own logs for the version writers and `setProtocolVersionDeadline`. -/
inductive CtmEvent
  /-- `NewProtocolVersion(old, new)` (:536). -/
  | newProtocolVersion (old new : ℕ)
  /-- `NewUpgradeTransition(old, t)` (:465). -/
  | newUpgradeTransition (old : ℕ) (t : Address)
  /-- `NewCurrentRelease(v, R)` (:317). -/
  | newCurrentRelease (v : ℕ) (R : Address)
  /-- `UpgradeTransitionReplaced(old, e, r)` (:441). -/
  | upgradeTransitionReplaced (old : ℕ) (e r : Address)
  /-- `UpdateProtocolVersionDeadline(v, ts)` (:565). -/
  | updateProtocolVersionDeadline (v ts : ℕ)
deriving DecidableEq

/-- What the CTM logs when an owner call succeeds. `NewUpgradeCutData` (:466) is left out (cut
bytes are not modelled), as are `NewPendingAdmin`, `NewServerNotifier` and the logs of the
calls whose effect is not modelled. For a commit the logged departing version is the CTM's
version before the call, which the commit requires to be `old`. -/
def CtmOp.events (W : World) : CtmOp → List CtmEvent
  | .commit t =>
      [.newProtocolVersion (W.tr t).old (W.tr t).new, .newUpgradeTransition (W.tr t).old t,
       .newCurrentRelease (W.tr t).new (W.tr t).newRel]
  | .replace e r =>
      [.upgradeTransitionReplaced (W.tr e).old e r, .newUpgradeTransition (W.tr e).old r]
  | .setDeadline v ts => [.updateProtocolVersionDeadline v ts]
  | _ => []

/-- The CTM's modelled storage. -/
structure CtmSide where
  /-- `owner()`. -/
  owner : Address
  /-- `pendingOwner()`. -/
  pending : Address
  /-- `admin` (:113), what `admin()` returns. -/
  admin : Address
  /-- `pendingAdmin` (:116). It is `private`: no getter reads it. -/
  pendingAdmin : Address
  /-- `protocolVersion`, `currentRelease`, `upgradeTransition`, with the legacy cut and the
  ghost `relAt` of the `VersionRegistry` model, which only its invariant `CtmInv` reads. -/
  reg : CTM
  /-- `protocolVersionDeadlines` (:97), the stored slot. When nonzero it is what
  `protocolVersionDeadline` returns (:546-549). -/
  dl : ℕ → ℕ
  /-- `serverNotifierAddress` (:125). -/
  notifier : Address

/-- One successful owner call from `sender`. Every constructor requires `sender` to be the
CTM's owner. -/
inductive CtmCall (W : World) (sender : Address) : CtmSide → CtmOp → CtmSide → Prop
  /-- :403-418, as `CStep.commit`. -/
  | commit {c : CtmSide} {t : Address} {r' : CTM} :
      sender = c.owner → CStep W c.reg (.commit t) r' →
      CtmCall W sender c (.commit t) { c with reg := r' }
  /-- :424-443, as `CStep.replace`. -/
  | replace {c : CtmSide} {e r : Address} {r' : CTM} :
      sender = c.owner → CStep W c.reg (.replace e r) r' →
      CtmCall W sender c (.replace e r) { c with reg := r' }
  /-- :563-566: `protocolVersionDeadlines[_protocolVersion] = _timestamp;`. -/
  | setDeadline {c : CtmSide} {v ts : ℕ} :
      sender = c.owner → CtmCall W sender c (.setDeadline v ts) { c with dl := upd c.dl v ts }
  /-- :618-621: a call into the chain; no CTM storage is written. -/
  | upgradeChain {c : CtmSide} {id v : ℕ} :
      sender = c.owner → CtmCall W sender c (.upgradeChain id v) c
  /-- `Ownable2StepUpgradeable.transferOwnership`: `_pendingOwner = newOwner`, no zero check. -/
  | transferOwnership {c : CtmSide} {a : Address} :
      sender = c.owner → CtmCall W sender c (.transferOwnership a) { c with pending := a }
  /-- :354-360: `pendingAdmin = _newPendingAdmin;`. -/
  | setPendingAdmin {c : CtmSide} {a : Address} :
      sender = c.owner → CtmCall W sender c (.setPendingAdmin a) { c with pendingAdmin := a }
  /-- :387-391: `serverNotifierAddress = _serverNotifier;`. -/
  | setServerNotifier {c : CtmSide} {n : Address} :
      sender = c.owner → CtmCall W sender c (.setServerNotifier n) { c with notifier := n }
  /-- Any other owner function: arbitrary effect. -/
  | other {c c' : CtmSide} {tag : ℕ} :
      sender = c.owner → CtmCall W sender c (.other tag) c'

/-! ## The executor -/

/-- A call `forward` makes (`governance/UpgradeExecutorBase.sol:46`). -/
inductive FwdCall
  /-- Target `CHAIN_TYPE_MANAGER`, calldata of a CTM owner function. -/
  | ctm (op : CtmOp)
  /-- Any other call: `withData` says whether it carries calldata, `tag` stands for the
  calldata. -/
  | other (target : Address) (withData : Bool) (tag : ℕ)
deriving DecidableEq

/-- The CTM owner call a forwarded call is, if it is one. -/
def FwdCall.ctmOp? : FwdCall → Option CtmOp
  | .ctm op => some op
  | .other _ _ _ => none

/-- A log at the executor's address. -/
inductive ExEvent
  /-- `CallForwarded(target, value, data)` (`governance/IUpgradeExecutorBase.sol:14`), for
  the call `c`. -/
  | callForwarded (c : FwdCall)
  /-- `CTMInfrastructureUpgradeApplied(T)`
  (`upgrades/registry/executors/ICTMUpgradeExecutor.sol:16`). -/
  | infraApplied (T : Address)
  /-- `CTMUpgradeApplied(t, old, new)` (`ICTMUpgradeExecutor.sol:19`). -/
  | ctmUpgradeApplied (t : Address) (old new : ℕ)
  /-- `ChainUpgradeApplied(id, new)` (`ICTMUpgradeExecutor.sol:22`). -/
  | chainUpgradeApplied (id new : ℕ)
  /-- `ProxyImplementationUpgraded(proxy, newImpl)`
  (`upgrades/registry/libraries/ProxyUpgradeRowLib.sol:43`, emitted at :125 by the engine's
  `applyRows`, in the executor's context). -/
  | proxyImplementationUpgraded (p x : Address)
  /-- Any other log. -/
  | other (tag : ℕ)
deriving DecidableEq

/-- One thing an engine does while delegatecalled. -/
inductive EngAct
  /-- A CTM owner call; `msg.sender` is the executor. -/
  | ctm (op : CtmOp)
  /-- `CTM_PROXY_ADMIN.upgrade(p, x)` on a proxy other than the CTM and the ServerNotifier, or
  the swap of such an `upgradeAndCall`, whose call is a separate `other` act. The real
  `ProxyAdmin.upgrade` reverts on a proxy it does not administer; the model does not require
  `s.adminOf p = cfg.paAddr` (`EngStep.upgradeProxy`), so it admits the act on any such proxy,
  an over-approximation. -/
  | upgradeProxy (p x : Address)
  /-- A log. Delegatecalled code logs at the executor's address. -/
  | emit (e : ExEvent)
  /-- Anything else. -/
  | other (tag : ℕ)
deriving DecidableEq

/-- The CTM owner call an engine act is, if it is one. -/
def EngAct.ctmOp? : EngAct → Option CtmOp
  | .ctm op => some op
  | _ => none

/-- The log an engine act emits at the executor's address, if it is one. -/
def EngAct.emitted? : EngAct → Option ExEvent
  | .emit e => some e
  | _ => none

/-- One entry of a frame's trace, in execution order. -/
inductive Obs
  /-- The CTM executed this owner call with the executor as `msg.sender`. -/
  | ctmCall (op : CtmOp)
  /-- A log at the executor's address. -/
  | exEvent (e : ExEvent)
  /-- A log at the CTM's address. -/
  | ctmEvent (e : CtmEvent)
deriving DecidableEq

/-- The owner call a trace entry records, if it is one. -/
def Obs.ownerCall? : Obs → Option CtmOp
  | .ctmCall op => some op
  | _ => none

/-- The executor's log entry a trace entry records, if it is one. -/
def Obs.exEvent? : Obs → Option ExEvent
  | .exEvent e => some e
  | _ => none

/-- The CTM's log entry a trace entry records, if it is one. -/
def Obs.ctmEvent? : Obs → Option CtmEvent
  | .ctmEvent e => some e
  | _ => none

/-- The CTM owner calls of a trace, in order. -/
def ownerCalls (tr : List Obs) : List CtmOp := tr.filterMap Obs.ownerCall?

/-- The executor's log: the trace's entries at the executor's address, in order. -/
def exLog (tr : List Obs) : List ExEvent := tr.filterMap Obs.exEvent?

/-- The CTM's log, in order. -/
def ctmLog (tr : List Obs) : List CtmEvent := tr.filterMap Obs.ctmEvent?

/-- A row as the executor's post-check reads it. -/
structure Row where
  /-- `proxy`. -/
  proxy : Address
  /-- `implNew`. -/
  implNew : Address
deriving DecidableEq

/-- An infrastructure transition, by its getters. -/
structure Transition where
  /-- The object's address. -/
  addr : Address
  /-- `getManifest().domain == ProxyUpgradeDomain.CTM`. -/
  isCtmDomain : Bool
  /-- `getManifest().proxyUpgradeEngine`. -/
  engine : Address
  /-- `toRows(getManifest().proxyUpgrades, …)`. -/
  rows : List Row

/-- Fixed configuration. -/
structure Config where
  /-- The deployed releases and CTM transitions. -/
  W : World
  /-- The executor. -/
  self : Address
  /-- `CHAIN_TYPE_MANAGER` (nonzero, `CTMUpgradeExecutor.sol:47-49`). -/
  ctmAddr : Address
  /-- `CTM_PROXY_ADMIN`. -/
  paAddr : Address
  /-- `address.code.length != 0`. -/
  hasCode : Address → Prop
  /-- The hash `_domainHolders` returns, as a function of the addresses it reads. Arbitrary. -/
  H : List Address → UInt256

/-- The state. -/
structure State where
  /-- The CTM. -/
  ctm : CtmSide
  /-- The executor's `owner()`. -/
  exOwner : Address
  /-- The executor's `pendingOwner()`. -/
  exPending : Address
  /-- `CTM_PROXY_ADMIN.owner()`. -/
  paOwner : Address
  /-- `CTM_PROXY_ADMIN.getProxyImplementation(p)`. -/
  impl : Address → Address
  /-- `CTM_PROXY_ADMIN.getProxyAdmin(p)`. -/
  adminOf : Address → Address
  /-- `owner()` of another `Ownable2Step` contract (the ServerNotifier). -/
  extOwner : Address → Address
  /-- `pendingOwner()` of another `Ownable2Step` contract. -/
  extPending : Address → Address
  /-- `IServerNotifier(n).chainTypeManager()` (`governance/IServerNotifier.sol:42`). -/
  extCtm : Address → Address
  /-- `CHAIN_TYPE_MANAGER.getChainAdmin(id)` (`ChainTypeManager.sol:260-262`). -/
  chainAdmin : ℕ → Address

/-- What `_domainHolders(CTM_PROXY_ADMIN, CHAIN_TYPE_MANAGER)` reads, in order
(`ProxyUpgradeExecutorBase.sol:123-147`): the `ProxyAdmin`'s owner, the CTM's owner, pending
owner and admin, what `getProxyAdmin(CTM)` returns, the ServerNotifier, and, when the
ServerNotifier is nonzero, its owner, pending owner, what `getProxyAdmin` returns for it, and
its CTM. The CTM executor's CTM is never zero (`CTMUpgradeExecutor.sol:47-49`), so the
:119-121 branch does not arise. -/
def holdersView (cfg : Config) (s : State) : List Address :=
  [s.paOwner, s.ctm.owner, s.ctm.pending, s.ctm.admin, s.adminOf cfg.ctmAddr, s.ctm.notifier] ++
    if s.ctm.notifier = 0 then []
    else [s.extOwner s.ctm.notifier, s.extPending s.ctm.notifier, s.adminOf s.ctm.notifier,
      s.extCtm s.ctm.notifier]

/-- One call of `forward` that succeeds, with what it leaves in the trace: the CTM's execution
and logs, then `CallForwarded` (:53). A call with calldata needs code at its target
(:42-44); a CTM owner call carries calldata. -/
inductive FwdStep (cfg : Config) : State → FwdCall → State → List Obs → Prop
  | ctm {s : State} {op : CtmOp} {c' : CtmSide} :
      cfg.hasCode cfg.ctmAddr →
      CtmCall cfg.W cfg.self s.ctm op c' →
      FwdStep cfg s (.ctm op) { s with ctm := c' }
        (Obs.ctmCall op :: (op.events cfg.W).map Obs.ctmEvent ++
          [Obs.exEvent (.callForwarded (.ctm op))])
  | other {s s' : State} {target : Address} {withData : Bool} {tag : ℕ} :
      (withData = true → cfg.hasCode target) →
      FwdStep cfg s (.other target withData tag) s'
        [Obs.exEvent (.callForwarded (.other target withData tag))]

/-- The calls of one `forward`, in order (:38-54). -/
inductive FwdRun (cfg : Config) : State → List FwdCall → State → List Obs → Prop
  | nil {s : State} : FwdRun cfg s [] s []
  | cons {s s' s'' : State} {c : FwdCall} {cs : List FwdCall} {tr₁ tr₂ : List Obs} :
      FwdStep cfg s c s' tr₁ → FwdRun cfg s' cs s'' tr₂ → FwdRun cfg s (c :: cs) s'' (tr₁ ++ tr₂)

/-- One act of the engine that succeeds. -/
inductive EngStep (cfg : Config) : State → EngAct → State → List Obs → Prop
  | ctm {s : State} {op : CtmOp} {c' : CtmSide} :
      CtmCall cfg.W cfg.self s.ctm op c' →
      EngStep cfg s (.ctm op) { s with ctm := c' }
        (Obs.ctmCall op :: (op.events cfg.W).map Obs.ctmEvent)
  /-- `ProxyAdmin.upgrade` is `onlyOwner`; the new implementation must be code. A swap of the
  CTM proxy or of the ServerNotifier proxy is an `other` act instead (see the modelling choices
  in the header). The step does not require that the `ProxyAdmin` administers `p`; it admits
  more steps than the contract makes (an over-approximation). -/
  | upgradeProxy {s : State} {p x : Address} :
      s.paOwner = cfg.self → cfg.hasCode x → p ≠ cfg.ctmAddr → p ≠ s.ctm.notifier →
      EngStep cfg s (.upgradeProxy p x) { s with impl := upd s.impl p x } []
  | emit {s : State} {e : ExEvent} : EngStep cfg s (.emit e) s [Obs.exEvent e]
  | other {s s' : State} {tag : ℕ} : EngStep cfg s (.other tag) s' []

/-- The engine's acts, in order. -/
inductive EngRun (cfg : Config) : State → List EngAct → State → List Obs → Prop
  | nil {s : State} : EngRun cfg s [] s []
  | cons {s s' s'' : State} {a : EngAct} {as : List EngAct} {tr₁ tr₂ : List Obs} :
      EngStep cfg s a s' tr₁ → EngRun cfg s' as s'' tr₂ → EngRun cfg s (a :: as) s'' (tr₁ ++ tr₂)

/-- The state-changing external functions of `CTMUpgradeExecutor`. -/
inductive Entry
  /-- `acceptCTMOwnership()`. -/
  | acceptCTMOwnership
  /-- `applyInfrastructureUpgrade(T)`, whose pinned engine did `acts`. -/
  | applyInfrastructureUpgrade (T : Transition) (acts : List EngAct)
  /-- `applyCTMUpgrade(t)`. -/
  | applyCTMUpgrade (t : Address)
  /-- `upgradeChain(t, id)`. -/
  | upgradeChain (t : Address) (id : ℕ)
  /-- `forward(calls)`. -/
  | forward (calls : List FwdCall)
  /-- `transferOwnership(a)` of the executor itself. -/
  | transferOwnership (a : Address)
  /-- `acceptOwnership()` of the executor itself. -/
  | acceptOwnership

/-- One successful frame: the state before, `msg.sender`, the entry, the state after, the
trace. -/
inductive Frame (cfg : Config) : State → Address → Entry → State → List Obs → Prop
  /-- `CTMUpgradeExecutor.sol:55-61`. `ctm.acceptOwnership()` needs the executor to be the
  CTM's pending owner; it is not an owner call. -/
  | acceptCTMOwnership {s : State} {caller : Address} :
      (caller = s.exOwner ∨ caller = s.ctm.owner) → cfg.self = s.ctm.pending →
      Frame cfg s caller .acceptCTMOwnership
        { s with ctm := { s.ctm with owner := cfg.self, pending := 0 } } []
  /-- `CTMUpgradeExecutor.sol:64-72` over `ProxyUpgradeExecutorBase.sol:51-104`: `onlyOwner`;
  the transition and its engine are code (:57, :63) and the domain is `CTM` (:59-61); the
  CTM's admin is not the `ProxyAdmin` (:75-77); the engine runs (:82-84); then the three
  post-checks (:93-95, :96-98, :99-103) and the leg's one log (`CTMUpgradeExecutor.sol:71`). -/
  | applyInfrastructureUpgrade {s s' : State} {caller : Address} {T : Transition}
      {acts : List EngAct} {tr : List Obs} :
      caller = s.exOwner →
      cfg.hasCode T.addr → T.isCtmDomain = true → cfg.hasCode T.engine →
      s.ctm.admin ≠ cfg.paAddr →
      EngRun cfg s acts s' tr →
      s'.exOwner = s.exOwner → s'.exPending = s.exPending →
      cfg.H (holdersView cfg s') = cfg.H (holdersView cfg s) →
      (∀ r ∈ T.rows, s'.impl r.proxy = r.implNew) →
      Frame cfg s caller (.applyInfrastructureUpgrade T acts) s'
        (tr ++ [Obs.exEvent (.infraApplied T.addr)])
  /-- `CTMUpgradeExecutor.sol:77-89`: `onlyOwner`, `requireCode` (:78), the commit (:82),
  the log (:83-87), then `_requireTransitionApplied` (:88, :109-121). -/
  | applyCTMUpgrade {s : State} {caller t : Address} {c' : CtmSide} :
      caller = s.exOwner → cfg.hasCode t →
      CtmCall cfg.W cfg.self s.ctm (.commit t) c' →
      c'.reg.ut (cfg.W.tr t).old = t → (cfg.W.tr t).new ≤ c'.reg.pv →
      Frame cfg s caller (.applyCTMUpgrade t) { s with ctm := c' }
        (Obs.ctmCall (.commit t) :: ((CtmOp.commit t).events cfg.W).map Obs.ctmEvent ++
          [Obs.exEvent (.ctmUpgradeApplied t (cfg.W.tr t).old (cfg.W.tr t).new)])
  /-- `CTMUpgradeExecutor.sol:92-107`: the owner or the chain's admin (:93-95); the
  transition is the committed one (:99-102); the call (:105); the log (:106). -/
  | upgradeChain {s : State} {caller t : Address} {id : ℕ} {c' : CtmSide} :
      (caller = s.exOwner ∨ caller = s.chainAdmin id) →
      s.ctm.reg.ut (cfg.W.tr t).old = t →
      CtmCall cfg.W cfg.self s.ctm (.upgradeChain id (cfg.W.tr t).old) c' →
      Frame cfg s caller (.upgradeChain t id) { s with ctm := c' }
        [Obs.ctmCall (.upgradeChain id (cfg.W.tr t).old),
         Obs.exEvent (.chainUpgradeApplied id (cfg.W.tr t).new)]
  /-- `governance/UpgradeExecutorBase.sol:35-55`: `onlyOwner`. -/
  | forward {s s' : State} {caller : Address} {calls : List FwdCall} {tr : List Obs} :
      caller = s.exOwner → FwdRun cfg s calls s' tr →
      Frame cfg s caller (.forward calls) s' tr
  /-- `Ownable2Step.transferOwnership`: `onlyOwner`, `_pendingOwner = newOwner`. -/
  | transferOwnership {s : State} {caller a : Address} :
      caller = s.exOwner → Frame cfg s caller (.transferOwnership a) { s with exPending := a } []
  /-- `Ownable2Step.acceptOwnership`: the caller must be the nominee. -/
  | acceptOwnership {s : State} {caller : Address} :
      caller = s.exPending →
      Frame cfg s caller .acceptOwnership { s with exOwner := caller, exPending := 0 } []

/-! ## The vocabulary of the statements -/

/-- The CTM owner calls an entry makes, read off the entry. -/
def Entry.ownerCalls (W : World) : Entry → List CtmOp
  | .acceptCTMOwnership => []
  | .applyInfrastructureUpgrade _ acts => acts.filterMap EngAct.ctmOp?
  | .applyCTMUpgrade t => [.commit t]
  | .upgradeChain t id => [.upgradeChain id (W.tr t).old]
  | .forward calls => calls.filterMap FwdCall.ctmOp?
  | .transferOwnership _ => []
  | .acceptOwnership => []

/-- The executor's log of an entry, read off the entry: for an infrastructure leg, the logs
its engine emitted, then `CTMInfrastructureUpgradeApplied`; for `forward`, one
`CallForwarded` per call. -/
def Entry.exLog (W : World) : Entry → List ExEvent
  | .acceptCTMOwnership => []
  | .applyInfrastructureUpgrade T acts => acts.filterMap EngAct.emitted? ++ [.infraApplied T.addr]
  | .applyCTMUpgrade t => [.ctmUpgradeApplied t (W.tr t).old (W.tr t).new]
  | .upgradeChain t id => [.chainUpgradeApplied id (W.tr t).new]
  | .forward calls => calls.map ExEvent.callForwarded
  | .transferOwnership _ => []
  | .acceptOwnership => []

/-- The owner call `op` is `applyCTMUpgrade(t)`'s commit, `t` has code, and the caller owns the
executor. -/
def FromApplyCTMUpgrade (cfg : Config) (s : State) (caller : Address) (e : Entry)
    (op : CtmOp) : Prop :=
  ∃ t, e = .applyCTMUpgrade t ∧ op = .commit t ∧ cfg.hasCode t ∧ caller = s.exOwner

/-- `op` is `upgradeChain(t, id)`'s call `upgradeChainFromVersion(id, oldProtocolVersion)`, `t`
is the transition the CTM has committed for that version, and the caller owns the executor or
is that chain's admin. -/
def FromUpgradeChain (cfg : Config) (s : State) (caller : Address) (e : Entry)
    (op : CtmOp) : Prop :=
  ∃ t id, e = .upgradeChain t id ∧ op = .upgradeChain id (cfg.W.tr t).old ∧
    s.ctm.reg.ut (cfg.W.tr t).old = t ∧ (caller = s.exOwner ∨ caller = s.chainAdmin id)

/-- `op` is one of the calls a `forward` lists, and the caller owns the executor. -/
def FromForward (_cfg : Config) (s : State) (caller : Address) (e : Entry) (op : CtmOp) : Prop :=
  ∃ calls, e = .forward calls ∧ FwdCall.ctm op ∈ calls ∧ caller = s.exOwner

/-- `op` is a call the engine of an `applyInfrastructureUpgrade(T)` made, `T` is a CTM-domain
transition with code that pins an engine with code, and the caller owns the executor. -/
def FromEngineLeg (cfg : Config) (s : State) (caller : Address) (e : Entry)
    (op : CtmOp) : Prop :=
  ∃ T acts, e = .applyInfrastructureUpgrade T acts ∧ EngAct.ctm op ∈ acts ∧
    T.isCtmDomain = true ∧ cfg.hasCode T.addr ∧ cfg.hasCode T.engine ∧ caller = s.exOwner

/-- Every CTM owner call of every successful frame satisfies `P`. -/
def OriginsCover (P : Config → State → Address → Entry → CtmOp → Prop) : Prop :=
  ∀ (cfg : Config) (s s' : State) (caller : Address) (e : Entry) (tr : List Obs),
    Frame cfg s caller e s' tr → ∀ op, Obs.ctmCall op ∈ tr → P cfg s caller e op

/-- The executor's log in the trace names the owner call `op`: as a forwarded call, as the
commit `CTMUpgradeApplied` announces, or as the chain upgrade `ChainUpgradeApplied`
announces. -/
def LoggedByExecutor (W : World) (tr : List Obs) (op : CtmOp) : Prop :=
  Obs.exEvent (.callForwarded (.ctm op)) ∈ tr ∨
  (∃ t, op = .commit t ∧ Obs.exEvent (.ctmUpgradeApplied t (W.tr t).old (W.tr t).new) ∈ tr) ∨
  (∃ t id, op = .upgradeChain id (W.tr t).old ∧
    Obs.exEvent (.chainUpgradeApplied id (W.tr t).new) ∈ tr)

/-- The entry is not an infrastructure leg whose engine makes a CTM owner call. -/
def Entry.EngineQuiet : Entry → Prop
  | .applyInfrastructureUpgrade _ acts => ∀ op, EngAct.ctm op ∉ acts
  | _ => True

/-- Every holder `_domainHolders` reads is the same in `s'` as in `s`: the `ProxyAdmin`'s
owner, the CTM's owner, pending owner, admin and ServerNotifier, what `getProxyAdmin(CTM)`
returns, and, when the ServerNotifier is nonzero, its owner, pending owner, what
`getProxyAdmin` returns for it, and its CTM. -/
def HoldersKept (cfg : Config) (s s' : State) : Prop :=
  s'.paOwner = s.paOwner ∧ s'.ctm.owner = s.ctm.owner ∧ s'.ctm.pending = s.ctm.pending ∧
    s'.ctm.admin = s.ctm.admin ∧ s'.adminOf cfg.ctmAddr = s.adminOf cfg.ctmAddr ∧
    s'.ctm.notifier = s.ctm.notifier ∧
    (s.ctm.notifier ≠ 0 →
      s'.extOwner s.ctm.notifier = s.extOwner s.ctm.notifier ∧
      s'.extPending s.ctm.notifier = s.extPending s.ctm.notifier ∧
      s'.adminOf s.ctm.notifier = s.adminOf s.ctm.notifier ∧
      s'.extCtm s.ctm.notifier = s.extCtm s.ctm.notifier)

/-- The holders hash collides on the two lists `_domainHolders` read in `s` and in `s'`: the
lists differ and hash the same. Both lists are fixed by the two states. -/
def HoldersCollide (cfg : Config) (s s' : State) : Prop :=
  holdersView cfg s' ≠ holdersView cfg s ∧ cfg.H (holdersView cfg s') = cfg.H (holdersView cfg s)

/-- An owner call whose effect the model fixes: any but `CtmOp.other`. -/
def CtmOp.Tame : CtmOp → Prop
  | .other _ => False
  | _ => True

/-- A forwarded call whose effect the model fixes: a CTM owner call other than
`CtmOp.other`. -/
def FwdCall.Tame : FwdCall → Prop
  | .ctm op => op.Tame
  | .other _ _ _ => False

/-- An engine act whose effect the model fixes: a CTM owner call other than `CtmOp.other`, a
`ProxyAdmin.upgrade`, or a log. -/
def EngAct.Tame : EngAct → Prop
  | .ctm op => op.Tame
  | .upgradeProxy _ _ => True
  | .emit _ => True
  | .other _ => False

/-- The entry makes no call or act whose effect the model leaves arbitrary: for a `forward`,
every listed call is tame; for an infrastructure leg, every engine act is. The other entries
make none. -/
def Entry.Tame : Entry → Prop
  | .applyInfrastructureUpgrade _ acts => ∀ a ∈ acts, a.Tame
  | .forward calls => ∀ c ∈ calls, c.Tame
  | _ => True

/-! ## Witness data

The `VersionRegistry` witness world: releases `100` (version 1) and `200` (version 2);
transitions `300` and `400`, both `1 → 2` from `100` to `200`. The executor is `1`, its owner
(governance) is `2`, the CTM is `8` and the CTM domain's `ProxyAdmin` is `7`. The executor
owns the CTM, the `ProxyAdmin` and the ServerNotifier `6`; the `ProxyAdmin` administers every
proxy, each running implementation `10`; the ServerNotifier is bound to the CTM. The CTM's
admin is `60`, and every chain's admin is `50`. -/

/-- The witness configuration, for a holders hash `H`. Every nonzero address has code. -/
def ocCfg (H : List Address → UInt256) : Config := ⟨wWorld, 1, 8, 7, fun a => a ≠ 0, H⟩

/-- A CTM initialized on release `100`, owned by the executor, with no nominations. -/
def ocS0 : State where
  ctm := ⟨1, 0, 60, 0, initState wWorld 100, fun _ => 0, 6⟩
  exOwner := 2
  exPending := 0
  paOwner := 1
  impl := fun _ => 10
  adminOf := fun _ => 7
  extOwner := fun _ => 1
  extPending := fun _ => 0
  extCtm := fun _ => 8
  chainAdmin := fun _ => 50

/-- `ocS0` after `applyCTMUpgrade(300)`: the CTM at version 2 on release `200`, with `300`
committed for version 1. -/
def ocS1 : State :=
  { ocS0 with
    ctm := { ocS0.ctm with
      reg := { ocS0.ctm.reg with
        pv := 2, cur := 200, ut := upd ocS0.ctm.reg.ut 1 300,
        relAt := upd ocS0.ctm.reg.relAt 2 200 } } }

/-- The trace of that `applyCTMUpgrade(300)`. -/
def ocCommitTrace : List Obs :=
  [.ctmCall (.commit 300),
   .ctmEvent (.newProtocolVersion 1 2), .ctmEvent (.newUpgradeTransition 1 300),
   .ctmEvent (.newCurrentRelease 2 200),
   .exEvent (.ctmUpgradeApplied 300 1 2)]

/-- A CTM-domain transition with one row, proxy `5` to implementation `11`, pinning the
engine at `9`. -/
def ocT : Transition := ⟨3, true, 9, [⟨5, 11⟩]⟩

/-- What the engine at `9` does in the witness leg: the row, with `applyRows`' log, then two
follow-up calls to the CTM: replace the committed `300` by `400`, and store deadline `77` for
version 1. -/
def ocActs : List EngAct :=
  [.upgradeProxy 5 11, .emit (.proxyImplementationUpgraded 5 11), .ctm (.replace 300 400),
   .ctm (.setDeadline 1 77)]

/-- The witness leg's trace. -/
def ocLegTrace : List Obs :=
  [.exEvent (.proxyImplementationUpgraded 5 11),
   .ctmCall (.replace 300 400),
   .ctmEvent (.upgradeTransitionReplaced 1 300 400), .ctmEvent (.newUpgradeTransition 1 400),
   .ctmCall (.setDeadline 1 77),
   .ctmEvent (.updateProtocolVersionDeadline 1 77),
   .exEvent (.infraApplied 3)]

/-- The witness `forward`: the deadline call to the CTM, then a call with calldata to `33`. -/
def ocFwdCalls : List FwdCall := [.ctm (.setDeadline 1 77), .other 33 true 0]

/-- An engine that applies the row, then nominates `42` as the CTM's owner. -/
def ocNominateOwner : List EngAct := [.upgradeProxy 5 11, .ctm (.transferOwnership 42)]

/-- An engine that applies the row, then nominates `42` as the CTM's admin. -/
def ocNominateAdmin : List EngAct := [.upgradeProxy 5 11, .ctm (.setPendingAdmin 42)]

/-- An engine that applies the row, then does one act the model leaves arbitrary. -/
def ocOpaqueActs : List EngAct := [.upgradeProxy 5 11, .other 0]

/-- What `ocOpaqueActs` leaves in the witness: the row applied, and the CTM's `currentRelease`
zero. -/
def ocOpaqueAfter : State :=
  { ocS1 with
    impl := upd ocS1.impl 5 11
    ctm := { ocS1.ctm with reg := { ocS1.ctm.reg with cur := 0 } } }

/-- A holders hash that reads the CTM's pending owner (the third address read). -/
def ocHPending : List Address → UInt256 := fun l => l.getD 2 0

/-- A holders hash that reads nothing. -/
def ocHConst : List Address → UInt256 := fun _ => 0

end Contracts.ExecutorOwnerCallsV35
