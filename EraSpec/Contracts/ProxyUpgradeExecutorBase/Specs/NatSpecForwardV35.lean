import EraSpec.Contracts.ChainTypeManager.Specs.VersionRegistry

/-!
# Model: who makes the CTM's owner calls, and what the executor logs for them (v0.35)

Source: era-contracts `draft/v0.35.0` at commit `d9f678900e1bc8286412b78f56d4a9f443983c29`.
Every `file:line` below is at that commit; paths are relative to `l1-contracts/contracts/`
unless they start with `docs/` or `protocol-docs/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.NatSpecForwardV35` and are proved in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.NatSpecForwardV35`.

## The two comments this model is about

`upgrades/registry/executors/CTMUpgradeExecutor.sol:24-29`:

    /// @dev Fixed logic. Its one delegatecall is into the engine an approved infrastructure transition
    ///      pins ({ProxyUpgradeExecutorBase}); there is no generic one. The transition it commits is the exact deployed
    ///      object governance approved, never a proxy. Every other owner operation of the CTM (freezing
    ///      a chain, moving a deadline, replacing a committed transition, ...) goes through the
    ///      owner-gated, event-logged `forward`; freezing and unfreezing a chain the CTM also takes
    ///      from the Bridgehub's owner directly ({ChainTypeManager-freezeChain}).

`governance/IUpgradeExecutorBase.sol:16-19`:

    /// @notice Escape hatch: forwards raw calls so the authority this executor holds (CTM /
    ///         ProxyAdmin ownership) never becomes unreachable — recovery, ownership succession
    ///         and one-off administrative actions outside the fixed entrypoints. Every call is
    ///         logged, so a bypass of the object-driven path is always visible.

Both leave out the engine. The executor delegatecalls the engine its infrastructure
transition pins (`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:76-78`), and
`upgrades/registry/engines/IProxyUpgradeEngine.sol:10-15` says what that means:

    /// @notice The code a `ProxyUpgradeTransition` pins to apply itself. A domain executor
    ///         DELEGATECALLS exactly {executeUpgrade} on its transition's `proxyUpgradeEngine`, so the
    ///         engine acts with the executor's authority: its `ProxyAdmin` and, in the CTM domain, the
    ///         CTM and the ServerNotifier. …

The engine's context carries the CTM's address for it (`chainTypeManager`,
`upgrades/registry/RegistryTypes.sol:219-225`), and
`upgrades/registry/engines/DefaultProxyUpgradeEngine.sol:18-23` tells a release to subclass
it and write its follow-up calls in the hooks. A call the engine makes to the CTM has
`msg.sender` = the executor = the CTM's owner, so it passes `onlyOwner`, and nothing in
`_applyProxyUpgradeTransition` emits `CallForwarded`.

The prose documents at the same commit already say so:
`docs/registry-driven-upgrades.md:449-453` ("A release's pinned upgrade engine reaches the
same methods from inside `applyInfrastructureUpgrade`, reviewed with the release and not
logged as `CallForwarded` …, except the last row: the executor's post-check refuses an
ownership move"), `docs/upgrade-operations.md:77-78` and
`protocol-docs/ecosystem-upgrade-coordination.md:150-152`. The two source comments above
were not updated. The model states both readings: the comments as written (refuted) and the
documents' version (proved).

## The code modelled

`governance/UpgradeExecutorBase.sol:34-48`:

    function forward(Call[] calldata _calls) external payable onlyOwner {
        for (uint256 i = 0; i < _calls.length; ++i) {
            (bool success, bytes memory returnData) = _calls[i].target.call{value: _calls[i].value}(_calls[i].data);
            if (!success) { assembly { revert(add(returnData, 0x20), mload(returnData)) } }
            emit CallForwarded(_calls[i].target, _calls[i].value, _calls[i].data);   // :46
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

`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:48-98`, the leg:

    ObjectAnchorLib.requireCode(address(_transition));                                // :54
    if (manifest.domain != _domain) { revert ProxyUpgradeDomainMismatch(...); }       // :56-58
    ObjectAnchorLib.requireCode(manifest.proxyUpgradeEngine);                         // :60
    address ownerBefore = owner();                                                    // :69
    address pendingOwnerBefore = pendingOwner();                                      // :70
    address serverNotifier = … IChainTypeManager(_chainTypeManager).serverNotifierAddress();   // :71-73
    bytes32 domainHoldersBefore = _domainHolders(_proxyAdmin, _chainTypeManager, serverNotifier); // :74
    (bool success, bytes memory returnData) = manifest.proxyUpgradeEngine.delegatecall(
        abi.encodeCall(IProxyUpgradeEngine.executeUpgrade, (context, manifest.proxyUpgrades)));  // :76-78
    if (!success) { … revert … }                                                      // :79-85
    if (owner() != ownerBefore || pendingOwner() != pendingOwnerBefore) { revert … }  // :87-89
    if (_domainHolders(_proxyAdmin, _chainTypeManager, serverNotifier) != domainHoldersBefore) { revert … } // :90-92
    ProxyUpgradeRow[] memory rows = ProxyUpgradeRowLib.toRows(manifest.proxyUpgrades, …);    // :93-96
    ProxyUpgradeRowLib.requireRowsApplied(_proxyAdmin, rows);                         // :97

`_domainHolders` (:109-139) hashes `_proxyAdmin.owner()`, the CTM's `owner()` and
`pendingOwner()` and `_proxyAdmin.getProxyAdmin(CTM)`, and, when the notifier read at
:71-73 is nonzero, that notifier's `owner()`, `pendingOwner()` and proxy admin.

`state-transition/ChainTypeManager.sol`, three of its `onlyOwner` writers:

    function setNewVersionUpgradeFromTransition(ICTMTransition _transition) external onlyOwner { … }  // :403-418
    function replaceUpgradeTransition(ICTMTransition _expectedTransition, ICTMTransition _replacement)
        external onlyOwner { … }                                                      // :424-443
    function setProtocolVersionDeadline(uint256 _protocolVersion, uint256 _timestamp) external onlyOwner {
        protocolVersionDeadlines[_protocolVersion] = _timestamp;                      // :564
        emit UpdateProtocolVersionDeadline(_protocolVersion, _timestamp);             // :565
    }                                                                                 // :563-566

## Modelling choices

* **A frame is one invocation of an executor entry point**, by any caller, at any call
  depth. What a frame's own code does (the engine it delegatecalls included) is its trace
  (`List Obs`): the CTM `onlyOwner` calls it made, the logs emitted at the executor's
  address, and the CTM's own logs for the three writers above. A call the frame makes to
  another contract that re-enters the executor is a separate frame with its own caller;
  its effect on the state is covered by the arbitrary-effect acts below.
* **A revert is the absence of a frame.**
* **The CTM** is its `Ownable2Step` owner and pending owner, the version state of
  `Contracts.ChainTypeManager.CTM` (`protocolVersion` :90, `currentRelease` :161,
  `upgradeTransition` :167), the stored deadlines (`protocolVersionDeadlines` :97) and
  `serverNotifierAddress`. The commit and the replacement are
  `Contracts.ChainTypeManager.CStep`, written at `e561b9cc2`; the d9f6789 code of the two
  functions (:403-418, :424-443, with `_commitVersionEdge` :523-537,
  `_recordTransition` :459-467, `_setCurrentRelease` :300-318,
  `_requireSameDeparture` :472-478, `_requireOnwardDestination` :498-518) is the same
  statement for statement. As there, reject-only checks that read nothing modelled are
  omitted: `_requireExecutable` (:449-452), `release.validate()` (:305), the genesis batch
  hash (:311-314) and `_requireSameDeadline` (:483-489). The witnesses below therefore
  assume objects that meet those checks.
* **Every other `onlyOwner` function of the CTM** is `CtmOp.other`: accepted from the
  owner only, with an *arbitrary* effect on the CTM's modelled state. That covers
  `setValidatorTimelockPostV29` (:379), `setServerNotifier` (:387), `revertBatches` (:591),
  `executeUpgrade` (:626), the per-chain setters (:633-665), the legacy
  `setNewVersionUpgrade` (:794), the cut-taking `upgradeChainFromVersion` (:821),
  `setUpgradeDiamondCut` (:837), `renounceOwnership`, and `freezeChain` / `unfreezeChain`
  (:577, :584) when the owner calls them. `transferOwnership` is separate
  (`CtmOp.transferOwnership`) because the leg's post-check reads what it writes.
  `upgradeChainFromVersion(chainId, oldVersion)` (:618-621) writes no CTM storage; what
  it does to the chain is not modelled, and it never fails here.
* **`onlyOwner` is modelled**: `CtmCall` takes the caller and requires it to be the CTM's
  owner. Every executor frame calls the CTM as `Config.self`.
* **The engine is the list of things it did** (`EngAct`), carried in the entry
  `Entry.applyInfrastructureUpgrade T acts`: a CTM owner call, a `ProxyAdmin.upgrade`, a
  log (delegatecalled code logs at the executor's address), or `EngAct.other` — anything
  else, with an arbitrary effect on the whole state. Which act lists a given engine
  contract can produce is not modelled; governance's approval of the transition is not
  modelled either.
* **A forwarded call** is a call of a CTM `onlyOwner` function (`FwdCall.ctm`) or anything
  else (`FwdCall.other`, arbitrary effect). `value` is not modelled.
* **The holders hash** is `Config.H`, an arbitrary function of the list of addresses
  `_domainHolders` reads (`holdersView`). No property assumes anything about `H`; where a
  hash collision matters the statement names the two colliding lists.
* **Rows** are what `toRows` returns (the inventory's non-inert slots, :93-96); the length
  check inside `toRows` and each row's `expectedOldImpl` are not modelled, since the
  executor's own post-check (`requireRowsApplied`,
  `upgrades/registry/libraries/ProxyUpgradeRowLib.sol:128-136`) reads neither.
* **Not modelled**: `renounceOwnership` on the executor (always reverts,
  `governance/UpgradeExecutorBase.sol:53-55`) and `receive()` (:59), which make no call;
  the OpenZeppelin ownership events; ETH; the chains; other callers of the CTM (the
  Bridgehub's owner freezing directly, :229-239, is not an executor frame).
-/

namespace Contracts.ProxyUpgradeExecutorBase.NatSpecForwardV35

open Contracts.ChainTypeManager (Address World CTM CStep upd initState wWorld)

/-! ## The CTM -/

/-- A call of an `onlyOwner` function of the CTM (`state-transition/ChainTypeManager.sol`). -/
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
  /-- Any other `onlyOwner` function; `tag` stands for its selector and arguments. -/
  | other (tag : ℕ)
deriving DecidableEq

/-- The CTM's own logs for the three modelled writers. -/
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

/-- What the CTM logs when a call succeeds. `NewUpgradeCutData` (:466) is left out (cut
bytes are not modelled), as are the logs of the calls whose effect is not modelled. -/
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
  /-- `protocolVersion`, `currentRelease`, `upgradeTransition` (and the legacy fields of the
  `VersionRegistry` model, which nothing here reads). -/
  reg : CTM
  /-- `protocolVersionDeadlines` (:97), the stored slot. When nonzero it is what
  `protocolVersionDeadline` returns (:546-549). -/
  dl : ℕ → ℕ
  /-- `serverNotifierAddress`. -/
  notifier : Address

/-- One successful call of an `onlyOwner` function, from `sender`. Every constructor
requires `sender` to be the owner (`onlyOwner`). -/
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
  /-- `Ownable2StepUpgradeable.transferOwnership`: `_pendingOwner = newOwner`. -/
  | transferOwnership {c : CtmSide} {a : Address} :
      sender = c.owner → CtmCall W sender c (.transferOwnership a) { c with pending := a }
  /-- Any other owner function: arbitrary effect. -/
  | other {c c' : CtmSide} {tag : ℕ} :
      sender = c.owner → CtmCall W sender c (.other tag) c'

/-! ## The executor -/

/-- A call `forward` makes (`governance/UpgradeExecutorBase.sol:39`). -/
inductive FwdCall
  /-- Target `CHAIN_TYPE_MANAGER`, calldata of an `onlyOwner` function. -/
  | ctm (op : CtmOp)
  /-- Any other target or calldata; `tag` stands for the calldata. -/
  | other (target : Address) (tag : ℕ)
deriving DecidableEq

/-- A log emitted at the executor's address. -/
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
  (`upgrades/registry/libraries/ProxyUpgradeRowLib.sol:38`, emitted at :120 by the engine's
  `applyRows`, in the executor's context). -/
  | proxyImplementationUpgraded (p x : Address)
  /-- Any other log. -/
  | other (tag : ℕ)
deriving DecidableEq

/-- One thing an engine does while delegatecalled. -/
inductive EngAct
  /-- A call of a CTM `onlyOwner` function; `msg.sender` is the executor. -/
  | ctm (op : CtmOp)
  /-- `CTM_PROXY_ADMIN.upgrade(p, x)` or `upgradeAndCall(p, x, …)`; the reinitializer's
  effect is not modelled. -/
  | upgradeProxy (p x : Address)
  /-- A log. Delegatecalled code logs at the executor's address. -/
  | emit (e : ExEvent)
  /-- Anything else: a write to the executor's storage, a call to any other contract. -/
  | other (tag : ℕ)
deriving DecidableEq

/-- One entry of a frame's trace, in execution order. -/
inductive Obs
  /-- The CTM executed this `onlyOwner` call with the executor as `msg.sender`. -/
  | ctmCall (op : CtmOp)
  /-- A log at the executor's address. -/
  | exEvent (e : ExEvent)
  /-- A log at the CTM's address. -/
  | ctmEvent (e : CtmEvent)
deriving DecidableEq

/-- The executor's log: the trace's entries at the executor's address. -/
def exLog (tr : List Obs) : List ExEvent :=
  tr.filterMap fun o => match o with
    | .exEvent e => some e
    | _ => none

/-- The CTM's log. -/
def ctmLog (tr : List Obs) : List CtmEvent :=
  tr.filterMap fun o => match o with
    | .ctmEvent e => some e
    | _ => none

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
  /-- `CHAIN_TYPE_MANAGER`. -/
  ctmAddr : Address
  /-- `address.code.length != 0`. -/
  hasCode : Address → Prop
  /-- `keccak256(abi.encode(…))` over the addresses `_domainHolders` reads. Arbitrary. -/
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
  /-- `CHAIN_TYPE_MANAGER.getChainAdmin(id)` (`ChainTypeManager.sol:260-262`). -/
  chainAdmin : ℕ → Address

/-- What `_domainHolders(_proxyAdmin, CTM, n)` reads
(`ProxyUpgradeExecutorBase.sol:109-139`), `n` being the notifier read before the engine ran.
The CTM executor's CTM is never zero (`CTMUpgradeExecutor.sol:47-49`), so the :114-116
branch does not arise. -/
def holdersView (cfg : Config) (n : Address) (s : State) : List Address :=
  [s.paOwner, s.ctm.owner, s.ctm.pending, s.adminOf cfg.ctmAddr] ++
    if n = 0 then [] else [s.extOwner n, s.extPending n, s.adminOf n]

/-- One call of `forward` that succeeds, with what it leaves in the trace: the CTM's
execution and logs, then `CallForwarded` (:46). -/
inductive FwdStep (cfg : Config) : State → FwdCall → State → List Obs → Prop
  | ctm {s : State} {op : CtmOp} {c' : CtmSide} :
      CtmCall cfg.W cfg.self s.ctm op c' →
      FwdStep cfg s (.ctm op) { s with ctm := c' }
        (Obs.ctmCall op :: (op.events cfg.W).map Obs.ctmEvent ++
          [Obs.exEvent (.callForwarded (.ctm op))])
  | other {s s' : State} {target : Address} {tag : ℕ} :
      FwdStep cfg s (.other target tag) s' [Obs.exEvent (.callForwarded (.other target tag))]

/-- The calls of one `forward`, in order (:37-47). -/
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
  /-- `ProxyAdmin.upgrade` is `onlyOwner`; the new implementation must be code. -/
  | upgradeProxy {s : State} {p x : Address} :
      s.paOwner = cfg.self → cfg.hasCode x →
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
  CTM's pending owner; it is not an `onlyOwner` call. -/
  | acceptCTMOwnership {s : State} {caller : Address} :
      (caller = s.exOwner ∨ caller = s.ctm.owner) → cfg.self = s.ctm.pending →
      Frame cfg s caller .acceptCTMOwnership
        { s with ctm := { s.ctm with owner := cfg.self, pending := 0 } } []
  /-- `CTMUpgradeExecutor.sol:64-72` over `ProxyUpgradeExecutorBase.sol:48-98`: `onlyOwner`;
  the transition and its engine are code (:54, :60) and the domain is `CTM` (:56-58); the
  engine runs; then the three post-checks (:87-89, :90-92, :93-97) and the leg's one log
  (`CTMUpgradeExecutor.sol:71`). -/
  | applyInfrastructureUpgrade {s s' : State} {caller : Address} {T : Transition}
      {acts : List EngAct} {tr : List Obs} :
      caller = s.exOwner →
      cfg.hasCode T.addr → T.isCtmDomain = true → cfg.hasCode T.engine →
      EngRun cfg s acts s' tr →
      s'.exOwner = s.exOwner → s'.exPending = s.exPending →
      cfg.H (holdersView cfg s.ctm.notifier s') = cfg.H (holdersView cfg s.ctm.notifier s) →
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
  /-- `governance/UpgradeExecutorBase.sol:34-48`: `onlyOwner`. -/
  | forward {s s' : State} {caller : Address} {calls : List FwdCall} {tr : List Obs} :
      caller = s.exOwner → FwdRun cfg s calls s' tr →
      Frame cfg s caller (.forward calls) s' tr
  /-- `Ownable2Step.transferOwnership`. -/
  | transferOwnership {s : State} {caller a : Address} :
      caller = s.exOwner → Frame cfg s caller (.transferOwnership a) { s with exPending := a } []
  /-- `Ownable2Step.acceptOwnership`. -/
  | acceptOwnership {s : State} {caller : Address} :
      caller = s.exPending →
      Frame cfg s caller .acceptOwnership { s with exOwner := caller, exPending := 0 } []

/-! ## The vocabulary of the statements -/

/-- The CTM owner call `op` was `applyCTMUpgrade`'s commit, and the caller owns the
executor. -/
def FromApplyCTMUpgrade (_cfg : Config) (s : State) (caller : Address) (e : Entry)
    (op : CtmOp) : Prop :=
  ∃ t, e = .applyCTMUpgrade t ∧ op = .commit t ∧ caller = s.exOwner

/-- `op` was `upgradeChain`'s call, and the caller owns the executor or is that chain's
admin. -/
def FromUpgradeChain (cfg : Config) (s : State) (caller : Address) (e : Entry)
    (op : CtmOp) : Prop :=
  ∃ t id, e = .upgradeChain t id ∧ op = .upgradeChain id (cfg.W.tr t).old ∧
    (caller = s.exOwner ∨ caller = s.chainAdmin id)

/-- `op` was one of the calls of a `forward`, and the caller owns the executor. -/
def FromForward (_cfg : Config) (s : State) (caller : Address) (e : Entry) (op : CtmOp) : Prop :=
  ∃ calls, e = .forward calls ∧ FwdCall.ctm op ∈ calls ∧ caller = s.exOwner

/-- `op` was made by the engine of an `applyInfrastructureUpgrade`, and the caller owns the
executor. -/
def FromEngineLeg (_cfg : Config) (s : State) (caller : Address) (e : Entry)
    (op : CtmOp) : Prop :=
  ∃ T acts, e = .applyInfrastructureUpgrade T acts ∧ EngAct.ctm op ∈ acts ∧ caller = s.exOwner

/-- Every CTM owner call of every successful frame satisfies `P`. -/
def OriginsCover (P : Config → State → Address → Entry → CtmOp → Prop) : Prop :=
  ∀ (cfg : Config) (s s' : State) (caller : Address) (e : Entry) (tr : List Obs),
    Frame cfg s caller e s' tr → ∀ op, Obs.ctmCall op ∈ tr → P cfg s caller e op

/-- The CTM owner calls an entry makes, read off the entry. -/
def Entry.Makes (W : World) : Entry → CtmOp → Prop
  | .applyCTMUpgrade t, op => op = .commit t
  | .upgradeChain t id, op => op = .upgradeChain id (W.tr t).old
  | .forward calls, op => FwdCall.ctm op ∈ calls
  | .applyInfrastructureUpgrade _ acts, op => EngAct.ctm op ∈ acts
  | _, _ => False

/-- The executor's log names the CTM owner call `op`: as a forwarded call, as the commit
`CTMUpgradeApplied` announces, or as the chain upgrade `ChainUpgradeApplied` announces. -/
def LoggedByExecutor (W : World) (tr : List Obs) (op : CtmOp) : Prop :=
  Obs.exEvent (.callForwarded (.ctm op)) ∈ tr ∨
  (∃ t, op = .commit t ∧ Obs.exEvent (.ctmUpgradeApplied t (W.tr t).old (W.tr t).new) ∈ tr) ∨
  (∃ t id, op = .upgradeChain id (W.tr t).old ∧
    Obs.exEvent (.chainUpgradeApplied id (W.tr t).new) ∈ tr)

/-- The entry is not an infrastructure leg whose engine calls a CTM owner function. -/
def Entry.EngineQuiet : Entry → Prop
  | .applyInfrastructureUpgrade _ acts => ∀ op, EngAct.ctm op ∉ acts
  | _ => True

/-- An act whose effect on the CTM's owner the model leaves open. -/
def EngAct.Opaque : EngAct → Prop
  | .other _ => True
  | .ctm (.other _) => True
  | _ => False

/-! ## Witness data

The `VersionRegistry` witness world: releases `100` (version 1) and `200` (version 2);
transitions `300` and `400`, both `1 → 2` from `100` to `200`. The executor is `1`, its
owner (governance) is `2`, the CTM is `8`. The executor owns the CTM and the CTM domain's
`ProxyAdmin`; no ServerNotifier is set. Every proxy runs implementation `10`, and chain
`0`'s admin is `50`. -/

/-- The witness configuration, for any holders hash. -/
def wCfg (H : List Address → UInt256) : Config := ⟨wWorld, 1, 8, fun a => a ≠ 0, H⟩

/-- A fresh CTM on release `100`, owned by the executor. -/
def w0 : State where
  ctm := ⟨1, 0, initState wWorld 100, fun _ => 0, 0⟩
  exOwner := 2
  exPending := 0
  paOwner := 1
  impl := fun _ => 10
  adminOf := fun _ => 7
  extOwner := fun _ => 0
  extPending := fun _ => 0
  chainAdmin := fun _ => 50

/-- A CTM-domain transition with one row, proxy `5` to implementation `11`, pinning the
engine at `9`. -/
def wT : Transition := ⟨3, true, 9, [⟨5, 11⟩]⟩

/-- A CTM-domain transition whose inventory is all inert slots, pinning the engine at `9`. -/
def wT0 : Transition := ⟨4, true, 9, []⟩

/-- What the engine at `9` does in the witness leg: the row (with `applyRows`' log), then
three follow-up calls to the CTM: commit `300`, replace it by `400`, store deadline `77` for
version 1. -/
def wActs : List EngAct :=
  [.upgradeProxy 5 11, .emit (.proxyImplementationUpgraded 5 11), .ctm (.commit 300),
   .ctm (.replace 300 400), .ctm (.setDeadline 1 77)]

/-- The witness leg's trace. -/
def wTrace : List Obs :=
  [.exEvent (.proxyImplementationUpgraded 5 11),
   .ctmCall (.commit 300),
   .ctmEvent (.newProtocolVersion 1 2), .ctmEvent (.newUpgradeTransition 1 300),
   .ctmEvent (.newCurrentRelease 2 200),
   .ctmCall (.replace 300 400),
   .ctmEvent (.upgradeTransitionReplaced 1 300 400), .ctmEvent (.newUpgradeTransition 1 400),
   .ctmCall (.setDeadline 1 77),
   .ctmEvent (.updateProtocolVersionDeadline 1 77),
   .exEvent (.infraApplied 3)]

/-- A holders hash that reads the CTM's pending owner (the third address read). -/
def wHPending : List Address → UInt256 := fun l => l.getD 2 0

end Contracts.ProxyUpgradeExecutorBase.NatSpecForwardV35
