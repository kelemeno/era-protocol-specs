import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTiming

/-!
# Model: the ServerNotifier binding, and what an engine leg's post-check compares

Source: era-contracts `draft/v0.35.0` at commit **`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`**
(`b17415d20`, 2026-11-16). Every `file:line` below is at that commit, relative to
`l1-contracts/contracts/`.

This topic was started against `d9f6789` on the same branch. Of the files cited here,
`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol` changed in substance between the two
commits (`9775be946`: `_domainHolders` and the check before the engine); the others cited are
unchanged, or moved by a few lines (`RegistryBootstrapMigration.sol`, `RegistryTypes.sol`). This
model is of `b17415d20` only and does not describe `d9f6789`.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.NotifierBindingV35` and are proved in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.NotifierBindingV35`.

## Why this is modelled

A chain's validators may upgrade it only once the chain's entry in the ServerNotifier is set and
reached. The diamond finds that notifier through its CTM at call time
(`state-transition/chain-deps/facets/Admin.sol:577-585`):

    if (msg.sender != s.admin && msg.sender != s.chainTypeManager) {
        IServerNotifier serverNotifier = IServerNotifier(
            IChainTypeManager(s.chainTypeManager).serverNotifierAddress()
        );
        uint256 timestamp = serverNotifier.protocolVersionToUpgradeTimestamp(s.chainId, _oldProtocolVersion);
        if (timestamp == 0 || block.timestamp < timestamp) {
            revert UpgradeTimestampNotReached(timestamp, block.timestamp);
        }
    }

Who may write that entry is decided by two pointers:

* **the CTM's pointer to the notifier**, `serverNotifierAddress`
  (`state-transition/ChainTypeManager.sol:125`; `initialize` refuses zero, :277-279, and sets
  it, :290), written afterwards by `setServerNotifier` (`ChainTypeManager.sol:387-391`,
  `onlyOwner`, no zero check):

      function setServerNotifier(address _serverNotifier) external onlyOwner {
          address oldServerNotifier = serverNotifierAddress;
          serverNotifierAddress = _serverNotifier;
          emit NewServerNotifier(oldServerNotifier, _serverNotifier);
      }

* **the notifier's pointer back to a CTM**, `chainTypeManager`
  (`governance/ServerNotifier.sol:30`), written by `setChainTypeManager`
  (`ServerNotifier.sol:67-72`, `onlyOwner`, refuses only zero). Every per-chain write goes
  through it: `onlyChainAdmin(_chainId)` is
  `msg.sender == chainTypeManager.getChainAdmin(_chainId)` (`ServerNotifier.sol:43-48`).

`setUpgradeTimestamp` (`ServerNotifier.sol:113-132`) is the per-chain writer:

    function setUpgradeTimestamp(uint256 _chainId, uint256 _upgradeTimestamp) external onlyChainAdmin(_chainId) {
        if (_upgradeTimestamp == 0) { revert ZeroUpgradeTimestamp(); }                       // :114-116
        uint256 oldProtocolVersion = chainTypeManager.getProtocolVersion(_chainId);          // :117
        if (chainTypeManager.upgradeTransition(oldProtocolVersion) == address(0) &&
            chainTypeManager.upgradeCutHash(oldProtocolVersion) == bytes32(0)) {
            revert CutDataForProtocolVersionNotAvailable(oldProtocolVersion); }               // :120-125
        IUpgradePreconditionChecker checker = upgradePreconditionChecker[oldProtocolVersion]; // :126
        if (address(checker) != address(0)) {
            checker.checkUpgradePreconditions(_chainId, chainTypeManager.getZKChain(_chainId)); } // :127-129
        protocolVersionToUpgradeTimestamp[_chainId][oldProtocolVersion] = _upgradeTimestamp;  // :130
        emit UpgradeTimestampUpdated(_chainId, oldProtocolVersion, _upgradeTimestamp);        // :131
    }

and `setUpgradePreconditionChecker` (`ServerNotifier.sol:135-141`, `onlyOwner`) writes the
per-version checker. The contract's other functions write none of this: `initialize` (:57-62)
is an `initializer`, and `migrateToGateway` / `migrateFromGateway` (:78-99) only emit events.

On the real CTM, `getChainAdmin(id)` is `IZKChain(getZKChain(id)).getAdmin()`
(`ChainTypeManager.sol:260-262`, `getZKChain` at :253-255 asks the Bridgehub), and `getAdmin()`
returns the diamond's `s.admin` (`state-transition/chain-deps/facets/Getters.sol:44-46`).
`getProtocolVersion(id)` is the diamond's version in the same way (`ChainTypeManager.sol:714-716`).
That identification is only as good as the notifier's `chainTypeManager` pointer.

The CTM also has an **admin role**, distinct from its owner: `admin` (`ChainTypeManager.sol:113`)
and the private `pendingAdmin` (:116), written by `setPendingAdmin` (:354-360,
`onlyOwnerOrAdmin`, :208-213) and `acceptAdmin` (:363-375, only the pending admin, which then
becomes `admin` and clears the nomination). It enters this model only because the post-check
below reads `admin()`.

## The binding

`RegistryAuthorityLib.requireNotifierHandedOver`
(`upgrades/registry/libraries/RegistryAuthorityLib.sol:91-105`) is the binding: the CTM points
at the notifier (:92-95), the notifier points back at the CTM (:96-99), the notifier is owned by
the CTM executor (:100-103), and no nomination is pending (:104, `requireNoNomination`,
:109-114). It is called by the bootstrap's `validate()`
(`upgrades/registry/bootstrap/RegistryBootstrapMigration.sol:174`) and, through
`requireRegistryAuthority` (`RegistryAuthorityLib.sol:50-62`), by its `validateApplied()` (:219).
A source search at this commit finds no other caller.

## The engine leg's post-check

`ProxyUpgradeExecutorBase._applyProxyUpgradeTransition`
(`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:51-104`) delegatecalls the
transition's engine (:82-84), so every call the engine makes has the executor as `msg.sender`.
The executor owns the CTM, the CTM-domain `ProxyAdmin` and the notifier in the registry shape
(`RegistryAuthorityLib.sol:50-62, :100-103`), so the engine passes every `onlyOwner` of all
three. The contract's NatSpec (`ProxyUpgradeExecutorBase.sol:34-41`) says what the executor
checks afterwards:

    /// @dev The engine runs with the executor's authority and storage. What the executor checks after
    ///      it returns: its own ownership (owner and pending owner unchanged), the holders of the domain
    ///      it lends the engine (the `ProxyAdmin`'s owner and, in a CTM domain, the CTM's owner, pending
    ///      owner, admin, proxy admin and ServerNotifier, and that ServerNotifier's owner, pending owner,
    ///      proxy admin and CTM, unchanged; a succession or a re-pointed ServerNotifier is a `forward`,
    ///      not a leg) and every row's proxy at its `implNew`.

Before the engine (:72-80):

    if (_chainTypeManager != address(0) && IChainTypeManager(_chainTypeManager).admin() == address(_proxyAdmin)) {
        revert ProxyUpgradeCTMAdminIsProxyAdmin(_chainTypeManager);                            // :75-77
    }
    ...
    bytes32 domainHoldersBefore = _domainHolders(_proxyAdmin, _chainTypeManager);              // :80

and after it (:96-98):

    if (_domainHolders(_proxyAdmin, _chainTypeManager) != domainHoldersBefore) {
        revert ProxyUpgradeEngineMovedDomainAuthority(manifest.proxyUpgradeEngine); }

`_domainHolders` (:118-148), with a nonzero CTM, reads `serverNotifierAddress()` itself at each
call (:123) and returns

    keccak256(abi.encode(_proxyAdmin.owner(), ctm.owner(), ctm.pendingOwner(),
        IChainTypeManager(ctm).admin(), _proxyAdmin.getProxyAdmin(ctm), serverNotifier))      // :124-133

when `serverNotifier` is zero (:134-136), and otherwise

    keccak256(abi.encode(<that hash>, notifier.owner(), notifier.pendingOwner(),
        _proxyAdmin.getProxyAdmin(notifier), IServerNotifier(notifier).chainTypeManager()))   // :138-147

Its NatSpec (:112-115): "A proxy `_proxyAdmin` no longer administers passes `getProxyAdmin`'s
`admin()` query to its implementation: a moved CTM answers its own `admin()` (the caller refuses
that being the `ProxyAdmin`), a moved ServerNotifier has none and reverts the leg. The CTM's
`pendingAdmin` is private, so a nomination is not compared."

## Modelling choices

* **One CTM**, at `Env.ctm`, which is the diamonds' `s.chainTypeManager` (the identification
  `Specs/UpgradeTiming.lean` already makes: `state-transition/chain-deps/DiamondInit.sol:91`
  sets it to the deploying CTM). Its storage is `CtmStore`. The CTM domain is the executor's
  nonzero `CHAIN_TYPE_MANAGER` (`CTMUpgradeExecutor.sol:47-49`), so only `_domainHolders`'s
  CTM branch is modelled.
* **Every address has ServerNotifier-shaped proxy storage** (`State.notifiers`). A pointer may
  be set to any address, so the store of an address nobody uses is arbitrary initial data: this
  is how "a notifier owned by anyone, holding anything" is expressed. A contract at that address
  that is not a ServerNotifier proxy answers whatever its code says, or reverts (an address
  without code reverts every getter, its empty return data not decoding); the model does not
  bound the answers and does not model those reverts, which only removes accepted legs. The
  CTM's own address is not meant as a notifier address.
* **After a code swap, a proxy is read as running its contract's code** (ServerNotifier, or
  ChainTypeManager) on the storage the swap leaves. New code whose getters answer otherwise, or
  whose functions are gated otherwise, is outside the model; the executor's row check
  (:99-103) pins the implementation of each proxy the manifest's rows name.
* **What other contracts answer is fixed configuration (`Env`)**: what each address answers to
  `getChainAdmin(id)`, `getProtocolVersion(id)`, whether it has an upgrade scheduled at a version
  (`upgradeTransition(v) != 0 || upgradeCutHash(v) != 0`), and whether a checker accepts a chain.
  Every per-step result here is about one step inside one transaction. The results about
  sequences (`ShapeKeptByOtherCallers`, `ShapeKeptAlongDomainRuns`) fix one `Env` for the whole
  sequence and hold for every `Env`.
* **Proxy admins.** The ERC-1967 admin slot is part of a proxy's storage (`CtmStore.adminSlot`,
  `NotifierStore.adminSlot`). `_proxyAdmin.getProxyAdmin(p)` is OpenZeppelin v4's `staticcall` of
  `admin()` on `p` from the `ProxyAdmin`; the transparent proxy answers its slot when the caller
  is its admin, and otherwise forwards the call to its implementation (the NatSpec at :112-115).
  So `getProxyAdmin` answers `pa` when `pa` administers the proxy; otherwise the CTM answers its
  `admin` role (`ctmProxyAdminSeen`), and a ServerNotifier, which has no `admin()`, reverts.
  `domainHolders` models exactly that.
* **Calls a transparent proxy's own admin makes** to anything but the proxy's admin functions
  revert in the source. The model does not refuse them: such a caller still takes the `Step`s
  its role allows, and if the executor administered the CTM proxy or the notifier proxy, the
  source's `_domainHolders` would revert where `domainHolders` answers. That only adds steps and
  accepted legs, so the results about every step, run or accepted leg carry over; the witnesses
  here are states where no caller they use administers a proxy.
* **`paOwner a` is who controls the proxy admin `a`**: `owner()` when `a` is an OpenZeppelin
  `ProxyAdmin` (plain `Ownable`), as it is for the CTM domain's. An implementation swap or admin
  change of a proxy is by `paOwner` of its admin slot. For a proxy whose admin is an externally
  owned account, read `paOwner a` as `a`.
* **The hash is a parameter.** `PostCheck h` compares `h` of the holders tuples. Every
  "the check passes" result is for every `h` (equal tuples hash equal), so no property of
  keccak is assumed. Where a result says the check fails, it is stated for the comparison of the
  tuples themselves (`h = id`), and for an arbitrary `h` as: passing needs `h` to collide on the
  two tuples the leg's own readings give. `domainHash k` is the source's hash, two `keccak256`
  calls over `abi.encode`, for a keccak `k` on lists of 32-byte words (addresses are words here).
  `abi.encode` of static values is the concatenation of their 32-byte words, so distinct word
  lists are distinct byte strings. A collision of `domainHash k` on two distinct tuples is a
  collision of `k` on two named, distinct preimages (`DomainHashCollisionIsKeccakCollision`).
* **The executor's own-ownership check** (:93-95) and the **row check** (:99-103) read state no
  step of this model writes: the executor's own storage, and the implementation slots of the
  proxies the manifest's rows name (the row carries its proxy address,
  `upgrades/registry/RegistryTypes.sol:166-175`). They are left out of `LegAccepted`, which
  therefore admits at least the legs the source admits. So are the reject-only checks before
  the engine (`requireCode`, the domain match, :57-63).
* **An engine leg is a `Run`**: a sequence of successful calls. The engine's own calls are sent
  by the executor; a contract the engine calls may send calls of its own. The post-check reads
  only the end state, so the results about accepted legs hold whatever the calls are.
* **Writers modelled**: the five ServerNotifier and CTM functions named above, the CTM's admin
  role (`setPendingAdmin`, `acceptAdmin`), the `Ownable2Step` ownership functions of the notifier
  (OpenZeppelin v4; `ServerNotifier` overrides none) and of the CTM (`Ownable2StepUpgradeable`,
  `ChainTypeManager.sol:58`; `renounceOwnership` is not disabled), `transferOwnership` /
  `renounceOwnership` of a `ProxyAdmin`, `ProxyAdmin.changeProxyAdmin` for a notifier proxy and
  for the CTM proxy, and an implementation swap of either proxy through its `ProxyAdmin`, which
  may leave any storage, the admin slot included (`upgradeAndCall` runs the new code in the
  proxy's storage).
* **Not a step**: `ServerNotifier.initialize` (:57-62). It is an `initializer` and reverts on a
  proxy whose `Initializable` flag is set; every notifier store here is read as initialised. The
  CTM's other `onlyOwner` functions write no field of `State`. So do the executor's other entry
  points: `applyCTMUpgrade` (`CTMUpgradeExecutor.sol:77-89`) and `upgradeChain` (:92-107) call
  CTM functions that write its version registry and the chain (`Specs/UpgradeTiming.lean`).
* **A revert is the absence of a step.** Events are omitted.
-/

namespace Contracts.NotifierBindingV35

open Contracts.ChainTypeManager (Address ChainId upd TimedSys TimedConfig TimedStep LegacyCut
  setNotifierEntry)

/-! ## State -/

/-- One ServerNotifier proxy's storage (`governance/ServerNotifier.sol:28-39`), with the
proxy's ERC-1967 admin slot. -/
structure NotifierStore where
  /-- `chainTypeManager` (:30): the contract `onlyChainAdmin` asks. -/
  chainTypeManager : Address
  /-- `Ownable.owner()`. -/
  owner : Address
  /-- `Ownable2Step.pendingOwner()`; zero when no nomination is outstanding. -/
  pendingOwner : Address
  /-- The proxy's ERC-1967 admin. -/
  adminSlot : Address
  /-- `protocolVersionToUpgradeTimestamp[chainId][oldProtocolVersion]` (:33-34); zero is unset. -/
  entry : ChainId → ℕ → ℕ
  /-- `upgradePreconditionChecker[oldProtocolVersion]` (:37-39); zero is none. -/
  checker : ℕ → Address

/-- The CTM proxy's storage that this model reads (`state-transition/ChainTypeManager.sol`), with
the proxy's ERC-1967 admin slot. -/
structure CtmStore where
  /-- `serverNotifierAddress` (:125). -/
  serverNotifier : Address
  /-- `owner()` (`Ownable2StepUpgradeable`). -/
  owner : Address
  /-- `pendingOwner()`. -/
  pendingOwner : Address
  /-- `admin` (:113), the CTM's admin role. -/
  admin : Address
  /-- `pendingAdmin` (:116, private). -/
  pendingAdmin : Address
  /-- The proxy's ERC-1967 admin. -/
  adminSlot : Address

/-- The CTM's storage, every address's notifier storage, and the proxy admins' owners. -/
structure State where
  /-- The CTM proxy's storage. -/
  ctm : CtmStore
  /-- The ServerNotifier proxy storage at each address. -/
  notifiers : Address → NotifierStore
  /-- Who controls the proxy admin at each address: `owner()` of a `ProxyAdmin`. -/
  paOwner : Address → Address

/-- What the contracts outside `State` answer. -/
structure Env where
  /-- The CTM's address: every diamond's `s.chainTypeManager`. -/
  ctm : Address
  /-- `C.getChainAdmin(id)` at address `C`. -/
  adminVia : Address → ChainId → Address
  /-- `C.getProtocolVersion(id)` at address `C`. -/
  pvVia : Address → ChainId → ℕ
  /-- `C.upgradeTransition(v) != address(0) || C.upgradeCutHash(v) != bytes32(0)` at `C`
  (`ServerNotifier.sol:120-125`). -/
  scheduledVia : Address → ℕ → Prop
  /-- `k.checkUpgradePreconditions(id, C.getZKChain(id))` does not revert, for checker `k` and
  notifier CTM `C` (`ServerNotifier.sol:127-129`). -/
  checkerAccepts : Address → Address → ChainId → Prop
  /-- `s.admin` of chain `id`'s diamond. -/
  diamondAdmin : ChainId → Address

/-- On the real CTM, `getChainAdmin(id)` is the diamond's `s.admin`
(`ChainTypeManager.sol:260-262`, `Getters.sol:44-46`), for the diamond the Bridgehub registers
under `id` (`ChainTypeManager.sol:253-255`). A fact about the CTM's and the Bridgehub's code and
state, used as a premise where a result needs it (`MODEL-NOTIFIER-BINDING` in `ASSUMPTIONS.md`). -/
def CtmAnswersDiamondAdmin (E : Env) : Prop :=
  ∀ id, E.adminVia E.ctm id = E.diamondAdmin id

/-- The entry the diamond of chain `id` reads for departing version `v`: the one in the notifier
the CTM points at **now** (`Admin.sol:578-581`). -/
def liveEntry (s : State) (id : ChainId) (v : ℕ) : ℕ :=
  (s.notifiers s.ctm.serverNotifier).entry id v

/-- The validator gate of `Admin.upgradeChainFromVersion` at block time `τ` is open
(`Admin.sol:582-584` does not revert). It applies to callers other than `s.admin` and the CTM. -/
def ValidatorGateOpen (s : State) (id : ChainId) (v τ : ℕ) : Prop :=
  liveEntry s id v ≠ 0 ∧ liveEntry s id v ≤ τ

/-! ## Steps -/

/-- Write one per-chain entry. -/
def setEntry (e : ChainId → ℕ → ℕ) (id : ChainId) (v ts : ℕ) : ChainId → ℕ → ℕ :=
  upd e id (upd (e id) v ts)

/-- The writers. Each is a call with some `msg.sender`, given separately to `Step`. -/
inductive Op
  /-- `ChainTypeManager.setServerNotifier(n)` (`ChainTypeManager.sol:387-391`). -/
  | setServerNotifier (n : Address)
  /-- `ChainTypeManager.setPendingAdmin(a)` (`ChainTypeManager.sol:354-360`). -/
  | ctmSetPendingAdmin (a : Address)
  /-- `ChainTypeManager.acceptAdmin()` (`ChainTypeManager.sol:363-375`). -/
  | ctmAcceptAdmin
  /-- `ServerNotifier(n).setChainTypeManager(c)` (`ServerNotifier.sol:67-72`). -/
  | setChainTypeManager (n c : Address)
  /-- `ServerNotifier(n).setUpgradePreconditionChecker(v, k)` (`ServerNotifier.sol:135-141`). -/
  | setUpgradePreconditionChecker (n : Address) (v : ℕ) (k : Address)
  /-- `ServerNotifier(n).setUpgradeTimestamp(id, ts)` (`ServerNotifier.sol:113-132`). -/
  | setUpgradeTimestamp (n : Address) (id : ChainId) (ts : ℕ)
  /-- `ServerNotifier(n).transferOwnership(o)` (OpenZeppelin v4 `Ownable2Step`). -/
  | notifierTransferOwnership (n o : Address)
  /-- `ServerNotifier(n).acceptOwnership()` (`Ownable2Step`). -/
  | notifierAcceptOwnership (n : Address)
  /-- `ServerNotifier(n).renounceOwnership()` (`Ownable`, not disabled by `ServerNotifier`). -/
  | notifierRenounceOwnership (n : Address)
  /-- An implementation swap of the notifier proxy `n` through its `ProxyAdmin`
  (`upgrade` / `upgradeAndCall`), leaving storage `st`. -/
  | upgradeNotifierProxy (n : Address) (st : NotifierStore)
  /-- `ProxyAdmin.changeProxyAdmin(n, a)` for the notifier proxy `n`. -/
  | changeNotifierProxyAdmin (n a : Address)
  /-- The CTM's `transferOwnership(o)` (`Ownable2StepUpgradeable`). -/
  | ctmTransferOwnership (o : Address)
  /-- The CTM's `acceptOwnership()`. -/
  | ctmAcceptOwnership
  /-- The CTM's `renounceOwnership()` (not disabled by `ChainTypeManager`). -/
  | ctmRenounceOwnership
  /-- An implementation swap of the CTM proxy through its `ProxyAdmin`, leaving storage `c`. -/
  | upgradeCtmProxy (c : CtmStore)
  /-- `ProxyAdmin.changeProxyAdmin(ctm, a)` for the CTM proxy. -/
  | changeCtmProxyAdmin (a : Address)
  /-- `ProxyAdmin(pa).transferOwnership(o)` (plain `Ownable`). -/
  | paTransferOwnership (pa o : Address)
  /-- `ProxyAdmin(pa).renounceOwnership()`. -/
  | paRenounceOwnership (pa : Address)

/-- One successful call of `op` with `msg.sender = caller`. -/
inductive Step (E : Env) : State → Address → Op → State → Prop
  /-- `setServerNotifier`: `onlyOwner`; no other check (`ChainTypeManager.sol:387-391`). -/
  | setServerNotifier {s : State} {caller n : Address} :
      caller = s.ctm.owner →
      Step E s caller (.setServerNotifier n) { s with ctm := { s.ctm with serverNotifier := n } }
  /-- `setPendingAdmin`: the admin role or the owner (`onlyOwnerOrAdmin`,
  `ChainTypeManager.sol:208-213`); any nominee. -/
  | ctmSetPendingAdmin {s : State} {caller a : Address} :
      (caller = s.ctm.admin ∨ caller = s.ctm.owner) →
      Step E s caller (.ctmSetPendingAdmin a) { s with ctm := { s.ctm with pendingAdmin := a } }
  /-- `acceptAdmin`: only the pending admin, which becomes `admin`; the nomination is cleared
  (`ChainTypeManager.sol:363-375`). -/
  | ctmAcceptAdmin {s : State} {caller : Address} :
      caller = s.ctm.pendingAdmin →
      Step E s caller .ctmAcceptAdmin
        { s with ctm := { s.ctm with admin := caller, pendingAdmin := 0 } }
  /-- `setChainTypeManager`: `onlyOwner`, nonzero (`ServerNotifier.sol:67-72`). -/
  | setChainTypeManager {s : State} {caller n c : Address} :
      caller = (s.notifiers n).owner → c ≠ 0 →
      Step E s caller (.setChainTypeManager n c)
        { s with notifiers := upd s.notifiers n { s.notifiers n with chainTypeManager := c } }
  /-- `setUpgradePreconditionChecker`: `onlyOwner` (`ServerNotifier.sol:135-141`). -/
  | setUpgradePreconditionChecker {s : State} {caller n : Address} {v : ℕ} {k : Address} :
      caller = (s.notifiers n).owner →
      Step E s caller (.setUpgradePreconditionChecker n v k)
        { s with notifiers := upd s.notifiers n (
            { s.notifiers n with checker := upd (s.notifiers n).checker v k }) }
  /-- `setUpgradeTimestamp` (`ServerNotifier.sol:113-132`), every check asked of the notifier's
  own `chainTypeManager`. -/
  | setUpgradeTimestamp {s : State} {caller n : Address} {id : ChainId} {ts : ℕ} :
      caller = E.adminVia (s.notifiers n).chainTypeManager id →
      ts ≠ 0 →
      E.scheduledVia (s.notifiers n).chainTypeManager
        (E.pvVia (s.notifiers n).chainTypeManager id) →
      ((s.notifiers n).checker (E.pvVia (s.notifiers n).chainTypeManager id) = 0 ∨
        E.checkerAccepts ((s.notifiers n).checker (E.pvVia (s.notifiers n).chainTypeManager id))
          (s.notifiers n).chainTypeManager id) →
      Step E s caller (.setUpgradeTimestamp n id ts)
        { s with notifiers := upd s.notifiers n (
            { s.notifiers n with
                entry := setEntry (s.notifiers n).entry id
                  (E.pvVia (s.notifiers n).chainTypeManager id) ts }) }
  /-- `transferOwnership`: `onlyOwner`, sets the nominee. -/
  | notifierTransferOwnership {s : State} {caller n o : Address} :
      caller = (s.notifiers n).owner →
      Step E s caller (.notifierTransferOwnership n o)
        { s with notifiers := upd s.notifiers n { s.notifiers n with pendingOwner := o } }
  /-- `acceptOwnership`: only the nominee; clears the nomination. -/
  | notifierAcceptOwnership {s : State} {caller n : Address} :
      caller = (s.notifiers n).pendingOwner →
      Step E s caller (.notifierAcceptOwnership n)
        { s with notifiers := upd s.notifiers n (
            { s.notifiers n with owner := caller, pendingOwner := 0 }) }
  /-- `renounceOwnership`: `onlyOwner`; owner and nominee become zero. -/
  | notifierRenounceOwnership {s : State} {caller n : Address} :
      caller = (s.notifiers n).owner →
      Step E s caller (.notifierRenounceOwnership n)
        { s with notifiers := upd s.notifiers n (
            { s.notifiers n with owner := 0, pendingOwner := 0 }) }
  /-- An implementation swap of notifier `n`: only who controls `n`'s proxy admin; the new code
  may leave any storage, the admin slot included. -/
  | upgradeNotifierProxy {s : State} {caller n : Address} {st : NotifierStore} :
      caller = s.paOwner (s.notifiers n).adminSlot →
      Step E s caller (.upgradeNotifierProxy n st) { s with notifiers := upd s.notifiers n st }
  /-- `changeProxyAdmin` of notifier `n`: `onlyOwner` of its `ProxyAdmin`; the proxy refuses a
  zero admin. -/
  | changeNotifierProxyAdmin {s : State} {caller n a : Address} :
      caller = s.paOwner (s.notifiers n).adminSlot → a ≠ 0 →
      Step E s caller (.changeNotifierProxyAdmin n a)
        { s with notifiers := upd s.notifiers n { s.notifiers n with adminSlot := a } }
  /-- The CTM's `transferOwnership`: `onlyOwner`, sets the nominee. -/
  | ctmTransferOwnership {s : State} {caller o : Address} :
      caller = s.ctm.owner →
      Step E s caller (.ctmTransferOwnership o) { s with ctm := { s.ctm with pendingOwner := o } }
  /-- The CTM's `acceptOwnership`: only the nominee; clears the nomination. -/
  | ctmAcceptOwnership {s : State} {caller : Address} :
      caller = s.ctm.pendingOwner →
      Step E s caller .ctmAcceptOwnership
        { s with ctm := { s.ctm with owner := caller, pendingOwner := 0 } }
  /-- The CTM's `renounceOwnership`: `onlyOwner`; owner and nominee become zero. -/
  | ctmRenounceOwnership {s : State} {caller : Address} :
      caller = s.ctm.owner →
      Step E s caller .ctmRenounceOwnership
        { s with ctm := { s.ctm with owner := 0, pendingOwner := 0 } }
  /-- An implementation swap of the CTM: only who controls the CTM's proxy admin; the new code
  may leave any storage, the admin slot included. -/
  | upgradeCtmProxy {s : State} {caller : Address} {c : CtmStore} :
      caller = s.paOwner s.ctm.adminSlot →
      Step E s caller (.upgradeCtmProxy c) { s with ctm := c }
  /-- `changeProxyAdmin` of the CTM proxy: `onlyOwner` of its `ProxyAdmin`; nonzero. -/
  | changeCtmProxyAdmin {s : State} {caller a : Address} :
      caller = s.paOwner s.ctm.adminSlot → a ≠ 0 →
      Step E s caller (.changeCtmProxyAdmin a) { s with ctm := { s.ctm with adminSlot := a } }
  /-- A `ProxyAdmin`'s `transferOwnership`: `onlyOwner`, nonzero (plain `Ownable`). -/
  | paTransferOwnership {s : State} {caller pa o : Address} :
      caller = s.paOwner pa → o ≠ 0 →
      Step E s caller (.paTransferOwnership pa o) { s with paOwner := upd s.paOwner pa o }
  /-- A `ProxyAdmin`'s `renounceOwnership`: `onlyOwner`. -/
  | paRenounceOwnership {s : State} {caller pa : Address} :
      caller = s.paOwner pa →
      Step E s caller (.paRenounceOwnership pa) { s with paOwner := upd s.paOwner pa 0 }

/-- A sequence of successful calls, each with its own caller. -/
inductive Run (E : Env) : State → List (Address × Op) → State → Prop
  | nil {s : State} : Run E s [] s
  | cons {s s' s'' : State} {caller : Address} {op : Op} {cs : List (Address × Op)} :
      Step E s caller op s' → Run E s' cs s'' → Run E s ((caller, op) :: cs) s''

/-! ## The binding -/

/-- `RegistryAuthorityLib.requireNotifierHandedOver` for notifier `sn` and CTM executor `exec`
(`RegistryAuthorityLib.sol:91-105`), the CTM being `E.ctm`. -/
structure NotifierHandedOver (E : Env) (s : State) (sn exec : Address) : Prop where
  /-- `serverNotifierAddress() == _a.serverNotifier` (:92-95). -/
  ctmPointsAtNotifier : s.ctm.serverNotifier = sn
  /-- The notifier is not the zero address: the check calls `chainTypeManager()` on it (:96),
  and a call to an address without code returns no data, which does not decode as an address, so
  the check reverts. -/
  notifierNonzero : sn ≠ 0
  /-- `ServerNotifier(_a.serverNotifier).chainTypeManager() == _a.ctm` (:96-99). -/
  notifierPointsAtCtm : (s.notifiers sn).chainTypeManager = E.ctm
  /-- `owner() == _a.ctmExecutor` (:100-103). -/
  ownedByExecutor : (s.notifiers sn).owner = exec
  /-- `requireNoNomination` (:104, :109-114). -/
  noNomination : (s.notifiers sn).pendingOwner = 0

/-- The CTM domain in the registry shape: the notifier is handed over, and the CTM, the
CTM-domain `ProxyAdmin` `pa` and through it both proxies are the executor's.

The first four fields are what `RegistryAuthorityLib.requireRegistryAuthority` checks of the
state modelled here (`RegistryAuthorityLib.sol:50-62`). The last two are not checked by it: that
`pa` is the admin of the CTM proxy and of the notifier proxy is what the source documents
(`CTMUpgradeExecutor.sol:38-40`, `ServerNotifier.sol:25-27`, `RegistryTypes.sol:166-168`). -/
structure CtmDomainShape (E : Env) (s : State) (sn exec pa : Address) : Prop where
  /-- `requireNotifierHandedOver` (:61, :91-105). -/
  handedOver : NotifierHandedOver E s sn exec
  /-- The CTM's owner is the executor (:51-54). -/
  ctmOwned : s.ctm.owner = exec
  /-- No nomination outstanding on the CTM (:55). -/
  ctmNoNomination : s.ctm.pendingOwner = 0
  /-- The `ProxyAdmin`'s owner is the executor (:56-59). -/
  proxyAdminOwned : s.paOwner pa = exec
  /-- `pa` is the admin of the CTM proxy. -/
  ctmUnderProxyAdmin : s.ctm.adminSlot = pa
  /-- `pa` is the admin of the notifier proxy. -/
  notifierUnderProxyAdmin : (s.notifiers sn).adminSlot = pa

/-! ## The executor's checks around the engine -/

/-- What `_domainHolders` hashes in a CTM domain (`ProxyUpgradeExecutorBase.sol:123-147`). -/
structure Holders where
  /-- `_proxyAdmin.owner()` (:126). -/
  proxyAdminOwner : Address
  /-- `ctm.owner()` (:127). -/
  ctmOwner : Address
  /-- `ctm.pendingOwner()` (:128). -/
  ctmPendingOwner : Address
  /-- `IChainTypeManager(ctm).admin()` (:129). -/
  ctmAdmin : Address
  /-- `_proxyAdmin.getProxyAdmin(ctm)` (:130). -/
  ctmProxyAdmin : Address
  /-- `serverNotifier`, read by `serverNotifierAddress()` (:123, :131). -/
  serverNotifier : Address
  /-- With a nonzero notifier: its `owner()`, `pendingOwner()`,
  `_proxyAdmin.getProxyAdmin(notifier)` and `chainTypeManager()` (:142-145). -/
  notifierPart : Option (Address × Address × Address × Address)
  deriving DecidableEq

/-- `_proxyAdmin.getProxyAdmin(ctm)` for `_proxyAdmin = pa`: the CTM proxy answers `pa` from its
admin slot when `pa` is its admin, and otherwise forwards `admin()` to the CTM implementation,
which answers its `admin` role (`ProxyUpgradeExecutorBase.sol:112-114`). -/
def ctmProxyAdminSeen (c : CtmStore) (pa : Address) : Address :=
  if c.adminSlot = pa then pa else c.admin

/-- `_domainHolders(_proxyAdmin = pa, ctm)` before hashing, in state `s`
(`ProxyUpgradeExecutorBase.sol:118-148`); `none` when it reverts, which is when the CTM points at
a nonzero notifier that `pa` does not administer: `getProxyAdmin` then reaches the notifier's
implementation, which has no `admin()` (:114). -/
def domainHolders (s : State) (pa : Address) : Option Holders :=
  if s.ctm.serverNotifier = 0 then
    some ⟨s.paOwner pa, s.ctm.owner, s.ctm.pendingOwner, s.ctm.admin, ctmProxyAdminSeen s.ctm pa,
      0, none⟩
  else if (s.notifiers s.ctm.serverNotifier).adminSlot = pa then
    some ⟨s.paOwner pa, s.ctm.owner, s.ctm.pendingOwner, s.ctm.admin, ctmProxyAdminSeen s.ctm pa,
      s.ctm.serverNotifier,
      some ((s.notifiers s.ctm.serverNotifier).owner,
        (s.notifiers s.ctm.serverNotifier).pendingOwner, pa,
        (s.notifiers s.ctm.serverNotifier).chainTypeManager)⟩
  else none

/-- The check before the engine runs (`ProxyUpgradeExecutorBase.sol:72-77`): the CTM's `admin()`
is not the `ProxyAdmin`. -/
def PreCheck (s : State) (pa : Address) : Prop :=
  s.ctm.admin ≠ pa

/-- The domain-holders comparison (`ProxyUpgradeExecutorBase.sol:80, :96-98`) with hash `h`:
both readings succeed and hash equal. -/
def PostCheck {H : Type} (h : Holders → H) (pa : Address) (s s' : State) : Prop :=
  ∃ t t', domainHolders s pa = some t ∧ domainHolders s' pa = some t' ∧ h t' = h t

/-- An engine leg of the CTM-domain executor with `ProxyAdmin` `pa` that the executor accepts:
the check before the engine passes in `s`, the calls `cs` all succeed from `s` to `s'`, and the
domain-holders comparison passes for hash `h`. -/
def LegAccepted {H : Type} (E : Env) (h : Holders → H) (pa : Address) (s : State)
    (cs : List (Address × Op)) (s' : State) : Prop :=
  PreCheck s pa ∧ Run E s cs s' ∧ PostCheck h pa s s'

/-! ## The source's hash -/

/-- The words `abi.encode` lays out for the first `keccak256` of `_domainHolders`
(`ProxyUpgradeExecutorBase.sol:124-133`). -/
def innerPreimage (t : Holders) : List Address :=
  [t.proxyAdminOwner, t.ctmOwner, t.ctmPendingOwner, t.ctmAdmin, t.ctmProxyAdmin,
    t.serverNotifier]

/-- The words of the `keccak256` whose value `_domainHolders` returns: the first preimage when
there is no notifier (:134-136), otherwise the first hash followed by the notifier's four
readings (:138-147). -/
def domainPreimage (k : List Address → Address) (t : Holders) : List Address :=
  match t.notifierPart with
  | none => innerPreimage t
  | some (o, p, a, c) => [k (innerPreimage t), o, p, a, c]

/-- `_domainHolders` as the source computes it, for a keccak `k` on lists of 32-byte words. -/
def domainHash (k : List Address → Address) (t : Holders) : Address :=
  k (domainPreimage k t)

/-! ## Runs of the CTM domain, `forward` left out -/

/-- What happens to the CTM domain of executor `exec`, one transaction at a time, apart from the
executor's `forward` (`governance/UpgradeExecutorBase.sol`, owner-gated). -/
inductive DomainEvent
  /-- A successful call by `caller`, which is neither the executor nor the zero address. -/
  | call (caller : Address) (op : Op)
  /-- `CTMUpgradeExecutor.applyInfrastructureUpgrade` (`CTMUpgradeExecutor.sol:64-72`): an engine
  leg with calls `cs` that the executor accepts; `before` and `after` are the two readings its
  domain-holders comparison hashed. -/
  | leg (cs : List (Address × Op)) (before after : Holders)
  /-- `CTMUpgradeExecutor.acceptCTMOwnership` (`CTMUpgradeExecutor.sol:55-61`): the executor
  calls the CTM's `acceptOwnership()`. -/
  | acceptCtmOwnership

/-- A sequence of `DomainEvent`s, with the engine legs' comparison done with hash `h`. -/
inductive DomainRun (E : Env) {H : Type} (h : Holders → H) (exec pa : Address) :
    State → List DomainEvent → State → Prop
  | nil {s : State} : DomainRun E h exec pa s [] s
  | call {s s' s'' : State} {caller : Address} {op : Op} {es : List DomainEvent} :
      caller ≠ exec → caller ≠ 0 → Step E s caller op s' → DomainRun E h exec pa s' es s'' →
      DomainRun E h exec pa s (.call caller op :: es) s''
  | leg {s s' s'' : State} {cs : List (Address × Op)} {t t' : Holders} {es : List DomainEvent} :
      PreCheck s pa → Run E s cs s' → domainHolders s pa = some t →
      domainHolders s' pa = some t' → h t' = h t → DomainRun E h exec pa s' es s'' →
      DomainRun E h exec pa s (.leg cs t t' :: es) s''
  | acceptCtmOwnership {s s' s'' : State} {es : List DomainEvent} :
      Step E s exec .ctmAcceptOwnership s' → DomainRun E h exec pa s' es s'' →
      DomainRun E h exec pa s (.acceptCtmOwnership :: es) s''

/-! ## Correspondence with `Specs/UpgradeTiming.lean` -/

/-- The timed system `ts` of `Specs/UpgradeTiming.lean` describes state `s` at chain `id`: its
notifier schedule is the live notifier's, the chain's admin is `s.admin`, the chain is
registered at the version the CTM reports, and a version the CTM reports scheduled is
scheduled there too. Nothing here mentions the notifier's `chainTypeManager`. -/
structure AgreesAt (E : Env) (ts : TimedSys) (s : State) (id : ChainId) : Prop where
  /-- `TimedSys.notifier` is the live notifier's `protocolVersionToUpgradeTimestamp`. -/
  notifier : ts.notifier = liveEntry s
  /-- `DiamondAux.admin` is `s.admin`. -/
  admin : (ts.aux id).admin = E.diamondAdmin id
  /-- The chain is registered, at the version `getProtocolVersion(id)` reports. -/
  chain : ∃ c, ts.sys.chains id = some c ∧ c.pv = E.pvVia E.ctm id
  /-- `upgradeTransition(v) != 0 || upgradeCutHash(v) != 0` is what that model checks. -/
  scheduled : ∀ v, E.scheduledVia E.ctm v →
    (ts.sys.ctm.ut v ≠ 0 ∨ ts.sys.ctm.legacy v ≠ LegacyCut.none)

/-! ## Witness data

CTM `8`; its executor `1` owns the CTM and the notifier `6`; the CTM-domain `ProxyAdmin` is `2`,
owned by `1`, and administers both proxies. The CTM's admin role is `4`. Chain `0` is at
version `1`, which has an upgrade scheduled; its diamond's admin is `3`. Contract `9` answers `5`
to `getChainAdmin` for every chain; the notifier `7`, also administered by `2`, is owned by `5`
and points at `9`. -/

/-- The witness environment. -/
def nbEnv : Env where
  ctm := 8
  adminVia := fun c _ => if c = 9 then 5 else 3
  pvVia := fun _ _ => 1
  scheduledVia := fun _ v => v = 1
  checkerAccepts := fun _ _ _ => True
  diamondAdmin := fun _ => 3

/-- `nbEnv` with a CTM whose `getChainAdmin` answers `5`, not the diamond's admin `3`. -/
def nbEnvWrongAdmin : Env := { nbEnv with adminVia := fun _ _ => 5 }

/-- The bound notifier `6`: points at the CTM, owned by the executor, under `ProxyAdmin` `2`,
nothing scheduled. -/
def nbBound : NotifierStore := ⟨8, 1, 0, 2, fun _ _ => 0, fun _ => 0⟩

/-- A foreign notifier `7`: points at `9`, owned by `5`, under `ProxyAdmin` `2`, nothing
scheduled. -/
def nbForeign : NotifierStore := ⟨9, 5, 0, 2, fun _ _ => 0, fun _ => 0⟩

/-- The CTM in the registry shape: it points at `6`, is owned by `1` with no nomination, its
admin role is `4`, and `ProxyAdmin` `2` administers it. -/
def nbCtm : CtmStore := ⟨6, 1, 0, 4, 0, 2⟩

/-- The registry shape: the CTM points at `6`, which is handed over to executor `1`. -/
def nbState0 : State where
  ctm := nbCtm
  notifiers := fun a => if a = 7 then nbForeign else nbBound
  paOwner := fun _ => 1

/-- A timed system that agrees with `nbState0` at chain `0`: chain `0` at version `1` with its
admin `3`, and version `1`'s transition committed at `300`. -/
def nbTimed : TimedSys :=
  ⟨⟨⟨1, 100, fun v => if v = 1 then 300 else 0, fun _ => LegacyCut.none, fun _ => 0⟩,
      fun id => if id = 0 then some ⟨1, fun _ => none⟩ else none⟩,
    fun _ => ⟨3, fun _ => false, 0, 0, none⟩,
    fun _ _ => 0⟩

end Contracts.NotifierBindingV35
