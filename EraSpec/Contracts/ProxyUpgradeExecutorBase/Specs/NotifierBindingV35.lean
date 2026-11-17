import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTiming

/-!
# Model: the ServerNotifier binding, and what an engine leg's post-check sees of it

Source: era-contracts `draft/v0.35.0` at commit **`d9f678900e1bc8286412b78f56d4a9f443983c29`**
(`d9f6789`). Every `file:line` below is at that commit, relative to `l1-contracts/contracts/`.

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
per-version checker. The contract's other functions write none of this: `initialize` (:57-62) is
an `initializer` and reverts on an initialised proxy, and `migrateToGateway` /
`migrateFromGateway` (:78-99) only emit events.

On the real CTM, `getChainAdmin(id)` is `IZKChain(getZKChain(id)).getAdmin()`
(`ChainTypeManager.sol:260-262`, `getZKChain` at :253-255 asks the Bridgehub), and `getAdmin()`
returns the diamond's `s.admin` (`state-transition/chain-deps/facets/Getters.sol:44-46`).
`getProtocolVersion(id)` is the diamond's version in the same way (`ChainTypeManager.sol:714-716`).
That identification is only as good as the notifier's `chainTypeManager` pointer.

## The binding

`RegistryAuthorityLib.requireNotifierHandedOver`
(`upgrades/registry/libraries/RegistryAuthorityLib.sol:91-105`) is the binding: the CTM points
at the notifier (:92-95), the notifier points back at the CTM (:96-99), the notifier is owned by
the CTM executor (:100-103), and no nomination is pending (:104, `requireNoNomination`,
:109-114). It is checked only by the bootstrap
(`upgrades/registry/bootstrap/RegistryBootstrapMigration.sol:171` and, through
`requireRegistryAuthority`, :216). A source search at this commit finds no other caller: nothing
re-checks it after the bootstrap.

## The engine leg's post-check

`ProxyUpgradeExecutorBase._applyProxyUpgradeTransition`
(`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:48-98`) delegatecalls the
transition's engine (:76-78), so every call the engine makes has the executor as `msg.sender`.
The executor owns the CTM, the CTM-domain `ProxyAdmin` and the notifier in the registry shape
(`RegistryAuthorityLib.sol:51-59, :100-103`), so the engine passes every `onlyOwner` of all
three. The contract's NatSpec (`ProxyUpgradeExecutorBase.sol:32-36`) says what the executor
checks afterwards:

    /// @dev The engine runs with the executor's authority and storage. What the executor checks after
    ///      it returns: its own ownership (owner and pending owner unchanged), the holders of the domain
    ///      it lends the engine (the `ProxyAdmin`'s owner and, in a CTM domain, the owner, pending owner
    ///      and proxy admin of the CTM and of its ServerNotifier unchanged; a succession is a `forward`,
    ///      not a leg) and every row's proxy at its `implNew`.

The notifier is read **before** the engine runs (:71-73) and the same address is used after
(:90):

    address serverNotifier = _chainTypeManager == address(0)
        ? address(0)
        : IChainTypeManager(_chainTypeManager).serverNotifierAddress();                     // :71-73
    bytes32 domainHoldersBefore = _domainHolders(_proxyAdmin, _chainTypeManager, serverNotifier); // :74
    ... delegatecall ...                                                                       // :76-85
    if (_domainHolders(_proxyAdmin, _chainTypeManager, serverNotifier) != domainHoldersBefore) {
        revert ProxyUpgradeEngineMovedDomainAuthority(manifest.proxyUpgradeEngine); }          // :90-92

`_domainHolders` (:109-139) hashes `_proxyAdmin.owner()`, the CTM's `owner()` and
`pendingOwner()`, `_proxyAdmin.getProxyAdmin(ctm)` and, when the notifier is nonzero, that
notifier's `owner()`, `pendingOwner()` and `_proxyAdmin.getProxyAdmin(notifier)`. It never
reads `serverNotifierAddress` after the engine, and never reads the notifier's
`chainTypeManager`.

## Modelling choices

* **One CTM**, at `Env.ctm`, which is the diamonds' `s.chainTypeManager` (the identification
  `Specs/UpgradeTiming.lean` already makes: `state-transition/chain-deps/DiamondInit.sol:91`
  sets it to the deploying CTM). Its state is the fields `ctmNotifier`, `ctmOwner`,
  `ctmPending`, `ctmAdmin`.
* **Every address has ServerNotifier-shaped storage** (`State.notifiers`). A pointer may be set
  to any address, so the store of an address nobody uses is arbitrary initial data: this is how
  "a notifier owned by anyone, holding anything" is expressed. A contract at that address that is
  not a ServerNotifier answers whatever its code says, which this model does not bound; that only
  adds behaviour to the `setServerNotifier` results. The CTM's own address is not meant as a
  notifier address.
* **What other contracts answer is fixed configuration (`Env`)**: what each address answers to
  `getChainAdmin(id)`, `getProtocolVersion(id)`, whether it has an upgrade scheduled at a version
  (`upgradeTransition(v) != 0 || upgradeCutHash(v) != 0`), and whether a checker accepts a chain.
  Every per-step result here is about one step inside one transaction. `ShapeKeptByOtherCallers`
  is about a sequence of steps, and it does not read `Env`'s answers at all.
* **Proxy admins are their ERC-1967 admin slot** (`ctmAdmin`, `proxyAdminOf`; the latter is used
  for notifier addresses only). The source reads them through OpenZeppelin v4
  `ProxyAdmin.getProxyAdmin`, a `staticcall` of `admin()` that the proxy answers from the slot
  only when the caller is its admin. Otherwise the call reaches the implementation: "a moved CTM
  answers its own `admin()` and fails the comparison, a moved ServerNotifier has none and reverts
  the leg" (`ProxyUpgradeExecutorBase.sol:106-108`). So for a proxy the `ProxyAdmin` no longer
  administers, the source rejects the leg where the model's tuples merely differ. No accepted leg
  in the results here writes an admin slot. For `PostCheckAfterRead`, which is not the source's
  check, reading a notifier `_proxyAdmin` does not administer would also revert; that variant
  therefore accepts at most what the model says it accepts.
* **`paOwner a` is who controls the proxy admin `a`**: `owner()` when `a` is an OpenZeppelin
  `ProxyAdmin` (plain `Ownable`), as it is for the CTM domain's. An implementation swap or admin
  change of a proxy is by `paOwner` of its admin. For a foreign notifier whose admin is an
  externally owned account, read `paOwner a` as `a`.
* **The hash is a parameter.** `PostCheck h` compares `h` of the holders tuples. Every
  "the check passes" result is for every `h` (equal tuples hash equal), so no property of
  keccak is assumed. Where a result says the check fails, it is stated for the comparison of the
  tuples themselves (`h = id`), and for an arbitrary `h` as: passing needs `h` to collide on two
  specific, distinct tuples.
* **The executor's own-ownership check** (:87-89) and the **row check** (:93-97) read state no
  step of this model writes: the executor's own storage, and the implementation slots of the
  proxies the manifest's rows name (the row carries its proxy address,
  `upgrades/registry/RegistryTypes.sol:168-173`; it is not looked up through the CTM). They are
  left out of `PostCheck`. The legs in the results swap no implementation, so they can be
  appended to any leg that passes both.
* **Writers modelled**: the five functions named above; the `Ownable2Step` ownership functions
  of the notifier (OpenZeppelin v4; `ServerNotifier` overrides none) and of the CTM
  (`Ownable2StepUpgradeable`, `ChainTypeManager.sol:58`; `renounceOwnership` is not disabled);
  `transferOwnership` / `renounceOwnership` of a `ProxyAdmin`; `ProxyAdmin.changeProxyAdmin` for
  a notifier proxy and for the CTM proxy; and an implementation swap of either proxy through its
  `ProxyAdmin`, which may leave any storage in the fields modelled here.
* **A revert is the absence of a step.** Events are omitted.
-/

namespace Contracts.NotifierBindingV35

open Contracts.ChainTypeManager

/-! ## State -/

/-- One ServerNotifier proxy's storage (`governance/ServerNotifier.sol:28-39`). -/
structure NotifierStore where
  /-- `chainTypeManager` (:30): the contract `onlyChainAdmin` asks. -/
  ctm : Address
  /-- `Ownable.owner()`. -/
  owner : Address
  /-- `Ownable2Step.pendingOwner()`; zero when no nomination is outstanding. -/
  pending : Address
  /-- `protocolVersionToUpgradeTimestamp[chainId][oldProtocolVersion]` (:33-34); zero is unset. -/
  entry : ChainId → ℕ → ℕ
  /-- `upgradePreconditionChecker[oldProtocolVersion]` (:37-39); zero is none. -/
  checker : ℕ → Address

/-- The CTM's notifier-related state, every address's notifier storage, and the proxy admins. -/
structure State where
  /-- The CTM's `serverNotifierAddress` (`ChainTypeManager.sol:125`). -/
  ctmNotifier : Address
  /-- The CTM's `owner()`. -/
  ctmOwner : Address
  /-- The CTM's `pendingOwner()`. -/
  ctmPending : Address
  /-- The ERC-1967 admin of the CTM proxy. -/
  ctmAdmin : Address
  /-- The ServerNotifier storage at each address. -/
  notifiers : Address → NotifierStore
  /-- The ERC-1967 admin of the notifier proxy at each address. -/
  proxyAdminOf : Address → Address
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
  (s.notifiers s.ctmNotifier).entry id v

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
  /-- An implementation swap of the CTM proxy through its `ProxyAdmin` that leaves
  `serverNotifierAddress = n`, `owner() = o` and `pendingOwner() = p`. -/
  | upgradeCtmProxy (n o p : Address)
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
      caller = s.ctmOwner →
      Step E s caller (.setServerNotifier n) { s with ctmNotifier := n }
  /-- `setChainTypeManager`: `onlyOwner`, nonzero (`ServerNotifier.sol:67-72`). -/
  | setChainTypeManager {s : State} {caller n c : Address} :
      caller = (s.notifiers n).owner → c ≠ 0 →
      Step E s caller (.setChainTypeManager n c)
        { s with notifiers := upd s.notifiers n { s.notifiers n with ctm := c } }
  /-- `setUpgradePreconditionChecker`: `onlyOwner` (`ServerNotifier.sol:135-141`). -/
  | setUpgradePreconditionChecker {s : State} {caller n : Address} {v : ℕ} {k : Address} :
      caller = (s.notifiers n).owner →
      Step E s caller (.setUpgradePreconditionChecker n v k)
        { s with notifiers := upd s.notifiers n (
            { s.notifiers n with checker := upd (s.notifiers n).checker v k }) }
  /-- `setUpgradeTimestamp` (`ServerNotifier.sol:113-132`), every check asked of the notifier's
  own `chainTypeManager`. -/
  | setUpgradeTimestamp {s : State} {caller n : Address} {id : ChainId} {ts : ℕ} :
      caller = E.adminVia (s.notifiers n).ctm id →
      ts ≠ 0 →
      E.scheduledVia (s.notifiers n).ctm (E.pvVia (s.notifiers n).ctm id) →
      ((s.notifiers n).checker (E.pvVia (s.notifiers n).ctm id) = 0 ∨
        E.checkerAccepts ((s.notifiers n).checker (E.pvVia (s.notifiers n).ctm id))
          (s.notifiers n).ctm id) →
      Step E s caller (.setUpgradeTimestamp n id ts)
        { s with notifiers := upd s.notifiers n (
            { s.notifiers n with
                entry := setEntry (s.notifiers n).entry id (E.pvVia (s.notifiers n).ctm id) ts }) }
  /-- `transferOwnership`: `onlyOwner`, sets the nominee. -/
  | notifierTransferOwnership {s : State} {caller n o : Address} :
      caller = (s.notifiers n).owner →
      Step E s caller (.notifierTransferOwnership n o)
        { s with notifiers := upd s.notifiers n { s.notifiers n with pending := o } }
  /-- `acceptOwnership`: only the nominee; clears the nomination. -/
  | notifierAcceptOwnership {s : State} {caller n : Address} :
      caller = (s.notifiers n).pending →
      Step E s caller (.notifierAcceptOwnership n)
        { s with notifiers := upd s.notifiers n (
            { s.notifiers n with owner := caller, pending := 0 }) }
  /-- `renounceOwnership`: `onlyOwner`; owner and nominee become zero. -/
  | notifierRenounceOwnership {s : State} {caller n : Address} :
      caller = (s.notifiers n).owner →
      Step E s caller (.notifierRenounceOwnership n)
        { s with notifiers := upd s.notifiers n (
            { s.notifiers n with owner := 0, pending := 0 }) }
  /-- An implementation swap of notifier `n`: only who controls `n`'s proxy admin; the new code
  may leave any storage. -/
  | upgradeNotifierProxy {s : State} {caller n : Address} {st : NotifierStore} :
      caller = s.paOwner (s.proxyAdminOf n) →
      Step E s caller (.upgradeNotifierProxy n st) { s with notifiers := upd s.notifiers n st }
  /-- `changeProxyAdmin` of notifier `n`: `onlyOwner` of its `ProxyAdmin`; the proxy refuses a
  zero admin. -/
  | changeNotifierProxyAdmin {s : State} {caller n a : Address} :
      caller = s.paOwner (s.proxyAdminOf n) → a ≠ 0 →
      Step E s caller (.changeNotifierProxyAdmin n a)
        { s with proxyAdminOf := upd s.proxyAdminOf n a }
  /-- The CTM's `transferOwnership`: `onlyOwner`, sets the nominee. -/
  | ctmTransferOwnership {s : State} {caller o : Address} :
      caller = s.ctmOwner →
      Step E s caller (.ctmTransferOwnership o) { s with ctmPending := o }
  /-- The CTM's `acceptOwnership`: only the nominee; clears the nomination. -/
  | ctmAcceptOwnership {s : State} {caller : Address} :
      caller = s.ctmPending →
      Step E s caller .ctmAcceptOwnership { s with ctmOwner := caller, ctmPending := 0 }
  /-- The CTM's `renounceOwnership`: `onlyOwner`; owner and nominee become zero. -/
  | ctmRenounceOwnership {s : State} {caller : Address} :
      caller = s.ctmOwner →
      Step E s caller .ctmRenounceOwnership { s with ctmOwner := 0, ctmPending := 0 }
  /-- An implementation swap of the CTM: only who controls the CTM's proxy admin; the new code
  may leave any notifier pointer, owner and nominee. -/
  | upgradeCtmProxy {s : State} {caller n o p : Address} :
      caller = s.paOwner s.ctmAdmin →
      Step E s caller (.upgradeCtmProxy n o p)
        { s with ctmNotifier := n, ctmOwner := o, ctmPending := p }
  /-- `changeProxyAdmin` of the CTM proxy: `onlyOwner` of its `ProxyAdmin`; nonzero. -/
  | changeCtmProxyAdmin {s : State} {caller a : Address} :
      caller = s.paOwner s.ctmAdmin → a ≠ 0 →
      Step E s caller (.changeCtmProxyAdmin a) { s with ctmAdmin := a }
  /-- A `ProxyAdmin`'s `transferOwnership`: `onlyOwner`, nonzero (plain `Ownable`). -/
  | paTransferOwnership {s : State} {caller pa o : Address} :
      caller = s.paOwner pa → o ≠ 0 →
      Step E s caller (.paTransferOwnership pa o) { s with paOwner := upd s.paOwner pa o }
  /-- A `ProxyAdmin`'s `renounceOwnership`: `onlyOwner`. -/
  | paRenounceOwnership {s : State} {caller pa : Address} :
      caller = s.paOwner pa →
      Step E s caller (.paRenounceOwnership pa) { s with paOwner := upd s.paOwner pa 0 }

/-- A sequence of successful calls by one caller: what an engine does while delegatecalled by
the executor `caller` (`ProxyUpgradeExecutorBase.sol:76-78`). -/
inductive Leg (E : Env) : State → Address → List Op → State → Prop
  | nil {s : State} {caller : Address} : Leg E s caller [] s
  | cons {s s' s'' : State} {caller : Address} {op : Op} {ops : List Op} :
      Step E s caller op s' → Leg E s' caller ops s'' → Leg E s caller (op :: ops) s''

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
  ctmPointsAtNotifier : s.ctmNotifier = sn
  /-- `ServerNotifier(_a.serverNotifier).chainTypeManager() == _a.ctm` (:96-99). -/
  notifierPointsAtCtm : (s.notifiers sn).ctm = E.ctm
  /-- `owner() == _a.ctmExecutor` (:100-103). -/
  ownedByExecutor : (s.notifiers sn).owner = exec
  /-- `requireNoNomination` (:104, :109-114). -/
  noNomination : (s.notifiers sn).pending = 0

/-- The CTM domain in the registry shape: the notifier is handed over, and the CTM, the
CTM-domain `ProxyAdmin` `pa` and through it both proxies are the executor's.

The first four fields are what `RegistryAuthorityLib.requireRegistryAuthority` checks of the
state modelled here (`RegistryAuthorityLib.sol:50-62`). The last two are not checked by it: that
`pa` is the admin of the CTM proxy and of the notifier proxy is what the source documents
(`CTMUpgradeExecutor.sol:38-40`, `ServerNotifier.sol:25-27`, `RegistryTypes.sol:164-166`). -/
structure CtmDomainShape (E : Env) (s : State) (sn exec pa : Address) : Prop where
  /-- `requireNotifierHandedOver` (:61, :91-105). -/
  handedOver : NotifierHandedOver E s sn exec
  /-- The CTM's owner is the executor (:51-54). -/
  ctmOwned : s.ctmOwner = exec
  /-- No nomination outstanding on the CTM (:55). -/
  ctmNoNomination : s.ctmPending = 0
  /-- The `ProxyAdmin`'s owner is the executor (:56-59). -/
  proxyAdminOwned : s.paOwner pa = exec
  /-- `pa` is the admin of the CTM proxy. -/
  ctmUnderProxyAdmin : s.ctmAdmin = pa
  /-- `pa` is the admin of the notifier proxy. -/
  notifierUnderProxyAdmin : s.proxyAdminOf sn = pa

/-! ## The executor's post-check -/

/-- What `_domainHolders` hashes in a CTM domain (`ProxyUpgradeExecutorBase.sol:117-138`). -/
structure Holders where
  /-- `_proxyAdmin.owner()`. -/
  proxyAdminOwner : Address
  /-- `ctm.owner()`. -/
  ctmOwner : Address
  /-- `ctm.pendingOwner()`. -/
  ctmPending : Address
  /-- `_proxyAdmin.getProxyAdmin(ctm)`. -/
  ctmAdmin : Address
  /-- With a nonzero notifier: its `owner()`, `pendingOwner()` and
  `_proxyAdmin.getProxyAdmin(notifier)` (:126-138). -/
  notifier : Option (Address × Address × Address)
  deriving DecidableEq

/-- `_domainHolders(_proxyAdmin = pa, ctm, _serverNotifier = sn)` before hashing, in state `s`. -/
def holders (s : State) (pa sn : Address) : Holders :=
  { proxyAdminOwner := s.paOwner pa
    ctmOwner := s.ctmOwner
    ctmPending := s.ctmPending
    ctmAdmin := s.ctmAdmin
    notifier := if sn = 0 then none
      else some ((s.notifiers sn).owner, (s.notifiers sn).pending, s.proxyAdminOf sn) }

/-- The domain-holders comparison as written (`ProxyUpgradeExecutorBase.sol:71-74, :90-92`), with
hash `h`: the notifier is the one the CTM pointed at **before** the engine ran, in both readings. -/
def PostCheck {H : Type} (h : Holders → H) (pa : Address) (s s' : State) : Prop :=
  h (holders s' pa s.ctmNotifier) = h (holders s pa s.ctmNotifier)

/-- The same comparison with the notifier read again **after** the engine. Not what the source
does; stated to show that the read time is load-bearing. -/
def PostCheckAfterRead {H : Type} (h : Holders → H) (pa : Address) (s s' : State) : Prop :=
  h (holders s' pa s'.ctmNotifier) = h (holders s pa s.ctmNotifier)

/-- An engine leg of the CTM-domain executor `exec`, with `ProxyAdmin` `pa`, that the executor
accepts: every call succeeds and the domain-holders check passes for hash `h`. -/
def LegAccepted {H : Type} (E : Env) (h : Holders → H) (exec pa : Address) (s : State)
    (ops : List Op) (s' : State) : Prop :=
  Leg E s exec ops s' ∧ PostCheck h pa s s'

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
owned by `1`. Chain `0` is at version `1`, which has an upgrade scheduled; its diamond's admin
is `3`. Contract `9` answers `5` to `getChainAdmin` for every chain; the notifier `7` is owned
by `5` and points at `9`. -/

/-- The witness environment. -/
def wEnv : Env where
  ctm := 8
  adminVia := fun c _ => if c = 9 then 5 else 3
  pvVia := fun _ _ => 1
  scheduledVia := fun _ v => v = 1
  checkerAccepts := fun _ _ _ => True
  diamondAdmin := fun _ => 3

/-- `wEnv` with a CTM whose `getChainAdmin` answers `5`, not the diamond's admin `3`. -/
def wEnvWrongAdmin : Env := { wEnv with adminVia := fun _ _ => 5 }

/-- The bound notifier `6`: points at the CTM, owned by the executor, nothing scheduled. -/
def wBound : NotifierStore := ⟨8, 1, 0, fun _ _ => 0, fun _ => 0⟩

/-- A foreign notifier `7`: points at `9`, owned by `5`, nothing scheduled. -/
def wForeign : NotifierStore := ⟨9, 5, 0, fun _ _ => 0, fun _ => 0⟩

/-- The registry shape: the CTM points at `6`, which is handed over to executor `1`. -/
def wState0 : State where
  ctmNotifier := 6
  ctmOwner := 1
  ctmPending := 0
  ctmAdmin := 2
  notifiers := fun a => if a = 7 then wForeign else wBound
  proxyAdminOf := fun _ => 2
  paOwner := fun _ => 1

/-- A timed system that agrees with `wState0` at chain `0`: chain `0` at version `1` with its
admin `3`, and version `1`'s transition committed at `300`. -/
def wTimed : TimedSys :=
  ⟨⟨⟨1, 100, fun v => if v = 1 then 300 else 0, fun _ => LegacyCut.none, fun _ => 0⟩,
      fun id => if id = 0 then some ⟨1, fun _ => none⟩ else none⟩,
    fun _ => ⟨3, fun _ => false, 0, 0, none⟩,
    fun _ _ => 0⟩

end Contracts.NotifierBindingV35
