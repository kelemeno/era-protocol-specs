import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsCurrent
import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashEncoding

/-!
# Model: the engine leg of `ProxyUpgradeExecutorBase` at `b17415d20`

Source: era-contracts branch `draft/v0.35.0` at commit
**`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`**. Every `file:line` below is at that commit,
relative to `l1-contracts/contracts/upgrades/registry/` unless it says otherwise. The model was
first written against `d9f678900e1bc8286412b78f56d4a9f443983c29` and re-pinned; the last
section lists what changed between the two.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.EngineLegV35` and are proved in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.EngineLegV35`.

## The leg

At `e561b9cc2` (the snapshot `../../ChainTypeManager/` and `../../ProxyUpgradeRowLib/` model)
each executor applied the rows itself through `ProxyUpgradeRowLib.applyTransition`. On
`draft/v0.35.0` both executors (`CoreUpgradeExecutor.applyL1Upgrade`,
`executors/CoreUpgradeExecutor.sol:33-36`; `CTMUpgradeExecutor.applyInfrastructureUpgrade`,
`executors/CTMUpgradeExecutor.sol:64-72`) call `_applyProxyUpgradeTransition`
(`executors/ProxyUpgradeExecutorBase.sol:51-104`). That function DELEGATECALLS the engine the
transition pins, so the engine runs with the executor's storage and authority. The checks
after the delegatecall are the executor's only on-chain defence against what the engine did.

## `_applyProxyUpgradeTransition` (`executors/ProxyUpgradeExecutorBase.sol:51-104`)

    ObjectAnchorLib.requireCode(address(_transition));                              // :57
    ProxyUpgradeTransitionManifest memory manifest = _transition.getManifest();     // :58
    if (manifest.domain != _domain) { revert ProxyUpgradeDomainMismatch(...); }     // :59-61
    // A codeless delegatecall target succeeds silently.
    ObjectAnchorLib.requireCode(manifest.proxyUpgradeEngine);                       // :62-63
    ProxyUpgradeContext memory context = ProxyUpgradeContext({...});                // :65-71
    if (_chainTypeManager != address(0) &&
        IChainTypeManager(_chainTypeManager).admin() == address(_proxyAdmin)) {
        revert ProxyUpgradeCTMAdminIsProxyAdmin(_chainTypeManager);                 // :75-77
    }
    address ownerBefore = owner();                                                  // :78
    address pendingOwnerBefore = pendingOwner();                                    // :79
    bytes32 domainHoldersBefore = _domainHolders(_proxyAdmin, _chainTypeManager);   // :80
    (bool success, bytes memory returnData) = manifest.proxyUpgradeEngine.delegatecall(
        abi.encodeCall(IProxyUpgradeEngine.executeUpgrade, (context, manifest.proxyUpgrades))); // :82-84
    if (!success) { assembly { revert(add(returnData, 0x20), mload(returnData)) } } // :85-91
    if (owner() != ownerBefore || pendingOwner() != pendingOwnerBefore) {
        revert ProxyUpgradeEngineChangedExecutorOwnership(manifest.proxyUpgradeEngine); // :93-95
    }
    if (_domainHolders(_proxyAdmin, _chainTypeManager) != domainHoldersBefore) {
        revert ProxyUpgradeEngineMovedDomainAuthority(manifest.proxyUpgradeEngine);  // :96-98
    }
    ProxyUpgradeRow[] memory rows = ProxyUpgradeRowLib.toRows(
        manifest.proxyUpgrades, ProxyUpgradeRowLib.inventoryLength(_domain));       // :99-102
    ProxyUpgradeRowLib.requireRowsApplied(_proxyAdmin, rows);                       // :103

The comment above the CTM-admin check (`:72-74`): "A CTM the `ProxyAdmin` no longer
administers answers `getProxyAdmin` with its own `admin()`: were that the `ProxyAdmin`, a moved
CTM would hash as unmoved. The hash pins `admin()`, so refusing that state before the engine
runs covers the leg."

`_domainHolders` (`:118-148`):

    if (_chainTypeManager == address(0)) {
        return keccak256(abi.encode(_proxyAdmin.owner()));                          // :119-121
    }
    IOwnable ctm = IOwnable(_chainTypeManager);
    address serverNotifier = IChainTypeManager(_chainTypeManager).serverNotifierAddress(); // :123
    bytes32 holders = keccak256(abi.encode(_proxyAdmin.owner(), ctm.owner(), ctm.pendingOwner(),
        IChainTypeManager(_chainTypeManager).admin(),
        _proxyAdmin.getProxyAdmin(ITransparentUpgradeableProxy(_chainTypeManager)),
        serverNotifier));                                                           // :124-133
    if (serverNotifier == address(0)) { return holders; }                           // :134-136
    IOwnable notifier = IOwnable(serverNotifier);
    return keccak256(abi.encode(holders, notifier.owner(), notifier.pendingOwner(),
        _proxyAdmin.getProxyAdmin(ITransparentUpgradeableProxy(serverNotifier)),
        IServerNotifier(serverNotifier).chainTypeManager()));                       // :137-147

So the ServerNotifier is read inside `_domainHolders`, once before the engine runs and once
after, and its address is one of the hashed words.

The contract's description (`:34-41`): "What the executor checks after it returns: its own
ownership (owner and pending owner unchanged), the holders of the domain it lends the engine
(…) and every row's proxy at its `implNew`. Anything else the engine does is what governance
reviewed when it approved the transition, and the engine's own postconditions."

`ProxyUpgradeRowLib` (`libraries/ProxyUpgradeRowLib.sol`): `toRows` (`:58-66`) reverts unless
the inventory has exactly `inventoryLength(domain)` slots (`:62-64`), then drops the inert
slots (`_dropInertSlots`, `:145-161`); `requireRowsApplied` (`:133-141`) reverts unless every
row's proxy runs its `implNew`; `applyRows` (`:106-128`) is `requireRowCode`, the
source-checked loop, then `requireRowsApplied`. These are the semantics the `e561b9cc2` model
transcribes (`ProxyUpgradeCurrent.toRows`, `RowsApplied`, `ApplyRows`; compare the code quoted
in `../../ProxyUpgradeRowLib/Specs/RowsCurrent.lean` with `:106-141`), and this file reuses
them. The length check is a separate conjunct here (`LegPre.inventoryLength`).

## Modelling choices

* **A revert is the absence of a step.** `Leg … st s st' s'` says the call succeeds from
  executor storage `st` and world `s` and ends in `st'`, `s'`. The caller check of the two
  entry points (`onlyOwner`) is not modelled.
* **Executor storage** (`Store`) is the two slots the executors declare, `owner` and
  `pendingOwner` (`Ownable2Step`, `l1-contracts/contracts/governance/UpgradeExecutorBase.sol:23`;
  the executors' other bindings are immutables, `executors/CoreUpgradeExecutor.sol:23`,
  `executors/CTMUpgradeExecutor.sol:36,40`), and every other slot (`Store.other`). No executor
  function reads the other slots. Delegatecalled code can write them, and the engine of a
  later transition can read them.
* **Everything else is a world state `σ` read through getters**: `_proxyAdmin.owner()`,
  `IOwnable(x).owner()`, `IOwnable(x).pendingOwner()`, `_proxyAdmin.getProxyAdmin(x)`,
  `IChainTypeManager(ctm).admin()`, `ctm.serverNotifierAddress()`,
  `IServerNotifier(x).chainTypeManager()`, `_proxyAdmin.getProxyImplementation(p)`, code
  existence. The getters are view calls, arbitrary total functions of `σ`. In the source a
  getter can revert, and then the leg reverts; so the model admits at least the legs the source
  admits, and each "successful leg ⇒ …" result carries over. `Env.adminSlot` (who administers
  a proxy) is not read by the executor; it only states `AdminFallsThrough`.
* **The engine** (`Engine`) is an arbitrary relation: from the context, the inventory, the
  executor storage and the world, it picks the executor storage at return and a list of calls
  sent with `msg.sender` = the executor. The storage at return covers the engine's own writes
  and those of any reentrant call (a nominee calling `acceptOwnership`, say). The calls run in
  order through the world's call relation (`CallRun`); a call whose failure the engine catches
  is not in the list. A codeless delegatecall target succeeds with no effect (`Delegate`,
  second disjunct; the comment at `:62`).
* **Hashing.** `keccak256` is an arbitrary function `Env.keccak` on byte strings. Nothing is
  assumed about it. `abi.encode` of a tuple of static words (addresses, `bytes32`) is the
  concatenation of their 32-byte big-endian words (`abiEncode`, reusing
  `AttackVectors.BundleHashEncoding.word`). A real address is a `UInt256` below `2^160`; the
  model encodes the whole word, which is the left-padded encoding for real addresses.
* **`getManifest()`** is a `view` call read once (`:58`): the manifest `M` is the value it
  returned. Nothing is assumed about how the object was constructed.
* **Not modelled**: events, the executor's ETH balance (an engine can send it), the revert
  data bubbled at `:85-91`, gas.

## The concrete world

`WState`/`WCall` is one concrete world, used for the witnesses, the countermodels and the
description of `DefaultProxyUpgradeEngine`: one `ProxyAdmin` (`2`) and an executor (`1`), and
four kinds of executor-sent calls (`ProxyAdmin.upgrade`, `ProxyAdmin.changeProxyAdmin`,
`Ownable2Step.transferOwnership`, `ChainTypeManager.setServerNotifier`). Reinitializers are
inert there, so `upgradeAndCall(…, initializeUpgrade())` is `upgrade`. Contracts are
transparent proxies, and no state used below has the executor as a proxy's admin. The
`ProxyAdmin`'s `getProxyAdmin(x)` answers `2` when `2` is `x`'s admin, and otherwise the
`admin()` of `x`'s implementation, which for a CTM is its admin role (`wGetProxyAdmin`; the
behaviour the comments at `:72-74` and `:112-114` describe). For a proxy whose implementation
has no `admin()` the source reverts there; no scenario below reads such a proxy. The engines of that
world are `DefaultProxyUpgradeEngine` (`engines/DefaultProxyUpgradeEngine.sol:32-47`, empty
hooks `:52`, `:57`, `:63-66`) and subclasses that add a storage write or follow-up calls
(`engineWith`).

## What changed since `d9f6789`

`git diff d9f6789 b17415d20` (commit `9775be946`) on the files this model reads:

* `_applyProxyUpgradeTransition` gained the CTM-admin check (`:72-77`), and the `@dev`
  (`:34-41`) now lists the CTM's admin, its ServerNotifier, and that notifier's CTM among the
  holders.
* `_domainHolders` lost its notifier parameter. It reads `serverNotifierAddress()` itself
  (`:123`), so the before and after hashes each use the notifier of their time. The CTM tuple
  gained the CTM's `admin()` and the notifier's address (`:124-133`), and the notifier tuple
  gained `IServerNotifier(serverNotifier).chainTypeManager()` (`:137-147`). At `d9f6789` the
  notifier was read once before the engine ran and the tuples had four words each.
* `DefaultProxyUpgradeEngine.executeUpgrade` (`:32-47`) gives each hook its own memory copy of
  the calldata inventory. The engines modelled here do not read the inventory in their hooks.
* `ProxyUpgradeRowLib` gained a `@dev` paragraph (`:28-32`) and no code change, so its line
  numbers moved by five.
-/

namespace Contracts.EngineLegV35

open Clear
open Contracts.ProxyUpgradeCurrent (Address Row Impl upd RowsApplied toRows Domain)

/-! ## Encoding -/

/-- One 32-byte ABI word: the value big-endian (`AttackVectors.BundleHashEncoding.word`). -/
def abiWord (w : UInt256) : List UInt8 := AttackVectors.BundleHashEncoding.word w.val

/-- `abi.encode(w₁, …, wₙ)` for static one-word arguments: the words concatenated. -/
def abiEncode (ws : List UInt256) : List UInt8 := ws.flatMap abiWord

/-- `x` and `y` are distinct preimages with the same hash under `k`: a collision on these two
named inputs. -/
def Collides (k : List UInt8 → UInt256) (x y : List UInt8) : Prop := x ≠ y ∧ k x = k y

/-! ## Types -/

/-- `ProxyUpgradeRowLib.inventoryLength` (`libraries/ProxyUpgradeRowLib.sol:47-49`): the member
counts of `L1EcosystemContract` (9) and `CTMContract` (21), counted from the enums
(`libraries/ContractIdentifiers.sol:117-127`, `:64-92`, `:133-134`). The enums are
append-only, so a later commit can have larger counts. -/
def inventoryLength : Domain → ℕ
  | .core => 9
  | .ctm => 21

/-- `ProxyUpgradeTransitionManifest` (`RegistryTypes.sol:205-209`). -/
structure Manifest where
  /-- `domain`. -/
  domain : Domain
  /-- `proxyUpgrades`: the enum-indexed inventory. -/
  proxyUpgrades : List Row
  /-- `proxyUpgradeEngine`. -/
  proxyUpgradeEngine : Address

/-- `ProxyUpgradeContext` (`RegistryTypes.sol:221-227`). -/
structure Context where
  /-- `transition`. -/
  transition : Address
  /-- `proxyUpgradeEngine`. -/
  proxyUpgradeEngine : Address
  /-- `domain`. -/
  domain : Domain
  /-- `proxyAdmin`. -/
  proxyAdmin : Address
  /-- `chainTypeManager`. -/
  chainTypeManager : Address

/-- The executor's storage: the two `Ownable2Step` slots, and every other slot. -/
structure Store where
  /-- `owner()`. -/
  owner : Address
  /-- `pendingOwner()`. -/
  pendingOwner : Address
  /-- Every slot the executors do not declare, by slot number. No executor function reads
  them; delegatecalled code can read and write them. -/
  other : UInt256 → UInt256

/-- The executor's bindings and the world it runs in, as getters of a world state `σ`, and
the calls `κ` the executor can send. -/
structure Env (σ κ : Type) where
  /-- `_proxyAdmin`: the executor's bound `ProxyAdmin`. -/
  proxyAdmin : Address
  /-- `_chainTypeManager`: the bound CTM, or `0` in the `Core` domain. -/
  chainTypeManager : Address
  /-- `ObjectAnchorLib.requireCode` passes (`libraries/ObjectAnchorLib.sol:21-25`). -/
  hasCode : σ → Address → Prop
  /-- `_proxyAdmin.owner()`. -/
  paOwner : σ → Address
  /-- `IOwnable(x).owner()`. -/
  ownerOf : σ → Address → Address
  /-- `IOwnable(x).pendingOwner()`. -/
  pendingOwnerOf : σ → Address → Address
  /-- `_proxyAdmin.getProxyAdmin(x)`. -/
  getProxyAdmin : σ → Address → Address
  /-- `IChainTypeManager(_chainTypeManager).admin()`, read by the executor. -/
  ctmAdmin : σ → Address
  /-- `IChainTypeManager(_chainTypeManager).serverNotifierAddress()`. -/
  serverNotifierAddress : σ → Address
  /-- `IServerNotifier(x).chainTypeManager()`. -/
  notifierCtm : σ → Address → Address
  /-- `_proxyAdmin.getProxyImplementation(p)`. -/
  impl : σ → Impl
  /-- The admin of proxy `x` (its EIP-1967 admin slot). The executor does not read it. -/
  adminSlot : σ → Address → Address
  /-- `keccak256`. Nothing is assumed about it. -/
  keccak : List UInt8 → UInt256
  /-- One successful call sent with `msg.sender` = the executor. -/
  call : σ → κ → σ → Prop

/-- What the code at an engine address does when delegatecalled with `executeUpgrade(ctx, inv)`
from executor storage `st` and world `s`, if it succeeds: the executor storage `st'` at
return and the calls it sends, in order. Any relation is an engine. -/
abbrev Engine (σ κ : Type) :=
  Context → List Row → Store → σ → Store → List κ → Prop

variable {σ κ : Type}

/-- A run of executor-sent calls; a failing call reverts the whole leg. -/
inductive CallRun (E : Env σ κ) : σ → List κ → σ → Prop
  | nil {s : σ} : CallRun E s [] s
  | cons {s s' s'' : σ} {c : κ} {cs : List κ} :
      E.call s c s' → CallRun E s' cs s'' → CallRun E s (c :: cs) s''

/-- The successful delegatecall at `:82-91`. With code at `e`: the engine's storage writes and
calls. Without code: a silent success that changes nothing (the comment at `:62`). -/
def Delegate (E : Env σ κ) (eng : Engine σ κ) (e : Address) (ctx : Context) (inv : List Row)
    (st : Store) (s : σ) (st' : Store) (s' : σ) : Prop :=
  (E.hasCode s e ∧ ∃ calls, eng ctx inv st s st' calls ∧ CallRun E s calls s') ∨
  (¬ E.hasCode s e ∧ st' = st ∧ s' = s)

/-! ## The domain holders (`:118-148`) -/

/-- The `Core` preimage: `abi.encode(_proxyAdmin.owner())` (`:120`). -/
def corePre (E : Env σ κ) (s : σ) : List UInt8 := abiEncode [E.paOwner s]

/-- The six words of the CTM tuple (`:125-132`): the `ProxyAdmin`'s owner, the CTM's owner,
pending owner and admin, the CTM's proxy admin, and the CTM's ServerNotifier. -/
def ctmWords (E : Env σ κ) (s : σ) : List Address :=
  [E.paOwner s, E.ownerOf s E.chainTypeManager, E.pendingOwnerOf s E.chainTypeManager,
    E.ctmAdmin s, E.getProxyAdmin s E.chainTypeManager, E.serverNotifierAddress s]

/-- The CTM preimage (`:124-133`). -/
def ctmPre (E : Env σ κ) (s : σ) : List UInt8 := abiEncode (ctmWords E s)

/-- The four words the notifier tuple adds after the CTM hash (`:142-145`), for the
ServerNotifier the CTM names in `s`: its owner, pending owner, proxy admin and CTM. -/
def notifierWords (E : Env σ κ) (s : σ) : List Address :=
  [E.ownerOf s (E.serverNotifierAddress s), E.pendingOwnerOf s (E.serverNotifierAddress s),
    E.getProxyAdmin s (E.serverNotifierAddress s), E.notifierCtm s (E.serverNotifierAddress s)]

/-- The ServerNotifier preimage (`:139-146`): the CTM hash, then `notifierWords`. -/
def notifierPre (E : Env σ κ) (s : σ) : List UInt8 :=
  abiEncode (E.keccak (ctmPre E s) :: notifierWords E s)

/-- The preimage of the hash `_domainHolders` returns in world `s`: the `Core` preimage; with a
CTM and no ServerNotifier, the CTM preimage; with both, the notifier preimage. -/
def holdersPre (E : Env σ κ) (s : σ) : List UInt8 :=
  if E.chainTypeManager = 0 then corePre E s
  else if E.serverNotifierAddress s = 0 then ctmPre E s
  else notifierPre E s

/-- `_domainHolders(_proxyAdmin, _chainTypeManager)` in world `s` (`:118-148`): `keccak256` of
`holdersPre` in each of the three branches. -/
def domainHolders (E : Env σ κ) (s : σ) : UInt256 := E.keccak (holdersPre E s)

/-- The holder tuple `_domainHolders` hashes, unhashed (`:109-111`): one address in the `Core`
domain, the six `ctmWords` with a CTM and no ServerNotifier, and those followed by the four
`notifierWords` with both. -/
def holderTuple (E : Env σ κ) (s : σ) : List Address :=
  if E.chainTypeManager = 0 then [E.paOwner s]
  else if E.serverNotifierAddress s = 0 then ctmWords E s
  else ctmWords E s ++ notifierWords E s

/-- A collision on the named preimages the holders check compares between `s` and `s'`: the
two preimages whose hashes `:96` compares, or, when both are notifier preimages, the CTM
preimages nested in them. -/
def HoldersBreak (E : Env σ κ) (s s' : σ) : Prop :=
  Collides E.keccak (holdersPre E s) (holdersPre E s') ∨
    (E.chainTypeManager ≠ 0 ∧ E.serverNotifierAddress s ≠ 0 ∧ E.serverNotifierAddress s' ≠ 0 ∧
      Collides E.keccak (ctmPre E s) (ctmPre E s'))

/-- The `ProxyAdmin`'s `getProxyAdmin(ctm)` answers the `ProxyAdmin` when it is the CTM proxy's
admin, and otherwise the CTM's `admin()` role, the value the executor reads as
`IChainTypeManager(ctm).admin()`. This is the behaviour the comments at `:72-74` and `:112-114`
describe: OpenZeppelin v4's `TransparentUpgradeableProxy` answers `admin()` itself only to its
admin and forwards every other caller's call to the implementation, here a CTM implementation
whose `admin()` getter does not depend on the caller. (The submodule
`lib/openzeppelin-contracts-v4`, at `693e945` in `b17415d20`, was not available to cite by
line.) In a state where the executor itself is the CTM proxy's admin, the proxy answers the
executor's `admin()` read itself, so the two answers can differ there; but in such a state
the executor's other reads of the CTM (`serverNotifierAddress()`, `ctm.owner()`) revert, so no
leg starts or ends in it, and total getters satisfying this premise can be chosen for it. -/
def AdminFallsThrough (E : Env σ κ) : Prop :=
  ∀ s, E.getProxyAdmin s E.chainTypeManager =
    if E.adminSlot s E.chainTypeManager = E.proxyAdmin then E.proxyAdmin else E.ctmAdmin s

/-! ## The leg -/

/-- The context the executor builds (`:65-71`) from its own bindings. -/
def context (E : Env σ κ) (T : Address) (M : Manifest) (d : Domain) : Context :=
  ⟨T, M.proxyUpgradeEngine, d, E.proxyAdmin, E.chainTypeManager⟩

/-- The two requirements no countermodel deletes: the transition is code (`:57`) and
`toRows`' length check (`:99-102` with `libraries/ProxyUpgradeRowLib.sol:62-64`). -/
structure LegPre (E : Env σ κ) (T : Address) (M : Manifest) (d : Domain) (s : σ) : Prop where
  /-- `requireCode(address(_transition))` (`:57`). -/
  transitionCode : E.hasCode s T
  /-- `toRows`' length check (`libraries/ProxyUpgradeRowLib.sol:62-64`). -/
  inventoryLength : M.proxyUpgrades.length = inventoryLength d

/-- The leg's six checks, which the countermodels delete one at a time. -/
inductive Check
  /-- `manifest.domain == _domain` (`:59-61`). -/
  | domain
  /-- `requireCode(manifest.proxyUpgradeEngine)` (`:62-63`). -/
  | engineCode
  /-- With a CTM, its `admin()` is not the `ProxyAdmin` before the engine runs (`:75-77`). -/
  | ctmAdmin
  /-- Owner and pending owner unchanged (`:93-95`). -/
  | ownership
  /-- Domain holders' hash unchanged (`:96-98`). -/
  | holders
  /-- `requireRowsApplied` (`:103`). -/
  | rows
deriving DecidableEq

/-- What check `c` requires of a leg from `(st, s)` ending in `(st', s')`. -/
def Check.Holds (E : Env σ κ) (M : Manifest) (d : Domain) (st : Store) (s : σ) (st' : Store)
    (s' : σ) : Check → Prop
  | .domain => M.domain = d
  | .engineCode => E.hasCode s M.proxyUpgradeEngine
  | .ctmAdmin => E.chainTypeManager ≠ 0 → E.ctmAdmin s ≠ E.proxyAdmin
  | .ownership => st'.owner = st.owner ∧ st'.pendingOwner = st.pendingOwner
  | .holders => domainHolders E s' = domainHolders E s
  | .rows => RowsApplied (E.impl s') (toRows M.proxyUpgrades)

/-- Everything in the leg except the six checks: the two fixed requirements and the
delegatecall into the code at `manifest.proxyUpgradeEngine`, whose behaviour is `eng`. -/
def LegCore (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ) : Prop :=
  LegPre E T M d s ∧
    Delegate E eng M.proxyUpgradeEngine (context E T M d) M.proxyUpgrades st s st' s'

/-- A successful `_applyProxyUpgradeTransition(_proxyAdmin, T, d, _chainTypeManager)`
(`:51-104`) whose transition returned manifest `M` and whose engine behaves as `eng`. -/
def Leg (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ) : Prop :=
  LegCore E eng T M d st s st' s' ∧ ∀ c, Check.Holds E M d st s st' s' c

/-- The same leg with check `c₀` deleted and every other check kept. -/
def LegWithout (c₀ : Check) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest)
    (d : Domain) (st : Store) (s : σ) (st' : Store) (s' : σ) : Prop :=
  LegCore E eng T M d st s st' s' ∧ ∀ c, c ≠ c₀ → Check.Holds E M d st s st' s' c

/-- Some outcome of the leg succeeds. -/
def Accepts (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) : Prop :=
  ∃ st' s', Leg E eng T M d st s st' s'

/-- Some outcome of the leg with check `c₀` deleted succeeds. -/
def AcceptsWithout (c₀ : Check) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest)
    (d : Domain) (st : Store) (s : σ) : Prop :=
  ∃ st' s', LegWithout c₀ E eng T M d st s st' s'

/-! ## The concrete world

Executor `1`, `ProxyAdmin` `2`, transition `3`, engine `4`, CTM proxy `8`, ServerNotifier `9`,
another notifier contract `13`, the CTM's admin role `15`. Row proxy `5`, another proxy `6`;
implementations `10`, `11`, `12`. -/

/-- A concrete world: the implementation behind each proxy, the `ProxyAdmin`'s owner, each
`Ownable2Step` contract's owner and pending owner, each proxy's admin, each CTM's admin role
and ServerNotifier, and each ServerNotifier's CTM. -/
structure WState where
  /-- `getProxyImplementation`. -/
  impl : Impl
  /-- `ProxyAdmin.owner()`. -/
  paOwner : Address
  /-- `IOwnable(x).owner()`. -/
  owner : Address → Address
  /-- `IOwnable(x).pendingOwner()`. -/
  pending : Address → Address
  /-- The admin of each proxy (its EIP-1967 admin slot). -/
  adminSlot : Address → Address
  /-- `ChainTypeManager(x).admin()`: the CTM's admin role
  (`l1-contracts/contracts/state-transition/ChainTypeManager.sol:113`). -/
  roleAdmin : Address → Address
  /-- `ChainTypeManager(x).serverNotifierAddress()` (`ChainTypeManager.sol:125`). -/
  notifier : Address → Address
  /-- `ServerNotifier(x).chainTypeManager()`
  (`l1-contracts/contracts/governance/ServerNotifier.sol:30`). -/
  notifierCtm : Address → Address

/-- `ProxyAdmin(2).getProxyAdmin(x)`: `2` if `2` administers `x`, else the `admin()` of `x`'s
implementation, the CTM admin role. -/
def wGetProxyAdmin (s : WState) (x : Address) : Address :=
  if s.adminSlot x = 2 then 2 else s.roleAdmin x

/-- Calls the executor (`1`) can send in the concrete world. -/
inductive WCall
  /-- `ProxyAdmin.upgrade(p, x)`. -/
  | upgrade (p x : Address)
  /-- `ProxyAdmin.changeProxyAdmin(p, x)`: makes `x` the admin of proxy `p`. -/
  | changeProxyAdmin (p x : Address)
  /-- `Ownable2Step(t).transferOwnership(x)`: nominates `x`. -/
  | transferOwnership (t x : Address)
  /-- `ChainTypeManager(t).setServerNotifier(x)` (`ChainTypeManager.sol:387-391`). -/
  | setServerNotifier (t x : Address)

/-- One successful executor-sent call in the concrete world, with the executor `1` as
`msg.sender`. The `ProxyAdmin` calls are `onlyOwner` and reach a proxy's admin functions only
when `2` is its admin; an upgrade needs code at the new implementation (OpenZeppelin's
`ERC1967Upgrade._setImplementation`) and a new admin is nonzero (`_setAdmin`).
`transferOwnership` and `setServerNotifier` are `onlyOwner` on their target. -/
inductive WStep (code : Address → Prop) : WState → WCall → WState → Prop
  | upgrade {s : WState} {p x : Address} : s.paOwner = 1 → s.adminSlot p = 2 → code x →
      WStep code s (.upgrade p x) { s with impl := upd s.impl p x }
  | changeProxyAdmin {s : WState} {p x : Address} : s.paOwner = 1 → s.adminSlot p = 2 →
      x ≠ 0 → WStep code s (.changeProxyAdmin p x) { s with adminSlot := upd s.adminSlot p x }
  | transferOwnership {s : WState} {t x : Address} : s.owner t = 1 →
      WStep code s (.transferOwnership t x) { s with pending := upd s.pending t x }
  | setServerNotifier {s : WState} {t x : Address} : s.owner t = 1 →
      WStep code s (.setServerNotifier t x) { s with notifier := upd s.notifier t x }

/-- The executor's environment in the concrete world: bound CTM `c` (`0` for the `Core`
executor), code predicate `code`, hash `k`. -/
def wEnvWith (c : Address) (code : Address → Prop) (k : List UInt8 → UInt256) :
    Env WState WCall where
  proxyAdmin := 2
  chainTypeManager := c
  hasCode := fun _ a => code a
  paOwner := WState.paOwner
  ownerOf := WState.owner
  pendingOwnerOf := WState.pending
  getProxyAdmin := wGetProxyAdmin
  ctmAdmin := fun s => s.roleAdmin c
  serverNotifierAddress := fun s => s.notifier c
  notifierCtm := WState.notifierCtm
  impl := WState.impl
  adminSlot := WState.adminSlot
  keccak := k
  call := WStep code

/-- The row configuration `applyRows` runs under inside an engine: the executor `1`, the
`ProxyAdmin`'s owner in `s`, inert reinitializers. -/
def rowConfig (code : Address → Prop) (s : WState) : ProxyUpgradeCurrent.Config where
  self := 1
  adminOwner := s.paOwner
  hasCode := code
  reinit := fun _ I => I

/-- The `ProxyAdmin` calls `applyRows`' loop sends (`libraries/ProxyUpgradeRowLib.sol:109-126`):
nothing for a row already at `implNew`, else `upgrade`. -/
def rowCalls : Impl → List Row → List WCall
  | _, [] => []
  | I, r :: rs =>
      if I r.proxy = r.implNew then rowCalls I rs
      else .upgrade r.proxy r.implNew :: rowCalls (upd I r.proxy r.implNew) rs

/-- `DefaultProxyUpgradeEngine.executeUpgrade` (`engines/DefaultProxyUpgradeEngine.sol:32-47`)
in a subclass whose `_afterSwaps` writes executor storage by `write` and sends the follow-up
calls `after`; `_beforeSwaps` and `_checkPostconditions` are empty. In order: the `ProxyAdmin`
owner check (`:33-37`), `toRows`' length check and `applyRows` with its own
`requireRowsApplied` (`:41-44`, `libraries/ProxyUpgradeRowLib.sol:127`), then the hook
(`:45`). -/
def engineWith (code : Address → Prop) (write : Store → Store) (after : List WCall) :
    Engine WState WCall :=
  fun ctx inv st s st' calls =>
    s.paOwner = 1 ∧ inv.length = inventoryLength ctx.domain ∧
      (∃ J, ProxyUpgradeCurrent.ApplyRows (rowConfig code s) s.impl (toRows inv) J) ∧
      st' = write st ∧ calls = rowCalls s.impl (toRows inv) ++ after

/-- `DefaultProxyUpgradeEngine` itself: empty hooks (`:52`, `:57`, `:63-66`). -/
def defaultEngineWith (code : Address → Prop) : Engine WState WCall := engineWith code id []

/-! ## Witness data -/

/-- Every address has code. -/
def allCode : Address → Prop := fun _ => True

/-- `DefaultProxyUpgradeEngine` where every address has code. -/
def defaultEngine : Engine WState WCall := defaultEngineWith allCode

/-- The six CTM words in `w0`. -/
def ctmWords0 : List UInt256 := [1, 1, 0, 15, 2, 9]

/-- The words of the notifier preimage in `w0` once the CTM hash is `100`. -/
def notifierWords0 : List UInt256 := [100, 1, 0, 2, 8]

/-- A toy hash: `100` on the CTM preimage of `w0`, `200` on its notifier preimage, `0` on
everything else. -/
def wKeccak (b : List UInt8) : UInt256 :=
  if b = abiEncode ctmWords0 then 100 else if b = abiEncode notifierWords0 then 200 else 0

/-- A hash that maps everything to `0`. -/
def constKeccak : List UInt8 → UInt256 := fun _ => 0

/-- The CTM executor's environment: CTM `8`, every address has code, hash `wKeccak`. -/
def wEnv : Env WState WCall := wEnvWith 8 allCode wKeccak

/-- Every address except the engine `4` has code. -/
def noEngineCode : Address → Prop := fun a => a ≠ 4

/-- The CTM executor's environment in which the engine has no code. -/
def wEnvCodeless : Env WState WCall := wEnvWith 8 noEngineCode wKeccak

/-- A slot marked "not upgraded". -/
def inertSlot : Row := ⟨0, 0, 0, false⟩

/-- The one row of the witness: proxy `5`, `10 → 11`. -/
def wRow : Row := ⟨5, 10, 11, false⟩

/-- A CTM inventory (21 slots) whose only active slot is `wRow`. -/
def wInv : List Row := wRow :: List.replicate 20 inertSlot

/-- The witness manifest: CTM domain, `wInv`, engine `4`. -/
def wManifest : Manifest := ⟨.ctm, wInv, 4⟩

/-- A CTM inventory with no active slot: an empty transition. -/
def wInvEmpty : List Row := List.replicate 21 inertSlot

/-- The empty transition's manifest. -/
def wManifestEmpty : Manifest := ⟨.ctm, wInvEmpty, 4⟩

/-- A manifest that says `Core` and carries the 21-slot inventory `wInv`. The constructor of
`ProxyUpgradeTransition` refuses it (`objects/ProxyUpgradeTransition.sol:28-31`). -/
def wManifestForeign : Manifest := ⟨.core, wInv, 4⟩

/-- A `Core` inventory (9 slots) whose only active slot is `wRow`. -/
def wInvCore : List Row := wRow :: List.replicate 8 inertSlot

/-- The `Core` witness manifest. -/
def wManifestCore : Manifest := ⟨.core, wInvCore, 4⟩

/-- The transition object's address. -/
def wT : Address := 3

/-- The executor's storage: owned by governance `100`, no nominee, other slots zero. -/
def wStore : Store := ⟨100, 0, fun _ => 0⟩

/-- The start world: every proxy at `10`; the executor `1` owns the `ProxyAdmin`, the CTM and
the ServerNotifier `9`; contract `13` is owned by `6`; no nominees; `2` administers every
proxy; every CTM's admin role is `15` and its notifier `9`; every notifier serves CTM `8`. -/
def w0 : WState where
  impl := fun _ => 10
  paOwner := 1
  owner := fun a => if a = 13 then 6 else 1
  pending := fun _ => 0
  adminSlot := fun _ => 2
  roleAdmin := fun _ => 15
  notifier := fun _ => 9
  notifierCtm := fun _ => 8

/-- `w0` after the row: proxy `5` at `11`. -/
def w1 : WState := { w0 with impl := upd w0.impl 5 11 }

/-- `w1` after `ctm.transferOwnership(7)`. -/
def wNominated : WState := { w1 with pending := upd w1.pending 8 7 }

/-- `w1` after proxy `5` is moved back to `10`. -/
def wMovedBack : WState := { w1 with impl := upd w1.impl 5 10 }

/-- `w1` after proxy `6`, which no row names, is moved to `12`. -/
def wUnlisted : WState := { w1 with impl := upd w1.impl 6 12 }

/-- `w1` after `ctm.setServerNotifier(13)`. -/
def wRepointed : WState := { w1 with notifier := upd w1.notifier 8 13 }

/-- `w1` with the `ProxyAdmin` owned by `6`, not by the executor. -/
def wUnowned : WState := { w1 with paOwner := 6 }

/-- `w0` with every CTM's admin role held by the `ProxyAdmin` `2`. -/
def wAliased : WState := { w0 with roleAdmin := fun _ => 2 }

/-- `wAliased` after the row: proxy `5` at `11`. -/
def wAliased1 : WState := { wAliased with impl := upd wAliased.impl 5 11 }

/-- `wAliased1` after `ProxyAdmin.changeProxyAdmin(ctm, 13)`: `13`, not the `ProxyAdmin`,
administers the CTM proxy. -/
def wCtmMoved : WState := { wAliased1 with adminSlot := upd wAliased1.adminSlot 8 13 }

/-! ## The witness engines -/

/-- An engine whose hook writes `6` into the executor's owner slot. -/
def ownerWriteEngine : Engine WState WCall :=
  engineWith allCode (fun st => { st with owner := 6 }) []

/-- An engine whose hook writes `1` into slot `7` of the executor's storage, a slot the
executors do not declare. -/
def slotWriteEngine : Engine WState WCall :=
  engineWith allCode (fun st => { st with other := upd st.other 7 1 }) []

/-- An engine whose `_afterSwaps` calls `ctm.transferOwnership(7)`. -/
def ctmNominateEngine : Engine WState WCall :=
  engineWith allCode id [.transferOwnership 8 7]

/-- An engine whose `_afterSwaps` moves the row's proxy `5` back to `10`. -/
def moveBackEngine : Engine WState WCall :=
  engineWith allCode id [.upgrade 5 10]

/-- An engine whose `_afterSwaps` moves proxy `6`, which no row names, to `12`. -/
def unlistedMoveEngine : Engine WState WCall :=
  engineWith allCode id [.upgrade 6 12]

/-- An engine whose `_afterSwaps` calls `ctm.setServerNotifier(13)`. -/
def notifierRepointEngine : Engine WState WCall :=
  engineWith allCode id [.setServerNotifier 8 13]

/-- An engine whose `_afterSwaps` calls `ProxyAdmin.changeProxyAdmin(ctm, 13)`. -/
def ctmMoveEngine : Engine WState WCall :=
  engineWith allCode id [.changeProxyAdmin 8 13]

end Contracts.EngineLegV35
