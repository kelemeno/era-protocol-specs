import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsCurrent
import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashEncoding

/-!
# Model: the engine leg of `ProxyUpgradeExecutorBase` at `d9f6789`

Source: era-contracts branch `draft/v0.35.0` at commit
**`d9f678900e1bc8286412b78f56d4a9f443983c29`**. Every `file:line` below is at that commit,
relative to `l1-contracts/contracts/upgrades/registry/` unless it says otherwise.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.EngineLegV35` and are proved in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.EngineLegV35`.

## What changed since `e561b9cc2`

At `e561b9cc2` (the snapshot `../../ChainTypeManager/` and `../../ProxyUpgradeRowLib/` model)
each executor applied the rows itself through `ProxyUpgradeRowLib.applyTransition`. At
`d9f6789` both executors (`CoreUpgradeExecutor.applyL1Upgrade`,
`executors/CoreUpgradeExecutor.sol:33-36`; `CTMUpgradeExecutor.applyInfrastructureUpgrade`,
`executors/CTMUpgradeExecutor.sol:64-72`) call `_applyProxyUpgradeTransition`
(`executors/ProxyUpgradeExecutorBase.sol:48-98`). That function DELEGATECALLS the engine the
transition pins, so the engine runs with the executor's storage and authority. The post-checks
after the delegatecall are the executor's only on-chain defence against what the engine did.

## `_applyProxyUpgradeTransition` (`executors/ProxyUpgradeExecutorBase.sol:48-98`)

    ObjectAnchorLib.requireCode(address(_transition));                              // :54
    ProxyUpgradeTransitionManifest memory manifest = _transition.getManifest();     // :55
    if (manifest.domain != _domain) { revert ProxyUpgradeDomainMismatch(...); }     // :56-58
    // A codeless delegatecall target succeeds silently.
    ObjectAnchorLib.requireCode(manifest.proxyUpgradeEngine);                       // :59-60
    ProxyUpgradeContext memory context = ProxyUpgradeContext({...});                // :62-68
    address ownerBefore = owner();                                                  // :69
    address pendingOwnerBefore = pendingOwner();                                    // :70
    address serverNotifier = _chainTypeManager == address(0)
        ? address(0) : IChainTypeManager(_chainTypeManager).serverNotifierAddress(); // :71-73
    bytes32 domainHoldersBefore = _domainHolders(_proxyAdmin, _chainTypeManager, serverNotifier); // :74
    (bool success, bytes memory returnData) = manifest.proxyUpgradeEngine.delegatecall(
        abi.encodeCall(IProxyUpgradeEngine.executeUpgrade, (context, manifest.proxyUpgrades))); // :76-78
    if (!success) { assembly { revert(add(returnData, 0x20), mload(returnData)) } } // :79-85
    if (owner() != ownerBefore || pendingOwner() != pendingOwnerBefore) {
        revert ProxyUpgradeEngineChangedExecutorOwnership(manifest.proxyUpgradeEngine); // :87-89
    }
    if (_domainHolders(_proxyAdmin, _chainTypeManager, serverNotifier) != domainHoldersBefore) {
        revert ProxyUpgradeEngineMovedDomainAuthority(manifest.proxyUpgradeEngine);  // :90-92
    }
    ProxyUpgradeRow[] memory rows = ProxyUpgradeRowLib.toRows(
        manifest.proxyUpgrades, ProxyUpgradeRowLib.inventoryLength(_domain));       // :93-96
    ProxyUpgradeRowLib.requireRowsApplied(_proxyAdmin, rows);                       // :97

`_domainHolders` (`:109-139`):

    if (_chainTypeManager == address(0)) {
        return keccak256(abi.encode(_proxyAdmin.owner()));                          // :114-116
    }
    IOwnable ctm = IOwnable(_chainTypeManager);
    bytes32 holders = keccak256(abi.encode(_proxyAdmin.owner(), ctm.owner(), ctm.pendingOwner(),
        _proxyAdmin.getProxyAdmin(ITransparentUpgradeableProxy(_chainTypeManager)))); // :117-125
    if (_serverNotifier == address(0)) { return holders; }                          // :126-128
    IOwnable notifier = IOwnable(_serverNotifier);
    return keccak256(abi.encode(holders, notifier.owner(), notifier.pendingOwner(),
        _proxyAdmin.getProxyAdmin(ITransparentUpgradeableProxy(_serverNotifier)))); // :129-138

The contract's description (`:32-38`): "What the executor checks after it returns: its own
ownership (owner and pending owner unchanged), the holders of the domain it lends the engine
(…) and every row's proxy at its `implNew`. Anything else the engine does is what governance
reviewed when it approved the transition, and the engine's own postconditions."

`ProxyUpgradeRowLib` at `d9f6789` (`libraries/ProxyUpgradeRowLib.sol`): `toRows` (`:53-61`)
reverts unless the inventory has exactly `inventoryLength(domain)` slots (`:57-59`), then drops
the inert slots (`_dropInertSlots`, `:140-156`); `requireRowsApplied` (`:128-136`) reverts
unless every row's proxy runs its `implNew`; `applyRows` (`:101-123`) is `requireRowCode`, the
source-checked loop, then `requireRowsApplied`. `git diff e561b9cc2 d9f6789` on the library
only removes `applyTransition` and splits the last loop of `applyRows` out as
`requireRowsApplied`, so these are the semantics of the `e561b9cc2` model
(`ProxyUpgradeCurrent.toRows`, `RowsApplied`, `ApplyRows`), which this file reuses. The
length check is a separate conjunct here (`LegPre.inventoryLength`).

## Modelling choices

* **A revert is the absence of a step.** `Leg … st s st' s'` says the call succeeds from
  executor storage `st` and world `s` and ends in `st'`, `s'`.
* **Executor storage** (`Store`) is the two slots the executors declare, `owner` and
  `pendingOwner` (`Ownable2Step`, `l1-contracts/contracts/governance/UpgradeExecutorBase.sol:22`;
  the executors' other bindings are immutables, `executors/CoreUpgradeExecutor.sol:23`,
  `executors/CTMUpgradeExecutor.sol:36,40`), and every other slot (`Store.other`). No executor
  function reads the other slots. Delegatecalled code can write them, and the engine of a
  later transition can read them.
* **Everything else is a world state `σ` read through getters**: `_proxyAdmin.owner()`,
  `IOwnable(x).owner()`, `IOwnable(x).pendingOwner()`, `_proxyAdmin.getProxyAdmin(x)`,
  `ctm.serverNotifierAddress()`, `_proxyAdmin.getProxyImplementation(p)`, code existence. The
  getters are arbitrary total functions of `σ`. In the source a getter can revert, and then
  the leg reverts; so the model admits at least the legs the source admits, and each
  "successful leg ⇒ …" result carries over. What `getProxyAdmin` and
  `getProxyImplementation` answer for a proxy the admin no longer administers (`:106-108`) is a
  separate topic.
* **The engine** (`Engine`) is an arbitrary relation: from the context, the inventory, the
  executor storage and the world, it picks the executor storage at return and a list of calls
  sent with `msg.sender` = the executor. The storage at return covers the engine's own writes
  and those of any reentrant call (a nominee calling `acceptOwnership`, say). The calls run in
  order through the world's call relation (`CallRun`); a call whose failure the engine catches
  is not in the list. A codeless delegatecall target succeeds with no effect (`Delegate`,
  second disjunct; the comment at `:59`).
* **Hashing.** `keccak256` is an arbitrary function `Env.keccak` on byte strings. Nothing is
  assumed about it. `abi.encode` of a tuple of static words (addresses, `bytes32`) is the
  concatenation of their 32-byte big-endian words (`abiEncode`, reusing
  `AttackVectors.BundleHashEncoding.word`). A real address is a `UInt256` below `2^160`; the
  model encodes the whole word, which is the left-padded encoding for real addresses.
* **`getManifest()`** is a `view` call read once (`:55`): the manifest `M` is the value it
  returned. Nothing is assumed about how the object was constructed.
* **Not modelled**: events, the executor's ETH balance (an engine can send it), the revert
  data bubbled at `:79-85`, gas.

## The concrete world

`WState`/`WCall` is one concrete world, used for the witnesses, the countermodels and the
description of `DefaultProxyUpgradeEngine`: one `ProxyAdmin` (`2`) and an executor (`1`), and
three kinds of executor-sent calls (`ProxyAdmin.upgrade`, `Ownable2Step.transferOwnership`,
`ChainTypeManager.setServerNotifier`). Reinitializers are inert there, so
`upgradeAndCall(…, initializeUpgrade())` is `upgrade`. The engines of that world are
`DefaultProxyUpgradeEngine` (`engines/DefaultProxyUpgradeEngine.sol:32-46`, empty hooks
`:51`, `:56`, `:62-65`) and subclasses that add a storage write or follow-up calls
(`engineWith`).
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

/-- `ProxyUpgradeRowLib.inventoryLength` (`libraries/ProxyUpgradeRowLib.sol:42-44`): the member
counts of `L1EcosystemContract` (9) and `CTMContract` (21), counted from the enums at
`d9f6789` (`libraries/ContractIdentifiers.sol:111-121`, `:61-89`, `:127-128`). The enums are
append-only, so a later commit can have larger counts. -/
def inventoryLength : Domain → ℕ
  | .core => 9
  | .ctm => 21

/-- `ProxyUpgradeTransitionManifest` (`RegistryTypes.sol:203-207`). -/
structure Manifest where
  /-- `domain`. -/
  domain : Domain
  /-- `proxyUpgrades`: the enum-indexed inventory. -/
  proxyUpgrades : List Row
  /-- `proxyUpgradeEngine`. -/
  proxyUpgradeEngine : Address

/-- `ProxyUpgradeContext` (`RegistryTypes.sol:219-225`). -/
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
  /-- `address(this)`: the executor. -/
  self : Address
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
  /-- `IChainTypeManager(_chainTypeManager).serverNotifierAddress()`. -/
  serverNotifierAddress : σ → Address
  /-- `_proxyAdmin.getProxyImplementation(p)`. -/
  impl : σ → Impl
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

/-- The successful delegatecall at `:76-85`. With code at `e`: the engine's storage writes and
calls. Without code: a silent success that changes nothing (the comment at `:59`). -/
def Delegate (E : Env σ κ) (eng : Engine σ κ) (e : Address) (ctx : Context) (inv : List Row)
    (st : Store) (s : σ) (st' : Store) (s' : σ) : Prop :=
  (E.hasCode s e ∧ ∃ calls, eng ctx inv st s st' calls ∧ CallRun E s calls s') ∨
  (¬ E.hasCode s e ∧ st' = st ∧ s' = s)

/-! ## The domain holders (`:109-139`) -/

/-- The ServerNotifier read at `:71-73`, before the engine runs. -/
def notifierAt (E : Env σ κ) (s : σ) : Address :=
  if E.chainTypeManager = 0 then 0 else E.serverNotifierAddress s

/-- The `Core` preimage: `abi.encode(_proxyAdmin.owner())` (`:115`). -/
def corePre (E : Env σ κ) (s : σ) : List UInt8 := abiEncode [E.paOwner s]

/-- The CTM preimage (`:118-125`): the `ProxyAdmin`'s owner, the CTM's owner and pending
owner, and the CTM's proxy admin. -/
def ctmPre (E : Env σ κ) (s : σ) : List UInt8 :=
  abiEncode [E.paOwner s, E.ownerOf s E.chainTypeManager, E.pendingOwnerOf s E.chainTypeManager,
    E.getProxyAdmin s E.chainTypeManager]

/-- The ServerNotifier preimage (`:130-137`): the CTM hash, then the notifier `n`'s owner,
pending owner and proxy admin. -/
def notifierPre (E : Env σ κ) (n : Address) (s : σ) : List UInt8 :=
  abiEncode [E.keccak (ctmPre E s), E.ownerOf s n, E.pendingOwnerOf s n, E.getProxyAdmin s n]

/-- `_domainHolders(_proxyAdmin, _chainTypeManager, n)` in world `s` (`:109-139`). -/
def domainHolders (E : Env σ κ) (n : Address) (s : σ) : UInt256 :=
  if E.chainTypeManager = 0 then E.keccak (corePre E s)
  else if n = 0 then E.keccak (ctmPre E s)
  else E.keccak (notifierPre E n s)

/-- The holder tuple `_domainHolders` hashes, unhashed (`:104-105`): one address in the `Core`
domain, four with a CTM and no notifier, seven with both. -/
def holderTuple (E : Env σ κ) (n : Address) (s : σ) : List Address :=
  if E.chainTypeManager = 0 then [E.paOwner s]
  else if n = 0 then
    [E.paOwner s, E.ownerOf s E.chainTypeManager, E.pendingOwnerOf s E.chainTypeManager,
      E.getProxyAdmin s E.chainTypeManager]
  else
    [E.paOwner s, E.ownerOf s E.chainTypeManager, E.pendingOwnerOf s E.chainTypeManager,
      E.getProxyAdmin s E.chainTypeManager, E.ownerOf s n, E.pendingOwnerOf s n,
      E.getProxyAdmin s n]

/-- A collision on the named preimages the holders check compares between `s` and `s'`: the
`Core` preimage; the CTM preimage; or, with a notifier, the notifier preimage or the CTM
preimage nested in it. -/
def HoldersBreak (E : Env σ κ) (n : Address) (s s' : σ) : Prop :=
  if E.chainTypeManager = 0 then Collides E.keccak (corePre E s) (corePre E s')
  else if n = 0 then Collides E.keccak (ctmPre E s) (ctmPre E s')
  else Collides E.keccak (notifierPre E n s) (notifierPre E n s') ∨
    Collides E.keccak (ctmPre E s) (ctmPre E s')

/-! ## The leg -/

/-- The context the executor builds (`:62-68`) from its own bindings. -/
def context (E : Env σ κ) (T : Address) (M : Manifest) (d : Domain) : Context :=
  ⟨T, M.proxyUpgradeEngine, d, E.proxyAdmin, E.chainTypeManager⟩

/-- The two requirements no countermodel deletes: the transition is code (`:54`) and
`toRows`' length check (`:93-96` with `libraries/ProxyUpgradeRowLib.sol:57-59`). -/
structure LegPre (E : Env σ κ) (T : Address) (M : Manifest) (d : Domain) (s : σ) : Prop where
  /-- `requireCode(address(_transition))` (`:54`). -/
  transitionCode : E.hasCode s T
  /-- `toRows`' length check (`libraries/ProxyUpgradeRowLib.sol:57-59`). -/
  inventoryLength : M.proxyUpgrades.length = inventoryLength d

/-- The leg's five checks, which the countermodels delete one at a time. -/
inductive Check
  /-- `manifest.domain == _domain` (`:56-58`). -/
  | domain
  /-- `requireCode(manifest.proxyUpgradeEngine)` (`:59-60`). -/
  | engineCode
  /-- Owner and pending owner unchanged (`:87-89`). -/
  | ownership
  /-- Domain holders' hash unchanged (`:90-92`). -/
  | holders
  /-- `requireRowsApplied` (`:97`). -/
  | rows
deriving DecidableEq

/-- What check `c` requires of a leg from `(st, s)` ending in `(st', s')`. -/
def Check.Holds (E : Env σ κ) (M : Manifest) (d : Domain) (st : Store) (s : σ) (st' : Store)
    (s' : σ) : Check → Prop
  | .domain => M.domain = d
  | .engineCode => E.hasCode s M.proxyUpgradeEngine
  | .ownership => st'.owner = st.owner ∧ st'.pendingOwner = st.pendingOwner
  | .holders => domainHolders E (notifierAt E s) s' = domainHolders E (notifierAt E s) s
  | .rows => RowsApplied (E.impl s') (toRows M.proxyUpgrades)

/-- Everything in the leg except the five checks: the two fixed requirements and the
delegatecall into the code at `manifest.proxyUpgradeEngine`, whose behaviour is `eng`. -/
def LegCore (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ) : Prop :=
  LegPre E T M d s ∧
    Delegate E eng M.proxyUpgradeEngine (context E T M d) M.proxyUpgrades st s st' s'

/-- A successful `_applyProxyUpgradeTransition(_proxyAdmin, T, d, _chainTypeManager)`
(`:48-98`) whose transition returned manifest `M` and whose engine behaves as `eng`. -/
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
another notifier contract `13`. Row proxy `5`, another proxy `6`; implementations `10`, `11`,
`12`. -/

/-- A concrete world: the implementation behind each proxy, the `ProxyAdmin`'s owner, each
`Ownable2Step` contract's owner and pending owner, each proxy's admin, and each CTM's
ServerNotifier. -/
structure WState where
  /-- `getProxyImplementation`. -/
  impl : Impl
  /-- `ProxyAdmin.owner()`. -/
  paOwner : Address
  /-- `IOwnable(x).owner()`. -/
  owner : Address → Address
  /-- `IOwnable(x).pendingOwner()`. -/
  pending : Address → Address
  /-- `ProxyAdmin.getProxyAdmin(x)`. -/
  admin : Address → Address
  /-- `IChainTypeManager(t).serverNotifierAddress()`. -/
  notifier : Address → Address

/-- Calls the executor (`1`) can send in the concrete world. -/
inductive WCall
  /-- `ProxyAdmin.upgrade(p, x)`. -/
  | upgrade (p x : Address)
  /-- `Ownable2Step(t).transferOwnership(x)`: nominates `x`. -/
  | transferOwnership (t x : Address)
  /-- `ChainTypeManager(t).setServerNotifier(x)`
  (`l1-contracts/contracts/state-transition/ChainTypeManager.sol:387-391`). -/
  | setServerNotifier (t x : Address)

/-- One successful executor-sent call in the concrete world. Each is `onlyOwner` on its
target, with the executor `1` as `msg.sender`; an upgrade needs code at the new implementation
(OpenZeppelin's `ERC1967Upgrade._setImplementation`). -/
inductive WStep (code : Address → Prop) : WState → WCall → WState → Prop
  | upgrade {s : WState} {p x : Address} : s.paOwner = 1 → code x →
      WStep code s (.upgrade p x) { s with impl := upd s.impl p x }
  | transferOwnership {s : WState} {t x : Address} : s.owner t = 1 →
      WStep code s (.transferOwnership t x) { s with pending := upd s.pending t x }
  | setServerNotifier {s : WState} {t x : Address} : s.owner t = 1 →
      WStep code s (.setServerNotifier t x) { s with notifier := upd s.notifier t x }

/-- The executor's environment in the concrete world: bound CTM `c` (`0` for the `Core`
executor), code predicate `code`, hash `k`. -/
def wEnvWith (c : Address) (code : Address → Prop) (k : List UInt8 → UInt256) :
    Env WState WCall where
  self := 1
  proxyAdmin := 2
  chainTypeManager := c
  hasCode := fun _ a => code a
  paOwner := WState.paOwner
  ownerOf := WState.owner
  pendingOwnerOf := WState.pending
  getProxyAdmin := WState.admin
  serverNotifierAddress := fun s => s.notifier c
  impl := WState.impl
  keccak := k
  call := WStep code

/-- The row configuration `applyRows` runs under inside an engine: the executor `1`, the
`ProxyAdmin`'s owner in `s`, inert reinitializers. -/
def rowConfig (code : Address → Prop) (s : WState) : ProxyUpgradeCurrent.Config where
  self := 1
  adminOwner := s.paOwner
  hasCode := code
  reinit := fun _ I => I

/-- The `ProxyAdmin` calls `applyRows`' first loop sends
(`libraries/ProxyUpgradeRowLib.sol:104-121`): nothing for a row already at `implNew`, else
`upgrade`. -/
def rowCalls : Impl → List Row → List WCall
  | _, [] => []
  | I, r :: rs =>
      if I r.proxy = r.implNew then rowCalls I rs
      else .upgrade r.proxy r.implNew :: rowCalls (upd I r.proxy r.implNew) rs

/-- `DefaultProxyUpgradeEngine.executeUpgrade` (`engines/DefaultProxyUpgradeEngine.sol:32-46`)
in a subclass whose `_afterSwaps` writes executor storage by `write` and sends the follow-up
calls `after`; `_beforeSwaps` and `_checkPostconditions` are empty. In order: the `ProxyAdmin`
owner check (`:33-37`), `toRows`' length check and `applyRows` with its own
`requireRowsApplied` (`:40-43`, `libraries/ProxyUpgradeRowLib.sol:122`), then the hook
(`:44`). -/
def engineWith (code : Address → Prop) (write : Store → Store) (after : List WCall) :
    Engine WState WCall :=
  fun ctx inv st s st' calls =>
    s.paOwner = 1 ∧ inv.length = inventoryLength ctx.domain ∧
      (∃ J, ProxyUpgradeCurrent.ApplyRows (rowConfig code s) s.impl (toRows inv) J) ∧
      st' = write st ∧ calls = rowCalls s.impl (toRows inv) ++ after

/-- `DefaultProxyUpgradeEngine` itself: empty hooks (`:51`, `:56`, `:62-65`). -/
def defaultEngineWith (code : Address → Prop) : Engine WState WCall := engineWith code id []

/-! ## Witness data -/

/-- Every address has code. -/
def allCode : Address → Prop := fun _ => True

/-- `DefaultProxyUpgradeEngine` where every address has code. -/
def defaultEngine : Engine WState WCall := defaultEngineWith allCode

/-- The preimage of the CTM hash in `w0`. -/
def ctmPre0 : List UInt8 := abiEncode [1, 1, 0, 2]

/-- The notifier preimage in `w0` once the CTM hash is `100`. -/
def notifierPre0 : List UInt8 := abiEncode [100, 1, 0, 2]

/-- A toy hash: `100` on `ctmPre0`, `200` on `notifierPre0`, `0` on everything else. -/
def wKeccak (b : List UInt8) : UInt256 :=
  if b = ctmPre0 then 100 else if b = notifierPre0 then 200 else 0

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
proxy; every CTM's notifier is `9`. -/
def w0 : WState where
  impl := fun _ => 10
  paOwner := 1
  owner := fun a => if a = 13 then 6 else 1
  pending := fun _ => 0
  admin := fun _ => 2
  notifier := fun _ => 9

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

end Contracts.EngineLegV35
