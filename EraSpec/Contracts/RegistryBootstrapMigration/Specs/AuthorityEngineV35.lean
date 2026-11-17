import EraSpec.Contracts.RegistryBootstrapMigration.Specs.Forward

/-!
# Model: engine legs on the authority state (draft/v0.35.0)

Source: era-contracts `draft/v0.35.0` at commit `d9f678900e1bc8286412b78f56d4a9f443983c29`
(`d9` below). Paths are relative to `l1-contracts/contracts/`; every `file:line` in this file
is at `d9`. `Specs/Authority.lean` and `Specs/Forward.lean` were written at `e561b9cc2`.
Between the two commits, `RegistryBootstrapMigration.migrate()` (:262-304),
`RegistryAuthorityLib` and `UpgradeExecutorBase.forward` do the same thing. The only
`RegistryBootstrapMigration` edit renames `upgradeEngine` to `chainUpgradeEngine` in
reject-only checks (:68, :173). So `MigrateStep` and `OpStep` are reused unchanged, and the
line numbers they quote for `migrate()` are the same at `d9`. What `d9` adds is a second
transaction kind, the **engine leg**.

**This file is definitions only.** The results are in
`EraSpec.Contracts.RegistryBootstrapMigration.Properties.AuthorityEngineV35` and are proved
in `EraSpec.Contracts.RegistryBootstrapMigration.Proofs.AuthorityEngineV35`.

## The engine leg (`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:48-98`)

Both domain executors reach it from one owner-only entry point:
`CTMUpgradeExecutor.applyInfrastructureUpgrade` (`upgrades/registry/executors/CTMUpgradeExecutor.sol:64-72`,
domain `CTM`, bound CTM) and `CoreUpgradeExecutor.applyL1Upgrade`
(`upgrades/registry/executors/CoreUpgradeExecutor.sol:33-36`, domain `Core`, CTM zero). The leg:

    address ownerBefore = owner();                                                  // :69
    address pendingOwnerBefore = pendingOwner();                                    // :70
    address serverNotifier = _chainTypeManager == address(0)
        ? address(0) : IChainTypeManager(_chainTypeManager).serverNotifierAddress(); // :71-73
    bytes32 domainHoldersBefore = _domainHolders(_proxyAdmin, _chainTypeManager, serverNotifier); // :74
    (bool success, bytes memory returnData) = manifest.proxyUpgradeEngine.delegatecall(
        abi.encodeCall(IProxyUpgradeEngine.executeUpgrade, (context, manifest.proxyUpgrades))); // :76-78
    if (!success) { ... revert ... }                                                // :79-85
    if (owner() != ownerBefore || pendingOwner() != pendingOwnerBefore) {
        revert ProxyUpgradeEngineChangedExecutorOwnership(...); }                   // :87-89
    if (_domainHolders(_proxyAdmin, _chainTypeManager, serverNotifier) != domainHoldersBefore) {
        revert ProxyUpgradeEngineMovedDomainAuthority(...); }                       // :90-92
    ProxyUpgradeRowLib.requireRowsApplied(_proxyAdmin, rows);                       // :93-97

`_domainHolders` (:109-139) is `keccak256(abi.encode(_proxyAdmin.owner()))` in the `Core`
domain (:114-116). In the `CTM` domain it hashes:
* the `ProxyAdmin`'s owner, and the CTM's `owner()`, `pendingOwner()` and proxy admin
  (:118-125);
* then, with the notifier, the notifier's `owner()`, `pendingOwner()` and proxy admin
  (:129-138).

The engine runs with the executor's address and storage. `engines/IProxyUpgradeEngine.sol:10-18`
says the engine "acts with the executor's authority" and that "every storage slot is the
executor's". So it can make any call the executor can make, and it can write the executor's
own `Ownable2Step` slots directly.

The checks at :87-92 compare **end values with start values** only:
* the executor's own owner and nominee are compared exactly;
* the domain's holders are compared through a hash.

A collision of that hash on the logged `(before, after)` pair is the only way a leg can leave
different holders.

`docs/registry-driven-upgrades.md:257-268` (from the repository root) states the check: "a hook
cannot transfer or nominate those holders through their setters, nor move those proxies with
`changeProxyAdmin`; a succession is a `forward`". It also states what the check does not see:
"The check compares what those getters return, and rows: a hook that swaps the implementation
of, or `upgradeAndCall`s into, a proxy that is not a row (the CTM and the ServerNotifier
included) can change what they return". And :449-453: "every `forward` cell below holds for it
too, except the last row: the executor's post-check refuses an ownership move".

## The bootstrap runs a core leg (`upgrades/registry/bootstrap/RegistryBootstrapSequence.sol:88-105`)

    actions_[offset] = BootstrapAction({
        label: "hand the ecosystem ProxyAdmin to the bound core executor",
        authority: "ecosystem ProxyAdmin owner (governance)",
        call: Call({ target: address(coreExecutor.PROXY_ADMIN()), value: 0,
                     data: abi.encodeCall(Ownable.transferOwnership, (address(coreExecutor))) }) }); // :88-96
    actions_[offset + 1] = BootstrapAction({
        label: "apply the pinned ecosystem inventory (applyL1Upgrade)",
        authority: "core executor owner (governance)",
        call: Call({ target: address(coreExecutor), value: 0,
                     data: abi.encodeCall(CoreUpgradeExecutor.applyL1Upgrade,
                                          (IProxyUpgradeTransition(CORE_TRANSITION))) }) });    // :97-105

So the governance bundle itself contains a core-domain engine leg. It runs before the CTM
nomination (:106-110) and `migrate()` (:120-124). The core leg's hash covers only the
ecosystem `ProxyAdmin`'s owner, and nothing in the leg checks the CTM domain. The CTM domain
is kept because the core executor holds none of its authority (`OtherDomainQuiet`).

## The executor's entry points, called by the engine itself

During the delegatecall, a call from the engine back into the executor has the executor
itself as `msg.sender`. The gates (`ExecEntry.GatePasses`):

* `forward` (`governance/UpgradeExecutorBase.sol:34`), `applyInfrastructureUpgrade`
  (`CTMUpgradeExecutor.sol:64`), `applyCTMUpgrade` (:77), `applyL1Upgrade`
  (`CoreUpgradeExecutor.sol:33`) and `transferOwnership` are `onlyOwner`;
* `upgradeChain` (`CTMUpgradeExecutor.sol:92-95`) takes the owner or the chain's admin;
* `acceptCTMOwnership` (`CTMUpgradeExecutor.sol:55-61`) takes the owner or the CTM's owner;
* `acceptOwnership` takes the nominee (OpenZeppelin `Ownable2Step`);
* `renounceOwnership` always reverts (`UpgradeExecutorBase.sol:50-55`).

`receive()` (`UpgradeExecutorBase.sol:59`) takes ETH from anyone and writes no storage; it is
not listed.

## Modelling choices

* **`VState` extends `AState`** with:
  * the executors' `owner` and `pendingOwner`, and the ecosystem `ProxyAdmin`'s owner;
  * the CTM's proxy admin. It is fixed: no step writes it. `Forward` likewise does not model
    `changeProxyAdmin` on the CTM proxy;
  * what the CTM's code answers to `owner()` and `pendingOwner()`;
  * the ServerNotifier's owner, nominee and proxy admin, and whether the CTM names a notifier
    at all (`hasNotifier`). With none, `_domainHolders` returns the four-entry hash (:126-128).
* **A transaction is a call trace** (`VCall`, `VRun`), as in `Forward`: each call has its own
  `msg.sender`. A trace may hold `Forward`'s ops (`VOp.fwd`) and the writers of the new
  fields. A revert is the absence of a step.
* **The executor's own slots** are written by `VOp.execSlots`. Only code running in that
  executor's storage can do that, which is the engine during that executor's leg (`ctx`). The
  executors make no other delegatecall (`UpgradeExecutorBase.sol:17-19`;
  `CTMUpgradeExecutor.sol:24-25`; `CoreUpgradeExecutor.sol:18-19`).
* **A CTM code swap** (`VOp.ctmCodeSwap`) is `Forward`'s `Op.ctmCodeSwap`, plus how the new
  code answers the ownership reads: `none` means from its `Ownable2Step` slots, `some (o, p)`
  means fixed answers. `_domainHolders` reads the answers (`VState.ctmRead`). Parking is about
  the slots.
* **`holdersHash` is an arbitrary function** `Holders → UInt256`. No injectivity premise is
  made anywhere. Each result carries a collision on the leg's own logged pair as a disjunct
  (`Collides`), and `CollisionDisjunctNeeded` shows that the disjunct is load-bearing.
  `_domainHolders` nests two `keccak256` calls (:118-125 inside :130-138). `holdersHash` is
  their composition, so a collision of `holdersHash` is a collision of one of the two.
* **Over-approximations**, which only add runs:
  * the leg needs no owner as its outer sender;
  * the rows check (:93-97) and the code checks are omitted;
  * a notifier proxy-admin query that would revert (:106-108) is read as the field's value.
* **Fixed configuration**, as in `Specs/Authority.lean`:
  * `migrate()` reads the executors' getters from `Config.exec`, not from the live `VState`
    fields;
  * which notifier the CTM names. A leg reads `serverNotifierAddress()` once, before the engine
    runs (:71-73), and compares that notifier before and after. `setServerNotifier`
    (`state-transition/ChainTypeManager.sol:387-391`) is not modelled, so the notifier fields
    describe one notifier throughout.
* **Not modelled.**
  * `ProxyAdmin.changeProxyAdmin` on the CTM proxy: `VState.ctmAdmin` has no writer, as in
    `Forward`. At `d9` a leg that moves the CTM proxy's admin makes `getProxyAdmin` return the
    CTM's own `admin()` (:106-108, `ChainTypeManager.sol:113`), so the comparison fails unless
    that answer is the `ProxyAdmin`'s address.
  * A leg nested inside another domain's leg. The inner leg's entry point is `onlyOwner`, so
    it needs a call sent by the other executor's owner; `OtherDomainQuiet` excludes those
    calls where it is assumed. A nested leg of the same domain only adds checks.
  * ETH, events, and the executors' `upgradeChain`/`applyCTMUpgrade` bodies (calls they make
    are calls of the trace).
-/

namespace Contracts.RegistryBootstrapMigration

open Clear

/-! ## Domains and the extended state -/

/-- The two registry executors that apply a `ProxyUpgradeTransition` through an engine. -/
inductive Domain
  /-- `CoreUpgradeExecutor`, bound to the ecosystem `ProxyAdmin`. -/
  | core
  /-- `CTMUpgradeExecutor`, bound to the CTM and the CTM-domain `ProxyAdmin`. -/
  | ctm
deriving DecidableEq

/-- The executor of a domain: the manifest's `coreExecutor` or `ctmExecutor`. -/
def Domain.executor (K : Config) : Domain → Address
  | .core => K.m.core
  | .ctm => K.m.E

/-- The authority state, with the executors, the ecosystem `ProxyAdmin` and the notifier. -/
structure VState where
  /-- The state of `Specs/Authority.lean`: the CTM's slots, the CTM-domain `ProxyAdmin`'s owner,
  the migration's `executed`. -/
  a : AState
  /-- The CTM executor's `owner()`. -/
  eOwner : Address
  /-- The CTM executor's `pendingOwner()`. -/
  ePending : Address
  /-- The core executor's `owner()`. -/
  cOwner : Address
  /-- The core executor's `pendingOwner()`. -/
  cPending : Address
  /-- The ecosystem `ProxyAdmin`'s `owner()` (the core executor's `PROXY_ADMIN()`). -/
  ecoOwner : Address
  /-- `ctmProxyAdmin.getProxyAdmin(ctm)` (`ProxyUpgradeExecutorBase.sol:123`). No step writes it. -/
  ctmAdmin : Address
  /-- How the CTM's code answers `owner()` and `pendingOwner()`: `none` from its `Ownable2Step`
  slots (`a.ctmOwner`, `a.ctmPending`), `some (o, p)` with fixed answers. -/
  ctmAnswers : Option (Address × Address)
  /-- The ServerNotifier's `owner()` (`governance/ServerNotifier.sol:28`, `Ownable2Step`). -/
  nOwner : Address
  /-- The ServerNotifier's `pendingOwner()`. -/
  nPending : Address
  /-- `ctmProxyAdmin.getProxyAdmin(serverNotifier)` (`ProxyUpgradeExecutorBase.sol:136`). -/
  nAdmin : Address
  /-- The CTM's `serverNotifierAddress()` is nonzero (`ProxyUpgradeExecutorBase.sol:71-73`,
  `:126-128`). No step writes it. -/
  hasNotifier : Bool
deriving DecidableEq

/-- A domain executor's `owner()`. -/
def VState.execOwner (s : VState) : Domain → Address
  | .core => s.cOwner
  | .ctm => s.eOwner

/-- A domain executor's `pendingOwner()`. -/
def VState.execPending (s : VState) : Domain → Address
  | .core => s.cPending
  | .ctm => s.ePending

/-- Write a domain executor's owner and nominee. -/
def VState.setExec (s : VState) : Domain → Address → Address → VState
  | .core, o, p => { s with cOwner := o, cPending := p }
  | .ctm, o, p => { s with eOwner := o, ePending := p }

/-- What the CTM answers to `owner()` and `pendingOwner()`. -/
def VState.ctmRead (s : VState) : Address × Address :=
  s.ctmAnswers.getD (s.a.ctmOwner, s.a.ctmPending)

/-! ## Calls -/

/-- An entry point that writes a tracked slot. -/
inductive VOp
  /-- One of `Forward`'s ops other than its CTM code swap: `Op.ctmCodeSwap` has no `fwd` step,
  and is `VOp.ctmCodeSwap` instead. -/
  | fwd (op : Op)
  /-- `ProxyAdmin.upgrade`/`upgradeAndCall` on the CTM proxy. The CTM's owner, nominee, version
  and release become `o`, `p`, `v`, `r`, and its new code answers the ownership reads as
  `answers` says (`none`: from those slots). -/
  | ctmCodeSwap (o p : Address) (v : ℕ) (r : Address) (answers : Option (Address × Address))
  /-- The executor's `transferOwnership(x)` (OpenZeppelin `Ownable2Step`, `onlyOwner`). -/
  | execTransferOwnership (d : Domain) (x : Address)
  /-- The executor's `acceptOwnership()`. -/
  | execAcceptOwnership (d : Domain)
  /-- The executor's `renounceOwnership()`, which always reverts
  (`UpgradeExecutorBase.sol:50-55`): it has no step. -/
  | execRenounceOwnership (d : Domain)
  /-- Code running in the executor's storage writes its `Ownable2Step` slots directly. -/
  | execSlots (d : Domain) (o p : Address)
  /-- The ecosystem `ProxyAdmin`'s `transferOwnership(x)` (`Ownable`, `x ≠ 0`). -/
  | ecoTransferOwnership (x : Address)
  /-- The ecosystem `ProxyAdmin`'s `renounceOwnership()`. -/
  | ecoRenounceOwnership
  /-- The notifier's `transferOwnership(x)`. -/
  | notifierTransferOwnership (x : Address)
  /-- The notifier's `acceptOwnership()`. -/
  | notifierAcceptOwnership
  /-- The notifier's `renounceOwnership()` (`ServerNotifier` does not override it). -/
  | notifierRenounceOwnership
  /-- Moving the notifier proxy's admin to `x`: `ProxyAdmin.changeProxyAdmin`, or `changeAdmin`
  by an admin that is not the `ProxyAdmin`. -/
  | notifierChangeAdmin (x : Address)
  /-- Replacing the notifier's code; the new code answers the ownership reads with `o`, `p`. -/
  | notifierCodeSwap (o p : Address)
deriving DecidableEq

/-- One call: its `msg.sender` and its entry point. -/
structure VCall where
  /-- `msg.sender`. -/
  sender : Address
  /-- The entry point. -/
  op : VOp
deriving DecidableEq

/-- Who may act on the notifier proxy: the CTM-domain `ProxyAdmin`'s owner while that
`ProxyAdmin` is its admin, otherwise its admin itself. -/
def NotifierAdminAuth (K : Config) (s : VState) (a : Address) : Prop :=
  (s.nAdmin = K.m.pa ∧ s.a.paOwner = a) ∨ (s.nAdmin ≠ K.m.pa ∧ s.nAdmin = a)

/-- One successful call by `a`. `ctx` is the executor whose storage the running code shares:
`some d` during domain `d`'s engine leg, `none` otherwise. -/
inductive VOpStep (K : Config) (ctx : Option Domain) (a : Address) : VState → VOp → VState → Prop
  /-- `Forward`'s call, on `AState`. -/
  | fwd {s : VState} {op : Op} {t : AState} :
      OpStep K a s.a op t → ¬ op.swapsCtmCode → VOpStep K ctx a s (.fwd op) { s with a := t }
  /-- `onlyOwner` on the `ProxyAdmin` (`OZ/proxy/transparent/ProxyAdmin.sol:62-64, 74-80`), which
  must administer the CTM proxy. -/
  | ctmCodeSwap {s : VState} {o p : Address} {v : ℕ} {r : Address}
      {ans : Option (Address × Address)} :
      s.a.paOwner = a → s.ctmAdmin = K.m.pa →
      VOpStep K ctx a s (.ctmCodeSwap o p v r ans)
        { s with a := { s.a with ctmOwner := o, ctmPending := p, ctmPv := v, ctmRel := r },
                 ctmAnswers := ans }
  /-- `onlyOwner`, then the nomination is `x`. -/
  | execTransferOwnership {s : VState} {d : Domain} {x : Address} :
      s.execOwner d = a →
      VOpStep K ctx a s (.execTransferOwnership d x) (s.setExec d (s.execOwner d) x)
  /-- `pendingOwner() == msg.sender`, then the caller owns it and the nomination is deleted. -/
  | execAcceptOwnership {s : VState} {d : Domain} :
      s.execPending d = a → VOpStep K ctx a s (.execAcceptOwnership d) (s.setExec d a 0)
  /-- Only the code delegatecalled into executor `d`, as `d`. -/
  | execSlots {s : VState} {d : Domain} {o p : Address} :
      ctx = some d → a = d.executor K → VOpStep K ctx a s (.execSlots d o p) (s.setExec d o p)
  /-- `onlyOwner` and `x ≠ 0` (`OZ/access/Ownable.sol:69-72`). -/
  | ecoTransferOwnership {s : VState} {x : Address} :
      s.ecoOwner = a → x ≠ 0 → VOpStep K ctx a s (.ecoTransferOwnership x) { s with ecoOwner := x }
  /-- `onlyOwner` (`OZ/access/Ownable.sol:61-63`). -/
  | ecoRenounceOwnership {s : VState} :
      s.ecoOwner = a → VOpStep K ctx a s .ecoRenounceOwnership { s with ecoOwner := 0 }
  /-- `onlyOwner`, then the nomination is `x`. -/
  | notifierTransferOwnership {s : VState} {x : Address} :
      s.nOwner = a → VOpStep K ctx a s (.notifierTransferOwnership x) { s with nPending := x }
  /-- The nominee accepts. -/
  | notifierAcceptOwnership {s : VState} :
      s.nPending = a →
      VOpStep K ctx a s .notifierAcceptOwnership { s with nOwner := a, nPending := 0 }
  /-- `onlyOwner`, then no owner and no nominee. -/
  | notifierRenounceOwnership {s : VState} :
      s.nOwner = a →
      VOpStep K ctx a s .notifierRenounceOwnership { s with nOwner := 0, nPending := 0 }
  /-- The proxy's admin moves (OpenZeppelin v4 `_changeAdmin` rejects zero). -/
  | notifierChangeAdmin {s : VState} {x : Address} :
      NotifierAdminAuth K s a → x ≠ 0 →
      VOpStep K ctx a s (.notifierChangeAdmin x) { s with nAdmin := x }
  /-- The notifier's code is replaced. -/
  | notifierCodeSwap {s : VState} {o p : Address} :
      NotifierAdminAuth K s a →
      VOpStep K ctx a s (.notifierCodeSwap o p) { s with nOwner := o, nPending := p }

/-- A call trace, in execution order; a failing call reverts them all. -/
inductive VRun (K : Config) (ctx : Option Domain) : VState → List VCall → VState → Prop
  | nil {s : VState} : VRun K ctx s [] s
  | cons {s s' s'' : VState} {c : VCall} {cs : List VCall} :
      VOpStep K ctx c.sender s c.op s' → VRun K ctx s' cs s'' → VRun K ctx s (c :: cs) s''

/-! ## The domain holders and the leg -/

/-- What `_domainHolders` (`ProxyUpgradeExecutorBase.sol:109-139`) encodes before hashing. -/
inductive Holders
  /-- `abi.encode(_proxyAdmin.owner())` (:115). -/
  | core (ecoOwner : Address)
  /-- The CTM domain's tuple: the `ProxyAdmin`'s owner and the CTM's owner, nominee and proxy
  admin (:118-125); then, if the CTM names a notifier, the notifier's owner, nominee and proxy
  admin (:126-138). -/
  | ctm (paOwner ctmOwner ctmPending ctmAdmin : Address)
      (notifier : Option (Address × Address × Address))
deriving DecidableEq

/-- The holders a domain's leg logs. The CTM's entries are what its code answers. -/
def VState.holders (s : VState) : Domain → Holders
  | .core => .core s.ecoOwner
  | .ctm => .ctm s.a.paOwner s.ctmRead.1 s.ctmRead.2 s.ctmAdmin
      (if s.hasNotifier then some (s.nOwner, s.nPending, s.nAdmin) else none)

/-- `holdersHash` collides on a logged pair: the tuples differ, the hashes agree. -/
def Collides (H : Holders → UInt256) (h h' : Holders) : Prop :=
  h ≠ h' ∧ H h = H h'

/-- **One successful engine leg** of domain `d` with call trace `cs`. The trace runs in `d`'s
executor's storage (`:76-85`). The executor's owner and nominee are as before (`:87-89`), and
the hash of the holders is as before (`:90-92`). `H` is `holdersHash`, an arbitrary function. -/
inductive EngineLeg (K : Config) (H : Holders → UInt256) (d : Domain) :
    VState → List VCall → VState → Prop
  | mk {s s' : VState} {cs : List VCall} :
      VRun K (some d) s cs s' →
      s'.execOwner d = s.execOwner d → s'.execPending d = s.execPending d →
      H (s'.holders d) = H (s.holders d) →
      EngineLeg K H d s cs s'

/-- The leg without the holders check at `:90-92`, for the countermodel. -/
inductive EngineLegNoHolderCheck (K : Config) (d : Domain) : VState → List VCall → VState → Prop
  | mk {s s' : VState} {cs : List VCall} :
      VRun K (some d) s cs s' →
      s'.execOwner d = s.execOwner d → s'.execPending d = s.execPending d →
      EngineLegNoHolderCheck K d s cs s'

/-! ## Projections and premises -/

/-- The `Forward` op a call is, if any. -/
def VOp.toOp : VOp → Option Op
  | .fwd op => some op
  | .ctmCodeSwap o p v r _ => some (.ctmCodeSwap o p v r)
  | _ => none

/-- The `Forward` call a call is, if any. -/
def VCall.toCall (c : VCall) : Option Call :=
  c.op.toOp.map fun op => ⟨c.sender, op⟩

/-- The calls of a trace that `Forward` models, in order. -/
def VCall.project (cs : List VCall) : List Call :=
  cs.filterMap VCall.toCall

/-- The call hands authority to the migration by an ownership call (`Op.handsToMigration`). -/
def VOp.handsToMigration (K : Config) : VOp → Prop
  | .fwd op => op.handsToMigration K
  | _ => False

/-- The call replaces the CTM's code. -/
def VOp.swapsCtmCode : VOp → Prop
  | .fwd op => op.swapsCtmCode
  | .ctmCodeSwap _ _ _ _ _ => True
  | _ => False

/-- The call replaces the CTM's code with code that does not answer the ownership reads from
its slots. -/
def VOp.answersFalsely : VOp → Prop
  | .ctmCodeSwap _ _ _ _ (some _) => True
  | _ => False

/-- The other domain's holders send no call in the trace, and a core leg makes no `migrate()`
call. The holders are taken at the start of the leg.
* For a CTM leg: the ecosystem `ProxyAdmin`'s owner, and the core executor's owner and nominee.
* For a core leg: the CTM's owner and nominee, the CTM-domain `ProxyAdmin`'s owner, and the CTM
  executor's owner and nominee. -/
def OtherDomainQuiet (d : Domain) (s : VState) (cs : List VCall) : Prop :=
  match d with
  | .ctm => ∀ c ∈ cs, c.sender ≠ s.ecoOwner ∧ c.sender ≠ s.cOwner ∧ c.sender ≠ s.cPending
  | .core => ∀ c ∈ cs, c.sender ≠ s.a.ctmOwner ∧ c.sender ≠ s.a.ctmPending ∧
      c.sender ≠ s.a.paOwner ∧ c.sender ≠ s.eOwner ∧ c.sender ≠ s.ePending ∧ c.op ≠ .fwd .migrate

/-- The slots a leg's own checks cover, unchanged.
* CTM leg: the CTM's owner and nominee, the CTM-domain `ProxyAdmin`'s owner, and the CTM
  executor's owner and nominee.
* Core leg: the ecosystem `ProxyAdmin`'s owner, and the core executor's owner and nominee. -/
def OwnFrame : Domain → VState → VState → Prop
  | .ctm, s, s' => s'.a.ctmOwner = s.a.ctmOwner ∧ s'.a.ctmPending = s.a.ctmPending ∧
      s'.a.paOwner = s.a.paOwner ∧ s'.eOwner = s.eOwner ∧ s'.ePending = s.ePending
  | .core, s, s' => s'.ecoOwner = s.ecoOwner ∧ s'.cOwner = s.cOwner ∧ s'.cPending = s.cPending

/-- The other domain's slots, unchanged. For a core leg this includes the migration's
`executed`. -/
def OtherFrame : Domain → VState → VState → Prop
  | .ctm, s, s' => s'.ecoOwner = s.ecoOwner ∧ s'.cOwner = s.cOwner ∧ s'.cPending = s.cPending
  | .core, s, s' => s'.a.ctmOwner = s.a.ctmOwner ∧ s'.a.ctmPending = s.a.ctmPending ∧
      s'.a.paOwner = s.a.paOwner ∧ s'.eOwner = s.eOwner ∧ s'.ePending = s.ePending ∧
      s'.a.executed = s.a.executed

/-- The authority slots of this topic, all unchanged: the CTM's owner and nominee, both
`ProxyAdmin`s' owners, and both executors' owner and nominee. -/
def AuthFrame (s s' : VState) : Prop :=
  s'.a.ctmOwner = s.a.ctmOwner ∧ s'.a.ctmPending = s.a.ctmPending ∧
    s'.a.paOwner = s.a.paOwner ∧ s'.ecoOwner = s.ecoOwner ∧
    s'.eOwner = s.eOwner ∧ s'.ePending = s.ePending ∧ s'.cOwner = s.cOwner ∧ s'.cPending = s.cPending

/-! ## Runs with engine legs -/

/-- A transaction. -/
inductive VLabel
  /-- One of `Specs/Authority.lean`'s transactions; the new fields are untouched. -/
  | tx (l : Label)
  /-- Any transaction without a delegatecall into an executor (a `forward`, a direct call), as
  its call trace. -/
  | call (cs : List VCall)
  /-- An engine leg of domain `d`, as its call trace. -/
  | engineLeg (d : Domain) (cs : List VCall)

/-- One successful transaction. -/
inductive VSysStep (K : Config) (H : Holders → UInt256) : VState → VLabel → VState → Prop
  | tx {s : VState} {l : Label} {t : AState} :
      AStep K s.a l t → VSysStep K H s (.tx l) { s with a := t }
  | call {s s' : VState} {cs : List VCall} : VRun K none s cs s' → VSysStep K H s (.call cs) s'
  | engineLeg {s s' : VState} {d : Domain} {cs : List VCall} :
      EngineLeg K H d s cs s' → VSysStep K H s (.engineLeg d cs) s'

/-- A sequence of successful transactions. -/
inductive VSysRun (K : Config) (H : Holders → UInt256) : VState → List VLabel → VState → Prop
  | nil {s : VState} : VSysRun K H s [] s
  | cons {s s' s'' : VState} {v : VLabel} {vs : List VLabel} :
      VSysStep K H s v s' → VSysRun K H s' vs s'' → VSysRun K H s (v :: vs) s''

/-- The premises of the re-parking results, per transaction.
* A model transaction, a call trace, or a core leg hands nothing to the migration by an
  ownership call and does not replace the CTM's code.
* A CTM leg may do anything except leave the CTM running code that answers the ownership
  reads falsely. -/
def VLabel.Clean (K : Config) : VLabel → Prop
  | .tx l => ¬ l.handsToMigration K
  | .call cs => ∀ c ∈ cs, ¬ c.op.handsToMigration K ∧ ¬ c.op.swapsCtmCode
  | .engineLeg .core cs => ∀ c ∈ cs, ¬ c.op.handsToMigration K ∧ ¬ c.op.swapsCtmCode
  | .engineLeg .ctm cs => ∀ c ∈ cs, ¬ c.op.answersFalsely

/-- No call of the transaction is sent by the zero address. -/
def VLabel.SendersNonzero : VLabel → Prop
  | .tx _ => True
  | .call cs => ∀ c ∈ cs, c.sender ≠ 0
  | .engineLeg _ cs => ∀ c ∈ cs, c.sender ≠ 0

/-! ## The executor's constructor and entry points -/

/-- `UpgradeExecutorBase`'s constructor (`governance/UpgradeExecutorBase.sol:24-31`). It
reverts on a zero `_initialOwner` (:27-29); otherwise the owner is `_initialOwner` and there
is no nominee. Arguments: initial owner, resulting owner, resulting nominee. -/
inductive ExecConstructed : Address → Address → Address → Prop
  | mk {o : Address} : o ≠ 0 → ExecConstructed o o 0

/-- The external entry points of the two executors that are not `view`. -/
inductive ExecEntry
  /-- `UpgradeExecutorBase.forward` (:34). -/
  | forward
  /-- `CTMUpgradeExecutor.applyInfrastructureUpgrade` (:64). -/
  | applyInfrastructureUpgrade
  /-- `CTMUpgradeExecutor.applyCTMUpgrade` (:77). -/
  | applyCTMUpgrade
  /-- `CoreUpgradeExecutor.applyL1Upgrade` (:33). -/
  | applyL1Upgrade
  /-- `CTMUpgradeExecutor.upgradeChain(_, chainId)` (:92). -/
  | upgradeChain (chainId : ℕ)
  /-- `CTMUpgradeExecutor.acceptCTMOwnership` (:55). -/
  | acceptCTMOwnership
  /-- `Ownable2Step.transferOwnership(x)`. -/
  | transferOwnership (x : Address)
  /-- `Ownable2Step.acceptOwnership()`. -/
  | acceptOwnership
  /-- `UpgradeExecutorBase.renounceOwnership` (:53). -/
  | renounceOwnership
deriving DecidableEq

/-- Which executor declares the entry point. -/
def Domain.Declares : Domain → ExecEntry → Prop
  | .ctm, .applyL1Upgrade => False
  | .core, .applyInfrastructureUpgrade => False
  | .core, .applyCTMUpgrade => False
  | .core, .upgradeChain _ => False
  | .core, .acceptCTMOwnership => False
  | _, _ => True

/-- What a gate reads when it runs: the executor's owner and nominee, the CTM's answer to
`owner()`, and the CTM's `getChainAdmin`. -/
structure GateView where
  /-- The executor's `owner()`. -/
  owner : Address
  /-- The executor's `pendingOwner()`. -/
  pending : Address
  /-- `ctm.owner()`. -/
  ctmOwner : Address
  /-- `CHAIN_TYPE_MANAGER.getChainAdmin(chainId)`. -/
  chainAdmin : ℕ → Address

/-- The gate a domain executor's entry point applies, read from the state. -/
def VState.gateView (s : VState) (d : Domain) (chainAdmin : ℕ → Address) : GateView :=
  ⟨s.execOwner d, s.execPending d, s.ctmRead.1, chainAdmin⟩

/-- The caller check of an entry point passes for `sender`:
* `onlyOwner`: `forward` (`UpgradeExecutorBase.sol:34`), `applyInfrastructureUpgrade`
  (`CTMUpgradeExecutor.sol:64`), `applyCTMUpgrade` (:77), `applyL1Upgrade`
  (`CoreUpgradeExecutor.sol:33`), `transferOwnership`;
* `upgradeChain`: the owner or the chain's admin (`CTMUpgradeExecutor.sol:93-95`);
* `acceptCTMOwnership`: the owner or the CTM's owner (`CTMUpgradeExecutor.sol:57-59`);
* `acceptOwnership`: the nominee;
* `renounceOwnership`: never (`UpgradeExecutorBase.sol:53-55`). -/
def ExecEntry.GatePasses (g : GateView) (sender : Address) : ExecEntry → Prop
  | .forward => sender = g.owner
  | .applyInfrastructureUpgrade => sender = g.owner
  | .applyCTMUpgrade => sender = g.owner
  | .applyL1Upgrade => sender = g.owner
  | .upgradeChain id => sender = g.owner ∨ sender = g.chainAdmin id
  | .acceptCTMOwnership => sender = g.owner ∨ sender = g.ctmOwner
  | .transferOwnership _ => sender = g.owner
  | .acceptOwnership => sender = g.pending
  | .renounceOwnership => False

/-! ## Witness data

The configuration of `Specs/Authority.lean`'s witnesses: migration `50`, CTM `1`, CTM-domain
`ProxyAdmin` `2`, CTM executor `3`, core executor `4`, governance `9`. The core executor owns
the ecosystem `ProxyAdmin`, and the CTM executor owns the notifier. The CTM-domain
`ProxyAdmin` administers the CTM and notifier proxies. Address `7` is another account. -/

/-- After the witness bundle (`wPost`): governance `9` owns both executors, the core executor
`4` owns the ecosystem `ProxyAdmin`, the CTM executor `3` owns the notifier, and the CTM-domain
`ProxyAdmin` `2` administers the CTM and notifier proxies. -/
def wPostV : VState where
  a := wPost
  eOwner := 9
  ePending := 0
  cOwner := 9
  cPending := 0
  ecoOwner := 4
  ctmAdmin := 2
  ctmAnswers := none
  nOwner := 3
  nPending := 0
  nAdmin := 2
  hasNotifier := true

/-- After the non-genuine executor's `migrate()` (`wParked`). -/
def wParkedV : VState := { wPostV with a := wParked }

/-- `wParkedV` after executor `3` accepts the CTM. -/
def wRecoveredV : VState := { wPostV with a := ⟨3, 0, 3, 35, 60, true⟩ }

/-- `wPostV` after the CTM-domain `ProxyAdmin` moves to `7`. -/
def wPaMovedV : VState := { wPostV with a := { wPost with paOwner := 7 } }

/-- `wPostV` after the migration is nominated on the CTM. -/
def wNominatedV : VState := { wPostV with a := { wPost with ctmPending := 50 } }

/-- `wPostV` after the CTM's owner renounces. -/
def wCtmRenouncedV : VState := { wPostV with a := ⟨0, 0, 3, 35, 60, true⟩ }

/-- Governance's hand-over before `migrate()` (`wHanded`). -/
def wHandedV : VState := { wPostV with a := wHanded }

/-- `wPostV` with a CTM that names no notifier. -/
def wNoNotifierV : VState := { wPostV with hasNotifier := false }

/-- A CTM leg that hands the CTM to `7` and takes it back. -/
def wTransient : List VCall :=
  [⟨3, .fwd (.ctmTransferOwnership 7)⟩, ⟨7, .fwd .ctmAcceptOwnership⟩,
    ⟨7, .fwd (.ctmTransferOwnership 3)⟩, ⟨3, .fwd .ctmAcceptOwnership⟩]

end Contracts.RegistryBootstrapMigration
