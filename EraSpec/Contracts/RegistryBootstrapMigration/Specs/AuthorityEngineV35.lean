import EraSpec.Contracts.RegistryBootstrapMigration.Specs.Forward

/-!
# Model: engine legs on the authority state (draft/v0.35.0)

Source: era-contracts `draft/v0.35.0` at commit `b17415d20` (`b17` below). Paths are relative
to `l1-contracts/contracts/`; every `file:line` in this file is at `b17`. OpenZeppelin is the
pair of submodules `Specs/Forward.lean` cites (`dc44c9f`, `2d081f2`); `b17` pins the same two.

`Specs/Authority.lean` and `Specs/Forward.lean` (first written at `e561b9cc2`, re-pinned to
`b17`) supply the `MigrateStep` and `OpStep` this file reuses. At `b17`, `RegistryBootstrapMigration.migrate()` is
`upgrades/registry/bootstrap/RegistryBootstrapMigration.sol:265-307`. It makes the calls
`Specs/Authority.lean` quotes, in the same order, each three lines below the number quoted
there; `validate()` (:152-189) makes the same checks, and the `RegistryAuthorityLib` functions
it cites are at the cited lines. At `b17`, `UpgradeExecutorBase.forward`
(`governance/UpgradeExecutorBase.sol:35-55`) also reverts on a call with calldata to a target
without code (:42-44, added after `d9f6789`); that is a reject-only check, so
`Specs/Forward.lean`'s `FRun` still over-approximates it. What `b17` has beyond those models is
a second transaction kind, the **engine leg**.

An earlier version of this file was pinned at `d9f6789`. Between `d9f6789` and `b17` the leg
gained a check before the engine runs (:72-77), and `_domainHolders` gained the CTM's
`admin()`, the CTM's `serverNotifierAddress()` and the notifier's `chainTypeManager()`, and now
re-reads the notifier address after the engine returns. This file models `b17`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.RegistryBootstrapMigration.Properties.AuthorityEngineV35` and are proved in
`EraSpec.Contracts.RegistryBootstrapMigration.Proofs.AuthorityEngineV35`.

## The engine leg (`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:51-104`)

Both domain executors reach it from one owner-only entry point:
`CTMUpgradeExecutor.applyInfrastructureUpgrade`
(`upgrades/registry/executors/CTMUpgradeExecutor.sol:64-72`, domain `CTM`, bound CTM) and
`CoreUpgradeExecutor.applyL1Upgrade` (`upgrades/registry/executors/CoreUpgradeExecutor.sol:33-36`,
domain `Core`, CTM zero). After the reject-only checks on the transition and the engine's code
(:57-63), the leg is:

    if (_chainTypeManager != address(0) &&
        IChainTypeManager(_chainTypeManager).admin() == address(_proxyAdmin)) {
        revert ProxyUpgradeCTMAdminIsProxyAdmin(_chainTypeManager); }              // :75-77
    address ownerBefore = owner();                                                  // :78
    address pendingOwnerBefore = pendingOwner();                                    // :79
    bytes32 domainHoldersBefore = _domainHolders(_proxyAdmin, _chainTypeManager);   // :80
    (bool success, bytes memory returnData) = manifest.proxyUpgradeEngine.delegatecall( // :82
        abi.encodeCall(IProxyUpgradeEngine.executeUpgrade, (context, manifest.proxyUpgrades)));
    if (!success) { ... revert ... }                                                // :85-91
    if (owner() != ownerBefore || pendingOwner() != pendingOwnerBefore) {
        revert ProxyUpgradeEngineChangedExecutorOwnership(...); }                   // :93-95
    if (_domainHolders(_proxyAdmin, _chainTypeManager) != domainHoldersBefore) {
        revert ProxyUpgradeEngineMovedDomainAuthority(...); }                       // :96-98
    ProxyUpgradeRowLib.requireRowsApplied(_proxyAdmin, rows);                       // :99-103

`_domainHolders` (:118-148) is `keccak256(abi.encode(_proxyAdmin.owner()))` in the `Core`
domain (:119-121). In the `CTM` domain it reads the CTM's `serverNotifierAddress()` (:123) and
hashes:
* the `ProxyAdmin`'s owner, the CTM's `owner()`, `pendingOwner()` and `admin()`,
  `_proxyAdmin.getProxyAdmin(ctm)`, and that notifier address (:124-133);
* then, if the address is nonzero (:134-136), the hash above with the notifier's `owner()`,
  `pendingOwner()`, `_proxyAdmin.getProxyAdmin(notifier)` and `chainTypeManager()` (:137-147).

`getProxyAdmin` is OpenZeppelin's static call of `admin()` on the proxy. The NatSpec at
:112-114 states what it returns: a proxy `_proxyAdmin` no longer administers passes the query to
its implementation, so "a moved CTM answers its own `admin()` ..., a moved ServerNotifier has
none and reverts the leg". The CTM's `pendingAdmin` is private and is not compared (:114-117).

The engine runs with the executor's address and storage
(`upgrades/registry/engines/IProxyUpgradeEngine.sol:10-21`: it "acts with the executor's
authority", and "every storage slot is the executor's"). So it can make any call the executor
can make, and it can write the executor's own `Ownable2Step` slots directly.

The checks at :93-98 compare **end values with start values** only:
* the executor's own owner and nominee are compared exactly;
* the domain's holders are compared through a hash.

A collision of that hash on the leg's logged `(before, after)` pair is the only way a leg can
leave different holders.

`docs/registry-driven-upgrades.md` (from the repository root) states the check at :275-292: "a
hook cannot transfer those holders, nominate an owner, take the CTM's admin role, re-point the
CTM at another ServerNotifier or the ServerNotifier at another CTM, nor move those proxies with
`changeProxyAdmin`; a succession is a `forward`". It also states what the check does not see:
"The CTM's `pendingAdmin` is private, so a hook that only nominates a CTM admin is not seen",
and "a hook that swaps the implementation of, or `upgradeAndCall`s into, any proxy under the
`ProxyAdmin` (rows, the CTM and the ServerNotifier included) can change what it returns or
stores". And :473-478: "every `forward` cell below holds for it too, except a completed
`setPendingAdmin` (the admin role changing hands), `setServerNotifier` and the last row".

## The bootstrap runs a core leg (`RegistryBootstrapSequence.sol:91-108`)

In `upgrades/registry/bootstrap/RegistryBootstrapSequence.sol`:

    actions_[offset] = BootstrapAction({                                            // :91-99
        label: "hand the ecosystem ProxyAdmin to the bound core executor", ...
        call: Call({ target: address(coreExecutor.PROXY_ADMIN()), value: 0,
                     data: abi.encodeCall(Ownable.transferOwnership, (address(coreExecutor))) }) });
    actions_[offset + 1] = BootstrapAction({                                        // :100-108
        label: "apply the pinned ecosystem inventory (applyL1Upgrade)", ...
        call: Call({ target: address(coreExecutor), value: 0,
                     data: abi.encodeCall(CoreUpgradeExecutor.applyL1Upgrade,
                                          (IProxyUpgradeTransition(CORE_TRANSITION))) }) });

So the governance bundle itself contains a core-domain engine leg. It runs before the CTM
nomination (:109-113) and `migrate()` (:123-127). The core leg's hash covers only the
ecosystem `ProxyAdmin`'s owner, and nothing in the leg checks the CTM domain. Which CTM-domain
slots a core leg keeps depends on who sends the calls in its trace (`OtherDomainQuiet`).

## The executor's entry points, called by the engine itself

During the delegatecall, a call from the engine back into the executor has the executor
itself as `msg.sender`. The gates (`ExecEntry.GatePasses`):

* `forward` (`governance/UpgradeExecutorBase.sol:35`), `applyInfrastructureUpgrade`
  (`CTMUpgradeExecutor.sol:64`), `applyCTMUpgrade` (:77), `applyL1Upgrade`
  (`CoreUpgradeExecutor.sol:33`) and `transferOwnership` are `onlyOwner`;
* `upgradeChain` (`CTMUpgradeExecutor.sol:92-95`) takes the owner or the chain's admin;
* `acceptCTMOwnership` (`CTMUpgradeExecutor.sol:55-61`) takes the owner or the CTM's owner;
* `acceptOwnership` takes the nominee (OpenZeppelin `Ownable2Step`);
* `renounceOwnership` always reverts (`UpgradeExecutorBase.sol:60-62`).

`receive()` (`UpgradeExecutorBase.sol:66`) takes ETH from anyone and writes no storage; it is
not listed.

## Modelling choices

* **`VState` extends `AState`** with:
  * the executors' `owner` and `pendingOwner`, and the ecosystem `ProxyAdmin`'s owner;
  * the CTM proxy's admin (`ctmProxyAdmin`). No step writes it: `changeProxyAdmin` on the CTM
    proxy is not modelled, as in `Forward`;
  * what the CTM's code answers to `owner()` and `pendingOwner()` (`ctmAnswers`);
  * the CTM's `admin()`, its private `pendingAdmin`, and its `serverNotifierAddress()`
    (`state-transition/ChainTypeManager.sol:113, 116, 125`);
  * a notifier state for every address (`NotifierState`): what the contract there answers to
    `owner()`, `pendingOwner()` and `chainTypeManager()`, its proxy's admin, and what its
    implementation answers to `admin()` (`none`: it has no such function, as
    `governance/ServerNotifier.sol` has none). `_domainHolders` reads the state at the address
    the CTM names.
* **A transaction is a call trace** (`VCall`, `VRun`), as in `Forward`: each call has its own
  `msg.sender`. A trace may hold `Forward`'s ops (`VOp.fwd`) and the writers of the new
  fields. A revert is the absence of a step. Here `Op.untracked` is a call that writes none of
  `VState`'s fields; the calls that write the new fields are their own ops.
* **The executor's own slots** are written by `VOp.execSlots`. Only code running in that
  executor's storage can do that, which is the engine during that executor's leg (`ctx`). The
  executors make no other delegatecall: `UpgradeExecutorBase` makes plain calls only (:46), and
  `CTMUpgradeExecutor` and `CoreUpgradeExecutor` make none outside `_applyProxyUpgradeTransition`
  (as their NatSpec says, `CTMUpgradeExecutor.sol:24-25`, `CoreUpgradeExecutor.sol:18-19`).
* **A CTM code swap** (`VOp.ctmCodeSwap`) is `Forward`'s `Op.ctmCodeSwap`, plus what the new
  code leaves in the admin, pending-admin and notifier fields, and how it answers the
  ownership reads: `none` means from its `Ownable2Step` slots, `some (o, p)` means fixed
  answers. `_domainHolders` reads the answers (`VState.ctmRead`). Parking is about the slots.
  The CTM is a row of the CTM domain (`upgrades/registry/libraries/ContractIdentifiers.sol:74`),
  so an infrastructure leg's own row swaps its implementation; a row that keeps the storage is
  the swap that writes back the current values. A notifier code swap (`VOp.notifierCodeSwap`)
  sets every answer of that notifier.
* **`holdersHash` is an arbitrary function** `DomainHolders → UInt256`. No injectivity premise
  is made anywhere. Each result about a leg carries a collision on the leg's own logged pair
  as a disjunct (`HoldersCollide`), and `CollisionDisjunctNeeded` shows that the disjunct is
  load-bearing. `_domainHolders` nests two `keccak256` calls (:124-133 inside :137-147), so a
  collision of `holdersHash` on a pair of tuples is a `keccak256` collision of the outer or of
  the inner call.
* **Over-approximations**, which only add runs:
  * the leg needs no owner as its outer sender;
  * the rows check (:99-103) and the code checks (:57-63) are omitted;
  * a read that reverts in the contract is read as the field's value, for example on an
    address without code named as a notifier, on a swapped-in CTM implementation without one of
    the read functions, or on a proxy whose admin is the executor itself (the proxy does not
    forward its admin's calls). The one revert modelled is a named notifier's `getProxyAdmin`
    (`HoldersReadable`);
  * calls by a proxy's admin to the proxy's implementation, which the transparent proxy refuses,
    are allowed.
* **Model boundaries** (assumptions, not over-approximations):
  * After a CTM code swap the CTM's code has the entry points modelled here and no other writer
    of the modelled fields, as a `ChainTypeManager` implementation does. A swap's own writes are
    arbitrary. The results along runs (`NoReparkingAcrossEngineLegs`, ...) rest on this; the
    results about one leg compare its two ends.
  * A contract named as a notifier changes its answers only through the notifier ops, as
    `ServerNotifier` does.
  * `migrate()` and the bundle (`VLabel.tx`) leave the new fields alone: the bootstrap rows'
    implementation swaps keep the storage that the reads use, as `Specs/Authority.lean` assumes
    for the CTM's `Ownable2Step` slots.
  * Only the CTM-domain `ProxyAdmin`'s owner replaces the CTM's code, and only while that
    `ProxyAdmin` administers the CTM proxy (as `Forward` ties `Op.ctmCodeSwap` to that owner).
    In a state where another admin holds the CTM proxy, that admin's code swaps have no step.
    The pre-check at :75-77 exists for that state (the comment at :72-74). No step of this
    model moves the CTM proxy away from the `ProxyAdmin`, and the witnesses all start with the
    `ProxyAdmin` as its admin.
* **Fixed configuration**, as in `Specs/Authority.lean`: `migrate()` reads the executors'
  getters from `Config.exec`, not from the live `VState` fields. The CTM executor is the
  manifest's `ctmExecutor`, bound (immutably) to the manifest's CTM and CTM-domain `ProxyAdmin`
  (`upgrades/registry/libraries/RegistryAuthorityLib.sol:76-78` checks the bindings by value
  before the domain is handed over); the core executor is the manifest's `coreExecutor`, and
  `ecoOwner` is the owner of the `ProxyAdmin` it is bound to.
* **Not modelled.**
  * `ProxyAdmin.changeProxyAdmin` on the CTM proxy (above).
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
inductive LegDomain
  /-- `CoreUpgradeExecutor`, bound to the ecosystem `ProxyAdmin`. -/
  | core
  /-- `CTMUpgradeExecutor`, bound to the CTM and the CTM-domain `ProxyAdmin`. -/
  | ctm
deriving DecidableEq

/-- The executor of a domain: the manifest's `coreExecutor` or `ctmExecutor`. -/
def LegDomain.executor (K : Config) : LegDomain → Address
  | .core => K.m.core
  | .ctm => K.m.E

/-- What the contract at one address answers when `_domainHolders` reads it as a notifier. -/
structure NotifierState where
  /-- `owner()` (`governance/ServerNotifier.sol:28`, `Ownable2Step`). -/
  owner : Address
  /-- `pendingOwner()`. -/
  pending : Address
  /-- The admin of its transparent proxy. -/
  proxyAdmin : Address
  /-- `chainTypeManager()` (`ServerNotifier.sol:30`). -/
  ctm : Address
  /-- What its implementation answers to `admin()`: `none` if it has no such function and the
  call reverts, as for `ServerNotifier`. -/
  adminAnswer : Option Address
deriving DecidableEq

/-- The authority state, with the executors, the ecosystem `ProxyAdmin`, the CTM's admin role
and notifier binding, and the notifiers. -/
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
  /-- The admin of the CTM's transparent proxy. No step writes it. -/
  ctmProxyAdmin : Address
  /-- How the CTM's code answers `owner()` and `pendingOwner()`: `none` from its `Ownable2Step`
  slots (`a.ctmOwner`, `a.ctmPending`), `some (o, p)` with fixed answers. -/
  ctmAnswers : Option (Address × Address)
  /-- The CTM's `admin()` (`state-transition/ChainTypeManager.sol:113`). -/
  ctmAdmin : Address
  /-- The CTM's private `pendingAdmin` (`ChainTypeManager.sol:116`). -/
  ctmPendingAdmin : Address
  /-- The CTM's `serverNotifierAddress()` (`ChainTypeManager.sol:125`); zero for none. -/
  notifier : Address
  /-- The contract at each address, read as a notifier. -/
  notifiers : Address → NotifierState

/-- A domain executor's `owner()`. -/
def VState.execOwner (s : VState) : LegDomain → Address
  | .core => s.cOwner
  | .ctm => s.eOwner

/-- A domain executor's `pendingOwner()`. -/
def VState.execPending (s : VState) : LegDomain → Address
  | .core => s.cPending
  | .ctm => s.ePending

/-- Write a domain executor's owner and nominee. -/
def VState.setExec (s : VState) : LegDomain → Address → Address → VState
  | .core, o, p => { s with cOwner := o, cPending := p }
  | .ctm, o, p => { s with eOwner := o, ePending := p }

/-- What the CTM answers to `owner()` and `pendingOwner()`. -/
def VState.ctmRead (s : VState) : Address × Address :=
  s.ctmAnswers.getD (s.a.ctmOwner, s.a.ctmPending)

/-- `ctmProxyAdmin.getProxyAdmin(ctm)`: the `ProxyAdmin` itself while it administers the CTM
proxy, otherwise the CTM's own `admin()` (`ProxyUpgradeExecutorBase.sol:112-114`). -/
def VState.ctmProxyAdminRead (K : Config) (s : VState) : Address :=
  if s.ctmProxyAdmin = K.m.pa then K.m.pa else s.ctmAdmin

/-- `ctmProxyAdmin.getProxyAdmin(n)` for a notifier `n`: the `ProxyAdmin` itself while it
administers `n`'s proxy, otherwise what `n`'s implementation answers to `admin()`; `none` is a
revert. -/
def VState.notifierAdminRead (K : Config) (s : VState) (n : Address) : Option Address :=
  if (s.notifiers n).proxyAdmin = K.m.pa then some K.m.pa else (s.notifiers n).adminAnswer

/-- Replace the state of the notifier at `n`. -/
def VState.setNotifier (s : VState) (n : Address) (t : NotifierState) : VState :=
  { s with notifiers := Function.update s.notifiers n t }

/-! ## Calls -/

/-- An entry point that writes a tracked slot. -/
inductive VOp
  /-- One of `Forward`'s ops other than its CTM code swap: `Op.ctmCodeSwap` has no `fwd` step,
  and is `VOp.ctmCodeSwap` instead. -/
  | fwd (op : Op)
  /-- `ProxyAdmin.upgrade`/`upgradeAndCall` on the CTM proxy. The CTM's owner, nominee, version
  and release become `o`, `p`, `v`, `r`; its admin, pending admin and notifier become `adm`,
  `padm`, `nf`; and its new code answers the ownership reads as `answers` says (`none`: from
  the slots). -/
  | ctmCodeSwap (o p : Address) (v : ℕ) (r : Address) (adm padm nf : Address)
      (answers : Option (Address × Address))
  /-- The CTM's `setPendingAdmin(x)` (`ChainTypeManager.sol:354-360`, `onlyOwnerOrAdmin`). -/
  | ctmSetPendingAdmin (x : Address)
  /-- The CTM's `acceptAdmin()` (`ChainTypeManager.sol:363-375`). -/
  | ctmAcceptAdmin
  /-- The CTM's `setServerNotifier(x)` (`ChainTypeManager.sol:387-391`, `onlyOwner`). -/
  | ctmSetServerNotifier (x : Address)
  /-- The executor's `transferOwnership(x)` (OpenZeppelin `Ownable2Step`, `onlyOwner`). -/
  | execTransferOwnership (d : LegDomain) (x : Address)
  /-- The executor's `acceptOwnership()`. -/
  | execAcceptOwnership (d : LegDomain)
  /-- The executor's `renounceOwnership()`, which always reverts
  (`UpgradeExecutorBase.sol:60-62`): it has no step. -/
  | execRenounceOwnership (d : LegDomain)
  /-- Code running in the executor's storage writes its `Ownable2Step` slots directly. -/
  | execSlots (d : LegDomain) (o p : Address)
  /-- The ecosystem `ProxyAdmin`'s `transferOwnership(x)` (`Ownable`, `x ≠ 0`). -/
  | ecoTransferOwnership (x : Address)
  /-- The ecosystem `ProxyAdmin`'s `renounceOwnership()`. -/
  | ecoRenounceOwnership
  /-- The notifier at `n`: `transferOwnership(x)`. -/
  | notifierTransferOwnership (n x : Address)
  /-- The notifier at `n`: `acceptOwnership()`. -/
  | notifierAcceptOwnership (n : Address)
  /-- The notifier at `n`: `renounceOwnership()` (`ServerNotifier` does not override it). -/
  | notifierRenounceOwnership (n : Address)
  /-- The notifier at `n`: `setChainTypeManager(x)` (`ServerNotifier.sol:67-72`, `onlyOwner`,
  `x ≠ 0`). -/
  | notifierSetChainTypeManager (n x : Address)
  /-- Moving the notifier proxy at `n` to admin `x`: `ProxyAdmin.changeProxyAdmin`, or
  `changeAdmin` by an admin that is not the `ProxyAdmin`. -/
  | notifierChangeAdmin (n x : Address)
  /-- Replacing the code of the notifier at `n`; the new code answers `owner()`,
  `pendingOwner()`, `chainTypeManager()` and `admin()` with `o`, `p`, `c`, `adm`. -/
  | notifierCodeSwap (n o p c : Address) (adm : Option Address)
deriving DecidableEq

/-- One call: its `msg.sender` and its entry point. -/
structure VCall where
  /-- `msg.sender`. -/
  sender : Address
  /-- The entry point. -/
  op : VOp
deriving DecidableEq

/-- Who may act on the notifier proxy at `n`: the CTM-domain `ProxyAdmin`'s owner while that
`ProxyAdmin` is its admin, otherwise its admin itself. -/
def NotifierAdminAuth (K : Config) (s : VState) (n a : Address) : Prop :=
  ((s.notifiers n).proxyAdmin = K.m.pa ∧ s.a.paOwner = a) ∨
    ((s.notifiers n).proxyAdmin ≠ K.m.pa ∧ (s.notifiers n).proxyAdmin = a)

/-- One successful call by `a`. `ctx` is the executor whose storage the running code shares:
`some d` during domain `d`'s engine leg, `none` otherwise. -/
inductive VOpStep (K : Config) (ctx : Option LegDomain) (a : Address) :
    VState → VOp → VState → Prop
  /-- `Forward`'s call, on `AState`. -/
  | fwd {s : VState} {op : Op} {t : AState} :
      OpStep K a s.a op t → ¬ op.swapsCtmCode → VOpStep K ctx a s (.fwd op) { s with a := t }
  /-- `onlyOwner` on the `ProxyAdmin` (`OZ/proxy/transparent/ProxyAdmin.sol:62-64, 74-80`), which
  must administer the CTM proxy. -/
  | ctmCodeSwap {s : VState} {o p : Address} {v : ℕ} {r adm padm nf : Address}
      {ans : Option (Address × Address)} :
      s.a.paOwner = a → s.ctmProxyAdmin = K.m.pa →
      VOpStep K ctx a s (.ctmCodeSwap o p v r adm padm nf ans)
        { s with a := { s.a with ctmOwner := o, ctmPending := p, ctmPv := v, ctmRel := r },
                 ctmAdmin := adm, ctmPendingAdmin := padm, notifier := nf, ctmAnswers := ans }
  /-- `onlyOwnerOrAdmin` (`ChainTypeManager.sol:208-213`), then the pending admin is `x`. -/
  | ctmSetPendingAdmin {s : VState} {x : Address} :
      (s.ctmAdmin = a ∨ s.a.ctmOwner = a) →
      VOpStep K ctx a s (.ctmSetPendingAdmin x) { s with ctmPendingAdmin := x }
  /-- The pending admin accepts: the caller is the admin and the nomination is deleted. -/
  | ctmAcceptAdmin {s : VState} :
      s.ctmPendingAdmin = a →
      VOpStep K ctx a s .ctmAcceptAdmin { s with ctmAdmin := a, ctmPendingAdmin := 0 }
  /-- `onlyOwner`, then the CTM names notifier `x`. -/
  | ctmSetServerNotifier {s : VState} {x : Address} :
      s.a.ctmOwner = a → VOpStep K ctx a s (.ctmSetServerNotifier x) { s with notifier := x }
  /-- `onlyOwner`, then the nomination is `x`. -/
  | execTransferOwnership {s : VState} {d : LegDomain} {x : Address} :
      s.execOwner d = a →
      VOpStep K ctx a s (.execTransferOwnership d x) (s.setExec d (s.execOwner d) x)
  /-- `pendingOwner() == msg.sender`, then the caller owns it and the nomination is deleted. -/
  | execAcceptOwnership {s : VState} {d : LegDomain} :
      s.execPending d = a → VOpStep K ctx a s (.execAcceptOwnership d) (s.setExec d a 0)
  /-- Only the code delegatecalled into executor `d`, as `d`. -/
  | execSlots {s : VState} {d : LegDomain} {o p : Address} :
      ctx = some d → a = d.executor K → VOpStep K ctx a s (.execSlots d o p) (s.setExec d o p)
  /-- `onlyOwner` and `x ≠ 0` (`OZ/access/Ownable.sol:69-72`). -/
  | ecoTransferOwnership {s : VState} {x : Address} :
      s.ecoOwner = a → x ≠ 0 → VOpStep K ctx a s (.ecoTransferOwnership x) { s with ecoOwner := x }
  /-- `onlyOwner` (`OZ/access/Ownable.sol:61-63`). -/
  | ecoRenounceOwnership {s : VState} :
      s.ecoOwner = a → VOpStep K ctx a s .ecoRenounceOwnership { s with ecoOwner := 0 }
  /-- `onlyOwner`, then the nomination is `x`. -/
  | notifierTransferOwnership {s : VState} {n x : Address} :
      (s.notifiers n).owner = a →
      VOpStep K ctx a s (.notifierTransferOwnership n x)
        (s.setNotifier n { s.notifiers n with pending := x })
  /-- The nominee accepts. -/
  | notifierAcceptOwnership {s : VState} {n : Address} :
      (s.notifiers n).pending = a →
      VOpStep K ctx a s (.notifierAcceptOwnership n)
        (s.setNotifier n { s.notifiers n with owner := a, pending := 0 })
  /-- `onlyOwner`, then no owner and no nominee. -/
  | notifierRenounceOwnership {s : VState} {n : Address} :
      (s.notifiers n).owner = a →
      VOpStep K ctx a s (.notifierRenounceOwnership n)
        (s.setNotifier n { s.notifiers n with owner := 0, pending := 0 })
  /-- `onlyOwner` and `x ≠ 0`, then the notifier serves CTM `x`. -/
  | notifierSetChainTypeManager {s : VState} {n x : Address} :
      (s.notifiers n).owner = a → x ≠ 0 →
      VOpStep K ctx a s (.notifierSetChainTypeManager n x)
        (s.setNotifier n { s.notifiers n with ctm := x })
  /-- The proxy's admin moves (OpenZeppelin v4 `_changeAdmin` rejects zero). -/
  | notifierChangeAdmin {s : VState} {n x : Address} :
      NotifierAdminAuth K s n a → x ≠ 0 →
      VOpStep K ctx a s (.notifierChangeAdmin n x)
        (s.setNotifier n { s.notifiers n with proxyAdmin := x })
  /-- The notifier's code is replaced. -/
  | notifierCodeSwap {s : VState} {n o p c : Address} {adm : Option Address} :
      NotifierAdminAuth K s n a →
      VOpStep K ctx a s (.notifierCodeSwap n o p c adm)
        (s.setNotifier n
          { s.notifiers n with owner := o, pending := p, ctm := c, adminAnswer := adm })

/-- A call trace, in execution order; a failing call reverts them all. -/
inductive VRun (K : Config) (ctx : Option LegDomain) : VState → List VCall → VState → Prop
  | nil {s : VState} : VRun K ctx s [] s
  | cons {s s' s'' : VState} {c : VCall} {cs : List VCall} :
      VOpStep K ctx c.sender s c.op s' → VRun K ctx s' cs s'' → VRun K ctx s (c :: cs) s''

/-! ## The domain holders and the leg -/

/-- What `_domainHolders` (`ProxyUpgradeExecutorBase.sol:118-148`) encodes before hashing. -/
inductive DomainHolders
  /-- `abi.encode(_proxyAdmin.owner())` (:120). -/
  | core (ecoOwner : Address)
  /-- The CTM domain's tuple: the `ProxyAdmin`'s owner, the CTM's owner, nominee and admin, its
  `getProxyAdmin` read and its notifier address (:124-133); then, if that address is nonzero,
  the notifier's owner, nominee, `getProxyAdmin` read and CTM (:137-147). -/
  | ctm (paOwner ctmOwner ctmPending ctmAdmin ctmProxyAdmin notifier : Address)
      (notifierPart : Option (Address × Address × Address × Address))
deriving DecidableEq

/-- The holders a domain's leg logs. The CTM's ownership entries are what its code answers. A
notifier's `getProxyAdmin` read is taken where it does not revert (`HoldersReadable`). -/
def VState.holders (K : Config) (s : VState) : LegDomain → DomainHolders
  | .core => .core s.ecoOwner
  | .ctm => .ctm s.a.paOwner s.ctmRead.1 s.ctmRead.2 s.ctmAdmin (s.ctmProxyAdminRead K) s.notifier
      (if s.notifier = 0 then none
       else some ((s.notifiers s.notifier).owner, (s.notifiers s.notifier).pending,
                  (s.notifierAdminRead K s.notifier).getD 0, (s.notifiers s.notifier).ctm))

/-- `_domainHolders` does not revert: in the CTM domain, a named notifier's `getProxyAdmin`
read succeeds. -/
def HoldersReadable (K : Config) : LegDomain → VState → Prop
  | .core, _ => True
  | .ctm, s => s.notifier ≠ 0 → (s.notifierAdminRead K s.notifier).isSome

/-- `holdersHash` collides on a logged pair: the tuples differ, the hashes agree. -/
def HoldersCollide (H : DomainHolders → UInt256) (h h' : DomainHolders) : Prop :=
  h ≠ h' ∧ H h = H h'

/-- **One successful engine leg** of domain `d` with call trace `cs`. In the CTM domain the
CTM's `admin()` is not the `ProxyAdmin` (`:75-77`). `_domainHolders` succeeds before (`:80`) and
after. The trace runs in `d`'s executor's storage (`:82-91`). The executor's owner and nominee
are as before (`:93-95`), and the hash of the holders is as before (`:96-98`). `H` is
`holdersHash`, an arbitrary function. -/
inductive EngineLeg (K : Config) (H : DomainHolders → UInt256) (d : LegDomain) :
    VState → List VCall → VState → Prop
  | mk {s s' : VState} {cs : List VCall} :
      (d = .ctm → s.ctmAdmin ≠ K.m.pa) →
      HoldersReadable K d s →
      VRun K (some d) s cs s' →
      s'.execOwner d = s.execOwner d → s'.execPending d = s.execPending d →
      HoldersReadable K d s' →
      H (s'.holders K d) = H (s.holders K d) →
      EngineLeg K H d s cs s'

/-- The leg without the holders check at `:96-98`, for the countermodel. -/
inductive EngineLegNoHolderCheck (K : Config) (d : LegDomain) :
    VState → List VCall → VState → Prop
  | mk {s s' : VState} {cs : List VCall} :
      VRun K (some d) s cs s' →
      s'.execOwner d = s.execOwner d → s'.execPending d = s.execPending d →
      EngineLegNoHolderCheck K d s cs s'

/-! ## Projections and premises -/

/-- The `Forward` op a call is, if any. -/
def VOp.toOp : VOp → Option Op
  | .fwd op => some op
  | .ctmCodeSwap o p v r _ _ _ _ => some (.ctmCodeSwap o p v r)
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
  | .ctmCodeSwap _ _ _ _ _ _ _ _ => True
  | _ => False

/-- The call replaces the CTM's code with code that does not answer the ownership reads from
its slots. -/
def VOp.answersFalsely : VOp → Prop
  | .ctmCodeSwap _ _ _ _ _ _ _ (some _) => True
  | _ => False

/-- The other domain's holders send no call in the trace, and a core leg makes no `migrate()`
call. The holders are taken at the start of the leg.
* For a CTM leg: the ecosystem `ProxyAdmin`'s owner, and the core executor's owner and nominee.
* For a core leg: the CTM's owner and nominee, the CTM-domain `ProxyAdmin`'s owner, and the CTM
  executor's owner and nominee. -/
def OtherDomainQuiet (d : LegDomain) (s : VState) (cs : List VCall) : Prop :=
  match d with
  | .ctm => ∀ c ∈ cs, c.sender ≠ s.ecoOwner ∧ c.sender ≠ s.cOwner ∧ c.sender ≠ s.cPending
  | .core => ∀ c ∈ cs, c.sender ≠ s.a.ctmOwner ∧ c.sender ≠ s.a.ctmPending ∧
      c.sender ≠ s.a.paOwner ∧ c.sender ≠ s.eOwner ∧ c.sender ≠ s.ePending ∧ c.op ≠ .fwd .migrate

/-- The authority slots a leg's own checks cover, unchanged.
* CTM leg: the CTM's owner and nominee, the CTM-domain `ProxyAdmin`'s owner, and the CTM
  executor's owner and nominee.
* Core leg: the ecosystem `ProxyAdmin`'s owner, and the core executor's owner and nominee. -/
def LegOwnFrame : LegDomain → VState → VState → Prop
  | .ctm, s, s' => s'.a.ctmOwner = s.a.ctmOwner ∧ s'.a.ctmPending = s.a.ctmPending ∧
      s'.a.paOwner = s.a.paOwner ∧ s'.eOwner = s.eOwner ∧ s'.ePending = s.ePending
  | .core, s, s' => s'.ecoOwner = s.ecoOwner ∧ s'.cOwner = s.cOwner ∧ s'.cPending = s.cPending

/-- The other domain's slots, unchanged. For a core leg this includes the migration's
`executed`. -/
def LegOtherFrame : LegDomain → VState → VState → Prop
  | .ctm, s, s' => s'.ecoOwner = s.ecoOwner ∧ s'.cOwner = s.cOwner ∧ s'.cPending = s.cPending
  | .core, s, s' => s'.a.ctmOwner = s.a.ctmOwner ∧ s'.a.ctmPending = s.a.ctmPending ∧
      s'.a.paOwner = s.a.paOwner ∧ s'.eOwner = s.eOwner ∧ s'.ePending = s.ePending ∧
      s'.a.executed = s.a.executed

/-- The authority slots of this topic, all unchanged: the CTM's owner and nominee, both
`ProxyAdmin`s' owners, and both executors' owner and nominee. -/
def LegAuthFrame (s s' : VState) : Prop :=
  s'.a.ctmOwner = s.a.ctmOwner ∧ s'.a.ctmPending = s.a.ctmPending ∧
    s'.a.paOwner = s.a.paOwner ∧ s'.ecoOwner = s.ecoOwner ∧
    s'.eOwner = s.eOwner ∧ s'.ePending = s.ePending ∧ s'.cOwner = s.cOwner ∧
    s'.cPending = s.cPending

/-- The CTM domain's bindings that `b17` added to the hash, unchanged: the CTM's `admin()` and
the notifier it names, and, if it names one, that notifier's owner, nominee, CTM and
`getProxyAdmin` read. -/
def CtmBindingsFrame (K : Config) (s s' : VState) : Prop :=
  s'.ctmAdmin = s.ctmAdmin ∧ s'.notifier = s.notifier ∧
    (s.notifier ≠ 0 →
      (s'.notifiers s.notifier).owner = (s.notifiers s.notifier).owner ∧
      (s'.notifiers s.notifier).pending = (s.notifiers s.notifier).pending ∧
      (s'.notifiers s.notifier).ctm = (s.notifiers s.notifier).ctm ∧
      s'.notifierAdminRead K s.notifier = s.notifierAdminRead K s.notifier)

/-! ## Runs with engine legs -/

/-- A transaction. -/
inductive VLabel
  /-- One of `Specs/Authority.lean`'s transactions; the new fields are untouched. -/
  | tx (l : Label)
  /-- Any transaction without a delegatecall into an executor (a `forward`, a direct call), as
  its call trace. -/
  | call (cs : List VCall)
  /-- An engine leg of domain `d`, as its call trace. -/
  | engineLeg (d : LegDomain) (cs : List VCall)

/-- One successful transaction. -/
inductive VSysStep (K : Config) (H : DomainHolders → UInt256) : VState → VLabel → VState → Prop
  | tx {s : VState} {l : Label} {t : AState} :
      AStep K s.a l t → VSysStep K H s (.tx l) { s with a := t }
  | call {s s' : VState} {cs : List VCall} : VRun K none s cs s' → VSysStep K H s (.call cs) s'
  | engineLeg {s s' : VState} {d : LegDomain} {cs : List VCall} :
      EngineLeg K H d s cs s' → VSysStep K H s (.engineLeg d cs) s'

/-- A sequence of successful transactions. -/
inductive VSysRun (K : Config) (H : DomainHolders → UInt256) :
    VState → List VLabel → VState → Prop
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

/-- The run splits as `vs₁`, an engine leg of domain `d` and trace `cs`, then `vs₂`: the prefix
reaches `t` from `s`, the leg runs from `t` to `t'`, the rest reaches `s'` from `t'`, and
`holdersHash` collides on the holders that leg logs at `t` and `t'`. Every transaction has one
outcome (`EngineRunsDeterministic`), so `t` and `t'` are the states the run passes through. -/
def RunLegCollides (K : Config) (H : DomainHolders → UInt256) (s : VState) (vs : List VLabel)
    (s' : VState) : Prop :=
  ∃ (vs₁ vs₂ : List VLabel) (d : LegDomain) (cs : List VCall) (t t' : VState),
    vs = vs₁ ++ VLabel.engineLeg d cs :: vs₂ ∧ VSysRun K H s vs₁ t ∧ EngineLeg K H d t cs t' ∧
      VSysRun K H t' vs₂ s' ∧ HoldersCollide H (t.holders K d) (t'.holders K d)

/-! ## The executor's constructor and entry points -/

/-- `UpgradeExecutorBase`'s constructor (`governance/UpgradeExecutorBase.sol:25-32`). It
reverts on a zero `_initialOwner` (:28-30); otherwise the owner is `_initialOwner` and there
is no nominee. Arguments: initial owner, resulting owner, resulting nominee. -/
inductive ExecConstructed : Address → Address → Address → Prop
  | mk {o : Address} : o ≠ 0 → ExecConstructed o o 0

/-- The external entry points of the two executors that are not `view`. -/
inductive ExecEntry
  /-- `UpgradeExecutorBase.forward` (:35). -/
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
  /-- `UpgradeExecutorBase.renounceOwnership` (:60). -/
  | renounceOwnership
deriving DecidableEq

/-- Which executor declares the entry point. -/
def LegDomain.Declares : LegDomain → ExecEntry → Prop
  | .ctm, .applyL1Upgrade => False
  | .core, .applyInfrastructureUpgrade => False
  | .core, .applyCTMUpgrade => False
  | .core, .upgradeChain _ => False
  | .core, .acceptCTMOwnership => False
  | _, _ => True

/-- What a gate reads when it runs: the executor's owner and nominee, the CTM's answer to
`owner()`, and the CTM's `getChainAdmin`. -/
structure ExecGateView where
  /-- The executor's `owner()`. -/
  owner : Address
  /-- The executor's `pendingOwner()`. -/
  pending : Address
  /-- `ctm.owner()`. -/
  ctmOwner : Address
  /-- `CHAIN_TYPE_MANAGER.getChainAdmin(chainId)`. -/
  chainAdmin : ℕ → Address

/-- The gate a domain executor's entry point applies, read from the state. -/
def VState.gateView (s : VState) (d : LegDomain) (chainAdmin : ℕ → Address) : ExecGateView :=
  ⟨s.execOwner d, s.execPending d, s.ctmRead.1, chainAdmin⟩

/-- The caller check of an entry point passes for `sender`:
* `onlyOwner`: `forward` (`UpgradeExecutorBase.sol:35`), `applyInfrastructureUpgrade`
  (`CTMUpgradeExecutor.sol:64`), `applyCTMUpgrade` (:77), `applyL1Upgrade`
  (`CoreUpgradeExecutor.sol:33`), `transferOwnership`;
* `upgradeChain`: the owner or the chain's admin (`CTMUpgradeExecutor.sol:93-95`);
* `acceptCTMOwnership`: the owner or the CTM's owner (`CTMUpgradeExecutor.sol:57-59`);
* `acceptOwnership`: the nominee;
* `renounceOwnership`: never (`UpgradeExecutorBase.sol:60-62`). -/
def ExecEntry.GatePasses (g : ExecGateView) (sender : Address) : ExecEntry → Prop
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
the ecosystem `ProxyAdmin`. The CTM names the notifier at `8`, which the CTM executor owns and
which serves CTM `1`. The CTM-domain `ProxyAdmin` administers the CTM and notifier proxies.
The CTM's admin role is held by account `6`. Address `7` is another account. -/

/-- The notifier at `8` after the witness bundle: owned by the CTM executor `3`, no nominee,
administered by the `ProxyAdmin` `2`, serving CTM `1`, with `ServerNotifier`'s code (no
`admin()`). -/
def wNotifierState : NotifierState := ⟨3, 0, 2, 1, none⟩

/-- The notifiers: `8` as above; every other address answers zero and has no `admin()`. -/
def wNotifiers : Address → NotifierState := fun n =>
  if n = 8 then wNotifierState else ⟨0, 0, 0, 0, none⟩

/-- After the witness bundle (`wPost`): governance `9` owns both executors, the core executor
`4` owns the ecosystem `ProxyAdmin`, and the CTM-domain `ProxyAdmin` `2` administers the CTM.
The CTM's admin is `6`, with no pending admin, and it names notifier `8`. -/
def wPostV : VState where
  a := wPost
  eOwner := 9
  ePending := 0
  cOwner := 9
  cPending := 0
  ecoOwner := 4
  ctmProxyAdmin := 2
  ctmAnswers := none
  ctmAdmin := 6
  ctmPendingAdmin := 0
  notifier := 8
  notifiers := wNotifiers

/-- After the non-genuine executor's `migrate()` (`wParked`). -/
def wParkedV : VState := { wPostV with a := wParked }

/-- `wParkedV` after executor `3` accepts the CTM: the authority state of `wPostV`. -/
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
def wNoNotifierV : VState := { wPostV with notifier := 0 }

/-- `wPostV` with the CTM's admin role held by the CTM-domain `ProxyAdmin`. -/
def wAdminIsPaV : VState := { wPostV with ctmAdmin := 2 }

/-- `wPostV` after the notifier's owner renounces. -/
def wNotifierRenouncedV : VState :=
  wPostV.setNotifier 8 { wNotifierState with owner := 0, pending := 0 }

/-- `wPostV` after the notifier is pointed at CTM `5`. -/
def wNotifierRepointedV : VState := wPostV.setNotifier 8 { wNotifierState with ctm := 5 }

/-- `wPostV` after the CTM's owner nominates `7` for the CTM's admin role. -/
def wAdminNominatedV : VState := { wPostV with ctmPendingAdmin := 7 }

/-- `wAdminNominatedV` after `7` accepts the admin role. -/
def wAdminTakenV : VState := { wPostV with ctmAdmin := 7 }

/-- A CTM leg that hands the CTM to `7` and takes it back. -/
def wTransientLeg : List VCall :=
  [⟨3, .fwd (.ctmTransferOwnership 7)⟩, ⟨7, .fwd .ctmAcceptOwnership⟩,
    ⟨7, .fwd (.ctmTransferOwnership 3)⟩, ⟨3, .fwd .ctmAcceptOwnership⟩]

/-- A CTM leg that moves the CTM-domain `ProxyAdmin` to `7`, which moves it back. -/
def wPaRoundTrip : List VCall :=
  [⟨3, .fwd (.paTransferOwnership 7)⟩, ⟨7, .fwd (.paTransferOwnership 3)⟩]

/-- A core leg that moves the ecosystem `ProxyAdmin` to `7`, which moves it back. -/
def wEcoRoundTrip : List VCall :=
  [⟨4, .ecoTransferOwnership 7⟩, ⟨7, .ecoTransferOwnership 4⟩]

/-- A CTM leg that unbinds the CTM's notifier and binds it again. -/
def wNotifierRoundTrip : List VCall :=
  [⟨3, .ctmSetServerNotifier 0⟩, ⟨3, .ctmSetServerNotifier 8⟩]

end Contracts.RegistryBootstrapMigration
