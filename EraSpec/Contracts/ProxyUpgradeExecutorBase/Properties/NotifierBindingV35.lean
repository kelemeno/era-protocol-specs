import EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.NotifierBindingV35

/-!
# Properties: the ServerNotifier binding at `d9f6789`

Statements only; the model is `Specs/NotifierBindingV35.lean` and the proofs are
`Proofs/NotifierBindingV35.lean`. Source: era-contracts `draft/v0.35.0` at
`d9f678900e1bc8286412b78f56d4a9f443983c29`.

## The claim checked

`ProxyUpgradeExecutorBase.sol:32-36` says the executor checks, after the engine returns, that
"the owner, pending owner and proxy admin of the CTM and of its ServerNotifier" are unchanged.
What it compares is the holders of the notifier the CTM pointed at **before** the engine
(:71-73, :90). `PostCheckIsHolderReadingsEqual` says exactly which readings the comparison
constrains. It never compares which notifier the CTM points at, nor which CTM the notifier asks
for chain admins.

* **An engine leg can re-point the CTM at another notifier** (`EngineRepointsServerNotifier`).
  `setServerNotifier(N')` is `onlyOwner` and the executor owns the CTM, so the leg succeeds for
  every `N'`, whoever owns it. The check passes for every hash function, because the old
  notifier's holders did not change. Afterwards every chain's validator gate reads `N'`'s
  schedule, and `requireNotifierHandedOver` for the original notifier fails.
* **An engine leg can re-bind the notifier to another CTM** (`EngineRebindsNotifierCtm`).
  `setChainTypeManager(C')` is `onlyOwner` and the executor owns the notifier. `_domainHolders`
  never reads that field (`DomainHoldersIgnoreBinding`), so the check passes at either read time.
  Afterwards `C'` names every chain's admin for the notifier.
* **Reading the notifier after the engine would catch a repoint exactly when the new
  notifier's holders differ** (`PostReadCatchesOnlyHolderChange`). It would catch a foreign-owned
  `N'`. It would not catch an `N'` with the same owner, nominee and proxy admin, and it would
  never catch a re-bind.
* **What the check does catch** (`PostCheckCatchesNotifierNomination`): a leg that nominates a
  new owner on the notifier the CTM pointed at fails the comparison of the tuples, so it passes
  only if the hash collides on two specific tuples.

## Who moves the binding, and who writes an entry

* **The binding** (`BindingMovedOnlyByItsHolders`): a step that breaks
  `requireNotifierHandedOver` is by the notifier's owner (the executor), the CTM's owner, or
  whoever controls the `ProxyAdmin` of the notifier or of the CTM. In the registry shape all of
  these are the executor, so no sequence of calls by anyone else leaves the shape
  (`ShapeKeptByOtherCallers`). An engine leg is a sequence of calls by the executor.
* **Per notifier** (`NotifierEntryWritersV35`): an entry `(id, v)` of notifier `n` changes
  only by `setUpgradeTimestamp(id, ts)` from `n.chainTypeManager.getChainAdmin(id)`, with
  `v = n.chainTypeManager.getProtocolVersion(id)` and `ts ≠ 0`, or by an implementation swap
  from whoever controls `n`'s `ProxyAdmin`. The notifier's own owner never writes an entry. It
  chooses who does, by `setChainTypeManager` (`NotifierBindingWritersV35`).
* **The entry the diamond reads** (`LiveEntryWritersV35`) additionally changes when the CTM's
  owner calls `setServerNotifier`, or the CTM's `ProxyAdmin` owner swaps the CTM's code.

## Under the binding

With `requireNotifierHandedOver` holding, the notifier's CTM is the real CTM, and the real CTM's
`getChainAdmin(id)` is the diamond's `s.admin`. So the only per-chain writer of the live entry is
the diamond's admin (`BoundNotifierAdminIsDiamondAdmin`). Such a step is a
`TimedStep.setUpgradeTimestamp` of `Specs/UpgradeTiming.lean` (`BoundStepRefinesUpgradeTiming`),
so that model's `NotifierWrittenOnlyByItsChainAdmin` applies to it
(`BoundLiveEntryWrittenOnlyByItsChainAdmin`). In the whole registry shape, every step that
changes a live entry is that one or a step by the executor (`BoundLiveEntryWritersV35`).

Both premises are load-bearing. Once a leg re-binds the notifier to a contract that names
`X ≠ s.admin`, `X` schedules the chain and opens its validator gate
(`RebindNotifierCtmLetsForeignAdminSchedule`). The same holds after a repoint
(`RepointLetsForeignAdminSchedule`), which a post-engine read would have caught. A repoint to a
notifier with the same holders is caught by neither read time (`SameHolderRepointPassesBothReads`).
`BoundRefinementPremisesAreLoadBearing` shows that such a step is no admin step of
`Specs/UpgradeTiming.lean`, with either premise dropped.
`BoundPremisesSatisfiable` shows the premises of the bound results hold together.
-/

namespace Contracts.NotifierBindingV35

open Contracts.ChainTypeManager

/-! ## What the post-check reads -/

/-- **THE DOMAIN-HOLDERS TUPLE READS NONE OF THE BINDING.** Two states that agree on the
`ProxyAdmin`'s owner, the CTM's owner, nominee and admin, and notifier `sn`'s owner, nominee and
admin have the same holders tuple for `sn` (`ProxyUpgradeExecutorBase.sol:109-139`). In
particular the CTM's `serverNotifierAddress`, every notifier's `chainTypeManager`, schedule and
checkers, and every other notifier, are not read. -/
def Properties.DomainHoldersIgnoreBinding : Prop :=
  ∀ (s t : State) (pa sn : Address),
    t.paOwner pa = s.paOwner pa → t.ctmOwner = s.ctmOwner → t.ctmPending = s.ctmPending →
    t.ctmAdmin = s.ctmAdmin → (t.notifiers sn).owner = (s.notifiers sn).owner →
    (t.notifiers sn).pending = (s.notifiers sn).pending →
    t.proxyAdminOf sn = s.proxyAdminOf sn →
    holders t pa sn = holders s pa sn

/-- **EXACTLY WHAT THE DOMAIN-HOLDERS CHECK COMPARES.** For states `s` before and `s'` after
the engine:
* the comparison of the tuples themselves (`h = id`) holds iff the `ProxyAdmin`'s owner and the
  CTM's owner, nominee and proxy admin are unchanged and, when the CTM pointed at a nonzero
  notifier before the engine, that notifier's owner, nominee and proxy admin are unchanged
  (`ProxyUpgradeExecutorBase.sol:71-74, :90-92, :109-139`);
* when it holds, the check passes for every hash `h`;
* a hash `h` that passes while it fails collides on two distinct tuples.

Neither `s'.ctmNotifier` nor any notifier's `chainTypeManager`, schedule or checker occurs. -/
def Properties.PostCheckIsHolderReadingsEqual : Prop :=
  ∀ (s s' : State) (pa : Address),
    (PostCheck id pa s s' ↔
      (s'.paOwner pa = s.paOwner pa ∧ s'.ctmOwner = s.ctmOwner ∧ s'.ctmPending = s.ctmPending ∧
        s'.ctmAdmin = s.ctmAdmin ∧
        (s.ctmNotifier ≠ 0 →
          (s'.notifiers s.ctmNotifier).owner = (s.notifiers s.ctmNotifier).owner ∧
          (s'.notifiers s.ctmNotifier).pending = (s.notifiers s.ctmNotifier).pending ∧
          s'.proxyAdminOf s.ctmNotifier = s.proxyAdminOf s.ctmNotifier))) ∧
    (PostCheck id pa s s' → ∀ (H : Type) (h : Holders → H), PostCheck h pa s s') ∧
    (∀ (H : Type) (h : Holders → H), PostCheck h pa s s' → ¬ PostCheck id pa s s' →
      ∃ a b : Holders, a ≠ b ∧ h a = h b)

/-! ## (a) An engine leg re-points the CTM's notifier -/

/-- **AN ENGINE LEG CAN RE-POINT THE CTM AT ANY NOTIFIER, AND THE EXECUTOR ACCEPTS IT.** For the
executor `exec` that owns the CTM, any `ProxyAdmin` `pa`, any address `N'`, and any hash `h`:
* the one-call leg `setServerNotifier(N')` succeeds and passes the domain-holders check;
* afterwards the entry every diamond reads is `N'`'s, whatever `N'` holds;
* if `N'` is not the original notifier, `requireNotifierHandedOver` for the original notifier
  fails, for every executor;
* `requireNotifierHandedOver` can hold afterwards only for `N'` itself, and only if `N'` already
  pointed at the CTM, was owned by the executor named, and had no nomination.

This refutes `ProxyUpgradeExecutorBase.sol:32-36` read as a statement about the notifier the
CTM points at after the leg. -/
def Properties.EngineRepointsServerNotifier : Prop :=
  ∀ (E : Env) (s : State) (exec pa N' : Address) (H : Type) (h : Holders → H),
    s.ctmOwner = exec →
    LegAccepted E h exec pa s [.setServerNotifier N'] { s with ctmNotifier := N' } ∧
    (∀ id v, liveEntry { s with ctmNotifier := N' } id v = (s.notifiers N').entry id v) ∧
    (N' ≠ s.ctmNotifier →
      ∀ exec', ¬ NotifierHandedOver E { s with ctmNotifier := N' } s.ctmNotifier exec') ∧
    (∀ sn' exec', NotifierHandedOver E { s with ctmNotifier := N' } sn' exec' →
      sn' = N' ∧ (s.notifiers N').ctm = E.ctm ∧ (s.notifiers N').owner = exec' ∧
      (s.notifiers N').pending = 0)

/-- **READING THE NOTIFIER AFTER THE ENGINE CATCHES A REPOINT EXACTLY WHEN THE NEW NOTIFIER'S
HOLDERS DIFFER.** With the comparison done on the tuples (`h = id`), the post-read variant of the
check accepts the repoint to `N'` iff `N'` and the original notifier have the same holder
component: both zero, or both nonzero with the same owner, nominee and proxy admin. The source's
pre-engine read accepts every repoint (`EngineRepointsServerNotifier`). -/
def Properties.PostReadCatchesOnlyHolderChange : Prop :=
  ∀ (s : State) (pa N' : Address),
    PostCheckAfterRead id pa s { s with ctmNotifier := N' } ↔
      (holders s pa N').notifier = (holders s pa s.ctmNotifier).notifier

/-! ## (b) An engine leg re-binds the notifier's CTM -/

/-- **AN ENGINE LEG CAN RE-BIND THE NOTIFIER TO ANY CTM, AND NO READ TIME CATCHES IT.** For the
executor `exec` that owns the live notifier, any nonzero `C'`, any `ProxyAdmin` `pa` and any hash
`h`: the one-call leg `setChainTypeManager(C')` on the live notifier succeeds and passes the
domain-holders check, and would pass it with the notifier re-read after the engine too. The CTM
still points at the same notifier and every live entry is unchanged, but the notifier now asks
`C'` for chain admins. If `C'` is not the CTM, `requireNotifierHandedOver` fails for every
notifier and executor. -/
def Properties.EngineRebindsNotifierCtm : Prop :=
  ∀ (E : Env) (s : State) (exec pa C' : Address) (H : Type) (h : Holders → H),
    (s.notifiers s.ctmNotifier).owner = exec → C' ≠ 0 →
    ∃ s', LegAccepted E h exec pa s [.setChainTypeManager s.ctmNotifier C'] s' ∧
      PostCheckAfterRead h pa s s' ∧
      s'.ctmNotifier = s.ctmNotifier ∧ (s'.notifiers s.ctmNotifier).ctm = C' ∧
      (∀ id v, liveEntry s' id v = liveEntry s id v) ∧
      (C' ≠ E.ctm → ∀ sn exec', ¬ NotifierHandedOver E s' sn exec')

/-! ## What the check does catch -/

/-- **THE CHECK SEES A NOMINATION ON THE NOTIFIER THE CTM POINTED AT.** For the executor `exec`
that owns the live notifier, when that notifier's address is nonzero: the one-call leg
`transferOwnership(o)` on it, with `o` not the current nominee, succeeds as a call but changes
the holders tuple. So the comparison of the tuples rejects it, and a hash `h` accepts it only by
colliding on those two distinct tuples (`ProxyUpgradeExecutorBase.sol:129-137`). -/
def Properties.PostCheckCatchesNotifierNomination : Prop :=
  ∀ (E : Env) (s : State) (exec pa o : Address),
    (s.notifiers s.ctmNotifier).owner = exec → s.ctmNotifier ≠ 0 →
    o ≠ (s.notifiers s.ctmNotifier).pending →
    ∃ s', Leg E s exec [.notifierTransferOwnership s.ctmNotifier o] s' ∧
      holders s' pa s.ctmNotifier ≠ holders s pa s.ctmNotifier ∧
      ¬ PostCheck id pa s s' ∧
      ∀ (H : Type) (h : Holders → H), LegAccepted E h exec pa s
          [.notifierTransferOwnership s.ctmNotifier o] s' →
        h (holders s' pa s.ctmNotifier) = h (holders s pa s.ctmNotifier)

/-! ## (c) Who writes an entry, and who moves the pointers -/

/-- **AN ENTRY OF A NOTIFIER CHANGES ONLY BY ITS CHAIN ADMIN, AS ITS CTM NAMES IT, OR BY AN
IMPLEMENTATION SWAP.** A step that changes entry `(id, v)` of notifier `n` is either
`setUpgradeTimestamp(id, ts)` on `n` by `n.chainTypeManager.getChainAdmin(id)`, with
`v = n.chainTypeManager.getProtocolVersion(id)`, `ts ≠ 0` and the new entry `ts`
(`ServerNotifier.sol:43-48, :113-132`), or a code swap of `n` by whoever controls `n`'s
`ProxyAdmin`. No step by the notifier's own owner writes an entry. -/
def Properties.NotifierEntryWritersV35 : Prop :=
  ∀ (E : Env) (s s' : State) (caller : Address) (op : Op) (n : Address) (id : ChainId) (v : ℕ),
    Step E s caller op s' → (s'.notifiers n).entry id v ≠ (s.notifiers n).entry id v →
    (∃ ts, op = .setUpgradeTimestamp n id ts ∧ caller = E.adminVia (s.notifiers n).ctm id ∧
      v = E.pvVia (s.notifiers n).ctm id ∧ ts ≠ 0 ∧ (s'.notifiers n).entry id v = ts) ∨
    (∃ st, op = .upgradeNotifierProxy n st ∧ caller = s.paOwner (s.proxyAdminOf n))

/-- **THE TWO POINTERS MOVE ONLY BY THEIR OWNERS OR BY A CODE SWAP.** A step that changes the
CTM's `serverNotifierAddress` is `setServerNotifier` by the CTM's owner
(`ChainTypeManager.sol:387-391`) or a CTM code swap by whoever controls the CTM's `ProxyAdmin`.
A step that changes notifier `n`'s `chainTypeManager` is `setChainTypeManager` on `n` by `n`'s
owner, to a nonzero value (`ServerNotifier.sol:67-72`), or a code swap of `n` by whoever
controls `n`'s `ProxyAdmin`. -/
def Properties.NotifierBindingWritersV35 : Prop :=
  ∀ (E : Env) (s s' : State) (caller : Address) (op : Op),
    Step E s caller op s' →
    (s'.ctmNotifier ≠ s.ctmNotifier →
      (op = .setServerNotifier s'.ctmNotifier ∧ caller = s.ctmOwner) ∨
      (∃ o p, op = .upgradeCtmProxy s'.ctmNotifier o p ∧ caller = s.paOwner s.ctmAdmin)) ∧
    (∀ n, (s'.notifiers n).ctm ≠ (s.notifiers n).ctm →
      (op = .setChainTypeManager n (s'.notifiers n).ctm ∧ caller = (s.notifiers n).owner ∧
        (s'.notifiers n).ctm ≠ 0) ∨
      (∃ st, op = .upgradeNotifierProxy n st ∧ caller = s.paOwner (s.proxyAdminOf n)))

/-- **THE ENTRY THE DIAMOND READS CHANGES ONLY BY ITS CHAIN ADMIN, AS THE LIVE NOTIFIER'S CTM
NAMES IT, OR BY A POINTER OR CODE CHANGE.** A step that changes `liveEntry id v` is one of:
`setUpgradeTimestamp(id, ts)` on the live notifier by its CTM's `getChainAdmin(id)`, at that
CTM's `getProtocolVersion(id)`, to `ts ≠ 0`; a code swap of the live notifier by whoever
controls its `ProxyAdmin`; `setServerNotifier` by the CTM's owner; or a CTM code swap by whoever
controls the CTM's `ProxyAdmin`. -/
def Properties.LiveEntryWritersV35 : Prop :=
  ∀ (E : Env) (s s' : State) (caller : Address) (op : Op) (id : ChainId) (v : ℕ),
    Step E s caller op s' → liveEntry s' id v ≠ liveEntry s id v →
    (∃ ts, op = .setUpgradeTimestamp s.ctmNotifier id ts ∧
      caller = E.adminVia (s.notifiers s.ctmNotifier).ctm id ∧
      v = E.pvVia (s.notifiers s.ctmNotifier).ctm id ∧ ts ≠ 0 ∧ liveEntry s' id v = ts) ∨
    (∃ st, op = .upgradeNotifierProxy s.ctmNotifier st ∧
      caller = s.paOwner (s.proxyAdminOf s.ctmNotifier)) ∨
    (∃ n, op = .setServerNotifier n ∧ caller = s.ctmOwner) ∨
    (∃ n o p, op = .upgradeCtmProxy n o p ∧ caller = s.paOwner s.ctmAdmin)

/-- **THE BINDING IS MOVED ONLY BY ITS HOLDERS.** A step from a state where
`requireNotifierHandedOver` holds for `(sn, exec)` to one where it fails is a call by the
notifier's owner `exec`, by the CTM's owner, or by whoever controls the `ProxyAdmin` of the
notifier or of the CTM. The last disjunct is the zero address accepting the empty nomination,
which no transaction's sender is. -/
def Properties.BindingMovedOnlyByItsHolders : Prop :=
  ∀ (E : Env) (s s' : State) (caller : Address) (op : Op) (sn exec : Address),
    NotifierHandedOver E s sn exec → Step E s caller op s' → ¬ NotifierHandedOver E s' sn exec →
    caller = exec ∨ caller = s.ctmOwner ∨ caller = s.paOwner (s.proxyAdminOf sn) ∨
      caller = s.paOwner s.ctmAdmin ∨ caller = 0

/-- **IN THE REGISTRY SHAPE, ONLY THE EXECUTOR LEAVES IT.** From a state in the CTM-domain
registry shape for `(sn, exec, pa)`, every sequence of successful calls none of which is by
`exec` or by the zero address ends in the shape: the CTM still points at `sn`, `sn` still asks
the CTM, and every authority is still the executor's. Chain admins, the notifier's would-be
nominees and everyone else are among those callers. An engine leg is a sequence of calls by
`exec`, and `EngineRepointsServerNotifier` / `EngineRebindsNotifierCtm` are accepted legs that
leave the shape. -/
def Properties.ShapeKeptByOtherCallers : Prop :=
  ∀ (E : Env) (s s' : State) (cs : List (Address × Op)) (sn exec pa : Address),
    CtmDomainShape E s sn exec pa → Run E s cs s' →
    (∀ c ∈ cs, c.1 ≠ exec ∧ c.1 ≠ 0) →
    CtmDomainShape E s' sn exec pa

/-! ## (d) Under the binding -/

/-- **UNDER THE BINDING, THE NOTIFIER'S CHAIN ADMIN IS THE DIAMOND'S ADMIN.** If
`requireNotifierHandedOver` holds for `sn` and the CTM's `getChainAdmin(id)` is the diamond's
`s.admin`, a successful `setUpgradeTimestamp(id, ts)` on `sn` is by `s.admin` of chain `id`, and
writes the live entry at the version the CTM reports for `id`. -/
def Properties.BoundNotifierAdminIsDiamondAdmin : Prop :=
  ∀ (E : Env) (s s' : State) (sn exec caller : Address) (id : ChainId) (ts : ℕ),
    CtmAnswersDiamondAdmin E → NotifierHandedOver E s sn exec →
    Step E s caller (.setUpgradeTimestamp sn id ts) s' →
    caller = E.diamondAdmin id ∧ liveEntry s' id (E.pvVia E.ctm id) = ts

/-- **UNDER THE BINDING, A SCHEDULING STEP IS A STEP OF `Specs/UpgradeTiming.lean`.** With the
premises of `BoundNotifierAdminIsDiamondAdmin`, and a timed system `ts` that agrees with `s` at
chain `id` (`AgreesAt`), a successful `setUpgradeTimestamp(id, t)` on the bound notifier is a
`TimedStep.setUpgradeTimestamp id caller t` from `ts`, whose resulting schedule is the new live
schedule. -/
def Properties.BoundStepRefinesUpgradeTiming : Prop :=
  ∀ (E : Env) (T : TimedConfig) (ts : TimedSys) (s s' : State) (sn exec caller : Address)
    (id : ChainId) (t : ℕ),
    CtmAnswersDiamondAdmin E → NotifierHandedOver E s sn exec → AgreesAt E ts s id →
    Step E s caller (.setUpgradeTimestamp sn id t) s' →
    TimedStep T ts (.setUpgradeTimestamp id caller t) { ts with notifier := liveEntry s' }

/-- **UNDER THE BINDING, `NotifierWrittenOnlyByItsChainAdmin` HOLDS FOR THE LIVE ENTRY.** With the
binding, `CtmAnswersDiamondAdmin`, and `ts` agreeing with `s` at chain `id`: a
`setUpgradeTimestamp` on any notifier, for any chain, that changes the live entry `(id, v)` is by
the admin of chain `id` in `ts`, while `id` is registered at `v` there, to a nonzero time that
becomes the entry. This is the conclusion of
`Contracts.ChainTypeManager.Properties.NotifierWrittenOnlyByItsChainAdmin` for the projected
step. -/
def Properties.BoundLiveEntryWrittenOnlyByItsChainAdmin : Prop :=
  ∀ (E : Env) (T : TimedConfig) (ts : TimedSys) (s s' : State) (sn exec caller n : Address)
    (id id' : ChainId) (v t : ℕ),
    CtmAnswersDiamondAdmin E → NotifierHandedOver E s sn exec → AgreesAt E ts s id →
    Step E s caller (.setUpgradeTimestamp n id' t) s' →
    liveEntry s' id v ≠ liveEntry s id v →
    caller = (ts.aux id).admin ∧ (∃ c, ts.sys.chains id = some c ∧ c.pv = v) ∧ t ≠ 0 ∧
      liveEntry s' id v = t

/-- **IN THE REGISTRY SHAPE, A LIVE ENTRY CHANGES ONLY BY THE DIAMOND'S ADMIN OR BY THE
EXECUTOR.** With the CTM-domain shape for `(sn, exec, pa)` and `CtmAnswersDiamondAdmin`: any
step, of any kind, that changes the live entry `(id, v)` is either
`setUpgradeTimestamp(id, ts)` on `sn` by `s.admin` of chain `id`, at the version the CTM reports
for `id`, to `ts ≠ 0`, or it is a call by the executor. -/
def Properties.BoundLiveEntryWritersV35 : Prop :=
  ∀ (E : Env) (s s' : State) (sn exec pa caller : Address) (op : Op) (id : ChainId) (v : ℕ),
    CtmAnswersDiamondAdmin E → CtmDomainShape E s sn exec pa →
    Step E s caller op s' → liveEntry s' id v ≠ liveEntry s id v →
    (∃ ts, op = .setUpgradeTimestamp sn id ts ∧ caller = E.diamondAdmin id ∧
      v = E.pvVia E.ctm id ∧ ts ≠ 0 ∧ liveEntry s' id v = ts) ∨
    caller = exec

/-! ## Countermodels and witnesses -/

/-- **WITHOUT THE BINDING, A FOREIGN ADMIN SCHEDULES THE CHAIN: RE-BIND.** There is a state in
the CTM-domain registry shape (so `requireNotifierHandedOver` holds), with the CTM answering the
diamond's admin, where an engine leg `setChainTypeManager(C')` on the bound notifier is accepted
for every hash, at either read time. After it `X`, which `C'` names as chain `id`'s admin but
which is not the diamond's admin, sets chain `id`'s entry at its current version to `t`, opening
its validator gate at time `t`. That gate was closed before, and from the bound state `X` cannot
make that call. So the binding premise of `BoundNotifierAdminIsDiamondAdmin` is load-bearing. -/
def Properties.RebindNotifierCtmLetsForeignAdminSchedule : Prop :=
  ∃ (E : Env) (s0 s1 s2 : State) (exec pa sn C' X : Address) (id : ChainId) (v t : ℕ),
    CtmAnswersDiamondAdmin E ∧ CtmDomainShape E s0 sn exec pa ∧
    (∀ (H : Type) (h : Holders → H),
      LegAccepted E h exec pa s0 [.setChainTypeManager sn C'] s1 ∧ PostCheckAfterRead h pa s0 s1) ∧
    Step E s1 X (.setUpgradeTimestamp sn id t) s2 ∧
    X ≠ E.diamondAdmin id ∧ X ≠ exec ∧ v = E.pvVia E.ctm id ∧
    ValidatorGateOpen s2 id v t ∧ ¬ ValidatorGateOpen s0 id v t ∧
    ∀ s', ¬ Step E s0 X (.setUpgradeTimestamp sn id t) s'

/-- **WITHOUT THE BINDING, A FOREIGN ADMIN SCHEDULES THE CHAIN: REPOINT.** There is a state in
the CTM-domain registry shape where an engine leg `setServerNotifier(N')` is accepted for every
hash, with `N'` owned by `X` and bound to a contract naming `X` as chain `id`'s admin. `X` then
sets chain `id`'s entry on `N'` and opens its validator gate at time `t`; it could not schedule
on the bound notifier. Reading the notifier after the engine and comparing the tuples (`h = id`)
would have rejected this leg. -/
def Properties.RepointLetsForeignAdminSchedule : Prop :=
  ∃ (E : Env) (s0 s1 s2 : State) (exec pa sn N' X : Address) (id : ChainId) (v t : ℕ),
    CtmAnswersDiamondAdmin E ∧ CtmDomainShape E s0 sn exec pa ∧
    (∀ (H : Type) (h : Holders → H), LegAccepted E h exec pa s0 [.setServerNotifier N'] s1) ∧
    ¬ PostCheckAfterRead (_root_.id : Holders → Holders) pa s0 s1 ∧
    (s0.notifiers N').owner = X ∧
    Step E s1 X (.setUpgradeTimestamp N' id t) s2 ∧
    X ≠ E.diamondAdmin id ∧ X ≠ exec ∧ v = E.pvVia E.ctm id ∧
    ValidatorGateOpen s2 id v t ∧ ¬ ValidatorGateOpen s0 id v t ∧
    ∀ s', ¬ Step E s0 X (.setUpgradeTimestamp sn id t) s'

/-- **A REPOINT TO A NOTIFIER WITH THE SAME HOLDERS PASSES EITHER READ TIME.** There is a state in
the CTM-domain registry shape and an `N'` whose owner, nominee and proxy admin are the original
notifier's, but whose `chainTypeManager` is not the CTM: the leg `setServerNotifier(N')` passes
the check with the notifier read before or after the engine, for every hash, and leaves
`requireNotifierHandedOver` failing for every notifier and executor. -/
def Properties.SameHolderRepointPassesBothReads : Prop :=
  ∃ (E : Env) (s0 s1 : State) (exec pa sn N' : Address),
    CtmDomainShape E s0 sn exec pa ∧ N' ≠ sn ∧
    (∀ (H : Type) (h : Holders → H),
      LegAccepted E h exec pa s0 [.setServerNotifier N'] s1 ∧ PostCheckAfterRead h pa s0 s1) ∧
    ∀ sn' exec', ¬ NotifierHandedOver E s1 sn' exec'

/-- **BOTH PREMISES OF THE REFINEMENT ARE LOAD-BEARING.** `BoundStepRefinesUpgradeTiming` assumes
the binding and `CtmAnswersDiamondAdmin`. Drop either and there are a state `s`, a timed system
`ts` agreeing with it at chain `id`, and a successful `setUpgradeTimestamp(id, t)` by `X` on the
live notifier that changes the live entry of `id`, while `X` is not chain `id`'s admin in `ts`,
so no `TimedStep.setUpgradeTimestamp id X t` exists from `ts`, for any configuration:
* without the binding: `CtmAnswersDiamondAdmin` holds, but the live notifier asks another
  contract;
* without `CtmAnswersDiamondAdmin`: the whole registry shape holds, but the CTM's
  `getChainAdmin` does not answer the diamond's admin.

In `Specs/UpgradeTiming.lean` the only label left for such a change of the schedule is the
unguarded `swapNotifier`. -/
def Properties.BoundRefinementPremisesAreLoadBearing : Prop :=
  (∃ (E : Env) (ts : TimedSys) (s s' : State) (X : Address) (id : ChainId) (v t : ℕ),
    CtmAnswersDiamondAdmin E ∧ AgreesAt E ts s id ∧
    Step E s X (.setUpgradeTimestamp s.ctmNotifier id t) s' ∧
    liveEntry s' id v ≠ liveEntry s id v ∧ X ≠ (ts.aux id).admin ∧
    ∀ (T : TimedConfig) (ts' : TimedSys), ¬ TimedStep T ts (.setUpgradeTimestamp id X t) ts') ∧
  (∃ (E : Env) (ts : TimedSys) (s s' : State) (sn exec pa X : Address) (id : ChainId) (v t : ℕ),
    CtmDomainShape E s sn exec pa ∧ AgreesAt E ts s id ∧
    Step E s X (.setUpgradeTimestamp sn id t) s' ∧
    liveEntry s' id v ≠ liveEntry s id v ∧ X ≠ (ts.aux id).admin ∧
    ∀ (T : TimedConfig) (ts' : TimedSys), ¬ TimedStep T ts (.setUpgradeTimestamp id X t) ts')

/-- **THE BOUND RESULTS' PREMISES HOLD TOGETHER.** Some environment, state, timed system and
step satisfy every premise of `BoundStepRefinesUpgradeTiming`, `BoundLiveEntryWritersV35` and
`ShapeKeptByOtherCallers` at once: the CTM answers the diamond's admin, the state is in the
CTM-domain registry shape, the timed system agrees with it, and the chain's admin, who is
neither the executor nor zero, schedules the chain. -/
def Properties.BoundPremisesSatisfiable : Prop :=
  ∃ (E : Env) (ts : TimedSys) (s s' : State) (sn exec pa caller : Address) (id : ChainId)
    (t : ℕ),
    CtmAnswersDiamondAdmin E ∧ CtmDomainShape E s sn exec pa ∧ AgreesAt E ts s id ∧
    Step E s caller (.setUpgradeTimestamp sn id t) s' ∧ caller ≠ exec ∧ caller ≠ 0 ∧
    liveEntry s' id (E.pvVia E.ctm id) ≠ liveEntry s id (E.pvVia E.ctm id)

end Contracts.NotifierBindingV35
