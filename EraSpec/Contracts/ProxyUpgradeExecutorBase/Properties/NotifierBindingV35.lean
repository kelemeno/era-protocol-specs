import EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.NotifierBindingV35
import EraSpec.Core.Headline

/-!
# Properties: the ServerNotifier binding at `b17415d20`

Statements only; the model is `Specs/NotifierBindingV35.lean` and the proofs are
`Proofs/NotifierBindingV35.lean`. Source: era-contracts `draft/v0.35.0` at
`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`.

## The claim checked

`ProxyUpgradeExecutorBase.sol:34-41` says the executor checks, after the engine returns, that
"the CTM's owner, pending owner, admin, proxy admin and ServerNotifier, and that ServerNotifier's
owner, pending owner, proxy admin and CTM" are unchanged, and that "a re-pointed ServerNotifier is
a `forward`, not a leg".

* **What the comparison reads** (`DomainHoldersReadOnly`, `PostCheckComparesExactly`): exactly
  the `ProxyAdmin`'s owner, the CTM's owner, pending owner, `admin()` and `getProxyAdmin`
  reading, the CTM's `serverNotifierAddress`, and, for a nonzero notifier, whether the
  `ProxyAdmin` administers it and its owner, pending owner and `chainTypeManager`. When these
  agree before and after, the check passes for every hash; when they do not, a hash passes only
  by colliding on the two readings.
* **Both pointers of the binding are compared** (`PostCheckRejectsRepoint`,
  `PostCheckRejectsRebind`, witnessed by `EngineRepointAndRebindRejected`).
* **An accepted leg keeps the registry shape** (`AcceptedLegKeepsShape`; for an arbitrary hash
  `AcceptedLegKeepsShapeOrCollision`, and for the source's two `keccak256` calls
  `AcceptedLegKeepsShapeOrKeccakCollision`). This needs the check before the engine
  (`PreCheckIsLoadBearing`). `AcceptedLegWitness` is an accepted leg with an effect: the
  comparison reads neither the notifier's checkers nor the CTM's `pendingAdmin`.
* **Along runs** (`ShapeKeptAlongDomainRuns`, `ShapeKeptAlongDomainRunsOrCollision`): calls by
  anyone but the executor and the zero address, accepted engine legs and the executor's
  `acceptCTMOwnership` keep the shape. A call the executor sends outside a leg, as `forward` does,
  can move either pointer (`CallsOutsideLegsMoveTheBinding`).

## Who moves the binding, and who writes an entry

* **Per notifier** (`NotifierEntryWritersV35`): an entry `(id, v)` of notifier `n` changes
  only by `setUpgradeTimestamp(id, ts)` from `n.chainTypeManager.getChainAdmin(id)`, with
  `v = n.chainTypeManager.getProtocolVersion(id)` and `ts ≠ 0`, or by an implementation swap
  from whoever controls `n`'s `ProxyAdmin`.
* **The pointers** (`NotifierBindingWritersV35`): the CTM's by its owner or a CTM code swap;
  a notifier's `chainTypeManager` by its owner or a code swap of it.
* **The entry the diamond reads** (`LiveEntryWritersV35`) additionally changes when the CTM's
  owner calls `setServerNotifier`, or the CTM's `ProxyAdmin` owner swaps the CTM's code.
* **The binding** (`BindingMovedOnlyByItsHolders`, `ShapeKeptByOtherCallers`).

## Under the binding

With `requireNotifierHandedOver` holding, the notifier's CTM is the real CTM, and under
`CtmAnswersDiamondAdmin` the real CTM's `getChainAdmin(id)` is the diamond's `s.admin`. So a
successful `setUpgradeTimestamp(id, ts)` on the bound notifier is by the diamond's admin
(`BoundNotifierAdminIsDiamondAdmin`). Such a step is a
`TimedStep.setUpgradeTimestamp` of `Specs/UpgradeTiming.lean` (`BoundStepRefinesUpgradeTiming`),
so that model's `NotifierWrittenOnlyByItsChainAdmin` applies to it
(`BoundLiveEntryWrittenOnlyByItsChainAdmin`). In the whole registry shape, every step that
changes a live entry is that one or a step by the executor (`BoundLiveEntryWritersV35`), and
that stays so after any run of the domain (`OnlyDiamondAdminSchedulesAlongDomainRuns`, witnessed
by `OnlyDiamondAdminSchedulesWitness`). Both premises are load-bearing
(`BoundRefinementPremisesAreLoadBearing`), and they hold together (`BoundPremisesSatisfiable`).
`Specs/UpgradeTiming.lean` is pinned at `e561b9cc2`; these results relate its model to this one.
-/

namespace Contracts.NotifierBindingV35

open Contracts.ChainTypeManager (Address ChainId TimedSys TimedConfig TimedStep)

/-! ## What the post-check reads -/

/-- **THE DOMAIN-HOLDERS READING DEPENDS ONLY ON THE HOLDERS.** Two states that agree on the
`ProxyAdmin` `pa`'s owner, the CTM's owner, pending owner, `admin`, admin slot and
`serverNotifierAddress`, and on that notifier's owner, pending owner, admin slot and
`chainTypeManager`, give the same `domainHolders` reading (`ProxyUpgradeExecutorBase.sol:118-148`),
a revert included. In particular the CTM's `pendingAdmin`, every notifier's schedule and checkers,
every other notifier and every other `ProxyAdmin`'s owner are not read. -/
def Properties.DomainHoldersReadOnly : Prop :=
  ∀ (s t : State) (pa : Address),
    t.paOwner pa = s.paOwner pa → t.ctm.owner = s.ctm.owner →
    t.ctm.pendingOwner = s.ctm.pendingOwner → t.ctm.admin = s.ctm.admin →
    t.ctm.adminSlot = s.ctm.adminSlot → t.ctm.serverNotifier = s.ctm.serverNotifier →
    (t.notifiers s.ctm.serverNotifier).owner = (s.notifiers s.ctm.serverNotifier).owner →
    (t.notifiers s.ctm.serverNotifier).pendingOwner =
      (s.notifiers s.ctm.serverNotifier).pendingOwner →
    (t.notifiers s.ctm.serverNotifier).adminSlot = (s.notifiers s.ctm.serverNotifier).adminSlot →
    (t.notifiers s.ctm.serverNotifier).chainTypeManager =
      (s.notifiers s.ctm.serverNotifier).chainTypeManager →
    domainHolders t pa = domainHolders s pa

/-- **EXACTLY WHAT THE DOMAIN-HOLDERS CHECK COMPARES.** Let `s` be the state before the engine,
with its reading `t` defined (`domainHolders s pa = some t`), and `s'` the state after. Call
*the holders agree* the conjunction: the `ProxyAdmin`'s owner and the CTM's owner, pending owner
and `admin` are unchanged, `getProxyAdmin(ctm)` reads the same (`ctmProxyAdminSeen`), the CTM's
`serverNotifierAddress` is unchanged and, when it is nonzero, `pa` still administers that
notifier and its owner, pending owner and `chainTypeManager` are unchanged
(`ProxyUpgradeExecutorBase.sol:118-148`). Then:
* the comparison of the tuples themselves passes iff the holders agree;
* if the holders agree, the check passes for every hash `h`;
* if they do not, a hash `h` passes only if `s'` has a reading `t'` with `t' ≠ t` and
  `h t' = h t`. -/
def Properties.PostCheckComparesExactly : Prop :=
  ∀ (s s' : State) (pa : Address) (t : Holders), domainHolders s pa = some t →
    let agree : Prop :=
      s'.paOwner pa = s.paOwner pa ∧ s'.ctm.owner = s.ctm.owner ∧
      s'.ctm.pendingOwner = s.ctm.pendingOwner ∧ s'.ctm.admin = s.ctm.admin ∧
      ctmProxyAdminSeen s'.ctm pa = ctmProxyAdminSeen s.ctm pa ∧
      s'.ctm.serverNotifier = s.ctm.serverNotifier ∧
      (s.ctm.serverNotifier ≠ 0 →
        (s'.notifiers s.ctm.serverNotifier).adminSlot = pa ∧
        (s'.notifiers s.ctm.serverNotifier).owner = (s.notifiers s.ctm.serverNotifier).owner ∧
        (s'.notifiers s.ctm.serverNotifier).pendingOwner =
          (s.notifiers s.ctm.serverNotifier).pendingOwner ∧
        (s'.notifiers s.ctm.serverNotifier).chainTypeManager =
          (s.notifiers s.ctm.serverNotifier).chainTypeManager)
    (PostCheck (fun x : Holders => x) pa s s' ↔ agree) ∧
    (agree → ∀ (H : Type) (h : Holders → H), PostCheck h pa s s') ∧
    (¬ agree → ∀ (H : Type) (h : Holders → H), PostCheck h pa s s' →
      ∃ t', domainHolders s' pa = some t' ∧ t' ≠ t ∧ h t' = h t)

/-! ## Both pointers of the binding are compared -/

/-- **A RE-POINTED SERVERNOTIFIER FAILS THE COMPARISON.** If the CTM's `serverNotifierAddress`
after the engine differs from before, a hash `h` passes the check only if the reading after,
`t'`, differs from the reading before, `t`, and `h t' = h t`. With `h = id` that is impossible,
so the comparison of the tuples rejects the leg (`ProxyUpgradeExecutorBase.sol:123, :131,
:96-98`). -/
def Properties.PostCheckRejectsRepoint : Prop :=
  ∀ (s s' : State) (pa : Address) (t : Holders), domainHolders s pa = some t →
    s'.ctm.serverNotifier ≠ s.ctm.serverNotifier →
    ∀ (H : Type) (h : Holders → H), PostCheck h pa s s' →
      ∃ t', domainHolders s' pa = some t' ∧ t' ≠ t ∧ h t' = h t

/-- **A RE-BOUND SERVERNOTIFIER FAILS THE COMPARISON.** If the CTM points at the same nonzero
notifier before and after the engine, and that notifier's `chainTypeManager` changed, a hash `h`
passes the check only by colliding on the two readings, as in `PostCheckRejectsRepoint`
(`ProxyUpgradeExecutorBase.sol:145`). -/
def Properties.PostCheckRejectsRebind : Prop :=
  ∀ (s s' : State) (pa : Address) (t : Holders), domainHolders s pa = some t →
    s.ctm.serverNotifier ≠ 0 → s'.ctm.serverNotifier = s.ctm.serverNotifier →
    (s'.notifiers s.ctm.serverNotifier).chainTypeManager ≠
      (s.notifiers s.ctm.serverNotifier).chainTypeManager →
    ∀ (H : Type) (h : Holders → H), PostCheck h pa s s' →
      ∃ t', domainHolders s' pa = some t' ∧ t' ≠ t ∧ h t' = h t

/-! ## An accepted leg keeps the registry shape -/

/-- **AN ACCEPTED ENGINE LEG KEEPS THE REGISTRY SHAPE.** From a state in the CTM-domain registry
shape for notifier `sn`, executor `exec` and `ProxyAdmin` `pa`, every engine leg that the
executor accepts with the comparison of the tuples themselves (`h = id`) ends in that shape:
`requireNotifierHandedOver` still holds for `sn` and `exec`, and the CTM, `pa` and both proxies
are still the executor's. The leg's calls may be anything. -/
def Properties.AcceptedLegKeepsShape : Prop :=
  ∀ (E : Env) (s s' : State) (cs : List (Address × Op)) (sn exec pa : Address),
    CtmDomainShape E s sn exec pa → LegAccepted E (fun x : Holders => x) pa s cs s' →
    CtmDomainShape E s' sn exec pa

/-- **FOR ANY HASH: THE SHAPE, OR A COLLISION ON THE LEG'S OWN READINGS.** As
`AcceptedLegKeepsShape`, for an arbitrary hash `h`: the leg ends in the shape, or the readings
`t` before and `t'` after the engine are distinct and `h t' = h t`. -/
def Properties.AcceptedLegKeepsShapeOrCollision : Prop :=
  ∀ (E : Env) (H : Type) (h : Holders → H) (s s' : State) (cs : List (Address × Op))
    (sn exec pa : Address),
    CtmDomainShape E s sn exec pa → LegAccepted E h pa s cs s' →
    CtmDomainShape E s' sn exec pa ∨
      ∃ t t', domainHolders s pa = some t ∧ domainHolders s' pa = some t' ∧ t' ≠ t ∧ h t' = h t

/-- **A COLLISION OF THE SOURCE'S HASH IS A KECCAK COLLISION ON NAMED PREIMAGES.** For any
function `k` on lists of 32-byte words, if `domainHash k` (`_domainHolders`'s two `keccak256`
calls over `abi.encode`, `ProxyUpgradeExecutorBase.sol:124-147`) takes the same value on two
distinct tuples `t'` and `t`, then `k` takes the same value on two distinct lists: the outer
preimages `domainPreimage k t'` and `domainPreimage k t`, or the inner preimages
`innerPreimage t'` and `innerPreimage t`. -/
def Properties.DomainHashCollisionIsKeccakCollision : Prop :=
  ∀ (k : List Address → Address) (t t' : Holders), t' ≠ t →
    domainHash k t' = domainHash k t →
    (domainPreimage k t' ≠ domainPreimage k t ∧
        k (domainPreimage k t') = k (domainPreimage k t)) ∨
      (innerPreimage t' ≠ innerPreimage t ∧ k (innerPreimage t') = k (innerPreimage t))

/-- **WITH THE SOURCE'S HASH: THE SHAPE, OR A KECCAK COLLISION.** As
`AcceptedLegKeepsShapeOrCollision`, with the comparison done by `domainHash k`: the leg ends in
the shape, or `k` takes the same value on two distinct preimages built from the readings `t`
before and `t'` after the engine, as in `DomainHashCollisionIsKeccakCollision`. -/
@[headline] def Properties.AcceptedLegKeepsShapeOrKeccakCollision : Prop :=
  ∀ (E : Env) (k : List Address → Address) (s s' : State) (cs : List (Address × Op))
    (sn exec pa : Address),
    CtmDomainShape E s sn exec pa → LegAccepted E (domainHash k) pa s cs s' →
    CtmDomainShape E s' sn exec pa ∨
      ∃ t t', domainHolders s pa = some t ∧ domainHolders s' pa = some t' ∧
        ((domainPreimage k t' ≠ domainPreimage k t ∧
            k (domainPreimage k t') = k (domainPreimage k t)) ∨
          (innerPreimage t' ≠ innerPreimage t ∧ k (innerPreimage t') = k (innerPreimage t)))

/-! ## Runs of the CTM domain -/

/-- **CALLS BY ANYONE ELSE KEEP THE SHAPE.** From a state in the CTM-domain registry shape for
`(sn, exec, pa)`, every sequence of successful calls none of which is by `exec` or by the zero
address ends in the shape. Chain admins, the CTM's admin role, the notifier's would-be nominees
and everyone else are among those callers. -/
def Properties.ShapeKeptByOtherCallers : Prop :=
  ∀ (E : Env) (s s' : State) (cs : List (Address × Op)) (sn exec pa : Address),
    CtmDomainShape E s sn exec pa → Run E s cs s' →
    (∀ c ∈ cs, c.1 ≠ exec ∧ c.1 ≠ 0) →
    CtmDomainShape E s' sn exec pa

/-- **ALONG A RUN OF THE DOMAIN, ONLY A COLLISION ON A LEG'S READINGS LEAVES THE SHAPE.** From a
state in the CTM-domain registry shape for `(sn, exec, pa)`, every `DomainRun` (calls by anyone
but `exec` and the zero address, engine legs the executor accepts with hash `h`, and the
executor's `acceptCTMOwnership`) ends in the shape, or one of the run's own legs has distinct
readings `before ≠ after` with `h after = h before`. -/
def Properties.ShapeKeptAlongDomainRunsOrCollision : Prop :=
  ∀ (E : Env) (H : Type) (h : Holders → H) (s s' : State) (es : List DomainEvent)
    (sn exec pa : Address),
    CtmDomainShape E s sn exec pa → DomainRun E h exec pa s es s' →
    CtmDomainShape E s' sn exec pa ∨
      ∃ cs t t', DomainEvent.leg cs t t' ∈ es ∧ t' ≠ t ∧ h t' = h t

/-- **ALONG A RUN OF THE DOMAIN, THE SHAPE IS KEPT.** As `ShapeKeptAlongDomainRunsOrCollision`,
with the legs' comparison done on the tuples themselves (`h = id`): the run ends in the shape. -/
def Properties.ShapeKeptAlongDomainRuns : Prop :=
  ∀ (E : Env) (s s' : State) (es : List DomainEvent) (sn exec pa : Address),
    CtmDomainShape E s sn exec pa → DomainRun E (fun x : Holders => x) exec pa s es s' →
    CtmDomainShape E s' sn exec pa

/-! ## Who writes an entry, and who moves the pointers -/

/-- **AN ENTRY OF A NOTIFIER CHANGES ONLY BY ITS CHAIN ADMIN, AS ITS CTM NAMES IT, OR BY AN
IMPLEMENTATION SWAP.** A step that changes entry `(id, v)` of notifier `n` is either
`setUpgradeTimestamp(id, ts)` on `n` by `n.chainTypeManager.getChainAdmin(id)`, with
`v = n.chainTypeManager.getProtocolVersion(id)`, `ts ≠ 0` and the new entry `ts`
(`ServerNotifier.sol:43-48, :113-132`), or a code swap of `n`, leaving its new storage, by
whoever controls `n`'s `ProxyAdmin`. -/
def Properties.NotifierEntryWritersV35 : Prop :=
  ∀ (E : Env) (s s' : State) (caller : Address) (op : Op) (n : Address) (id : ChainId) (v : ℕ),
    Step E s caller op s' → (s'.notifiers n).entry id v ≠ (s.notifiers n).entry id v →
    (∃ ts, op = .setUpgradeTimestamp n id ts ∧
      caller = E.adminVia (s.notifiers n).chainTypeManager id ∧
      v = E.pvVia (s.notifiers n).chainTypeManager id ∧ ts ≠ 0 ∧
      (s'.notifiers n).entry id v = ts) ∨
    (op = .upgradeNotifierProxy n (s'.notifiers n) ∧
      caller = s.paOwner (s.notifiers n).adminSlot)

/-- **THE TWO POINTERS MOVE ONLY BY THEIR OWNERS OR BY A CODE SWAP.** A step that changes the
CTM's `serverNotifierAddress` is `setServerNotifier` by the CTM's owner
(`ChainTypeManager.sol:387-391`) or a CTM code swap by whoever controls the CTM's `ProxyAdmin`.
A step that changes notifier `n`'s `chainTypeManager` is `setChainTypeManager` on `n` by `n`'s
owner, to a nonzero value (`ServerNotifier.sol:67-72`), or a code swap of `n` by whoever
controls `n`'s `ProxyAdmin`. -/
def Properties.NotifierBindingWritersV35 : Prop :=
  ∀ (E : Env) (s s' : State) (caller : Address) (op : Op),
    Step E s caller op s' →
    (s'.ctm.serverNotifier ≠ s.ctm.serverNotifier →
      (op = .setServerNotifier s'.ctm.serverNotifier ∧ caller = s.ctm.owner) ∨
      (op = .upgradeCtmProxy s'.ctm ∧ caller = s.paOwner s.ctm.adminSlot)) ∧
    (∀ n, (s'.notifiers n).chainTypeManager ≠ (s.notifiers n).chainTypeManager →
      (op = .setChainTypeManager n (s'.notifiers n).chainTypeManager ∧
        caller = (s.notifiers n).owner ∧ (s'.notifiers n).chainTypeManager ≠ 0) ∨
      (op = .upgradeNotifierProxy n (s'.notifiers n) ∧
        caller = s.paOwner (s.notifiers n).adminSlot))

/-- **THE ENTRY THE DIAMOND READS CHANGES ONLY BY ITS CHAIN ADMIN, AS THE LIVE NOTIFIER'S CTM
NAMES IT, OR BY A POINTER OR CODE CHANGE.** A step that changes `liveEntry id v` is one of:
`setUpgradeTimestamp(id, ts)` on the live notifier by its CTM's `getChainAdmin(id)`, at that
CTM's `getProtocolVersion(id)`, to `ts ≠ 0`; a code swap of the live notifier by whoever
controls its `ProxyAdmin`; `setServerNotifier` by the CTM's owner; or a CTM code swap by whoever
controls the CTM's `ProxyAdmin`. -/
def Properties.LiveEntryWritersV35 : Prop :=
  ∀ (E : Env) (s s' : State) (caller : Address) (op : Op) (id : ChainId) (v : ℕ),
    Step E s caller op s' → liveEntry s' id v ≠ liveEntry s id v →
    (∃ ts, op = .setUpgradeTimestamp s.ctm.serverNotifier id ts ∧
      caller = E.adminVia (s.notifiers s.ctm.serverNotifier).chainTypeManager id ∧
      v = E.pvVia (s.notifiers s.ctm.serverNotifier).chainTypeManager id ∧ ts ≠ 0 ∧
      liveEntry s' id v = ts) ∨
    (∃ st, op = .upgradeNotifierProxy s.ctm.serverNotifier st ∧
      caller = s.paOwner (s.notifiers s.ctm.serverNotifier).adminSlot) ∨
    (∃ n, op = .setServerNotifier n ∧ caller = s.ctm.owner) ∨
    (∃ c, op = .upgradeCtmProxy c ∧ caller = s.paOwner s.ctm.adminSlot)

/-- **THE BINDING IS MOVED ONLY BY ITS HOLDERS.** A step from a state where
`requireNotifierHandedOver` holds for `(sn, exec)` to one where it fails is a call by the
notifier's owner `exec`, by the CTM's owner, or by whoever controls the `ProxyAdmin` of the
notifier or of the CTM. The last disjunct is the zero address accepting the empty nomination,
which no transaction's sender is. -/
def Properties.BindingMovedOnlyByItsHolders : Prop :=
  ∀ (E : Env) (s s' : State) (caller : Address) (op : Op) (sn exec : Address),
    NotifierHandedOver E s sn exec → Step E s caller op s' → ¬ NotifierHandedOver E s' sn exec →
    caller = exec ∨ caller = s.ctm.owner ∨ caller = s.paOwner (s.notifiers sn).adminSlot ∨
      caller = s.paOwner s.ctm.adminSlot ∨ caller = 0

/-! ## Under the binding -/

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
`TimedStep.setUpgradeTimestamp id caller t` from `ts`, for every timed configuration, whose
resulting schedule is the new live schedule. -/
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
  ∀ (E : Env) (ts : TimedSys) (s s' : State) (sn exec caller n : Address)
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

/-- **ALONG A RUN OF THE DOMAIN, ONLY THE DIAMOND'S ADMIN SCHEDULES ITS CHAIN.** With
`CtmAnswersDiamondAdmin`, from a state in the CTM-domain registry shape for `(sn, exec, pa)`,
after any `DomainRun` whose legs are compared on the tuples themselves: a successful call by
anyone but the executor that changes the live entry `(id, v)` is `setUpgradeTimestamp(id, ts)` on
`sn` by `s.admin` of chain `id`, at the version the CTM reports for `id`, to `ts ≠ 0`, which
becomes the entry. -/
def Properties.OnlyDiamondAdminSchedulesAlongDomainRuns : Prop :=
  ∀ (E : Env) (s s₁ s₂ : State) (es : List DomainEvent) (sn exec pa caller : Address) (op : Op)
    (id : ChainId) (v : ℕ),
    CtmAnswersDiamondAdmin E → CtmDomainShape E s sn exec pa →
    DomainRun E (fun x : Holders => x) exec pa s es s₁ → caller ≠ exec →
    Step E s₁ caller op s₂ → liveEntry s₂ id v ≠ liveEntry s₁ id v →
    ∃ ts, op = .setUpgradeTimestamp sn id ts ∧ caller = E.diamondAdmin id ∧
      v = E.pvVia E.ctm id ∧ ts ≠ 0 ∧ liveEntry s₂ id v = ts

/-! ## Countermodels and witnesses -/

/-- **THE CHECK BEFORE THE ENGINE IS LOAD-BEARING.** `AcceptedLegKeepsShape` fails without
`PreCheck`: there is a state in the CTM-domain registry shape whose CTM `admin()` is the
`ProxyAdmin` `pa` (so `PreCheck` fails, and the source reverts at
`ProxyUpgradeExecutorBase.sol:75-77`), and the one-call leg in which the executor calls
`changeProxyAdmin` of the CTM proxy to an admin `a ≠ pa` succeeds, after which the
domain-holders comparison passes for every hash while the shape no longer holds: the CTM proxy's
admin is `a`. `getProxyAdmin(ctm)` reads `pa` before the leg (from the slot) and after it (from
the CTM's `admin`); this is the case the comment at `:72-74` describes. -/
@[countermodel] def Properties.PreCheckIsLoadBearing : Prop :=
  ∃ (E : Env) (s s' : State) (sn exec pa a : Address),
    CtmDomainShape E s sn exec pa ∧ ¬ PreCheck s pa ∧ a ≠ pa ∧
    Run E s [(exec, .changeCtmProxyAdmin a)] s' ∧ s'.ctm.adminSlot = a ∧
    (∀ (H : Type) (h : Holders → H), PostCheck h pa s s') ∧
    ¬ CtmDomainShape E s' sn exec pa

/-- **AN ACCEPTED LEG WITH AN EFFECT.** From the witness registry shape `nbState0` (notifier
`6`, executor `1`, `ProxyAdmin` `2`), the two-call leg in which the executor sets checker `9`
for version `1` on the bound notifier and then nominates `5` as the CTM's `pendingAdmin` is
accepted for every hash, and its end state differs from the start in both: the comparison reads
neither the notifier's checkers nor the CTM's `pendingAdmin`
(`ProxyUpgradeExecutorBase.sol:114-115`). So the premises of `AcceptedLegKeepsShape` hold for a
leg that changes the state. -/
@[witness] def Properties.AcceptedLegWitness : Prop :=
  ∃ s' : State,
    CtmDomainShape nbEnv nbState0 6 1 2 ∧
    (∀ (H : Type) (h : Holders → H), LegAccepted nbEnv h 2 nbState0
      [(1, .setUpgradePreconditionChecker 6 1 9), (1, .ctmSetPendingAdmin 5)] s') ∧
    s'.ctm.pendingAdmin ≠ nbState0.ctm.pendingAdmin ∧
    (s'.notifiers 6).checker 1 ≠ (nbState0.notifiers 6).checker 1

/-- **A RE-POINTING LEG AND A RE-BINDING LEG ARE REJECTED.** From the witness registry shape
`nbState0`, the one-call leg `setServerNotifier(7)` by the executor, and the one-call leg
`setChainTypeManager(9)` on the bound notifier by the executor, both succeed as calls; the
comparison of the tuples fails for each, and each leaves `requireNotifierHandedOver` failing for
`(6, 1)`. So the premises of `PostCheckRejectsRepoint` and `PostCheckRejectsRebind` are met by
legs that succeed. -/
def Properties.EngineRepointAndRebindRejected : Prop :=
  ∃ s1 s2 : State,
    CtmDomainShape nbEnv nbState0 6 1 2 ∧ PreCheck nbState0 2 ∧
    Run nbEnv nbState0 [(1, .setServerNotifier 7)] s1 ∧
    s1.ctm.serverNotifier ≠ nbState0.ctm.serverNotifier ∧
    ¬ PostCheck (fun x : Holders => x) 2 nbState0 s1 ∧ ¬ NotifierHandedOver nbEnv s1 6 1 ∧
    Run nbEnv nbState0 [(1, .setChainTypeManager 6 9)] s2 ∧
    (s2.notifiers 6).chainTypeManager ≠ (nbState0.notifiers 6).chainTypeManager ∧
    ¬ PostCheck (fun x : Holders => x) 2 nbState0 s2 ∧ ¬ NotifierHandedOver nbEnv s2 6 1

/-- **A CALL THE EXECUTOR SENDS OUTSIDE A LEG MOVES THE BINDING.** `ShapeKeptAlongDomainRuns`
leaves out calls by the executor other than engine legs and `acceptCTMOwnership`; `forward`
sends such calls. That exclusion is load-bearing: there is a state in the CTM-domain registry
shape, with the CTM answering the diamond's admin, where
* the executor's call `setServerNotifier(N')` succeeds, `requireNotifierHandedOver` then fails
  for `(sn, exec)`, and afterwards `X`, which is neither the diamond's admin nor the executor,
  sets chain `id`'s entry on `N'` at its current version to `t`, opening its validator gate at
  time `t`, closed before; and
* the executor's call `setChainTypeManager(C')` on `sn` succeeds, the binding then fails, and
  afterwards the same `X` sets that entry on `sn` itself, opening the gate.

From the shape, `X` cannot make that call on `sn`. The same calls made as an engine leg fail the
domain-holders comparison (`EngineRepointAndRebindRejected`). -/
@[countermodel] def Properties.CallsOutsideLegsMoveTheBinding : Prop :=
  ∃ (E : Env) (s0 s1 s2 s3 s4 : State) (exec pa sn N' C' X : Address) (id : ChainId) (v t : ℕ),
    CtmAnswersDiamondAdmin E ∧ CtmDomainShape E s0 sn exec pa ∧
    X ≠ E.diamondAdmin id ∧ X ≠ exec ∧ v = E.pvVia E.ctm id ∧ ¬ ValidatorGateOpen s0 id v t ∧
    (∀ s', ¬ Step E s0 X (.setUpgradeTimestamp sn id t) s') ∧
    Step E s0 exec (.setServerNotifier N') s1 ∧ ¬ NotifierHandedOver E s1 sn exec ∧
    Step E s1 X (.setUpgradeTimestamp N' id t) s2 ∧ ValidatorGateOpen s2 id v t ∧
    Step E s0 exec (.setChainTypeManager sn C') s3 ∧ ¬ NotifierHandedOver E s3 sn exec ∧
    Step E s3 X (.setUpgradeTimestamp sn id t) s4 ∧ ValidatorGateOpen s4 id v t

/-- **A RUN OF THE DOMAIN WITH A FOREIGN CALL AND AN ACCEPTED LEG.** From the witness registry
shape `nbState0`, the run in which chain `0`'s admin `3` calls `setUpgradeTimestamp(0, 12)` on
the bound notifier and then the executor applies the leg of `AcceptedLegWitness`, its two
readings being the same tuple `t`, is a `DomainRun` for every hash; its end state differs from
the start in the live schedule. So the premises of `ShapeKeptAlongDomainRuns` hold for a run
with both a foreign call and an accepted leg. -/
def Properties.DomainRunWitness : Prop :=
  ∃ (s' : State) (t : Holders),
    CtmDomainShape nbEnv nbState0 6 1 2 ∧
    (∀ (H : Type) (h : Holders → H), DomainRun nbEnv h 1 2 nbState0
      [.call 3 (.setUpgradeTimestamp 6 0 12),
        .leg [(1, .setUpgradePreconditionChecker 6 1 9), (1, .ctmSetPendingAdmin 5)] t t] s') ∧
    liveEntry s' 0 1 ≠ liveEntry nbState0 0 1

/-- **THE DIAMOND'S ADMIN SCHEDULES AFTER AN ACCEPTED LEG.** The premises of
`OnlyDiamondAdminSchedulesAlongDomainRuns` hold together with a nonempty run: from the witness
registry shape `nbState0`, after the run consisting of the leg of `AcceptedLegWitness` (accepted
on the tuples, both readings `t`), chain `0`'s admin `3`, who is not the executor, calls
`setUpgradeTimestamp(0, 12)` on the bound notifier and changes the live entry of chain `0` at
version `1`. -/
def Properties.OnlyDiamondAdminSchedulesWitness : Prop :=
  ∃ (s₁ s₂ : State) (t : Holders),
    CtmAnswersDiamondAdmin nbEnv ∧ CtmDomainShape nbEnv nbState0 6 1 2 ∧
    DomainRun nbEnv (fun x : Holders => x) 1 2 nbState0
      [.leg [(1, .setUpgradePreconditionChecker 6 1 9), (1, .ctmSetPendingAdmin 5)] t t] s₁ ∧
    Step nbEnv s₁ 3 (.setUpgradeTimestamp 6 0 12) s₂ ∧ liveEntry s₂ 0 1 ≠ liveEntry s₁ 0 1

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
    Step E s X (.setUpgradeTimestamp s.ctm.serverNotifier id t) s' ∧
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
neither the executor nor zero, schedules the chain, changing its live entry. -/
def Properties.BoundPremisesSatisfiable : Prop :=
  ∃ (E : Env) (ts : TimedSys) (s s' : State) (sn exec pa caller : Address) (id : ChainId)
    (t : ℕ),
    CtmAnswersDiamondAdmin E ∧ CtmDomainShape E s sn exec pa ∧ AgreesAt E ts s id ∧
    Step E s caller (.setUpgradeTimestamp sn id t) s' ∧ caller ≠ exec ∧ caller ≠ 0 ∧
    liveEntry s' id (E.pvVia E.ctm id) ≠ liveEntry s id (E.pvVia E.ctm id)

end Contracts.NotifierBindingV35
