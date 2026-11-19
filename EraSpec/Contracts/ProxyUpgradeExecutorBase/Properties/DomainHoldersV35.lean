import EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.DomainHoldersV35

/-!
# Properties: what the domain-holder check catches, at `b17415d`

Statements about `EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.DomainHoldersV35`. Proofs
are in `EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.DomainHoldersV35`. `leg` is the
`b17415d20` leg.

## Summary

* What a successful leg keeps (`PassingLegKeepsHolderReads`): every read `_domainHolders`
  hashes is the same before and after the engine, or the leg's own compared word lists collide
  (`HolderPairCollides`). No hash premise.
* The CTM half of the `@dev` at `ProxyUpgradeExecutorBase.sol:112-117` (`MovedCtmCaught`): if
  the `ProxyAdmin` administered the CTM proxy before the leg and the engine moved the admin
  slot away from it, the leg reverts or the compared pair collides, for any engine and with no
  premise on what the CTM's `admin()` answers afterwards. The check before the engine
  (`:75-77`) refuses a CTM whose `admin()` already is the `ProxyAdmin`
  (`CtmAdminIsProxyAdminReverts`); from such a state, moving the CTM proxy's admin leaves the
  hashed word list unchanged for every hash (`CtmAdminCheckLoadBearing`).
* The ServerNotifier half (`MovedNotifierReverts`): a nonzero notifier the CTM points at after
  the engine, not administered by the `ProxyAdmin` and without `admin()`, reverts the leg. No
  hash premise. `NotifierAdminGetterLoadBearing` shows the "without `admin()`" premise is
  needed.
* `ChainTypeManager.pendingAdmin` is not compared (`CtmPendingAdminOutsideHash`), as the
  `@dev` says.
* The rows post-check reverts a moved CTM that has a participating row and whose
  implementation has no `implementation()` (`MovedCtmWithCtmRowLegReverts`).
* The comparison with the `d9f6789` leg is a record of that older commit, in
  `EraSpec.Contracts.ProxyUpgradeExecutorBase.History.Properties.DomainHoldersD9`.

Every statement is about this model's worlds, in which what an implementation answers does
not depend on the caller (the spec's "Modelling choices").
-/

namespace Contracts.DomainHoldersV35

/-! ## (a) What a successful leg keeps -/

/-- **A SUCCESSFUL LEG KEEPS EVERY HOLDER READ, OR ITS COMPARED PAIR COLLIDES.** For every
hash function, engine and world: if the leg succeeds with post-state `w'`, then either the
compared word lists collide (`HolderPairCollides`: the two CTM tuples, or the two lists whose
hashes were compared, differ and hash equal), or all of the following hold: the `ProxyAdmin`'s
owner is unchanged; and, with a CTM, the CTM's `owner()` and `pendingOwner()`, the answer to
`admin()` sent by the executor, the answer to `admin()` sent by the `ProxyAdmin` (that is,
`getProxyAdmin(ctm)`) and the CTM's `serverNotifierAddress` are unchanged; and, if that
notifier is nonzero, its `owner()`, `pendingOwner()`, `getProxyAdmin(notifier)` and
`chainTypeManager()` are unchanged. No hash premise. -/
def Properties.PassingLegKeepsHolderReads : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (eng : Engine) (w w' : World),
    leg E B tr m eng w = some w' →
    (w'.paOwner = w.paOwner
      ∧ (B.ctm ≠ 0 →
          w'.owner B.ctm = w.owner B.ctm ∧ w'.pendingOwner B.ctm = w.pendingOwner B.ctm
          ∧ adminCall w' B.self B.ctm = adminCall w B.self B.ctm
          ∧ adminCall w' B.pa B.ctm = adminCall w B.pa B.ctm
          ∧ w'.serverNotifier = w.serverNotifier
          ∧ (w.serverNotifier ≠ 0 →
              w'.owner w.serverNotifier = w.owner w.serverNotifier
              ∧ w'.pendingOwner w.serverNotifier = w.pendingOwner w.serverNotifier
              ∧ adminCall w' B.pa w.serverNotifier = adminCall w B.pa w.serverNotifier
              ∧ w'.notifierCtm w.serverNotifier = w.notifierCtm w.serverNotifier)))
    ∨ HolderPairCollides B E.H w w'

/-- **A LEG THAT WRITES `pendingAdmin` SUCCEEDS** (witness for `PassingLegKeepsHolderReads`
and `CtmPendingAdminOutsideHash`). A CTM executor in its standing configuration, with a
nonzero notifier, the check at `:75-77` passing, a nonempty set of participating rows that are
already applied, and an engine that only calls `ctm.setPendingAdmin(Y)` for a `Y` other than
the current `pendingAdmin`: the leg succeeds, with that write as its post-state. -/
def Properties.PendingAdminLegWitness : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w : World) (Y : Address),
    Prechecks E B tr m ∧ ExecutorHoldsCtm B w ∧ CtmAdminOk B w ∧ w.serverNotifier ≠ 0
    ∧ toRows m.proxyUpgrades ≠ [] ∧ rowsApplied B w (toRows m.proxyUpgrades)
    ∧ Y ≠ w.ctmPendingAdmin
    ∧ leg E B tr m (setCtmPendingAdmin Y) w = some { w with ctmPendingAdmin := Y }

/-! ## (b) The CTM half of the `@dev` -/

/-- **A MOVED CTM IS CAUGHT.** If there is a CTM, the `ProxyAdmin` administers the CTM proxy
before the leg, and the engine's post-state `w'` has the CTM proxy's admin slot at anything
other than the `ProxyAdmin`, then the leg reverts, or the compared pair collides
(`HolderPairCollides B E.H w w'`). The engine is an arbitrary function on this model's worlds,
and nothing is assumed about what the CTM's `admin()` answers in `w'`. No hash premise. -/
def Properties.MovedCtmCaught : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (eng : Engine) (w w' : World),
    B.ctm ≠ 0 →
    (w.proxy B.ctm).adminSlot = B.pa →
    eng B.self (buildContext B tr m) m.proxyUpgrades w = some w' →
    (w'.proxy B.ctm).adminSlot ≠ B.pa →
    leg E B tr m eng w = none ∨ HolderPairCollides B E.H w w'

/-- **`MovedCtmCaught` FIRES.** A CTM executor in its standing configuration, with a nonzero
notifier, the check at `:75-77` passing, nonempty participating rows already applied, and the
engine `aliasCtmProxyAdmin X` for an `X` other than zero, the executor and the `ProxyAdmin`:
every premise of `MovedCtmCaught` holds, the engine moves the CTM proxy's admin slot to `X`,
`leg` reverts, and the pair does not collide under the environment's hash. (The same run passes
the `d9f6789` leg: `Contracts.DomainHoldersV35.History.Properties.MovedCtmCaughtNotVacuous`.) -/
def Properties.MovedCtmCaughtWitness : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w w' : World) (X : Address),
    Prechecks E B tr m ∧ ExecutorHoldsCtm B w ∧ CtmAdminOk B w ∧ w.serverNotifier ≠ 0
    ∧ toRows m.proxyUpgrades ≠ [] ∧ rowsApplied B w (toRows m.proxyUpgrades)
    ∧ X ≠ 0 ∧ X ≠ B.self ∧ X ≠ B.pa
    ∧ aliasCtmProxyAdmin X B.self (buildContext B tr m) m.proxyUpgrades w = some w'
    ∧ (w'.proxy B.ctm).adminSlot = X
    ∧ leg E B tr m (aliasCtmProxyAdmin X) w = none
    ∧ ¬ HolderPairCollides B E.H w w'

/-- **COUNTERMODEL: THE COLLISION DISJUNCT OF `MovedCtmCaught` IS LOAD-BEARING.** With a hash
that sends every word list to the same word, a CTM executor in its standing configuration with
the check at `:75-77` passing, whose engine is `aliasCtmProxyAdmin X`, meets every premise of
`MovedCtmCaught`, and the leg succeeds. -/
def Properties.MovedCtmCollisionDisjunctLoadBearing : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w w' : World) (X : Address),
    (∀ l l', E.H l = E.H l')
    ∧ Prechecks E B tr m ∧ ExecutorHoldsCtm B w ∧ CtmAdminOk B w
    ∧ aliasCtmProxyAdmin X B.self (buildContext B tr m) m.proxyUpgrades w = some w'
    ∧ (w'.proxy B.ctm).adminSlot ≠ B.pa
    ∧ leg E B tr m (aliasCtmProxyAdmin X) w = some w'

/-! ## (c) The check before the engine (`:72-77`) -/

/-- **A CTM WHOSE `admin()` IS THE `ProxyAdmin` IS REFUSED.** If there is a CTM and `admin()`
sent by the executor to the CTM answers the `ProxyAdmin`, the leg reverts, whatever the
engine and the hash. -/
def Properties.CtmAdminIsProxyAdminReverts : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (eng : Engine) (w : World),
    B.ctm ≠ 0 → adminCall w B.self B.ctm = some B.pa → leg E B tr m eng w = none

/-- **THE CHECK AT `:75-77` IS WHAT REFUSES A MOVE THE HASH CANNOT SEE.** A CTM executor in its
standing configuration, with a nonzero notifier, except that the CTM's `admin()` answers the
`ProxyAdmin`; the engine `moveProxyAdmin ctm X` moves the CTM proxy's admin slot to an `X`
other than zero, the executor and the `ProxyAdmin`. Then: the prechecks pass; the word list
`_domainHolders` hashes is the same before and after the engine, for every hash function (and
its reads succeed); the executor's ownership is unchanged; the rows are applied; the check at
`:75-77` fails (`¬ CtmAdminOk`); and the leg reverts. So on this instance every check of the
leg other than `:75-77` passes. -/
def Properties.CtmAdminCheckLoadBearing : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w w' : World) (X : Address),
    Prechecks E B tr m ∧ ExecutorHoldsCtm B w ∧ w.serverNotifier ≠ 0
    ∧ adminCall w B.self B.ctm = some B.pa
    ∧ X ≠ 0 ∧ X ≠ B.self ∧ X ≠ B.pa
    ∧ moveProxyAdmin B.ctm X B.self (buildContext B tr m) m.proxyUpgrades w = some w'
    ∧ (w'.proxy B.ctm).adminSlot = X
    ∧ (∀ H : Hash, (holderPreimage B H w).isSome ∧ holderPreimage B H w' = holderPreimage B H w)
    ∧ w'.execOwner = w.execOwner ∧ w'.execPendingOwner = w.execPendingOwner
    ∧ rowsApplied B w' (toRows m.proxyUpgrades)
    ∧ ¬ CtmAdminOk B w
    ∧ leg E B tr m (moveProxyAdmin B.ctm X) w = none

/-! ## (d) The ServerNotifier half -/

/-- **A MOVED NOTIFIER WITHOUT `admin()` REVERTS THE LEG.** With a CTM, if the engine's
post-state `w'` has a nonzero `serverNotifierAddress` whose proxy is administered by anything
but the `ProxyAdmin`, and that notifier's implementation has no `admin()` (as `ServerNotifier`
at `b17415d`), the leg reverts. The notifier here is the one the CTM points at after the
engine: the second `_domainHolders` call reads `serverNotifierAddress()` again (`:123`).
(`PassingLegKeepsHolderReads` says a successful leg leaves that address unchanged unless the
compared pair collides.) The engine is arbitrary. No hash premise and no premise on the
pre-state. -/
def Properties.MovedNotifierReverts : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (eng : Engine) (w w' : World),
    B.ctm ≠ 0 →
    eng B.self (buildContext B tr m) m.proxyUpgrades w = some w' →
    w'.serverNotifier ≠ 0 →
    (w'.proxy w'.serverNotifier).adminSlot ≠ B.pa →
    w'.adminAnswer w'.serverNotifier = none →
    leg E B tr m eng w = none

/-- **`MovedNotifierReverts` IS NOT VACUOUS.** A CTM executor in its standing configuration,
the check at `:75-77` passing, with a nonzero notifier the `ProxyAdmin` administers and whose
implementation has no `admin()`, and the engine `moveProxyAdmin notifier X`: every premise
holds, and the notifier the CTM points at is the same before and after. -/
def Properties.MovedNotifierRevertsSatisfiable : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w w' : World) (X : Address),
    Prechecks E B tr m ∧ ExecutorHoldsCtm B w ∧ CtmAdminOk B w ∧ w.serverNotifier ≠ 0
    ∧ (w.proxy w.serverNotifier).adminSlot = B.pa
    ∧ w.adminAnswer w.serverNotifier = none
    ∧ moveProxyAdmin w.serverNotifier X B.self (buildContext B tr m) m.proxyUpgrades w = some w'
    ∧ w'.serverNotifier = w.serverNotifier
    ∧ (w'.proxy w'.serverNotifier).adminSlot ≠ B.pa
    ∧ w'.adminAnswer w'.serverNotifier = none

/-- **COUNTERMODEL: THE "NO `admin()`" PREMISE IS LOAD-BEARING.** If the notifier's
implementation answered `admin()` with the `ProxyAdmin`, the same move would pass every check,
for every hash function: the leg succeeds with the notifier proxy administered by
`X ≠ ProxyAdmin`. (`ServerNotifier` at `b17415d` declares no `admin()`.) -/
def Properties.NotifierAdminGetterLoadBearing : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w w' : World) (X : Address),
    Prechecks E B tr m ∧ ExecutorHoldsCtm B w ∧ CtmAdminOk B w ∧ w.serverNotifier ≠ 0
    ∧ (w.proxy w.serverNotifier).adminSlot = B.pa
    ∧ w.adminAnswer w.serverNotifier = some B.pa
    ∧ X ≠ B.pa
    ∧ moveProxyAdmin w.serverNotifier X B.self (buildContext B tr m) m.proxyUpgrades w = some w'
    ∧ w'.serverNotifier = w.serverNotifier
    ∧ (w'.proxy w'.serverNotifier).adminSlot = X
    ∧ ∀ H : Hash, leg { E with H := H } B tr m (moveProxyAdmin w.serverNotifier X) w = some w'

/-! ## (e) `pendingAdmin` is not compared -/

/-- **`ChainTypeManager.pendingAdmin` IS NOT GUARDED.** For a CTM executor in its standing
configuration with the check at `:75-77` passing and a transition passing the prechecks whose
rows are already applied, an engine that only calls `ctm.setPendingAdmin(Y)` passes the leg
for every `Y` and every hash function, and the leg's result is exactly that write. -/
def Properties.CtmPendingAdminOutsideHash : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w : World) (Y : Address),
    Prechecks E B tr m → ExecutorHoldsCtm B w → CtmAdminOk B w →
    rowsApplied B w (toRows m.proxyUpgrades) →
    leg E B tr m (setCtmPendingAdmin Y) w = some { w with ctmPendingAdmin := Y }

/-! ## (f) The rows post-check -/

/-- **THE ROWS POST-CHECK REVERTS A MOVED CTM THAT HAS A ROW.** If the engine's post-state has
the CTM proxy administered by anything but the `ProxyAdmin`, the CTM's implementation has no
`implementation()` (as `ChainTypeManager`), and the transition has a participating row on the
CTM proxy, then `requireRowsApplied` (`:103`) reverts the leg, for every hash function. (The
`d9f6789` leg reverts too: `Contracts.DomainHoldersV35.History.Properties.MovedCtmWithCtmRowReverts`.) -/
def Properties.MovedCtmWithCtmRowLegReverts : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (eng : Engine) (w w' : World),
    eng B.self (buildContext B tr m) m.proxyUpgrades w = some w' →
    (w'.proxy B.ctm).adminSlot ≠ B.pa →
    w'.implAnswer B.ctm = none →
    (∃ r ∈ toRows m.proxyUpgrades, r.proxy = B.ctm) →
    leg E B tr m eng w = none

/-- **`MovedCtmWithCtmRowLegReverts` IS NOT VACUOUS.** A CTM executor in its standing
configuration with the check at `:75-77` passing, a transition passing the prechecks whose one
participating row is on the CTM proxy and already applied, and the engine
`moveProxyAdmin ctm X`: every premise holds. -/
def Properties.MovedCtmWithCtmRowRevertsWitness : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w w' : World) (X : Address),
    Prechecks E B tr m ∧ ExecutorHoldsCtm B w ∧ CtmAdminOk B w
    ∧ rowsApplied B w (toRows m.proxyUpgrades)
    ∧ moveProxyAdmin B.ctm X B.self (buildContext B tr m) m.proxyUpgrades w = some w'
    ∧ (w'.proxy B.ctm).adminSlot ≠ B.pa ∧ w'.implAnswer B.ctm = none
    ∧ (∃ r ∈ toRows m.proxyUpgrades, r.proxy = B.ctm)

/-! ## (g) Comparison with `d9f6789` -/

end Contracts.DomainHoldersV35
