import EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.DomainHoldersV35

/-!
# Properties: what the domain-holder check catches, at `d9f6789`

Statements about `EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.DomainHoldersV35`. Proofs
are in `EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.DomainHoldersV35`.

## The `@dev` at `ProxyUpgradeExecutorBase.sol:106-108`

It says that once `_proxyAdmin` no longer administers a proxy, `getProxyAdmin` falls through
to the implementation, so "a moved CTM answers its own `admin()` and fails the comparison, a
moved ServerNotifier has none and reverts the leg".

* The ServerNotifier half holds with no hash premise (`NotifierProxyAdminMoveReverts`), as
  long as the notifier's implementation still has no `admin()`
  (`NotifierAdminGetterLoadBearing` shows that premise is what it rests on).
* The CTM half holds only when the moved CTM's `ChainTypeManager.admin` is not the
  `ProxyAdmin` (`MovedCtmProxyAdminCaught`, with a pinned collision disjunct and no hash
  premise; `MovedCtmCollisionDisjunctLoadBearing` shows the disjunct cannot be dropped). That
  premise is not something the executor checks, and an engine leg can establish its negation
  itself: `MovedCtmPassesHolderCheck` makes the CTM's `admin` the `ProxyAdmin` (through
  `upgradeAndCall(…, acceptAdmin())`, which runs with `msg.sender = ProxyAdmin`) and then
  moves the CTM proxy's admin slot to an arbitrary `X`. Every check at `:87-97` passes for
  every hash function, the hashed tuples are equal word for word, and afterwards `X`, not the
  executor's `ProxyAdmin`, administers the CTM proxy. `CtmAdminPremiseLoadBearing` packages
  that as the countermodel to `MovedCtmProxyAdminCaught` without its premise.
* The rows post-check at `:93-97` catches a moved CTM only when the transition itself upgrades
  the CTM (`MovedCtmWithCtmRowReverts`), which is why `MovedCtmPassesHolderCheck` asks for no
  participating row on the CTM proxy.
* `ChainTypeManager.admin` and `pendingAdmin` are not hashed while the `ProxyAdmin`
  administers the CTM proxy (`HolderHashIgnoresCtmAdminRole`, `CtmAdminRoleOutsideHash`,
  `CtmAdminTakenByExecutorPasses`).

## The `@notice` at `RegistryTypes.sol:209-210`

"Built by the executor from its own immutable bindings, never from the manifest or the
caller." Three of the five fields are the bindings (`ContextBindingFields`); `transition` is
the `onlyOwner` caller's argument and `proxyUpgradeEngine` is the manifest's field, so no
function of the bindings alone gives the context (`ContextNotFromBindings`). The `@param`
lines of the same struct (`:213-214`) describe those two fields correctly.
-/

namespace Contracts.DomainHoldersV35

/-! ## (a) The CTM half of the `@dev`, in its true form -/

/-- **A MOVED CTM IS CAUGHT WHEN ITS `admin` IS NOT THE `ProxyAdmin`, OR THE PAIR COLLIDES.**
If the `ProxyAdmin` administers the CTM proxy before the leg, the engine's post-state has
moved the CTM proxy's admin slot away from it, and the CTM implementation's `admin()` in that
post-state does not answer the `ProxyAdmin` (a different address, or a revert), then the leg
reverts — unless the two CTM tuples read before and after (which then differ) hash equal, or
the two outer notifier tuples differ and hash equal (`HolderPairCollides`). The engine is
arbitrary. No hash premise. -/
def Properties.MovedCtmProxyAdminCaught : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (eng : Engine) (w w' : World),
    B.ctm ≠ 0 →
    (w.proxy B.ctm).adminSlot = B.pa →
    eng B.self (buildContext B tr m) m.proxyUpgrades w = some w' →
    (w'.proxy B.ctm).adminSlot ≠ B.pa →
    w'.adminAnswer B.ctm ≠ some B.pa →
    leg E B tr m eng w = none ∨ HolderPairCollides B E.H w w' w.serverNotifier

/-- **`MovedCtmProxyAdminCaught` IS NOT VACUOUS AND ITS DISJUNCT IS NOT A TAUTOLOGY.** A CTM
executor in its standing configuration, with a nonzero notifier and genuine prechecks, whose
engine only moves the CTM proxy's admin slot (`PA.changeProxyAdmin(ctm, X)`): every premise
holds, the leg reverts, and the named pair does not collide. -/
def Properties.MovedCtmProxyAdminCaughtNotVacuous : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w w' : World) (X : Address),
    Prechecks E B tr m ∧ ExecutorHoldsCtm B w ∧ w.serverNotifier ≠ 0
    ∧ B.ctm ≠ 0 ∧ (w.proxy B.ctm).adminSlot = B.pa
    ∧ moveProxyAdmin B.ctm X B.self (buildContext B tr m) m.proxyUpgrades w = some w'
    ∧ (w'.proxy B.ctm).adminSlot ≠ B.pa ∧ w'.adminAnswer B.ctm ≠ some B.pa
    ∧ leg E B tr m (moveProxyAdmin B.ctm X) w = none
    ∧ ¬ HolderPairCollides B E.H w w' w.serverNotifier

/-- **COUNTERMODEL: THE COLLISION DISJUNCT OF `MovedCtmProxyAdminCaught` IS LOAD-BEARING.**
With a hash that sends every word list to the same word, a CTM executor in its standing
configuration whose engine only moves the CTM proxy's admin slot meets every premise of
`MovedCtmProxyAdminCaught` and the leg succeeds: the comparison at `:90` is a comparison of
hashes, so "fails the comparison" holds only up to that collision. -/
def Properties.MovedCtmCollisionDisjunctLoadBearing : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w w' : World) (X : Address),
    (∀ l l', E.H l = E.H l')
    ∧ Prechecks E B tr m ∧ ExecutorHoldsCtm B w
    ∧ B.ctm ≠ 0 ∧ (w.proxy B.ctm).adminSlot = B.pa
    ∧ moveProxyAdmin B.ctm X B.self (buildContext B tr m) m.proxyUpgrades w = some w'
    ∧ (w'.proxy B.ctm).adminSlot ≠ B.pa ∧ w'.adminAnswer B.ctm ≠ some B.pa
    ∧ leg E B tr m (moveProxyAdmin B.ctm X) w = some w'

/-! ## (b) The ServerNotifier half -/

/-- **MOVING THE PRE-LEG NOTIFIER'S PROXY ADMIN REVERTS THE LEG.** With a CTM and a nonzero
notifier fixed before the engine runs, if the engine's post-state has the notifier proxy
administered by anything but the `ProxyAdmin` and the notifier's implementation still has no
`admin()` (as `ServerNotifier` at `d9f6789`), the leg reverts. The engine is arbitrary. No
hash premise and no premise on the pre-state. -/
def Properties.NotifierProxyAdminMoveReverts : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (eng : Engine) (w w' : World),
    B.ctm ≠ 0 → w.serverNotifier ≠ 0 →
    eng B.self (buildContext B tr m) m.proxyUpgrades w = some w' →
    (w'.proxy w.serverNotifier).adminSlot ≠ B.pa →
    w'.adminAnswer w.serverNotifier = none →
    leg E B tr m eng w = none

/-- **`NotifierProxyAdminMoveReverts` IS NOT VACUOUS.** A CTM executor in its standing
configuration with genuine prechecks, whose engine moves the notifier proxy's admin slot
(`PA.changeProxyAdmin(notifier, X)`), meets every premise. -/
def Properties.NotifierProxyAdminMoveRevertsSatisfiable : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w w' : World) (X : Address),
    Prechecks E B tr m ∧ ExecutorHoldsCtm B w ∧ w.serverNotifier ≠ 0
    ∧ (w.proxy w.serverNotifier).adminSlot = B.pa
    ∧ moveProxyAdmin w.serverNotifier X B.self (buildContext B tr m) m.proxyUpgrades w = some w'
    ∧ (w'.proxy w.serverNotifier).adminSlot ≠ B.pa
    ∧ w'.adminAnswer w.serverNotifier = none

/-- **COUNTERMODEL: THE "NO `admin()`" PREMISE IS LOAD-BEARING.** Were the notifier's
implementation to answer `admin()` with the `ProxyAdmin`, the same move would pass every
check, for every hash function: the leg succeeds with the notifier proxy administered by
`X ≠ ProxyAdmin`. (`ServerNotifier` at `d9f6789` has no such getter; this is what a later
notifier implementation must not add.) -/
def Properties.NotifierAdminGetterLoadBearing : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w w' : World) (X : Address),
    Prechecks E B tr m ∧ ExecutorHoldsCtm B w ∧ w.serverNotifier ≠ 0
    ∧ w.adminAnswer w.serverNotifier = some B.pa
    ∧ X ≠ B.pa ∧ (w'.proxy w.serverNotifier).adminSlot = X
    ∧ ∀ H : Hash, leg { E with H := H } B tr m (moveProxyAdmin w.serverNotifier X) w = some w'

/-! ## (c) The refutation: a moved CTM that passes -/

/-- **A MOVED CTM PASSES THE HOLDER CHECK.** Take a CTM executor in its standing configuration
(`ExecutorHoldsCtm`), a transition passing the prechecks, and an engine that first runs any
prefix `pre` (for example the rows) leaving the holder reads alone (`HolderFrame`) with every
participating row applied and none on the CTM proxy, and then runs `aliasCtmProxyAdmin X`
for any `X` other than zero, the executor and the `ProxyAdmin`. Then, **for every hash
function**:
* the leg succeeds;
* the CTM proxy's admin slot is `X`, its implementation is unchanged, and the CTM's `admin`
  is the `ProxyAdmin`;
* the CTM tuple read after is the one read before, word for word, and so is the outer
  notifier tuple — no collision is involved;
* `X` now administers the CTM proxy: an `upgradeTo` it sends installs any code as the CTM's
  implementation;
* the executor's `ProxyAdmin` no longer does: its `changeProxyAdmin` to any address reverts,
  and so does an `upgradeTo` from it. -/
def Properties.MovedCtmPassesHolderCheck : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (pre : Engine) (w₀ w₁ : World)
    (X : Address),
    Prechecks E B tr m → ExecutorHoldsCtm B w₀ →
    pre B.self (buildContext B tr m) m.proxyUpgrades w₀ = some w₁ →
    HolderFrame B w₀.serverNotifier w₀ w₁ →
    rowsApplied B w₁ (toRows m.proxyUpgrades) →
    (∀ r ∈ toRows m.proxyUpgrades, r.proxy ≠ B.ctm) →
    X ≠ 0 → X ≠ B.self → X ≠ B.pa →
    ∃ w₂, leg E B tr m (pre.andThen (aliasCtmProxyAdmin X)) w₀ = some w₂
      ∧ (w₂.proxy B.ctm).adminSlot = X
      ∧ (w₂.proxy B.ctm).impl = (w₀.proxy B.ctm).impl
      ∧ w₂.adminAnswer B.ctm = some B.pa
      ∧ ctmWords B w₂ = ctmWords B w₀
      ∧ notifierWords B E.H w₂ w₀.serverNotifier = notifierWords B E.H w₀ w₀.serverNotifier
      ∧ (∀ impl, E.hasCode impl = true →
          tupAdminUpgradeTo E.hasCode (w₂.proxy B.ctm) X impl
            = some { (w₂.proxy B.ctm) with impl := impl })
      ∧ (∀ a, paChangeProxyAdmin w₂ B.pa B.self B.ctm a = none)
      ∧ (∀ impl, tupAdminUpgradeTo E.hasCode (w₂.proxy B.ctm) B.pa impl = none)

/-- **THE PREMISES OF `MovedCtmPassesHolderCheck` HOLD TOGETHER**, with a nonzero notifier, a
nonempty set of participating rows (a transition must have one,
`ProxyUpgradeTransition.sol:34-36`) that the prefix applies, a CTM whose `admin` is initially
not the `ProxyAdmin`, and an `X` meeting the side conditions. -/
def Properties.MovedCtmPassesHolderCheckSatisfiable : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (pre : Engine) (w₀ w₁ : World)
    (X : Address),
    Prechecks E B tr m ∧ ExecutorHoldsCtm B w₀ ∧ w₀.serverNotifier ≠ 0
    ∧ w₀.adminAnswer B.ctm ≠ some B.pa
    ∧ pre B.self (buildContext B tr m) m.proxyUpgrades w₀ = some w₁
    ∧ HolderFrame B w₀.serverNotifier w₀ w₁
    ∧ toRows m.proxyUpgrades ≠ [] ∧ ¬ rowsApplied B w₀ (toRows m.proxyUpgrades)
    ∧ rowsApplied B w₁ (toRows m.proxyUpgrades)
    ∧ (∀ r ∈ toRows m.proxyUpgrades, r.proxy ≠ B.ctm)
    ∧ X ≠ 0 ∧ X ≠ B.self ∧ X ≠ B.pa

/-- **COUNTERMODEL: THE PREMISE `CTM.admin ≠ ProxyAdmin` OF `MovedCtmProxyAdminCaught` IS
LOAD-BEARING.** Every other premise of `MovedCtmProxyAdminCaught` holds, the executor is in
its standing configuration, the leg succeeds, and the pair does not collide: the conclusion
fails. The engine is a rows prefix followed by `aliasCtmProxyAdmin`. -/
def Properties.CtmAdminPremiseLoadBearing : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (eng : Engine) (w w' : World),
    Prechecks E B tr m ∧ ExecutorHoldsCtm B w
    ∧ B.ctm ≠ 0 ∧ (w.proxy B.ctm).adminSlot = B.pa
    ∧ eng B.self (buildContext B tr m) m.proxyUpgrades w = some w'
    ∧ (w'.proxy B.ctm).adminSlot ≠ B.pa
    ∧ leg E B tr m eng w = some w' ∧ ¬ HolderPairCollides B E.H w w' w.serverNotifier

/-- **THE ROWS POST-CHECK CATCHES A MOVED CTM ONLY THROUGH A CTM ROW.** If the engine's
post-state has the CTM proxy administered by anything but the `ProxyAdmin`, the CTM's
implementation has no `implementation()` (as `ChainTypeManager` at `d9f6789`), and the
transition has a participating row on the CTM proxy, the leg reverts at `:97`. So the premise
"no participating row on the CTM proxy" of `MovedCtmPassesHolderCheck` cannot be dropped. -/
def Properties.MovedCtmWithCtmRowReverts : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (eng : Engine) (w w' : World),
    eng B.self (buildContext B tr m) m.proxyUpgrades w = some w' →
    (w'.proxy B.ctm).adminSlot ≠ B.pa →
    w'.implAnswer B.ctm = none →
    (∃ r ∈ toRows m.proxyUpgrades, r.proxy = B.ctm) →
    leg E B tr m eng w = none

/-! ## (d) The CTM's `admin` role is outside the hash -/

/-- **THE HOLDER HASH DOES NOT READ `ChainTypeManager.pendingAdmin`, NOR `admin` WHILE THE
`ProxyAdmin` ADMINISTERS THE CTM PROXY.** For every hash, notifier argument and world:
rewriting `pendingAdmin` leaves `_domainHolders` unchanged; and if the `ProxyAdmin` is the CTM
proxy's admin, so does rewriting what the CTM's `admin()` answers (to any address, or to a
revert). The fourth hashed word is the EIP-1967 admin slot in that state, and
`ChainTypeManager.admin` only otherwise. -/
def Properties.HolderHashIgnoresCtmAdminRole : Prop :=
  ∀ (B : Bindings) (H : Hash) (w : World) (n : Address) (a : Option Address) (y : Address),
    domainHolders B H { w with ctmPendingAdmin := y } n = domainHolders B H w n
    ∧ ((w.proxy B.ctm).adminSlot = B.pa →
        domainHolders B H
            { w with adminAnswer := upd w.adminAnswer B.ctm a, ctmPendingAdmin := y } n
          = domainHolders B H w n)

/-- **`ChainTypeManager.pendingAdmin` IS NOT GUARDED.** For a CTM executor in its standing
configuration and a transition passing the prechecks whose rows are already applied, an
engine that only calls `ctm.setPendingAdmin(Y)` passes the leg for every `Y` and every hash
function, and the leg's result is exactly that write. -/
def Properties.CtmAdminRoleOutsideHash : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w : World) (Y : Address),
    Prechecks E B tr m → ExecutorHoldsCtm B w →
    rowsApplied B w (toRows m.proxyUpgrades) →
    leg E B tr m (setCtmPendingAdmin Y) w = some { w with ctmPendingAdmin := Y }

/-- **`ChainTypeManager.admin` IS NOT GUARDED EITHER.** Under the same premises, an engine
that calls `ctm.setPendingAdmin(this)` and then `ctm.acceptAdmin()` passes the leg, leaving the
executor as the CTM's `admin` and no pending admin. -/
def Properties.CtmAdminTakenByExecutorPasses : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w : World),
    Prechecks E B tr m → ExecutorHoldsCtm B w →
    rowsApplied B w (toRows m.proxyUpgrades) →
    ∃ w', leg E B tr m takeCtmAdmin w = some w'
      ∧ w'.adminAnswer B.ctm = some B.self ∧ w'.ctmPendingAdmin = 0

/-- **THE PREMISES OF THE TWO RESULTS ABOVE HOLD TOGETHER**, with a nonzero notifier and a
nonempty set of participating rows. -/
def Properties.CtmAdminRoleOutsideHashSatisfiable : Prop :=
  ∃ (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (w : World),
    Prechecks E B tr m ∧ ExecutorHoldsCtm B w ∧ w.serverNotifier ≠ 0
    ∧ toRows m.proxyUpgrades ≠ [] ∧ rowsApplied B w (toRows m.proxyUpgrades)

/-! ## (e) Where the context comes from -/

/-- **THREE CONTEXT FIELDS ARE THE BINDINGS.** `proxyAdmin`, `domain` and `chainTypeManager`
are the executor's immutables, whatever the caller's transition argument and the manifest;
when the prechecks pass, `domain` is also the manifest's. -/
def Properties.ContextBindingFields : Prop :=
  ∀ (E : Env) (B : Bindings) (tr : Address) (m : Manifest),
    (buildContext B tr m).proxyAdmin = B.pa
    ∧ (buildContext B tr m).domain = B.domain
    ∧ (buildContext B tr m).chainTypeManager = B.ctm
    ∧ (Prechecks E B tr m → (buildContext B tr m).domain = m.domain)

/-- **THE CONTEXT IS NOT BUILT FROM THE BINDINGS ALONE** (refutes `RegistryTypes.sol:209-210`
as written). `transition` is the `onlyOwner` caller's argument and `proxyUpgradeEngine` is the
manifest's field. Consequently, for every executor whose environment has two distinct code
addresses, no context depends on the bindings only: two calls passing the prechecks hand the
engine different contexts — one pair differing only in the caller's transition argument, one
pair differing only in the manifest's engine. -/
def Properties.ContextNotFromBindings : Prop :=
  (∀ (B : Bindings) (tr : Address) (m : Manifest),
    (buildContext B tr m).transition = tr ∧ (buildContext B tr m).proxyUpgradeEngine = m.engine)
  ∧ ∀ (E : Env) (B : Bindings), (∃ a b, a ≠ b ∧ E.hasCode a = true ∧ E.hasCode b = true) →
      (∃ tr tr' m, Prechecks E B tr m ∧ Prechecks E B tr' m
          ∧ buildContext B tr m ≠ buildContext B tr' m)
      ∧ (∃ tr m m', Prechecks E B tr m ∧ Prechecks E B tr m'
          ∧ buildContext B tr m ≠ buildContext B tr m')
      ∧ ¬ ∃ c : Context, ∀ tr m, Prechecks E B tr m → buildContext B tr m = c

end Contracts.DomainHoldersV35
