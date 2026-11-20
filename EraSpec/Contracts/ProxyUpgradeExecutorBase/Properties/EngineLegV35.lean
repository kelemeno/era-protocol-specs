import EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.EngineLegV35
import EraSpec.Core.Headline

/-!
# Properties: what a successful engine leg pins, and each check is load-bearing

Statements about `EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.EngineLegV35`
(`executors/ProxyUpgradeExecutorBase.sol:51-104` at `b17415d20`). Proofs are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.EngineLegV35`.

## What a successful leg pins, for every engine

The engine is an arbitrary relation and the world an arbitrary set of getters, so these hold
for any code a transition can pin:

* the engine that ran is the one the manifest names, with the context the executor built and
  the pinned inventory, and the leg's checks before the engine passed
  (`LegRunsThePinnedEngine`, `:57-84`);
* the executor's owner and pending owner are unchanged (`LegKeepsExecutorOwnership`, `:93-95`),
  so the only executor storage that can differ is slots the executors do not declare
  (`LegChangesOnlyUndeclaredExecutorStorage`);
* the holder tuple of the domain is unchanged, or two preimages the check hashed differ and
  collide under `keccak256` (`LegKeepsDomainHoldersOrCollides`, `:96-98`; getter by getter in
  `LegKeepsNamedHoldersUnlessCollision`). Nothing is assumed about `keccak256`; the encoding
  contributes no collisions (`AbiEncodeInjective`). The check refuses no engine that leaves
  the tuple alone (`UnchangedHoldersPassTheCheck`);
* where `getProxyAdmin` falls through to the CTM's `admin()` once the `ProxyAdmin` no longer
  administers the CTM proxy (`AdminFallsThrough`), a leg that starts with the `ProxyAdmin`
  administering the CTM proxy ends with it still administering it, unless a compared
  preimage collides (`LegKeepsCtmProxyAdministeredUnlessCollision`, `:72-77`);
* every row of the inventory runs its `implNew` (`LegLandsEveryRow`,
  `LegLandsEveryActiveSlot`, `:99-103`).

## `DefaultProxyUpgradeEngine`

In the concrete world, from a state where the `ProxyAdmin` administers every proxy, a leg
through `DefaultProxyUpgradeEngine` is the `e561b9cc2` `applyTransition` plus four
requirements: the engine is code, the executor owns the `ProxyAdmin`, the inventory has the
domain's length, and a bound CTM's admin is not the `ProxyAdmin`
(`DefaultEngineLegIsApplyTransition`). So there the post-checks never refuse it. The owner
requirement is new behaviour (`UnownedAdminReplayNowReverts`). `DefaultEngineLegWitness` and
`DefaultEngineCoreLegWitness` are the satisfiability witnesses: one row, both domains, every
hash function, no collision.

## Each check is load-bearing

For each check there is an engine or manifest that the leg refuses and that the same leg with
only that check deleted accepts: an owner-slot write (`OwnerSlotWriteIsCaught`), a
`ctm.transferOwnership` (`CtmNominationIsCaught`) and a `ctm.setServerNotifier`
(`NotifierRepointIsCaught`) for the holders check (refused under a hash that does not collide
there, and accepted under any hash only with a collision), an `_afterSwaps` that moves a row's
proxy back (`RowMovedBackIsCaught`), a `changeProxyAdmin` of a CTM whose `admin()` is the
`ProxyAdmin` (`AliasedCtmMoveIsCaughtByTheAdminCheck`), and a manifest of the other domain
(`ForeignDomainManifestIsCaught`). Two of the checks are load-bearing only in a corner:

* `requireCode(engine)` (`:62-63`): without it, a codeless engine leg succeeds exactly when
  every row is already at its target, and then nothing changes (`CodelessEngineLegIff`,
  `CodelessEngineMovesNothing`, instantiated by `CodelessEngineFreshStateIsRefused`); so it
  matters on a replay and on an empty transition (`CodelessEngineReplayIsCaught`,
  `CodelessEngineEmptyTransitionIsCaught`).
* the domain check (`:59-61`): for a manifest whose inventory has its own domain's length,
  which the `ProxyUpgradeTransition` constructor enforces, the length check at `:99-102`
  already refuses the other domain (`DomainCheckRedundantAtConstructorLength`).

## Boundaries

The collision disjunct cannot be dropped (`HoldersCollisionIsNeeded`). The checks say nothing
about proxies no row names (`UnlistedProxyMovePassesEveryCheck`) or about executor storage
slots the executors do not declare (`UndeclaredSlotWritePassesEveryCheck`). The source says
so: "Anything else the engine does is what governance reviewed" (`:40-41`; also
`engines/IProxyUpgradeEngine.sol:18-21`).
-/

namespace Contracts.EngineLegV35

open Clear
open Contracts.ProxyUpgradeCurrent (Address Row Impl upd RowsApplied toRows Domain)

/-! ## Encoding -/

/-- **THE ENCODING IS INJECTIVE.** `abi.encode` of a tuple of static one-word values
(addresses, `bytes32`) determines the tuple: two tuples with the same encoding are equal.
Lengths need no premise, since every word is 32 bytes. -/
def Properties.AbiEncodeInjective : Prop :=
  ∀ ws ws' : List UInt256, abiEncode ws = abiEncode ws' → ws = ws'

/-! ## What a successful leg pins -/

/-- **THE LEG RUNS THE PINNED ENGINE ON THE EXECUTOR'S OWN CONTEXT.** A successful leg found
code at the transition and at the engine its manifest names, the manifest was of the
executor's domain, a bound CTM's `admin()` was not the `ProxyAdmin` before the engine ran, and
the engine code ran with the context built from the executor's bindings (`:65-71`) and the
manifest's inventory (`:82-84`): its calls took the world from `s` to `s'`. -/
def Properties.LegRunsThePinnedEngine : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ),
    Leg E eng T M d st s st' s' →
      E.hasCode s T ∧ M.domain = d ∧ E.hasCode s M.proxyUpgradeEngine ∧
        (E.chainTypeManager ≠ 0 → E.ctmAdmin s ≠ E.proxyAdmin) ∧
        ∃ calls, eng ⟨T, M.proxyUpgradeEngine, d, E.proxyAdmin, E.chainTypeManager⟩
          M.proxyUpgrades st s st' calls ∧ CallRun E s calls s'

/-- **(a) THE ENGINE CANNOT CHANGE WHO GOVERNS THE EXECUTOR.** For every engine, a successful
leg leaves the executor's `owner()` and `pendingOwner()` as they were (`:78-79`, `:93-95`). -/
@[headline] def Properties.LegKeepsExecutorOwnership : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ),
    Leg E eng T M d st s st' s' → st'.owner = st.owner ∧ st'.pendingOwner = st.pendingOwner

/-- **(a) COROLLARY: NO DECLARED EXECUTOR STORAGE CHANGES.** The executors declare two storage
slots, the owner and the pending owner. After a successful leg the executor's storage is what
it was, except possibly in slots the executors do not declare.
`UndeclaredSlotWritePassesEveryCheck` shows the exception is real. -/
def Properties.LegChangesOnlyUndeclaredExecutorStorage : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ),
    Leg E eng T M d st s st' s' → st' = { st with other := st'.other }

/-- **(b) THE DOMAIN HOLDERS ARE KEPT, OR KECCAK COLLIDES ON THE COMPARED PREIMAGES.** For every
engine and every hash function, after a successful leg the holder tuple is what it was, or one
of the named `abi.encode` preimages compared at `:80` and `:96` differs between before and
after while its hash does not (`HoldersBreak`). The holder tuple (`holderTuple`) is the
`ProxyAdmin`'s owner in the `Core` domain; with a CTM, the six words of the CTM tuple
(`:124-133`), followed by the four notifier words (`:137-147`) when the CTM names a nonzero
ServerNotifier, read in each world for the ServerNotifier the CTM names in that world. The
before-preimage is fixed before the engine runs, so `HoldersBreak` pairs that fixed preimage with
one the engine's world produces: a second preimage of a value fixed in advance, not a free
collision between two chosen inputs. -/
def Properties.LegKeepsDomainHoldersOrCollides : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ),
    Leg E eng T M d st s st' s' →
      holderTuple E s' = holderTuple E s ∨ HoldersBreak E s s'

/-- **(b), GETTER BY GETTER.** After a successful leg with no collision on the compared
preimages: the `ProxyAdmin`'s owner is unchanged; with a bound CTM, so are the CTM's owner,
pending owner, `admin()` and proxy admin, and the ServerNotifier it names; and when that
ServerNotifier `n` was nonzero before the leg, so are `n`'s owner, pending owner, proxy admin
and CTM. The premises are satisfiable (`DefaultEngineLegWitness`). -/
def Properties.LegKeepsNamedHoldersUnlessCollision : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ),
    Leg E eng T M d st s st' s' → ¬ HoldersBreak E s s' →
      E.paOwner s' = E.paOwner s ∧
      (E.chainTypeManager ≠ 0 →
        E.ownerOf s' E.chainTypeManager = E.ownerOf s E.chainTypeManager ∧
        E.pendingOwnerOf s' E.chainTypeManager = E.pendingOwnerOf s E.chainTypeManager ∧
        E.ctmAdmin s' = E.ctmAdmin s ∧
        E.getProxyAdmin s' E.chainTypeManager = E.getProxyAdmin s E.chainTypeManager ∧
        E.serverNotifierAddress s' = E.serverNotifierAddress s) ∧
      (E.chainTypeManager ≠ 0 → E.serverNotifierAddress s ≠ 0 →
        E.ownerOf s' (E.serverNotifierAddress s) = E.ownerOf s (E.serverNotifierAddress s) ∧
        E.pendingOwnerOf s' (E.serverNotifierAddress s) =
          E.pendingOwnerOf s (E.serverNotifierAddress s) ∧
        E.getProxyAdmin s' (E.serverNotifierAddress s) =
          E.getProxyAdmin s (E.serverNotifierAddress s) ∧
        E.notifierCtm s' (E.serverNotifierAddress s) = E.notifierCtm s (E.serverNotifierAddress s))

/-- **THE HOLDERS CHECK REFUSES NO ENGINE THAT LEAVES THE HOLDERS ALONE.** If the holder tuple
is the same in two worlds, so is the hash `_domainHolders` returns, for every hash function.
The premise holds on `DefaultEngineLegWitness`'s `w0` and `w1`. -/
def Properties.UnchangedHoldersPassTheCheck : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (s s' : σ),
    holderTuple E s' = holderTuple E s → domainHolders E s' = domainHolders E s

/-- **THE CTM PROXY STAYS WITH THE `ProxyAdmin`, UNLESS KECCAK COLLIDES.** For every engine and
every hash function: if `getProxyAdmin(ctm)` follows `AdminFallsThrough` and the `ProxyAdmin`
administers the CTM proxy before a successful CTM-domain leg with no collision on the compared
preimages, then it still administers it afterwards, and the CTM's `admin()` is still not the
`ProxyAdmin`. This is, in the model, the claim of the comment at `:72-74` ("refusing that
state before the engine runs covers the leg"). It rests on the check at `:75-77`:
`AliasedCtmMoveIsCaughtByTheAdminCheck` shows the leg without that check ends with the CTM
proxy administered by another address. The premises are satisfiable
(`DefaultEngineLegWitness`). -/
def Properties.LegKeepsCtmProxyAdministeredUnlessCollision : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ),
    Leg E eng T M d st s st' s' → ¬ HoldersBreak E s s' → E.chainTypeManager ≠ 0 →
    AdminFallsThrough E → E.adminSlot s E.chainTypeManager = E.proxyAdmin →
      E.adminSlot s' E.chainTypeManager = E.proxyAdmin ∧ E.ctmAdmin s' ≠ E.proxyAdmin

/-- **(c) EVERY ROW LANDS.** For every engine, after a successful leg every row of
`toRows(manifest.proxyUpgrades, inventoryLength(domain))` has
`getProxyImplementation(row.proxy) = row.implNew` (`:99-103`;
`libraries/ProxyUpgradeRowLib.sol:133-141`), and the inventory had exactly
`inventoryLength(domain)` slots (`libraries/ProxyUpgradeRowLib.sol:62-64`). -/
@[headline] def Properties.LegLandsEveryRow : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ),
    Leg E eng T M d st s st' s' →
      M.proxyUpgrades.length = inventoryLength d ∧
        ∀ r ∈ toRows M.proxyUpgrades, E.impl s' r.proxy = r.implNew

/-- **(c), ON THE INVENTORY.** The same without `toRows`: after a successful leg every slot of
the manifest's inventory whose `implNew` is nonzero has its proxy at that `implNew`. -/
def Properties.LegLandsEveryActiveSlot : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ),
    Leg E eng T M d st s st' s' →
      ∀ r ∈ M.proxyUpgrades, r.implNew ≠ 0 → E.impl s' r.proxy = r.implNew

/-! ## `DefaultProxyUpgradeEngine` -/

/-- **A DEFAULT-ENGINE LEG IS `applyTransition`, PLUS FOUR REQUIREMENTS.** In the concrete
world (any bound CTM `c`, code predicate, hash, manifest, storage, and start state in which
the `ProxyAdmin` `2` administers every proxy, as `applyRows` assumes of its bound admin,
`libraries/ProxyUpgradeRowLib.sol:100-101`; inert reinitializers), a leg through
`DefaultProxyUpgradeEngine` (`engines/DefaultProxyUpgradeEngine.sol:32-47`) succeeds exactly
when

* the engine address is code (`:62-63`),
* the executor owns the `ProxyAdmin` (`engines/DefaultProxyUpgradeEngine.sol:33-37`),
* the inventory has the domain's length,
* a bound CTM's admin role is not the `ProxyAdmin` (`:75-77`), and
* the `e561b9cc2` `applyTransition` of the transition's rows succeeds on the implementations,

and then the executor's storage is unchanged and the world differs only in the
implementations. So in this world the engine "applies the rows … and nothing else"
(`engines/DefaultProxyUpgradeEngine.sol:15-17`), and none of the three post-checks refuses
it. -/
def Properties.DefaultEngineLegIsApplyTransition : Prop :=
  ∀ (c : Address) (code : Address → Prop) (k : List UInt8 → UInt256) (T : Address)
    (M : Manifest) (d : Domain) (st : Store) (s : WState) (st' : Store) (s' : WState),
    (∀ p, s.adminSlot p = 2) →
    (Leg (wEnvWith c code k) (defaultEngineWith code) T M d st s st' s' ↔
      code M.proxyUpgradeEngine ∧ s.paOwner = 1 ∧ M.proxyUpgrades.length = inventoryLength d ∧
      (c ≠ 0 → s.roleAdmin c ≠ 2) ∧
      ProxyUpgradeCurrent.ApplyTransition (rowConfig code s) d
        ⟨T, M.domain, toRows M.proxyUpgrades⟩ s.impl s'.impl ∧
      st' = st ∧ s' = { s with impl := s'.impl })

/-- **(d) A DEFAULT-ENGINE LEG PASSES EVERY CHECK.** In the concrete world, for every hash
function, `DefaultProxyUpgradeEngine` with one row (`5: 10 → 11`) in the CTM domain succeeds
from `w0` and ends in `w1` with executor storage unchanged, no compared preimage collides, and
`getProxyAdmin(ctm)` follows `AdminFallsThrough`. Proxy `5` moves; the inventory has its own
domain's length; the `ProxyAdmin` administers every proxy; the CTM names ServerNotifier `9`
and its admin role is `15`; and the holder tuple has all ten entries and is the same before
and after. -/
@[witness] def Properties.DefaultEngineLegWitness : Prop :=
  (∀ k : List UInt8 → UInt256,
      Leg (wEnvWith 8 allCode k) defaultEngine wT wManifest .ctm wStore w0 wStore w1 ∧
        ¬ HoldersBreak (wEnvWith 8 allCode k) w0 w1 ∧ AdminFallsThrough (wEnvWith 8 allCode k)) ∧
    toRows wManifest.proxyUpgrades = [wRow] ∧ w0.impl 5 = 10 ∧ w1.impl 5 = 11 ∧
    wManifest.proxyUpgrades.length = inventoryLength wManifest.domain ∧
    (∀ p, w0.adminSlot p = 2) ∧
    wEnv.serverNotifierAddress w0 = 9 ∧ wEnv.ctmAdmin w0 = 15 ∧
    holderTuple wEnv w1 = holderTuple wEnv w0 ∧ (holderTuple wEnv w0).length = 10

/-- **(d) THE SAME FOR THE `Core` EXECUTOR.** With no bound CTM (`_chainTypeManager = 0`), for
every hash function, `DefaultProxyUpgradeEngine` with one row in a 9-slot `Core` inventory
succeeds from `w0` and ends in `w1`, and the compared preimage does not collide. The holder
tuple is the `ProxyAdmin`'s owner alone. -/
def Properties.DefaultEngineCoreLegWitness : Prop :=
  (∀ k : List UInt8 → UInt256,
      Leg (wEnvWith 0 allCode k) defaultEngine wT wManifestCore .core wStore w0 wStore w1 ∧
        ¬ HoldersBreak (wEnvWith 0 allCode k) w0 w1) ∧
    toRows wManifestCore.proxyUpgrades = [wRow] ∧
    holderTuple (wEnvWith 0 allCode wKeccak) w0 = [1]

/-- **A REPLAY FROM AN UNOWNED `ProxyAdmin` SUCCEEDED AT `e561b9cc2` AND REVERTS NOW.** In
`wUnowned` the row is already applied and the `ProxyAdmin` is not owned by the executor. The
`e561b9cc2` `applyTransition` succeeds there (a skip sends no `onlyOwner` call). The
`b17415d20` leg through `DefaultProxyUpgradeEngine` refuses for every hash function, because
the engine first requires `proxyAdmin.owner() == address(this)`
(`engines/DefaultProxyUpgradeEngine.sol:33-37`). -/
def Properties.UnownedAdminReplayNowReverts : Prop :=
  ProxyUpgradeCurrent.ApplyTransition (rowConfig allCode wUnowned) .ctm
      ⟨wT, .ctm, toRows wInv⟩ wUnowned.impl wUnowned.impl ∧
    (rowConfig allCode wUnowned).adminOwner ≠ (rowConfig allCode wUnowned).self ∧
    ∀ k : List UInt8 → UInt256,
      ¬ Accepts (wEnvWith 8 allCode k) defaultEngine wT wManifest .ctm wStore wUnowned

/-! ## Each check is load-bearing -/

/-- **THE OWNERSHIP CHECK (`:93-95`) IS LOAD-BEARING.** For every hash function, an engine
whose hook writes `6` into the executor's owner slot is refused from `w0`, and the same leg
with only the ownership check deleted succeeds, ending with the executor owned by `6` instead
of `100`. -/
def Properties.OwnerSlotWriteIsCaught : Prop :=
  (∀ k : List UInt8 → UInt256,
      ¬ Accepts (wEnvWith 8 allCode k) ownerWriteEngine wT wManifest .ctm wStore w0) ∧
    (∀ k : List UInt8 → UInt256,
      LegWithout .ownership (wEnvWith 8 allCode k) ownerWriteEngine wT wManifest .ctm wStore w0
        { wStore with owner := 6 } w1) ∧
    wStore.owner = 100

/-- **THE HOLDERS CHECK (`:96-98`) IS LOAD-BEARING: A CTM NOMINATION.** Take an engine whose
`_afterSwaps` calls `ctm.transferOwnership(7)`, from `w0`. For every hash function, the leg
accepts it only if the hash collides on the compared preimages of `w0` and `wNominated`; the
toy hash `wKeccak` does not collide there, so under it the leg refuses. The same leg with only
the holders check deleted succeeds for every hash function and ends in `wNominated`, where the
CTM's pending owner is `7`. -/
def Properties.CtmNominationIsCaught : Prop :=
  (∀ k : List UInt8 → UInt256,
      Accepts (wEnvWith 8 allCode k) ctmNominateEngine wT wManifest .ctm wStore w0 →
        HoldersBreak (wEnvWith 8 allCode k) w0 wNominated) ∧
    ¬ HoldersBreak wEnv w0 wNominated ∧
    ¬ Accepts wEnv ctmNominateEngine wT wManifest .ctm wStore w0 ∧
    (∀ k : List UInt8 → UInt256,
      LegWithout .holders (wEnvWith 8 allCode k) ctmNominateEngine wT wManifest .ctm wStore w0
        wStore wNominated) ∧
    wNominated.pending 8 = 7

/-- **THE HOLDERS CHECK IS LOAD-BEARING: A RE-POINTED SERVERNOTIFIER.** Take an engine whose
`_afterSwaps` calls `ctm.setServerNotifier(13)`, from `w0`, where the CTM names notifier `9`.
`_domainHolders` reads the notifier in each world and hashes its address (`:123`, `:131`).
For every hash function, the leg accepts the engine only if the hash collides on the compared
preimages of `w0` and `wRepointed`; under `wKeccak` it does not, and the leg refuses. The same
leg with only the holders check deleted succeeds for every hash function and ends in
`wRepointed`, where the CTM names notifier `13`, owned by `6`. -/
def Properties.NotifierRepointIsCaught : Prop :=
  (∀ k : List UInt8 → UInt256,
      Accepts (wEnvWith 8 allCode k) notifierRepointEngine wT wManifest .ctm wStore w0 →
        HoldersBreak (wEnvWith 8 allCode k) w0 wRepointed) ∧
    ¬ HoldersBreak wEnv w0 wRepointed ∧
    ¬ Accepts wEnv notifierRepointEngine wT wManifest .ctm wStore w0 ∧
    (∀ k : List UInt8 → UInt256,
      LegWithout .holders (wEnvWith 8 allCode k) notifierRepointEngine wT wManifest .ctm wStore
        w0 wStore wRepointed) ∧
    wEnv.serverNotifierAddress w0 = 9 ∧ wEnv.serverNotifierAddress wRepointed = 13 ∧
    wRepointed.owner 13 = 6

/-- **THE ROWS CHECK (`:103`) IS LOAD-BEARING.** For every hash function, an engine whose
`_afterSwaps` moves the row's proxy back to its old implementation (after the engine's own
`requireRowsApplied`) is refused from `w0`, and the same leg with only the rows check deleted
succeeds, ending in `wMovedBack` with proxy `5` at `10`. This is the case the library names
(`libraries/ProxyUpgradeRowLib.sol:131-132`): "a follow-up hook that moves a proxy of the row
set is caught too". -/
def Properties.RowMovedBackIsCaught : Prop :=
  (∀ k : List UInt8 → UInt256,
      ¬ Accepts (wEnvWith 8 allCode k) moveBackEngine wT wManifest .ctm wStore w0) ∧
    (∀ k : List UInt8 → UInt256,
      LegWithout .rows (wEnvWith 8 allCode k) moveBackEngine wT wManifest .ctm wStore w0 wStore
        wMovedBack) ∧
    wMovedBack.impl 5 = 10

/-- **THE CTM-ADMIN CHECK (`:75-77`) IS LOAD-BEARING.** In `wAliased` the CTM's admin role is
the `ProxyAdmin` `2`, which administers the CTM proxy. Take an engine whose `_afterSwaps`
calls `ProxyAdmin.changeProxyAdmin(ctm, 13)`. For every hash function:

* the leg refuses it (the check at `:75-77`);
* the same leg with only that check deleted succeeds and ends in `wCtmMoved`, where `13`, not
  the `ProxyAdmin`, administers the CTM proxy. The holder tuple is the same word for word
  before and after: `getProxyAdmin(ctm)` answered `2` as the CTM's admin, and answers `2`
  afterwards as the CTM's admin role (`AdminFallsThrough`), which is the case the comment at
  `:72-74` describes;
* from `w0`, where the CTM's admin role is `15`, the same engine is accepted only if the hash
  collides on the compared preimages. -/
def Properties.AliasedCtmMoveIsCaughtByTheAdminCheck : Prop :=
  (∀ k : List UInt8 → UInt256,
      ¬ Accepts (wEnvWith 8 allCode k) ctmMoveEngine wT wManifest .ctm wStore wAliased) ∧
    (∀ k : List UInt8 → UInt256,
      LegWithout .ctmAdmin (wEnvWith 8 allCode k) ctmMoveEngine wT wManifest .ctm wStore wAliased
        wStore wCtmMoved ∧
      holderTuple (wEnvWith 8 allCode k) wCtmMoved = holderTuple (wEnvWith 8 allCode k) wAliased ∧
      AdminFallsThrough (wEnvWith 8 allCode k)) ∧
    wAliased.adminSlot 8 = 2 ∧ wAliased.roleAdmin 8 = 2 ∧ wCtmMoved.adminSlot 8 = 13 ∧
    (∀ (k : List UInt8 → UInt256) (st' : Store) (s' : WState),
      Leg (wEnvWith 8 allCode k) ctmMoveEngine wT wManifest .ctm wStore w0 st' s' →
        HoldersBreak (wEnvWith 8 allCode k) w0 s')

/-- **WHAT `requireCode(engine)` (`:62-63`) ADDS.** With the check deleted, a leg whose engine
has no code succeeds exactly when the transition is code, the manifest is of the executor's
domain with the right inventory length, a bound CTM's `admin()` is not the `ProxyAdmin`, every
row is already at its `implNew` (vacuously so for an empty row set), and nothing changes:
neither executor storage nor the world. With the check, it never succeeds. -/
def Properties.CodelessEngineLegIff : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ),
    ¬ E.hasCode s M.proxyUpgradeEngine →
      (LegWithout .engineCode E eng T M d st s st' s' ↔
        LegPre E T M d s ∧ M.domain = d ∧ (E.chainTypeManager ≠ 0 → E.ctmAdmin s ≠ E.proxyAdmin) ∧
          st' = st ∧ s' = s ∧ RowsApplied (E.impl s) (toRows M.proxyUpgrades)) ∧
      ¬ Leg E eng T M d st s st' s'

/-- **A CODELESS ENGINE CANNOT APPLY A ROW.** Without the code check, a codeless engine's leg
from a state where some row is not at its target fails anyway (the rows check). The premises
are satisfiable (`CodelessEngineFreshStateIsRefused`). -/
def Properties.CodelessEngineMovesNothing : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ),
    ¬ E.hasCode s M.proxyUpgradeEngine →
      (∃ r ∈ toRows M.proxyUpgrades, E.impl s r.proxy ≠ r.implNew) →
      ¬ AcceptsWithout .engineCode E eng T M d st s

/-- **`CodelessEngineMovesNothing` ON AN INSTANCE.** In `w0` the engine `4` has no code under
`noEngineCode` and the row's proxy `5` is at `10`, not `11`; the leg without the code check
refuses. -/
def Properties.CodelessEngineFreshStateIsRefused : Prop :=
  ¬ wEnvCodeless.hasCode w0 wManifest.proxyUpgradeEngine ∧
    (∃ r ∈ toRows wManifest.proxyUpgrades, wEnvCodeless.impl w0 r.proxy ≠ r.implNew) ∧
    ¬ AcceptsWithout .engineCode wEnvCodeless defaultEngine wT wManifest .ctm wStore w0

/-- **`requireCode(engine)` IS LOAD-BEARING ON A REPLAY.** With a codeless engine and the row
already applied (`w1`), the leg without the code check succeeds and changes nothing; the leg
refuses. -/
def Properties.CodelessEngineReplayIsCaught : Prop :=
  LegWithout .engineCode wEnvCodeless defaultEngine wT wManifest .ctm wStore w1 wStore w1 ∧
    ¬ Accepts wEnvCodeless defaultEngine wT wManifest .ctm wStore w1

/-- **`requireCode(engine)` IS LOAD-BEARING ON AN EMPTY TRANSITION.** With a codeless engine
and no active slot, the leg without the code check succeeds from `w0` and changes nothing; the
leg refuses. A `ProxyUpgradeTransition` object cannot carry such an inventory (its constructor
refuses one with no participating row, `objects/ProxyUpgradeTransition.sol:34-36`); the
executor does not check that. -/
def Properties.CodelessEngineEmptyTransitionIsCaught : Prop :=
  LegWithout .engineCode wEnvCodeless defaultEngine wT wManifestEmpty .ctm wStore w0 wStore w0 ∧
    ¬ Accepts wEnvCodeless defaultEngine wT wManifestEmpty .ctm wStore w0

/-- **THE DOMAIN CHECK (`:59-61`) IS LOAD-BEARING.** A manifest that says `Core` and carries a
21-slot inventory is refused by the CTM executor from `w0`, and the same leg with only the
domain check deleted succeeds, ending in `w1`: the engine and the length check both use the
executor's domain, not the manifest's. The manifest's inventory does not have its own domain's
length, so `DomainCheckRedundantAtConstructorLength` does not apply to it. -/
def Properties.ForeignDomainManifestIsCaught : Prop :=
  ¬ Accepts wEnv defaultEngine wT wManifestForeign .ctm wStore w0 ∧
    LegWithout .domain wEnv defaultEngine wT wManifestForeign .ctm wStore w0 wStore w1 ∧
    wManifestForeign.proxyUpgrades.length ≠ inventoryLength wManifestForeign.domain

/-- **THE DOMAIN CHECK ADDS NOTHING FOR A MANIFEST OF ITS OWN DOMAIN'S LENGTH.** If the
manifest's inventory has `inventoryLength(manifest.domain)` slots, which the
`ProxyUpgradeTransition` constructor enforces (`objects/ProxyUpgradeTransition.sol:28-31`),
then for every engine the leg without the domain check succeeds exactly when the leg does:
the length check at `:99-102` refuses the other domain, after the engine has run. This rests
on the two domains' lengths being different (9 and 21 at `b17415d20`). The premise holds on
`DefaultEngineLegWitness`'s manifest. -/
def Properties.DomainCheckRedundantAtConstructorLength : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ),
    M.proxyUpgrades.length = inventoryLength M.domain →
      (LegWithout .domain E eng T M d st s st' s' ↔ Leg E eng T M d st s st' s')

/-! ## Boundaries -/

/-- **THE COLLISION DISJUNCT IS NEEDED.** Under a hash that maps everything to `0`, the CTM
nomination engine passes every check from `w0`, the holder tuple changes, and the compared
preimages collide. So (b) cannot be strengthened to plain equality without a premise on
`keccak256`. -/
def Properties.HoldersCollisionIsNeeded : Prop :=
  Leg (wEnvWith 8 allCode constKeccak) ctmNominateEngine wT wManifest .ctm wStore w0 wStore
      wNominated ∧
    holderTuple (wEnvWith 8 allCode constKeccak) wNominated ≠
      holderTuple (wEnvWith 8 allCode constKeccak) w0 ∧
    HoldersBreak (wEnvWith 8 allCode constKeccak) w0 wNominated

/-- **THE CHECKS DO NOT COVER PROXIES NO ROW NAMES.** For every hash function, an engine whose
`_afterSwaps` upgrades proxy `6`, which no row names, passes every check from `w0`, and proxy
`6` moved from `10` to `12`. -/
def Properties.UnlistedProxyMovePassesEveryCheck : Prop :=
  (∀ k : List UInt8 → UInt256,
      Leg (wEnvWith 8 allCode k) unlistedMoveEngine wT wManifest .ctm wStore w0 wStore
        wUnlisted) ∧
    (∀ r ∈ toRows wManifest.proxyUpgrades, r.proxy ≠ 6) ∧
    w0.impl 6 = 10 ∧ wUnlisted.impl 6 = 12

/-- **THE CHECKS DO NOT COVER UNDECLARED STORAGE SLOTS.** For every hash function, an engine
whose hook writes slot `7` of the executor's storage passes every check from `w0`, and that
slot changed from `0` to `1`. -/
def Properties.UndeclaredSlotWritePassesEveryCheck : Prop :=
  ∃ st' : Store,
    (∀ k : List UInt8 → UInt256,
      Leg (wEnvWith 8 allCode k) slotWriteEngine wT wManifest .ctm wStore w0 st' w1) ∧
    wStore.other 7 = 0 ∧ st'.other 7 = 1

end Contracts.EngineLegV35
