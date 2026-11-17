import EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.EngineLegV35

/-!
# Properties: what a successful engine leg pins, and each check is load-bearing

Statements about `EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.EngineLegV35`
(`executors/ProxyUpgradeExecutorBase.sol:48-98` at `d9f6789`). Proofs are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.EngineLegV35`.

## What a successful leg pins, for every engine

The engine is an arbitrary relation, so these hold for any code a transition can pin:

* the engine that ran is the one the manifest names, with the context the executor built and
  the pinned inventory (`LegRunsThePinnedEngine`, `:54-78`);
* the executor's owner and pending owner are unchanged (`LegKeepsExecutorOwnership`, `:87-89`),
  so the only executor storage that can differ is slots the executors do not declare
  (`LegChangesOnlyUndeclaredExecutorStorage`);
* the holder tuple of the domain is unchanged, or the two preimages the check hashed differ
  and collide under `keccak256` (`LegKeepsDomainHoldersOrCollides`, `:90-92`; getter by
  getter in `LegKeepsNamedHoldersUnlessCollision`). Nothing is assumed about `keccak256`; the
  encoding contributes no collisions (`AbiEncodeInjective`). The check refuses no engine that
  leaves the tuple alone (`UnchangedHoldersPassTheCheck`);
* every row of the inventory runs its `implNew` (`LegLandsEveryRow`,
  `LegLandsEveryActiveSlot`, `:93-97`).

## `DefaultProxyUpgradeEngine`

In the concrete world a leg through `DefaultProxyUpgradeEngine` is the `e561b9cc2`
`applyTransition` plus three requirements: the engine is code, the executor owns the
`ProxyAdmin`, and the inventory has the domain's length (`DefaultEngineLegIsApplyTransition`).
The post-checks never refuse it. The owner requirement is new behaviour
(`UnownedAdminReplayNowReverts`). `DefaultEngineLegWitness` and `DefaultEngineCoreLegWitness`
are the satisfiability witnesses: one row, both domains, every hash function, no collision.

## Each check is load-bearing

For each check there is an engine or manifest that the leg refuses and that the same leg with
only that check deleted accepts: an owner-slot write (`OwnerSlotWriteIsCaught`), a
`ctm.transferOwnership` (`CtmNominationIsCaught`), an `_afterSwaps` that moves a row's proxy
back (`RowMovedBackIsCaught`), and a manifest of the other domain
(`ForeignDomainManifestIsCaught`). Two of the checks are load-bearing only in a corner:

* `requireCode(engine)` (`:59-60`): without it, a codeless engine leg succeeds exactly when
  every row is already at its target, and then nothing changes (`CodelessEngineLegIff`,
  `CodelessEngineMovesNothing`); so it matters on a replay and on an empty transition
  (`CodelessEngineReplayIsCaught`, `CodelessEngineEmptyTransitionIsCaught`).
* the domain check (`:56-58`): for a manifest whose inventory has its own domain's length,
  which the `ProxyUpgradeTransition` constructor enforces, the length check at `:93-96`
  already refuses the other domain (`DomainCheckRedundantAtConstructorLength`).

## Boundaries

The collision disjunct cannot be dropped (`HoldersCollisionIsNeeded`). The checks say nothing
about proxies no row names (`UnlistedProxyMovePassesEveryCheck`), about which ServerNotifier
the CTM names afterwards (`NotifierRepointPassesEveryCheck`), or about executor storage slots
the executors do not declare (`UndeclaredSlotWritePassesEveryCheck`). The source says so:
"Anything else the engine does is what governance reviewed" (`:37-38`).
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
executor's domain, and the engine code ran with the context built from the executor's bindings
(`:62-68`) and the manifest's inventory (`:76-78`): its calls took the world from `s` to
`s'`. -/
def Properties.LegRunsThePinnedEngine : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ),
    Leg E eng T M d st s st' s' →
      E.hasCode s T ∧ M.domain = d ∧ E.hasCode s M.proxyUpgradeEngine ∧
        ∃ calls, eng ⟨T, M.proxyUpgradeEngine, d, E.proxyAdmin, E.chainTypeManager⟩
          M.proxyUpgrades st s st' calls ∧ CallRun E s calls s'

/-- **(a) THE ENGINE CANNOT CHANGE WHO GOVERNS THE EXECUTOR.** For every engine, a successful
leg leaves the executor's `owner()` and `pendingOwner()` as they were (`:69-70`, `:87-89`). -/
def Properties.LegKeepsExecutorOwnership : Prop :=
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
engine and every hash function, after a successful leg the holder tuple (`:104-105`; the
ServerNotifier is the one read at `:71-73`, before the engine ran) is what it was, or one of
the named `abi.encode` preimages compared at `:74` and `:90` differs between before and after
while its hash does not (`HoldersBreak`). -/
def Properties.LegKeepsDomainHoldersOrCollides : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ),
    Leg E eng T M d st s st' s' →
      holderTuple E (notifierAt E s) s' = holderTuple E (notifierAt E s) s ∨
        HoldersBreak E (notifierAt E s) s s'

/-- **(b), GETTER BY GETTER.** After a successful leg with no collision on the compared
preimages: the `ProxyAdmin`'s owner is unchanged; with a bound CTM, so are the CTM's owner,
pending owner and proxy admin; and with a ServerNotifier `n` read before the engine, so are
`n`'s owner, pending owner and proxy admin. The premise is satisfiable
(`DefaultEngineLegWitness`). -/
def Properties.LegKeepsNamedHoldersUnlessCollision : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ),
    Leg E eng T M d st s st' s' → ¬ HoldersBreak E (notifierAt E s) s s' →
      E.paOwner s' = E.paOwner s ∧
      (E.chainTypeManager ≠ 0 →
        E.ownerOf s' E.chainTypeManager = E.ownerOf s E.chainTypeManager ∧
        E.pendingOwnerOf s' E.chainTypeManager = E.pendingOwnerOf s E.chainTypeManager ∧
        E.getProxyAdmin s' E.chainTypeManager = E.getProxyAdmin s E.chainTypeManager) ∧
      (E.chainTypeManager ≠ 0 → notifierAt E s ≠ 0 →
        E.ownerOf s' (notifierAt E s) = E.ownerOf s (notifierAt E s) ∧
        E.pendingOwnerOf s' (notifierAt E s) = E.pendingOwnerOf s (notifierAt E s) ∧
        E.getProxyAdmin s' (notifierAt E s) = E.getProxyAdmin s (notifierAt E s))

/-- **THE HOLDERS CHECK REFUSES NO ENGINE THAT LEAVES THE HOLDERS ALONE.** If the holder tuple
is the same in two worlds, so is the hash `_domainHolders` returns, for every hash function. -/
def Properties.UnchangedHoldersPassTheCheck : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (n : Address) (s s' : σ),
    holderTuple E n s' = holderTuple E n s → domainHolders E n s' = domainHolders E n s

/-- **(c) EVERY ROW LANDS.** For every engine, after a successful leg every row of
`toRows(manifest.proxyUpgrades, inventoryLength(domain))` has
`getProxyImplementation(row.proxy) = row.implNew` (`:93-97`;
`libraries/ProxyUpgradeRowLib.sol:128-136`), and the inventory had exactly
`inventoryLength(domain)` slots (`libraries/ProxyUpgradeRowLib.sol:57-59`). -/
def Properties.LegLandsEveryRow : Prop :=
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

/-- **A DEFAULT-ENGINE LEG IS `applyTransition`, PLUS THREE REQUIREMENTS.** In the concrete
world (any bound CTM, code predicate, hash, manifest, storage and world state; inert
reinitializers), a leg through `DefaultProxyUpgradeEngine`
(`engines/DefaultProxyUpgradeEngine.sol:32-46`) succeeds exactly when

* the engine address is code (`:59-60`),
* the executor owns the `ProxyAdmin` (`engines/DefaultProxyUpgradeEngine.sol:33-37`),
* the inventory has the domain's length, and
* the `e561b9cc2` `applyTransition` of the transition's rows succeeds on the implementations,

and then the executor's storage is unchanged and the world differs only in the
implementations. So the engine "applies the rows … and nothing else"
(`engines/DefaultProxyUpgradeEngine.sol:15-17`), and none of the three post-checks ever
refuses it. -/
def Properties.DefaultEngineLegIsApplyTransition : Prop :=
  ∀ (c : Address) (code : Address → Prop) (k : List UInt8 → UInt256) (T : Address)
    (M : Manifest) (d : Domain) (st : Store) (s : WState) (st' : Store) (s' : WState),
    Leg (wEnvWith c code k) (defaultEngineWith code) T M d st s st' s' ↔
      code M.proxyUpgradeEngine ∧ s.paOwner = 1 ∧ M.proxyUpgrades.length = inventoryLength d ∧
      ProxyUpgradeCurrent.ApplyTransition (rowConfig code s) d
        ⟨T, M.domain, toRows M.proxyUpgrades⟩ s.impl s'.impl ∧
      st' = st ∧ s' = { s with impl := s'.impl }

/-- **(d) A DEFAULT-ENGINE LEG PASSES EVERY CHECK.** In the concrete world, for every hash
function, `DefaultProxyUpgradeEngine` with one row (`5: 10 → 11`) in the CTM domain, whose
ServerNotifier `9` is nonzero, succeeds from `w0` and ends in `w1` with executor storage
unchanged, and no compared preimage collides. Proxy `5` moves and the holder tuple has all
seven entries. -/
def Properties.DefaultEngineLegWitness : Prop :=
  (∀ k : List UInt8 → UInt256,
      Leg (wEnvWith 8 allCode k) defaultEngine wT wManifest .ctm wStore w0 wStore w1 ∧
        ¬ HoldersBreak (wEnvWith 8 allCode k) 9 w0 w1) ∧
    notifierAt wEnv w0 = 9 ∧ toRows wManifest.proxyUpgrades = [wRow] ∧
    w0.impl 5 = 10 ∧ w1.impl 5 = 11 ∧
    (holderTuple wEnv 9 w0).length = 7

/-- **(d) THE SAME FOR THE `Core` EXECUTOR.** With no bound CTM (`_chainTypeManager = 0`), for
every hash function, `DefaultProxyUpgradeEngine` with one row in a 9-slot `Core` inventory
succeeds from `w0` and ends in `w1`, and the compared preimage does not collide. The holder
tuple is the `ProxyAdmin`'s owner alone. -/
def Properties.DefaultEngineCoreLegWitness : Prop :=
  (∀ k : List UInt8 → UInt256,
      Leg (wEnvWith 0 allCode k) defaultEngine wT wManifestCore .core wStore w0 wStore w1 ∧
        ¬ HoldersBreak (wEnvWith 0 allCode k) 0 w0 w1) ∧
    notifierAt (wEnvWith 0 allCode wKeccak) w0 = 0 ∧
    toRows wManifestCore.proxyUpgrades = [wRow] ∧
    holderTuple (wEnvWith 0 allCode wKeccak) 0 w0 = [1]

/-- **A REPLAY FROM AN UNOWNED `ProxyAdmin` SUCCEEDED AT `e561b9cc2` AND REVERTS NOW.** In
`wUnowned` the row is already applied and the `ProxyAdmin` is not owned by the executor. The
`e561b9cc2` `applyTransition` succeeds there (a skip sends no `onlyOwner` call). The
`d9f6789` leg through `DefaultProxyUpgradeEngine` refuses, because the engine first requires
`proxyAdmin.owner() == address(this)` (`engines/DefaultProxyUpgradeEngine.sol:33-37`). -/
def Properties.UnownedAdminReplayNowReverts : Prop :=
  ProxyUpgradeCurrent.ApplyTransition (rowConfig allCode wUnowned) .ctm
      ⟨wT, .ctm, toRows wInv⟩ wUnowned.impl wUnowned.impl ∧
    (rowConfig allCode wUnowned).adminOwner ≠ (rowConfig allCode wUnowned).self ∧
    ¬ Accepts wEnv defaultEngine wT wManifest .ctm wStore wUnowned

/-! ## Each check is load-bearing -/

/-- **THE OWNERSHIP CHECK (`:87-89`) IS LOAD-BEARING.** An engine whose hook writes the
executor's owner slot is refused from `w0`, and accepted by the same leg with only the
ownership check deleted. -/
def Properties.OwnerSlotWriteIsCaught : Prop :=
  ¬ Accepts wEnv ownerWriteEngine wT wManifest .ctm wStore w0 ∧
    AcceptsWithout .ownership wEnv ownerWriteEngine wT wManifest .ctm wStore w0

/-- **THE HOLDERS CHECK (`:90-92`) IS LOAD-BEARING.** Take an engine whose `_afterSwaps` calls
`ctm.transferOwnership(7)`, from `w0`. For every hash function, the leg accepts it only if the
hash collides on the compared preimages of `w0` and `wNominated`; the toy hash `wKeccak` does
not collide there, so the leg refuses it. The same leg with only the holders check deleted
accepts it, for every hash function. -/
def Properties.CtmNominationIsCaught : Prop :=
  (∀ k : List UInt8 → UInt256,
      Accepts (wEnvWith 8 allCode k) ctmNominateEngine wT wManifest .ctm wStore w0 →
        HoldersBreak (wEnvWith 8 allCode k) 9 w0 wNominated) ∧
    ¬ HoldersBreak wEnv 9 w0 wNominated ∧
    ¬ Accepts wEnv ctmNominateEngine wT wManifest .ctm wStore w0 ∧
    (∀ k : List UInt8 → UInt256,
      AcceptsWithout .holders (wEnvWith 8 allCode k) ctmNominateEngine wT wManifest .ctm wStore
        w0)

/-- **THE ROWS CHECK (`:97`) IS LOAD-BEARING.** An engine whose `_afterSwaps` moves the row's
proxy back to its old implementation (after the engine's own `requireRowsApplied`) is refused
from `w0`, and accepted by the same leg with only the rows check deleted. This is the case the
library names (`libraries/ProxyUpgradeRowLib.sol:126-127`): "a follow-up hook that moves a
proxy of the row set is caught too". -/
def Properties.RowMovedBackIsCaught : Prop :=
  ¬ Accepts wEnv moveBackEngine wT wManifest .ctm wStore w0 ∧
    AcceptsWithout .rows wEnv moveBackEngine wT wManifest .ctm wStore w0

/-- **WHAT `requireCode(engine)` (`:59-60`) ADDS.** With the check deleted, a leg whose engine
has no code succeeds exactly when the transition is code, the manifest is of the executor's
domain with the right inventory length, every row is already at its `implNew` (vacuously so
for an empty row set), and nothing changes: neither executor storage nor the world. With the
check, it never succeeds. -/
def Properties.CodelessEngineLegIff : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ) (st' : Store) (s' : σ),
    ¬ E.hasCode s M.proxyUpgradeEngine →
      (LegWithout .engineCode E eng T M d st s st' s' ↔
        LegPre E T M d s ∧ M.domain = d ∧ st' = st ∧ s' = s ∧
          RowsApplied (E.impl s) (toRows M.proxyUpgrades)) ∧
      ¬ Leg E eng T M d st s st' s'

/-- **A CODELESS ENGINE CANNOT APPLY A ROW.** Without the code check, a codeless engine's leg
from a state where some row is not at its target fails anyway (the rows check). -/
def Properties.CodelessEngineMovesNothing : Prop :=
  ∀ (σ κ : Type) (E : Env σ κ) (eng : Engine σ κ) (T : Address) (M : Manifest) (d : Domain)
    (st : Store) (s : σ),
    ¬ E.hasCode s M.proxyUpgradeEngine →
      (∃ r ∈ toRows M.proxyUpgrades, E.impl s r.proxy ≠ r.implNew) →
      ¬ AcceptsWithout .engineCode E eng T M d st s

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

/-- **THE DOMAIN CHECK (`:56-58`) IS LOAD-BEARING.** A manifest that says `Core` and carries a
21-slot inventory is refused by the CTM executor from `w0`, and accepted by the same leg with
only the domain check deleted: the engine and the length check both use the executor's
domain, not the manifest's. -/
def Properties.ForeignDomainManifestIsCaught : Prop :=
  ¬ Accepts wEnv defaultEngine wT wManifestForeign .ctm wStore w0 ∧
    AcceptsWithout .domain wEnv defaultEngine wT wManifestForeign .ctm wStore w0

/-- **THE DOMAIN CHECK ADDS NOTHING FOR A MANIFEST OF ITS OWN DOMAIN'S LENGTH.** If the
manifest's inventory has `inventoryLength(manifest.domain)` slots, which the
`ProxyUpgradeTransition` constructor enforces (`objects/ProxyUpgradeTransition.sol:28-31`),
then for every engine the leg without the domain check succeeds exactly when the leg does:
the length check at `:93-96` refuses the other domain, after the engine has run. This rests
on the two domains' lengths being different (9 and 21 at `d9f6789`). -/
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
    holderTuple (wEnvWith 8 allCode constKeccak) 9 wNominated ≠
      holderTuple (wEnvWith 8 allCode constKeccak) 9 w0 ∧
    HoldersBreak (wEnvWith 8 allCode constKeccak) 9 w0 wNominated

/-- **THE CHECKS DO NOT COVER PROXIES NO ROW NAMES.** An engine whose `_afterSwaps` upgrades
proxy `6`, which no row names, passes every check from `w0`, and proxy `6` moved from `10` to
`12`. -/
def Properties.UnlistedProxyMovePassesEveryCheck : Prop :=
  Leg wEnv unlistedMoveEngine wT wManifest .ctm wStore w0 wStore wUnlisted ∧
    (∀ r ∈ toRows wManifest.proxyUpgrades, r.proxy ≠ 6) ∧
    w0.impl 6 = 10 ∧ wUnlisted.impl 6 = 12

/-- **THE HOLDERS CHECK READS THE SERVERNOTIFIER THE CTM NAMED BEFORE THE ENGINE RAN.** An
engine whose `_afterSwaps` calls `ctm.setServerNotifier(13)` passes every check from `w0`,
with no collision on the compared preimages. Before the leg the CTM's ServerNotifier is `9`,
owned by the executor `1`; after it the CTM's ServerNotifier is `13`, owned by `6`. The holder
tuple read with the notifier of the time differs before and after; the check compares the
holders of `9` both times (`:71-74`, `:90`, `:103`). -/
def Properties.NotifierRepointPassesEveryCheck : Prop :=
  Leg wEnv notifierRepointEngine wT wManifest .ctm wStore w0 wStore wRepointed ∧
    ¬ HoldersBreak wEnv 9 w0 wRepointed ∧
    notifierAt wEnv w0 = 9 ∧ notifierAt wEnv wRepointed = 13 ∧
    wEnv.ownerOf w0 9 = 1 ∧ wEnv.ownerOf wRepointed 13 = 6 ∧
    holderTuple wEnv (notifierAt wEnv wRepointed) wRepointed ≠
      holderTuple wEnv (notifierAt wEnv w0) w0

/-- **THE CHECKS DO NOT COVER UNDECLARED STORAGE SLOTS.** An engine whose hook writes slot `7`
of the executor's storage passes every check from `w0`, and that slot changed from `0` to
`1`. -/
def Properties.UndeclaredSlotWritePassesEveryCheck : Prop :=
  ∃ st' : Store, Leg wEnv slotWriteEngine wT wManifest .ctm wStore w0 st' w1 ∧
    wStore.other 7 = 0 ∧ st'.other 7 = 1

end Contracts.EngineLegV35
