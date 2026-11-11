import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: who holds the CTM domain's authority across the registry bootstrap

Source: branch `feat/upgrade-simplification` of the zksync-era `contracts` repository,
pinned for this model at commit `e561b9cc2` (2026-10-19), the same commit as
`EraSpec.Contracts.ChainTypeManager`. The branch moves; every `file:line` below is at that
commit. Paths are relative to `l1-contracts/contracts/upgrades/registry/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.RegistryBootstrapMigration.Properties.Authority` and are proved in
`EraSpec.Contracts.RegistryBootstrapMigration.Proofs.Authority`.

## The claim under test

`bootstrap/RegistryBootstrapMigration.sol:48-50`:

    /// @dev Authority is never parked: `migrate()` acquires nothing it does not hand onward in the same
    ///      transaction. Governance transfers ownership in, the migration executes, and ownership
    ///      leaves to the executors before the call returns.

and `validateApplied` (:197-217), whose comment at :213-215 reads "the accept inside
`migrate()` completed, nothing is parked on this spent object".

**"Parked", as the source uses it** (`ParkedOnMigration`): some authority the edge drives
rests with the spent migration object — it owns the CTM, it is the CTM's `Ownable2Step`
nominee, or it owns the CTM-domain `ProxyAdmin`. A spent migration has no function left
that could act with that authority (`migrate` refuses a second run, :263-265, and the
contract has no other state-changing entry point), so authority parked there is stuck.
`validateApplied` additionally requires that **no nomination is outstanding** on the CTM
(`RegistryAuthorityLib.requireNoNomination`, `libraries/RegistryAuthorityLib.sol:109-114`,
called at :55); the model tracks that separately (`AState.ctmPending`).

## The authorities

* The CTM is `Ownable2Step`: `owner` and `pendingOwner`. `transferOwnership(x)` (owner
  only) sets `pendingOwner = x`; `acceptOwnership()` requires `msg.sender == pendingOwner`,
  makes it the owner and clears `pendingOwner`.
* The CTM-domain `ProxyAdmin` is plain `Ownable` (`:294-295`: "The ProxyAdmin is plain
  `Ownable`, so its transfer lands immediately"); `transferOwnership(x)` requires `x != 0`.

## `migrate()` (:262-304)

    if (executed) { revert BootstrapAlreadyExecuted(); }                          // :263-265
    executed = true;                                                               // :266
    if (Ownable2Step(m.ctm).pendingOwner() == address(this)) {                     // :271
        Ownable2Step(m.ctm).acceptOwnership(); }                                   // :272
    validate();                                                                    // :274
    ProxyUpgradeRowLib.applyRows(m.ctmProxyAdmin, ...);                            // :276-279
    ctm.setNewVersionUpgrade({... _oldProtocolVersion: m.expectedProtocolVersion,
                              _newRelease: m.currentRelease });                    // :287-292
    Ownable2Step(m.ctm).transferOwnership(m.ctmExecutor);                          // :299
    m.ctmProxyAdmin.transferOwnership(m.ctmExecutor);                              // :300
    CTMUpgradeExecutor(payable(m.ctmExecutor)).acceptCTMOwnership();               // :301

`validate()` (:149-186) requires, among reject-only code checks:

    if (ctmOwner != address(this)) { revert BootstrapAuthorityNotHeld(...); }      // :153-156
    if (proxyAdminOwner != address(this)) { revert BootstrapAuthorityNotHeld(...); } // :157-160
    RegistryAuthorityLib.requireExecutorAuthorities(authority);                    // :163
    if (liveVersion != m.expectedProtocolVersion) { revert OutdatedProtocolVersion(...); } // :166-169
    RegistryAuthorityLib.requireNotifierHandedOver(authority);                     // :171

and `requireExecutorAuthorities` (`libraries/RegistryAuthorityLib.sol:70-86`) checks the
executors **by their answers to getters**: code present (:71-72), `owner() == governance`
and `pendingOwner() == 0` for both (:73-74 → :118-124), `CHAIN_TYPE_MANAGER() == ctm` and
`CTM_PROXY_ADMIN() == ctmProxyAdmin` (:76-78), and the core executor's `PROXY_ADMIN()`
owned by the core executor (:80-85). Nothing checks that the code at `ctmExecutor` *is* a
`CTMUpgradeExecutor`.

A genuine `CTMUpgradeExecutor.acceptCTMOwnership` (`executors/CTMUpgradeExecutor.sol:55-61`):

    if (msg.sender != owner() && msg.sender != ctm.owner()) { revert Unauthorized(msg.sender); } // :57-59
    ctm.acceptOwnership();                                                         // :60

## `validateApplied()` (:197-217)

    if (!executed) { revert BootstrapNotYetExecuted(); }                           // :198-200
    if (liveVersion != derivedNewProtocolVersion) { revert OutdatedProtocolVersion(...); } // :204-207
    if (liveRelease != m.currentRelease) { revert BootstrapReleaseNotInstalled(...); } // :208-211
    RegistryAuthorityLib.requireRegistryAuthority(_authority(m));                  // :216

where `requireRegistryAuthority` (`libraries/RegistryAuthorityLib.sol:50-62`) requires the
CTM owned by the CTM executor (:51-54), no CTM nomination (:55), the `ProxyAdmin` owned by
the CTM executor (:56-59), and the executor and notifier checks again (:60-61).

## The bundle

`RegistryBootstrapSequence.actions()` (`bootstrap/RegistryBootstrapSequence.sol:68-134`)
derives the governance bundle; its last four calls are:

    Ownable2Step.transferOwnership(MIGRATION)   on m.ctm            // :106-110
    Ownable.transferOwnership(MIGRATION)        on m.ctmProxyAdmin  // :111-119
    RegistryBootstrapMigration.migrate()                            // :120-124
    RegistryBootstrapMigration.validateApplied()                    // :125-133

"one bundle ending with the completion check, so a failing check reverts the whole
bootstrap" is the design (`validateApplied`'s notice, :192-193). `Label.bundle` is those
four calls executed atomically; the earlier calls (notifier accept, ecosystem `ProxyAdmin`
handover, core leg) are summarised by the configuration flags `coreHeld` and `notifierOk`.

## Modelling choices

* **A revert is the absence of a step.** Reject-only checks that read nothing modelled are
  omitted: code existence of the engine, composer and release (:173-178), published L2
  bytecodes (:181-184), `release.validate()` (:185), the proxy rows' own checks
  (:276-279), and the deadline. Omitting them only adds runs.
* **Executors are their getters** (`ExecView`), fixed for the run, plus one bit saying
  whether `acceptCTMOwnership()` runs the genuine logic or returns without effect. The
  migration's own address answers no executor getter: `RegistryBootstrapMigration`
  declares no `owner()`, so `Ownable2Step(M).owner()` reverts (`Config.migNoExec`).
* **Other actors over-approximate.** Any owner other than the migration may nominate,
  move the `ProxyAdmin`, or move the CTM's version; any nominee other than the migration
  may accept. The migration acts only inside `migrate`. Over-approximating the others
  only adds runs.
* **The CTM implementation swap** applied by the rows (:276-279) keeps the `Ownable2Step`
  storage. The model assumes the new implementation reads the same owner slots.
* **Versions are `ℕ`**; the registry `setNewVersionUpgrade` (`ChainTypeManager.sol:799-818`)
  requires the old version to be the live one and the new one (the release's own) to be
  larger (`_commitVersionEdge`, :531-539), and installs the release (:817).
-/

namespace Contracts.RegistryBootstrapMigration

open Clear

/-- Addresses as 256-bit words; `0` is the zero address. -/
abbrev Address := UInt256

/-- What an executor-shaped contract answers, and whether its `acceptCTMOwnership()` runs
`CTMUpgradeExecutor`'s logic (`executors/CTMUpgradeExecutor.sol:55-61`) or returns
without effect. -/
structure ExecView where
  /-- `owner()`. -/
  owner : Address
  /-- `pendingOwner()`. -/
  pending : Address
  /-- `CHAIN_TYPE_MANAGER()`. -/
  ctmBinding : Address
  /-- `CTM_PROXY_ADMIN()`. -/
  paBinding : Address
  /-- `acceptCTMOwnership()` calls `CHAIN_TYPE_MANAGER.acceptOwnership()` after the caller
  check (`true`), or returns without effect (`false`). -/
  genuineAccept : Bool
deriving DecidableEq

/-- The fields of the `BootstrapManifest` the authority model reads. -/
structure Manifest where
  /-- `ctm`. -/
  ctm : Address
  /-- `ctmProxyAdmin`. -/
  pa : Address
  /-- `ctmExecutor`. -/
  E : Address
  /-- `coreExecutor`. -/
  core : Address
  /-- `governance`. -/
  G : Address
  /-- `expectedProtocolVersion`. -/
  expectedPv : ℕ
  /-- `currentRelease`, the genesis release. -/
  release : Address
  /-- `derivedNewProtocolVersion`: the genesis release's `protocolVersion()`, read at
  construction (:80-82). -/
  newPv : ℕ
deriving DecidableEq

/-- The deployed migration, its manifest, and the fixed answers of the other contracts. -/
structure Config where
  /-- The migration's own address (`address(this)`). -/
  M : Address
  /-- Its manifest. -/
  m : Manifest
  /-- Executor getters, `none` where a getter call reverts (no code, or no such function). -/
  exec : Address → Option ExecView
  /-- `coreExecutor.PROXY_ADMIN().owner() == coreExecutor`
  (`libraries/RegistryAuthorityLib.sol:80-85`). -/
  coreHeld : Bool
  /-- `requireNotifierHandedOver` passes (`libraries/RegistryAuthorityLib.sol:91-105`). -/
  notifierOk : Bool
  /-- The migration answers no `owner()`: `RegistryBootstrapMigration` declares none. -/
  migNoExec : exec M = none
  /-- The migration is deployed code, so its address is not zero. -/
  migNonzero : M ≠ 0

/-- The authority state the edge drives, and the CTM version state it moves. -/
structure AState where
  /-- The CTM's `owner()`. -/
  ctmOwner : Address
  /-- The CTM's `pendingOwner()`; zero for none. -/
  ctmPending : Address
  /-- The CTM-domain `ProxyAdmin`'s `owner()`. -/
  paOwner : Address
  /-- The CTM's `protocolVersion`. -/
  ctmPv : ℕ
  /-- The CTM's `currentRelease`. -/
  ctmRel : Address
  /-- The migration's `executed` flag (:54). -/
  executed : Bool
deriving DecidableEq

/-- `RegistryAuthorityLib.requireExecutorAuthorities` (`libraries/RegistryAuthorityLib.sol:70-86`). -/
def ExecutorAuthorities (K : Config) : Prop :=
  ∃ e c, K.exec K.m.E = some e ∧ K.exec K.m.core = some c ∧
    e.owner = K.m.G ∧ e.pending = 0 ∧ c.owner = K.m.G ∧ c.pending = 0 ∧
    e.ctmBinding = K.m.ctm ∧ e.paBinding = K.m.pa ∧ K.coreHeld = true

/-- The claim at :271-273: accept a nomination of the migration. -/
def claim (K : Config) (s : AState) : AState :=
  if s.ctmPending = K.M then { s with ctmOwner := K.M, ctmPending := 0 } else s

/-- The state after :287-300, before the executor's accept: the version edge is committed,
the CTM's executor is nominated and the `ProxyAdmin` is the executor's. -/
def handOn (K : Config) (s : AState) : AState :=
  { s with executed := true, ctmPv := K.m.newPv, ctmRel := K.m.release,
           ctmPending := K.m.E, paOwner := K.m.E }

/-- `acceptCTMOwnership()` at :301. The genuine logic's caller check passes (the caller,
the migration, is the CTM's owner), and its `acceptOwnership()` passes (the executor is
the nominee), so it makes the executor the owner and clears the nomination. -/
def executorAccept (K : Config) (s : AState) : AState :=
  match K.exec K.m.E with
  | some e => if e.genuineAccept then { s with ctmOwner := K.m.E, ctmPending := 0 } else s
  | none => s

/-- One successful `migrate()`. -/
inductive MigrateStep (K : Config) : AState → AState → Prop
  /-- The guards, in order: not yet executed (:263-265); after the claim, the CTM is the
  migration's (:153-156); the `ProxyAdmin` is the migration's (:157-160); the executors'
  getters (:163); the departing version (:166-169); the notifier handover (:171); the
  registry CTM's version edge (`ChainTypeManager.sol:537-539`, also the constructor's
  `requireValidEdge`, :86-92); a nonzero executor (constructor, :65). -/
  | mk {s : AState} :
      s.executed = false →
      (claim K s).ctmOwner = K.M →
      s.paOwner = K.M →
      ExecutorAuthorities K →
      s.ctmPv = K.m.expectedPv →
      K.notifierOk = true →
      K.m.expectedPv < K.m.newPv →
      K.m.E ≠ 0 →
      MigrateStep K s (executorAccept K (handOn K (claim K s)))

/-- `validateApplied()` passes (:197-217). -/
def ValidateAppliedPasses (K : Config) (s : AState) : Prop :=
  s.executed = true ∧ s.ctmPv = K.m.newPv ∧ s.ctmRel = K.m.release ∧
    s.ctmOwner = K.m.E ∧ s.ctmPending = 0 ∧ s.paOwner = K.m.E ∧
    ExecutorAuthorities K ∧ K.notifierOk = true

/-- Authority rests with the migration object: it owns the CTM, is the CTM's nominee, or
owns the CTM-domain `ProxyAdmin`. -/
def ParkedOnMigration (K : Config) (s : AState) : Prop :=
  s.ctmOwner = K.M ∨ s.ctmPending = K.M ∨ s.paOwner = K.M

/-- What happens. -/
inductive Label
  /-- The CTM's owner (not the migration) calls `transferOwnership(x)`. -/
  | nominate (x : Address)
  /-- The CTM's nominee (not the migration) calls `acceptOwnership()`. -/
  | accept
  /-- The `ProxyAdmin`'s owner (not the migration) calls `transferOwnership(x)`. -/
  | transferPA (x : Address)
  /-- The CTM's owner (not the migration) moves its version and release. -/
  | legacyMove (v : ℕ) (r : Address)
  /-- Anyone calls `migrate()`. -/
  | migrate
  /-- Governance runs the bundle's last four calls (:106-133) in one transaction. -/
  | bundle
deriving DecidableEq

/-- One successful transaction. -/
inductive AStep (K : Config) : AState → Label → AState → Prop
  | nominate {s : AState} {x : Address} :
      s.ctmOwner ≠ K.M → AStep K s (.nominate x) { s with ctmPending := x }
  | accept {s : AState} :
      s.ctmPending ≠ 0 → s.ctmPending ≠ K.M →
      AStep K s .accept { s with ctmOwner := s.ctmPending, ctmPending := 0 }
  | transferPA {s : AState} {x : Address} :
      s.paOwner ≠ K.M → x ≠ 0 → AStep K s (.transferPA x) { s with paOwner := x }
  | legacyMove {s : AState} {v : ℕ} {r : Address} :
      s.ctmOwner ≠ K.M → AStep K s (.legacyMove v r) { s with ctmPv := v, ctmRel := r }
  | migrate {s s' : AState} : MigrateStep K s s' → AStep K s .migrate s'
  /-- The bundle's calls at `RegistryBootstrapSequence.sol:106-133` in one transaction, sent
  by the owner of both authorities: nominate the migration on the CTM, hand it the
  `ProxyAdmin` (a nonzero address, `Config.migNonzero`), `migrate()`, `validateApplied()`.
  A revert anywhere reverts all four. -/
  | bundle {s s' : AState} :
      s.ctmOwner ≠ K.M → s.paOwner ≠ K.M →
      MigrateStep K { s with ctmPending := K.M, paOwner := K.M } s' →
      ValidateAppliedPasses K s' →
      AStep K s .bundle s'

/-- A sequence of successful transactions. -/
inductive ARun (K : Config) : AState → List Label → AState → Prop
  | nil {s : AState} : ARun K s [] s
  | cons {s s' s'' : AState} {l : Label} {ls : List Label} :
      AStep K s l s' → ARun K s' ls s'' → ARun K s (l :: ls) s''

/-- A transaction that hands authority to the migration. -/
def Label.handsToMigration (K : Config) : Label → Prop
  | .nominate x => x = K.M
  | .transferPA x => x = K.M
  | _ => False

/-! ## Witness data

Migration `50`, CTM `1`, `ProxyAdmin` `2`, CTM executor `3`, core executor `4`,
governance `9`, genesis release `60` at version `35`, departing version `34`. -/

/-- The manifest of the witnesses. -/
def wManifest : Manifest := ⟨1, 2, 3, 4, 9, 34, 60, 35⟩

/-- Executor getters: `3` is bound to CTM `1` and `ProxyAdmin` `2`; `4` is the core
executor; both governed by `9` with no nomination. -/
def wExec (genuine : Bool) : Address → Option ExecView := fun a =>
  if a = 3 then some ⟨9, 0, 1, 2, genuine⟩
  else if a = 4 then some ⟨9, 0, 0, 0, true⟩
  else none

/-- The witness configuration, with a genuine or a non-genuine CTM executor. -/
def wConfig (genuine : Bool) : Config where
  M := 50
  m := wManifest
  exec := wExec genuine
  coreHeld := true
  notifierOk := true
  migNoExec := by simp [wExec]
  migNonzero := by decide

/-- Before the bundle: governance owns the CTM and its `ProxyAdmin`, the CTM is at the
departing version `34` on the pre-registry release `0`, the edge is unspent. -/
def wPre : AState := ⟨9, 0, 9, 34, 0, false⟩

/-- The same, but the CTM's version has drifted to `33`. -/
def wPreDrift : AState := ⟨9, 0, 9, 33, 0, false⟩

end Contracts.RegistryBootstrapMigration
