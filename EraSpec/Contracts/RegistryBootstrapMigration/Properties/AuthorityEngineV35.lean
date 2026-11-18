import EraSpec.Contracts.RegistryBootstrapMigration.Specs.AuthorityEngineV35

/-!
# Properties: the authority results across engine legs (draft/v0.35.0)

Statements about `EraSpec.Contracts.RegistryBootstrapMigration.Specs.AuthorityEngineV35`.
Proofs are in `EraSpec.Contracts.RegistryBootstrapMigration.Proofs.AuthorityEngineV35`.
Source lines are at era-contracts `b17415d20` (`draft/v0.35.0`).

`MigrateLeavesNothingParked`, `NoReparkingAfterMigrate` and `NoReparkingAcrossForwards` were
proved for the `e561b9cc2` system, where no executor makes a delegatecall. At `b17415d20` each
domain executor runs an engine leg (`ProxyUpgradeExecutorBase.sol:51-104`). The engine runs
with the executor's address and storage. What the leg checks about the domain's authority is
the pre-check at :75-77 and the post-checks at :93-98. The results below extend the earlier
ones to runs with legs. Each result about a leg carries, as its only extra disjunct, a
collision of `holdersHash` on that leg's own logged `(before, after)` pair. No injectivity
premise is made on `holdersHash`.

## What holds

"Answering from its slots" below means the CTM's code answers `owner()` and `pendingOwner()`
from its `Ownable2Step` slots (`VState.ctmAnswers = none`), before and after the leg.

* **A leg can neither park nor unpark.**
  * `EngineLegKeepsItsExecutor`: the leg's executor keeps its owner and nominee, exactly.
  * `EngineLegOwnDomainFrameOrCollision`: the authority slots the leg's own checks cover are
    unchanged, or `holdersHash` collides on the leg's logged pair. No premise on senders; a CTM
    leg's CTM answers from its slots.
  * `EngineLegOtherDomainFrame`: the other domain's slots are unchanged, exactly, if that
    domain's holders send no call in the trace (and, for a core leg, no call is `migrate()`).
  * `EngineLegFrameOrCollision` is the two together: the CTM's owner and nominee, both
    `ProxyAdmin`s' owners and both executors' owner and nominee are unchanged, or the hash
    collides.
  * `EngineLegNeitherParksNorUnparks`: authority is parked on the migration after a leg
    exactly if it was before, or the hash collides. For a CTM leg whose CTM answers from its
    slots, with any trace; for a core leg, under the other-domain premise above.
  * `EngineLegKeepsCtmBindingsOrCollision`: a CTM leg leaves the CTM's admin, the notifier the
    CTM names, and that notifier's owner, nominee, CTM and proxy-admin read unchanged, or the
    hash collides; no premise on how the CTM answers. The CTM's admin, the notifier address and
    the notifier's CTM are new in the hash at `b17415d20`.
  * `EngineLegRefusesCtmAdminProxyAdmin`: no CTM leg runs while the CTM's admin is the
    `ProxyAdmin` (:75-77).
  * `LegCannotRecoverParkedCTM`: in the state `NonGenuineExecutorParksTheCTM` leaves, a CTM leg
    whose CTM answers from its slots leaves the CTM parked (or collides), and the recovering
    accept succeeds as a leg exactly when the hash collides. As a call trace it recovers the
    CTM.
  * `LegRenounceReverts`: a CTM leg whose CTM answers from its slots, or a core leg, leaves
    every nonzero owner it checks nonzero (a named notifier's included), or collides. As a call
    trace, the CTM's renounce leaves the CTM with neither owner nor nominee.
* **A leg's calls are a forward.** `EngineLegCallsAreAForward`: projected on `AState`, a leg's
  trace is an `FRun` of `Forward`'s ops (and so is every trace, `CallTracesAreForwards`). Hence:
  * `NoReparkingAcrossEngineLegs`: along runs of the model's transactions, call traces and
    engine legs, from a spent edge with nothing parked and a CTM answering from its slots,
    nothing is re-parked, or the run passes a leg whose hash collides on that leg's logged pair
    (`RunLegCollides`; the run's states are determined, `EngineRunsDeterministic`). Calls and
    core legs hand nothing to the migration by an ownership call and swap no CTM code; CTM legs
    need no premise beyond "does not leave the CTM answering its reads falsely".
  * `MigrateLeavesNothingParkedWithEngineLegs`: the same from the state a genuine `migrate()`
    leaves.
* **The engine reaches only `acceptCTMOwnership` in the executor**
  (`EngineReachesOnlyAcceptCTMOwnership`). Calling back into its executor, it passes no caller
  check but that one's, while the executor's slots name the executor neither as owner nor as
  nominee and it is no chain's admin.
* **The executor's owner is never zero** (`ExecutorOwnerNeverZero`), across the constructor,
  calls, the two-step transfer, `renounceOwnership` (which always reverts) and engine legs, when
  no call is sent by the zero address.

## Countermodels and witnesses

* `CollisionDisjunctNeeded`: a CTM leg that moves the CTM-domain `ProxyAdmin` succeeds exactly
  when `holdersHash` collides on its logged pair, and then the frame fails.
  `NoReparkingCollisionDisjunctNeeded` does the same for the run results, and
  `CtmBindingsCollisionNeeded` for the bindings.
* `NoHolderCheckReparks`: without :96-98 a leg's nomination of the migration re-parks the CTM.
* `EngineCtmSwapReparks`: a leg that swaps the CTM's code for code that rewrites the slots and
  keeps answering the old holders passes for every hash and parks the CTM. The upstream
  documentation names such swaps as outside the check (`docs/registry-driven-upgrades.md:287-290`).
* `CoreLegMayRunMigrate`: a core leg may call the permissionless `migrate()`, which moves the
  CTM domain without any check of the core leg seeing it. So `OtherDomainQuiet`'s `migrate`
  clause is needed.
* `OtherDomainQuietNeeded`: a CTM leg in whose trace the ecosystem `ProxyAdmin`'s owner sends a
  transfer passes for every hash, and the ecosystem `ProxyAdmin` has moved. So
  `OtherDomainQuiet`'s sender clause is needed.
* `UnnamedNotifierIsUnchecked`: with a CTM that names no notifier, a CTM leg may renounce a
  notifier's ownership, for every hash.
* `EngineCtmAdminNominationUnseen`: a CTM leg may nominate a CTM admin unseen, for every hash;
  the CTM's `pendingAdmin` is not in the hash, as `ProxyUpgradeExecutorBase.sol:114-117`
  states. The nominee then takes the role in a later transaction.
* `EngineGatePremisesNeeded`: an executor that owns itself, or is a chain's admin, passes
  `forward` or `upgradeChain`. The :93-95 check does not see an engine that makes the executor
  its own owner and restores the owner before returning; this gives the engine nothing beyond
  the executor's authority, which it already has during the delegatecall.
* `EngineLegTransientWitness`: a leg that hands the CTM away and takes it back succeeds for
  every hash, so the guarantees are about the net effect only. With
  `EngineLegPremisesWitness` it instantiates the premises of every result above.
-/

namespace Contracts.RegistryBootstrapMigration

open Clear

/-! ## A leg can neither park nor unpark -/

/-- **A LEG KEEPS ITS EXECUTOR'S OWNERSHIP, EXACTLY.** After any successful engine leg of
domain `d`, `d`'s executor has the owner and the nominee it had before. There is no collision
disjunct: `:93-95` compares the values. -/
def Properties.EngineLegKeepsItsExecutor : Prop :=
  ∀ (K : Config) (H : DomainHolders → UInt256) (d : LegDomain) (s s' : VState)
    (cs : List VCall),
    EngineLeg K H d s cs s' → s'.execOwner d = s.execOwner d ∧ s'.execPending d = s.execPending d

/-- **A LEG LEAVES THE OTHER DOMAIN ALONE, EXACTLY.** Take a successful engine leg of domain
`d` in which no call is sent by a holder of the other domain (taken at the start), and, for a
core leg, no call is `migrate()`. Then `LegOtherFrame` holds:
* a CTM leg leaves the ecosystem `ProxyAdmin`'s owner and the core executor's owner and nominee
  unchanged;
* a core leg leaves the CTM's owner and nominee, the CTM-domain `ProxyAdmin`'s owner, the CTM
  executor's owner and nominee, and the migration's `executed` unchanged.

There is no collision disjunct: nothing in the leg checks the other domain. -/
def Properties.EngineLegOtherDomainFrame : Prop :=
  ∀ (K : Config) (H : DomainHolders → UInt256) (d : LegDomain) (s s' : VState)
    (cs : List VCall),
    EngineLeg K H d s cs s' → OtherDomainQuiet d s cs → LegOtherFrame d s s'

/-- **A LEG LEAVES ITS OWN DOMAIN'S HOLDERS AS THEY WERE, OR THE HASH COLLIDES ON ITS OWN PAIR.**
Take a successful engine leg of domain `d`, with any `holdersHash` `H` and any call trace. For
a CTM leg, suppose the CTM answers its ownership reads from its slots before and after. Then
either:
* `LegOwnFrame` holds and the logged holders are equal. For a CTM leg: the CTM's owner and
  nominee, the CTM-domain `ProxyAdmin`'s owner and the CTM executor's owner and nominee are
  unchanged. For a core leg: the ecosystem `ProxyAdmin`'s owner and the core executor's owner
  and nominee are unchanged; or
* `H` collides on the leg's own logged `(before, after)` pair.

The start state is arbitrary. For a CTM leg this assumes the CTM proxy sits under the CTM-domain
`ProxyAdmin`: in a state where another admin holds the CTM proxy, that admin's code swaps of the
CTM have no step (Specs, model boundaries), so there the result rests on the missing step. -/
def Properties.EngineLegOwnDomainFrameOrCollision : Prop :=
  ∀ (K : Config) (H : DomainHolders → UInt256) (d : LegDomain) (s s' : VState)
    (cs : List VCall),
    EngineLeg K H d s cs s' →
    (d = .ctm → s.ctmAnswers = none ∧ s'.ctmAnswers = none) →
    (LegOwnFrame d s s' ∧ s'.holders K d = s.holders K d) ∨
      HoldersCollide H (s.holders K d) (s'.holders K d)

/-- **(a) A LEG LEAVES THE AUTHORITY SLOTS AS THEY WERE, OR THE HASH COLLIDES ON ITS OWN PAIR.**
Take a successful engine leg of domain `d`, with any `holdersHash` `H`, in which the other
domain's holders send no call (and, for a core leg, no call is `migrate()`). For a CTM leg,
suppose the CTM answers its ownership reads from its slots before and after. Then either:
* all of `LegAuthFrame` holds (the CTM's owner and nominee, both `ProxyAdmin`s' owners, both
  executors' owner and nominee unchanged), and the logged holders are equal; or
* `H` collides on the leg's own logged `(before, after)` pair.

The start state is arbitrary. For a CTM leg this assumes the CTM proxy sits under the CTM-domain
`ProxyAdmin`: in a state where another admin holds the CTM proxy, that admin's code swaps of the
CTM have no step (Specs, model boundaries), so there the result rests on the missing step. -/
def Properties.EngineLegFrameOrCollision : Prop :=
  ∀ (K : Config) (H : DomainHolders → UInt256) (d : LegDomain) (s s' : VState)
    (cs : List VCall),
    EngineLeg K H d s cs s' → OtherDomainQuiet d s cs →
    (d = .ctm → s.ctmAnswers = none ∧ s'.ctmAnswers = none) →
    (LegAuthFrame s s' ∧ s'.holders K d = s.holders K d) ∨
      HoldersCollide H (s.holders K d) (s'.holders K d)

/-- **A LEG CAN NEITHER PARK NOR UNPARK.** Take a successful engine leg of domain `d`, with
any `holdersHash` `H`.
* For a CTM leg, suppose the CTM answers its ownership reads from its slots before and after.
  The trace is arbitrary.
* For a core leg, suppose the CTM domain's holders send no call and no call is `migrate()`.

Then authority is parked on the migration after the leg if and only if it was before, or `H`
collides on the leg's own logged pair.

The start state is arbitrary. For a CTM leg this assumes the CTM proxy sits under the CTM-domain
`ProxyAdmin`: in a state where another admin holds the CTM proxy, that admin's code swaps of the
CTM have no step (Specs, model boundaries), so there the result rests on the missing step. -/
def Properties.EngineLegNeitherParksNorUnparks : Prop :=
  ∀ (K : Config) (H : DomainHolders → UInt256) (d : LegDomain) (s s' : VState)
    (cs : List VCall),
    EngineLeg K H d s cs s' →
    (d = .ctm → s.ctmAnswers = none ∧ s'.ctmAnswers = none) →
    (d = .core → OtherDomainQuiet .core s cs) →
    (ParkedOnMigration K s'.a ↔ ParkedOnMigration K s.a) ∨
      HoldersCollide H (s.holders K d) (s'.holders K d)

/-- **A CTM LEG KEEPS THE CTM'S ADMIN AND NOTIFIER BINDING, OR THE HASH COLLIDES.** Take a
successful CTM leg, with any `holdersHash` `H` and any call trace; the CTM may answer its
ownership reads in any way. Then either:
* `CtmBindingsFrame` holds and the logged holders are equal: the CTM's `admin()` and the
  notifier the CTM names are unchanged, and if it names one, that notifier's owner, nominee,
  `chainTypeManager()` and `getProxyAdmin` read are unchanged; or
* `H` collides on the leg's own logged pair.

The CTM's admin, the notifier address and the notifier's CTM are the entries `b17415d20`
added to `_domainHolders` (:129, :131, :145); it also reads the notifier address again after
the engine returns (:123). The CTM's `pendingAdmin` is not hashed
(`EngineCtmAdminNominationUnseen`).

The start state is arbitrary. For a CTM leg this assumes the CTM proxy sits under the CTM-domain
`ProxyAdmin`: in a state where another admin holds the CTM proxy, that admin's code swaps of the
CTM have no step (Specs, model boundaries), so there the result rests on the missing step. -/
def Properties.EngineLegKeepsCtmBindingsOrCollision : Prop :=
  ∀ (K : Config) (H : DomainHolders → UInt256) (s s' : VState) (cs : List VCall),
    EngineLeg K H .ctm s cs s' →
    (CtmBindingsFrame K s s' ∧ s'.holders K .ctm = s.holders K .ctm) ∨
      HoldersCollide H (s.holders K .ctm) (s'.holders K .ctm)

/-- **NO CTM LEG RUNS WHILE THE CTM'S ADMIN IS THE `ProxyAdmin`** (`:75-77`).
* For every configuration, `holdersHash`, trace and end state, no CTM leg starts from a state
  whose CTM `admin()` is the CTM-domain `ProxyAdmin`.
* After the witness bundle, the leg `wTransientLeg` succeeds for every `holdersHash`; from
  `wAdminIsPaV`, which differs only in the CTM's admin, the same leg has no successful
  execution for any `holdersHash`. -/
def Properties.EngineLegRefusesCtmAdminProxyAdmin : Prop :=
  (∀ (K : Config) (H : DomainHolders → UInt256) (s s' : VState) (cs : List VCall),
      s.ctmAdmin = K.m.pa → ¬ EngineLeg K H .ctm s cs s') ∧
    (∀ H : DomainHolders → UInt256, EngineLeg (wConfig true) H .ctm wPostV wTransientLeg wPostV) ∧
    ∀ (H : DomainHolders → UInt256) (s' : VState),
      ¬ EngineLeg (wConfig true) H .ctm wAdminIsPaV wTransientLeg s'

/-- **(c) A LEG CANNOT RECOVER THE PARKED CTM; A CALL TRACE CAN.** In the configuration of
`NonGenuineExecutorParksTheCTM`, the state it leaves (`wParked`) has the CTM owned by the spent
migration with executor `3` nominated. The configuration fixes only what `migrate()` reads
(the executors' getters and whether `3`'s `acceptCTMOwnership()` has effect); the leg clauses
are about a CTM leg, that is `ProxyUpgradeExecutorBase`'s code run by the CTM executor.
* Every successful CTM leg from a state with that authority state, with any `holdersHash`,
  leaves the CTM owned by the migration with `3` nominated (so parked), or `H` collides on the
  leg's logged pair. Before and after, the CTM answers its reads from its slots.
* The recovering call, `3`'s `acceptOwnership()` on the CTM, succeeds as a call trace from
  `wParkedV` and leaves nothing parked.
* As a leg from `wParkedV`, the same call succeeds exactly when `H` takes the same value on the
  two logged holder tuples, which differ. -/
def Properties.LegCannotRecoverParkedCTM : Prop :=
  (∀ (H : DomainHolders → UInt256) (s s' : VState) (cs : List VCall), s.a = wParked →
      s.ctmAnswers = none → s'.ctmAnswers = none →
      EngineLeg (wConfig false) H .ctm s cs s' →
      (s'.a.ctmOwner = 50 ∧ s'.a.ctmPending = 3 ∧ ParkedOnMigration (wConfig false) s'.a) ∨
        HoldersCollide H (s.holders (wConfig false) .ctm) (s'.holders (wConfig false) .ctm)) ∧
    (∃ s', VRun (wConfig false) none wParkedV [⟨3, .fwd .ctmAcceptOwnership⟩] s' ∧
      s'.a.ctmOwner = 3 ∧ s'.a.ctmPending = 0 ∧ ¬ ParkedOnMigration (wConfig false) s'.a) ∧
    (∀ H : DomainHolders → UInt256,
      (∃ s', EngineLeg (wConfig false) H .ctm wParkedV [⟨3, .fwd .ctmAcceptOwnership⟩] s') ↔
        H (wParkedV.holders (wConfig false) .ctm) = H (wRecoveredV.holders (wConfig false) .ctm)) ∧
    wParkedV.holders (wConfig false) .ctm ≠ wRecoveredV.holders (wConfig false) .ctm

/-- **(d) A LEG CANNOT RENOUNCE WHAT IT CHECKS.**
* A successful CTM leg from a state where the CTM and the CTM-domain `ProxyAdmin` have nonzero
  owners leaves them nonzero, or `H` collides on the leg's logged pair. Before and after, the
  CTM answers its reads from its slots. If the CTM names a notifier, a nonzero owner of that
  notifier stays nonzero too.
* A successful core leg leaves a nonzero ecosystem `ProxyAdmin` owner nonzero, or collides.
* The executor's own `renounceOwnership()` has no successful execution, in any context.
* After the witness bundle, a CTM leg of the CTM's `renounceOwnership()` succeeds exactly when
  `H` takes the same value on the two logged holder tuples, which differ. The same call as a
  call trace succeeds and leaves the CTM with neither owner nor nominee. -/
def Properties.LegRenounceReverts : Prop :=
  (∀ (K : Config) (H : DomainHolders → UInt256) (s s' : VState) (cs : List VCall),
      EngineLeg K H .ctm s cs s' → s.ctmAnswers = none → s'.ctmAnswers = none →
      s.a.ctmOwner ≠ 0 → s.a.paOwner ≠ 0 →
      (s'.a.ctmOwner ≠ 0 ∧ s'.a.paOwner ≠ 0 ∧
          (s.notifier ≠ 0 → (s.notifiers s.notifier).owner ≠ 0 →
            (s'.notifiers s.notifier).owner ≠ 0)) ∨
        HoldersCollide H (s.holders K .ctm) (s'.holders K .ctm)) ∧
    (∀ (K : Config) (H : DomainHolders → UInt256) (s s' : VState) (cs : List VCall),
      EngineLeg K H .core s cs s' → s.ecoOwner ≠ 0 →
      s'.ecoOwner ≠ 0 ∨ HoldersCollide H (s.holders K .core) (s'.holders K .core)) ∧
    (∀ (K : Config) (ctx : Option LegDomain) (a : Address) (s t : VState) (d : LegDomain),
      ¬ VOpStep K ctx a s (.execRenounceOwnership d) t) ∧
    (∀ H : DomainHolders → UInt256,
      (∃ s', EngineLeg (wConfig true) H .ctm wPostV [⟨3, .fwd .ctmRenounceOwnership⟩] s') ↔
        H (wPostV.holders (wConfig true) .ctm) = H (wCtmRenouncedV.holders (wConfig true) .ctm)) ∧
    wPostV.holders (wConfig true) .ctm ≠ wCtmRenouncedV.holders (wConfig true) .ctm ∧
    (∃ s', VRun (wConfig true) none wPostV [⟨3, .fwd .ctmRenounceOwnership⟩] s' ∧
      s'.a.ctmOwner = 0 ∧ s'.a.ctmPending = 0)

/-! ## A leg's calls are a forward -/

/-- **EVERY CALL TRACE IS A FORWARD ON `AState`.** For any context, a successful call trace
relates the authority states of its ends exactly as `Forward`'s `FRun` of its projected calls
does. Each projected call is one of the trace's calls with the same sender (`VCall.toCall`). -/
def Properties.CallTracesAreForwards : Prop :=
  ∀ (K : Config) (ctx : Option LegDomain) (s s' : VState) (cs : List VCall),
    VRun K ctx s cs s' →
    FRun K s.a (VCall.project cs) s'.a ∧
      ∀ c ∈ VCall.project cs, ∃ c' ∈ cs, c'.toCall = some c

/-- **(b) A LEG'S CALLS ARE A FORWARD.** A successful engine leg of either domain, with any
`holdersHash`, relates the authority states of its ends as `Forward`'s `FRun` of its projected
calls does. -/
def Properties.EngineLegCallsAreAForward : Prop :=
  ∀ (K : Config) (H : DomainHolders → UInt256) (d : LegDomain) (s s' : VState)
    (cs : List VCall),
    EngineLeg K H d s cs s' → FRun K s.a (VCall.project cs) s'.a

/-- **EVERY TRANSACTION HAS ONE OUTCOME.** For any configuration and `holdersHash`, two runs of
the same transactions from the same state end in the same state. So the states `t`, `t'` that
`RunLegCollides` names are the states the run passes through before and after that leg. -/
def Properties.EngineRunsDeterministic : Prop :=
  ∀ (K : Config) (H : DomainHolders → UInt256) (s t₁ t₂ : VState) (vs : List VLabel),
    VSysRun K H s vs t₁ → VSysRun K H s vs t₂ → t₁ = t₂

/-- **NOTHING RE-PARKS ACROSS ENGINE LEGS, OR A LEG OF THE RUN COLLIDED.** Start from a spent
edge with nothing parked, and a CTM that answers its ownership reads from its slots. Take any
run of the model's transactions, call traces and engine legs, with any `holdersHash`, where:
* no transaction, call trace or core leg hands authority to the migration by an ownership call
  or replaces the CTM's code;
* no CTM leg replaces the CTM's code with code that answers the reads falsely. CTM legs may
  otherwise do anything, including nominate the migration and swap the CTM's implementation.

Then nothing is parked on the migration at the end, or `RunLegCollides`: the run splits at one
of its engine legs, and `H` collides on the holders that leg logs, from the state the run
reaches before it to the state after it. The model's CTM keeps its entry points after a code
swap (the Specs' model boundaries). -/
def Properties.NoReparkingAcrossEngineLegs : Prop :=
  ∀ (K : Config) (H : DomainHolders → UInt256) (s s' : VState) (vs : List VLabel),
    s.a.executed = true → ¬ ParkedOnMigration K s.a → s.ctmAnswers = none →
    VSysRun K H s vs s' → (∀ v ∈ vs, v.Clean K) →
    ¬ ParkedOnMigration K s'.a ∨ RunLegCollides K H s vs s'

/-- **`migrate()` WITH A GENUINE EXECUTOR PARKS NOTHING, ENGINE LEGS INCLUDED.** If the CTM
executor's `acceptCTMOwnership()` runs `CTMUpgradeExecutor`'s logic, take a successful
`migrate()` and any run after it as in `NoReparkingAcrossEngineLegs`, starting with the CTM
answering its reads from its slots. Then nothing is parked on the migration at the end, or
`RunLegCollides` (a leg of the run collided on its own logged pair). -/
def Properties.MigrateLeavesNothingParkedWithEngineLegs : Prop :=
  ∀ (K : Config) (H : DomainHolders → UInt256) (t : AState) (s s' : VState) (vs : List VLabel),
    (∀ e, K.exec K.m.E = some e → e.genuineAccept = true) →
    MigrateStep K t s.a → s.ctmAnswers = none →
    VSysRun K H s vs s' → (∀ v ∈ vs, v.Clean K) →
    ¬ ParkedOnMigration K s'.a ∨ RunLegCollides K H s vs s'

/-! ## The engine inside its executor -/

/-- **(e) CALLING BACK INTO ITS EXECUTOR, THE ENGINE PASSES ONLY `acceptCTMOwnership`'s GATE.**
During a leg of domain `d` the engine's calls into `d`'s executor are sent by that executor.
Suppose the executor's owner and nominee, as the gate reads them, are not the executor, and it
is no chain's admin. Then:
* every entry point the executor declares whose caller check passes for the executor is
  `acceptCTMOwnership()`, and only on the CTM executor while the CTM answers that the executor
  owns it. The caller checks of `forward`, the `apply*` entry points, `upgradeChain`,
  `transferOwnership`, `acceptOwnership` and `renounceOwnership` fail;
* conversely `acceptCTMOwnership`'s caller check passes for the CTM executor whenever the CTM
  answers that it owns it.

`ExecEntry.GatePasses` is a table of the caller checks, transcribed from
`CTMUpgradeExecutor.sol:55-107`, `CoreUpgradeExecutor.sol:33` and `UpgradeExecutorBase.sol:35,
60`. No `VOpStep` refers to it, so this result checks that transcription; it is not derived
from the step relation. -/
def Properties.EngineReachesOnlyAcceptCTMOwnership : Prop :=
  (∀ (K : Config) (d : LegDomain) (s : VState) (chainAdmin : ℕ → Address) (e : ExecEntry),
      d.Declares e → s.execOwner d ≠ d.executor K → s.execPending d ≠ d.executor K →
      (∀ id, chainAdmin id ≠ d.executor K) →
      e.GatePasses (s.gateView d chainAdmin) (d.executor K) →
      e = .acceptCTMOwnership ∧ d = .ctm ∧ s.ctmRead.1 = K.m.E) ∧
    ∀ (K : Config) (s : VState) (chainAdmin : ℕ → Address), s.ctmRead.1 = K.m.E →
      ExecEntry.acceptCTMOwnership.GatePasses (s.gateView .ctm chainAdmin) K.m.E

/-- **(f) THE EXECUTOR'S OWNER IS NEVER ZERO.**
* The constructor reverts on a zero initial owner, and otherwise leaves a nonzero owner.
* `renounceOwnership()` has no successful execution.
* Along any run of the model's transactions, call traces and engine legs, with any
  `holdersHash`, where no call is sent by the zero address, both executors' nonzero owners stay
  nonzero. This includes the two-step transfer and any writes an engine makes to its
  executor's slots during a leg.

The first two clauses hold by the definition of `ExecConstructed`; the run clause is the one
with content. -/
def Properties.ExecutorOwnerNeverZero : Prop :=
  (∀ o own p : Address, ExecConstructed o own p → own ≠ 0) ∧
    (∀ own p : Address, ¬ ExecConstructed 0 own p) ∧
    (∀ (K : Config) (ctx : Option LegDomain) (a : Address) (s t : VState) (d : LegDomain),
      ¬ VOpStep K ctx a s (.execRenounceOwnership d) t) ∧
    ∀ (K : Config) (H : DomainHolders → UInt256) (s s' : VState) (vs : List VLabel),
      VSysRun K H s vs s' → (∀ v ∈ vs, v.SendersNonzero) →
      s.eOwner ≠ 0 → s.cOwner ≠ 0 → s'.eOwner ≠ 0 ∧ s'.cOwner ≠ 0

/-! ## Countermodels -/

/-- **THE COLLISION DISJUNCT IS LOAD-BEARING.** After the witness bundle, a CTM leg whose engine
calls the CTM-domain `ProxyAdmin`'s `transferOwnership(7)`:
* succeeds exactly when `H` takes the same value on the logged pair, which differs;
* meets the premises of `EngineLegFrameOrCollision`;
* for some `holdersHash` (a constant one), succeeds and moves the `ProxyAdmin` to `7`, so
  `LegAuthFrame` fails. -/
def Properties.CollisionDisjunctNeeded : Prop :=
  (∀ H : DomainHolders → UInt256,
      (∃ s', EngineLeg (wConfig true) H .ctm wPostV [⟨3, .fwd (.paTransferOwnership 7)⟩] s') ↔
        H (wPostV.holders (wConfig true) .ctm) = H (wPaMovedV.holders (wConfig true) .ctm)) ∧
    wPostV.holders (wConfig true) .ctm ≠ wPaMovedV.holders (wConfig true) .ctm ∧
    OtherDomainQuiet .ctm wPostV [⟨3, .fwd (.paTransferOwnership 7)⟩] ∧
    wPostV.ctmAnswers = none ∧ wPaMovedV.ctmAnswers = none ∧
    ∃ (H : DomainHolders → UInt256) (s' : VState),
      EngineLeg (wConfig true) H .ctm wPostV [⟨3, .fwd (.paTransferOwnership 7)⟩] s' ∧
        s'.a.paOwner = 7 ∧ ¬ LegAuthFrame wPostV s'

/-- **WITHOUT :96-98 A LEG RE-PARKS THE CTM.** After the witness bundle the edge is spent and
nothing is parked. A CTM leg whose engine calls the CTM's `transferOwnership(migration)` passes
the leg's other check (:93-95) and leaves the migration nominated, which is parked. (The spent
migration can no longer accept, `MigrateIsOneShot`; the nomination alone is the parking.) With
:96-98 the same leg succeeds exactly when `H` takes the same value on the two logged holder
tuples, which differ. -/
def Properties.NoHolderCheckReparks : Prop :=
  wPostV.a.executed = true ∧ ¬ ParkedOnMigration (wConfig true) wPostV.a ∧
    EngineLegNoHolderCheck (wConfig true) .ctm wPostV [⟨3, .fwd (.ctmTransferOwnership 50)⟩]
      wNominatedV ∧
    ParkedOnMigration (wConfig true) wNominatedV.a ∧
    (∀ H : DomainHolders → UInt256,
      (∃ s', EngineLeg (wConfig true) H .ctm wPostV [⟨3, .fwd (.ctmTransferOwnership 50)⟩] s') ↔
        H (wPostV.holders (wConfig true) .ctm) = H (wNominatedV.holders (wConfig true) .ctm)) ∧
    wPostV.holders (wConfig true) .ctm ≠ wNominatedV.holders (wConfig true) .ctm

/-- **THE RUN RESULTS' COLLISION DISJUNCT IS LOAD-BEARING.** With a constant `holdersHash`, the
one-transaction run whose CTM leg nominates the migration on the CTM:
* meets every premise of `NoReparkingAcrossEngineLegs` (spent edge, nothing parked, the CTM
  answering from its slots, every transaction `Clean`);
* ends with authority parked on the migration;
* and `RunLegCollides` holds for it, at that leg. -/
def Properties.NoReparkingCollisionDisjunctNeeded : Prop :=
  wPostV.a.executed = true ∧ ¬ ParkedOnMigration (wConfig true) wPostV.a ∧
    wPostV.ctmAnswers = none ∧
    VSysRun (wConfig true) (fun _ => 0) wPostV
      [.engineLeg .ctm [⟨3, .fwd (.ctmTransferOwnership 50)⟩]] wNominatedV ∧
    (∀ v ∈ [VLabel.engineLeg .ctm [⟨3, .fwd (.ctmTransferOwnership 50)⟩]], v.Clean (wConfig true)) ∧
    ParkedOnMigration (wConfig true) wNominatedV.a ∧
    RunLegCollides (wConfig true) (fun _ => 0) wPostV
      [.engineLeg .ctm [⟨3, .fwd (.ctmTransferOwnership 50)⟩]] wNominatedV

/-- **A LEG THAT SWAPS THE CTM'S CODE RE-PARKS IT UNSEEN.** After the witness bundle, a CTM leg
whose engine calls `upgradeAndCall` on the CTM proxy, with new code that writes the migration
into the owner slot, keeps the admin, the pending admin and the notifier, and keeps answering
`owner() = 3`, `pendingOwner() = 0`:
* succeeds for every `holdersHash`, logging equal holders, so no collision is involved;
* hands nothing to the migration by an ownership call;
* leaves the migration owning the CTM, with the CTM no longer answering from its slots.

This is the premise `s'.ctmAnswers = none` of `EngineLegFrameOrCollision`, and the `Clean`
premise of `NoReparkingAcrossEngineLegs`, failing. -/
def Properties.EngineCtmSwapReparks : Prop :=
  wPostV.a.executed = true ∧ ¬ ParkedOnMigration (wConfig true) wPostV.a ∧
    (∀ c ∈ [VCall.mk 3 (.ctmCodeSwap 50 0 35 60 6 0 8 (some (3, 0)))],
      ¬ c.op.handsToMigration (wConfig true)) ∧
    ∀ H : DomainHolders → UInt256, ∃ s',
      EngineLeg (wConfig true) H .ctm wPostV [⟨3, .ctmCodeSwap 50 0 35 60 6 0 8 (some (3, 0))⟩] s' ∧
        s'.holders (wConfig true) .ctm = wPostV.holders (wConfig true) .ctm ∧
        ParkedOnMigration (wConfig true) s'.a ∧ s'.ctmAnswers ≠ none

/-- **A CORE LEG MAY RUN `migrate()`.** After governance's hand-over, with a genuine executor, a
core leg whose engine calls the permissionless `migrate()` succeeds for every `holdersHash`.
It moves the CTM-domain `ProxyAdmin` and the CTM's owner, which nothing in the core leg checks.
So `OtherDomainQuiet`'s `migrate()` clause is needed for `EngineLegOtherDomainFrame`. (The move
is the migration's own, to the executor; it parks nothing.) -/
def Properties.CoreLegMayRunMigrate : Prop :=
  ∀ H : DomainHolders → UInt256, ∃ s',
    EngineLeg (wConfig true) H .core wHandedV [⟨4, .fwd .migrate⟩] s' ∧
      s'.a.ctmOwner ≠ wHandedV.a.ctmOwner ∧ s'.a.paOwner ≠ wHandedV.a.paOwner ∧
      ¬ ParkedOnMigration (wConfig true) s'.a

/-- **THE SENDER PREMISE OF THE OTHER-DOMAIN FRAME IS LOAD-BEARING.** After the witness bundle,
take a CTM leg in whose trace the core executor `4`, which owns the ecosystem `ProxyAdmin`,
sends `transferOwnership(7)` to it. (Such a call needs a call into the core executor's
`forward` by its owner, which the trace leaves out as a call writing nothing tracked.) The leg
succeeds for every `holdersHash`, logging equal holders, and the ecosystem `ProxyAdmin` has
moved to `7`. Only `OtherDomainQuiet` fails. -/
def Properties.OtherDomainQuietNeeded : Prop :=
  ¬ OtherDomainQuiet .ctm wPostV [⟨4, .ecoTransferOwnership 7⟩] ∧
    ∀ H : DomainHolders → UInt256, ∃ s',
      EngineLeg (wConfig true) H .ctm wPostV [⟨4, .ecoTransferOwnership 7⟩] s' ∧
        s'.holders (wConfig true) .ctm = wPostV.holders (wConfig true) .ctm ∧ s'.ecoOwner = 7 ∧
        ¬ LegAuthFrame wPostV s'

/-- **A NOTIFIER THE CTM DOES NOT NAME IS NOT CHECKED.** Take the state after the witness
bundle, but with a CTM whose `serverNotifierAddress()` is zero (`setServerNotifier` takes zero,
`ChainTypeManager.sol:387-391`). A CTM leg whose engine calls `renounceOwnership()` on the
notifier at `8` succeeds for every `holdersHash`, logging equal holders, and leaves that
notifier without an owner. So `LegRenounceReverts`' notifier clause can speak only of the
notifier the CTM names. With the notifier named, the same leg succeeds exactly when `H` takes
the same value on the two logged holder tuples, which differ. -/
def Properties.UnnamedNotifierIsUnchecked : Prop :=
  (∀ H : DomainHolders → UInt256, ∃ s',
      EngineLeg (wConfig true) H .ctm wNoNotifierV [⟨3, .notifierRenounceOwnership 8⟩] s' ∧
        s'.holders (wConfig true) .ctm = wNoNotifierV.holders (wConfig true) .ctm ∧
        (wNoNotifierV.notifiers 8).owner ≠ 0 ∧ (s'.notifiers 8).owner = 0) ∧
    (∀ H : DomainHolders → UInt256,
      (∃ s', EngineLeg (wConfig true) H .ctm wPostV [⟨3, .notifierRenounceOwnership 8⟩] s') ↔
        H (wPostV.holders (wConfig true) .ctm) =
          H (wNotifierRenouncedV.holders (wConfig true) .ctm)) ∧
    wPostV.holders (wConfig true) .ctm ≠ wNotifierRenouncedV.holders (wConfig true) .ctm

/-- **THE BINDINGS' COLLISION DISJUNCT IS LOAD-BEARING.** After the witness bundle:
* a CTM leg whose engine calls the CTM's `setServerNotifier(0)` succeeds exactly when `H` takes
  the same value on its two logged holder tuples, which differ;
* so does a CTM leg whose engine calls the notifier's `setChainTypeManager(5)`;
* for some `holdersHash` (a constant one) the second leg succeeds, the notifier serves CTM `5`,
  and `CtmBindingsFrame` fails. -/
def Properties.CtmBindingsCollisionNeeded : Prop :=
  (∀ H : DomainHolders → UInt256,
      (∃ s', EngineLeg (wConfig true) H .ctm wPostV [⟨3, .ctmSetServerNotifier 0⟩] s') ↔
        H (wPostV.holders (wConfig true) .ctm) = H (wNoNotifierV.holders (wConfig true) .ctm)) ∧
    wPostV.holders (wConfig true) .ctm ≠ wNoNotifierV.holders (wConfig true) .ctm ∧
    (∀ H : DomainHolders → UInt256,
      (∃ s', EngineLeg (wConfig true) H .ctm wPostV [⟨3, .notifierSetChainTypeManager 8 5⟩] s') ↔
        H (wPostV.holders (wConfig true) .ctm) =
          H (wNotifierRepointedV.holders (wConfig true) .ctm)) ∧
    wPostV.holders (wConfig true) .ctm ≠ wNotifierRepointedV.holders (wConfig true) .ctm ∧
    ∃ (H : DomainHolders → UInt256) (s' : VState),
      EngineLeg (wConfig true) H .ctm wPostV [⟨3, .notifierSetChainTypeManager 8 5⟩] s' ∧
        (s'.notifiers 8).ctm = 5 ∧ ¬ CtmBindingsFrame (wConfig true) wPostV s'

/-- **A LEG MAY NOMINATE A CTM ADMIN UNSEEN.** After the witness bundle:
* a CTM leg whose engine calls the CTM's `setPendingAdmin(7)` succeeds for every
  `holdersHash`, logging equal holders, and leaves `7` nominated;
* afterwards `7`'s `acceptAdmin()`, as a call trace, makes `7` the CTM's admin, which `6` was;
* a CTM leg that makes both calls succeeds exactly when `H` takes the same value on its two
  logged holder tuples, which differ.

`ProxyUpgradeExecutorBase.sol:114-117` and `docs/registry-driven-upgrades.md:285-286` state
that the nomination is not compared. -/
def Properties.EngineCtmAdminNominationUnseen : Prop :=
  (∀ H : DomainHolders → UInt256,
      EngineLeg (wConfig true) H .ctm wPostV [⟨3, .ctmSetPendingAdmin 7⟩] wAdminNominatedV) ∧
    wAdminNominatedV.holders (wConfig true) .ctm = wPostV.holders (wConfig true) .ctm ∧
    wAdminNominatedV.ctmPendingAdmin = 7 ∧
    VRun (wConfig true) none wAdminNominatedV [⟨7, .ctmAcceptAdmin⟩] wAdminTakenV ∧
    wAdminTakenV.ctmAdmin = 7 ∧ wPostV.ctmAdmin = 6 ∧
    (∀ H : DomainHolders → UInt256,
      (∃ s', EngineLeg (wConfig true) H .ctm wPostV
          [⟨3, .ctmSetPendingAdmin 7⟩, ⟨7, .ctmAcceptAdmin⟩] s') ↔
        H (wPostV.holders (wConfig true) .ctm) = H (wAdminTakenV.holders (wConfig true) .ctm)) ∧
    wPostV.holders (wConfig true) .ctm ≠ wAdminTakenV.holders (wConfig true) .ctm

/-- **THE PREMISES OF `EngineReachesOnlyAcceptCTMOwnership` ARE LOAD-BEARING.**
* With the executor as its own owner, `forward`'s caller check passes for it.
* With the executor as a chain's admin, `upgradeChain`'s caller check passes for it.
* After the witness bundle, a CTM leg whose engine writes the executor's owner slot to the
  executor and then back to governance succeeds for every `holdersHash`. So :93-95 does not see
  a transient self-ownership, during which the first case applies. This gives the engine nothing
  beyond the authority it already has: during the delegatecall it runs with the executor's
  address and storage. -/
def Properties.EngineGatePremisesNeeded : Prop :=
  (∀ (K : Config) (d : LegDomain) (s : VState) (chainAdmin : ℕ → Address),
      s.execOwner d = d.executor K →
      ExecEntry.forward.GatePasses (s.gateView d chainAdmin) (d.executor K)) ∧
    (∀ (K : Config) (s : VState) (chainAdmin : ℕ → Address) (id : ℕ),
      chainAdmin id = K.m.E →
      (ExecEntry.upgradeChain id).GatePasses (s.gateView .ctm chainAdmin) K.m.E) ∧
    ∀ H : DomainHolders → UInt256,
      EngineLeg (wConfig true) H .ctm wPostV [⟨3, .execSlots .ctm 3 0⟩, ⟨3, .execSlots .ctm 9 0⟩]
        wPostV ∧
      VRun (wConfig true) (some .ctm) wPostV [⟨3, .execSlots .ctm 3 0⟩]
        (wPostV.setExec .ctm 3 0)

/-! ## Witnesses -/

/-- **(g) THE GUARANTEES ARE ABOUT THE NET EFFECT; THE RUN PREMISES ARE SATISFIABLE.** After the
witness bundle:
* the CTM leg `wTransientLeg` (nominate `7`, `7` accepts, `7` nominates `3`, `3` accepts)
  succeeds for every `holdersHash` and ends where it started, although midway `7` owns the CTM;
* it meets `OtherDomainQuiet` and starts and ends with the CTM answering from its slots;
* the run of that leg and the core leg `wEcoRoundTrip` (the ecosystem `ProxyAdmin` to `7` and
  back) succeeds for every `holdersHash`, with every transaction `Clean` and no zero sender,
  from a spent edge with nothing parked and nonzero executor owners. These are the premises of
  `NoReparkingAcrossEngineLegs` and `ExecutorOwnerNeverZero`. -/
def Properties.EngineLegTransientWitness : Prop :=
  (∀ H : DomainHolders → UInt256, EngineLeg (wConfig true) H .ctm wPostV wTransientLeg wPostV) ∧
    (∃ mid, VRun (wConfig true) (some .ctm) wPostV (wTransientLeg.take 2) mid ∧
      mid.a.ctmOwner = 7) ∧
    OtherDomainQuiet .ctm wPostV wTransientLeg ∧ wPostV.ctmAnswers = none ∧
    wPostV.a.executed = true ∧ ¬ ParkedOnMigration (wConfig true) wPostV.a ∧
    wPostV.eOwner ≠ 0 ∧ wPostV.cOwner ≠ 0 ∧
    ∀ H : DomainHolders → UInt256,
      VSysRun (wConfig true) H wPostV
        [.engineLeg .ctm wTransientLeg, .engineLeg .core wEcoRoundTrip] wPostV ∧
      (∀ v ∈ [VLabel.engineLeg .ctm wTransientLeg, .engineLeg .core wEcoRoundTrip],
        v.Clean (wConfig true) ∧ v.SendersNonzero) ∧
      OtherDomainQuiet .core wPostV wEcoRoundTrip

/-- **THE OTHER RESULTS' PREMISES ARE SATISFIABLE.**
* From the parked state `wParkedV` (the CTM answering from its slots), the CTM leg
  `wPaRoundTrip` (the CTM-domain `ProxyAdmin` to `7` and back) succeeds for every
  `holdersHash`: the premises of `LegCannotRecoverParkedCTM`'s first clause.
* `wPostV` has nonzero CTM and CTM-domain `ProxyAdmin` owners and names a notifier with a
  nonzero owner, so with `EngineLegTransientWitness`'s CTM leg every premise of
  `LegRenounceReverts`' first clause holds, its notifier clause's included.
* From `wPostV`, the core leg `wEcoRoundTrip` succeeds for every `holdersHash` from a nonzero
  ecosystem `ProxyAdmin` owner, which midway is `7`: the premises of `LegRenounceReverts`'
  second clause.
* From `wPostV`, the CTM leg `wNotifierRoundTrip` (the CTM's notifier to zero and back)
  succeeds for every `holdersHash`: the premise of `EngineLegKeepsCtmBindingsOrCollision`, on a
  leg that changes a binding midway.
* The witness configuration's CTM executor is genuine and a `migrate()` leaves `wPostV`'s
  authority state: the premises of `MigrateLeavesNothingParkedWithEngineLegs`, with the run of
  `EngineLegTransientWitness`.
* At `wPostV`, with no chain admin, every premise of `EngineReachesOnlyAcceptCTMOwnership`'s
  first clause holds for `acceptCTMOwnership`, whose caller check passes; the CTM answers that
  the CTM executor owns it, the premise of its second clause.
* The constructor succeeds for governance `9` as initial owner: the premise of
  `ExecutorOwnerNeverZero`'s first clause. -/
def Properties.EngineLegPremisesWitness : Prop :=
  wParkedV.a = wParked ∧ wParkedV.ctmAnswers = none ∧
    (∀ H : DomainHolders → UInt256,
      EngineLeg (wConfig false) H .ctm wParkedV wPaRoundTrip wParkedV) ∧
    (∃ mid, VRun (wConfig false) (some .ctm) wParkedV (wPaRoundTrip.take 1) mid ∧
      mid.a.paOwner = 7) ∧
    wPostV.a.ctmOwner ≠ 0 ∧ wPostV.a.paOwner ≠ 0 ∧ wPostV.notifier ≠ 0 ∧
    (wPostV.notifiers wPostV.notifier).owner ≠ 0 ∧
    (∀ H : DomainHolders → UInt256, EngineLeg (wConfig true) H .core wPostV wEcoRoundTrip wPostV) ∧
    (∃ mid, VRun (wConfig true) (some .core) wPostV (wEcoRoundTrip.take 1) mid ∧
      mid.ecoOwner = 7) ∧
    wPostV.ecoOwner ≠ 0 ∧
    (∀ H : DomainHolders → UInt256,
      EngineLeg (wConfig true) H .ctm wPostV wNotifierRoundTrip wPostV) ∧
    (∃ mid, VRun (wConfig true) (some .ctm) wPostV (wNotifierRoundTrip.take 1) mid ∧
      mid.notifier = 0) ∧
    (∀ e, (wConfig true).exec (wConfig true).m.E = some e → e.genuineAccept = true) ∧
    MigrateStep (wConfig true) wHanded wPostV.a ∧
    LegDomain.Declares .ctm .acceptCTMOwnership ∧
    wPostV.execOwner .ctm ≠ LegDomain.executor (wConfig true) .ctm ∧
    wPostV.execPending .ctm ≠ LegDomain.executor (wConfig true) .ctm ∧
    (∀ id : ℕ, (fun _ : ℕ => (0 : Address)) id ≠ LegDomain.executor (wConfig true) .ctm) ∧
    ExecEntry.acceptCTMOwnership.GatePasses (wPostV.gateView .ctm fun _ => 0)
      (LegDomain.executor (wConfig true) .ctm) ∧
    wPostV.ctmRead.1 = (wConfig true).m.E ∧
    ExecConstructed 9 9 0

end Contracts.RegistryBootstrapMigration
