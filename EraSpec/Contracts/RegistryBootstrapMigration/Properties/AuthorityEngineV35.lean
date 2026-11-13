import EraSpec.Contracts.RegistryBootstrapMigration.Specs.AuthorityEngineV35

/-!
# Properties: the authority results survive engine legs (draft/v0.35.0)

Statements about `EraSpec.Contracts.RegistryBootstrapMigration.Specs.AuthorityEngineV35`.
Proofs are in `EraSpec.Contracts.RegistryBootstrapMigration.Proofs.AuthorityEngineV35`.
Source lines are at era-contracts `d9f678900e1bc8286412b78f56d4a9f443983c29`.

`MigrateLeavesNothingParked`, `NoReparkingAfterMigrate` and `NoReparkingAcrossForwards` were
proved for the `e561b9cc2` system, where no executor makes a delegatecall. At `d9` each domain
executor runs an engine leg (`ProxyUpgradeExecutorBase.sol:48-98`). The engine runs with the
executor's address and storage, and the only thing standing between it and the domain's
authority is the post-check at :87-92. The results below extend the earlier ones to runs
with legs. Every one carries the collision of the leg's own logged pair as its only extra
disjunct, and no injectivity premise is made on `holdersHash`.

## What holds

* **A leg can neither park nor unpark.**
  * `EngineLegKeepsItsExecutor`: the leg's executor keeps its owner and nominee, exactly.
  * `EngineLegOwnDomainFrameOrCollision`: the slots the leg's own checks cover are unchanged,
    or `holdersHash` collides on the leg's logged pair. No premise on senders.
  * `EngineLegOtherDomainFrame`: the other domain's slots are unchanged, exactly, if that
    domain's holders send no call in the trace.
  * `EngineLegFrameOrCollision` is the two together: the CTM's owner and nominee, both
    `ProxyAdmin`s' owners and both executors' owner and nominee are unchanged, or the hash
    collides.
  * `EngineLegNeitherParksNorUnparks`: authority is parked on the migration after a leg
    exactly if it was before, or the hash collides.
  * `LegCannotRecoverParkedCTM`: in the state `NonGenuineExecutorParksTheCTM` leaves, a leg
    leaves the CTM parked (or collides), and the recovering accept succeeds as a leg exactly
    when the hash collides. As a `forward` it recovers the CTM (`ParkedForwardFramesFire`).
  * `LegRenounceReverts`: a leg leaves every owner it checks nonzero, or collides. Forwarded,
    the same renounce strands the CTM (`RenouncedAuthorityIsStranded`).
* **A leg's calls are a forward.** `EngineLegCallsAreAForward`: projected on `AState`, a leg's
  trace is an `FRun` of `Forward`'s ops (and so is every trace, `CallTracesAreForwards`). Hence:
  * `NoReparkingAcrossEngineLegs`: along runs of the model's transactions, call traces and
    engine legs, nothing is re-parked, or some leg of the run collided on its logged pair.
    CTM legs need no premise beyond "does not leave the CTM answering its reads falsely".
  * `MigrateLeavesNothingParkedWithEngineLegs`: the same from the state a genuine `migrate()`
    leaves.
* **The engine reaches only `acceptCTMOwnership` in the executor**
  (`EngineReachesOnlyAcceptCTMOwnership`). Calling back into its executor, it passes no gate
  but that one's, while the executor's slots name neither the executor as owner nor as nominee
  and it is no chain's admin.
* **The executor's owner is never zero** (`ExecutorOwnerNeverZero`). This holds across the
  constructor, calls, the two-step transfer, `renounceOwnership` (which always reverts) and
  engine legs. It is `UpgradeExecutorBase.sol:14-19`'s "the authority the executor holds never
  becomes unreachable", for the executor's own ownership.

## Countermodels and witnesses

* `CollisionDisjunctNeeded`: a CTM leg that moves the CTM-domain `ProxyAdmin` succeeds exactly
  when `holdersHash` collides on its logged pair, and then the frame fails.
* `NoHolderCheckReparks`: without :90-92 a leg's nomination of the migration re-parks the CTM.
* `EngineCtmSwapReparks`: a leg that swaps the CTM's code for code that rewrites the slots and
  keeps answering the old holders passes for every hash and parks the CTM. The CTM code swap
  is still the excluded case.
* `CoreLegMayRunMigrate`: a core leg may call the permissionless `migrate()`, which moves the
  CTM domain without any check of the core leg seeing it. So `OtherDomainQuiet`'s `migrate`
  clause is needed.
* `OtherDomainQuietNeeded`: a CTM leg in whose trace the ecosystem `ProxyAdmin`'s owner sends a
  transfer passes for every hash, and the ecosystem `ProxyAdmin` has moved. So
  `OtherDomainQuiet`'s sender clause is needed.
* `UnnamedNotifierIsUnchecked`: with a CTM that names no notifier, a CTM leg may move the
  notifier's ownership, for every hash.
* `EngineGatePremisesNeeded`: an executor that owns itself, or is a chain's admin, passes
  `forward` or `upgradeChain`. The :87-89 check does not see an engine that makes the executor
  its own owner and restores the owner before returning.
* `EngineLegTransientWitness`: a leg that hands the CTM away and takes it back succeeds for
  every hash, so the guarantees are about the net effect only. The run results' premises are
  satisfiable.
-/

namespace Contracts.RegistryBootstrapMigration

open Clear

/-! ## A leg can neither park nor unpark -/

/-- **A LEG KEEPS ITS EXECUTOR'S OWNERSHIP, EXACTLY.** After any successful engine leg of
domain `d`, `d`'s executor has the owner and the nominee it had before. There is no collision
disjunct: `:87-89` compares the values. -/
def Properties.EngineLegKeepsItsExecutor : Prop :=
  ∀ (K : Config) (H : Holders → UInt256) (d : Domain) (s s' : VState) (cs : List VCall),
    EngineLeg K H d s cs s' → s'.execOwner d = s.execOwner d ∧ s'.execPending d = s.execPending d

/-- **A LEG LEAVES THE OTHER DOMAIN ALONE, EXACTLY.** Take a successful engine leg of domain
`d` in which no call is sent by a holder of the other domain (taken at the start), and, for a
core leg, no call is `migrate()`. Then `OtherFrame` holds:
* a CTM leg leaves the ecosystem `ProxyAdmin`'s owner and the core executor's owner and nominee
  unchanged;
* a core leg leaves the CTM's owner and nominee, the CTM-domain `ProxyAdmin`'s owner, the CTM
  executor's owner and nominee, and the migration's `executed` unchanged.

There is no collision disjunct: nothing in the leg checks the other domain. -/
def Properties.EngineLegOtherDomainFrame : Prop :=
  ∀ (K : Config) (H : Holders → UInt256) (d : Domain) (s s' : VState) (cs : List VCall),
    EngineLeg K H d s cs s' → OtherDomainQuiet d s cs → OtherFrame d s s'

/-- **A LEG LEAVES ITS OWN DOMAIN'S HOLDERS AS THEY WERE, OR THE HASH COLLIDES ON ITS OWN PAIR.**
Take a successful engine leg of domain `d`, with any `holdersHash` `H` and any call trace. For
a CTM leg, suppose the CTM answers its ownership reads from its slots before and after. Then
either:
* `OwnFrame` holds and the logged holders are equal. For a CTM leg: the CTM's owner and
  nominee, the CTM-domain `ProxyAdmin`'s owner and the CTM executor's owner and nominee are
  unchanged. For a core leg: the ecosystem `ProxyAdmin`'s owner and the core executor's owner
  and nominee are unchanged; or
* `H` collides on the leg's own logged `(before, after)` pair. -/
def Properties.EngineLegOwnDomainFrameOrCollision : Prop :=
  ∀ (K : Config) (H : Holders → UInt256) (d : Domain) (s s' : VState) (cs : List VCall),
    EngineLeg K H d s cs s' →
    (d = .ctm → s.ctmAnswers = none ∧ s'.ctmAnswers = none) →
    (OwnFrame d s s' ∧ s'.holders d = s.holders d) ∨ Collides H (s.holders d) (s'.holders d)

/-- **(a) A LEG LEAVES THE AUTHORITY SLOTS AS THEY WERE, OR THE HASH COLLIDES ON ITS OWN PAIR.**
Take a successful engine leg of domain `d`, with any `holdersHash` `H`, in which the other
domain's holders send no call (and, for a core leg, no call is `migrate()`). For a CTM leg,
suppose the CTM answers its ownership reads from its slots before and after. Then either:
* all of `AuthFrame` holds (the CTM's owner and nominee, both `ProxyAdmin`s' owners, both
  executors' owner and nominee unchanged), and the logged holders are equal; or
* `H` collides on the leg's own logged `(before, after)` pair. -/
def Properties.EngineLegFrameOrCollision : Prop :=
  ∀ (K : Config) (H : Holders → UInt256) (d : Domain) (s s' : VState) (cs : List VCall),
    EngineLeg K H d s cs s' → OtherDomainQuiet d s cs →
    (d = .ctm → s.ctmAnswers = none ∧ s'.ctmAnswers = none) →
    (AuthFrame s s' ∧ s'.holders d = s.holders d) ∨ Collides H (s.holders d) (s'.holders d)

/-- **A LEG CAN NEITHER PARK NOR UNPARK.** Take a successful engine leg of domain `d`, with
any `holdersHash` `H`.
* For a CTM leg, suppose the CTM answers its ownership reads from its slots before and after.
  The trace is arbitrary.
* For a core leg, suppose the CTM domain's holders send no call and no call is `migrate()`.

Then authority is parked on the migration after the leg if and only if it was before, or `H`
collides on the leg's own logged pair. -/
def Properties.EngineLegNeitherParksNorUnparks : Prop :=
  ∀ (K : Config) (H : Holders → UInt256) (d : Domain) (s s' : VState) (cs : List VCall),
    EngineLeg K H d s cs s' →
    (d = .ctm → s.ctmAnswers = none ∧ s'.ctmAnswers = none) →
    (d = .core → OtherDomainQuiet .core s cs) →
    (ParkedOnMigration K s'.a ↔ ParkedOnMigration K s.a) ∨
      Collides H (s.holders d) (s'.holders d)

/-- **(c) A LEG CANNOT RECOVER THE PARKED CTM; A FORWARD CAN.** In the configuration of
`NonGenuineExecutorParksTheCTM` the state it leaves (`wParked`) has the CTM owned by the spent
migration with executor `3` nominated. That executor's `acceptCTMOwnership()` is not
`CTMUpgradeExecutor`'s. The leg clauses below are about a leg that does run
`ProxyUpgradeExecutorBase`'s code, as `ParkedForwardFramesFire` is about a `forward` that runs
`UpgradeExecutorBase`'s.
* Every successful CTM leg from a state with that authority state, with any `holdersHash`,
  leaves the CTM owned by the migration with `3` nominated (so parked), or `H` collides on the
  leg's logged pair. Before and after, the CTM answers its reads from its slots.
* The recovering call, `3`'s `acceptOwnership()` on the CTM, succeeds as a call trace and
  leaves nothing parked (`ParkedForwardFramesFire`).
* As a leg, the same call succeeds exactly when `H` takes the same value on the two holder
  tuples, which differ. -/
def Properties.LegCannotRecoverParkedCTM : Prop :=
  (∀ (H : Holders → UInt256) (s s' : VState) (cs : List VCall), s.a = wParked →
      s.ctmAnswers = none → s'.ctmAnswers = none →
      EngineLeg (wConfig false) H .ctm s cs s' →
      (s'.a.ctmOwner = 50 ∧ s'.a.ctmPending = 3 ∧ ParkedOnMigration (wConfig false) s'.a) ∨
        Collides H (s.holders .ctm) (s'.holders .ctm)) ∧
    (∃ s', VRun (wConfig false) none wParkedV [⟨3, .fwd .ctmAcceptOwnership⟩] s' ∧
      s'.a.ctmOwner = 3 ∧ s'.a.ctmPending = 0 ∧ ¬ ParkedOnMigration (wConfig false) s'.a) ∧
    (∀ H : Holders → UInt256,
      (∃ s', EngineLeg (wConfig false) H .ctm wParkedV [⟨3, .fwd .ctmAcceptOwnership⟩] s') ↔
        H (wParkedV.holders .ctm) = H (wRecoveredV.holders .ctm)) ∧
    wParkedV.holders .ctm ≠ wRecoveredV.holders .ctm

/-- **(d) A LEG CANNOT RENOUNCE WHAT IT CHECKS.**
* A successful CTM leg from a state where the CTM and the CTM-domain `ProxyAdmin` have nonzero
  owners leaves them nonzero, or `H` collides on the leg's logged pair. Before and after, the
  CTM answers its reads from its slots. If the CTM names a notifier, a nonzero notifier owner
  stays nonzero too.
* A successful core leg leaves a nonzero ecosystem `ProxyAdmin` owner nonzero, or collides.
* The executor's own `renounceOwnership()` has no successful execution, in any context.
* After the witness bundle, a CTM leg of the CTM's `renounceOwnership()` succeeds exactly when
  `H` takes the same value on the two holder tuples. The same call as a call trace succeeds and
  leaves the CTM with neither owner nor nominee, which `RenouncedAuthorityIsStranded` shows is
  stranded. -/
def Properties.LegRenounceReverts : Prop :=
  (∀ (K : Config) (H : Holders → UInt256) (s s' : VState) (cs : List VCall),
      EngineLeg K H .ctm s cs s' → s.ctmAnswers = none → s'.ctmAnswers = none →
      s.a.ctmOwner ≠ 0 → s.a.paOwner ≠ 0 →
      (s'.a.ctmOwner ≠ 0 ∧ s'.a.paOwner ≠ 0 ∧
          (s.hasNotifier = true → s.nOwner ≠ 0 → s'.nOwner ≠ 0)) ∨
        Collides H (s.holders .ctm) (s'.holders .ctm)) ∧
    (∀ (K : Config) (H : Holders → UInt256) (s s' : VState) (cs : List VCall),
      EngineLeg K H .core s cs s' → s.ecoOwner ≠ 0 →
      s'.ecoOwner ≠ 0 ∨ Collides H (s.holders .core) (s'.holders .core)) ∧
    (∀ (K : Config) (ctx : Option Domain) (a : Address) (s t : VState) (d : Domain),
      ¬ VOpStep K ctx a s (.execRenounceOwnership d) t) ∧
    (∀ H : Holders → UInt256,
      (∃ s', EngineLeg (wConfig true) H .ctm wPostV [⟨3, .fwd .ctmRenounceOwnership⟩] s') ↔
        H (wPostV.holders .ctm) = H (wCtmRenouncedV.holders .ctm)) ∧
    wPostV.holders .ctm ≠ wCtmRenouncedV.holders .ctm ∧
    (∃ s', VRun (wConfig true) none wPostV [⟨3, .fwd .ctmRenounceOwnership⟩] s' ∧
      s'.a.ctmOwner = 0 ∧ s'.a.ctmPending = 0)

/-! ## A leg's calls are a forward -/

/-- **EVERY CALL TRACE IS A FORWARD ON `AState`.** For any context, a successful call trace
relates the authority states of its ends exactly as `Forward`'s `FRun` of its projected calls
does. Each projected call is one of the trace's calls with the same sender (`VCall.toCall`). -/
def Properties.CallTracesAreForwards : Prop :=
  ∀ (K : Config) (ctx : Option Domain) (s s' : VState) (cs : List VCall),
    VRun K ctx s cs s' →
    FRun K s.a (VCall.project cs) s'.a ∧
      ∀ c ∈ VCall.project cs, ∃ c' ∈ cs, c'.toCall = some c

/-- **(b) A LEG'S CALLS ARE A FORWARD.** A successful engine leg of either domain, with any
`holdersHash`, relates the authority states of its ends as `Forward`'s `FRun` of its projected
calls does. -/
def Properties.EngineLegCallsAreAForward : Prop :=
  ∀ (K : Config) (H : Holders → UInt256) (d : Domain) (s s' : VState) (cs : List VCall),
    EngineLeg K H d s cs s' → FRun K s.a (VCall.project cs) s'.a

/-- **NOTHING RE-PARKS ACROSS ENGINE LEGS, OR A LEG COLLIDED.** Start from a spent edge with
nothing parked, and a CTM that answers its ownership reads from its slots. Take any run of the
model's transactions, call traces and engine legs, with any `holdersHash`, where:
* no transaction, call trace or core leg hands authority to the migration by an ownership call
  or replaces the CTM's code;
* no CTM leg replaces the CTM's code with code that answers the reads falsely. CTM legs may
  otherwise do anything, including nominate the migration.

Then nothing is parked on the migration at the end, or one of the run's legs, from the state
it ran in, succeeded with `H` colliding on its own logged pair. -/
def Properties.NoReparkingAcrossEngineLegs : Prop :=
  ∀ (K : Config) (H : Holders → UInt256) (s s' : VState) (vs : List VLabel),
    s.a.executed = true → ¬ ParkedOnMigration K s.a → s.ctmAnswers = none →
    VSysRun K H s vs s' → (∀ v ∈ vs, v.Clean K) →
    ¬ ParkedOnMigration K s'.a ∨
      ∃ (d : Domain) (cs : List VCall) (t t' : VState), VLabel.engineLeg d cs ∈ vs ∧
        EngineLeg K H d t cs t' ∧ Collides H (t.holders d) (t'.holders d)

/-- **`migrate()` WITH A GENUINE EXECUTOR PARKS NOTHING, ENGINE LEGS INCLUDED.** If the CTM
executor's `acceptCTMOwnership()` runs `CTMUpgradeExecutor`'s logic, take a successful
`migrate()` and any run after it as in `NoReparkingAcrossEngineLegs`, starting with the CTM
answering its reads from its slots. Then nothing is parked on the migration at the end, or a
leg of the run collided on its own logged pair. -/
def Properties.MigrateLeavesNothingParkedWithEngineLegs : Prop :=
  ∀ (K : Config) (H : Holders → UInt256) (t : AState) (s s' : VState) (vs : List VLabel),
    (∀ e, K.exec K.m.E = some e → e.genuineAccept = true) →
    MigrateStep K t s.a → s.ctmAnswers = none →
    VSysRun K H s vs s' → (∀ v ∈ vs, v.Clean K) →
    ¬ ParkedOnMigration K s'.a ∨
      ∃ (d : Domain) (cs : List VCall) (u u' : VState), VLabel.engineLeg d cs ∈ vs ∧
        EngineLeg K H d u cs u' ∧ Collides H (u.holders d) (u'.holders d)

/-! ## The engine inside its executor -/

/-- **(e) CALLING BACK INTO ITS EXECUTOR, THE ENGINE PASSES ONLY `acceptCTMOwnership`'s GATE.**
During a leg of domain `d` the engine's calls into `d`'s executor are sent by that executor.
Suppose the executor's owner and nominee, as the gate reads them, are not the executor, and it
is no chain's admin. Then:
* every entry point the executor declares whose gate passes is `acceptCTMOwnership()`, and
  only on the CTM executor while the CTM answers that the executor owns it. In particular
  `forward`, the `apply*` entry points, `upgradeChain`, `transferOwnership`, `acceptOwnership`
  and `renounceOwnership` revert;
* conversely `acceptCTMOwnership`'s gate does pass for the CTM executor whenever the CTM
  answers that it owns it. -/
def Properties.EngineReachesOnlyAcceptCTMOwnership : Prop :=
  (∀ (K : Config) (d : Domain) (s : VState) (chainAdmin : ℕ → Address) (e : ExecEntry),
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
  executor's slots during a leg. -/
def Properties.ExecutorOwnerNeverZero : Prop :=
  (∀ o own p : Address, ExecConstructed o own p → own ≠ 0) ∧
    (∀ own p : Address, ¬ ExecConstructed 0 own p) ∧
    (∀ (K : Config) (ctx : Option Domain) (a : Address) (s t : VState) (d : Domain),
      ¬ VOpStep K ctx a s (.execRenounceOwnership d) t) ∧
    ∀ (K : Config) (H : Holders → UInt256) (s s' : VState) (vs : List VLabel),
      VSysRun K H s vs s' → (∀ v ∈ vs, v.SendersNonzero) →
      s.eOwner ≠ 0 → s.cOwner ≠ 0 → s'.eOwner ≠ 0 ∧ s'.cOwner ≠ 0

/-! ## Countermodels -/

/-- **THE COLLISION DISJUNCT IS LOAD-BEARING.** After the witness bundle, a CTM leg whose engine
calls the CTM-domain `ProxyAdmin`'s `transferOwnership(7)`:
* succeeds exactly when `H` takes the same value on the logged pair, which differs;
* meets the premises of `EngineLegFrameOrCollision`;
* for some `holdersHash` (a constant one), succeeds and moves the `ProxyAdmin` to `7`, so
  `AuthFrame` fails. -/
def Properties.CollisionDisjunctNeeded : Prop :=
  (∀ H : Holders → UInt256,
      (∃ s', EngineLeg (wConfig true) H .ctm wPostV [⟨3, .fwd (.paTransferOwnership 7)⟩] s') ↔
        H (wPostV.holders .ctm) = H (wPaMovedV.holders .ctm)) ∧
    wPostV.holders .ctm ≠ wPaMovedV.holders .ctm ∧
    OtherDomainQuiet .ctm wPostV [⟨3, .fwd (.paTransferOwnership 7)⟩] ∧
    wPostV.ctmAnswers = none ∧ wPaMovedV.ctmAnswers = none ∧
    ∃ (H : Holders → UInt256) (s' : VState),
      EngineLeg (wConfig true) H .ctm wPostV [⟨3, .fwd (.paTransferOwnership 7)⟩] s' ∧
        s'.a.paOwner = 7 ∧ ¬ AuthFrame wPostV s'

/-- **WITHOUT :90-92 A LEG RE-PARKS THE CTM.** After the witness bundle the edge is spent and
nothing is parked. A CTM leg whose engine calls the CTM's `transferOwnership(migration)` passes
the leg's other check (:87-89) and leaves the migration nominated, which is parked. (The spent
migration can no longer accept, `MigrateIsOneShot`; the nomination alone is the parking.) With
:90-92 the same leg succeeds exactly when `H` takes the same value on the two holder tuples,
which differ. -/
def Properties.NoHolderCheckReparks : Prop :=
  wPostV.a.executed = true ∧ ¬ ParkedOnMigration (wConfig true) wPostV.a ∧
    EngineLegNoHolderCheck (wConfig true) .ctm wPostV [⟨3, .fwd (.ctmTransferOwnership 50)⟩]
      wNominatedV ∧
    ParkedOnMigration (wConfig true) wNominatedV.a ∧
    (∀ H : Holders → UInt256,
      (∃ s', EngineLeg (wConfig true) H .ctm wPostV [⟨3, .fwd (.ctmTransferOwnership 50)⟩] s') ↔
        H (wPostV.holders .ctm) = H (wNominatedV.holders .ctm)) ∧
    wPostV.holders .ctm ≠ wNominatedV.holders .ctm

/-- **A LEG THAT SWAPS THE CTM'S CODE RE-PARKS IT UNSEEN.** After the witness bundle, a CTM leg
whose engine calls `upgradeAndCall` on the CTM proxy, with new code that writes the migration
into the owner slot and keeps answering `owner() = 3`, `pendingOwner() = 0`:
* succeeds for every `holdersHash`, logging equal holders, so no collision is involved;
* hands nothing to the migration by an ownership call;
* leaves the migration owning the CTM, with the CTM no longer answering from its slots.

This is the premise `s'.ctmAnswers = none` of `EngineLegFrameOrCollision`, and the `Clean`
premise of `NoReparkingAcrossEngineLegs`, failing: the CTM code swap is still excluded. -/
def Properties.EngineCtmSwapReparks : Prop :=
  wPostV.a.executed = true ∧ ¬ ParkedOnMigration (wConfig true) wPostV.a ∧
    (∀ c ∈ [VCall.mk 3 (.ctmCodeSwap 50 0 35 60 (some (3, 0)))],
      ¬ c.op.handsToMigration (wConfig true)) ∧
    ∀ H : Holders → UInt256, ∃ s',
      EngineLeg (wConfig true) H .ctm wPostV [⟨3, .ctmCodeSwap 50 0 35 60 (some (3, 0))⟩] s' ∧
        s'.holders .ctm = wPostV.holders .ctm ∧ ParkedOnMigration (wConfig true) s'.a ∧
        s'.ctmAnswers ≠ none

/-- **A CORE LEG MAY RUN `migrate()`.** After governance's hand-over, with a genuine executor, a
core leg whose engine calls the permissionless `migrate()` succeeds for every `holdersHash`.
It moves the CTM-domain `ProxyAdmin` and the CTM's owner, which nothing in the core leg checks.
So `OtherDomainQuiet`'s `migrate()` clause is needed for `EngineLegOtherDomainFrame`. (The move
is the migration's own, to the executor; it parks nothing.) -/
def Properties.CoreLegMayRunMigrate : Prop :=
  ∀ H : Holders → UInt256, ∃ s',
    EngineLeg (wConfig true) H .core wHandedV [⟨4, .fwd .migrate⟩] s' ∧
      s'.a.ctmOwner ≠ wHandedV.a.ctmOwner ∧ s'.a.paOwner ≠ wHandedV.a.paOwner ∧
      ¬ ParkedOnMigration (wConfig true) s'.a

/-- **THE SENDER PREMISE OF THE OTHER-DOMAIN FRAME IS LOAD-BEARING.** After the witness bundle,
take a CTM leg in whose trace the core executor `4`, which owns the ecosystem `ProxyAdmin`,
sends `transferOwnership(7)` to it. (Such a call needs a call into the core executor's
`forward` by its owner.) The leg succeeds for every `holdersHash`, logging equal holders, and
the ecosystem `ProxyAdmin` has moved to `7`. Only `OtherDomainQuiet` fails. -/
def Properties.OtherDomainQuietNeeded : Prop :=
  ¬ OtherDomainQuiet .ctm wPostV [⟨4, .ecoTransferOwnership 7⟩] ∧
    ∀ H : Holders → UInt256, ∃ s',
      EngineLeg (wConfig true) H .ctm wPostV [⟨4, .ecoTransferOwnership 7⟩] s' ∧
        s'.holders .ctm = wPostV.holders .ctm ∧ s'.ecoOwner = 7 ∧ ¬ AuthFrame wPostV s'

/-- **A NOTIFIER THE CTM DOES NOT NAME IS NOT CHECKED.** Take the state after the witness
bundle, but with a CTM whose `serverNotifierAddress()` is zero. A CTM leg whose engine calls
the notifier's `renounceOwnership()` succeeds for every `holdersHash`, logging equal holders,
and leaves the notifier without an owner. So the `hasNotifier` premise of
`LegRenounceReverts` is needed. With the notifier named, the same leg succeeds exactly when
`H` takes the same value on two different holder tuples. -/
def Properties.UnnamedNotifierIsUnchecked : Prop :=
  (∀ H : Holders → UInt256, ∃ s',
      EngineLeg (wConfig true) H .ctm wNoNotifierV [⟨3, .notifierRenounceOwnership⟩] s' ∧
        s'.holders .ctm = wNoNotifierV.holders .ctm ∧ wNoNotifierV.nOwner ≠ 0 ∧ s'.nOwner = 0) ∧
    (∀ H : Holders → UInt256,
      (∃ s', EngineLeg (wConfig true) H .ctm wPostV [⟨3, .notifierRenounceOwnership⟩] s') ↔
        H (wPostV.holders .ctm) =
          H (({ wPostV with nOwner := 0, nPending := 0 } : VState).holders .ctm)) ∧
    wPostV.holders .ctm ≠ ({ wPostV with nOwner := 0, nPending := 0 } : VState).holders .ctm

/-- **THE PREMISES OF `EngineReachesOnlyAcceptCTMOwnership` ARE LOAD-BEARING.**
* With the executor as its own owner, `forward`'s gate passes for it.
* With the executor as a chain's admin, `upgradeChain`'s gate passes for it.
* After the witness bundle, a CTM leg whose engine writes the executor's owner slot to the
  executor and then back to governance succeeds for every `holdersHash`. So :87-89 does not see
  a transient self-ownership, during which the first case applies. -/
def Properties.EngineGatePremisesNeeded : Prop :=
  (∀ (K : Config) (d : Domain) (s : VState) (chainAdmin : ℕ → Address),
      s.execOwner d = d.executor K →
      ExecEntry.forward.GatePasses (s.gateView d chainAdmin) (d.executor K)) ∧
    (∀ (K : Config) (s : VState) (chainAdmin : ℕ → Address) (id : ℕ),
      chainAdmin id = K.m.E →
      (ExecEntry.upgradeChain id).GatePasses (s.gateView .ctm chainAdmin) K.m.E) ∧
    ∀ H : Holders → UInt256,
      EngineLeg (wConfig true) H .ctm wPostV [⟨3, .execSlots .ctm 3 0⟩, ⟨3, .execSlots .ctm 9 0⟩]
        wPostV ∧
      VRun (wConfig true) (some .ctm) wPostV [⟨3, .execSlots .ctm 3 0⟩]
        (wPostV.setExec .ctm 3 0)

/-! ## Witnesses -/

/-- **(g) THE GUARANTEES ARE ABOUT THE NET EFFECT; THE PREMISES ARE SATISFIABLE.** After the
witness bundle:
* the CTM leg `wTransient` (nominate `7`, `7` accepts, `7` nominates `3`, `3` accepts) succeeds
  for every `holdersHash` and ends where it started, although midway `7` owns the CTM;
* it meets `OtherDomainQuiet` and starts and ends with the CTM answering from its slots;
* the run of that leg and a core leg making an untracked call succeeds for every `holdersHash`,
  with every transaction `Clean` and no zero sender, from a spent edge with nothing parked and
  nonzero executor owners. These are the premises of `NoReparkingAcrossEngineLegs` and
  `ExecutorOwnerNeverZero`. -/
def Properties.EngineLegTransientWitness : Prop :=
  (∀ H : Holders → UInt256, EngineLeg (wConfig true) H .ctm wPostV wTransient wPostV) ∧
    (∃ mid, VRun (wConfig true) (some .ctm) wPostV (wTransient.take 2) mid ∧ mid.a.ctmOwner = 7) ∧
    OtherDomainQuiet .ctm wPostV wTransient ∧ wPostV.ctmAnswers = none ∧
    wPostV.a.executed = true ∧ ¬ ParkedOnMigration (wConfig true) wPostV.a ∧
    wPostV.eOwner ≠ 0 ∧ wPostV.cOwner ≠ 0 ∧
    ∀ H : Holders → UInt256,
      VSysRun (wConfig true) H wPostV
        [.engineLeg .ctm wTransient, .engineLeg .core [⟨4, .fwd .untracked⟩]] wPostV ∧
      (∀ v ∈ [VLabel.engineLeg .ctm wTransient, .engineLeg .core [⟨4, .fwd .untracked⟩]],
        v.Clean (wConfig true) ∧ v.SendersNonzero) ∧
      OtherDomainQuiet .core wPostV [⟨4, .fwd .untracked⟩]

end Contracts.RegistryBootstrapMigration
