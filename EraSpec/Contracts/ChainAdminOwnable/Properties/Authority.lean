import EraSpec.Contracts.ChainAdminOwnable.Specs.Authority
import EraSpec.Core.Headline

/-!
# Properties: who drives the calls of `ChainAdminOwnable`, and what a renounce leaves

Statements about `EraSpec.Contracts.ChainAdminOwnable.Specs.Authority`. Proofs are in
`EraSpec.Contracts.ChainAdminOwnable.Proofs.Authority`.

"Along any run" below means any derivation `Sem cfg .acts S L S'`: any sequence of top-level
calls, each by an address other than the `ChainAdminOwnable` and zero, with every re-entrant call
at any depth that unknown code may make in between. Only frames that committed leave events.

## What holds

* **Every call the `ChainAdminOwnable` makes is its owner's or its setter's**
  (`CallsAreOwnersOrSetters`). A `multicall` iteration makes exactly the submitted call, and the
  `multicall` was entered by the owner of that moment. A `setTokenMultiplier` makes exactly
  `t.setTokenMultiplier(n, d)` with value zero, for a caller that was the setter at that moment.
  The target `t` is whatever the setter passed.
* **The same, seen by the callee** (`ReceivedCallsAreOwnersOrSetters`): every successful call a
  diamond or the Bridgehub receives with `msg.sender` the `ChainAdminOwnable` has a logged
  successful call of the `ChainAdminOwnable` with that target and selector, authorized as above.
* **Every write to its storage passed its access check** (`WritesAreGuarded`): the nominee for
  `acceptOwnership`, the owner for every other writer, read from the storage the write ran on.
* **The setter changes only by the owner** (`SetterChangesOnlyByOwner`): at the end of a run the
  setter is the one at its start, or a logged `setTokenMultiplierSetter` by the owner of that
  moment wrote it.
* **The owner changes only by an accept or a renounce** (`OwnerChangesOnlyByAcceptOrRenounce`):
  the final owner is the initial one, or it accepted while it was the nominee, or it is zero and
  a renounce by the owner of that moment is logged. The final nominee is the initial one, zero,
  or named by a logged `transferOwnership` of the owner of that moment.
* **A renounce is permanent** (`RenounceIsPermanent`). From storage with no owner and no nominee,
  no write ever commits again, the storage stays as it is, and every call the contract makes is a
  `setTokenMultiplier` call made for the setter frozen in that storage.
* **No owner means no nominee, from construction on** (`OwnerlessHasNoNominee`,
  `ConstructedThenOwnerlessIsPermanent`): runs keep "owner zero implies nominee zero", which the
  constructor establishes. So once a run from a constructed contract reaches an owner of zero,
  everything after it is as in `RenounceIsPermanent`.
* **A zero setter makes no call** (`ZeroSetterIsInert`): until the owner writes a setter, a
  `ChainAdminOwnable` constructed with setter zero (the Bridgehub's, in the deploy script) makes
  no `setTokenMultiplier` call.

## The boundary: a renounce does not stop a `multicall` already running

`CallsAreOwnersOrSetters` reads the owner when the `multicall` was entered, and
`RenounceIsPermanent` speaks about runs that start from renounced storage. Both are needed:
`MulticallOutlivesRenounce` is a `multicall` by the owner whose first call reaches code that makes
the owner renounce; the `multicall`'s next call still goes out, after the renounce is logged, and
sets a diamond's pending admin.

## Witnesses

* `AuthorityWitness` (for `CallsAreOwnersOrSetters`, `ReceivedCallsAreOwnersOrSetters`,
  `WritesAreGuarded`, `SetterChangesOnlyByOwner`, `OwnerChangesOnlyByAcceptOrRenounce`): from the
  storage the constructor leaves, the owner sets the setter, the setter adjusts a diamond's
  multiplier, the owner's `multicall` nominates a pending admin on the diamond and on the
  Bridgehub, and ownership moves by `transferOwnership` then `acceptOwnership`. Both kinds of
  call, three kinds of write, and the entries the diamond and the Bridgehub receive are logged.
* `ZeroSetterWitness` (for `ZeroSetterIsInert`): from setter zero, an owner's `multicall` runs
  with no setter write.
* `RenounceWitness` (for `RenounceIsPermanent`, `OwnerlessHasNoNominee`,
  `ConstructedThenOwnerlessIsPermanent`, and the renounce case of
  `OwnerChangesOnlyByAcceptOrRenounce`): the owner sets the setter and renounces; afterwards the
  setter's calls still go out, to the diamond and to an address of no modelled contract.
-/

namespace Contracts.ChainAdminOwnable

/-! ## Calls -/

/-- **(a) EVERY CALL THE `ChainAdminOwnable` MAKES IS ITS OWNER'S OR ITS SETTER'S.** The model logs
every call the `ChainAdminOwnable` makes in a frame that commits as an `Event.caoCall` with its
origin (`Specs/Authority.lean`: only `loopStep` and `caoSetMultiplier` make such calls, and each
logs it). Along any run, every such logged call is authorized by its origin
(`Origin.Authorized`): either it is element `i` of a `multicall`'s submitted list and that
`multicall`'s `msg.sender` was the owner in the storage the `multicall` was entered with, or it is
`t.setTokenMultiplier(n, d)` (selector `0x235d9eb5`, value zero) made by a
`setTokenMultiplier(t, n, d)` whose `msg.sender` was the setter in the storage it ran on. Calls
whose low-level result is a failure are included (`ok = false`). -/
@[headline] def Properties.CallsAreOwnersOrSetters : Prop :=
  ∀ (cfg : Config) (S S' : State) (L : List Event), Sem cfg .acts S L S' →
    ∀ o c ok, Event.caoCall o c ok ∈ L → o.Authorized c

/-- **(a) WHAT A DIAMOND OR THE BRIDGEHUB RECEIVES FROM THE `ChainAdminOwnable` IS A CALL IT
MADE.** Along any run, every logged successful call into a diamond (or into the Bridgehub) whose
`msg.sender` is the `ChainAdminOwnable` has a logged successful call of the `ChainAdminOwnable`
with that target and that selector, and that call is authorized by its origin, as in
`CallsAreOwnersOrSetters`. So a diamond or the Bridgehub sees `msg.sender` equal to the
`ChainAdminOwnable` only in calls made by a `multicall` that the owner of that moment entered, or
by a `setTokenMultiplier` that the setter of that moment entered. -/
@[headline] def Properties.ReceivedCallsAreOwnersOrSetters : Prop :=
  ∀ (cfg : Config) (S S' : State) (L : List Event), Sem cfg .acts S L S' →
    (∀ D sel, Event.chainEntry D cfg.cao sel ∈ L →
      ∃ o c, Event.caoCall o c true ∈ L ∧ o.Authorized c ∧ c.target = D ∧ c.data.take 4 = sel) ∧
    (∀ sel, Event.hubEntry cfg.cao sel ∈ L →
      ∃ o c, Event.caoCall o c true ∈ L ∧ o.Authorized c ∧ c.target = cfg.hub ∧
        c.data.take 4 = sel)

/-! ## Storage -/

/-- **EVERY WRITE PASSED ITS ACCESS CHECK.** Along any run, every logged write to the
`ChainAdminOwnable`'s storage was made by the nominee (`acceptOwnership`) or by the owner (every
other writer), read from the storage the write ran on (`CaoWrite.Guard`). -/
def Properties.WritesAreGuarded : Prop :=
  ∀ (cfg : Config) (S S' : State) (L : List Event), Sem cfg .acts S L S' →
    ∀ inv pre w, Event.caoWrite inv pre w ∈ L → w.Guard inv pre

/-- **(b) THE SETTER CHANGES ONLY BY THE OWNER.** Along any run, the final setter is the initial
one, or a logged `setTokenMultiplierSetter` wrote exactly it, called by the owner of that
moment. -/
@[headline] def Properties.SetterChangesOnlyByOwner : Prop :=
  ∀ (cfg : Config) (S S' : State) (L : List Event), Sem cfg .acts S L S' →
    S'.cao.setter = S.cao.setter ∨
      ∃ inv pre, Event.caoWrite inv pre (.setSetter S'.cao.setter) ∈ L ∧ inv = pre.owner

/-- **(c) THE OWNER CHANGES ONLY BY AN ACCEPT OR A RENOUNCE.** Along any run:
* the final owner is the initial one; or it called `acceptOwnership` (logged) while it was the
  nominee; or it is zero and a `renounceOwnership` by the owner of that moment is logged;
* the final nominee is the initial one, or zero, or a logged `transferOwnership` by the owner of
  that moment named it. -/
@[headline] def Properties.OwnerChangesOnlyByAcceptOrRenounce : Prop :=
  ∀ (cfg : Config) (S S' : State) (L : List Event), Sem cfg .acts S L S' →
    (S'.cao.owner = S.cao.owner ∨
      (∃ pre, Event.caoWrite S'.cao.owner pre (.own .accept) ∈ L ∧ pre.pending = S'.cao.owner) ∨
      (S'.cao.owner = 0 ∧
        ∃ inv pre, Event.caoWrite inv pre (.own .renounce) ∈ L ∧ inv = pre.owner)) ∧
    (S'.cao.pending = S.cao.pending ∨ S'.cao.pending = 0 ∨
      ∃ inv pre, Event.caoWrite inv pre (.own (.transfer S'.cao.pending)) ∈ L ∧ inv = pre.owner)

/-- **A ZERO SETTER MAKES NO CALL.** In a well-formed configuration, start from storage whose
setter is zero, as the deploy script constructs the Bridgehub's `ChainAdminOwnable`
(`DeployL1CoreUtils.s.sol:117-118`). Along any run that logs no `setTokenMultiplierSetter` write,
the setter stays zero and no `setTokenMultiplier` call of the `ChainAdminOwnable` is logged:
every sender is nonzero, so none passes `msg.sender == tokenMultiplierSetter`. -/
def Properties.ZeroSetterIsInert : Prop :=
  ∀ (cfg : Config) (S S' : State) (L : List Event), cfg.WF → S.cao.setter = 0 →
    Sem cfg .acts S L S' → (∀ inv pre x, Event.caoWrite inv pre (.setSetter x) ∉ L) →
    S'.cao.setter = 0 ∧ ∀ inv pre t n d c ok, Event.caoCall (.multiplier inv pre t n d) c ok ∉ L

/-! ## A renounce strands the contract -/

/-- **(c) A RENOUNCE IS PERMANENT.** In a well-formed configuration, start from storage with no
owner and no nominee. Along any run, the storage ends as it started, no write to it is logged, and
every call the `ChainAdminOwnable` made is `t.setTokenMultiplier(n, d)` with value zero, from a
`setTokenMultiplier` called by the setter of the start storage, and succeeded. -/
def Properties.RenounceIsPermanent : Prop :=
  ∀ (cfg : Config) (S S' : State) (L : List Event), cfg.WF → S.cao.owner = 0 →
    S.cao.pending = 0 → Sem cfg .acts S L S' →
    S'.cao = S.cao ∧ (∀ inv pre w, Event.caoWrite inv pre w ∉ L) ∧
      ∀ o c ok, Event.caoCall o c ok ∈ L →
        ∃ t n d, o = .multiplier S.cao.setter S.cao t n d ∧ c = ⟨t, 0, multiplierData n d⟩ ∧
          ok = true

/-- **NO OWNER MEANS NO NOMINEE.** In a well-formed configuration, runs keep "owner zero implies
nominee zero". -/
def Properties.OwnerlessHasNoNominee : Prop :=
  ∀ (cfg : Config) (S S' : State) (L : List Event), cfg.WF →
    (S.cao.owner = 0 → S.cao.pending = 0) → Sem cfg .acts S L S' →
    S'.cao.owner = 0 → S'.cao.pending = 0

/-- **FROM CONSTRUCTION ON, AN OWNER OF ZERO IS PERMANENT.** In a well-formed configuration, take
storage the constructor left (`construct o σ`), a run to a state `S₁` whose owner is zero, and
any run from `S₁`. The second run leaves the storage as it is at `S₁`, and every call the
`ChainAdminOwnable` makes in it is a `setTokenMultiplier` call made for the setter of `S₁`.
`S₁` is the end of a run: a point between calls, not one inside a `multicall` (see
`MulticallOutlivesRenounce`). -/
@[headline] def Properties.ConstructedThenOwnerlessIsPermanent : Prop :=
  ∀ (cfg : Config) (S₀ S₁ S₂ : State) (L₁ L₂ : List Event) (o σ : Address), cfg.WF →
    construct o σ = some S₀.cao → Sem cfg .acts S₀ L₁ S₁ → S₁.cao.owner = 0 →
    Sem cfg .acts S₁ L₂ S₂ →
    S₂.cao = S₁.cao ∧
      ∀ o' c ok, Event.caoCall o' c ok ∈ L₂ →
        ∃ t n d, o' = .multiplier S₁.cao.setter S₁.cao t n d ∧ c = ⟨t, 0, multiplierData n d⟩

/-! ## The boundary -/

/-- **A RENOUNCE DOES NOT STOP A RUNNING `multicall`.** In the witness configuration, from `wS1`
(owner `6`, setter `7`, the `ChainAdminOwnable` admin of diamond `4`), the owner submits
`multicall(wCallsB, true)`. Its first call reaches the owner's own code (address `6`, empty
calldata), which calls `renounceOwnership()`; its second call, made after that, sets the diamond's
pending admin to `12`. The run commits with exactly this log, in this order, and ends with the
storage renounced and the diamond's pending admin `12`. -/
@[countermodel] def Properties.MulticallOutlivesRenounce : Prop :=
  ∃ L S', Sem wCfg .acts wS1 L S' ∧
    L = [.caoWrite 6 ⟨6, 0, 7⟩ (.own .renounce),
      .caoCall (.multicall 6 ⟨6, 0, 7⟩ wCallsB 0) ⟨6, 0, []⟩ true,
      .chainEntry 4 1 SEL_SET_PENDING_ADMIN,
      .caoCall (.multicall 6 ⟨6, 0, 7⟩ wCallsB 1) ⟨4, 0, withWord SEL_SET_PENDING_ADMIN 12⟩ true] ∧
    S'.cao = ⟨0, 0, 7⟩ ∧ S'.chain 4 = ⟨1, 12⟩

/-! ## Witnesses -/

/-- **THE CALL AND STORAGE RESULTS ARE NOT VACUOUS.** In the witness configuration, the start
storage is what the constructor leaves for owner `6` and setter zero, and one run from `wS0`:
* the owner sets the setter to `7` (logged write, by the owner);
* the setter's `setTokenMultiplier(4, 3, 2)` makes the `ChainAdminOwnable` call diamond `4`;
* the owner's `multicall(wCallsA, true)` makes both submitted calls, nominating `8` as pending
  admin of the diamond and of the Bridgehub;
* the owner nominates `10`, which accepts.
The diamond logs the two entries and the Bridgehub the one entry these calls make. The run ends
with owner `10`, no nominee and setter `7`, and with `8` the pending admin of the diamond and of
the Bridgehub. -/
@[witness] def Properties.AuthorityWitness : Prop :=
  construct 6 0 = some wS0.cao ∧
    ∃ L S', Sem wCfg .acts wS0 L S' ∧
      Event.caoWrite 6 ⟨6, 0, 0⟩ (.setSetter 7) ∈ L ∧
      Event.caoCall (.multiplier 7 ⟨6, 0, 7⟩ 4 3 2) ⟨4, 0, multiplierData 3 2⟩ true ∈ L ∧
      Event.caoCall (.multicall 6 ⟨6, 0, 7⟩ wCallsA 0)
        ⟨4, 0, withWord SEL_SET_PENDING_ADMIN 8⟩ true ∈ L ∧
      Event.caoCall (.multicall 6 ⟨6, 0, 7⟩ wCallsA 1)
        ⟨2, 0, withWord SEL_SET_PENDING_ADMIN 8⟩ true ∈ L ∧
      Event.caoWrite 6 ⟨6, 0, 7⟩ (.own (.transfer 10)) ∈ L ∧
      Event.caoWrite 10 ⟨6, 10, 7⟩ (.own .accept) ∈ L ∧
      Event.chainEntry 4 1 SEL_SET_MULTIPLIER ∈ L ∧ Event.chainEntry 4 1 SEL_SET_PENDING_ADMIN ∈ L ∧
      Event.hubEntry 1 SEL_SET_PENDING_ADMIN ∈ L ∧
      S'.cao = ⟨10, 0, 7⟩ ∧ S'.chain 4 = ⟨1, 8⟩ ∧ S'.hub = ⟨9, 0, 1, 8⟩

/-- **`ZeroSetterIsInert` IS NOT VACUOUS.** The witness configuration is well formed, and the
start storage has setter zero. From `wS0`, the owner's `multicall(wCallsA, true)` commits: the
`ChainAdminOwnable` makes both submitted calls, the run logs no `setTokenMultiplierSetter`
write, and the setter is still zero at the end. -/
@[witness] def Properties.ZeroSetterWitness : Prop :=
  wCfg.WF ∧ wS0.cao.setter = 0 ∧
    ∃ L S', Sem wCfg .acts wS0 L S' ∧ (∀ inv pre x, Event.caoWrite inv pre (.setSetter x) ∉ L) ∧
      Event.caoCall (.multicall 6 wS0.cao wCallsA 1) ⟨2, 0, withWord SEL_SET_PENDING_ADMIN 8⟩
        true ∈ L ∧
      S'.cao.setter = 0

/-- **THE RENOUNCE RESULTS ARE NOT VACUOUS.** The witness configuration is well formed. From the
constructed start storage, a run in which the owner sets the setter to `7` and renounces ends in
`wRenounced` (owner and nominee zero, setter `7`), with the renounce logged. From `wRenounced`, a
run of the setter's `setTokenMultiplier(4, 3, 2)` and `setTokenMultiplier(11, 3, 2)` commits: the
`ChainAdminOwnable` calls diamond `4` and address `11`, which runs no modelled contract, and its
storage stays `wRenounced`'s. -/
@[witness] def Properties.RenounceWitness : Prop :=
  wCfg.WF ∧ construct 6 0 = some wS0.cao ∧ wRenounced.cao.owner = 0 ∧ wRenounced.cao.pending = 0 ∧
    (∃ L, Sem wCfg .acts wS0 L wRenounced ∧ Event.caoWrite 6 ⟨6, 0, 7⟩ (.own .renounce) ∈ L) ∧
    ∃ L S', Sem wCfg .acts wRenounced L S' ∧
      Event.caoCall (.multiplier 7 ⟨0, 0, 7⟩ 4 3 2) ⟨4, 0, multiplierData 3 2⟩ true ∈ L ∧
      Event.caoCall (.multiplier 7 ⟨0, 0, 7⟩ 11 3 2) ⟨11, 0, multiplierData 3 2⟩ true ∈ L ∧
      S'.cao = wRenounced.cao

end Contracts.ChainAdminOwnable
