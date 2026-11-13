import EraSpec.Contracts.RegistryBootstrapMigration.Specs.AuthorityStrong

/-!
# Properties: who can move a CTM parked on the spent migration

Statements about `EraSpec.Contracts.RegistryBootstrapMigration.Specs.AuthorityStrong`, which is
the label model of `Specs/Authority.lean` and the call model of `Specs/Forward.lean` plus
witness data. Proofs are in
`EraSpec.Contracts.RegistryBootstrapMigration.Proofs.AuthorityStrong`.

## The omitted writer is not the nominee in general

`ParkedCTMLeavesOnlyByNomineeAccept` (`Properties/Authority.lean`) holds over the label model,
which has no CTM code swap. Its docstring said that in the parked states the model reaches,
the `ProxyAdmin`'s owner (who can swap the CTM's code) is the nominee too. That is false
(`ParkedPAOwnerNeedNotBeNominee`). From governance's hand-over, the non-genuine executor's
`migrate()` parks the CTM. One `transferPA 7` by the `ProxyAdmin`'s owner, an ordinary label
step, then reaches a parked state where the `ProxyAdmin`'s owner `7` is not the nominee `3`. A
code swap by `7` moves the CTM off the migration with no accept by anyone.

## The honest frame: two exits

With every call included, and no call sent by the migration:

* `ParkedCTMLeavesByAcceptOrCodeSwap`: one call from a parked state leaves the owner and the
  nominee as they were, or is the nominee's `acceptOwnership()`, or is a CTM code swap sent by
  the `ProxyAdmin`'s owner of that state.
* `ParkedCTMFirstExit`: along any sequence of calls (any number of transactions and forwards),
  the CTM stays parked with its nominee, or the run splits at a call `c` such that every state
  before `c` is parked with the start's nominee (so `c` is the first call that moves it), and
  `c` is the start state's nominee's `acceptOwnership()` or a CTM code swap sent by whoever owns
  the `ProxyAdmin` at that point.
* `SpentProxyAdminCustody`: once the edge is spent, that owner is the start's `ProxyAdmin`
  owner, zero, or an address some `ProxyAdmin` transfer in the run named.
* `SpentLabelRunsAreCalls`: from a spent edge, every run of the label model is a run of calls
  none sent by the migration, with the same labels. So the two results above cover the label
  model, and `ParkedCTMLeavesOnlyByNomineeAccept` is their special case without code swaps.

`AuthorityStrongWitness` fires both exits from `wParked`: the nominee's accept, and a hand-on of
the `ProxyAdmin` followed by its new owner's code swap.
-/

namespace Contracts.RegistryBootstrapMigration

/-! ## The countermodel -/

/-- **THE `ProxyAdmin`'S OWNER NEED NOT BE THE PARKED CTM'S NOMINEE.** In the witness
configuration with a non-genuine executor:
* governance nominates the migration and hands it the `ProxyAdmin`, and `migrate()` leaves
  `wParked` (CTM owned by the migration, executor `3` nominated, `ProxyAdmin` with `3`);
* the `ProxyAdmin`'s owner `3` transfers it to `7`, an ordinary `transferPA` step, and the CTM
  is still parked on the spent migration with nominee `3`, but the `ProxyAdmin`'s owner is now
  `7`;
* `7`, which is neither the migration nor the nominee, swaps the CTM's code, and the CTM leaves
  the migration. The conclusion of `ForwardMovesParkedCTMOnlyByNomineeAccept` fails: the owner
  moved and no call is the nominee's accept.

So the sentence "In the parked states this model reaches, that owner is the nominee too" is
false, and the code swap is a second exit. -/
def Properties.ParkedPAOwnerNeedNotBeNominee : Prop :=
  ARun (wConfig false) wPre [.nominate 50, .transferPA 50, .migrate] wParked ∧
    AStep (wConfig false) wParked (.transferPA 7) wParkedHandedOn ∧
    wParkedHandedOn.ctmOwner = 50 ∧ wParkedHandedOn.executed = true ∧
    ParkedOnMigration (wConfig false) wParkedHandedOn ∧
    wParkedHandedOn.paOwner ≠ wParkedHandedOn.ctmPending ∧
    (7 : Address) ≠ (wConfig false).M ∧
    FRun (wConfig false) wParkedHandedOn [⟨7, .ctmCodeSwap 7 0 35 60⟩] wParkedSwapped ∧
    wParkedSwapped.ctmOwner = 7 ∧
    ¬ ((wParkedSwapped.ctmOwner = 50 ∧ wParkedSwapped.ctmPending = wParkedHandedOn.ctmPending) ∨
      Call.mk wParkedHandedOn.ctmPending .ctmAcceptOwnership ∈
        ([⟨7, .ctmCodeSwap 7 0 35 60⟩] : List Call))

/-! ## The frame with code swaps included -/

/-- **ONE CALL MOVES A PARKED CTM ONLY BY THE NOMINEE'S ACCEPT OR A CODE SWAP BY THE
`ProxyAdmin`'S OWNER.** From a state where the spent migration owns the CTM, one successful call
not sent by the migration does one of three things:
* it leaves the owner, the nominee and the spent flag as they were;
* it is the nominee's own `acceptOwnership()`, which makes the nominee the owner and clears the
  nomination;
* it replaces the CTM's code, and its sender is the `ProxyAdmin`'s owner in that state, who
  need not be the nominee (`ParkedPAOwnerNeedNotBeNominee`).

No premise on what the call is: renounces and forwarded calls are included. -/
def Properties.ParkedCTMLeavesByAcceptOrCodeSwap : Prop :=
  ∀ (K : Config) (s s' : AState) (c : Call), s.ctmOwner = K.M → s.executed = true →
    c.sender ≠ K.M → OpStep K c.sender s c.op s' →
    (s'.ctmOwner = K.M ∧ s'.ctmPending = s.ctmPending ∧ s'.executed = true) ∨
      (c = ⟨s.ctmPending, .ctmAcceptOwnership⟩ ∧ s'.ctmOwner = s.ctmPending ∧
        s'.ctmPending = 0) ∨
      (c.op.swapsCtmCode ∧ c.sender = s.paOwner)

/-- **ALONG ANY CALLS, A PARKED CTM FIRST MOVES BY THE NOMINEE'S ACCEPT OR BY A CODE SWAP FROM
THE `ProxyAdmin`'S OWNER OF THE MOMENT.** Start from a state where the spent migration owns the
CTM. Take a successful sequence of calls, none sent by the migration (any number of
transactions, forwards included: several transactions in a row are one `FRun`). Then either
the owner and the nominee are as at the start, or the sequence splits as `pre ++ c :: post` at
a first call `c` that changes them:
* every state the run passes through before `c` (the state after any prefix of `pre`, the start
  and the state `t` just before `c` included) has the migration as the CTM's owner and the
  start's nominee as its nominee, so no earlier call moved the CTM, even temporarily;
* `c` leaves a state where that no longer holds;
* `c` is the start nominee's `acceptOwnership()`, or a CTM code swap sent by the owner of the
  `ProxyAdmin` in the state just before `c`.

That owner can differ from the start's `ProxyAdmin` owner and from the nominee. Who it can be
is `SpentProxyAdminCustody`. The prefix clause matters because a code swap can write the
migration and the old nominee back, so without it a later return-then-exit could be picked. -/
def Properties.ParkedCTMFirstExit : Prop :=
  ∀ (K : Config) (s s' : AState) (cs : List Call), s.ctmOwner = K.M → s.executed = true →
    (∀ c ∈ cs, c.sender ≠ K.M) → FRun K s cs s' →
    (s'.ctmOwner = K.M ∧ s'.ctmPending = s.ctmPending) ∨
      ∃ (pre post : List Call) (c : Call) (t t' : AState), cs = pre ++ c :: post ∧
        FRun K s pre t ∧ OpStep K c.sender t c.op t' ∧ FRun K t' post s' ∧
        (∀ (p₁ p₂ : List Call) (u : AState), pre = p₁ ++ p₂ → FRun K s p₁ u →
          u.ctmOwner = K.M ∧ u.ctmPending = s.ctmPending) ∧
        t.ctmOwner = K.M ∧ t.ctmPending = s.ctmPending ∧
        ¬ (t'.ctmOwner = K.M ∧ t'.ctmPending = s.ctmPending) ∧
        (c = ⟨s.ctmPending, .ctmAcceptOwnership⟩ ∨ (c.op.swapsCtmCode ∧ c.sender = t.paOwner))

/-- **ONCE THE EDGE IS SPENT, THE `ProxyAdmin` CHANGES HANDS ONLY BY ITS OWN TRANSFERS AND ITS
RENOUNCE.** Along any successful sequence of calls from a spent state, the `ProxyAdmin`'s owner
at the end is the one at the start, or zero, or an address that some
`transferOwnership` call on the `ProxyAdmin` in the sequence named. Each such call is sent by
the `ProxyAdmin`'s owner of its moment (`OpStep.paTransferOwnership`). -/
def Properties.SpentProxyAdminCustody : Prop :=
  ∀ (K : Config) (s s' : AState) (cs : List Call), s.executed = true → FRun K s cs s' →
    s'.paOwner = s.paOwner ∨ s'.paOwner = 0 ∨ ∃ c ∈ cs, c.op = .paTransferOwnership s'.paOwner

/-- **FROM A SPENT EDGE, THE LABEL MODEL'S RUNS ARE RUNS OF CALLS NOT SENT BY THE MIGRATION.**
Every run of `Specs/Authority.lean`'s transactions from a state where the edge is spent is a
run of calls with the same labels, none sent by the migration. So `ParkedCTMLeavesByAcceptOrCodeSwap`
and `ParkedCTMFirstExit` apply to it. Unlike `LabelsAreCoveredCalls`, no owner needs to be
nonzero. -/
def Properties.SpentLabelRunsAreCalls : Prop :=
  ∀ (K : Config) (s s' : AState) (ls : List Label), s.executed = true → ARun K s ls s' →
    ∃ cs : List Call, (∀ c ∈ cs, c.sender ≠ K.M) ∧ cs.flatMap Call.labels = ls ∧ FRun K s cs s'

/-! ## Witness -/

/-- **BOTH EXITS FIRE, AND THE PREMISES ARE MET.** Start from `wParked`, which the non-genuine
executor's `migrate()` leaves: the spent migration `50` owns the CTM, executor `3` is
nominated and owns the `ProxyAdmin`.
* The accept exit: `3`'s `acceptOwnership()` makes it the owner with no nominee.
* The code-swap exit, as `ParkedCTMFirstExit` splits it: `3` hands `7` the `ProxyAdmin`, which
  leaves the CTM parked with nominee `3`; then `7`, the `ProxyAdmin`'s owner of that moment and
  not the nominee, swaps the CTM's code and the CTM leaves the migration. `7` is named by the
  transfer.
* No call is sent by the migration.
* A label run from `wParked` (the hand-on, then the nominee's accept) is a run of calls with the
  same labels. -/
def Properties.AuthorityStrongWitness : Prop :=
  wParked.ctmOwner = (wConfig false).M ∧ wParked.executed = true ∧
    FRun (wConfig false) wParked [⟨3, .ctmAcceptOwnership⟩] ⟨3, 0, 3, 35, 60, true⟩ ∧
    (∀ c ∈ wHandOnThenSwap, c.sender ≠ (wConfig false).M) ∧
    FRun (wConfig false) wParked wHandOnThenSwap wParkedSwapped ∧
    wHandOnThenSwap = [⟨3, .paTransferOwnership 7⟩] ++ [⟨7, .ctmCodeSwap 7 0 35 60⟩] ∧
    FRun (wConfig false) wParked [⟨3, .paTransferOwnership 7⟩] wParkedHandedOn ∧
    wParkedHandedOn.ctmOwner = (wConfig false).M ∧
    wParkedHandedOn.ctmPending = wParked.ctmPending ∧
    OpStep (wConfig false) 7 wParkedHandedOn (.ctmCodeSwap 7 0 35 60) wParkedSwapped ∧
    wParkedSwapped.ctmOwner ≠ (wConfig false).M ∧
    wParkedHandedOn.paOwner = 7 ∧ (7 : Address) ≠ wParked.ctmPending ∧
    (7 : Address) ≠ wParked.paOwner ∧
    (∃ c ∈ wHandOnThenSwap, c.op = .paTransferOwnership wParkedSwapped.paOwner) ∧
    ARun (wConfig false) wParked [.transferPA 7, .accept] ⟨3, 0, 7, 35, 60, true⟩

end Contracts.RegistryBootstrapMigration
