import EraSpec.Contracts.RegistryBootstrapMigration.Specs.Forward

/-!
# Properties: forwarded calls and the authority model's label set

Statements about `EraSpec.Contracts.RegistryBootstrapMigration.Specs.Forward`. Proofs are
in `EraSpec.Contracts.RegistryBootstrapMigration.Proofs.Forward`.

## What holds

* **A forward is a run of the model's own transactions.** Take a successful transaction:
  a `forward`, with the calls its targets make in turn. Suppose no call is sent by the
  migration or the zero address, and none renounces an ownership or replaces the CTM's
  code. Then its start and end states are related by the run of its calls' labels in
  `Specs/Authority.lean` (`ForwardIsARun`):
  * each ownership or version call is the matching other-actor label;
  * `migrate()` is `migrate`;
  * a call that writes nothing tracked is no step.

  The labels hand authority to the migration only where the calls do. No premise is made on
  the executor's code. The same holds for whole runs that mix forwards with the model's
  transactions (`RunsWithForwardsAreRuns`). So every result stated "along any run", such as
  `NoReparkingAfterMigrate`, applies to them as stated.
* **Conversely, each label is one covered call** (`LabelsAreCoveredCalls`), from any state
  where both owners are nonzero (which the model's runs keep, `LabelRunsKeepOwnersNonzero`).
  From such a state the labels allow no step that a covered call could not make.
* **The run results hold across forwards, and need less.**
  * `NoReparkingAcrossForwards`: from a spent edge with nothing parked, a run whose forwards
    hand nothing to the migration and do not replace the CTM's code parks nothing. Unlike the
    route through `ForwardIsARun`, it also covers renounces and needs no premise on senders.
  * `ForwardMovesParkedCTMOnlyByNomineeAccept`: while the spent migration owns the CTM, a
    forward with no call from the migration and no CTM code swap moves it only if the
    forward contains the nominee's own `acceptOwnership()`.
  * `ForwardMovesParkedProxyAdminOnlyByMigrate`: a `ProxyAdmin` owned by the migration leaves
    it only through a forward that contains a successful `migrate()`. This one holds even with
    code swaps.

## What the label set misses

* **Renouncing.** The CTM (`Ownable2StepUpgradeable`) and the CTM-domain `ProxyAdmin`
  (`Ownable`) both keep OpenZeppelin's `renounceOwnership`, and a forward can call either.
  The state it leaves is reached by no run of the model's labels, because those runs keep
  both owners nonzero (`LabelRunsKeepOwnersNonzero`, `ForwardedRenounceLeavesTheLabelSet`).
  So the folder README's argument fails for this call. It does not park anything, and
  `NoReparkingAcrossForwards` covers it.
* **Renounced authority is stranded** (`RenouncedAuthorityIsStranded`). Once the
  `ProxyAdmin` has no owner, no call moves it again. Once the CTM has neither an owner nor a
  nominee, it gets them back only through a code swap by the `ProxyAdmin`'s owner.
  `RenounceStrandsWitness` shows both. `UpgradeExecutorBase.sol:14-17` says `forward` keeps
  the authority the executor holds reachable, and :48-53 disables `renounceOwnership` on the
  executor itself so that it cannot strand that authority. The authorities it holds keep
  their own `renounceOwnership`, so one forwarded call strands them.

## What is excluded: replacing the CTM's code

* `upgrade`/`upgradeAndCall` on the CTM proxy, through the `ProxyAdmin` the executor owns,
  is outside the label set: the CTM afterwards runs unknown code.
  * In the authority model it can park the CTM on the spent migration with no ownership
    call naming it (`ForwardCtmSwapReparks`).
  * It can move a parked CTM without the nominee's accept (`ForwardCtmSwapMovesParkedCTM`).

  In the version model it voids the CTM's invariants
  (`Contracts.ChainTypeManager.Properties.ForwardCtmSwapBreaksInvariants`). Both premises
  that exclude it are needed.

## Witnesses

* `ForwardWitness` is the witness bundle followed by an executor succession through
  `forward`: version move, nomination, `ProxyAdmin` hand-over, then the successor's own
  accept as a nested call. Every call is covered, none hands anything to the migration, and
  the successor ends up owning both authorities.
* `ParkedForwardFramesFire` shows that both frames have content.
  * In the non-genuine parked state, the executor's `acceptCTMOwnership()` does nothing. If
    its `forward` runs `UpgradeExecutorBase`'s code, it can still recover the CTM by
    forwarding the CTM's `acceptOwnership()`, the escape hatch of
    `UpgradeExecutorBase.sol:14-17`.
  * A forwarded `migrate()` moves a `ProxyAdmin` the migration holds.
-/

namespace Contracts.RegistryBootstrapMigration

/-! ## The label set covers forwarded calls -/

/-- **A FORWARD IS A RUN OF THE MODEL'S OWN TRANSACTIONS.** If no call of a successful
transaction is sent by the migration or by the zero address, renounces an ownership, or
replaces the CTM's code, then the transaction relates its start and end states as the run of
its calls' labels does. Each of those labels is an other-actor label or `migrate`, and one
hands authority to the migration only if one of the calls does. -/
def Properties.ForwardIsARun : Prop :=
  ∀ (K : Config) (s s' : AState) (cs : List Call), (∀ c ∈ cs, c.Covered K) →
    FRun K s cs s' →
    ARun K s (cs.flatMap Call.labels) s' ∧
      (∀ l ∈ cs.flatMap Call.labels, l.OtherActor ∨ l = .migrate) ∧
      (∀ l ∈ cs.flatMap Call.labels, l.handsToMigration K → ∃ c ∈ cs, c.op.handsToMigration K)

/-- **RUNS WITH FORWARDS ARE RUNS.** Along any run of the extended model whose forwards'
calls are all covered, the start and end states are related by the run of the model's labels
obtained by replacing each forward with its calls' labels. One of those labels hands
authority to the migration only if one of the run's transactions does. So every property of
`Specs/Authority.lean`'s runs applies to such runs. -/
def Properties.RunsWithForwardsAreRuns : Prop :=
  ∀ (K : Config) (s s' : AState) (xs : List XLabel), (∀ x ∈ xs, x.Covered K) →
    XRun K s xs s' →
    ARun K s (xs.flatMap XLabel.labels) s' ∧
      (∀ l ∈ xs.flatMap XLabel.labels, l.handsToMigration K → ∃ x ∈ xs, x.handsToMigration K)

/-- **EACH LABEL IS ONE COVERED CALL.** The converse of `ForwardIsARun`. From a state where
the CTM and the `ProxyAdmin` both have a nonzero owner, every successful transaction of
`Specs/Authority.lean` other than the bundle is one covered call, whose label is that
transaction's. The sender is the owner, the nominee, or (for `migrate()`) the executor. So
from such a state the labels allow no step that a covered call could not make. -/
def Properties.LabelsAreCoveredCalls : Prop :=
  ∀ (K : Config) (s s' : AState) (l : Label), s.ctmOwner ≠ 0 → s.paOwner ≠ 0 → l ≠ .bundle →
    AStep K s l s' → ∃ c : Call, c.Covered K ∧ c.labels = [l] ∧ FRun K s [c] s'

/-! ## The run results across forwards -/

/-- **NOTHING RE-PARKS ACROSS FORWARDS.** Start from a state where nothing is parked on the
migration and the edge is spent. Along any run of the model's transactions and forwards,
suppose no transaction hands authority to the migration by an ownership call and no forward
replaces the CTM's code. Then nothing is parked on the migration at the end. There is no
premise on senders, and renounces are allowed. -/
def Properties.NoReparkingAcrossForwards : Prop :=
  ∀ (K : Config) (s s' : AState) (xs : List XLabel), s.executed = true →
    ¬ ParkedOnMigration K s → XRun K s xs s' →
    (∀ x ∈ xs, ¬ x.handsToMigration K) → (∀ x ∈ xs, ¬ x.swapsCtmCode) →
    ¬ ParkedOnMigration K s'

/-- **WHILE THE SPENT MIGRATION OWNS THE CTM, A FORWARD MOVES IT ONLY BY THE NOMINEE'S
ACCEPT.** Start from a state where the migration owns the CTM and the edge is spent. Take a
successful transaction where no call is sent by the migration and none replaces the CTM's
code. Then either the owner is still the migration with the nomination unchanged, or the
transaction contains an `acceptOwnership()` sent by the nominee of the start state. -/
def Properties.ForwardMovesParkedCTMOnlyByNomineeAccept : Prop :=
  ∀ (K : Config) (s s' : AState) (cs : List Call), s.ctmOwner = K.M → s.executed = true →
    (∀ c ∈ cs, c.sender ≠ K.M) → (∀ c ∈ cs, ¬ c.op.swapsCtmCode) → FRun K s cs s' →
    (s'.ctmOwner = K.M ∧ s'.ctmPending = s.ctmPending) ∨
      Call.mk s.ctmPending .ctmAcceptOwnership ∈ cs

/-- **A `ProxyAdmin` THE MIGRATION OWNS LEAVES IT ONLY THROUGH `migrate()`.** Start from a
state where the migration owns the CTM-domain `ProxyAdmin`. A successful transaction where no
call is sent by the migration either leaves it there, or contains a `migrate()` call. Code
swaps are allowed: they need the `ProxyAdmin`'s owner. -/
def Properties.ForwardMovesParkedProxyAdminOnlyByMigrate : Prop :=
  ∀ (K : Config) (s s' : AState) (cs : List Call), s.paOwner = K.M →
    (∀ c ∈ cs, c.sender ≠ K.M) → FRun K s cs s' →
    s'.paOwner = K.M ∨ ∃ c ∈ cs, c.op = .migrate

/-! ## What the label set misses: renouncing -/

/-- **THE MODEL'S RUNS KEEP BOTH OWNERS NONZERO.** Along any run of `Specs/Authority.lean`'s
transactions, a nonzero CTM owner and a nonzero `ProxyAdmin` owner stay nonzero. -/
def Properties.LabelRunsKeepOwnersNonzero : Prop :=
  ∀ (K : Config) (s s' : AState) (ls : List Label), ARun K s ls s' →
    s.ctmOwner ≠ 0 → s.paOwner ≠ 0 → s'.ctmOwner ≠ 0 ∧ s'.paOwner ≠ 0

/-- **A FORWARDED RENOUNCE IS OUTSIDE THE LABEL SET.** The witness configuration has a
genuine executor. After the witness bundle, executor `3` owns the CTM and the `ProxyAdmin`.
Its forward of `renounceOwnership()` succeeds on either authority. It parks nothing. The
state it leaves is reached by no run of the model's labels from the same start. The sender is
neither the migration nor zero, so `ForwardIsARun` fails only for its label-set premise. -/
def Properties.ForwardedRenounceLeavesTheLabelSet : Prop :=
  (∃ s', FRun (wConfig true) wPost [⟨3, .paRenounceOwnership⟩] s' ∧ s'.paOwner = 0 ∧
      ¬ ParkedOnMigration (wConfig true) s' ∧ ¬ ∃ ls, ARun (wConfig true) wPost ls s') ∧
  (∃ s', FRun (wConfig true) wPost [⟨3, .ctmRenounceOwnership⟩] s' ∧ s'.ctmOwner = 0 ∧
      ¬ ParkedOnMigration (wConfig true) s' ∧ ¬ ∃ ls, ARun (wConfig true) wPost ls s')

/-- **RENOUNCED AUTHORITY IS STRANDED.** Take any sequence of modelled calls, none sent by
the zero address.
* If the `ProxyAdmin` has no owner at the start, it has none at the end.
* If the CTM has neither an owner nor a nominee at the start, then it has neither at the end,
  or the `ProxyAdmin` had an owner at the start and one of the calls replaces the CTM's code.
  So a renounced CTM with a renounced `ProxyAdmin` stays ownerless.

Several transactions in a row are one `FRun`, so this covers any number of them. -/
def Properties.RenouncedAuthorityIsStranded : Prop :=
  ∀ (K : Config) (s s' : AState) (cs : List Call), (∀ c ∈ cs, c.sender ≠ 0) →
    FRun K s cs s' →
    (s.paOwner = 0 → s'.paOwner = 0) ∧
      (s.ctmOwner = 0 → s.ctmPending = 0 →
        (s'.ctmOwner = 0 ∧ s'.ctmPending = 0) ∨ (s.paOwner ≠ 0 ∧ ∃ c ∈ cs, c.op.swapsCtmCode))

/-! ## What is excluded: replacing the CTM's code -/

/-- **A FORWARDED CTM CODE SWAP RE-PARKS THE CTM.** After the witness bundle the edge is spent
and nothing is parked. Executor `3`, owning the `ProxyAdmin`, forwards an `upgradeAndCall` on
the CTM proxy whose new code writes the migration into the CTM's owner slot. The forward
succeeds and makes no ownership call naming the migration. Only the no-swap premise of
`NoReparkingAcrossForwards` fails, and the migration ends up owning the CTM. -/
def Properties.ForwardCtmSwapReparks : Prop :=
  wPost.executed = true ∧ ¬ ParkedOnMigration (wConfig true) wPost ∧
    ¬ XLabel.handsToMigration (wConfig true) (.forward [⟨3, .ctmCodeSwap 50 0 35 60⟩]) ∧
    XLabel.swapsCtmCode (.forward [⟨3, .ctmCodeSwap 50 0 35 60⟩]) ∧
    ∃ s', XRun (wConfig true) wPost [.forward [⟨3, .ctmCodeSwap 50 0 35 60⟩]] s' ∧
      ParkedOnMigration (wConfig true) s'

/-- **A FORWARDED CTM CODE SWAP MOVES A PARKED CTM WITHOUT AN ACCEPT.** Start from the state
the non-genuine executor's `migrate()` leaves: the migration owns the CTM with executor `3`
nominated, and `3` owns the `ProxyAdmin`. A forward by `3` of an `upgradeAndCall` on the CTM
proxy, whose new code writes governance `9` as owner, succeeds. The conclusion of
`ForwardMovesParkedCTMOnlyByNomineeAccept` fails: the CTM has left the migration, and the
forward contains no accept. -/
def Properties.ForwardCtmSwapMovesParkedCTM : Prop :=
  wParked.ctmOwner = 50 ∧ wParked.executed = true ∧
    ∃ s', FRun (wConfig false) wParked [⟨3, .ctmCodeSwap 9 0 35 60⟩] s' ∧ s'.ctmOwner = 9 ∧
      ¬ ((s'.ctmOwner = 50 ∧ s'.ctmPending = wParked.ctmPending) ∨
        Call.mk wParked.ctmPending .ctmAcceptOwnership ∈ [⟨3, .ctmCodeSwap 9 0 35 60⟩])

/-! ## Witnesses -/

/-- **THE COVERAGE AND RE-PARKING RESULTS ARE NOT VACUOUS.** In the witness configuration with
a genuine executor:
* every call of the succession forward is covered, hands nothing to the migration and keeps
  the CTM's code;
* the bundle takes the pre-bundle state to a spent state where nothing is parked and both
  owners are nonzero;
* from there the executor's nomination of `7` is a step other than the bundle (the premises
  of `LabelsAreCoveredCalls` and `LabelRunsKeepOwnersNonzero`);
* from there the forward succeeds, and so does the run of the bundle followed by the forward;
* at the end, successor `7` owns the CTM (with no nomination outstanding) and the
  `ProxyAdmin`, at version 36 on release 61. -/
def Properties.ForwardWitness : Prop :=
  (∀ c ∈ wSuccession, c.Covered (wConfig true) ∧ ¬ c.op.handsToMigration (wConfig true) ∧
      ¬ c.op.swapsCtmCode) ∧
    AStep (wConfig true) wPre .bundle wPost ∧ wPost.executed = true ∧
    ¬ ParkedOnMigration (wConfig true) wPost ∧ wPost.ctmOwner ≠ 0 ∧ wPost.paOwner ≠ 0 ∧
    (∃ s₁, AStep (wConfig true) wPost (.nominate 7) s₁) ∧
    ∃ s', XRun (wConfig true) wPost [.forward wSuccession] s' ∧
      XRun (wConfig true) wPre [.tx .bundle, .forward wSuccession] s' ∧
      s'.ctmOwner = 7 ∧ s'.ctmPending = 0 ∧ s'.paOwner = 7 ∧ s'.ctmPv = 36 ∧ s'.ctmRel = 61

/-- **THE TWO FRAMES ARE NOT VACUOUS.**
* CTM frame: in the state the non-genuine `migrate()` leaves, a call by executor `3` to the
  CTM's `acceptOwnership()` succeeds. Its `forward` makes that call if it runs
  `UpgradeExecutorBase`'s code. The call makes `3` the owner with no nomination left, so the
  parked CTM is recovered.
* `ProxyAdmin` frame: after governance's hand-over the migration owns the `ProxyAdmin`, and a
  `migrate()` call moves it to the executor. -/
def Properties.ParkedForwardFramesFire : Prop :=
  (∃ s', FRun (wConfig false) wParked [⟨3, .ctmAcceptOwnership⟩] s' ∧ s'.ctmOwner = 3 ∧
      s'.ctmPending = 0) ∧
    wHanded.paOwner = 50 ∧ ∃ s', FRun (wConfig true) wHanded [⟨9, .migrate⟩] s' ∧ s'.paOwner = 3

/-- **`RenouncedAuthorityIsStranded` IS NOT VACUOUS.** Both cases start after the witness
bundle.
* Executor `3` forwards renounces of the CTM and then the `ProxyAdmin`. Afterwards there is
  no CTM owner, no nominee and no `ProxyAdmin` owner, and governance's transfer of the
  `ProxyAdmin` back to itself has no successful execution.
* Executor `3` renounces only the CTM. As the `ProxyAdmin`'s owner, it can then restore the
  CTM's owner with a code swap, the only way back. -/
def Properties.RenounceStrandsWitness : Prop :=
  (∃ s', FRun (wConfig true) wPost [⟨3, .ctmRenounceOwnership⟩, ⟨3, .paRenounceOwnership⟩] s' ∧
      s'.ctmOwner = 0 ∧ s'.ctmPending = 0 ∧ s'.paOwner = 0 ∧
      ¬ ∃ s'', FRun (wConfig true) s' [⟨9, .paTransferOwnership 9⟩] s'') ∧
    ∃ s' s'', FRun (wConfig true) wPost [⟨3, .ctmRenounceOwnership⟩] s' ∧
      s'.ctmOwner = 0 ∧ s'.ctmPending = 0 ∧ s'.paOwner = 3 ∧
      FRun (wConfig true) s' [⟨3, .ctmCodeSwap 3 0 35 60⟩] s'' ∧ s''.ctmOwner = 3

end Contracts.RegistryBootstrapMigration
