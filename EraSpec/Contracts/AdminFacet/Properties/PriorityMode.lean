import EraSpec.Contracts.AdminFacet.Specs.Mutants

/-!
# Properties: priority mode (the stage-1 escape hatch)

Statements about `EraSpec.Contracts.AdminFacet.Specs.AdminFacet`; proofs in
`EraSpec.Contracts.AdminFacet.Proofs.PriorityMode`.

* `Stage1InvHoldsAlongRuns` (run, headline): `Stage1Inv` holds where priority mode is neither
  allowed nor active (as on a fresh chain) and is kept by every interleaving of calls,
  environment changes and foreign writes that runs no cut. While
  priority mode is active, it was allowed and the chain is a permanent rollup; once it is allowed,
  operator filtering of priority transactions is off and the transaction filterer is the one
  governance picked for priority mode.
* `NoFacetCallBlocksDueActivation` (run, headline): once `activatePriorityMode` succeeds, after
  any further run without cuts priority mode is active or activation still succeeds, provided the
  selector is not freezable or the CTM sends none of the calls, and every foreign write keeps
  `ActivationQueueReady`.
* `OneWayFlagsAlongRuns` (run): without cuts, `isPermanentRollup`, `secondProofSystemRequired`
  and `canBeActivated` are never cleared, and once priority mode is allowed the fee parameters'
  pricing mode and three capacity fields never change.
* `ActivatePriorityModeExact`: `activatePriorityMode` succeeds, for any caller, exactly under its
  preconditions, and reverts every committed but unexecuted batch.
* `PriorityModeTogglesOnlyByItsEntries` (run): without cuts, priority mode turns on only by
  `activatePriorityMode` and off only by the CTM's `deactivatePriorityMode`.
* Witnesses: `PriorityModeWitness`, `PriorityModeDeactivationWitness`, `OneWayFlagsWitness`,
  `DueActivationSurvivesWitness`, and `PriorityModeActivationRevertsBatchesWitness` (a nonzero
  filterer installed, batches reverted and the upgrade batch number cleared).
* Countermodels: `CTMFreezeBlocksActivation` (the last premise of
  `NoFacetCallBlocksDueActivation` is needed), `ActivationNeedsPermanentRollup` (the
  permanent-rollup condition of `ActivatePriorityModeExact` is the only failing one in a reachable
  state), `UnguardedFiltererBreaksStage1`, `UnguardedL1FilteringBreaksStage1` (deleting either
  `NotCompatibleWithPriorityMode` check breaks `Stage1Inv` in one step).
-/

namespace Contracts.AdminFacet

/-- **HEADLINE: THE STAGE-1 INVARIANT HOLDS ALONG EVERY RUN WITHOUT CUTS.** A state where priority
mode is neither allowed nor active satisfies `Stage1Inv` (every chain `DiamondInit` creates is one:
of `priorityModeInfo` it writes only `permissionlessValidator`,
`state-transition/chain-deps/DiamondInit.sol:128`); and every run that runs no cut — any calls by
anyone at any times, environment changes, writes by the other facets — keeps it. -/
def Properties.Stage1InvHoldsAlongRuns : Prop :=
  (∀ s : State, s.priorityMode.canBeActivated = false → s.priorityMode.activated = false →
      Stage1Inv s) ∧
  ∀ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' → (∀ l ∈ ls, l.runsCut = false) → Stage1Inv w.st → Stage1Inv w'.st

/-- **HEADLINE: NO FACET CALL BLOCKS A DUE ACTIVATION.** Suppose `activatePriorityMode` succeeds
at time `τ` in the world `w`. Take any run from `w` that runs no cut and in which every foreign
write leaves `ActivationQueueReady s' τ` true: the chain stays on its settlement layer, the first
unprocessed priority transaction was requested at a recorded time `t ≠ 0` with
`t + PRIORITY_EXPIRATION ≤ τ`, and no more batches are executed than committed. Environment
changes are unrestricted. If the selector of `activatePriorityMode` is not marked freezable, or no
call in the run is sent by the CTM, then at the end priority mode is active or
`activatePriorityMode` succeeds for every caller at every time `τ' ≥ τ`. So no call to this facet
by anyone (other than the CTM when the selector is freezable) undoes a due activation; with the
selector freezable, calls by the CTM can (`CTMFreezeBlocksActivation`). The other facets'
effects (Executor, Mailbox, Migrator: executing or reverting batches, processing the overdue
priority transaction, migrating) enter only as foreign writes, which the `ActivationQueueReady`
premise restricts. Beyond the entries anyone may call, a validator's only entry of this facet
is `upgradeChainFromVersion`, which runs a cut. Runs with cuts are outside the statement. -/
def Properties.NoFacetCallBlocksDueActivation : Prop :=
  ∀ (K : Config) (w w' : World) (ls : List Label) (a : Address) (τ : ℕ),
    (∃ s₁, call K w.env w.st ⟨a, τ, .activatePriorityMode⟩ = some s₁) →
    Run K w ls w' → (∀ l ∈ ls, l.runsCut = false) →
    (∀ s', Label.foreign s' ∈ ls → ActivationQueueReady s' τ) →
    (w.st.freezable Entry.activatePriorityMode.sel = false ∨
      ∀ c, Label.call c ∈ ls → c.sender ≠ w.st.chainTypeManager) →
    w'.st.priorityMode.activated = true ∨
      ∀ (b : Address) (τ' : ℕ), τ ≤ τ' →
        ∃ s₂, call K w'.env w'.st ⟨b, τ', .activatePriorityMode⟩ = some s₂

/-- **ONE-WAY FLAGS.** Along any run without cuts: a permanent rollup stays one, a required second
proof system stays required, an allowed priority mode stays allowed; and once priority mode is
allowed, the pubdata pricing mode, `priorityTxMaxPubdata`, `maxPubdataPerBatch` and
`maxL2GasPerBatch` stay as they were (`Admin.sol:230-232, 246-257, 360-362`). -/
def Properties.OneWayFlagsAlongRuns : Prop :=
  ∀ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' → (∀ l ∈ ls, l.runsCut = false) →
    (w.st.isPermanentRollup = true → w'.st.isPermanentRollup = true) ∧
    (w.st.secondProofSystemRequired = true → w'.st.secondProofSystemRequired = true) ∧
    (w.st.priorityMode.canBeActivated = true →
      w'.st.priorityMode.canBeActivated = true ∧
      w'.st.feeParams.pricingMode = w.st.feeParams.pricingMode ∧
      w'.st.feeParams.priorityTxMaxPubdata = w.st.feeParams.priorityTxMaxPubdata ∧
      w'.st.feeParams.maxPubdataPerBatch = w.st.feeParams.maxPubdataPerBatch ∧
      w'.st.feeParams.maxL2GasPerBatch = w.st.feeParams.maxL2GasPerBatch)

/-- **ACTIVATING PRIORITY MODE, EXACTLY.** For any caller `a` at time `τ`, `activatePriorityMode`
succeeds iff the diamond does not block it, the chain is on its settlement layer and on L1,
priority mode is not active, it has been allowed, the chain is a permanent rollup, the first
unprocessed priority transaction has a recorded request time `t ≠ 0`, `t + 4 days ≤ τ`, and
`totalBatchesExecuted ≤ totalBatchesCommitted`. The new state differs only in: priority mode
active; `totalBatchesCommitted := totalBatchesExecuted`; `totalBatchesVerified` lowered to
`totalBatchesExecuted` if above it; the L2 upgrade batch number cleared if it was among the
reverted batches. The model omits the `nonReentrant` lock and the overflow reverts (see the spec's
module docstring), which can only make the source revert where the model succeeds. -/
def Properties.ActivatePriorityModeExact : Prop :=
  ∀ (K : Config) (e : Env) (s s' : State) (a : Address) (τ : ℕ),
    call K e s ⟨a, τ, .activatePriorityMode⟩ = some s' ↔
      (¬ (s.frozen = true ∧ s.freezable Entry.activatePriorityMode.sel = true) ∧
       s.settlementLayer = 0 ∧ K.onL1 = true ∧
       s.priorityMode.activated = false ∧ s.priorityMode.canBeActivated = true ∧
       s.isPermanentRollup = true ∧
       s.requestTimestamp s.firstUnprocessed ≠ 0 ∧
       s.requestTimestamp s.firstUnprocessed + PRIORITY_EXPIRATION ≤ τ ∧
       s.totalBatchesExecuted ≤ s.totalBatchesCommitted ∧
       s' = { s with
         priorityMode := { s.priorityMode with activated := true }
         totalBatchesCommitted := s.totalBatchesExecuted
         totalBatchesVerified :=
           if s.totalBatchesExecuted < s.totalBatchesVerified then s.totalBatchesExecuted
           else s.totalBatchesVerified
         upgradeBatchNumber :=
           if s.totalBatchesExecuted < s.upgradeBatchNumber then 0 else s.upgradeBatchNumber })

/-- **PRIORITY MODE TOGGLES ONLY THROUGH ITS TWO ENTRIES.** Along any run without cuts: if
priority mode ends active having started inactive, some `activatePriorityMode` call is in the run;
if it ends inactive having started active, the CTM sent `deactivatePriorityMode`. -/
def Properties.PriorityModeTogglesOnlyByItsEntries : Prop :=
  ∀ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' → (∀ l ∈ ls, l.runsCut = false) →
    (w.st.priorityMode.activated = false → w'.st.priorityMode.activated = true →
      ∃ a τ, Label.call ⟨a, τ, .activatePriorityMode⟩ ∈ ls) ∧
    (w.st.priorityMode.activated = true → w'.st.priorityMode.activated = false →
      ∃ τ, Label.call ⟨w.st.chainTypeManager, τ, .deactivatePriorityMode⟩ ∈ ls)

/-! ## Witnesses -/

/-- **WITNESS: PRIORITY MODE IS REACHABLE.** From a chain satisfying `Stage1Inv` with priority mode
neither allowed nor active and not a permanent rollup, a run without cuts ends with priority mode
active and `Stage1Inv` holding (the premises of `Stage1InvHoldsAlongRuns` and the antecedent of
the first half of `PriorityModeTogglesOnlyByItsEntries`). The run contains an
`activatePriorityMode` call from an address that is neither the admin nor the CTM. -/
def Properties.PriorityModeWitness : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' ∧ (∀ l ∈ ls, l.runsCut = false) ∧ Stage1Inv w.st ∧
    w.st.priorityMode.canBeActivated = false ∧ w.st.priorityMode.activated = false ∧
    w.st.isPermanentRollup = false ∧
    w'.st.priorityMode.activated = true ∧ Stage1Inv w'.st ∧
    ∃ a τ, Label.call ⟨a, τ, .activatePriorityMode⟩ ∈ ls ∧
      a ≠ w.st.admin ∧ a ≠ w.st.chainTypeManager

/-- **WITNESS: ALLOWING INSTALLS THE CTM'S FILTERER, AND ACTIVATION REVERTS BATCHES.** From a
state satisfying `Stage1Inv` with priority mode neither allowed nor active, with
`totalBatchesExecuted < totalBatchesVerified < totalBatchesCommitted` and an L2 upgrade batch
number above the executed count, a run without cuts in which the CTM sets a nonzero priority-mode
filterer `f` that differs from the current filterer, the admin allows priority mode and anyone
activates it, ends with `f` installed as the transaction filterer, priority mode active, the
committed and verified counts lowered to the executed count, the upgrade batch number cleared, and
`Stage1Inv` holding. Every effect `ActivatePriorityModeExact` and `permanentlyAllowPriorityMode`
spell out is visible here. -/
def Properties.PriorityModeActivationRevertsBatchesWitness : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label) (f : Address),
    Run K w ls w' ∧ (∀ l ∈ ls, l.runsCut = false) ∧ Stage1Inv w.st ∧
    w.st.priorityMode.canBeActivated = false ∧ w.st.priorityMode.activated = false ∧
    Label.call ⟨w.st.chainTypeManager, 0, .setPriorityModeTransactionFilterer f⟩ ∈ ls ∧
    f ≠ 0 ∧ w.st.transactionFilterer ≠ f ∧
    w.st.totalBatchesExecuted < w.st.totalBatchesVerified ∧
    w.st.totalBatchesVerified < w.st.totalBatchesCommitted ∧
    w.st.totalBatchesExecuted < w.st.upgradeBatchNumber ∧
    w'.st.priorityMode.activated = true ∧ w'.st.transactionFilterer = f ∧
    w'.st.priorityMode.transactionFilterer = f ∧
    w'.st.totalBatchesCommitted = w.st.totalBatchesExecuted ∧
    w'.st.totalBatchesVerified = w.st.totalBatchesExecuted ∧
    w'.st.upgradeBatchNumber = 0 ∧ Stage1Inv w'.st

/-- **WITNESS: PRIORITY MODE TURNED OFF.** From a state satisfying `Stage1Inv` with priority mode
active, a run without cuts ends with priority mode inactive and `Stage1Inv` holding (the
antecedent of the second half of `PriorityModeTogglesOnlyByItsEntries`). -/
def Properties.PriorityModeDeactivationWitness : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' ∧ (∀ l ∈ ls, l.runsCut = false) ∧ Stage1Inv w.st ∧
    w.st.priorityMode.activated = true ∧ w'.st.priorityMode.activated = false ∧
    Stage1Inv w'.st

/-- **WITNESS: FEE PARAMETERS STILL CHANGE ON A STAGE-1 CHAIN.** From a permanent rollup that
requires its second proof system and has priority mode allowed (every antecedent of
`OneWayFlagsAlongRuns` true), a run without cuts changes the fee parameters. -/
def Properties.OneWayFlagsWitness : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' ∧ (∀ l ∈ ls, l.runsCut = false) ∧
    w.st.isPermanentRollup = true ∧ w.st.secondProofSystemRequired = true ∧
    w.st.priorityMode.canBeActivated = true ∧
    w'.st.feeParams ≠ w.st.feeParams

/-- **WITNESS: A DUE ACTIVATION SURVIVES OTHER ACTIVITY.** From a world where
`activatePriorityMode` succeeds at time `τ`, a run without cuts — containing a facet call, an
environment change and a foreign write, with no call from the CTM and every foreign write keeping
`ActivationQueueReady` at `τ` — meets every premise of `NoFacetCallBlocksDueActivation` (both
disjuncts of its last one). At its end the committed batch count differs from the start, priority
mode is inactive and `activatePriorityMode` at `τ` succeeds. -/
def Properties.DueActivationSurvivesWitness : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label) (a : Address) (τ : ℕ) (s₁ s₂ : State),
    call K w.env w.st ⟨a, τ, .activatePriorityMode⟩ = some s₁ ∧
    Run K w ls w' ∧ (∀ l ∈ ls, l.runsCut = false) ∧
    (∀ s', Label.foreign s' ∈ ls → ActivationQueueReady s' τ) ∧
    w.st.freezable Entry.activatePriorityMode.sel = false ∧
    (∀ c, Label.call c ∈ ls → c.sender ≠ w.st.chainTypeManager) ∧
    (∃ c, Label.call c ∈ ls) ∧ (∃ e, Label.env e ∈ ls) ∧ (∃ s', Label.foreign s' ∈ ls) ∧
    w'.st.totalBatchesCommitted ≠ w.st.totalBatchesCommitted ∧
    w'.st.priorityMode.activated = false ∧
    call K w'.env w'.st ⟨a, τ, .activatePriorityMode⟩ = some s₂

/-! ## Countermodels -/

/-- **COUNTERMODEL: WITH A FREEZABLE SELECTOR, THE CTM CAN STOP A DUE ACTIVATION.** The last
premise of `NoFacetCallBlocksDueActivation` is needed. On a chain where `activatePriorityMode`
succeeds at `τ` and its selector is marked freezable, a run without cuts and without foreign
writes, all of whose calls are sent by the CTM, ends with priority mode inactive and
`activatePriorityMode` at `τ` reverting. -/
def Properties.CTMFreezeBlocksActivation : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label) (a : Address) (τ : ℕ) (s₁ : State),
    call K w.env w.st ⟨a, τ, .activatePriorityMode⟩ = some s₁ ∧
    w.st.freezable Entry.activatePriorityMode.sel = true ∧
    Run K w ls w' ∧ (∀ l ∈ ls, l.runsCut = false) ∧ (∀ s', Label.foreign s' ∉ ls) ∧
    (∀ c, Label.call c ∈ ls → c.sender = w.st.chainTypeManager) ∧
    w'.st.priorityMode.activated = false ∧
    call K w'.env w'.st ⟨a, τ, .activatePriorityMode⟩ = none

/-- **THE PERMANENT-ROLLUP CONDITION IS THE FAILING ONE IN A REACHABLE STATE.** A run without cuts
from a chain with priority mode neither allowed nor active reaches a state in which priority mode
is allowed and inactive, `ActivationQueueReady` holds at `τ` (on its settlement layer; the first
unprocessed priority transaction was requested at `t ≠ 0` with `t + PRIORITY_EXPIRATION ≤ τ`; no
more batches executed than committed), the chain is on L1, the diamond is not frozen and the chain
is not a permanent rollup; `activatePriorityMode` at `τ` reverts there. By
`ActivatePriorityModeExact`, the condition that fails is the permanent-rollup one
(`Admin.sol:528-530`; `permanentlyAllowPriorityMode`, `Admin.sol:482-515`, has no such check). -/
def Properties.ActivationNeedsPermanentRollup : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label) (a : Address) (τ : ℕ),
    Run K w ls w' ∧ (∀ l ∈ ls, l.runsCut = false) ∧
    w.st.priorityMode.canBeActivated = false ∧ w.st.priorityMode.activated = false ∧
    w'.st.priorityMode.canBeActivated = true ∧ w'.st.priorityMode.activated = false ∧
    ActivationQueueReady w'.st τ ∧
    K.onL1 = true ∧ w'.st.frozen = false ∧
    w'.st.isPermanentRollup = false ∧
    call K w'.env w'.st ⟨a, τ, .activatePriorityMode⟩ = none

/-- **COUNTERMODEL: THE FILTERER GUARD IS LOAD-BEARING.** Without the `canBeActivated` check of
`setTransactionFilterer` (`Admin.sol:369-371`), the admin can, from a state satisfying
`Stage1Inv` with priority mode allowed, install a filterer other than governance's in one call,
breaking `Stage1Inv`; the real entry reverts there. -/
def Properties.UnguardedFiltererBreaksStage1 : Prop :=
  ∃ (K : Config) (e : Env) (s s' : State) (a : Address) (τ : ℕ),
    Stage1Inv s ∧ setTransactionFiltererWithoutGuard K s s.admin a = some s' ∧ ¬ Stage1Inv s' ∧
    call K e s ⟨s.admin, τ, .setTransactionFilterer a⟩ = none

/-- **COUNTERMODEL: THE L1-FILTERING GUARD IS LOAD-BEARING.** Without the check of
`setZKsyncOSL1TxFiltering` (`Admin.sol:191-193`), the admin can switch operator filtering of
priority transactions on after priority mode is allowed, breaking `Stage1Inv`; the real entry
reverts there. -/
def Properties.UnguardedL1FilteringBreaksStage1 : Prop :=
  ∃ (K : Config) (e : Env) (s s' : State) (τ : ℕ),
    Stage1Inv s ∧ setL1TxFilteringWithoutGuard s s.admin true = some s' ∧ ¬ Stage1Inv s' ∧
    call K e s ⟨s.admin, τ, .setZKsyncOSL1TxFiltering true⟩ = none

end Contracts.AdminFacet
