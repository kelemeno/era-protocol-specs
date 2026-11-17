import EraSpec.Contracts.AdminFacet.Specs.Mutants

/-!
# Properties: priority mode (the stage-1 escape hatch)

Statements about `EraSpec.Contracts.AdminFacet.Specs.AdminFacet`; proofs in
`EraSpec.Contracts.AdminFacet.Proofs.PriorityMode`.

* `Stage1InvHoldsAlongRuns` (run, headline): `Stage1Inv` holds on a fresh chain and is kept by
  every interleaving of calls, environment changes and foreign writes that runs no cut. While
  priority mode is active, it was allowed and the chain is a permanent rollup; once it is allowed,
  operator filtering of priority transactions is off and the transaction filterer is the one
  governance picked for priority mode.
* `OneWayFlagsAlongRuns` (run): without cuts, `isPermanentRollup`, `secondProofSystemRequired`
  and `canBeActivated` are never cleared, and once priority mode is allowed the fee parameters'
  pricing mode and three capacity fields never change.
* `ActivatePriorityModeExact`: `activatePriorityMode` succeeds, for any caller, exactly under its
  preconditions, and reverts every committed but unexecuted batch.
* `PriorityModeTogglesOnlyByItsEntries` (run): without cuts, priority mode turns on only by
  `activatePriorityMode` and off only by the CTM's `deactivatePriorityMode`.
* `PriorityModeWitness`: a concrete run from a fresh chain reaches active priority mode.
* Countermodels `UnguardedFiltererBreaksStage1`, `UnguardedL1FilteringBreaksStage1`: deleting
  either `NotCompatibleWithPriorityMode` check breaks `Stage1Inv` in one step.
-/

namespace Contracts.AdminFacet

/-- **HEADLINE: THE STAGE-1 INVARIANT HOLDS ALONG EVERY RUN WITHOUT CUTS.** A state where priority
mode is neither allowed nor active (every chain `DiamondInit` creates) satisfies `Stage1Inv`; and
every run that runs no cut — any calls by anyone at any times, environment changes, writes by the
other facets — keeps it. -/
def Properties.Stage1InvHoldsAlongRuns : Prop :=
  (∀ s : State, s.priorityMode.canBeActivated = false → s.priorityMode.activated = false →
      Stage1Inv s) ∧
  ∀ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' → (∀ l ∈ ls, l.runsCut = false) → Stage1Inv w.st → Stage1Inv w'.st

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
reverted batches. -/
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

/-- **WITNESS: PRIORITY MODE IS REACHABLE.** From a chain with priority mode neither allowed nor
active and not a permanent rollup, a run without cuts — a priority transaction enqueued by the
Mailbox, the admin's `makePermanentRollup` and `permanentlyAllowPriorityMode`, and an outsider's
`activatePriorityMode` four days later — ends with priority mode active. -/
def Properties.PriorityModeWitness : Prop :=
  ∃ (K : Config) (w w' : World) (ls : List Label),
    Run K w ls w' ∧ (∀ l ∈ ls, l.runsCut = false) ∧
    w.st.priorityMode.canBeActivated = false ∧ w.st.priorityMode.activated = false ∧
    w.st.isPermanentRollup = false ∧
    w'.st.priorityMode.activated = true ∧ Stage1Inv w'.st

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
