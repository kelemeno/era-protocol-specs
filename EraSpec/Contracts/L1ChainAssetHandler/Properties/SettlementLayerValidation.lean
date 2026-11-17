import EraSpec.Contracts.L1ChainAssetHandler.Specs.SettlementLayerValidation

-- Named propositions are transparent definitions; proofs reference these statements.
set_option linter.unusedVariables false

/-!
# Properties: `isValidSettlementLayer` against the layer that executed each batch

Statements about `EraSpec.Contracts.L1ChainAssetHandler.Specs.SettlementLayerValidation`
(era-contracts `draft/v0.35.0` at `b17415d20`); proofs are in
`EraSpec.Contracts.L1ChainAssetHandler.Proofs.SettlementLayerValidation`. No statement takes a hash
premise. "Reachable" below means: the end state of a `valRun` from a state satisfying
`ValInit`, in any environment `K` and world `W` unless the statement fixes them.

## The function

* With `migrationNumber ≤ 2` and an empty index-2 interval, the loop is the closed form
  `closedForm`, which reads interval 1 only; above 2 the call reverts (`IsValidUnrolled`).
* The head never reads index 0; `main`'s loop, which starts at 0, agrees with it when the index-0
  interval is uninitialized and can differ when it is not (`LegacyIndexZero`).

## Reachable states

* `migrationNumber ≤ 2`, so the call never reverts with `IteratedMigrationsNotSupported`
  (`ReachableNeverReverts`).
* The executed batches of `c`, over both of its diamonds, are exactly `1 .. total`
  (`ExecutedLogContiguous`), and a recorded batch is never rewritten later
  (`ExecutedBatchNeverRewritten`).
* **The exact answer for an executed batch** (`ExecutedBatchAnswer`, under `ValWorld.Ok`): the call
  accepts `(X, k)` iff `X` is the layer that executed the batch and, when that layer is not L1,
  `k` lies in interval 1's recorded window: at least the lower bound, and at most the upper
  bound once the interval is closed. Corollary: **sound** (`ExecutedBatchSound`, any
  environment).
* **The layer batch lies inside the window.** A batch executed on a settlement layer was executed
  under interval 1, after its `migrateToGWBatchNumber` and (once closed) by its
  `migrateFromGWBatchNumber`; with `sealedOnly` the lower bound is strictly below the first layer
  batch containing it; with `finalizedAfterExec` that batch is at most the upper bound once the
  chain is back (`SLBatchWithinBounds`).
* **Complete** in the real environment (`ExecutedBatchComplete`): the call accepts the executing
  layer with the first layer batch containing the batch, and with every later layer batch up to
  the upper bound (any later one while the interval is active).

## Failure and the head

* After a confirmed failed migration every claim naming L1 is accepted and every other claim
  rejected, for every batch (`FailureClassifiesAllOnL1`).
* With migrations disabled (the head, `CFG:320`), from any state, the classification state is
  unchanged or reset by one failure confirmation, so every accepted claim naming another layer
  was accepted at the start (`MigrationsDisabledOnlyHistoricalIntervals`); from a start state
  every batch executes on L1 and every answer names L1 (`MigrationsDisabledEveryBatchOnL1`).

## What the guarantees need (countermodels)

* Without `sealedOnly`, the first layer batch containing an executed batch can lie below the lower
  bound and be rejected (`CompletenessNeedsSealedOnly`).
* Without `finalizedAfterExec`, the upper bound can lie below every layer batch containing an
  executed batch, so no such claim is accepted (`CompletenessNeedsFinalizedAfterExec`).
* Without `ValWorld.Ok`, a layer with chain id 0 is read as an uninitialized interval and its
  batches are accepted as L1 batches (`SoundnessNeedsNonzeroLayerIds`).
* The lower bound is not tight: on the witness round trip the call accepts the claim of layer
  batch 1 (the lower bound) for batch 3, which was first contained in layer batch 2
  (`ClaimBelowFirstContainingBatchAccepted`). Rejecting such a claim is left to the inclusion
  proof that follows the call (`L1MR:111-119`), which this model does not include.

## Non-vacuity

`RoundTripWitness` meets every premise of the reachable-state results on a round trip L1 → layer
5 → L1 with batches on both layers and nonzero bounds; `FailedMigrationWitness` meets those of
`FailureClassifiesAllOnL1` and shows that the answer for a batch not yet executed changes when the
failure is confirmed; `MigrationsDisabledWitness` meets those of the two head results.
-/

namespace Contracts.L1ChainAssetHandler.SettlementLayerValidation

/-! ## The function -/

/-- **THE LOOP, UNROLLED.** For every L1 chain id, migration number `mn ≤ 2`, interval row whose
index-2 interval is uninitialized, batch, claimed layer and claimed layer batch,
`isValidSettlementLayer` returns `closedForm` of interval 1. For `mn > 2` it reverts. -/
def Properties.IsValidUnrolled : Prop :=
  (∀ (l1 mn : ℕ) (ivs : ℕ → MigInterval) (b X k : ℕ), mn ≤ 2 → (ivs 2).sl = 0 →
    isValidSettlementLayer l1 mn ivs b X k = some (closedForm l1 mn (ivs 1) b X k)) ∧
  ∀ (l1 mn : ℕ) (ivs : ℕ → MigInterval) (b X k : ℕ), 2 < mn →
    isValidSettlementLayer l1 mn ivs b X k = none

/-- **INDEX 0 AT THE HEAD AND AT MAIN.** (1) At the head the answer does not depend on the
index-0 interval: two rows that agree off index 0 give the same answer. (2) `main`'s loop, which
starts at index 0, gives the head's answer whenever the index-0 interval is uninitialized
(`settlementLayerChainId == 0`). (3) With a closed legacy interval at index 0 and migration number
0, `main` accepts a claim of the legacy layer that the head rejects. -/
def Properties.LegacyIndexZero : Prop :=
  (∀ (l1 mn : ℕ) (ivs ivs' : ℕ → MigInterval) (b X k : ℕ), (∀ i, i ≠ 0 → ivs i = ivs' i) →
    isValidSettlementLayer l1 mn ivs b X k = isValidSettlementLayer l1 mn ivs' b X k) ∧
  (∀ (l1 mn : ℕ) (ivs : ℕ → MigInterval) (b X k : ℕ), (ivs 0).sl = 0 →
    isValidSettlementLayerMain l1 mn ivs b X k = isValidSettlementLayer l1 mn ivs b X k) ∧
  ∃ (l1 : ℕ) (ivs : ℕ → MigInterval) (b X k : ℕ),
    (ivs 0).active = false ∧ (ivs 0).sl ≠ 0 ∧ X ≠ l1 ∧
    isValidSettlementLayerMain l1 0 ivs b X k = some true ∧
    isValidSettlementLayer l1 0 ivs b X k = some false

/-! ## Reachable states -/

/-- **NO REVERT ON A REACHABLE STATE.** In every environment and world, on every state a run from
a start state reaches, `migrationNumber[c] ≤ 2`, so `isValidSettlementLayer` returns for every
batch, claimed layer and claimed layer batch. -/
def Properties.ReachableNeverReverts : Prop :=
  ∀ (K : ValEnv) (W : ValWorld) (s0 s : ValState) (ls : List ValLabel),
    ValInit W s0 → valRun K W s0 ls = some s →
      s.mn ≤ maxMigrations ∧ ∀ b X k, (isValidAt W s b X k).isSome = true

/-- **THE EXECUTED LOG IS CONTIGUOUS.** In every environment and world, on every reachable
state, batch `b` of `c` has been executed (on L1 or on a settlement layer) iff
`1 ≤ b ≤ total`. -/
def Properties.ExecutedLogContiguous : Prop :=
  ∀ (K : ValEnv) (W : ValWorld) (s0 s : ValState) (ls : List ValLabel),
    ValInit W s0 → valRun K W s0 ls = some s →
      ∀ b, (s.hist b).isSome = true ↔ 1 ≤ b ∧ b ≤ s.total

/-- **AN EXECUTED BATCH IS NEVER REWRITTEN.** In every environment and world, if a run from a
start state reaches `s1` and a further run reaches `s2`, every batch recorded at `s1` has the
same record (layer and layer batch) at `s2`. -/
def Properties.ExecutedBatchNeverRewritten : Prop :=
  ∀ (K : ValEnv) (W : ValWorld) (s0 s1 s2 : ValState) (ls1 ls2 : List ValLabel),
    ValInit W s0 → valRun K W s0 ls1 = some s1 → valRun K W s1 ls2 = some s2 →
      ∀ b r, s1.hist b = some r → s2.hist b = some r

/-- **THE EXACT ANSWER FOR AN EXECUTED BATCH.** In every environment, in a world where chain id
0 is not whitelisted, on every reachable state, for every executed batch `b` with record `r`,
every claimed layer `X` and claimed layer batch `k`: `isValidSettlementLayer(c, b, X, k)` returns
`true` iff `X` is `r.layer` and, when `r.layer` is not L1, `k` is at least interval 1's lower bound
and, when interval 1 is closed, at most its upper bound; otherwise it returns `false`. -/
def Properties.ExecutedBatchAnswer : Prop :=
  ∀ (K : ValEnv) (W : ValWorld) (s0 s : ValState) (ls : List ValLabel),
    W.Ok → ValInit W s0 → valRun K W s0 ls = some s →
    ∀ b r, s.hist b = some r → ∀ X k,
      isValidAt W s b X k = some (decide (X = r.layer ∧
        (r.layer ≠ W.l1 → (s.ivs 1).lower ≤ k ∧ ((s.ivs 1).active = false → k ≤ (s.ivs 1).upper))))

/-- **SOUND FOR EXECUTED BATCHES.** In every environment, in a world where chain id 0 is not
whitelisted, on every reachable state: if `isValidSettlementLayer(c, b, X, k)` returns `true` for
an executed batch `b`, then `X` is the layer whose diamond executed `b`. -/
def Properties.ExecutedBatchSound : Prop :=
  ∀ (K : ValEnv) (W : ValWorld) (s0 s : ValState) (ls : List ValLabel),
    W.Ok → ValInit W s0 → valRun K W s0 ls = some s →
    ∀ b r X k, s.hist b = some r → isValidAt W s b X k = some true → X = r.layer

/-- **THE LAYER BATCH LIES INSIDE THE RECORDED WINDOW.** In every environment and world, on every
reachable state, for an executed batch `b` whose layer is not L1: the layer is interval 1's
settlement layer, `migrationNumber ≥ 1`, `b` is after interval 1's `migrateToGWBatchNumber` and,
once the interval is closed, at most its `migrateFromGWBatchNumber`. If L1 executes only sealed
layer batches (`sealedOnly`), the lower bound is strictly below the first layer batch containing
`b`. If the return is finalized only after the layer batch containing the burn was executed on
L1 (`finalizedAfterExec`) and the interval is closed, that first layer batch is at most the upper
bound. -/
def Properties.SLBatchWithinBounds : Prop :=
  ∀ (K : ValEnv) (W : ValWorld) (s0 s : ValState) (ls : List ValLabel),
    ValInit W s0 → valRun K W s0 ls = some s →
    ∀ b r, s.hist b = some r → r.layer ≠ W.l1 →
      r.layer = (s.ivs 1).sl ∧ 1 ≤ s.mn ∧ (s.ivs 1).toGW < b ∧
      ((s.ivs 1).active = false → b ≤ (s.ivs 1).fromGW) ∧
      (K.sealedOnly = true → (s.ivs 1).lower < r.slBatch) ∧
      (K.finalizedAfterExec = true → (s.ivs 1).active = false → r.slBatch ≤ (s.ivs 1).upper)

/-- **COMPLETE FOR EXECUTED BATCHES.** In the real environment, in a world where chain id 0 is not
whitelisted, on every reachable state, for every executed batch `b` with record `r`:
`isValidSettlementLayer(c, b, r.layer, r.slBatch)` returns `true`, and so does the claim of every
layer batch `k ≥ r.slBatch` that is at most the upper bound when interval 1 is closed. -/
def Properties.ExecutedBatchComplete : Prop :=
  ∀ (W : ValWorld) (s0 s : ValState) (ls : List ValLabel),
    W.Ok → ValInit W s0 → valRun ValEnv.real W s0 ls = some s →
    ∀ b r, s.hist b = some r →
      isValidAt W s b r.layer r.slBatch = some true ∧
      ∀ k, r.slBatch ≤ k → ((s.ivs 1).active = false → k ≤ (s.ivs 1).upper) →
        isValidAt W s b r.layer k = some true

/-! ## A failed migration and the head -/

/-- **A CONFIRMED FAILURE CLASSIFIES EVERY BATCH AS L1.** In every environment and world, from
any state, after a `confirmFailure` step that succeeds, `isValidSettlementLayer(c, b, X, k)`
returns whether `X` is L1, for every `b`, `X` and `k`. -/
def Properties.FailureClassifiesAllOnL1 : Prop :=
  ∀ (K : ValEnv) (W : ValWorld) (s s' : ValState), valStep K W s .confirmFailure = some s' →
    ∀ b X k, isValidAt W s' b X k = some (decide (X = W.l1))

/-- **WITH MIGRATIONS DISABLED, ONLY HISTORICAL INTERVALS ANSWER OFF L1.** In every environment,
in a world with migrations disabled (`CHAIN_MIGRATIONS_ENABLED = false`, as at `b17415d20`), along
any run from any state `s0`: either `migrationNumber[c]` and the interval row are those of `s0`,
or `s0` had `migrationNumber` 1 and the run confirmed a failure, leaving `migrationNumber` 0 and
interval 1 empty. Hence every claim naming a layer other than L1 that is accepted at the end was
accepted, with the same layer batch, at `s0`. -/
def Properties.MigrationsDisabledOnlyHistoricalIntervals : Prop :=
  ∀ (K : ValEnv) (W : ValWorld) (s0 s : ValState) (ls : List ValLabel),
    W.enabled = false → valRun K W s0 ls = some s →
      ((s.mn = s0.mn ∧ s.ivs = s0.ivs) ∨
        (s0.mn = 1 ∧ s.mn = 0 ∧ s.ivs = upd s0.ivs 1 MigInterval.empty)) ∧
      ∀ b X k, X ≠ W.l1 → isValidAt W s b X k = some true → isValidAt W s0 b X k = some true

/-- **WITH MIGRATIONS DISABLED, A CHAIN THAT NEVER LEFT STAYS ON L1.** In every environment, in a
world with migrations disabled, on every state a run from a start state reaches, every executed
batch was executed on L1 and `isValidSettlementLayer(c, b, X, k)` returns whether `X` is L1. -/
def Properties.MigrationsDisabledEveryBatchOnL1 : Prop :=
  ∀ (K : ValEnv) (W : ValWorld) (s0 s : ValState) (ls : List ValLabel),
    W.enabled = false → ValInit W s0 → valRun K W s0 ls = some s →
      (∀ b r, s.hist b = some r → r.layer = W.l1) ∧
      ∀ b X k, isValidAt W s b X k = some (decide (X = W.l1))

/-! ## Countermodels -/

/-- **COMPLETENESS NEEDS `sealedOnly`.** In the environment where L1 may execute a layer's batch
before it is sealed (and the return is finalized after execution), completeness at the first
containing layer batch fails: there are a world where chain id 0 is not whitelisted, a run from a
start state and an executed batch whose claim `(r.layer, r.slBatch)` is rejected. -/
def Properties.CompletenessNeedsSealedOnly : Prop :=
  ¬ ∀ (W : ValWorld) (s0 s : ValState) (ls : List ValLabel),
      W.Ok → ValInit W s0 → valRun ⟨false, true⟩ W s0 ls = some s →
      ∀ b r, s.hist b = some r → isValidAt W s b r.layer r.slBatch = some true

/-- **COMPLETENESS NEEDS `finalizedAfterExec`.** In the environment where the return may be
finalized before the layer batch containing the burn is executed on L1 (and L1 executes only
sealed layer batches), there are a world where chain id 0 is not whitelisted, a run from a start
state and an executed batch for which no claim of its layer with a layer batch at or after the
first one containing it is accepted. -/
def Properties.CompletenessNeedsFinalizedAfterExec : Prop :=
  ¬ ∀ (W : ValWorld) (s0 s : ValState) (ls : List ValLabel),
      W.Ok → ValInit W s0 → valRun ⟨true, false⟩ W s0 ls = some s →
      ∀ b r, s.hist b = some r → ∃ k, r.slBatch ≤ k ∧ isValidAt W s b r.layer k = some true

/-- **SOUNDNESS NEEDS NONZERO LAYER IDS.** Without `ValWorld.Ok`, soundness fails: in some
environment and world (one that whitelists chain 0), a run from a start state executes a batch on
layer 0 and `isValidSettlementLayer` accepts a claim naming a different layer (L1) for it. -/
def Properties.SoundnessNeedsNonzeroLayerIds : Prop :=
  ¬ ∀ (K : ValEnv) (W : ValWorld) (s0 s : ValState) (ls : List ValLabel),
      ValInit W s0 → valRun K W s0 ls = some s →
      ∀ b r X k, s.hist b = some r → isValidAt W s b X k = some true → X = r.layer

/-- **THE LOWER BOUND IS NOT TIGHT.** "Every accepted claim of the executing layer names a layer
batch at or after the first one containing the batch" fails in the real environment, in a world
where chain id 0 is not whitelisted: on the witness round trip, batch 3 was first contained in
layer batch 2 and the claim `(5, 1)` is accepted (the lower bound is 1). -/
def Properties.ClaimBelowFirstContainingBatchAccepted : Prop :=
  ¬ ∀ (W : ValWorld) (s0 s : ValState) (ls : List ValLabel),
      W.Ok → ValInit W s0 → valRun ValEnv.real W s0 ls = some s →
      ∀ b r k, s.hist b = some r → isValidAt W s b r.layer k = some true → r.slBatch ≤ k

/-! ## Witnesses -/

/-- **THE ROUND TRIP MEETS EVERY PREMISE.** The witness world is `Ok` and has migrations enabled,
the fresh state is a start state, and `wRoundTrip` runs in the real environment. At its end
`migrationNumber` is 2 and interval 1 is closed with `migrateToGW = 2`, `migrateFromGW = 4`,
bounds `[1, 3]` and layer 5; batches 1, 2 and 5 were executed on L1 and batches 3 and 4 on layer
5, in layer batches 2 and 3. The call accepts `(1, _)` for batches 1 and 5 and `(5, 2)`, `(5, 3)`
for batches 3 and 4, and rejects `(5, _)` for batches 1 and 5, `(1, _)` for batch 3 and `(5, 4)`
(above the upper bound) for batch 4. While `c` was on layer 5 (after the first seven steps) the
call accepted `(5, 7)` for batch 3: no upper bound applies to an active interval. -/
def Properties.RoundTripWitness : Prop :=
  wWorld.Ok ∧ wWorld.enabled = true ∧ ValInit wWorld wFresh ∧
  (∃ s, valRun ValEnv.real wWorld wFresh (wRoundTrip.take 7) = some s ∧
    (s.ivs 1).active = true ∧ s.hist 3 = some ⟨5, 2⟩ ∧ isValidAt wWorld s 3 5 7 = some true) ∧
  ∃ s, valRun ValEnv.real wWorld wFresh wRoundTrip = some s ∧
    s.mn = 2 ∧ s.ivs 1 = ⟨2, 4, 1, 3, 5, false⟩ ∧ s.total = 5 ∧
    s.hist 1 = some ⟨1, 0⟩ ∧ s.hist 2 = some ⟨1, 0⟩ ∧ s.hist 3 = some ⟨5, 2⟩ ∧
    s.hist 4 = some ⟨5, 3⟩ ∧ s.hist 5 = some ⟨1, 0⟩ ∧
    isValidAt wWorld s 1 1 0 = some true ∧ isValidAt wWorld s 1 5 2 = some false ∧
    isValidAt wWorld s 3 5 2 = some true ∧ isValidAt wWorld s 3 1 0 = some false ∧
    isValidAt wWorld s 4 5 3 = some true ∧ isValidAt wWorld s 4 5 4 = some false ∧
    isValidAt wWorld s 5 1 0 = some true ∧ isValidAt wWorld s 5 5 3 = some false

/-- **A FAILED MIGRATION.** From the fresh state in the witness world: batch 1 on L1, a burn to
layer 5 and the failure of its transaction. Before the confirmation the call accepts `(5, 1)` for
batch 2, which has not been executed; the confirmation step succeeds, batch 2 is then executed on
L1, `migrationNumber` is 0, and the call accepts `(1, 0)` and rejects `(5, 1)` for batch 2. -/
def Properties.FailedMigrationWitness : Prop :=
  ∃ s1 s2 s3, valRun ValEnv.real wWorld wFresh [.execL1 1, .burnL1 5, .failSL] = some s1 ∧
    isValidAt wWorld s1 2 5 1 = some true ∧
    valStep ValEnv.real wWorld s1 .confirmFailure = some s2 ∧
    valStep ValEnv.real wWorld s2 (.execL1 2) = some s3 ∧
    s3.mn = 0 ∧ s3.hist 2 = some ⟨1, 0⟩ ∧
    isValidAt wWorld s3 2 1 0 = some true ∧ isValidAt wWorld s3 2 5 1 = some false

/-- **MIGRATIONS DISABLED.** (1) From the end of the round trip, which holds a closed interval for
layer 5, a run in the world with migrations disabled executes batch 6 on L1 and advances layer 5;
the claim `(5, 2)` for batch 3 is accepted at both ends, and a new burn reverts. (2) From the
fresh state in that world, batch 1 executes on L1 and a burn reverts. (3) A migration in flight
when migrations are disabled: after a burn to layer 5 in the enabled world, the disabled world
fails its transaction and confirms the failure, which takes `migrationNumber` from 1 to 0. -/
def Properties.MigrationsDisabledWitness : Prop :=
  wWorldBanned.enabled = false ∧ ValInit wWorldBanned wFresh ∧
  (∃ s0 s, valRun ValEnv.real wWorld wFresh wRoundTrip = some s0 ∧
    valRun ValEnv.real wWorldBanned s0 [.execL1 6, .slSeal 5, .slExecL1 5] = some s ∧
    s.hist 6 = some ⟨1, 0⟩ ∧ isValidAt wWorldBanned s0 3 5 2 = some true ∧
    isValidAt wWorldBanned s 3 5 2 = some true ∧ valStep ValEnv.real wWorldBanned s (.burnL1 5) = none) ∧
  (∃ s, valRun ValEnv.real wWorldBanned wFresh [.execL1 1] = some s ∧ s.hist 1 = some ⟨1, 0⟩ ∧
    valStep ValEnv.real wWorldBanned s (.burnL1 5) = none) ∧
  ∃ s0 s, valRun ValEnv.real wWorld wFresh [.execL1 1, .burnL1 5] = some s0 ∧ s0.mn = 1 ∧
    valRun ValEnv.real wWorldBanned s0 [.failSL, .confirmFailure] = some s ∧ s.mn = 0

end Contracts.L1ChainAssetHandler.SettlementLayerValidation
