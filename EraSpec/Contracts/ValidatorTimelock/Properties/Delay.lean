import EraSpec.Contracts.ValidatorTimelock.Specs.Model

/-!
# Properties: the execution delay

Statements about `EraSpec.Contracts.ValidatorTimelock.Specs.Model` (source `b17415d20`).
Proofs are in `EraSpec.Contracts.ValidatorTimelock.Proofs.Delay`.

## What holds

* **An execute waits the enforced delay after the last commit** (`ExecutionWaitsForTheDelay`,
  headline). If batch `i` of chain `c` was last committed through the timelock at time `t`
  (before `2^32`, the year 2106), every later successful `executeBatchesSharedBridge` of a
  range of `c` containing `i` runs at `t + D` or later, where `D` is the delay enforced for `c`
  when the execute runs. Re-commits in between are allowed if their clocks are at least `t`
  and below `2^32` (`ExecutionWaitsForEveryEarlierCommit`).
* **Without an owner setter in between, the delay at commit time applies**
  (`ExecutionWaitsForTheCommitTimeDelay`). The enforced delay of every chain never falls along
  calls other than `initialize`, `setExecutionDelay` and `setChainExecutionDelay`
  (`EnforcedDelayGrowsWithoutAnOwnerSetter`). A successful `increaseChainExecutionDelay` by the
  chain's verified admin strictly raises the enforced delay of its chain and of no other
  (`IncreaseStrictlyRaisesItsChain`). Only the owner's two setters, `initialize` and the chain
  admin's increase write a delay (`DelayWriters`), and only commits write timestamps
  (`OnlyCommitsWriteTimestamps`: a revert does not clear them).
* **The delay is at most 30 days** (`BoundedRuns`: every delay stays at most
  `MAX_EXECUTION_DELAY` and every stored timestamp below `2^32`), so once every batch of a range
  has a stored timestamp at least 30 days old, the delay check cannot block an executor's call
  (`ExecuteNotBlockedAfterMaxDelay`); `MaxDelayIsAttained` shows the 30 days are reached.

## What does not hold

* **The owner can shorten a pending delay** (`OwnerCanShortenAPendingDelay`): between a commit
  and its execute the owner's `setExecutionDelay(0)` lets the execute run at the commit's own
  timestamp. `validators/interfaces/IValidatorTimelock.sol:92-103` documents that the owner sets
  both delays to any value up to the cap.
* **After `2^32` seconds the stored timestamp wraps** (`ClockPast2106SkipsTheDelay`): a commit
  at `2^32 + 1000` stores `1000`, and an execute at the same timestamp passes. `VT:297-298`
  states the contract is not meant to run until 2106.
* **A batch never committed through the timelock is not delayed** (`UnrecordedBatchIsNotDelayed`):
  its stored timestamp is `0`, so it executes once `now` reaches the delay itself. `VT:336-339`
  states this.
* **A re-commit at an earlier clock restarts the delay from that clock**
  (`RecommitAtAnEarlierClock`): the model's per-call clocks are unrelated, so the clock premise
  of `ExecutionWaitsForEveryEarlierCommit` is needed there.

## The checks are load-bearing

* `UncheckedExecuteRunsEarly`: without the `TimeNotReached` check an execute runs at its
  commit's timestamp.
* `UncheckedIncreaseLowersTheDelay`: without the comparison of `VT:141-144`, the chain admin
  lowers the enforced delay.
* `StoredComparisonAdmitsNoRaise`: comparing against the stored chain delay instead of the
  enforced one admits a successful increase that leaves the enforced delay unchanged.

## Witnesses

`ExecutionWaitsForTheDelayWitness` instantiates every premise of the two headline forms, with a
non-empty run between commit and execute that raises the delay from 100 to 200 seconds, and the
execute at exactly `t + 200`; `DelayBoundIsTight` shows an execute one second earlier reverts.
`RecommitWitness` instantiates `ExecutionWaitsForEveryEarlierCommit` with a revert and a
re-commit in between. `DelayWritersWitness` runs each delay writer. `MaxDelayIsAttained` instantiates
`ExecuteNotBlockedAfterMaxDelay` at a 30-day enforced delay.
-/

namespace Contracts.ValidatorTimelock

/-! ## The delay after a commit -/

/-- **HEADLINE: AN EXECUTE COMES AT LEAST THE ENFORCED DELAY AFTER THE LAST COMMIT.** Take a
successful commit through the timelock (`kc`) of a range containing batch `i` of chain `c`, at a
time `t = kc.env.now` below `2^32`; then a run of successful calls (`mid`) none of which commits
batch `i` of `c` again; then a successful `executeBatchesSharedBridge` (`ke`) of chain `c` over
a range containing `i`. Then `t + D ≤ ke.env.now`, where `D` is the delay enforced for `c` in
the state the execute runs on. Nothing else is assumed about the calls of `mid`; in particular
they may change `D`. -/
def Properties.ExecutionWaitsForTheDelay : Prop :=
  ∀ (s s₁ s₂ s₃ : State) (kc ke : Call) (mid : List Call) (c : Address) (i lo hi : ℕ),
    step kc s = some s₁ → Run s₁ mid s₂ → step ke s₂ = some s₃ →
    kc.action.commits c i → (∀ k ∈ mid, ¬ k.action.commits c i) →
    ke.action = .executeBatches c lo hi → lo ≤ i → i ≤ hi → kc.env.now < UINT32 →
    kc.env.now + enforcedDelay s₂ c ≤ ke.env.now

/-- **WITHOUT AN OWNER SETTER IN BETWEEN, THE DELAY AT COMMIT TIME APPLIES.** As
`ExecutionWaitsForTheDelay`, where in addition no call of `mid` is `initialize`,
`setExecutionDelay` or `setChainExecutionDelay` (`Action.mayLowerDelay`). Then
`t + D₀ ≤ ke.env.now`, where `D₀` is the delay enforced for `c` in the state the commit runs
on. -/
def Properties.ExecutionWaitsForTheCommitTimeDelay : Prop :=
  ∀ (s s₁ s₂ s₃ : State) (kc ke : Call) (mid : List Call) (c : Address) (i lo hi : ℕ),
    step kc s = some s₁ → Run s₁ mid s₂ → step ke s₂ = some s₃ →
    kc.action.commits c i → (∀ k ∈ mid, ¬ k.action.commits c i) →
    (∀ k ∈ mid, ¬ k.action.mayLowerDelay) →
    ke.action = .executeBatches c lo hi → lo ≤ i → i ≤ hi → kc.env.now < UINT32 →
    kc.env.now + enforcedDelay s c ≤ ke.env.now

/-- **WITH CLOCKS THAT DO NOT GO BACK, AN EXECUTE WAITS FOR EVERY EARLIER COMMIT.** As
`ExecutionWaitsForTheDelay`, but the calls of `mid` may commit batch `i` of `c` again (after a
revert, say), provided each such re-commit runs at a time at least `t` and below `2^32`. Then
still `t + D ≤ ke.env.now`. With no re-commit in `mid` this is `ExecutionWaitsForTheDelay`. -/
def Properties.ExecutionWaitsForEveryEarlierCommit : Prop :=
  ∀ (s s₁ s₂ s₃ : State) (kc ke : Call) (mid : List Call) (c : Address) (i lo hi : ℕ),
    step kc s = some s₁ → Run s₁ mid s₂ → step ke s₂ = some s₃ →
    kc.action.commits c i →
    (∀ k ∈ mid, k.action.commits c i → kc.env.now ≤ k.env.now ∧ k.env.now < UINT32) →
    ke.action = .executeBatches c lo hi → lo ≤ i → i ≤ hi → kc.env.now < UINT32 →
    kc.env.now + enforcedDelay s₂ c ≤ ke.env.now

/-- **ONLY COMMITS WRITE TIMESTAMPS.** A successful call that is not a commit through the
timelock of a range containing batch `i` of chain `c` leaves `committedAt c i` unchanged (so a
revert, prove or execute does not clear it); a successful commit of such a range sets it to
`now % 2^32`. -/
def Properties.OnlyCommitsWriteTimestamps : Prop :=
  ∀ (k : Call) (s s' : State) (c : Address) (i : ℕ), step k s = some s' →
    (¬ k.action.commits c i → s'.committedAt c i = s.committedAt c i) ∧
    (k.action.commits c i → s'.committedAt c i = k.env.now % UINT32)

/-! ## Who moves the delay -/

/-- **THE ENFORCED DELAY NEVER FALLS WITHOUT AN OWNER SETTER.** Along any run of successful
calls none of which is `initialize`, `setExecutionDelay` or `setChainExecutionDelay`, the
delay enforced for every chain at the end is at least the one at the start. -/
def Properties.EnforcedDelayGrowsWithoutAnOwnerSetter : Prop :=
  ∀ (s s' : State) (ks : List Call), Run s ks s' → (∀ k ∈ ks, ¬ k.action.mayLowerDelay) →
    ∀ c, enforcedDelay s c ≤ enforcedDelay s' c

/-- **A CHAIN ADMIN'S INCREASE STRICTLY RAISES ITS CHAIN'S DELAY, AND ONLY ITS CHAIN'S.** If
`increaseChainExecutionDelay(c, d)` succeeds, the caller is `c`'s verified admin, the delay
enforced for `c` rises strictly, to `d`, the ecosystem-wide delay is unchanged, and so is the
chain delay of every other chain. -/
def Properties.IncreaseStrictlyRaisesItsChain : Prop :=
  ∀ (e : Env) (x c : Address) (d : ℕ) (s s' : State),
    step ⟨e, x, .increaseChainExecutionDelay c d⟩ s = some s' →
    chainAdmin e c = some x ∧ enforcedDelay s c < enforcedDelay s' c ∧ enforcedDelay s' c = d ∧
      s'.executionDelay = s.executionDelay ∧ ∀ c', c' ≠ c → s'.chainDelay c' = s.chainDelay c'

/-- **WHO WRITES A DELAY.** If a successful call changes the ecosystem-wide delay, it is the
owner's `setExecutionDelay` or `initialize` on uninitialized storage. If it changes chain `c`'s
delay, it is the owner's `setChainExecutionDelay(c, _)` or `increaseChainExecutionDelay(c, d)`
by `c`'s verified admin with `d` above the delay enforced for `c`. -/
def Properties.DelayWriters : Prop :=
  ∀ (k : Call) (s s' : State), step k s = some s' →
    (s'.executionDelay ≠ s.executionDelay →
      (∃ d, k.action = .setExecutionDelay d ∧ k.sender = s.owner) ∨
      (∃ o d, k.action = .initializeTimelock o d ∧ s.initialized = false)) ∧
    (∀ c, s'.chainDelay c ≠ s.chainDelay c →
      (∃ d, k.action = .setChainExecutionDelay c d ∧ k.sender = s.owner) ∨
      (∃ d, k.action = .increaseChainExecutionDelay c d ∧ chainAdmin k.env c = some k.sender ∧
        enforcedDelay s c < d))

/-! ## The 30-day bound -/

/-- **EVERY DELAY STAYS AT MOST 30 DAYS AND EVERY TIMESTAMP FITS A `uint32`.** Fresh storage is
`Bounded`, and every run of successful calls from a `Bounded` state ends in one. -/
def Properties.BoundedRuns : Prop :=
  Bounded init ∧ ∀ (s s' : State) (ks : List Call), Bounded s → Run s ks s' → Bounded s'

/-- **THE DELAY CHECK CANNOT BLOCK AFTER 30 DAYS.** In a `Bounded` state, let the caller be a
member of `EXECUTOR_ROLE` of chain `c`, the range valid and the forwarded call successful. If
every batch of the range has a stored timestamp at least `MAX_EXECUTION_DELAY` (30 days)
before `now`, the execute succeeds. -/
def Properties.ExecuteNotBlockedAfterMaxDelay : Prop :=
  ∀ (s : State) (e : Env) (x c : Address) (lo hi : ℕ), Bounded s →
    s.members c EXECUTOR_ROLE x = true → validRange lo hi → e.forwardOk = true →
    (∀ i, lo ≤ i → i ≤ hi → s.committedAt c i + MAX_EXECUTION_DELAY ≤ e.now) →
    step ⟨e, x, .executeBatches c lo hi⟩ s = some s

/-! ## Boundaries -/

/-- **THE OWNER CAN SHORTEN A PENDING DELAY.** After the witness setup (delay 100 seconds),
validator `3` commits batch `1` of chain `100` at time `1000`; the owner then calls
`setExecutionDelay(0)`; the execute of batch `1` succeeds at time `1000`, earlier than the
commit time plus the delay enforced at commit. So the `mayLowerDelay` premise of
`ExecutionWaitsForTheCommitTimeDelay` cannot be dropped. -/
def Properties.OwnerCanShortenAPendingDelay : Prop :=
  ∃ s₀ s₁ s₂ s₃ : State,
    Run init vtSetupCalls s₀ ∧
    step (vtCall 1000 vtValidator (.commitBatches vtChain 1 1)) s₀ = some s₁ ∧
    Run s₁ [vtCall 1000 vtOwner (.setExecutionDelay 0)] s₂ ∧
    step (vtCall 1000 vtValidator (.executeBatches vtChain 1 1)) s₂ = some s₃ ∧
    (Action.setExecutionDelay 0).mayLowerDelay ∧
    (1000 : ℕ) < 1000 + enforcedDelay s₀ vtChain

/-- **AFTER `2^32` SECONDS THE DELAY IS SKIPPED.** After the witness setup (delay 100 seconds),
validator `3` commits batch `1` of chain `100` at time `2^32 + 1000` and executes it at the same
time: both succeed, though the execute comes before the commit time plus the enforced delay.
So the `kc.env.now < UINT32` premise of `ExecutionWaitsForTheDelay` cannot be dropped. -/
def Properties.ClockPast2106SkipsTheDelay : Prop :=
  ∃ s₀ s₁ s₂ : State,
    Run init vtSetupCalls s₀ ∧
    step (vtCall (UINT32 + 1000) vtValidator (.commitBatches vtChain 1 1)) s₀ = some s₁ ∧
    step (vtCall (UINT32 + 1000) vtValidator (.executeBatches vtChain 1 1)) s₁ = some s₂ ∧
    s₁.committedAt vtChain 1 = 1000 ∧
    UINT32 + 1000 < UINT32 + 1000 + enforcedDelay s₁ vtChain

/-- **A RE-COMMIT AT AN EARLIER CLOCK RESTARTS THE DELAY FROM THAT CLOCK.** After the witness
setup (delay 100 seconds), batch `1` of chain `100` is committed at time `1000`, then committed
again by a call whose clock reads `500`, and executed at `600`: all three succeed, and
`600 < 1000 + 100`. The model's clocks are per call and unrelated; this shows the clock premise
of `ExecutionWaitsForEveryEarlierCommit` is needed in the model. -/
def Properties.RecommitAtAnEarlierClock : Prop :=
  ∃ s₀ s₁ s₂ s₃ : State,
    Run init vtSetupCalls s₀ ∧
    step (vtCall 1000 vtValidator (.commitBatches vtChain 1 1)) s₀ = some s₁ ∧
    Run s₁ [vtCall 500 vtValidator (.commitBatches vtChain 1 1)] s₂ ∧
    step (vtCall 600 vtValidator (.executeBatches vtChain 1 1)) s₂ = some s₃ ∧
    enforcedDelay s₂ vtChain = 100 ∧ (600 : ℕ) < 1000 + enforcedDelay s₂ vtChain

/-- **A BATCH NEVER COMMITTED THROUGH THE TIMELOCK IS NOT DELAYED.** After the witness setup
(delay 100 seconds, no commit), batch `7` of chain `100` has stored timestamp `0`, and its
execute by validator `3` succeeds at time `100`. -/
def Properties.UnrecordedBatchIsNotDelayed : Prop :=
  ∃ s₀ s₁ : State,
    Run init vtSetupCalls s₀ ∧ s₀.committedAt vtChain 7 = 0 ∧ enforcedDelay s₀ vtChain = 100 ∧
    step (vtCall 100 vtValidator (.executeBatches vtChain 7 7)) s₀ = some s₁

/-! ## The checks are load-bearing -/

/-- **WITHOUT THE `TimeNotReached` CHECK, AN EXECUTE RUNS AT ITS COMMIT'S TIMESTAMP.** After
the witness setup and a commit of batch `1` of chain `100` at time `1000`,
`executeBatchesUnchecked` succeeds at time `1000`; the deployed execute reverts there. -/
def Properties.UncheckedExecuteRunsEarly : Prop :=
  ∃ s₀ s₁ : State,
    Run init vtSetupCalls s₀ ∧
    step (vtCall 1000 vtValidator (.commitBatches vtChain 1 1)) s₀ = some s₁ ∧
    executeBatchesUnchecked (vtEnv 1000) vtValidator vtChain 1 1 s₁ = some s₁ ∧
    step (vtCall 1000 vtValidator (.executeBatches vtChain 1 1)) s₁ = none ∧
    enforcedDelay s₁ vtChain = 100

/-- **WITHOUT THE COMPARISON, THE CHAIN ADMIN LOWERS THE DELAY.** After the witness setup and
the chain admin's `increaseChainExecutionDelay(100, 300)`, `increaseChainExecutionDelayUnchecked`
with `150` succeeds and lowers the delay enforced for chain `100` from `300` to `150`; the
deployed call reverts there. -/
def Properties.UncheckedIncreaseLowersTheDelay : Prop :=
  ∃ s₀ s₁ s₂ : State,
    Run init vtSetupCalls s₀ ∧
    step (vtCall 1 vtAdmin (.increaseChainExecutionDelay vtChain 300)) s₀ = some s₁ ∧
    increaseChainExecutionDelayUnchecked (vtEnv 2) vtAdmin vtChain 150 s₁ = some s₂ ∧
    enforcedDelay s₁ vtChain = 300 ∧ enforcedDelay s₂ vtChain = 150 ∧
    step (vtCall 2 vtAdmin (.increaseChainExecutionDelay vtChain 150)) s₁ = none

/-- **COMPARING AGAINST THE STORED DELAY ADMITS AN INCREASE THAT RAISES NOTHING.** After the
witness setup (ecosystem delay 100, chain delay 0), `increaseChainExecutionDelayStored` with
`50` succeeds and sets the chain delay to `50`, while the delay enforced for chain `100` stays
`100`; the deployed call reverts there. -/
def Properties.StoredComparisonAdmitsNoRaise : Prop :=
  ∃ s₀ s₁ : State,
    Run init vtSetupCalls s₀ ∧
    increaseChainExecutionDelayStored (vtEnv 1) vtAdmin vtChain 50 s₀ = some s₁ ∧
    s₁.chainDelay vtChain = 50 ∧ enforcedDelay s₀ vtChain = 100 ∧
    enforcedDelay s₁ vtChain = 100 ∧
    step (vtCall 1 vtAdmin (.increaseChainExecutionDelay vtChain 50)) s₀ = none

/-! ## Witnesses -/

/-- **THE HEADLINE PREMISES ARE SATISFIABLE.** After the witness setup, every premise of
`ExecutionWaitsForTheDelay` and `ExecutionWaitsForTheCommitTimeDelay` holds for batch `2`
with `vtDelayCommit`, `vtDelayMid` and `vtDelayExecute`. The run between them is non-empty,
contains no owner setter, and raises the enforced delay from `100` (at commit) to `200` (at
execute), and the execute comes exactly `200` seconds after the commit. -/
def Properties.ExecutionWaitsForTheDelayWitness : Prop :=
  ∃ s₀ s₁ s₂ s₃ : State,
    Run init vtSetupCalls s₀ ∧ step vtDelayCommit s₀ = some s₁ ∧ Run s₁ vtDelayMid s₂ ∧
    step vtDelayExecute s₂ = some s₃ ∧
    vtDelayCommit.action.commits vtChain 2 ∧ (∀ k ∈ vtDelayMid, ¬ k.action.commits vtChain 2) ∧
    (∀ k ∈ vtDelayMid, ¬ k.action.mayLowerDelay) ∧
    vtDelayExecute.action = .executeBatches vtChain 1 3 ∧ vtDelayCommit.env.now < UINT32 ∧
    enforcedDelay s₀ vtChain = 100 ∧ enforcedDelay s₁ vtChain = 100 ∧
    enforcedDelay s₂ vtChain = 200 ∧
    vtDelayCommit.env.now + enforcedDelay s₂ vtChain = vtDelayExecute.env.now

/-- **RE-COMMITS ARE COVERED.** After the witness setup, batches `1 … 3` of chain `100` are
committed at `1000`, reverted at `1010` (the timestamps stay), committed again at `1020`, and
executed at `1120`. Every premise of `ExecutionWaitsForEveryEarlierCommit` holds for batch `2`
and the first commit, with a re-commit of batch `2` in the run between, and the execute comes
`120` seconds after the first commit, which is at least the enforced delay of `100`. -/
def Properties.RecommitWitness : Prop :=
  ∃ s₀ s₁ s₂ s₃ : State,
    Run init vtSetupCalls s₀ ∧
    step (vtCall 1000 vtValidator (.commitBatches vtChain 1 3)) s₀ = some s₁ ∧
    Run s₁ [vtCall 1010 vtValidator (.revertBatches vtChain),
            vtCall 1020 vtValidator (.commitBatches vtChain 1 3)] s₂ ∧
    step (vtCall 1120 vtValidator (.executeBatches vtChain 1 3)) s₂ = some s₃ ∧
    (Action.commitBatches vtChain 1 3).commits vtChain 2 ∧
    (1000 : ℕ) ≤ 1020 ∧ (1020 : ℕ) < UINT32 ∧ (1000 : ℕ) < UINT32 ∧
    enforcedDelay s₂ vtChain = 100 ∧ s₂.committedAt vtChain 2 = 1020

/-- **THE BOUND IS TIGHT, AT THE DELAY IN FORCE AT EXECUTION.** In the state the delay
witness's execute runs on, the same execute one second earlier (time `1199`, already more than
the commit-time delay of `100` seconds after the commit) reverts. -/
def Properties.DelayBoundIsTight : Prop :=
  ∃ s₀ s₁ s₂ : State,
    Run init vtSetupCalls s₀ ∧ step vtDelayCommit s₀ = some s₁ ∧ Run s₁ vtDelayMid s₂ ∧
    step (vtCall 1199 vtValidator (.executeBatches vtChain 1 3)) s₂ = none ∧
    1000 + 100 < 1199

/-- **EVERY DELAY WRITER RUNS.** After the witness setup (whose `initialize` set the ecosystem
delay from `0` to `100`), the owner's `setExecutionDelay(50)`, the chain admin's
`increaseChainExecutionDelay(100, 200)` and the owner's `setChainExecutionDelay(100, 10)` all
succeed, each changing the delay it writes; the delay enforced for chain `100` goes
`100 → 50 → 200 → 50`. -/
def Properties.DelayWritersWitness : Prop :=
  ∃ s₀ s₁ s₂ s₃ : State,
    Run init vtSetupCalls s₀ ∧ s₀.executionDelay = 100 ∧
    step (vtCall 1 vtOwner (.setExecutionDelay 50)) s₀ = some s₁ ∧
    step (vtCall 2 vtAdmin (.increaseChainExecutionDelay vtChain 200)) s₁ = some s₂ ∧
    step (vtCall 3 vtOwner (.setChainExecutionDelay vtChain 10)) s₂ = some s₃ ∧
    s₁.executionDelay = 50 ∧ s₂.chainDelay vtChain = 200 ∧ s₃.chainDelay vtChain = 10 ∧
    enforcedDelay s₀ vtChain = 100 ∧ enforcedDelay s₁ vtChain = 50 ∧
    enforcedDelay s₂ vtChain = 200 ∧ enforcedDelay s₃ vtChain = 50

/-- **THE 30 DAYS ARE REACHED.** After the witness setup, the chain admin raises chain `100`'s
delay to `MAX_EXECUTION_DELAY` and validator `3` commits batch `1` at time `1000`. In that
(`Bounded`) state the execute succeeds at `1000 + MAX_EXECUTION_DELAY` and reverts one second
earlier. -/
def Properties.MaxDelayIsAttained : Prop :=
  ∃ s₀ s₁ : State,
    Run init vtSetupCalls s₀ ∧
    Run s₀ [vtCall 1 vtAdmin (.increaseChainExecutionDelay vtChain MAX_EXECUTION_DELAY),
            vtCall 1000 vtValidator (.commitBatches vtChain 1 1)] s₁ ∧
    Bounded s₁ ∧ enforcedDelay s₁ vtChain = MAX_EXECUTION_DELAY ∧
    s₁.members vtChain EXECUTOR_ROLE vtValidator = true ∧ s₁.committedAt vtChain 1 = 1000 ∧
    step (vtCall (1000 + MAX_EXECUTION_DELAY) vtValidator (.executeBatches vtChain 1 1)) s₁ =
      some s₁ ∧
    step (vtCall (1000 + MAX_EXECUTION_DELAY - 1) vtValidator (.executeBatches vtChain 1 1)) s₁ =
      none

end Contracts.ValidatorTimelock
