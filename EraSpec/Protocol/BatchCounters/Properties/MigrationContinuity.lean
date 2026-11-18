import EraSpec.Protocol.BatchCounters.Specs.MigrationContinuity

/-!
# Properties: batch counters across migration

Statements about `EraSpec.Protocol.BatchCounters.Specs.MigrationContinuity` (source `b17415d20`,
latent there because migrations are disabled). Proofs are in
`EraSpec.Protocol.BatchCounters.Proofs.MigrationContinuity`.

* **Mint data.** A burn of a synced chain produces consistent data: the batch number equals
  the commitment's executed count, every committed batch is executed, and the commitment
  carries the one stored hash of the last executed batch (`BurnDataConsistent`). The mint
  checks the commitment's own shape and the message root's `<=`, and does not compare the
  commitment's counters or hashes with the diamond it overwrites (`StaleMintRewritesHistory`:
  data whose batch number passes the message root's check but whose commitment is stale lowers
  `totalBatchesExecuted` from 10 to 5, rewrites `storedBatchHashes[7]` and `[10]`, and leaves
  the chain unable to execute). With consistent data and synced counters the message root's
  `<=` check is enough: the executed count never goes down and no stored hash below it is
  rewritten (`ConsistentMintNeverLowersExecuted`).
* **Two copies.** Along every run of the two-layer system from a state satisfying `TwoInv`
  (`TwoInvInit` gives one), `TwoInv` holds (`TwoRunKeepsInv`): in particular exactly one copy
  of the chain settles or a migration is in flight (`ExactlyOneCopySettles`); pipeline steps
  happen only on the settling copy (`PipelineOnlyOnSettlingCopy`); an idle copy, and its
  message-root counter, change only by an arrival on its layer, except that a failure
  confirmation clears L1's copy's `away` flag (`IdleCopyChangesOnlyByMint`).
* **Continuity.** An arrival gives the destination copy counters all equal to the source's
  executed count `E`, the source's stored hash of batch `E` and no other stored hash, the
  source's upgrade-transaction fields, and a message-root counter at `E`
  (`ArrivalOnL1CopiesSource`, `ArrivalOnSLCopiesSource`). The batch numbers the chain executes
  over a run, on both layers together, are exactly the next ones after its executed count, in
  order (`ExecutedLogContiguous`), and neither copy's executed count ever goes down
  (`CopiesNeverGoBack`). An honest arrival always passes the checks the model keeps
  (`HonestArrivalsAccepted`), including `setMigratingChainBatchNumber`'s `<=`
  (`MessageRootBase.sol:154-155`).

## Witnesses

| Witness | Premises it meets |
|---|---|
| `RoundTripWitness` | `TwoInvInit` (an L1 copy with one batch executed, reached from the empty layer); runs of `TwoInv` states with departures from both layers, an arrival on a fresh settlement-layer diamond and an arrival back on L1, and pipeline steps of `C` on both layers (`TwoStepPreservesInv`, `TwoRunKeepsInv`, `ExactlyOneCopySettles`, `PipelineOnlyOnSettlingCopy`, `ExecutedLogContiguous`, `CopiesNeverGoBack`); an idle L1 copy while the settlement layer runs (`IdleCopyChangesOnlyByMint`); flights in both directions, towards a layer without a diamond (`HonestArrivalsAccepted`, `ArrivalOnL1CopiesSource` with the L1 copy behind the source, 1 < 3, `ArrivalOnSLCopiesSource` for a fresh diamond); a burn of a synced chain on each layer (`BurnDataConsistent`) and a consistent mint onto an existing diamond on L1 (`ConsistentMintNeverLowersExecuted`) |
| `ReentryWitness` | the same run continued: a failure confirmation from a `TwoInv` state whose L1 copy is away with 4 batches executed (`IdleCopyChangesOnlyByMint` for the cleared flag); an arrival on an existing settlement-layer diamond that is behind the data in flight, 3 < 4 (`ArrivalOnSLCopiesSource` for an existing diamond, the existing-diamond case of `HonestArrivalsAccepted`, `ConsistentMintNeverLowersExecuted` on the settlement layer) |

`StaleMintRewritesHistory` is a countermodel and needs no witness.
-/

namespace Contracts.BatchCounters

/-! ## Mint data on one layer -/

/-- **BURN DATA IS CONSISTENT.** If chain `c`'s counters agree, the data of a burn of `c` has
batch number equal to the commitment's `totalBatchesExecuted`, all three counters equal, the
shape `forwardedBridgeMint` checks, and exactly one batch hash: the diamond's stored hash of its
last executed batch. -/
def Properties.BurnDataConsistent : Prop :=
  ∀ (cfg : HubConfig) (h h' : Hub) (c : ChainId) (bn : ℕ) (com : Commitment),
    HubStep cfg h (.burn c bn com) h' → Synced h c →
    bn = com.executed ∧ com.committed = com.executed ∧ com.verified = com.executed ∧
      MintShape com ∧ ∃ d, h.chains c = some d ∧ com.batchHashes = [d.batchHash d.executed]

/-- **A CONSISTENT MINT NEVER LOWERS THE EXECUTED COUNT.** If chain `c`'s counters agree and a
mint of `c` onto its existing diamond `d` carries consistent data, the new diamond has executed
at least as many batches as `d`, and every stored hash of a batch below `d`'s executed count is
unchanged. -/
def Properties.ConsistentMintNeverLowersExecuted : Prop :=
  ∀ (cfg : HubConfig) (h h' : Hub) (c : ChainId) (bn : ℕ) (com : Commitment) (d : Diamond),
    HubStep cfg h (.mintExisting c bn com) h' → bn = com.executed → Synced h c →
    h.chains c = some d →
    ∃ d', h'.chains c = some d' ∧ d.executed ≤ d'.executed ∧
      ∀ n < d.executed, d'.batchHash n = d.batchHash n

/-- **A STALE COMMITMENT REWRITES HISTORY (countermodel).** `wAwayHub` (L1, migrations enabled)
satisfies the invariant, and its chain `1` — away, ten batches executed — is synced. The mint
data with batch number `10` and the commitment `wStaleCom` (executed `5`, committed `10`) has
the shape `forwardedBridgeMint` checks and passes the message root's check, so the mint step
exists. Afterwards the diamond has executed `5` batches, its stored hashes of batches 7 and 10
differ from before, the message-root counter is `10`, and no execute of chain `1` exists. -/
def Properties.StaleMintRewritesHistory : Prop :=
  HubInv wAwayHub ∧ Synced wAwayHub 1 ∧ MintShape wStaleCom ∧
    ∃ h', HubStep latentL1 wAwayHub (.mintExisting 1 10 wStaleCom) h' ∧
      ∃ d', h'.chains 1 = some d' ∧ d'.executed = 5 ∧
        d'.batchHash 7 ≠ wAwayDiamond.batchHash 7 ∧ d'.batchHash 10 ≠ wAwayDiamond.batchHash 10 ∧
        h'.mr.cur 1 = 10 ∧ ∀ (infos : List BatchInfo) (h'' : Hub), ¬ HubStep latentL1 h' (.execute 1 infos) h''

/-! ## The two-layer invariant -/

/-- **WHERE THE SYSTEM STARTS.** Two layers satisfying the layer invariant, the chain synced and
settling on L1, no diamond for it on the settlement layer and nothing in flight satisfy
`TwoInv`. -/
def Properties.TwoInvInit : Prop :=
  ∀ (P : TwoConfig) (s : TwoHubs), HubInv s.l1 → HubInv s.sl → Synced s.l1 P.C →
    Settles s.l1 P.C → s.sl.chains P.C = none → s.flight = none → TwoInv P s

/-- **EVERY STEP PRESERVES `TwoInv`.** -/
def Properties.TwoStepPreservesInv : Prop :=
  ∀ (P : TwoConfig) (s s' : TwoHubs) (l : TwoLabel), TwoInv P s → TwoStep P s l s' → TwoInv P s'

/-- **EVERY RUN PRESERVES `TwoInv`.** -/
def Properties.TwoRunKeepsInv : Prop :=
  ∀ (P : TwoConfig) (s s' : TwoHubs) (ls : List TwoLabel), TwoInv P s → TwoRun P s ls s' →
    TwoInv P s'

/-- **EXACTLY ONE COPY SETTLES, OR A MIGRATION IS IN FLIGHT.** Along any run from a state
satisfying `TwoInv`: the two copies never both settle, and nothing is in flight exactly when
one of them settles. -/
def Properties.ExactlyOneCopySettles : Prop :=
  ∀ (P : TwoConfig) (s s' : TwoHubs) (ls : List TwoLabel), TwoInv P s → TwoRun P s ls s' →
    (Settles s'.l1 P.C → ¬ Settles s'.sl P.C) ∧
      (s'.flight = none ↔ Settles s'.l1 P.C ∨ Settles s'.sl P.C)

/-- **PIPELINE STEPS HAPPEN ONLY ON THE SETTLING COPY.** In a state satisfying `TwoInv`, a
commit, prove, execute or revert of `C` on a layer requires `C` to settle on that layer, nothing
to be in flight, and the other copy to be idle. -/
def Properties.PipelineOnlyOnSettlingCopy : Prop :=
  ∀ (P : TwoConfig) (s s' : TwoHubs) (l : HubLabel), TwoInv P s → l.chain = P.C →
    l.isPipeline = true →
    (TwoStep P s (.l1 l) s' → Settles s.l1 P.C ∧ s.flight = none ∧ Idle s.sl P.C) ∧
      (TwoStep P s (.sl l) s' → Settles s.sl P.C ∧ s.flight = none ∧ Idle s.l1 P.C)

/-- **AN IDLE COPY CHANGES ONLY BY AN ARRIVAL.** In a state satisfying `TwoInv`, if `C`'s
diamond `d` on a layer is away, every step other than an arrival on that layer leaves a diamond
equal to `d` except possibly for the `away` flag, and leaves that layer's message-root counter
for `C` unchanged. -/
def Properties.IdleCopyChangesOnlyByMint : Prop :=
  ∀ (P : TwoConfig) (s s' : TwoHubs) (l : TwoLabel), TwoInv P s → TwoStep P s l s' →
    (l ≠ .arriveL1 → ∀ d, s.l1.chains P.C = some d → d.away = true →
      ∃ d', s'.l1.chains P.C = some d' ∧ { d' with away := true } = d ∧
        s'.l1.mr.cur P.C = s.l1.mr.cur P.C) ∧
    (l ≠ .arriveSLExisting → (∀ gh gr, l ≠ .arriveSLNew gh gr) →
      ∀ d, s.sl.chains P.C = some d → d.away = true →
        ∃ d', s'.sl.chains P.C = some d' ∧ { d' with away := true } = d ∧
          s'.sl.mr.cur P.C = s.sl.mr.cur P.C)

/-! ## Continuity -/

/-- **ARRIVING ON L1 COPIES THE DEPARTED COPY.** In a state satisfying `TwoInv`, the arrival on
L1 turns L1's diamond `d` into `d'` whose three counters equal the settlement-layer copy's
executed count `E`, whose stored hash of batch `E` is that copy's, whose other stored hashes
and logs roots are `d`'s, whose upgrade-transaction fields are that copy's, and which settles;
L1's message-root counter becomes `E`; and `E` is at least `d`'s executed count. -/
def Properties.ArrivalOnL1CopiesSource : Prop :=
  ∀ (P : TwoConfig) (s s' : TwoHubs), TwoInv P s → TwoStep P s .arriveL1 s' →
    ∃ src d d', s.sl.chains P.C = some src ∧ s.l1.chains P.C = some d ∧
      s'.l1.chains P.C = some d' ∧
      d'.executed = src.executed ∧ d'.committed = src.executed ∧ d'.verified = src.executed ∧
      d'.batchHash src.executed = src.batchHash src.executed ∧
      (∀ n, n ≠ src.executed → d'.batchHash n = d.batchHash n) ∧ d'.logsRoot = d.logsRoot ∧
      d'.upgradeTxHash = src.upgradeTxHash ∧ d'.upgradeBatch = src.upgradeBatch ∧
      d'.away = false ∧ s'.l1.mr.cur P.C = src.executed ∧ d.executed ≤ src.executed

/-- **ARRIVING ON THE SETTLEMENT LAYER COPIES THE DEPARTED COPY.** In a state satisfying
`TwoInv`, an arrival on the settlement layer (onto an existing diamond or a fresh one) leaves
a diamond `d'` whose three counters equal L1's copy's executed count `E`, whose stored hash of
batch `E` and upgrade-transaction fields are that copy's, and which settles, and sets the
layer's message-root counter to `E`. If the layer had a diamond `d`, `E` is at least `d`'s
executed count and `d'` keeps `d`'s other stored hashes and its logs roots. -/
def Properties.ArrivalOnSLCopiesSource : Prop :=
  ∀ (P : TwoConfig) (s s' : TwoHubs) (l : TwoLabel), TwoInv P s → TwoStep P s l s' →
    (l = .arriveSLExisting ∨ ∃ gh gr, l = .arriveSLNew gh gr) →
    ∃ src d', s.l1.chains P.C = some src ∧ s'.sl.chains P.C = some d' ∧
      d'.executed = src.executed ∧ d'.committed = src.executed ∧ d'.verified = src.executed ∧
      d'.batchHash src.executed = src.batchHash src.executed ∧
      d'.upgradeTxHash = src.upgradeTxHash ∧ d'.upgradeBatch = src.upgradeBatch ∧
      d'.away = false ∧ s'.sl.mr.cur P.C = src.executed ∧
      ∀ d, s.sl.chains P.C = some d → d.executed ≤ src.executed ∧
        (∀ n, n ≠ src.executed → d'.batchHash n = d.batchHash n) ∧ d'.logsRoot = d.logsRoot

/-- **THE EXECUTED LOG IS CONTIGUOUS ACROSS MIGRATIONS.** Along any run from a state satisfying
`TwoInv`, the batch numbers executed for `C` on both layers together, in run order, are
`E + 1, E + 2, …` where `E` is `chainExecuted` at the start, and `chainExecuted` at the end is
`E` plus their number. So no batch number is executed twice and none is skipped. -/
def Properties.ExecutedLogContiguous : Prop :=
  ∀ (P : TwoConfig) (s s' : TwoHubs) (ls : List TwoLabel), TwoInv P s → TwoRun P s ls s' →
    twoExecNumbers P.C ls = List.range' (chainExecuted P s + 1) (twoExecNumbers P.C ls).length ∧
      chainExecuted P s' = chainExecuted P s + (twoExecNumbers P.C ls).length

/-- **NEITHER COPY EVER GOES BACK.** Along any run from a state satisfying `TwoInv`, the
executed count of `C`'s diamond on each layer never decreases (a missing diamond counts as
`0`). In particular L1's count after a return is at least its count at departure. -/
def Properties.CopiesNeverGoBack : Prop :=
  ∀ (P : TwoConfig) (s s' : TwoHubs) (ls : List TwoLabel), TwoInv P s → TwoRun P s ls s' →
    copyExecuted s.l1 P.C ≤ copyExecuted s'.l1 P.C ∧ copyExecuted s.sl P.C ≤ copyExecuted s'.sl P.C

/-- **HONEST ARRIVALS ARE ACCEPTED.** In a state satisfying `TwoInv` with data in flight, and
migrations enabled on the destination: towards L1 the arrival step exists; towards the
settlement layer the arrival onto its diamond exists if it has one, and otherwise the arrival
onto a fresh one exists for every nonzero genesis hash. -/
def Properties.HonestArrivalsAccepted : Prop :=
  ∀ (P : TwoConfig) (s : TwoHubs) (f : Flight), TwoInv P s → s.flight = some f →
    (f.dir = .toL1 → P.l1.migrationsEnabled = true → ∃ s', TwoStep P s .arriveL1 s') ∧
    (f.dir = .toSL → P.sl.migrationsEnabled = true → s.sl.chains P.C ≠ none →
      ∃ s', TwoStep P s .arriveSLExisting s') ∧
    (f.dir = .toSL → P.sl.migrationsEnabled = true → s.sl.chains P.C = none →
      ∀ gh gr : Word, gh ≠ 0 → ∃ s', TwoStep P s (.arriveSLNew gh gr) s')

/-! ## Witness -/

/-- **A ROUND TRIP.** For chain `1` with migrations enabled on both layers: a run on L1 from the
empty layer creates it and executes batch 1. From there, with the settlement layer empty and
nothing in flight (a state satisfying `TwoInv`), the two-layer run departs from L1, arrives on
the settlement layer (which has no diamond for it), executes batches 2 and 3 there, departs,
arrives back on L1, and executes batch 4 on L1. The run's executed batch numbers are
`[2, 3, 4]`; at the end `TwoInv` holds, nothing is in flight, L1's copy has executed 4 batches
and settles, the settlement layer's copy has executed 3 and is away, and the message-root
counters are `4` on L1 and `3` on the settlement layer. -/
def Properties.RoundTripWitness : Prop :=
  ∃ (ls₀ : List HubLabel) (h₀ : Hub) (ls : List TwoLabel) (s : TwoHubs),
    HubRun latentL1 emptyHub ls₀ h₀ ∧ execNumbers 1 ls₀ = [1] ∧
    TwoInv wTwo { l1 := h₀, sl := emptyHub, flight := none } ∧
    TwoRun wTwo { l1 := h₀, sl := emptyHub, flight := none } ls s ∧
    TwoLabel.departL1 ∈ ls ∧ (∃ gh gr, TwoLabel.arriveSLNew gh gr ∈ ls) ∧
    TwoLabel.departSL ∈ ls ∧ TwoLabel.arriveL1 ∈ ls ∧
    twoExecNumbers 1 ls = [2, 3, 4] ∧ TwoInv wTwo s ∧ s.flight = none ∧
    (∃ d, s.l1.chains 1 = some d ∧ d.executed = 4 ∧ d.away = false) ∧
    (∃ d, s.sl.chains 1 = some d ∧ d.executed = 3 ∧ d.away = true) ∧
    s.l1.mr.cur 1 = 4 ∧ s.sl.mr.cur 1 = 3

/-- **A FAILED DEPARTURE, THEN AN ARRIVAL ON AN EXISTING DIAMOND.** For chain `1` with migrations
enabled on both layers, from the start of `RoundTripWitness` (a run on L1 from the empty layer,
the settlement layer empty, nothing in flight): a two-layer run `lsRt` that executes batches
`[2, 3, 4]`; then `C` departs from L1 again, and in the resulting state, which satisfies `TwoInv`,
L1's copy is away with 4 batches executed and the settlement layer's copy is away with 3; the
departure fails (`failL1`) and L1's copy settles again with 4 executed. `C` departs again, and in
the resulting state, which satisfies `TwoInv`, the data in flight carries 4 executed batches and
the settlement layer's existing copy is away with 3; it arrives on that diamond
(`arriveSLExisting`), which then settles with 4 executed and a message-root counter of 4; batch 5
is committed, proved and executed there, leaving a state satisfying `TwoInv` with the settlement
layer's copy and counter at 5. -/
def Properties.ReentryWitness : Prop :=
  ∃ (ls₀ : List HubLabel) (h₀ : Hub) (lsRt : List TwoLabel) (s₁ s₂ s₃ s₄ s₅ s : TwoHubs),
    HubRun latentL1 emptyHub ls₀ h₀ ∧
    TwoRun wTwo { l1 := h₀, sl := emptyHub, flight := none } lsRt s₁ ∧
    twoExecNumbers 1 lsRt = [2, 3, 4] ∧
    TwoStep wTwo s₁ .departL1 s₂ ∧ TwoInv wTwo s₂ ∧
    (∃ d, s₂.l1.chains 1 = some d ∧ d.away = true ∧ d.executed = 4) ∧
    (∃ e, s₂.sl.chains 1 = some e ∧ e.away = true ∧ e.executed = 3) ∧
    TwoStep wTwo s₂ .failL1 s₃ ∧ (∃ d, s₃.l1.chains 1 = some d ∧ d.away = false ∧ d.executed = 4) ∧
    TwoStep wTwo s₃ .departL1 s₄ ∧ TwoInv wTwo s₄ ∧
    (∃ f, s₄.flight = some f ∧ f.dir = .toSL ∧ f.com.executed = 4) ∧
    (∃ e, s₄.sl.chains 1 = some e ∧ e.away = true ∧ e.executed = 3) ∧
    TwoStep wTwo s₄ .arriveSLExisting s₅ ∧
    (∃ e, s₅.sl.chains 1 = some e ∧ e.away = false ∧ e.executed = 4) ∧ s₅.sl.mr.cur 1 = 4 ∧
    TwoRun wTwo s₅ [.sl (.commit 1 (wInfo 4) (wInfo 5)), .sl (.prove 1 5),
      .sl (.execute 1 [wInfo 5])] s ∧
    TwoInv wTwo s ∧ (∃ e, s.sl.chains 1 = some e ∧ e.executed = 5 ∧ e.away = false) ∧
    s.sl.mr.cur 1 = 5

end Contracts.BatchCounters
