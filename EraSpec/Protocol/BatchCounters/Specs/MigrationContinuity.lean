import EraSpec.Protocol.BatchCounters.Specs.MessageRootSync

/-!
# Model: one chain's batch counters across migration — two copies, one settling

Source: era-contracts `draft/v0.35.0` at `b17415d20`, as in
`EraSpec.Protocol.BatchCounters.Specs.MessageRootSync`, whose single-layer model (`Hub`,
`HubStep`) this file runs on two layers. Abbreviations as there.

**This file is definitions only.** The statements are in
`EraSpec.Protocol.BatchCounters.Properties.MigrationContinuity` and are proved in
`EraSpec.Protocol.BatchCounters.Proofs.MigrationContinuity`.

**Latent at `b17415d20`.** `bridgeBurn` and `bridgeMint` carry `whenMigrationsEnabled`
(`CAH:201, 365`) and `CHAIN_MIGRATIONS_ENABLED = false` (`common/Config.sol:320`), so with the
head configuration no departure or arrival step below can fire. The results are about the
migration code as written, for a release that enables it.

## What is modelled

L1 and one settlement layer (`TwoHubs.l1`, `TwoHubs.sl`), each a `Hub`, and one chain `C`
(`TwoConfig.C`) whose diamond may exist on both. `C` starts on L1. Its migrations are coupled
steps that pass the mint data through `TwoHubs.flight`:

| step | source |
|---|---|
| `departL1` | `HubStep.burn C` on L1 (`CAH:188-300`, `Mig:154-209`); the mint data (`CAH:281, 289-295`) goes in flight towards the settlement layer |
| `arriveSLNew` / `arriveSLExisting` | `HubStep.mintNew C` / `HubStep.mintExisting C` on the settlement layer with the data in flight (`CAH:361-420`) |
| `failL1` | `HubStep.confirmFailure C` on L1 (`L1CAH:122-172`) for a departure towards the settlement layer |
| `departSL` | `HubStep.burn C` on the settlement layer; the data goes in flight towards L1 |
| `arriveL1` | `HubStep.mintExisting C` on L1 with the data in flight |

Every other `HubStep` on either layer is a step (`l1`, `sl`), except the migration labels of
`C` (burn, mints, failure confirmation), which happen only as the coupled steps above.

## Model boundaries

* **The channel is honest and at-most-once.** An arrival or a failure confirmation consumes
  exactly the data the last departure put in flight, once. In the source this is the
  bridge's message authentication and replay protection: the L1 → settlement-layer priority
  transaction and its failure proof (`L1Nullifier`), and the settlement-layer → L1 message
  proved against an executed settlement-layer batch (`PROTO-EVIDENCE`). A failed arrival
  on the settlement layer and a failure confirmation are one step here (`failL1`).
  `StaleMintRewritesHistory` shows what the mint does with data that is not the departed
  copy's.
* **"The chain has gone back to L1 at most once"** (`MAX_ALLOWED_NUMBER_OF_MIGRATIONS = 2`,
  `common/Config.sol:329`, enforced at `CAH:274-279, 372-383`) is a reject-only check and is
  omitted: the model allows any number of round trips.
* Everything `HubStep` omits stays omitted; the settlement layer's `MessageRoot` is
  `L2MessageRoot`, which inherits `MessageRootBase` and overrides none of the modelled functions
  (`core/message-root/L2MessageRoot.sol:24`).
-/

namespace Contracts.BatchCounters

/-- Which way a migration goes. -/
inductive Dir
  /-- L1 → settlement layer. -/
  | toSL
  /-- Settlement layer → L1. -/
  | toL1
  deriving DecidableEq

/-- Mint data in flight: the direction, the batch number read from the source's message root
(`CAH:281`) and the source diamond's commitment (`Mig:208`). -/
structure Flight where
  dir : Dir
  bn : ℕ
  com : Commitment

/-- L1, the settlement layer, and `C`'s migration data in flight, if any. -/
structure TwoHubs where
  l1 : Hub
  sl : Hub
  flight : Option Flight

/-- The chain and the two layers' configurations. The settlement layer is not L1, so its
bridgehub has no `createNewChain` or `registerAlreadyDeployedZKChain`. -/
structure TwoConfig where
  C : ChainId
  l1 : HubConfig
  sl : HubConfig
  slNotL1 : sl.isL1 = false

/-- What happens. -/
inductive TwoLabel
  /-- A step on L1 other than a migration step of `C`. -/
  | l1 (l : HubLabel)
  /-- A step on the settlement layer other than a migration step of `C`. -/
  | sl (l : HubLabel)
  /-- `C` leaves L1. -/
  | departL1
  /-- `C` arrives on the settlement layer, which has no diamond for it, with the release's
  genesis hash and logs root. -/
  | arriveSLNew (genesisHash genesisRoot : Word)
  /-- `C` arrives on the settlement layer, which has its diamond. -/
  | arriveSLExisting
  /-- A departure towards the settlement layer failed; L1 takes `C` back. -/
  | failL1
  /-- `C` leaves the settlement layer. -/
  | departSL
  /-- `C` arrives back on L1. -/
  | arriveL1

/-- One step. -/
inductive TwoStep (P : TwoConfig) : TwoHubs → TwoLabel → TwoHubs → Prop
  | l1 {s : TwoHubs} {l : HubLabel} {h' : Hub} :
      (l.chain = P.C → l.isMigration = false) → HubStep P.l1 s.l1 l h' →
      TwoStep P s (.l1 l) { s with l1 := h' }
  | sl {s : TwoHubs} {l : HubLabel} {h' : Hub} :
      (l.chain = P.C → l.isMigration = false) → HubStep P.sl s.sl l h' →
      TwoStep P s (.sl l) { s with sl := h' }
  | departL1 {s : TwoHubs} {bn : ℕ} {com : Commitment} {h' : Hub} :
      s.flight = none → HubStep P.l1 s.l1 (.burn P.C bn com) h' →
      TwoStep P s .departL1 { s with l1 := h', flight := some ⟨.toSL, bn, com⟩ }
  | arriveSLNew {s : TwoHubs} {f : Flight} {gh gr : Word} {h' : Hub} :
      s.flight = some f → f.dir = .toSL → HubStep P.sl s.sl (.mintNew P.C f.bn f.com gh gr) h' →
      TwoStep P s (.arriveSLNew gh gr) { s with sl := h', flight := none }
  | arriveSLExisting {s : TwoHubs} {f : Flight} {h' : Hub} :
      s.flight = some f → f.dir = .toSL → HubStep P.sl s.sl (.mintExisting P.C f.bn f.com) h' →
      TwoStep P s .arriveSLExisting { s with sl := h', flight := none }
  | failL1 {s : TwoHubs} {f : Flight} {h' : Hub} :
      s.flight = some f → f.dir = .toSL → HubStep P.l1 s.l1 (.confirmFailure P.C) h' →
      TwoStep P s .failL1 { s with l1 := h', flight := none }
  | departSL {s : TwoHubs} {bn : ℕ} {com : Commitment} {h' : Hub} :
      s.flight = none → HubStep P.sl s.sl (.burn P.C bn com) h' →
      TwoStep P s .departSL { s with sl := h', flight := some ⟨.toL1, bn, com⟩ }
  | arriveL1 {s : TwoHubs} {f : Flight} {h' : Hub} :
      s.flight = some f → f.dir = .toL1 → HubStep P.l1 s.l1 (.mintExisting P.C f.bn f.com) h' →
      TwoStep P s .arriveL1 { s with l1 := h', flight := none }

/-- A sequence of steps. -/
inductive TwoRun (P : TwoConfig) : TwoHubs → List TwoLabel → TwoHubs → Prop
  | nil {s : TwoHubs} : TwoRun P s [] s
  | cons {s s' s'' : TwoHubs} {l : TwoLabel} {ls : List TwoLabel} :
      TwoStep P s l s' → TwoRun P s' ls s'' → TwoRun P s (l :: ls) s''

/-! ## Phases -/

/-- `C`'s diamond on this layer exists and settles here. -/
def Settles (h : Hub) (C : ChainId) : Prop := ∃ d, h.chains C = some d ∧ d.away = false

/-- `C` has no settling diamond on this layer: none, or one that is away. -/
def Idle (h : Hub) (C : ChainId) : Prop := ∀ d, h.chains C = some d → d.away = true

/-- Exactly one copy settles and nothing is in flight, or no copy settles and a migration is in
flight. -/
def Phase (P : TwoConfig) (s : TwoHubs) : Prop :=
  (s.flight = none ∧ Settles s.l1 P.C ∧ Idle s.sl P.C) ∨
  (s.flight = none ∧ Idle s.l1 P.C ∧ Settles s.sl P.C) ∨
  (s.flight ≠ none ∧ Idle s.l1 P.C ∧ Idle s.sl P.C)

/-- The layer a flight left. -/
def Flight.source (s : TwoHubs) (f : Flight) : Hub :=
  match f.dir with
  | .toSL => s.l1
  | .toL1 => s.sl

/-- `C`'s executed count on a layer (`0` without a diamond). -/
def copyExecuted (h : Hub) (C : ChainId) : ℕ :=
  match h.chains C with
  | some d => d.executed
  | none => 0

/-- `C`'s executed count: the commitment's while a migration is in flight, the settling
copy's otherwise. -/
def chainExecuted (P : TwoConfig) (s : TwoHubs) : ℕ :=
  match s.flight with
  | some f => f.com.executed
  | none =>
    match s.l1.chains P.C with
    | some d => if d.away = true then copyExecuted s.sl P.C else d.executed
    | none => copyExecuted s.sl P.C

/-- The invariant of the two-layer system.

* Both layers satisfy `HubInv`, and `C`'s counters agree on both.
* `C` has a diamond on L1 (it starts there and none is ever removed).
* `Phase`.
* `snapshot`: the data in flight is the source copy's commitment and counter, with every
  committed batch executed (`Mig:203-205`) — and that copy is still as it was.
* `behind`: neither copy has executed more than `chainExecuted`. -/
structure TwoInv (P : TwoConfig) (s : TwoHubs) : Prop where
  l1Inv : HubInv s.l1
  slInv : HubInv s.sl
  l1Sync : Synced s.l1 P.C
  slSync : Synced s.sl P.C
  l1Present : s.l1.chains P.C ≠ none
  phase : Phase P s
  snapshot : ∀ f, s.flight = some f → ∃ d, (Flight.source s f).chains P.C = some d ∧
    f.com = prepare d ∧ f.bn = d.executed ∧ d.committed = d.executed ∧ d.verified = d.executed
  behind : copyExecuted s.l1 P.C ≤ chainExecuted P s ∧ copyExecuted s.sl P.C ≤ chainExecuted P s

/-- The pipeline labels: commit, prove, execute, revert. -/
def HubLabel.isPipeline : HubLabel → Bool
  | .commit .. => true
  | .prove .. => true
  | .execute .. => true
  | .revert .. => true
  | _ => false

/-- The batch numbers a two-layer run executes for `C`, on either layer, in order. -/
def twoExecNumbers (C : ChainId) : List TwoLabel → List ℕ
  | [] => []
  | .l1 l :: ls => execNumbers C [l] ++ twoExecNumbers C ls
  | .sl l :: ls => execNumbers C [l] ++ twoExecNumbers C ls
  | _ :: ls => twoExecNumbers C ls

/-! ## Witness data -/

/-- L1 with migrations enabled: the configuration a release that re-enables them would have. -/
def latentL1 : HubConfig := { isL1 := true, migrationsEnabled := true, hash := wHash }

/-- A settlement layer with migrations enabled. -/
def latentSL : HubConfig := { isL1 := false, migrationsEnabled := true, hash := wHash }

/-- The witness system: chain `1` between L1 and a settlement layer. -/
def wTwo : TwoConfig := { C := 1, l1 := latentL1, sl := latentSL, slNotL1 := rfl }

/-- A diamond that has left: ten batches committed, verified and executed, stored hash
`500 + n` for every batch `n`. -/
def wAwayDiamond : Diamond where
  committed := 10
  verified := 10
  executed := 10
  batchHash := fun n => 500 + n
  logsRoot := fun _ => 0
  away := true
  upgradeTxHash := 0
  upgradeBatch := 0

/-- L1 with that diamond as chain `1`, its message-root counter at `10`. -/
def wAwayHub : Hub where
  mr := { reg := upd (fun _ => false) 1 true, cur := upd (fun _ => 0) 1 10, roots := fun _ _ => 0 }
  chains := upd (fun _ => none) 1 (some wAwayDiamond)

/-- A stale commitment: five batches executed, ten committed and verified, with the hashes of
batches 5 to 10. -/
def wStaleCom : Commitment where
  executed := 5
  verified := 10
  committed := 10
  upgradeTxHash := 0
  upgradeBatch := 0
  batchHashes := [1, 2, 3, 4, 5, 6]

end Contracts.BatchCounters
