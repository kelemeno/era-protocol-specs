import EraSpec.Protocol.AssetBridgePreparation.Specs.Resolution

/-!
# Properties: delivery and refund across two chains

Statements about `EraSpec.Protocol.AssetBridgePreparation.Specs.Resolution`; proofs are in
`EraSpec.Protocol.AssetBridgePreparation.Proofs.Resolution`. Every statement quantifies over
the hooks, the evidence and the witness types. None takes a hash premise.

## Books, with no evidence premise

* `TwoChainSourceBooks`: the source's supply plus the amount it burned and has not refunded is
  constant. Only the source's own record is used.
* `TwoChainDestinationBooks`: the destination's supply grows by exactly the amount it delivered.
  Only the destination's own record is used.
* `TwoChainLedgerExact`: across both chains, circulating supply plus value in flight changes by
  exactly the value paid twice. No premise on the evidence.

## The trace and its entries

* `TwoChainEntriesPersist`: entries are append-only and never rewritten; records only grow.
* `TwoChainEntriesFromRequests`: from an empty entry list, every entry is a logged request's
  destination, asset, depositor, receiver and nonzero amount.
* `TwoChainResolutionPaysEntry`: a delivery pays the entry's receiver and a refund its depositor
  exactly the entry's amount, and neither touches the other chain.
* `TwoChainRefundCallIsRecoveryCall`: the refund's vault call is B2's `recoveryCall`.
* `TwoChainExtendsPreparationTrace`: the closed trace of `Specs/Model.lean` is the source-side
  fragment of this one.
* `TwoChainResolutionsCommute`: a delivery and a refund enabled together stay enabled after each
  other and commute, also for the same entry: there is no shared lock.

## At most once, and never both (B5)

* `TwoChainReplayCounts`: each chain's own record counts its resolutions exactly; a run delivers
  an entry at most once and refunds it at most once, with no premise.
* `TwoChainDoubleResolutionLocated`: under `SoundOrBreak Brk`, an entry that is both delivered
  and refunded carries `Brk` on the two witnesses the run's own labels consumed.
* `TwoChainExclusive`, `TwoChainResolvesOnce` (`Sound`): no entry is both delivered and
  refunded, and each entry is resolved at most once across both chains.
* `TwoChainResolvesOnceOrBreak`: the same, or a located break.

## Conservation (B6)

* `TwoChainConservation` (headline, `Sound`): circulating supply on both chains plus value in
  flight is constant along every run whose records start empty.
* `TwoChainConservedOrBreak`: the same, or a located break.

## Refund enabledness (B12)

* `TwoChainRefundAvailable`: from a fresh trace, no step of the trace (spending on either chain,
  other preparations, deliveries, other refunds) can block the refund of an unrefunded entry.
  Only missing evidence or a failing hook can. The refund pays exactly the entry's amount.

## Evidence

* `ResolutionGateSoundIffNoBreak`: `Sound` is `SoundOrBreak` with the empty break.
* `TwoChainConflictingGateDoublePays` (countermodel): with evidence that accepts both sides, an
  entry is delivered and refunded and the books exceed their start by its amount. The local
  records alone do not give exclusivity.
* `TwoChainWithoutRecordsPaysTwice` (countermodel): with sound evidence but without the two local
  replay guards, one entry is delivered twice and another refunded twice. Sound evidence alone
  does not give at-most-once resolution. Both ingredients are needed.

## Anti-vacuity

`TwoChainSatisfiable` meets, in one run under the sound `splitResolutionGate 0 1`, the premises
of every result above except the commutation: two preparations, spending on both chains, a
delivery of entry `0`, and a refund of entry `1` from a state that meets every premise of
`TwoChainRefundAvailable`. `TwoChainResolutionsCommuteSatisfiable` meets the commutation's
premises at a reachable state under the same sound gate; the countermodel's run meets them for
one entry. The `…OrBreak` results are instantiated with real evidence in
`Properties/ResolutionEvidence.lean`, with their own witnesses.
-/

namespace AssetBridgePreparation

open Contracts

/-! ## Books, with no evidence premise -/

/-- **THE SOURCE'S BOOKS BALANCE, ON ITS OWN RECORD.** Along every run from a `WellFormed` source
whose records name existing entries, the source supply plus the total amount of the entries it
has not refunded is constant: a preparation moves its amount from supply into that total, a
refund moves it back, and nothing else (deliveries, spending) touches either. -/
def Properties.TwoChainSourceBooks : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (s t : TwoChainLedger A B)
    (ls : List (TwoChainLabel Wd Wr)),
    NativeTokenVaultBase.WellFormed s.source → s.RecordsInRange → TwoChainRun E s ls t →
      t.source.token.totalSupply + t.unrefunded = s.source.token.totalSupply + s.unrefunded

/-- **THE DESTINATION'S BOOKS BALANCE, ON ITS OWN RECORD.** Along every run whose records name
existing entries, the destination supply grows by exactly the total amount of the entries it
delivered during the run. No invariant of the destination vault is assumed. -/
def Properties.TwoChainDestinationBooks : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (s t : TwoChainLedger A B)
    (ls : List (TwoChainLabel Wd Wr)),
    s.RecordsInRange → TwoChainRun E s ls t →
      t.destination.token.totalSupply + s.deliveredAmount =
        s.destination.token.totalSupply + t.deliveredAmount

/-- **EXACT TWO-CHAIN ACCOUNTING, WITH NO EVIDENCE PREMISE.** Along every run from a `WellFormed`
source whose records name existing entries: the source stays `WellFormed`, the records keep
naming existing entries, and circulating supply on both chains plus value in flight changes by
exactly the change in value paid twice (`doublePaid`, the entries both delivered and
refunded). -/
def Properties.TwoChainLedgerExact : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (s t : TwoChainLedger A B)
    (ls : List (TwoChainLabel Wd Wr)),
    NativeTokenVaultBase.WellFormed s.source → s.RecordsInRange → TwoChainRun E s ls t →
      NativeTokenVaultBase.WellFormed t.source ∧ t.RecordsInRange ∧
      t.circulating + t.outstanding + s.doublePaid =
        s.circulating + s.outstanding + t.doublePaid

/-! ## The trace and its entries -/

/-- **ENTRIES ARE APPEND-ONLY, RECORDS ONLY GROW.** Every run only appends to the entry list, so
an entry's route context, receiver, depositor and amount never change once prepared, and neither
chain ever forgets a resolution. -/
def Properties.TwoChainEntriesPersist : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (s t : TwoChainLedger A B)
    (ls : List (TwoChainLabel Wd Wr)),
    TwoChainRun E s ls t →
      (∃ later, t.pending = s.pending ++ later) ∧ s.delivered ⊆ t.delivered ∧
        s.refunded ⊆ t.refunded

/-- **EVERY ENTRY IS A LOGGED REQUEST.** Along every run from an empty entry list on a `WellFormed`
source, every entry was appended by a preparation `prepare r` among the run's labels, and it
records that request's destination chain, asset, depositor (as `originalCaller`), receiver (as
`remoteReceiver`) and nonzero amount. With `TwoChainResolutionPaysEntry`: a delivery credits
exactly the requested receiver with the requested amount, and a refund returns exactly that
amount to the depositor. -/
def Properties.TwoChainEntriesFromRequests : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (s t : TwoChainLedger A B)
    (ls : List (TwoChainLabel Wd Wr)),
    NativeTokenVaultBase.WellFormed s.source → s.pending = [] → TwoChainRun E s ls t →
    ∀ o ∈ t.pending, ∃ r, TwoChainLabel.prepare r ∈ ls ∧
      o.destinationChain = r.destinationChain ∧ o.assetId = r.assetId ∧
      o.data.originalCaller = r.depositor ∧ o.data.remoteReceiver = r.data.receiver ∧
      o.data.amount = r.data.amount ∧ o.data.amount ≠ 0

/-- **A RESOLUTION PAYS EXACTLY ITS ENTRY, ON ITS OWN CHAIN.** A delivery of entry `o` credits
the entry's `remoteReceiver` with exactly its amount at the destination (supply up by the same,
every other destination balance unchanged) and leaves the source, the entries and the source's
record untouched. A refund of entry `o` credits the entry's `originalCaller` with exactly its
amount at the source and leaves the destination, the entries and the destination's record
untouched. -/
def Properties.TwoChainResolutionPaysEntry : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (s t : TwoChainLedger A B) (i : ℕ)
    (o : Obligation),
    s.pending[i]? = some o →
      (∀ wd : Wd, TwoChainStep E s (.deliver i wd) t →
        t.destination.token.balances o.data.remoteReceiver =
          s.destination.token.balances o.data.remoteReceiver + o.data.amount.val ∧
        t.destination.token.totalSupply = s.destination.token.totalSupply + o.data.amount.val ∧
        (∀ a, a ≠ o.data.remoteReceiver →
          t.destination.token.balances a = s.destination.token.balances a) ∧
        t.source = s.source ∧ t.pending = s.pending ∧ t.refunded = s.refunded) ∧
      (∀ wr : Wr, TwoChainStep E s (.refund i wr) t →
        t.source.token.balances o.data.originalCaller =
          s.source.token.balances o.data.originalCaller + o.data.amount.val ∧
        t.source.token.totalSupply = s.source.token.totalSupply + o.data.amount.val ∧
        (∀ a, a ≠ o.data.originalCaller →
          t.source.token.balances a = s.source.token.balances a) ∧
        t.destination = s.destination ∧ t.pending = s.pending ∧ t.delivered = s.delivered)

/-- **THE REFUND'S VAULT CALL IS B2'S RECOVERY CALL.** For an entry made by a preparation of
request `r` with returned data `data`, `twoChainRefundCall` is exactly the call
`NativeTokenVaultBase.recoveryCall` that B2's round-trip results are stated about. -/
def Properties.TwoChainRefundCallIsRecoveryCall : Prop :=
  ∀ (router : NativeTokenVaultBase.Address) (r : NativeTokenVaultBase.Request)
    (data : NativeTokenVaultBase.MintData),
    twoChainRefundCall router (obligation r data) = NativeTokenVaultBase.recoveryCall router r data

/-- **THE TWO-CHAIN TRACE EXTENDS THE CLOSED PREPARATION TRACE.** Every run of the closed trace of
`Specs/Model.lean` (`Reach`), played on the source chain, is a run of the two-chain trace that
leaves the destination and both records unchanged. Conversely, a two-chain preparation or source
transfer is a `Step` of the closed trace on the source and its entries, and leaves the destination
and both records unchanged. -/
def Properties.TwoChainExtendsPreparationTrace : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr),
    (∀ (s t : Ledger A) (d : NativeTokenVaultBase.State B) (D R : Finset ℕ),
      Reach E.hooks s t →
        ∃ ls, TwoChainRun E ⟨s.vault, d, s.pending, D, R⟩ ls ⟨t.vault, d, t.pending, D, R⟩) ∧
    (∀ (s t : TwoChainLedger A B) (l : TwoChainLabel Wd Wr),
      TwoChainStep E s l t → (l = .spendSource ∨ ∃ r, l = .prepare r) →
        Step E.hooks ⟨s.source, s.pending⟩ ⟨t.source, t.pending⟩ ∧
        t.destination = s.destination ∧ t.delivered = s.delivered ∧ t.refunded = s.refunded)

/-- **THE TWO RESOLUTIONS ARE INDEPENDENT: NO SHARED LOCK.** If, at one state, a delivery of entry
`i` and a refund of entry `j` are both enabled, then after either one the other is still enabled,
and the two orders reach the same state. This includes `i = j`: delivering an entry does not
disable its refund at the source, and refunding it does not disable its delivery at the
destination. Only the evidence can exclude one of them (`TwoChainConflictingGateDoublePays`). -/
def Properties.TwoChainResolutionsCommute : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (s t u : TwoChainLedger A B) (i j : ℕ)
    (wd : Wd) (wr : Wr),
    TwoChainStep E s (.deliver i wd) t → TwoChainStep E s (.refund j wr) u →
      ∃ v, TwoChainStep E t (.refund j wr) v ∧ TwoChainStep E u (.deliver i wd) v

/-! ## At most once, and never both -/

/-- **EACH CHAIN'S OWN RECORD COUNTS ITS RESOLUTIONS EXACTLY.** In every run, the number of
deliveries of entry `i` plus `1` if the destination had already delivered it equals `1` if it
has delivered it at the end, and likewise for refunds at the source. In particular every run
delivers each entry at most once and refunds it at most once, whatever the evidence. A failed
attempt is no step, so a retry after a revert is counted once. -/
def Properties.TwoChainReplayCounts : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (s t : TwoChainLedger A B)
    (ls : List (TwoChainLabel Wd Wr)),
    TwoChainRun E s ls t → ∀ i : ℕ,
      deliveryCount ls i + (if i ∈ s.delivered then 1 else 0) =
          (if i ∈ t.delivered then 1 else 0) ∧
        refundCount ls i + (if i ∈ s.refunded then 1 else 0) =
          (if i ∈ t.refunded then 1 else 0)

/-- **A DOUBLE RESOLUTION CARRIES ITS OWN LOCATED BREAK.** If the evidence is sound up to `Brk`
and the run starts with empty records, then for every entry that ends both delivered and
refunded, the run's own labels contain a delivery of it with a witness `wd` and a refund of it
with a witness `wr`, both passed the evidence, and `Brk` holds on exactly those two witnesses. -/
def Properties.TwoChainDoubleResolutionLocated : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (Brk : ℕ → Wd → Wr → Prop)
    (s t : TwoChainLedger A B) (ls : List (TwoChainLabel Wd Wr)),
    E.gate.SoundOrBreak Brk → s.FreshRecords → TwoChainRun E s ls t →
    ∀ i : ℕ, i ∈ t.delivered → i ∈ t.refunded →
      ∃ (wd : Wd) (wr : Wr), TwoChainLabel.deliver i wd ∈ ls ∧
        TwoChainLabel.refund i wr ∈ ls ∧ E.gate.finalize i wd ∧ E.gate.recover i wr ∧
        Brk i wd wr

/-- **NEVER BOTH.** With sound evidence, along every run whose records start empty, no entry is
both delivered and refunded. -/
def Properties.TwoChainExclusive : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (s t : TwoChainLedger A B)
    (ls : List (TwoChainLabel Wd Wr)),
    E.gate.Sound → s.FreshRecords → TwoChainRun E s ls t →
      ∀ i : ℕ, ¬ (i ∈ t.delivered ∧ i ∈ t.refunded)

/-- **EACH ENTRY IS RESOLVED AT MOST ONCE, ACROSS BOTH CHAINS.** With sound evidence, along every
run whose records start empty, the labels contain at most one resolution of each entry: one
delivery or one refund, not two of either and not one of each. -/
def Properties.TwoChainResolvesOnce : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (s t : TwoChainLedger A B)
    (ls : List (TwoChainLabel Wd Wr)),
    E.gate.Sound → s.FreshRecords → TwoChainRun E s ls t →
      ∀ i : ℕ, deliveryCount ls i + refundCount ls i ≤ 1

/-- **RESOLVED AT MOST ONCE, OR A LOCATED BREAK.** With evidence sound up to `Brk`, each entry is
resolved at most once in the run, or the run's labels deliver it with some `wd` and refund it
with some `wr` on which `Brk` holds. -/
def Properties.TwoChainResolvesOnceOrBreak : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (Brk : ℕ → Wd → Wr → Prop)
    (s t : TwoChainLedger A B) (ls : List (TwoChainLabel Wd Wr)),
    E.gate.SoundOrBreak Brk → s.FreshRecords → TwoChainRun E s ls t → ∀ i : ℕ,
      deliveryCount ls i + refundCount ls i ≤ 1 ∨
        ∃ (wd : Wd) (wr : Wr), TwoChainLabel.deliver i wd ∈ ls ∧
          TwoChainLabel.refund i wr ∈ ls ∧ Brk i wd wr

/-! ## Conservation -/

/-- **CONSERVATION ACROSS BOTH CHAINS.** With sound evidence, along every run from a `WellFormed`
source whose records start empty (entries may already be pending), the source supply plus the
destination supply plus the value in flight is constant, and nothing is ever paid twice. Any
number of entries, interleaved preparations, spending on either chain, deliveries and refunds,
in any order. -/
def Properties.TwoChainConservation : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (s t : TwoChainLedger A B)
    (ls : List (TwoChainLabel Wd Wr)),
    E.gate.Sound → NativeTokenVaultBase.WellFormed s.source → s.FreshRecords →
    TwoChainRun E s ls t →
      t.circulating + t.outstanding = s.circulating + s.outstanding ∧ t.doublePaid = 0

/-- **CONSERVATION, OR A LOCATED BREAK.** With evidence sound up to `Brk`, the books balance as in
`TwoChainConservation`, or some entry was delivered with a witness `wd` and refunded with a
witness `wr` from the run's own labels, and `Brk` holds on them. -/
def Properties.TwoChainConservedOrBreak : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (Brk : ℕ → Wd → Wr → Prop)
    (s t : TwoChainLedger A B) (ls : List (TwoChainLabel Wd Wr)),
    E.gate.SoundOrBreak Brk → NativeTokenVaultBase.WellFormed s.source → s.FreshRecords →
    TwoChainRun E s ls t →
      t.circulating + t.outstanding = s.circulating + s.outstanding ∨
        ∃ (i : ℕ) (wd : Wd) (wr : Wr), TwoChainLabel.deliver i wd ∈ ls ∧
          TwoChainLabel.refund i wr ∈ ls ∧ Brk i wd wr

/-! ## Refund enabledness -/

/-- **NOTHING IN THE TRACE BLOCKS A REFUND.** Along every run from a fresh trace on a `WellFormed`
source, for every entry the source has not refunded: given a passing source witness and a
succeeding resolution hook, the refund step is enabled, and it credits the entry's depositor
with exactly its amount. Spending on either chain, other preparations, deliveries and other
refunds cannot block it: the burn freed the supply headroom the re-mint needs, and the vault's
configuration, registry and pause flag are never changed by the trace. -/
def Properties.TwoChainRefundAvailable : Prop :=
  ∀ (A B Wd Wr : Type) (E : TwoChainEnv A B Wd Wr) (s t : TwoChainLedger A B)
    (ls : List (TwoChainLabel Wd Wr)),
    NativeTokenVaultBase.WellFormed s.source → s.FreshTrace → TwoChainRun E s ls t →
    ∀ (i : ℕ) (o : Obligation) (wr : Wr) (accounted : A),
      t.pending[i]? = some o → i ∉ t.refunded → E.gate.recover i wr →
      E.sourceResolve.fromChain t.source.accounting t.source.token o.destinationChain o.assetId
          o.data.amount = some accounted →
        ∃ u, TwoChainStep E t (.refund i wr) u ∧
          u.source.token.balances o.data.originalCaller =
            t.source.token.balances o.data.originalCaller + o.data.amount.val

/-! ## Evidence -/

/-- **SOUND IS SOUND WITH NO BREAK.** -/
def Properties.ResolutionGateSoundIffNoBreak : Prop :=
  ∀ (Wd Wr : Type) (G : ResolutionGate Wd Wr), G.Sound ↔ G.SoundOrBreak (fun _ _ _ => False)

/-- **COUNTERMODEL: WITHOUT EXCLUSIVE EVIDENCE THE LOCAL RECORDS DO NOT PREVENT DOUBLE PAYMENT.**
With the evidence that accepts both sides (`acceptAllResolutionGate`, not sound), from a fresh
trace on a `WellFormed` source, one preparation is delivered at the destination and refunded at
the source, each chain's own record admitting its step. The entry is both delivered and refunded,
and circulating supply plus value in flight ends exactly the entry's (nonzero) amount above its
start. -/
def Properties.TwoChainConflictingGateDoublePays : Prop :=
  ∃ (E : TwoChainEnv Unit Unit Unit Unit) (s t : TwoChainLedger Unit Unit)
    (ls : List (TwoChainLabel Unit Unit)),
    E.gate = acceptAllResolutionGate ∧ ¬ E.gate.Sound ∧
    NativeTokenVaultBase.WellFormed s.source ∧ s.FreshTrace ∧ TwoChainRun E s ls t ∧
    0 ∈ t.delivered ∧ 0 ∈ t.refunded ∧ pendingAmountAt t.pending 0 ≠ 0 ∧
    t.circulating + t.outstanding = s.circulating + s.outstanding + pendingAmountAt t.pending 0

/-- **COUNTERMODEL: WITHOUT THE LOCAL RECORDS, SOUND EVIDENCE DOES NOT PREVENT DOUBLE PAYMENT.** In
the trace without the two replay guards (`TwoChainStepUnguarded`), under the sound
`splitResolutionGate 0 1`, from a fresh trace on a `WellFormed` source: entry `0` is delivered
twice and entry `1` refunded twice, each time on passing evidence, and circulating supply plus
value in flight ends both entries' (nonzero) amounts above its start. Exclusive evidence is not
enough: at-most-once delivery and at-most-once refund are the local records' job. -/
def Properties.TwoChainWithoutRecordsPaysTwice : Prop :=
  ∃ (E : TwoChainEnv Unit Unit Unit Unit) (s t : TwoChainLedger Unit Unit)
    (ls : List (TwoChainLabel Unit Unit)),
    E.gate = splitResolutionGate 0 1 ∧ E.gate.Sound ∧
    NativeTokenVaultBase.WellFormed s.source ∧ s.FreshTrace ∧ TwoChainRunUnguarded E s ls t ∧
    deliveryCount ls 0 = 2 ∧ refundCount ls 1 = 2 ∧
    pendingAmountAt t.pending 0 ≠ 0 ∧ pendingAmountAt t.pending 1 ≠ 0 ∧
    t.circulating + t.outstanding =
      s.circulating + s.outstanding + pendingAmountAt t.pending 0 + pendingAmountAt t.pending 1

/-! ## Anti-vacuity -/

/-- **THE PREMISES ARE JOINTLY SATISFIABLE, WITH BOTH RESOLUTIONS FIRING UNDER SOUND EVIDENCE.**
Under the sound `splitResolutionGate 0 1`, from a fresh trace on a `WellFormed` source: two
preparations of nonzero amounts, a source transfer, a delivery of entry `0`, a destination
transfer, and then, from the state `t₁` just before it, a refund of entry `1` from a state that
meets every premise of `TwoChainRefundAvailable` (entry present and unrefunded, witness passing,
hook succeeding). At the end entry `0` is delivered, entry `1` refunded, and nothing is in
flight. -/
def Properties.TwoChainSatisfiable : Prop :=
  ∃ (E : TwoChainEnv Unit Unit Unit Unit) (s t₁ t : TwoChainLedger Unit Unit)
    (ls : List (TwoChainLabel Unit Unit)) (o : Obligation),
    E.gate = splitResolutionGate 0 1 ∧ E.gate.Sound ∧
    NativeTokenVaultBase.WellFormed s.source ∧ s.FreshTrace ∧
    TwoChainRun E s ls t₁ ∧ TwoChainLabel.spendSource ∈ ls ∧
    TwoChainLabel.spendDestination ∈ ls ∧ TwoChainLabel.deliver 0 () ∈ ls ∧
    t₁.pending[1]? = some o ∧ 1 ∉ t₁.refunded ∧ E.gate.recover 1 () ∧
    E.sourceResolve.fromChain t₁.source.accounting t₁.source.token o.destinationChain o.assetId
      o.data.amount = some () ∧
    TwoChainStep E t₁ (.refund 1 ()) t ∧ TwoChainRun E s (ls ++ [.refund 1 ()]) t ∧
    0 ∈ t.delivered ∧ 1 ∈ t.refunded ∧ pendingAmountAt t.pending 0 ≠ 0 ∧
    pendingAmountAt t.pending 1 ≠ 0 ∧ t.outstanding = 0

/-- **THE COMMUTATION PREMISES HOLD AT A REACHABLE STATE UNDER SOUND EVIDENCE.** Under the sound
`splitResolutionGate 0 1`, after two preparations from a fresh trace on a `WellFormed` source, a
delivery of entry `0` and a refund of entry `1` are both enabled. (The same-entry case is the
countermodel's run: there a delivery and a refund of entry `0` both fire.) -/
def Properties.TwoChainResolutionsCommuteSatisfiable : Prop :=
  ∃ (E : TwoChainEnv Unit Unit Unit Unit) (s₀ s t u : TwoChainLedger Unit Unit)
    (ls : List (TwoChainLabel Unit Unit)),
    E.gate = splitResolutionGate 0 1 ∧ E.gate.Sound ∧
    NativeTokenVaultBase.WellFormed s₀.source ∧ s₀.FreshTrace ∧ TwoChainRun E s₀ ls s ∧
    TwoChainStep E s (.deliver 0 ()) t ∧ TwoChainStep E s (.refund 1 ()) u

end AssetBridgePreparation
