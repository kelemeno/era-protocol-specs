import EraSpec.Contracts.InteropHandlerBase.Specs.ValueLedgerFaithful

/-!
# Properties: no inflation, for the handler's own ledger

Statements about `EraSpec.Contracts.InteropHandlerBase.Specs.ValueLedgerFaithful`. Proofs are in
`EraSpec.Contracts.InteropHandlerBase.Proofs.ValueLedgerFaithful`.

Every result below holds in the re-entrant model (every target behaviour, at every depth, over any
sequence of transactions) under the binding premise `NamesOnly b` for every entry-point call of the
run. The last three are from fresh storage, where the replay state is the committed history
(`Reentrancy.StatusRecordsExactlyTheCommittedEffects`).

* `ReleasesAreTheBundlesCalls`: every committed delivery of `b.hash` is of a call of `b`.
* `ReleaseIsTheHandlerLedger` (the link `BundleStatusMachine` lacks): the base token the handler
  released for `b` is `releasedSum` of its own ledger for `b` (one entry per call: value, final
  `callStatus`), and `collectedSum` of that ledger is what the source collected. So
  `released_le_collected`, `released_eq_collected_of_all_executed` and `shortfall_is_unexecuted`
  apply to the handler.
* `HandlerReleasesAtMostCollected` (no inflation): release is at most collection.
* `ExecutedBundleReleasesAllCollected` (the bound is attained): once `b` completes a whole-bundle
  execution, release equals collection.
* `SharedHashBreaksTheLedger`: without the binding premise, a second bundle with the same hash
  makes the handler release more than the first bundle collected.
* `LedgerWitness`: the premise holds on a run that executes one call and cancels the other, whose
  release is strictly below collection, and on one that executes the bundle whole.
-/

namespace Contracts.InteropHandler.Faithful

open AttackVectors.BundleStatusMachine (releasedSum collectedSum CallStatus)

/-- **EVERY RELEASE IS FOR A CALL OF THE BUNDLE.** From every state, along every sequence of
transactions all of whose entry-point calls satisfy the binding premise for `b`: every committed
delivery of call `i` of hash `b.hash` has `i < b.calls`. -/
def Properties.ReleasesAreTheBundlesCalls : Prop :=
  ∀ (s : State) (b : Bundle) (txs : List Tx), (∀ t ∈ txs, TxAll (NamesOnly b) t) →
    ∀ i, Effect.delivered b.hash i ∈ (submitAll .deployed s txs).2 → i < b.calls

/-- **THE LEDGER IS THE HANDLER'S.** From fresh storage, along every sequence of transactions all of
whose entry-point calls satisfy the binding premise for `b`, and for every assignment `val` of
values to `b`'s calls: the base token the handler released for `b` (`val i` per committed delivery
of call `i`) is `releasedSum` of the handler's ledger for `b` in the final state, and `collectedSum`
of that ledger is what the source collected for `b`. -/
def Properties.ReleaseIsTheHandlerLedger : Prop :=
  ∀ (val : CallValues) (b : Bundle) (txs : List Tx), (∀ t ∈ txs, TxAll (NamesOnly b) t) →
    releasedFor val b.hash (submitAll .deployed init txs).2 =
        releasedSum (handlerLedger val b (submitAll .deployed init txs).1) ∧
      collectedSum (handlerLedger val b (submitAll .deployed init txs).1) = collectedFor val b

/-- **NO INFLATION, FOR THE HANDLER.** Under the same premises, the handler releases for `b` at
most what the source collected for `b`. -/
def Properties.HandlerReleasesAtMostCollected : Prop :=
  ∀ (val : CallValues) (b : Bundle) (txs : List Tx), (∀ t ∈ txs, TxAll (NamesOnly b) t) →
    releasedFor val b.hash (submitAll .deployed init txs).2 ≤ collectedFor val b

/-- **AND EXACTLY THAT ONCE THE BUNDLE IS EXECUTED WHOLE.** Under the same premises, if the
committed log completes a whole-bundle execution of `b.hash`, the handler released for `b` exactly
what the source collected. -/
def Properties.ExecutedBundleReleasesAllCollected : Prop :=
  ∀ (val : CallValues) (b : Bundle) (txs : List Tx), (∀ t ∈ txs, TxAll (NamesOnly b) t) →
    Effect.executed b.hash ∈ (submitAll .deployed init txs).2 →
      releasedFor val b.hash (submitAll .deployed init txs).2 = collectedFor val b

/-- **THE BINDING PREMISE IS LOAD-BEARING.** `wShort` (one call) and `wLong` (two calls) share hash
`5`. The run executing `wLong` violates the premise for `wShort`, and with every call worth `1` the
handler releases `2` against hash `5`, while `wShort`'s source collected `1`. -/
def Properties.SharedHashBreaksTheLedger : Prop :=
  wLong.hash = wShort.hash ∧ wLong ≠ wShort ∧ ¬ TxAll (NamesOnly wShort) wLongRun ∧
    releasedFor (fun _ => 1) wShort.hash (submitAll .deployed init [wLongRun]).2 = 2 ∧
    collectedFor (fun _ => 1) wShort = 1

/-- **THE PREMISES HOLD, AND THE INEQUALITY CAN BE STRICT.** For bundle `wL` (hash `7`, calls worth
`3` and `5`), from fresh storage: the run `verifyBundle`, `unbundleBundle` (execute call 0, cancel
call 1) satisfies the binding premise; it delivers call 0 only; the handler's ledger is
`[(3, Executed), (5, Cancelled)]`; it releases `3` against a collected `8`. Executing `wL` whole
instead releases `8`. -/
def Properties.LedgerWitness : Prop :=
  (∀ t ∈ [wLVerify, wLUnbundle], TxAll (NamesOnly wL) t) ∧
    (submitAll .deployed init [wLVerify, wLUnbundle]).2 = [.delivered 7 0] ∧
    handlerLedger wLVal wL (submitAll .deployed init [wLVerify, wLUnbundle]).1 =
      [(3, .Executed), (5, .Cancelled)] ∧
    releasedFor wLVal wL.hash (submitAll .deployed init [wLVerify, wLUnbundle]).2 = 3 ∧
    collectedFor wLVal wL = 8 ∧
    TxAll (NamesOnly wL) wLExecute ∧
    releasedFor wLVal wL.hash (submitAll .deployed init [wLExecute]).2 = 8

end Contracts.InteropHandler.Faithful
