import EraSpec.Protocol.InteropAtomicity.Specs.OncePerLegAtHead

/-!
# Properties: once per leg, at head

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.OncePerLegAtHead` (`main`
`3605e82`); proofs in `EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLegAtHead`.  As in
`Properties/OncePerLeg.lean`, there is no hash premise and none on `cv`.

## The bridge

`StepsAtHeadIffSteps`: from genesis, the head's runs and the pin's runs reach the same chain
states with the same append logs.  The head has more calls (appends from stale hints) but no
new outcomes, because the hint never decides where the commit value lands.
`SysStepsAtHeadIffSysSteps` is the same for every chain at once.  So every result of
`Properties/OncePerLeg.lean` whose premise is a run from genesis describes the head's runs.
The headlines are restated over the head's relations below, with the head's own insert
wherever the pin's statement names `InsertSucceeds` or `AppendSucceeds`.

## What is new at head: liveness

At the pin an `append` could revert only because of its hint, being out of bounds, above the
value, or more than five hops from the right leaf (`AppendEnabledIff`).  At head the third
reason is gone.  On every reachable state, `append(f, b, .., hint)` passes the manager guard
and the tree's insert exactly when the commit value is nonzero and not a key and the hint is
an occupied index below it (`AppendAtHeadEnabledIff`).  `StaleHintAppendRevertsAtPinSucceedsAtHead`
is the pin's `HonestInsertRevertsAtDeployedFuel` lifted to an `append`: a reachable state of
both models where an append from the sentinel reverts at the pin for every landing index
and succeeds at head.  The pin reaches the same state only when the sender supplies the
landing index as the hint.

## Scope

As in the pin's topic: one chain's run from genesis (or every chain's, for the `System…`
results), every interleaving of the modelled calls.  The head's extra manager checks on
`append` are not modelled here; they only reject calls (see the spec).
-/

namespace Contracts.AppendPath

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund

/-! ## The bridge to the pin's runs -/

/-- **THE HEAD'S RUNS AND THE PIN'S RUNS REACH THE SAME STATES WITH THE SAME LOGS.**  From
genesis, for every commit value and chain. -/
def Properties.StepsAtHeadIffSteps : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    StepsAtHead cv c genesis s log ↔ Steps cv c genesis s log

/-- **THE SAME, FOR EVERY CHAIN AT ONCE.**  From every chain at genesis, the head's system runs
and the pin's reach the same chains with the same append and authorize logs. -/
def Properties.SysStepsAtHeadIffSysSteps : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Y : Chains) (log : List Obligation) (alog : List AuthCall),
    SysStepsAtHead h z0 hl cv fh S genesisAll Y log alog
      ↔ SysSteps h z0 hl cv fh S genesisAll Y log alog

/-- **ON A REACHABLE STATE, A HEAD APPEND IS A PIN APPEND FROM ITS LANDING INDEX.**  Same
landing index, so the same next state. -/
def Properties.AppendAtHeadIsPinAppendAtLanding : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    StepsAtHead cv c genesis s log → ∀ (f b : UInt256) (hint low : ℕ),
      AppendSucceedsAtHead cv s f b hint low → AppendSucceeds cv s f b low low

/-! ## Once per leg, restated -/

/-- **ONCE PER LEG AT HEAD (HEADLINE).**  `OncePerLeg` over the head's runs: for one chain's
run from genesis over every interleaving of center `append`s (from any hint the head
accepts), per-leg `authorizeRefund`s, `claimRefund`s and tree `initL2` calls, for every
commit-value function and with no hash premise:

1. each obligation is appended at most once;
2. each appended obligation is on this chain and occupies exactly one index of its tree;
3. two appended obligations with one commit value are the same obligation. -/
def Properties.OncePerLegAtHead : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    StepsAtHead cv c genesis s log →
      log.Nodup
        ∧ (∀ o ∈ log, o.chain = c
            ∧ ∃! i, i < s.tree.leafCount ∧ (s.tree.leaf i).value = commitOf cv o)
        ∧ (∀ o ∈ log, ∀ o' ∈ log, commitOf cv o = commitOf cv o' → o = o')

/-- **AFTER AN `append`, NEITHER GATE EVER ADMITS THAT LEG AGAIN, AT HEAD.**  `NoSecondAppend`
with the head's insert: after a successful head `append(f, b, .., hint)` and any head
continuation, the manager's guard fails for `(f, b)` and so does the head tree's insert of
`cv f b` from every hint. -/
def Properties.NoSecondAppendAtHead : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation)
    (f b : UInt256) (hint low : ℕ) (t : ChainState) (log' : List Obligation),
    StepsAtHead cv c genesis s log → AppendSucceedsAtHead cv s f b hint low →
    StepsAtHead cv c (s.appended cv f b low) t log' →
      ¬ AppendGuard t.mgr f b ∧ ∀ hint' low', ¬ InsertChecksAtHead t.tree (cv f b) hint' low'

/-- **A LEG PAST `Committed` WAS APPENDED EXACTLY ONCE, AND ITS VALUE IS A KEY, AT HEAD.** -/
def Properties.RefundedLegWasAppendedOnceAtHead : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    StepsAtHead cv c genesis s log → ∀ (f b : UInt256), 2 ≤ rank (s.mgr.legState f b) →
      log.count ⟨f, b, c⟩ = 1 ∧ cv f b ∈ keys (toAbs s.tree)

/-- **A NONZERO KEY IS A LEG THIS CHAIN APPENDED, OR CLASHES WITH ONE, NEVER BOTH, AT HEAD.** -/
def Properties.KeyPinsAppendedLegOrClashAtHead : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    StepsAtHead cv c genesis s log → ∀ (f b : UInt256), cv f b ≠ 0 →
      cv f b ∈ keys (toAbs s.tree) →
      ((⟨f, b, c⟩ : Obligation) ∈ log ∨ ∃ o ∈ log, CommitClash cv ⟨f, b, c⟩ o)
        ∧ ¬ ((⟨f, b, c⟩ : Obligation) ∈ log ∧ ∃ o ∈ log, CommitClash cv ⟨f, b, c⟩ o)

/-- **THE MANAGER'S GUARD IS IMPLIED BY THE HEAD TREE'S.**  On every reachable state, if the
head tree would accept the commit value of `(f, b)` from some hint, the manager has `(f, b)`
`Unset`. -/
def Properties.TreeGateImpliesManagerGateAtHead : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    StepsAtHead cv c genesis s log → ∀ (f b : UInt256) (hint low : ℕ),
      InsertChecksAtHead s.tree (cv f b) hint low → AppendGuard s.mgr f b

/-- **THE TWO GATES DISAGREE EXACTLY ON A LOGGED CLASH, AT HEAD.** -/
def Properties.GatesDisagreeOnlyOnLoggedClashAtHead : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    StepsAtHead cv c genesis s log → ∀ (f b : UInt256), cv f b ≠ 0 →
      ((AppendGuard s.mgr f b ∧ s.tree.valueToIndex (cv f b) ≠ 0)
        ↔ ∃ o ∈ log, CommitClash cv ⟨f, b, c⟩ o)

/-! ## Liveness at head -/

/-- **AT HEAD, AN `append` SUCCEEDS FROM EVERY ADMISSIBLE HINT.**  On every reachable state,
for every leg `(f, b)` and hint: some landing index makes `append(f, b, .., hint)` pass the
manager guard and the head tree's insert exactly when the commit value is nonzero and not yet
a key, and the hint is an occupied index whose value is below the commit value.  The pin
also needed the hint within five hops of the landing index. -/
def Properties.AppendAtHeadEnabledIff : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    StepsAtHead cv c genesis s log → ∀ (f b : UInt256) (hint : ℕ),
      (∃ low, AppendSucceedsAtHead cv s f b hint low)
        ↔ cv f b ≠ 0 ∧ cv f b ∉ keys (toAbs s.tree) ∧ hint < s.tree.leafCount
          ∧ (s.tree.leaf hint).value < cv f b

/-- **A FRESH LEG IS BLOCKED ONLY BY A LOGGED CLASH, AT HEAD.**  `AppendBlockedOnlyByClash`
with the head's append: for a leg `Unset` in the manager with a nonzero commit value, no hint
lets it be appended iff its commit value collides with that of a leg the run appended. -/
def Properties.AppendBlockedOnlyByClashAtHead : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    StepsAtHead cv c genesis s log → ∀ (f b : UInt256), AppendGuard s.mgr f b → cv f b ≠ 0 →
      ((¬ ∃ hint low, AppendSucceedsAtHead cv s f b hint low)
        ↔ ∃ o ∈ log, CommitClash cv ⟨f, b, c⟩ o)

/-- **THE PIN'S STALE-HINT REVERT, AS AN `append`, SUCCEEDS AT HEAD.**  With the commit value
`fun _ b => b` on chain `0`, a state reached by six appends in both models, whose tree is
`chainTree 6`, and the fresh leg `(0, 7)`, `Unset` in the manager:

* from hint `0` (the sentinel), the pin's `append` reverts for every landing index (the
  five-hop search runs out);
* the head's `append` from hint `0` succeeds, landing at index `6`;
* the pin's `append` from hint `6` succeeds, landing at `6`, and reaches the same state. -/
def Properties.StaleHintAppendRevertsAtPinSucceedsAtHead : Prop :=
  ∃ (cv : CommitValue) (s : ChainState) (log : List Obligation) (f b : UInt256),
    Steps cv 0 genesis s log ∧ StepsAtHead cv 0 genesis s log ∧ s.tree = chainTree 6
      ∧ AppendGuard s.mgr f b
      ∧ (∀ low, ¬ AppendSucceeds cv s f b 0 low)
      ∧ AppendSucceedsAtHead cv s f b 0 6
      ∧ AppendSucceeds cv s f b 6 6

/-! ## Every chain at once -/

/-- **ONCE PER LEG, SYSTEM-WIDE, AT HEAD.**  `SystemOncePerLeg` over the head's system runs. -/
def Properties.SystemOncePerLegAtHead : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Y : Chains) (log : List Obligation) (alog : List AuthCall),
    SysStepsAtHead h z0 hl cv fh S genesisAll Y log alog →
      log.Nodup
        ∧ (∀ o ∈ log, ∃! i, i < (Y o.chain).tree.leafCount
            ∧ ((Y o.chain).tree.leaf i).value = commitOf cv o)
        ∧ (∀ o ∈ log, ∀ o' ∈ log, o.chain = o'.chain → commitOf cv o = commitOf cv o' → o = o')

/-- **A REFUNDED OBLIGATION WAS APPENDED EXACTLY ONCE, AND ITS VALUE IS A KEY OF ITS OWN
CHAIN'S TREE, AT HEAD.** -/
def Properties.SystemRefundedWasAppendedOnceAtHead : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Y : Chains) (log : List Obligation) (alog : List AuthCall),
    SysStepsAtHead h z0 hl cv fh S genesisAll Y log alog → ∀ (o : Obligation),
      Refunded Y.mgrs o → log.count o = 1 ∧ commitOf cv o ∈ keys (toAbs (Y o.chain).tree)

/-- **THE REFUND MILESTONE FOR THE SYSTEM WITH TREES, AT HEAD.**
`SystemExecutedObligationNeverRefundedOrBreak` over the head's system runs. -/
def Properties.SystemExecutedObligationNeverRefundedOrBreakAtHead : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System), Wf S → ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Y : Chains) (log : List Obligation) (alog : List AuthCall),
      SysStepsAtHead h z0 hl cv fh S genesisAll Y log alog →
        ¬ Refunded Y.mgrs (obligationOf F leg)
          ∨ RefundBreak h z0 hl fh S F ev (obligationOf F leg) alog

/-! ## Anti-vacuity -/

/-- **A HEAD RUN WITH A STALE-HINT APPEND.**  With commit value `fun _ b => b` on chain `0`:
six honest appends, then the append of `(0, 7)` from the sentinel, which the pin's search
cannot reach.  The run's log has seven entries and its tree eight leaves, so the premises of
the head results are met by a run that uses a call outside the pin's model. -/
def Properties.OncePerLegAtHeadWitness : Prop :=
  ∃ (cv : CommitValue) (s : ChainState) (log : List Obligation),
    StepsAtHead cv 0 genesis s log ∧ log.length = 7 ∧ s.tree.leafCount = 8
      ∧ s.mgr.legState 0 7 = .Committed

end Contracts.AppendPath
