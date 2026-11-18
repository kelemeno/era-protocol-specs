import EraSpec.Protocol.InteropAtomicity.Specs.OncePerLegAtHead

/-!
# Properties: once per leg, at head

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.OncePerLegAtHead` (`main`
`70096e2` and `draft/v0.35.0` `b17415d`; the cited files are unchanged since `3605e82` and
`d9f6789`); proofs in `EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLegAtHead`.  As in
`Properties/OncePerLeg.lean`, there is no hash premise and none on `cv`.

## The bridge

`StepsAtHeadIffSteps`: from genesis, the head's runs and the pin's runs reach the same chain
states with the same append logs.  The head has more calls (appends from stale hints) but no
new outcomes, because on a valid tree the hint never decides where the commit value lands.
`SysStepsAtHeadIffSysSteps` is the same for every chain at once.  So every result of
`Properties/OncePerLeg.lean` whose premise is a run from genesis applies to the head's runs.
The headlines are restated over the head's relations below, with the head's own insert
wherever the pin's statement names `InsertSucceeds` or `AppendSucceeds`.

## What is new at head: which hints pass

`AppendSucceeds` and `AppendSucceedsAtHead` are the manager's `Unset` guard and the tree's
insert of the commit value.  At the pin they could fail for the commit value (zero or already
a key), the guard, or the hint: out of bounds, at a leaf whose value is not below the commit
value, or more than five hops from the right leaf (`AppendEnabledIff`).  At head the last
reason is gone.  On every reachable state some landing index makes `append(f, b, .., hint)`
pass the guard and the tree's insert exactly when the commit value is nonzero and not a key
and the hint is an occupied index whose value is below it (`AppendAtHeadEnabledIff`).
`StaleHintAppendRevertsAtPinSucceedsAtHead` is the pin's `HonestInsertRevertsAtDeployedFuel`
lifted to an `append`: on a state both models reach, an `append` from the sentinel passes the
pin's checks for no landing index and passes the head's.  The pin reaches the same next state
only when the sender supplies the landing index as the hint.  The head's other checks on
`append` and gas are not modelled (see the spec), so these are statements about the modelled
checks, not that a transaction succeeds.

## Scope

As in the pin's topic: one chain's run from genesis (or every chain's, for the `System…`
results), every interleaving of the modelled calls.  The head's extra manager checks only
revert, so the statements about all runs cover the head's runs (see the spec).

## Witnesses

The premise of the one-chain results is `StepsAtHead` from genesis, which is equivalent to
the pin's `Steps` (`StepsAtHeadIffSteps`).  `OncePerLegAtHeadWitness` meets it with a run whose
last `append` is from a stale hint, and `RefundedLegAtHeadWitness` continues that run with an
`authorizeRefund` and a `claimRefund` of the stale-hint leg (the premises of
`RefundedLegWasAppendedOnceAtHead` and, from a stale hint again, of
`TreeGateImpliesManagerGateAtHead`).  `NoSecondAppendAtHeadWitness` meets the premises of
`NoSecondAppendAtHead` with a stale-hint `append` and a nonempty continuation.
`ClashBlocksFreshLegAtHead` meets those of the clash results with both sides of
`AppendBlockedOnlyByClashAtHead` true, and `SystemWitnessAtHead` those of the `System…`
results.
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

/-! ## Enabledness at head: the modelled checks -/

/-- **AT HEAD, AN `append` PASSES THE GUARD AND THE TREE'S CHECKS FROM EVERY ADMISSIBLE HINT.**
On every reachable state, for every leg `(f, b)` and hint: some landing index makes
`append(f, b, .., hint)` pass the manager guard and the head tree's insert
(`AppendSucceedsAtHead`) exactly when the commit value is nonzero and not yet a key, and the
hint is an occupied index whose value is below the commit value.  The pin also needed the hint
within five hops of the landing index.  The head's other checks on `append` and gas are not
part of `AppendSucceedsAtHead`. -/
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

/-- **THE PIN'S STALE-HINT REVERT, AS AN `append`, PASSES THE HEAD'S CHECKS.**  With the commit
value `fun _ b => b` on chain `0`, a state reached by six appends in both models, whose tree
is `chainTree 6`, and the fresh leg `(0, 7)`, `Unset` in the manager:

* from hint `0` (the sentinel), the pin's `AppendSucceeds` holds for no landing index (the
  five-hop search runs out);
* the head's `AppendSucceedsAtHead` from hint `0` holds, landing at index `6`;
* the pin's `AppendSucceeds` from hint `6` holds, landing at `6`, so the pin's step reaches
  the same state. -/
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
cannot reach.  The run's log has seven entries and its tree eight leaves, so the premise of
the one-chain head results is met.  The stale-hint append is in the proof term, not in the
statement: since `StepsAtHeadIffSteps` holds, a pin run of seven appends satisfies the
statement too. -/
def Properties.OncePerLegAtHeadWitness : Prop :=
  ∃ (cv : CommitValue) (s : ChainState) (log : List Obligation),
    StepsAtHead cv 0 genesis s log ∧ log.length = 7 ∧ s.tree.leafCount = 8
      ∧ s.mgr.legState 0 7 = .Committed

/-- **THE STALE-HINT LEG IS REFUNDED, AND A SECOND STALE HINT PASSES.**  The run of
`OncePerLegAtHeadWitness`, then `authorizeRefund` and `claimRefund` of the stale-hint leg
`(0, 7)`: at the end `(0, 7)` is `Reverted` (rank `3 ≥ 2`), the log still has seven entries,
and the tree's head insert accepts the commit value `8` of the fresh leg `(0, 8)` from the
sentinel, landing at index `7` after seven hops, which the pin's search does not.  So the
premises of `RefundedLegWasAppendedOnceAtHead` and `TreeGateImpliesManagerGateAtHead` hold. -/
def Properties.RefundedLegAtHeadWitness : Prop :=
  ∃ (cv : CommitValue) (s : ChainState) (log : List Obligation),
    StepsAtHead cv 0 genesis s log ∧ log.length = 7 ∧ s.mgr.legState 0 7 = .Reverted
      ∧ 2 ≤ rank (s.mgr.legState 0 7)
      ∧ InsertChecksAtHead s.tree (cv 0 8) 0 7
      ∧ ∀ low, lowSearch s.tree (cv 0 8) maxLowIndexSearchAttempts 0 ≠ some low

/-- **`NoSecondAppendAtHead`'S PREMISES HOLD WITH A STALE-HINT `append`.**  On the state of six
appends, the `append` of `(0, 7)` from the sentinel passes the head's checks and the pin's
from no landing index, and after it a continuation with one more `append` (of `(0, 8)`, from
its own low leaf) runs, so the continuation's log is not empty. -/
def Properties.NoSecondAppendAtHeadWitness : Prop :=
  ∃ (cv : CommitValue) (s : ChainState) (log : List Obligation) (f b : UInt256)
    (hint low : ℕ) (t : ChainState) (log' : List Obligation),
    StepsAtHead cv 0 genesis s log ∧ AppendSucceedsAtHead cv s f b hint low
      ∧ (∀ low', ¬ AppendSucceeds cv s f b hint low')
      ∧ StepsAtHead cv 0 (s.appended cv f b low) t log' ∧ log' ≠ []

/-- **A CLASH BLOCKS A FRESH LEG AT HEAD.**  `ClashBlocksFreshLeg` over the head's runs: with the
constant commit value `1`, after appending `(0, 1)` on chain `0`, the leg `(0, 2)` is `Unset`
in the manager, has a nonzero commit value, clashes with the logged `(0, 1)`, and no hint lets
the head's `append` take it.  So both sides of `AppendBlockedOnlyByClashAtHead` hold, and the
clash disjunct of `KeyPinsAppendedLegOrClashAtHead` and the right side of
`GatesDisagreeOnlyOnLoggedClashAtHead` are live. -/
def Properties.ClashBlocksFreshLegAtHead : Prop :=
  ∃ (cv : CommitValue) (s : ChainState) (log : List Obligation) (f b : UInt256),
    StepsAtHead cv 0 genesis s log ∧ cv f b ≠ 0 ∧ cv f b ∈ keys (toAbs s.tree)
      ∧ (⟨f, b, 0⟩ : Obligation) ∉ log ∧ (∃ o ∈ log, CommitClash cv ⟨f, b, 0⟩ o)
      ∧ AppendGuard s.mgr f b ∧ s.tree.valueToIndex (cv f b) ≠ 0
      ∧ (¬ ∃ hint low, AppendSucceedsAtHead cv s f b hint low)

/-- **THE `System…` RESULTS' PREMISES HOLD AT HEAD.**  `SystemWitness` over the head's system
runs: for every node hash, padding constant and leaf hash, a well-formed history, a flow
executed on its evidence, and a head system run from genesis with appends on two chains and a
verified `authorizeRefund` (both logs nonempty, some obligation refunded), in which the
executed obligation is appended, not refunded, and has no `RefundBreak`. -/
def Properties.SystemWitnessAtHead : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (F : Flow) (ev : GateEvidence)
      (leg : FlowLeg) (Y : Chains) (log : List Obligation) (alog : List AuthCall),
      Wf S ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ SysStepsAtHead h z0 hl cv fh S genesisAll Y log alog
        ∧ obligationOf F leg ∈ log ∧ alog ≠ [] ∧ (∃ o, Refunded Y.mgrs o)
        ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) alog
        ∧ ¬ Refunded Y.mgrs (obligationOf F leg)

end Contracts.AppendPath
