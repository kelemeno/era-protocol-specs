import EraSpec.Protocol.InteropAtomicity.Specs.OncePerLeg

/-!
# Properties: each leg is appended once and occupies one tree key

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.OncePerLeg`; proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLeg`.

## What was open

`Protocol/InteropAtomicity/README.md` listed as open: "composing `CommitmentPinsLeg` (once
restated) with the manager's `no_double_append` and the tree's `dedup_gate_sound` into a
once-per-leg result".  `CommitmentPinsLeg` takes `CommitValueInj`, which no commit value
meets (`Contracts.Refund.Properties.CommitValueInjUnsatisfiable`).  Its bounded
restatement `Contracts.Refund.Properties.CommitmentPinsLegOn` takes `CommitValueInjOn cv os`
for an explicit list `os`.  Nothing discharged that premise, so it was recorded as having
no protocol content.

## What a run discharges

Take `os` to be a run's own `append` log.  Then the premise is a theorem
(`Properties.RunRefutesLoggedCommitClash`), with no hash premise.  The tree's dedup gate
turns a commit-value collision between a new leg and a logged one into a revert
(`IMTValueAlreadyExists`), so no two logged obligations ever clash.  So the natural
statement "two logged obligations with one commit value are the same obligation, or a
`CommitClash` holds on their preimages" can drop its clash disjunct:
`Properties.CommitmentPinsLoggedLeg` is the stronger form.  A clash can still matter in one
place: between a leg that was NOT appended and one that was.  There it blocks the new leg's
`append` at every later state, so it costs liveness, never a second key
(`Properties.KeyPinsAppendedLegOrClash`, `Properties.AppendBlockedOnlyByClash`,
`Properties.ClashBlocksFreshLeg`).

The `System…` section lifts all of this to every chain at once, with
`Contracts.Refund`'s verified `authorizeRefund`.  The system's managers are a
`Contracts.Refund.ReachLog` run, so the refund milestones hold for it unchanged.  Each
chain's projection is a run above, so the once-per-leg results hold for each chain.

## Which check does what

* The manager's `ManagerLegAlreadyCommitted` check (`no_double_append`) blocks a second
  `append` of the same `(flowId, bundleHash)`.
* The tree's `IMTValueAlreadyExists` check (`dedup_gate_sound`) blocks it too, since the
  same key has the same commit value.  It also blocks a different key with a colliding
  commit value.
* So on every reachable state the tree's check implies the manager's
  (`Properties.TreeGateImpliesManagerGate`).  The two disagree exactly on a logged clash
  (`Properties.GatesDisagreeOnlyOnLoggedClash`).  Without the tree's check, a clash puts one
  commit value at two indices (`Properties.WithoutDedupClashOccupiesTwoIndices`), and the
  manager's check does not stop it.

## Scope

All results are about one chain's run from `genesis`, and none takes a premise on `cv`.
The `append` steps admit any `(flowId, bundleHash)` and the `authorize` steps drop
`authorizeRefund`'s flow and timeout checks (see the spec).  So every sequence of the
modelled calls that the two contracts accept is a run here, within the spec's model
boundaries.  Obligations on different chains may share a commit value: they live in
different trees, and `CommitClash` ignores the chain.  Which tree holds the value is what
binds the chain field.
-/

namespace Contracts.AppendPath

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund

/-! ## The shape of every run -/

/-- **THE TREE IS THE SENTINEL, THEN ONE LEAF PER `append`, IN ORDER.**  Along every run
from genesis, the tree has one more leaf than the log has entries.  Index 0 holds the
sentinel value `0`.  Index `k + 1` holds the commit value of the `k`-th `append` (counting
from the first, so the log reversed).  So the `k`-th appended leg occupies index `k + 1`. -/
def Properties.RunTreeIsSentinelThenLog : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log →
      s.tree.leafCount = log.length + 1 ∧ (s.tree.leaf 0).value = 0
        ∧ (List.range log.length).map (fun k => (s.tree.leaf (k + 1)).value)
            = log.reverse.map (commitOf cv)

/-- **THE KEY SET IS THE SENTINEL PLUS THE LOGGED COMMIT VALUES.**  Every key of the
chain's tree is `0` or the commit value of an `append` in the run, and every such commit
value is a key.  In the terms of `Protocol/LocalHonesty.lean` this is its links 1 and 2
composed, for this model: the only step that inserts is the center's `append`, so every
nonzero key came from one.  Link 3 (the center builds `bundleHash` with `block.chainid`)
is not modelled here. -/
def Properties.RunKeysAreLoggedCommitValues : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log →
      keys (toAbs s.tree) = Insert.insert 0 (log.map (commitOf cv)).toFinset

/-- **THE MANAGER SAYS `Unset` EXACTLY FOR THE LEGS NEVER APPENDED.**  Every logged
obligation is on the run's chain.  A key `(f, b)` is `Unset` in the manager iff
`⟨f, b, c⟩` is not in the log.  `authorizeRefund` and `claimRefund` move legs only upward
from `Committed`, so no leg goes back to `Unset`. -/
def Properties.RunManagerTracksLog : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log →
      (∀ o ∈ log, o.chain = c)
        ∧ ∀ f b, s.mgr.legState f b = .Unset ↔ (⟨f, b, c⟩ : Obligation) ∉ log

/-- **THE MANAGER HALF OF A RUN IS A MANAGER RUN.**  So every result of
`Contracts/AtomicFlowManager/Properties/Model.lean` (`reach_rank_mono`,
`reverted_absorbing`, `no_double_claim`, `no_double_append`) applies to the composed
system. -/
def Properties.RunProjectsToManagerReach : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s t : ChainState) (log : List Obligation),
    Steps cv c s t log → Contracts.AtomicFlowManager.Reach s.mgr t.mgr

/-- **THE TREE HALF OF A RUN IS A TREE RUN.**  From a valid tree, the tree states of a run
are related by `Reaches` (finitely many guarded inserts).  So `ReachesValid` and
`ReachesKeysMono` apply to the composed system.  `genesis.tree = setup` is valid
(`setup_valid`). -/
def Properties.RunProjectsToTreeReaches : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s t : ChainState) (log : List Obligation),
    Steps cv c s t log → Valid s.tree → Reaches s.tree t.tree

/-- **BATCH SNAPSHOTS OF A RUN HAVE THE `Wf` TREE SHAPE.**  Cut one chain's run at any
sequence of states, for instance its batch ends: the first reachable from genesis, each
next one from the previous.  Their trees meet the `start` and `batch` fields of `Wf`
(`Protocol/InteropAtomicity/Specs/Atomicity.lean`) for that chain.  So the fixed
multi-batch history the atomicity results quantify over can be taken from composed runs. -/
def Properties.RunSnapshotsMeetWfShape : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (snap : ℕ → ChainState),
    (∃ l, Steps cv c genesis (snap 0) l) → (∀ n, ∃ l, Steps cv c (snap n) (snap (n + 1)) l) →
      Reaches setup (snap 0).tree ∧ ∀ n, Reaches (snap n).tree (snap (n + 1)).tree

/-! ## Once per leg -/

/-- **NO OBLIGATION IS APPENDED TWICE.**  The log of every run from genesis has no
repeated entry. -/
def Properties.AppendedAtMostOnce : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log → log.Nodup

/-- **THE RUN DISCHARGES `CommitValueInjOn` ON ITS OWN LOG.**  No two obligations a run
has appended have a `CommitClash`, for every `cv`.  This holds although every `cv` has
collisions (`Contracts.Refund.Properties.UnpinnedCollisionsAlwaysExist`).  The tree refuses
the later leg of a colliding pair (`IMTValueAlreadyExists`), so a colliding pair never gets
into one log. -/
def Properties.RunRefutesLoggedCommitClash : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log → CommitValueInjOn cv log

/-- **`CommitmentPinsLeg`, RESTATED, WITH ITS PREMISE DISCHARGED.**  Two obligations
appended in one run with one commit value are the same obligation, chain included.
`Contracts.Refund.Properties.CommitmentPinsLegOn`, with `os` the run's log and its premise
supplied by `Properties.RunRefutesLoggedCommitClash`, gives the `(flowId, bundleHash)`
part.  The chain part holds because every logged obligation is on the run's chain. -/
def Properties.CommitmentPinsLoggedLeg : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log →
      ∀ o ∈ log, ∀ o' ∈ log, commitOf cv o = commitOf cv o' → o = o'

/-- **EACH LOGGED OBLIGATION OCCUPIES EXACTLY ONE INDEX: THE ONE `valueToIndex` NAMES.**
For every appended obligation, the dedup map points at an occupied, non-sentinel index.
That index is the only occupied index whose leaf carries the obligation's commit value. -/
def Properties.OneIndexPerLoggedObligation : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log → ∀ o ∈ log,
      0 < s.tree.valueToIndex (commitOf cv o)
        ∧ s.tree.valueToIndex (commitOf cv o) < s.tree.leafCount
        ∧ ∀ i < s.tree.leafCount,
            ((s.tree.leaf i).value = commitOf cv o ↔ i = s.tree.valueToIndex (commitOf cv o))

/-- **EACH NONZERO KEY NAMES EXACTLY ONE LOGGED OBLIGATION.**  The converse direction:
every nonzero key of the chain's tree is the commit value of one and only one obligation
the run appended. -/
def Properties.KeyNamesOneLoggedObligation : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log → ∀ v ∈ keys (toAbs s.tree), v ≠ 0 →
      ∃! o, o ∈ log ∧ commitOf cv o = v

/-- **ONCE PER LEG (HEADLINE).**  Take one chain's run from genesis, over every
interleaving of center `append`s, per-leg `authorizeRefund`s, `claimRefund`s and tree
`initL2` calls, for every commit-value function `cv` and with no hash premise.  Then:

1. each obligation is appended at most once;
2. each appended obligation is on this chain and occupies exactly one index of its tree;
3. two appended obligations with one commit value are the same obligation.

Item 3 is "two tree keys equal to the commit values of two logged obligations name the
same obligation, or a `CommitClash` holds on their preimages" without the clash disjunct,
which the run refutes (`Properties.RunRefutesLoggedCommitClash`). -/
def Properties.OncePerLeg : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log →
      log.Nodup
        ∧ (∀ o ∈ log, o.chain = c
            ∧ ∃! i, i < s.tree.leafCount ∧ (s.tree.leaf i).value = commitOf cv o)
        ∧ (∀ o ∈ log, ∀ o' ∈ log, commitOf cv o = commitOf cv o' → o = o')

/-- **AFTER AN `append`, NEITHER GATE EVER ADMITS THAT LEG AGAIN.**  The composed form of
the manager's `no_double_append`.  Take a run from genesis to `s`, a successful
`append(f, b, _, hint)` at `s`, and any continuation from there to `t`.  At `t` the
manager's guard fails for `(f, b)` (`no_double_append`, on the continuation's manager run),
and so does the tree's insert of `cv f b` for every hint (`ReachesKeysMono` keeps the value
a key; `dedup_gate_sound` then refuses it).  Each check alone blocks the second
`append`. -/
def Properties.NoSecondAppend : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation)
    (f b : UInt256) (hint low : ℕ) (t : ChainState) (log' : List Obligation),
    Steps cv c genesis s log → AppendSucceeds cv s f b hint low →
    Steps cv c (s.appended cv f b low) t log' →
      ¬ AppendGuard t.mgr f b ∧ ∀ hint' low', ¬ InsertSucceeds t.tree (cv f b) hint' low'

/-- **A LEG PAST `Committed` WAS APPENDED EXACTLY ONCE, AND ITS VALUE IS A KEY.**  On every
run from genesis, take a leg that is `Revertable` or `Reverted` (the rank test of
`Contracts.Refund.Refunded`).  It appears exactly once in the log, and its commit value is
a key of the chain's tree.  So `claimRefund`, which pays out at most once per leg
(`no_double_claim`), pays out only for a leg this chain's center appended exactly once. -/
def Properties.RefundedLegWasAppendedOnce : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log → ∀ (f b : UInt256), 2 ≤ rank (s.mgr.legState f b) →
      log.count ⟨f, b, c⟩ = 1 ∧ cv f b ∈ keys (toAbs s.tree)

/-! ## What a key says, and when the two gates disagree -/

/-- **A NONZERO KEY OF CHAIN `c`'S TREE IS A LEG CHAIN `c` APPENDED, OR CLASHES WITH ONE,
NEVER BOTH.**  Let `(f, b)` be any flow id and bundle hash, for instance a leg of a flow
presented in calldata, whose commit value is a nonzero key of chain `c`'s tree.  Then either
chain `c` appended `⟨f, b, c⟩`, or `cv` collides on `(f, b)` and an obligation the run
appended.  The two cases exclude each other, and the clash partner, when there is one, is
unique (`Properties.KeyNamesOneLoggedObligation`).

The clash is pinned to the run's own log, not to a free variable.  Neither disjunct is
redundant: `Properties.HonestKeyHasNoClash` has the first without the second, and
`Properties.ClashBlocksFreshLeg` has the second without the first. -/
def Properties.KeyPinsAppendedLegOrClash : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log → ∀ (f b : UInt256), cv f b ≠ 0 → cv f b ∈ keys (toAbs s.tree) →
      ((⟨f, b, c⟩ : Obligation) ∈ log ∨ ∃ o ∈ log, CommitClash cv ⟨f, b, c⟩ o)
        ∧ ¬ ((⟨f, b, c⟩ : Obligation) ∈ log ∧ ∃ o ∈ log, CommitClash cv ⟨f, b, c⟩ o)

/-- **THE MANAGER'S GUARD IS IMPLIED BY THE TREE'S.**  On every reachable state: if the
tree would accept the commit value of `(f, b)`, the manager has `(f, b)` `Unset`.  So the
manager's `ManagerLegAlreadyCommitted` check (`AtomicFlowManager.sol:93`) never decides
whether an `append` succeeds.  It is defense in depth that fails first, before the
external call. -/
def Properties.TreeGateImpliesManagerGate : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log → ∀ (f b : UInt256) (hint low : ℕ),
      InsertSucceeds s.tree (cv f b) hint low → AppendGuard s.mgr f b

/-- **THE TWO GATES DISAGREE EXACTLY ON A LOGGED CLASH.**  For a pair `(f, b)` with a
nonzero commit value, these are equivalent on every reachable state:

* the manager has it `Unset` while the tree's dedup map has its commit value registered;
* its commit value collides with that of an obligation the run appended.

The model's `no_double_append` docstring says this machine and the tree's dedup gate
"agree"; this is the exact sense in which they do. -/
def Properties.GatesDisagreeOnlyOnLoggedClash : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log → ∀ (f b : UInt256), cv f b ≠ 0 →
      ((AppendGuard s.mgr f b ∧ s.tree.valueToIndex (cv f b) ≠ 0)
        ↔ ∃ o ∈ log, CommitClash cv ⟨f, b, c⟩ o)

/-- **WHEN AN `append` CAN SUCCEED.**  On every reachable state, some hint makes
`append(f, b, _, hint)` succeed iff the commit value of `(f, b)` is nonzero and not yet a
key.  The working hint is the index of the leaf whose window straddles the value: the
search then makes no hop, so the deployed fuel of five hops is enough.  So when the commit
value is nonzero and not a key, an `append` that reverts did so only because of its hint
(out of bounds, above the value, or more than five hops from the right leaf). -/
def Properties.AppendEnabledIff : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log → ∀ (f b : UInt256),
      (∃ hint low, AppendSucceeds cv s f b hint low) ↔ cv f b ≠ 0 ∧ cv f b ∉ keys (toAbs s.tree)

/-- **A FRESH LEG IS BLOCKED ONLY BY A LOGGED CLASH.**  Take a leg that is `Unset` in the
manager and has a nonzero commit value.  No hint lets it be appended iff its commit value
collides with that of a leg the run appended.  A collision is a liveness loss for the later
leg, never a second key: its `InteropCenter.sendBundle` (`InteropCenter.sol:262`, through
`_sendBundle` at `:574`) reverts with `IMTValueAlreadyExists`, burn included. -/
def Properties.AppendBlockedOnlyByClash : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (s : ChainState) (log : List Obligation),
    Steps cv c genesis s log → ∀ (f b : UInt256), AppendGuard s.mgr f b → cv f b ≠ 0 →
      ((¬ ∃ hint low, AppendSucceeds cv s f b hint low) ↔ ∃ o ∈ log, CommitClash cv ⟨f, b, c⟩ o)

/-! ## Every chain at once

`SysSteps` interleaves every chain's composed `append`s and `claimRefund`s with
`Contracts.Refund`'s verified `authorizeRefund`s.  Its managers form a
`Contracts.Refund.ReachLog` run with the same authorize log
(`Properties.SystemProjectsToReachLog`), so every result of `Properties/Refund.lean` holds of
it.  Each chain's projection is a `Steps` run (`Properties.SystemProjectsToChainRuns`), so
every result above holds of each chain.  The system-level statements below are the two
combined.  Across chains a commit-value clash is possible and harmless: the two values sit
in different trees (`Properties.SystemWitness`, last conjunct). -/

/-- **EACH CHAIN OF A SYSTEM RUN IS A CHAIN RUN.**  From every chain at genesis, chain `c`'s
state, with the obligations appended on `c`, is a run of chain `c`. -/
def Properties.SystemProjectsToChainRuns : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Y : Chains) (log : List Obligation) (alog : List AuthCall),
    SysSteps h z0 hl cv fh S genesisAll Y log alog →
      ∀ c, Steps cv c genesis (Y c) (log.filter (fun o => o.chain = c))

/-- **THE MANAGERS OF A SYSTEM RUN ARE A LOGGED REFUND RUN, WITH THE SAME AUTHORIZE LOG.**
So the system with its trees attached refines `Contracts.Refund`'s model. -/
def Properties.SystemProjectsToReachLog : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (X Y : Chains) (log : List Obligation) (alog : List AuthCall),
    SysSteps h z0 hl cv fh S X Y log alog → ReachLog h z0 hl cv fh S X.mgrs Y.mgrs alog

/-- **ONCE PER LEG, SYSTEM-WIDE.**  Over every interleaving of every chain's calls:

1. no obligation is appended twice;
2. each appended obligation occupies exactly one index of its own chain's tree;
3. two appended obligations on one chain with one commit value are the same obligation.

Item 3 needs "on one chain": `Properties.SystemWitness` has a cross-chain clash in the
log. -/
def Properties.SystemOncePerLeg : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Y : Chains) (log : List Obligation) (alog : List AuthCall),
    SysSteps h z0 hl cv fh S genesisAll Y log alog →
      log.Nodup
        ∧ (∀ o ∈ log, ∃! i, i < (Y o.chain).tree.leafCount
            ∧ ((Y o.chain).tree.leaf i).value = commitOf cv o)
        ∧ (∀ o ∈ log, ∀ o' ∈ log, o.chain = o'.chain → commitOf cv o = commitOf cv o' → o = o')

/-- **A REFUNDED OBLIGATION WAS APPENDED EXACTLY ONCE, AND ITS VALUE IS A KEY OF ITS OWN
CHAIN'S TREE.**  `Refunded` is `Contracts.Refund`'s: past `Committed` on the obligation's
chain. -/
def Properties.SystemRefundedWasAppendedOnce : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Y : Chains) (log : List Obligation) (alog : List AuthCall),
    SysSteps h z0 hl cv fh S genesisAll Y log alog → ∀ (o : Obligation), Refunded Y.mgrs o →
      log.count o = 1 ∧ commitOf cv o ∈ keys (toAbs (Y o.chain).tree)

/-- **EVERY LOGGED `authorizeRefund` MARKED AN APPENDED OBLIGATION, AND ON ONE CHAIN NO TWO OF
THEM CLASH.**  The obligations the run's authorize log names (the objects of
`Contracts.Refund.RefundBreak`) were all appended, and two of them on one chain have no
`CommitClash`.  This is `Contracts.Refund.Properties.SharedCommitmentYieldsCollision`
pinned to the run: for two obligations drawn from the run's log on one chain, its
collision disjunct is empty.  Across chains two appended obligations can clash
(`Properties.SystemWitness`), harmlessly, since the two values sit in different trees. -/
def Properties.SystemAuthorizedWereAppended : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Y : Chains) (log : List Obligation) (alog : List AuthCall),
    SysSteps h z0 hl cv fh S genesisAll Y log alog →
      (∀ a ∈ alog, obligationOf a.flow a.leg ∈ log)
        ∧ ∀ a ∈ alog, ∀ a' ∈ alog, a.leg.chain = a'.leg.chain →
            ¬ CommitClash cv (obligationOf a.flow a.leg) (obligationOf a'.flow a'.leg)

/-- **A NONZERO KEY OF CHAIN `c`'S TREE IS A LEG APPENDED ON `c`, OR CLASHES WITH ONE,
NEVER BOTH.**  `Properties.KeyPinsAppendedLegOrClash`, on chain `c` of a system run.  The
clash partner is an obligation appended on `c` itself. -/
def Properties.SystemKeyPinsAppendedLegOrClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Y : Chains) (log : List Obligation) (alog : List AuthCall),
    SysSteps h z0 hl cv fh S genesisAll Y log alog →
      ∀ (c : Chain) (f b : UInt256), cv f b ≠ 0 → cv f b ∈ keys (toAbs (Y c).tree) →
        ((⟨f, b, c⟩ : Obligation) ∈ log ∨ ∃ o ∈ log, o.chain = c ∧ CommitClash cv ⟨f, b, c⟩ o)
          ∧ ¬ ((⟨f, b, c⟩ : Obligation) ∈ log
              ∧ ∃ o ∈ log, o.chain = c ∧ CommitClash cv ⟨f, b, c⟩ o)

/-- **THE REFUND MILESTONE HOLDS FOR THE SYSTEM WITH TREES.**
`Contracts.Refund.Properties.ExecutedObligationNeverRefundedOrBreak`, transferred along
`Properties.SystemProjectsToReachLog`.  If leg `leg` of `F` executed on gate evidence `ev`,
its obligation is never past `Committed` in a system run, or a call in the run's authorize
log that marked it carries a `RefundBreak`. -/
def Properties.SystemExecutedObligationNeverRefundedOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System), Wf S → ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Y : Chains) (log : List Obligation) (alog : List AuthCall),
      SysSteps h z0 hl cv fh S genesisAll Y log alog →
        ¬ Refunded Y.mgrs (obligationOf F leg)
          ∨ RefundBreak h z0 hl fh S F ev (obligationOf F leg) alog

/-! ## Anti-vacuity and countermodels

The premise of most results above is only `Steps cv c genesis s log` (or, for the two
projections, a run from `genesis` with `Valid setup`).  `Properties.OncePerLegWitness`
meets it with a two-entry log on which the conclusions have content.  The remaining
premises are covered as follows.

* `NoSecondAppend`: `Properties.NoSecondAppendWitness`.
* `RunSnapshotsMeetWfShape`: `Properties.RunSnapshotsWitness`.
* `RefundedLegWasAppendedOnce`: in `Properties.OncePerLegWitness`, leg `(0, 1)` is
  `Reverted`.
* `KeyPinsAppendedLegOrClash`: `Properties.HonestKeyHasNoClash` (first disjunct only) and
  `Properties.ClashBlocksFreshLeg` (second disjunct only).
* `TreeGateImpliesManagerGate`: the last conjunct of `Properties.OncePerLegWitness`.
* `GatesDisagreeOnlyOnLoggedClash` and `AppendBlockedOnlyByClash`:
  `Properties.ClashBlocksFreshLeg` makes both sides true.  For the first,
  `Properties.HonestKeyHasNoClash` makes both sides false.
* The `System…` results: `Properties.SystemWitness`, a system run with appends on two
  chains and a verified `authorizeRefund`, alongside an executed flow. -/

/-- **A RUN THAT USES EVERY CALL.**  With commit value `fun _ b => b` on chain `0`: append
`(0, 1)` from hint `0`; append `(0, 2)` from hint `0`, which makes the search hop once;
authorize `(0, 1)`; claim `(0, 1)`.  At the end the log is the two appends,
`(0, 1)` is `Reverted`, `(0, 2)` is `Committed`, and the tree would accept the commit value
`3` of `(0, 3)` from hint `2`. -/
def Properties.OncePerLegWitness : Prop :=
  ∃ (cv : CommitValue) (s : ChainState) (log : List Obligation),
    Steps cv 0 genesis s log ∧ log = [⟨0, 2, 0⟩, ⟨0, 1, 0⟩]
      ∧ s.mgr.legState 0 1 = .Reverted ∧ s.mgr.legState 0 2 = .Committed
      ∧ InsertSucceeds s.tree (cv 0 3) 2 2

/-- **`NoSecondAppend`'S PREMISES HOLD TOGETHER, WITH A NONEMPTY CONTINUATION.** -/
def Properties.NoSecondAppendWitness : Prop :=
  ∃ (cv : CommitValue) (s : ChainState) (log : List Obligation) (f b : UInt256)
    (hint low : ℕ) (t : ChainState) (log' : List Obligation),
    Steps cv 0 genesis s log ∧ AppendSucceeds cv s f b hint low
      ∧ Steps cv 0 (s.appended cv f b low) t log' ∧ log' ≠ []

/-- **`RunSnapshotsMeetWfShape`'S PREMISES HOLD WITH A GROWING TREE.**  Snapshots of the run
of `Properties.OncePerLegWitness`: genesis, then after the first append, then the end
state from batch 2 on.  At batch 2 the tree has three leaves. -/
def Properties.RunSnapshotsWitness : Prop :=
  ∃ (cv : CommitValue) (snap : ℕ → ChainState),
    (∃ l, Steps cv 0 genesis (snap 0) l) ∧ (∀ n, ∃ l, Steps cv 0 (snap n) (snap (n + 1)) l)
      ∧ (snap 1).tree.leafCount = 2 ∧ (snap 2).tree.leafCount = 3

/-- **AN HONEST KEY: THE LEG WAS APPENDED, AND THERE IS NO CLASH.**  With commit value
`fun _ b => b`, after appending `(0, 1)` on chain `0`: the key `1` is present, the leg is
in the log, no logged obligation clashes with it, and the gates do not disagree on it.
So the clash disjunct of `Properties.KeyPinsAppendedLegOrClash` is no tautology. -/
def Properties.HonestKeyHasNoClash : Prop :=
  ∃ (cv : CommitValue) (s : ChainState) (log : List Obligation) (f b : UInt256),
    Steps cv 0 genesis s log ∧ cv f b ≠ 0 ∧ cv f b ∈ keys (toAbs s.tree)
      ∧ (⟨f, b, 0⟩ : Obligation) ∈ log ∧ (¬ ∃ o ∈ log, CommitClash cv ⟨f, b, 0⟩ o)
      ∧ ¬ (AppendGuard s.mgr f b ∧ s.tree.valueToIndex (cv f b) ≠ 0)

/-- **A CLASH BLOCKS A FRESH LEG: THE CLASH DISJUNCT IS LIVE.**  With the constant commit
value `1`, after appending `(0, 1)` on chain `0`, consider the leg `(0, 2)`.  Its commit
value is a key, yet it was never appended.  It clashes with the logged `(0, 1)`.  The
manager has it `Unset` while the tree has its value registered, and no hint lets it be
appended.  The log is still clash-free, while the log extended by `(0, 2)` would not
be.  So `Properties.RunRefutesLoggedCommitClash` is a fact about the run, not about `cv`. -/
def Properties.ClashBlocksFreshLeg : Prop :=
  ∃ (cv : CommitValue) (s : ChainState) (log : List Obligation) (f b : UInt256),
    Steps cv 0 genesis s log ∧ cv f b ≠ 0 ∧ cv f b ∈ keys (toAbs s.tree)
      ∧ (⟨f, b, 0⟩ : Obligation) ∉ log ∧ (∃ o ∈ log, CommitClash cv ⟨f, b, 0⟩ o)
      ∧ AppendGuard s.mgr f b ∧ s.tree.valueToIndex (cv f b) ≠ 0
      ∧ (¬ ∃ hint low, AppendSucceeds cv s f b hint low)
      ∧ CommitValueInjOn cv log ∧ ¬ CommitValueInjOn cv (⟨f, b, 0⟩ :: log)

/-- **COUNTERMODEL: WITHOUT THE DEDUP CHECK, A CLASH OCCUPIES TWO INDICES.**  In the same
clashing state as `Properties.ClashBlocksFreshLeg`, the manager's guard is open for
`(0, 2)`.  Every check of the tree's `insert` except `IMTValueAlreadyExists` passes for its
commit value, and the real `insert` refuses it.  Were that one check absent, the `append`
would go through, and the commit value would then sit at two indices, so
`Properties.OneIndexPerLoggedObligation` would fail.  The manager's check does not prevent
this; the tree's dedup check is load-bearing. -/
def Properties.WithoutDedupClashOccupiesTwoIndices : Prop :=
  ∃ (cv : CommitValue) (s : ChainState) (log : List Obligation) (f b : UInt256) (hint low : ℕ),
    Steps cv 0 genesis s log ∧ (∃ o ∈ log, CommitClash cv ⟨f, b, 0⟩ o)
      ∧ AppendGuard s.mgr f b ∧ InsertSucceedsWithoutDedup s.tree (cv f b) hint low
      ∧ ¬ InsertSucceeds s.tree (cv f b) hint low
      ∧ ¬ ∃! i, i < (s.appended cv f b low).tree.leafCount
            ∧ ((s.appended cv f b low).tree.leaf i).value = cv f b

/-- **A SYSTEM RUN WITH BOTH LOGS NONEMPTY, AND A HARMLESS CROSS-CHAIN CLASH.**  For every
node hash, padding constant and leaf hash, take the constant commit value `1`,
`lengthFlowHash` and the fixed history `mixedSystem 1`.  The flow `subsetFlow 0 1` executes
on honest evidence, and its leg is appended on chain `0`.  The leg `⟨1, 2⟩` of the different
flow `mixedFlow 1 1 2` is appended on chain `1` and then authorized for refund on a verified
timeout.  So the premises of every `System…` result hold with both logs nonempty and a
refunded obligation.  The executed obligation is not refunded and no `RefundBreak` is
located for it.  The two appended obligations clash (both commit values are `1`) although
both were appended; they sit on different chains, which is why `Properties.SystemOncePerLeg`
item 3 needs "on one chain". -/
def Properties.SystemWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (F : Flow) (ev : GateEvidence)
      (leg : FlowLeg) (Y : Chains) (log : List Obligation) (alog : List AuthCall),
      Wf S ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ SysSteps h z0 hl cv fh S genesisAll Y log alog
        ∧ obligationOf F leg ∈ log ∧ alog ≠ [] ∧ (∃ o, Refunded Y.mgrs o)
        ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) alog
        ∧ ¬ Refunded Y.mgrs (obligationOf F leg)
        ∧ ∃ o ∈ log, ∃ o' ∈ log, CommitClash cv o o'

end Contracts.AppendPath
