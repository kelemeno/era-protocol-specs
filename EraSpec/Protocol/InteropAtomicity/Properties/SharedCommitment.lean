import EraSpec.Protocol.InteropAtomicity.Specs.SharedCommitment

/-!
# Properties: what a shared commitment means, on a run, at the gate and at the timeout check

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.SharedCommitment`; proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.SharedCommitment`.

## What is repaired

`Contracts.Refund.Properties.SharedCommitmentYieldsCollision` ends in an unpinned "some collision
exists", which every commit value meets (`Contracts.Refund.Properties.UnpinnedCollisionsAlwaysExist`).
Its pinned form, `Contracts.Refund.Properties.CommitmentPinsLegOrCollision`, is excluded middle,
and stays so when the two obligations are drawn from a run's log (see the spec header).  The
statements below have content because the run decides them.

## On a run

* **Within one chain a shared commitment is impossible, and that is the only constraint.**
  `Properties.ChainLogIffAppendable`: a list is the `append` log of some run of chain `c` iff its
  entries are on `c`, have nonzero commit values, appear once and have no `CommitClash` among
  them.  `Properties.SystemLogIffAppendablePerChain` is the same for every chain at once, chain by
  chain.  The forward directions are topic `OncePerLeg`'s; the converses are new: every such list
  is realized by a run.
* **The headline.**  `Properties.SharedCommitmentCoexistsIffCrossChain`: two distinct obligations
  with one nonzero commit value can both be appended in one system run iff they are on different
  chains.  `Properties.SharedCommitmentPinnedToRun` is the backlog sketch's shape with that
  content: two obligations drawn from a system run's logs (both the `append` log and the
  `authorizeRefund` log) with one commit value are the same obligation, or they sit on different
  chains, where the shared value is either the same leg on two chains or a `CommitClash` on exactly
  those two obligations.
* **Both cross-chain cases occur**, with both logs nonempty
  (`Properties.SharedCommitmentSameLegTwoChainsWitness`, under a commit value with no clash in the
  run, and `Properties.SharedCommitmentCrossChainClashWitness`).  For every duplicate-free list of
  obligations on one chain there is a commit value with no clash on it under which the list is a
  run's log (`Properties.HonestCommitValueRealizesChainLog`), so the clash disjunct is false on
  nonempty logs.
* **The tree is what refutes the same-chain clash.**  The managers alone, i.e.
  `Contracts.Refund.ReachLog`, whose `append` is the manager's guard only, reach an authorize log
  marking two clashing obligations on one chain, and no run with trees attached has that log
  (`Properties.SharedCommitmentManagersAloneAdmitSameChainClash`).

## At the gate

`requireFlowFinalized` checks that each leg's commit value is in its declared chain's batch-end
tree.  If that tree is the tree of a run of the chain (`HistoryFromRuns`), the value names what
was appended there.  `Properties.GateLegWasAppendedOrClash`: a leg that passes the inclusion check
was appended on its declared chain by that batch, or `cv` collides on that leg and a leg appended
there, or the leg's commit value is the sentinel `0`, or the submitted proof carries a located
`InclusionBreak`.  `Properties.ExecutedFlowLegsWereAppendedOrClash` is the flow form: when any
leg executes, every leg of the flow was appended on its own declared chain, up to the same three
located exceptions on that leg.  No hash premise is taken.

Each exception is needed.  In `Properties.SharedCommitmentClashLetsUnappendedLegExecute`,
`Properties.SharedCommitmentZeroLetsUnappendedLegExecute` and
`Properties.SharedCommitmentForgedProofLetsUnappendedLegExecute`, a leg that no chain ever
appended executes, and exactly one exception holds.  `Properties.SharedCommitmentGateWitness` meets
the premises with all three exceptions false.  `Properties.SystemHistoryIsHistoryFromRuns` and
`Properties.ExecutedFlowLegsWereAppendedInSystemOrClash` state the same for a history cut from one
run of topic `OncePerLeg`'s system model, including one whose refund checks consult that same
history (`Properties.SystemHistoryWitness`).

## At the timeout check

The timeout check is the other way round.
`Properties.TimeoutAbsenceExcludesSharedCommitmentOrBreak`: if `authorizeRefund`'s absence proof
for a missing leg passes, no obligation appended behind the checked root shares that leg's commit
value, or the proof carries a located `AbsenceBreak`.  There is no clash exception: a shared value
sits in the tree, so it can only make absence fail.  `Properties.TimeoutAbsenceWitness` meets the
premises on a nonempty log with the break false.  `Properties.SharedCommitmentClashBlocksTimeout`
shows the cost: a never-appended leg whose value clashes with an appended one cannot be timed out
without a break, and its flow executes instead.

A commit-value collision therefore costs liveness at `append` (topic `OncePerLeg`,
`AppendBlockedOnlyByClash`) and at the timeout check.  It costs safety at the inclusion check, where
it lets a leg with nothing appended behind it pass.

## The source's claim

The source says "a leg's commit value can only be inserted into its own source chain's tree"
(`AtomicInteropProof.sol:107-110`).  In this model that holds up to a pinned keccak collision with a
leg appended on that chain, or a keccak preimage of `0`.  The zero case is there because
`IndexedMerkleTree.verifyInclusion` (`IndexedMerkleTree.sol:133-145`) has no `_value != 0` check,
unlike `insert` (`:69-71`) and `verifyNonInclusion` (`:160-162`).  Index 0 of every initialized
tree holds the sentinel, whose value is `0`: `setup` writes `{0, 0, 0}` (`:42-51`), and `insert`
rewrites only a low leaf's `nextIndex` and `nextValue` (`:96-100`).  So a zero commit value would
verify against every chain's tree.  The chain-specific `bundleHash` half of the source's argument
(`interop/InteropCenter.sol:644`) is not modelled (backlog S4): in the model one
`(flowId, bundleHash)` can be appended on two chains
(`Properties.SharedCommitmentSameLegTwoChainsWitness`).
-/

namespace Contracts.SharedCommitment

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.AppendPath

/-! ## Which logs a run can have -/

/-- **ONE CHAIN'S `append` LOGS ARE EXACTLY THE CLASH-FREE ONES.**  For every commit value `cv`
and chain `c`, a list of obligations is the `append` log of some run of chain `c` from `genesis`
(`Contracts.AppendPath.Steps`, every interleaving of center `append`s, per-leg
`authorizeRefund`s, `claimRefund`s and `initL2`) iff it is an `AppendableLog`: its entries are on
`c`, have nonzero commit values, appear once, and have no `CommitClash` among them.

The forward direction is `Contracts.AppendPath.Properties.RunRefutesLoggedCommitClash` with its
companions.  The converse says the append path rules out nothing else: no ordering constraint, no
bound beyond the commit values.  A `CommitClash` within one chain is therefore exactly what a run's
log can never contain. -/
def Properties.ChainLogIffAppendable : Prop :=
  ∀ (cv : CommitValue) (c : Chain) (log : List Obligation),
    (∃ s, Steps cv c genesis s log) ↔ AppendableLog cv c log

/-- **A SYSTEM RUN'S `append` LOG IS CLASH-FREE CHAIN BY CHAIN, AND THAT IS ALL.**  A list of
obligations is the `append` log of some run of every chain at once
(`Contracts.AppendPath.SysSteps`, with any authorize log) iff, for every chain `c`, its entries on
`c` form an `AppendableLog` for `c`.  Nothing constrains entries on different chains against each
other: they may share a commit value, whether as the same `(flowId, bundleHash)` or through a
`CommitClash`. -/
def Properties.SystemLogIffAppendablePerChain : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (log : List Obligation),
    (∃ (Y : Chains) (alog : List AuthCall), SysSteps h z0 hl cv fh S genesisAll Y log alog)
      ↔ ∀ c, AppendableLog cv c (log.filter (fun o => o.chain = c))

/-- **AN HONEST COMMIT VALUE REALIZES EVERY LOG.**  For every list of obligations on one chain `c`
that has no repeated entry and fewer than `2^256` entries, there is a commit value with no
`CommitClash` among the list's entries under which the list is the `append` log of a run of `c`.
So the clash disjunct of the sketch is false on every such log, nonempty ones included.

`Contracts.Refund.honestCommitValue o` is not used: it gives `o` itself the value `0`, which the
tree refuses (`IMTValueZero`), so `o` could never be logged under it. -/
def Properties.HonestCommitValueRealizesChainLog : Prop :=
  ∀ (c : Chain) (os : List Obligation), (∀ o ∈ os, o.chain = c) → os.Nodup →
    os.length < UInt256.size →
      ∃ cv : CommitValue, CommitValueInjOn cv os ∧ ∃ s, Steps cv c genesis s os

/-- **ITS PREMISES HOLD ON A LOG THAT A CONSTANT COMMIT VALUE COULD NOT PRODUCE.**  A two-entry list
on chain `0` meets the premises of `Properties.HonestCommitValueRealizesChainLog`, yet has a
`CommitClash` under the constant commit value `1`, so by `Properties.ChainLogIffAppendable` no run
under that commit value has it as its log.  The honest commit value is what makes it a log. -/
def Properties.HonestCommitValueRealizesChainLogWitness : Prop :=
  ∃ (c : Chain) (os : List Obligation), (∀ o ∈ os, o.chain = c) ∧ os.Nodup
    ∧ os.length < UInt256.size ∧ os.length = 2 ∧ ¬ CommitValueInjOn (fun _ _ => 1) os

/-! ## What a shared commitment means in a run -/

/-- **A SHARED COMMITMENT BETWEEN TWO LOGGED OBLIGATIONS IS ONE OBLIGATION, OR IT CROSSES CHAINS.**
The pinned restatement of `Contracts.Refund.Properties.SharedCommitmentYieldsCollision` on a run.
Take any system run from `genesisAll` (`Contracts.AppendPath.SysSteps`; its managers form a
`Contracts.Refund.ReachLog` run with the same authorize log,
`Contracts.AppendPath.Properties.SystemProjectsToReachLog`).  Take two obligations drawn from its
logs (`runObligations`: the `append` log and the obligations the logged `authorizeRefund` calls
marked) with one commit value.  Then they are the same obligation, or they are on different chains
and are either the same leg there (equal `(flowId, bundleHash)`) or a `CommitClash` on exactly
these two.

Once the commit values are equal, the inner disjunction (the same leg, or a `CommitClash`) is
excluded middle.  The content is the chain condition: two obligations on one chain can only be
equal.  The tree's `IMTValueAlreadyExists` check refuses the later of two clashing appends on one
chain, and every marked obligation was appended
(`Contracts.AppendPath.Properties.SystemAuthorizedWereAppended`).  Both cross-chain cases occur
(`Properties.SharedCommitmentSameLegTwoChainsWitness`,
`Properties.SharedCommitmentCrossChainClashWitness`). -/
def Properties.SharedCommitmentPinnedToRun : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (Y : Chains) (log : List Obligation) (alog : List AuthCall),
    SysSteps h z0 hl cv fh S genesisAll Y log alog →
      ∀ o ∈ runObligations log alog, ∀ o' ∈ runObligations log alog,
        commitOf cv o = commitOf cv o' →
          o = o' ∨ (o.chain ≠ o'.chain
            ∧ ((o.flowId = o'.flowId ∧ o.bundleHash = o'.bundleHash) ∨ CommitClash cv o o'))

/-- **A SHARED COMMITMENT CAN BE APPENDED TWICE IFF IT CROSSES CHAINS (HEADLINE).**  Let `o` and
`o'` be distinct obligations with one nonzero commit value.  Some run of every chain at once
appends both iff `o` and `o'` are on different chains.

Both directions have content.  Left to right is the once-per-leg result of topic `OncePerLeg`: on
one chain the tree refuses the second value.  Right to left says a value shared across chains is
never refused, since the two values sit in different trees.  This holds whether the two are the
same leg on two chains or a `CommitClash`.  Which tree holds the value is what binds the chain
field (`Properties.GateLegWasAppendedOrClash`). -/
def Properties.SharedCommitmentCoexistsIffCrossChain : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (o o' : Obligation), o ≠ o' → commitOf cv o = commitOf cv o' → commitOf cv o ≠ 0 →
      ((∃ (Y : Chains) (log : List Obligation) (alog : List AuthCall),
          SysSteps h z0 hl cv fh S genesisAll Y log alog ∧ o ∈ log ∧ o' ∈ log)
        ↔ o.chain ≠ o'.chain)

/-- **BOTH SIDES OF THE HEADLINE OCCUR.**  For every node hash, padding constant and leaf hash
there are a commit value and three obligations `o`, `o'`, `o''`, all with one nonzero commit value
and `o` distinct from the other two.  Some system run appends both `o` and `o'`, which are on
different chains.  No system run appends both `o` and `o''`, which are on one chain. -/
def Properties.SharedCommitmentCoexistsIffCrossChainWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (o o' o'' : Obligation),
      o ≠ o' ∧ o ≠ o'' ∧ commitOf cv o = commitOf cv o' ∧ commitOf cv o = commitOf cv o''
        ∧ commitOf cv o ≠ 0
        ∧ (∃ (Y : Chains) (log : List Obligation) (alog : List AuthCall),
            SysSteps h z0 hl cv fh S genesisAll Y log alog ∧ o ∈ log ∧ o' ∈ log)
        ∧ ¬ (∃ (Y : Chains) (log : List Obligation) (alog : List AuthCall),
            SysSteps h z0 hl cv fh S genesisAll Y log alog ∧ o ∈ log ∧ o'' ∈ log)

/-- **THE SAME LEG ON TWO CHAINS, WITH NO CLASH ANYWHERE IN THE RUN.**  For every node hash,
padding constant and leaf hash there is a system run whose two logs are both nonempty, and two
distinct obligations drawn from them with one commit value, which are the same leg on two chains.
No two obligations drawn from the run's logs have a `CommitClash`.  So the premises of
`Properties.SharedCommitmentPinnedToRun` hold with `o ≠ o'`, and its clash disjunct is false on
the whole run. -/
def Properties.SharedCommitmentSameLegTwoChainsWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (Y : Chains) (log : List Obligation)
      (alog : List AuthCall) (o o' : Obligation),
      SysSteps h z0 hl cv fh S genesisAll Y log alog ∧ log ≠ [] ∧ alog ≠ []
        ∧ o ∈ runObligations log alog ∧ o' ∈ runObligations log alog
        ∧ commitOf cv o = commitOf cv o' ∧ o ≠ o'
        ∧ (o.flowId = o'.flowId ∧ o.bundleHash = o'.bundleHash)
        ∧ CommitValueInjOn cv (runObligations log alog)

/-- **A CROSS-CHAIN CLASH IN ONE RUN.**  For every node hash, padding constant and leaf hash there
is a system run whose `append` log holds two obligations on different chains with a `CommitClash`.
So the clash disjunct of `Properties.SharedCommitmentPinnedToRun` is live, and the "on one chain"
restriction is needed. -/
def Properties.SharedCommitmentCrossChainClashWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (Y : Chains) (log : List Obligation)
      (alog : List AuthCall) (o o' : Obligation),
      SysSteps h z0 hl cv fh S genesisAll Y log alog
        ∧ o ∈ runObligations log alog ∧ o' ∈ runObligations log alog
        ∧ CommitClash cv o o' ∧ o.chain ≠ o'.chain

/-- **COUNTERMODEL: THE MANAGERS ALONE DO NOT REFUTE A SAME-CHAIN CLASH.**  For every node hash,
padding constant and leaf hash, `Contracts.Refund.ReachLog` (every chain's manager, each
`authorizeRefund` verified against the fixed history, `append` guarded by the manager's
`ManagerLegAlreadyCommitted` check only) reaches an authorize log with two calls that mark two
obligations on one chain with a `CommitClash`.  No run with the trees attached
(`Contracts.AppendPath.SysSteps`, same parameters) has that authorize log.  So
`Properties.SharedCommitmentPinnedToRun` needs the composed model: its same-chain content is the
tree's `IMTValueAlreadyExists` check (`IndexedMerkleTree.sol:72-74`), not the manager's guard. -/
def Properties.SharedCommitmentManagersAloneAdmitSameChainClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (Ms : Managers) (alog : List AuthCall)
      (a a' : AuthCall),
      ReachLog h z0 hl cv fh S emptyManagers Ms alog ∧ a ∈ alog ∧ a' ∈ alog
        ∧ a.leg.chain = a'.leg.chain
        ∧ CommitClash cv (obligationOf a.flow a.leg) (obligationOf a'.flow a'.leg)
        ∧ ∀ (Y : Chains) (log : List Obligation), ¬ SysSteps h z0 hl cv fh S genesisAll Y log alog

/-! ## What a shared commitment means at the gate -/

/-- **A LEG THAT PASSES THE INCLUSION CHECK WAS APPENDED ON ITS DECLARED CHAIN, OR A LOCATED
EXCEPTION.**  Let chain `leg.chain`'s batch-`n` tree in `S` be the tree of a state `s` that chain
`leg.chain` reaches from `genesis` with `append` log `l`.  Suppose `requireFlowFinalized`'s check
for leg `leg` of the presented flow `F` passes on batch `n` with inclusion proof `p`
(`LegFinalizedBy`: the batch is on time, and `verifyInclusion` accepts `p` for the leg's commit
value against that batch's end root).  Then one of:

* `obligationOf F leg ∈ l`: chain `leg.chain` appended this very obligation;
* `cv` collides on this leg's `(flowId, bundleHash)` and on an obligation in `l` (`CommitClash`,
  both inputs named);
* the leg's commit value is `0`, the value of the sentinel leaf every initialized tree holds at
  index 0;
* `p` carries a located `TreeRootBreak` (`InclusionBreak`).

The first two exclude each other on every run. -/
def Properties.GateLegWasAppendedOrClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (F : Flow)
    (leg : FlowLeg) (n : ℕ) (p : ImtProof) (s : ChainState) (l : List Obligation),
    Steps cv leg.chain genesis s l → S.tree leg.chain n = s.tree →
    LegFinalizedBy h z0 hl cv S F leg n p →
      (obligationOf F leg ∈ l ∨ (∃ o ∈ l, CommitClash cv (obligationOf F leg) o)
          ∨ legValue cv F leg = 0 ∨ InclusionBreak h z0 hl S leg.chain n p)
        ∧ ¬ (obligationOf F leg ∈ l ∧ ∃ o ∈ l, CommitClash cv (obligationOf F leg) o)

/-- **WHEN ONE LEG EXECUTES, EVERY LEG OF THE FLOW WAS APPENDED ON ITS OWN DECLARED CHAIN, OR A
LOCATED EXCEPTION ON THAT LEG.**  Let the history `S` be read off runs (`HistoryFromRuns`) and let
leg `leg` of `F` execute on gate evidence `ev` (`ExecutedViaBy`: `_checkFlowId` passed and every
leg's inclusion check passed).  Then for every leg `other` of `F`, at the batch `(ev other).1` the
gate cited for it, one of:

* `other`'s obligation is in the `append` log of chain `other.chain` at that batch;
* `cv` collides on `other`'s `(flowId, bundleHash)` and on an obligation in that log;
* `other`'s commit value is `0`;
* the inclusion proof `(ev other).2` carries a located `InclusionBreak`.

No hash premise is taken.  With a commit value that has no collision on those inputs and never
takes the value `0`, and honest proofs, the result is "no leg executes unless every leg of its
flow was appended on its declared chain". -/
def Properties.ExecutedFlowLegsWereAppendedOrClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (snap : Chain → ℕ → ChainState) (logAt : Chain → ℕ → List Obligation),
    HistoryFromRuns cv S snap logAt →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
      ∀ other ∈ F.legs,
        obligationOf F other ∈ logAt other.chain (ev other).1
          ∨ (∃ o ∈ logAt other.chain (ev other).1, CommitClash cv (obligationOf F other) o)
          ∨ legValue cv F other = 0
          ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2

/-- **A HISTORY CUT FROM ONE SYSTEM RUN IS READ OFF RUNS.**  If every batch of `S` is the trees of
a state of one `SysSteps` run from `genesisAll` (`HistoryFromSystemRun`), then `S` meets
`HistoryFromRuns`, with chain `c`'s log at batch `n` being the system's `append` log at batch `n`
filtered to chain `c` (`Contracts.AppendPath.Properties.SystemProjectsToChainRuns`).  So the gate
results apply to the system model of topic `OncePerLeg`, whose `authorizeRefund`s are verified. -/
def Properties.SystemHistoryIsHistoryFromRuns : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S' S : System)
    (snapY : ℕ → Chains) (logs : ℕ → List Obligation) (alogs : ℕ → List AuthCall),
    HistoryFromSystemRun h z0 hl cv fh S' S snapY logs alogs →
      HistoryFromRuns cv S (fun c n => snapY n c) (fun c n => (logs n).filter (fun o => o.chain = c))

/-- **`Properties.ExecutedFlowLegsWereAppendedOrClash` ON A HISTORY CUT FROM ONE SYSTEM RUN.**  When
any leg of `F` executes, every leg `other` of `F` has its obligation in the system's `append` log at
the batch the gate cited for it, or `cv` collides on `other` and an obligation appended on
`other.chain` by then, or `other`'s commit value is `0`, or its proof carries a located break. -/
def Properties.ExecutedFlowLegsWereAppendedInSystemOrClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S' S : System)
    (snapY : ℕ → Chains) (logs : ℕ → List Obligation) (alogs : ℕ → List AuthCall),
    HistoryFromSystemRun h z0 hl cv fh S' S snapY logs alogs →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
      ∀ other ∈ F.legs,
        obligationOf F other ∈ logs (ev other).1
          ∨ (∃ o ∈ logs (ev other).1, o.chain = other.chain
              ∧ CommitClash cv (obligationOf F other) o)
          ∨ legValue cv F other = 0
          ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2

/-- **THE SYSTEM FORM'S PREMISES HOLD, WITH `S' = S` AND EVERY EXCEPTION FALSE.**  For every node
hash, padding constant and leaf hash: a well-formed history cut from one system run, whose refund
checks consult that same history, in which chain `0` appended one leg; a one-leg flow on chain `0`
executes on the honest inclusion proof.  Its leg's obligation is in the system's `append` log at
the cited batch, no obligation appended on its chain clashes with it, its commit value is nonzero,
and its proof carries no break. -/
def Properties.SystemHistoryWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (snapY : ℕ → Chains)
      (logs : ℕ → List Obligation) (alogs : ℕ → List AuthCall) (F : Flow) (ev : GateEvidence)
      (leg : FlowLeg),
      Wf S ∧ HistoryFromSystemRun h z0 hl cv fh S S snapY logs alogs
        ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ ∀ other ∈ F.legs, obligationOf F other ∈ logs (ev other).1
            ∧ ¬ (∃ o ∈ logs (ev other).1, o.chain = other.chain
                ∧ CommitClash cv (obligationOf F other) o)
            ∧ legValue cv F other ≠ 0
            ∧ ¬ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2

/-- **THE GATE RESULT'S PREMISES HOLD WITH EVERY EXCEPTION FALSE.**  For every node hash, padding
constant and leaf hash: a well-formed history read off runs, in which chain `0` appended one leg;
a one-leg flow on chain `0` executes on the honest inclusion proof.  For every leg of the flow, its
obligation is in the log at the cited batch, no logged obligation clashes with it, its commit
value is nonzero, and its proof carries no break. -/
def Properties.SharedCommitmentGateWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (snap : Chain → ℕ → ChainState)
      (logAt : Chain → ℕ → List Obligation) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
      Wf S ∧ HistoryFromRuns cv S snap logAt ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ ∀ other ∈ F.legs, obligationOf F other ∈ logAt other.chain (ev other).1
            ∧ ¬ (∃ o ∈ logAt other.chain (ev other).1, CommitClash cv (obligationOf F other) o)
            ∧ legValue cv F other ≠ 0
            ∧ ¬ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2

/-- **COUNTERMODEL: A CLASH LETS A NEVER-APPENDED LEG EXECUTE.**  For every node hash, padding
constant and leaf hash: in a well-formed history read off runs, a one-leg flow executes on an
honest inclusion proof although no chain ever appended its leg.  Its commit value equals that of
the leg chain `0` did append, and that `CommitClash`, pinned to the logged obligation, is the only
exception that holds: the value is nonzero and the proof has no break.  So the clash disjunct of
`Properties.GateLegWasAppendedOrClash` cannot be dropped: the inclusion gate relies on the commit
value having no collision between the presented leg and an appended one. -/
def Properties.SharedCommitmentClashLetsUnappendedLegExecute : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (snap : Chain → ℕ → ChainState)
      (logAt : Chain → ℕ → List Obligation) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
      Wf S ∧ HistoryFromRuns cv S snap logAt ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ (∀ c n, obligationOf F leg ∉ logAt c n)
        ∧ (∃ o ∈ logAt leg.chain (ev leg).1, CommitClash cv (obligationOf F leg) o)
        ∧ legValue cv F leg ≠ 0
        ∧ ¬ InclusionBreak h z0 hl S leg.chain (ev leg).1 (ev leg).2

/-- **COUNTERMODEL: A ZERO COMMIT VALUE LETS A NEVER-APPENDED LEG EXECUTE.**  For every node hash,
padding constant and leaf hash: in a well-formed history read off runs, a one-leg flow whose commit
value is `0` executes on the honest inclusion proof of the sentinel leaf at index 0, although no
chain ever appended its leg.  No logged obligation clashes with it and the proof has no break.  The
contract's `verifyInclusion` has no zero check (`IndexedMerkleTree.sol:133-145`), unlike `insert`
(`:69-71`) and `verifyNonInclusion` (`:160-162`).  So "finalized" rests on `commitValue` never
being `0`, a keccak preimage of zero on the leg's own `abi.encode(TAG, flowId, bundleHash)`. -/
def Properties.SharedCommitmentZeroLetsUnappendedLegExecute : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (snap : Chain → ℕ → ChainState)
      (logAt : Chain → ℕ → List Obligation) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
      Wf S ∧ HistoryFromRuns cv S snap logAt ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ (∀ c n, obligationOf F leg ∉ logAt c n)
        ∧ ¬ (∃ o ∈ logAt leg.chain (ev leg).1, CommitClash cv (obligationOf F leg) o)
        ∧ legValue cv F leg = 0
        ∧ ¬ InclusionBreak h z0 hl S leg.chain (ev leg).1 (ev leg).2

/-! ## What a shared commitment means at the timeout check -/

/-- **A PASSING TIMEOUT CHECK MEANS NO APPENDED LEG SHARES THE MISSING LEG'S COMMIT VALUE, OR A
LOCATED BREAK.**  Let the history `S` be read off runs (`HistoryFromRuns`) and let
`authorizeRefund`'s timeout check pass for leg `m` of `F` on batch `N` with absence proof `p`
(`LegRefundableBy`: absence from the BEGIN root of a late batch, or from the END root of the last
on-time batch).  Then no obligation in the `append` log behind the root the check used
(`absenceLog`) has `m`'s commit value, or `p` carries a located `AbsenceBreak` on that root.  In
particular `m`'s own obligation was not appended by then.

Unlike `Properties.GateLegWasAppendedOrClash` there is no clash exception, and no zero exception
(`verifyNonInclusion` refuses `0`).  A shared commitment puts the missing leg's value into the tree,
so it can only make an absence proof fail.  On the timeout side a commit-value collision costs
liveness (`Properties.SharedCommitmentClashBlocksTimeout`) and never yields a refund the run does
not justify. -/
def Properties.TimeoutAbsenceExcludesSharedCommitmentOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System)
    (snap : Chain → ℕ → ChainState) (logAt : Chain → ℕ → List Obligation),
    HistoryFromRuns cv S snap logAt →
    ∀ (F : Flow) (m : FlowLeg) (N : ℕ) (p : ImtProof), LegRefundableBy h z0 hl cv S F m N p →
      (∀ o ∈ absenceLog logAt S F.deadline m.chain N, commitOf cv o ≠ legValue cv F m)
        ∨ AbsenceBreak h z0 hl S F.deadline m.chain N p

/-- **THE TIMEOUT RESULT'S PREMISES HOLD ON A NONEMPTY LOG, WITH THE BREAK FALSE.**  For every node
hash, padding constant and leaf hash: in a history read off runs in which chain `0` appended one
leg, the timeout check passes for a different, never-appended leg of chain `0` on the honest absence
proof, against a root whose log is nonempty.  No logged obligation shares the missing leg's commit
value, and the proof carries no break. -/
def Properties.TimeoutAbsenceWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (S : System) (snap : Chain → ℕ → ChainState)
      (logAt : Chain → ℕ → List Obligation) (F : Flow) (m : FlowLeg) (N : ℕ) (p : ImtProof),
      Wf S ∧ HistoryFromRuns cv S snap logAt ∧ LegRefundableBy h z0 hl cv S F m N p
        ∧ absenceLog logAt S F.deadline m.chain N ≠ []
        ∧ (∀ o ∈ absenceLog logAt S F.deadline m.chain N, commitOf cv o ≠ legValue cv F m)
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline m.chain N p

/-- **COUNTERMODEL: A CLASH TURNS A LEG THAT SHOULD TIME OUT INTO ONE THAT EXECUTES.**  For every
node hash, padding constant and leaf hash: in a well-formed history read off runs, take a one-leg
flow whose leg no chain ever appended.  Its commit value equals that of a leg chain `0` did append.
Then the flow executes on an honest inclusion proof (as in
`Properties.SharedCommitmentClashLetsUnappendedLegExecute`).  Every absence proof that passes the
timeout check for that leg, on any batch, carries a located `AbsenceBreak`.  So the collision costs
the refund path its liveness, and the outcome is an execution with nothing appended behind it. -/
def Properties.SharedCommitmentClashBlocksTimeout : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (snap : Chain → ℕ → ChainState)
      (logAt : Chain → ℕ → List Obligation) (F : Flow) (m : FlowLeg) (ev : GateEvidence),
      Wf S ∧ HistoryFromRuns cv S snap logAt ∧ m ∈ F.legs
        ∧ (∀ c n, obligationOf F m ∉ logAt c n)
        ∧ ExecutedViaBy h z0 hl cv fh S F ev m
        ∧ ∀ (N : ℕ) (p : ImtProof), LegRefundableBy h z0 hl cv S F m N p →
            AbsenceBreak h z0 hl S F.deadline m.chain N p

/-- **COUNTERMODEL: A FORGED PROOF LETS A NEVER-APPENDED LEG EXECUTE.**  For every node hash and
padding constant there is a leaf hash (one that collides on the sentinel leaf) under which, in a
well-formed history read off runs where nothing was ever appended, a one-leg flow with a nonzero
commit value executes.  No clash with a logged obligation holds, since the logs are empty, and the
proof carries a located `InclusionBreak` (`leafCollision`).  So the break disjunct of
`Properties.GateLegWasAppendedOrClash` cannot be dropped either. -/
def Properties.SharedCommitmentForgedProofLetsUnappendedLegExecute : Prop :=
  ∀ (h : Hash) (z0 : UInt256),
    ∃ (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
      (snap : Chain → ℕ → ChainState) (logAt : Chain → ℕ → List Obligation) (F : Flow)
      (ev : GateEvidence) (leg : FlowLeg),
      Wf S ∧ HistoryFromRuns cv S snap logAt ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ (∀ c n, obligationOf F leg ∉ logAt c n)
        ∧ ¬ (∃ o ∈ logAt leg.chain (ev leg).1, CommitClash cv (obligationOf F leg) o)
        ∧ legValue cv F leg ≠ 0
        ∧ InclusionBreak h z0 hl S leg.chain (ev leg).1 (ev leg).2

end Contracts.SharedCommitment
