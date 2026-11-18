import EraSpec.Protocol.InteropAtomicity.Specs.SystemAtV35
import EraSpec.Protocol.InteropAtomicity.Specs.LegSourceFilterAtV35
import EraSpec.Contracts.AtomicFlowManager.Specs.RefundClosesAppend

/-!
# Properties: the composed system at `draft/v0.35.0`

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.SystemAtV35` (pin `b17415d20`); proofs
in `EraSpec.Protocol.InteropAtomicity.Proofs.SystemAtV35`.  No statement takes a hash premise.

Several merged topics model parts of v35 already: `Contracts.AtomicFlowManager.RefundClosesAppend`
(one chain's manager and root storage, `authorizeRefund` marking several keys per call),
`Contracts.FlowCanonicalAtV35` (one chain's manager under the full `_validateAndComputeFlowId`),
`Contracts.LegSourceFilterAtV35` (the receive filter over the pin's relations),
`Contracts.FlowBindingAtHead` (the head `append` and the calling-chain marking, with a
`RunAtV35`), `Contracts.AppendPath`'s `SysStepsAtHead` (the unbounded walk) and
`Contracts.InteropHandlerAtV35` (the `InteropHandlerBase` topic `ReentrancyAtV35`: one handler's
bundle and call statuses under re-entrant call trees, with the gate's verdict an input bit of
each entry-point call).  This file puts each result in exactly one of three categories: new, a
transfer of a merged result along a projection, or a counterpart of a merged result restated
over `RunV35`.  Three statements are only witnesses, outside the categories:
`Properties.CodeAuthorizeCallIsAuthorizeStepsWitnessV35` (for a new result),
`Properties.ExecutedObligationStaysCommittedWitnessV35` (for a transfer) and
`Properties.DeregisteredPeerWitnessV35` (for a counterpart); see "Witnesses and countermodels"
below.  Where a new result or a transfer has an analogue over another merged model, its
docstring names that analogue as a parallel; no proof here uses it.

## New

* **The relation and its projections.**  `RunV35` keeps the root storage, the bridgehubs, the
  handler's `bundleStatus`, every manager and every tree (with the unbounded insert) as state on
  every chain at once.  Its managers form a pin `Contracts.Refund.ReachLog` run and a pin
  `Contracts.FlowBinding.RunLog` run, and its managers and trees a merged
  `Contracts.AppendPath.SysStepsAtHead` run (`Properties.RunV35ProjectsToReachLog`,
  `Properties.RunV35ProjectsToRunLog`, `Properties.RunV35ProjectsToSysStepsAtHead`).  The
  projections are new because the relation is; the second parallels
  `Contracts.LegSourceFilterAtV35.Properties.RunAtV35ProjectsToRunLog`, which projects that
  model's runs to the same `RunLog`.
* **The expired-flow gate binds only the chain that refunded.**  On one run, a refund is
  authorized on chain `1` and chain `0` then appends a leg of the refunded flow
  (`Properties.RefundThenAppendWitnessV35`), as the NatSpec at `AtomicFlowManager.sol:114-116`
  says ("other source chains have their own views").  The one merged model that keeps the root
  timestamp as state, `RefundClosesAppend`, has one chain; `FlowBindingAtHead`'s `RunAtV35` reads
  the timestamp per call.
* **The refund simplification, refined.**  The model marks a leg on its declared chain; the code
  marks the `Committed` keys of the chain that runs the call.  On runs from genesis, one code
  call whose modelled checks pass on a chain is a sequence of model `authorize` steps ending in
  exactly the code's write, unless a logged `append` on that chain clashes with the presented
  flow (`Properties.CodeAuthorizeCallIsAuthorizeStepsV35`).

## Transfers

Along the projections: an executed obligation is never refunded at v35, or a logged refund
step carries a `RefundBreak` (`Properties.V35ExecutedObligationNeverRefundedOrBreak`, from
`Contracts.Refund.Properties.ExecutedObligationNeverRefundedOrBreak`; it parallels
`Contracts.LegSourceFilterAtV35.Properties.ExecutedObligationNeverRefundedOrBreakAtV35`, the same
transfer over that model); once per leg, with one tree index per appended obligation
(`Properties.SystemOncePerLegV35`, from `Contracts.AppendPath.Properties.SystemOncePerLegAtHead`;
it parallels `Contracts.LegSourceFilterAtV35.Properties.SystemOncePerLegAtV35`, over that model's
five-hop insert).

## Counterparts of merged results, restated over `RunV35`

These are proved directly over `RunV35`, not derived from the merged results.  Their content is
the merged result's; what they add is that it holds on the composed relation, where several
chains' managers, root storages, bridgehubs and bundle statuses move together and each call's
checks are read from that state.

* Of `Contracts.AtomicFlowManager.RefundClosesAppend` (one chain, closer to the code: there
  `authorizeRefund` marks every `Committed` key of the flow in one call):
  `Properties.LatestRootTimestampMonotoneMaxV35` (`LatestBoundsStoredInvariant`,
  `LatestNeverDecreases`); `Properties.RefundedChainLatestPastDeadlineV35` (the first conjunct of
  `AuthorizedPreimageAppendHitsDeadlineGate`); `Properties.NoAppendAfterRefundOnSameChainV35`
  (`LaterAppendsHaveLaterDeadlines`, `AuthorizedPreimageNeverAppendedAgain`); the countermodel
  `Properties.WithoutDeadlineGateAppendAfterRefundV35`
  (`WithoutDeadlineGateLegCommittedAfterRefund`).
* Of `Contracts.LegSourceFilterAtV35` (whose log records the allow-lists each call read):
  `Properties.HubsAreReplayedAdminLogV35`, `Properties.GateFilterHeldWhenLoggedV35` and
  `Properties.RefundFilterHeldWhenLoggedV35` derive the bridgehub of each call's time from the
  admin log; `Properties.DeregisteredPeerBlocksLaterGatesAndRefundsV35`
  (`BlockedUntilReallowedAtV35`); `Properties.ReallowedPeerGateWitnessV35` (one instance of the
  stronger `ReallowRestoresGateAtV35`).  The gate half of
  `Properties.DeregisteredPeerBlocksLaterGatesAndRefundsV35` and
  `Properties.ReallowedPeerGateWitnessV35` also parallel, in that order, the first two conjuncts
  of `Contracts.InteropHandlerAtV35.Properties.ReceiveFilterIsReadAtTheGateAtV35` (after a
  deregistration the verdict fails; after the peer is allowed again it can pass).
* Of `Contracts.InteropHandlerAtV35` (whose gate verdict is an input bit of each entry-point
  call, and in its filter results `gateVerdictAtV35` of a whitelist with every other check one
  input bit): `Properties.StatusLeavesUnreceivedOnlyThroughGateV35` (`DeliveryNeedsTheGateAtV35`,
  in contrapositive form; here a structural invariant of the step relation) and
  `Properties.VerifiedBundleExecutesAfterDeregistrationV35` (the last conjunct of
  `ReceiveFilterIsReadAtTheGateAtV35` and its witness `ReceiveFilterWitnessAtV35`, through the
  edge of `VerifiedBundleExecutesWithoutTheGateAtV35`).  What `RunV35` adds is that a logged gate
  call's verdict is `GateOkV35` read on the composed state: its evidence checked against `S`, and
  the receive filter on the chain's bridgehub as the logged admin steps leave it.  What it lacks
  is that model's call trees, re-entry, reverting frames and per-call statuses.
* Of `Contracts.FlowBindingAtHead` (whose `authorizeRefund` step marks the calling chain, as the
  code does): `Properties.SetKeyHasLoggedAppendV35` (`CommittedLegHasLoggedPreimage`; on one
  chain, also `Contracts.FlowCanonicalAtV35.Properties.WrittenLegAppendedUnderAcceptedPreimageV35`)
  and `Properties.CodeAuthorizeMarksDeclaredLegOrLoggedClashV35`
  (`AuthorizeMarksDeclaredLegOrLoggedClash`).  Here the latter bounds this model's
  declared-chain marking, and `Properties.CodeAuthorizeCallIsAuthorizeStepsV35` builds on it.
* Of `Contracts.AppendPath.SysStepsAtHead`: `Properties.AppendedAtMostOnceV35` (the first conjunct
  of `SystemOncePerLegAtHead`, that the append log has no duplicate, with the manager-level fact
  that every appended key stays set; on one chain, also
  `Contracts.FlowCanonicalAtV35.Properties.RunV35AppendsEachLegAtMostOnce`).

`Contracts.LegSourceFilterAtV35.Properties.SystemAtV35Witness` is a witness for that topic's
system restatements, over its `SysStepsAtV35`; despite the name it is not a statement of this
topic.

## Scope

The model drops checks of the code that can only reject (the spec's "What differs from the
code"), so the exclusion results here (`…NoAppend…`, `…Blocks…`) are stated over a relation
with more runs than those checks would allow.  Two modelling choices are not of that kind: the
tree side of every proof is the fixed history `S`, as at the pin, and a refund step marks a leg
on its declared chain, which `Properties.CodeAuthorizeMarksDeclaredLegOrLoggedClashV35` and
`Properties.CodeAuthorizeCallIsAuthorizeStepsV35` bound on runs from genesis.  The witnesses are
runs of the model.  Not covered: liveness, and the settlement layer's own clock (`roots` is a
free sequence of imports).
-/

namespace Contracts.SystemAtV35

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.FlowBinding Contracts.AppendPath

/-! ## Projections (new) and transfers -/

/-- **THE MANAGERS OF A v35 RUN ARE A LOGGED REFUND RUN.**  New.  For every v35 run, the managers
form a `Contracts.Refund.ReachLog` run whose log is the run's `authorizeRefund` steps, in the
same order.  So every statement of `Properties/Refund.lean` over `ReachLog` applies to them. -/
def Properties.RunV35ProjectsToReachLog : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log → ReachLog h z0 hl cv fh S X.mgrs Y.mgrs (authLog log)

/-- **THE MANAGERS AND GATE CALLS OF A v35 RUN ARE A FLOW-BINDING RUN.**  New.  For every v35 run,
the managers form a `Contracts.FlowBinding.RunLog` run whose log is the run's gate calls (as
`execute`) and `authorizeRefund` steps, in the same order.  So every statement of
`Properties/FlowBinding.lean` over `RunLog` applies to them.  The status edges that run no gate
are not in that log.  It parallels
`Contracts.LegSourceFilterAtV35.Properties.RunAtV35ProjectsToRunLog`, the projection of that
model's runs to the same `RunLog`; the proof here does not use it. -/
def Properties.RunV35ProjectsToRunLog : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log → RunLog h z0 hl cv fh S X.mgrs Y.mgrs (checkedLog log)

/-- **THE MANAGERS AND TREES OF A v35 RUN ARE A HEAD SYSTEM RUN.**  New.  For every v35 run,
every chain's manager and tree form a `Contracts.AppendPath.SysStepsAtHead` run (`SysSteps` with the
unbounded walk) whose logs are the run's appended obligations and its `authorizeRefund` steps.
So every statement of `Properties/OncePerLegAtHead.lean` over `SysStepsAtHead` applies to
them. -/
def Properties.RunV35ProjectsToSysStepsAtHead : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log →
      SysStepsAtHead h z0 hl cv fh S X.chains Y.chains (appendLog log) (authLog log)

/-- **AN EXECUTED OBLIGATION IS NEVER REFUNDED AT v35, OR A LOCATED BREAK.**  Transfer:
`Contracts.Refund.Properties.ExecutedObligationNeverRefundedOrBreak`, transferred along
`Properties.RunV35ProjectsToReachLog`: if leg `leg` of `F` passes the pin's gate on evidence `ev`
(`ExecutedViaBy`) against a well-formed history `S`, then in every v35 run from genesis its
obligation is not past `Committed`, or a logged `authorizeRefund` step that marked it carries a
`RefundBreak`.  It parallels
`Contracts.LegSourceFilterAtV35.Properties.ExecutedObligationNeverRefundedOrBreakAtV35`, the same
transfer over that model's runs. -/
def Properties.V35ExecutedObligationNeverRefundedOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (H0 : Chain → HubV35) (Y : WorldV35) (log : List CallV35),
      RunV35 h z0 hl cv fh S (genesisV35 H0) Y log →
        ¬ Refunded Y.mgrs (obligationOf F leg)
          ∨ RefundBreak h z0 hl fh S F ev (obligationOf F leg) (authLog log)

/-- **ONCE PER LEG AT v35, WITH THE TREES.**  Transfer:
`Contracts.AppendPath.Properties.SystemOncePerLegAtHead`, transferred along
`Properties.RunV35ProjectsToSysStepsAtHead`: along every v35 run from genesis, no obligation is
appended twice, each appended obligation occupies exactly one index of its chain's tree (the
leaf there holds its commit value), and two appended obligations on one chain with one commit
value are equal.  The insert here has no hop bound, as at v35.  It parallels
`Contracts.LegSourceFilterAtV35.Properties.SystemOncePerLegAtV35`, the same statement over that
model's `SysStepsAtV35`, whose insert keeps the pin's five-hop search. -/
def Properties.SystemOncePerLegV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (H0 : Chain → HubV35) (Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S (genesisV35 H0) Y log →
      (appendLog log).Nodup
        ∧ (∀ o ∈ appendLog log, ∃! i, i < (Y o.chain).base.tree.leafCount
            ∧ ((Y o.chain).base.tree.leaf i).value = commitOf cv o)
        ∧ (∀ o ∈ appendLog log, ∀ o' ∈ appendLog log, o.chain = o'.chain →
            commitOf cv o = commitOf cv o' → o = o')

/-! ## Root storage and the expired-flow gate

Counterparts over `RunV35` of `Contracts.AtomicFlowManager.RefundClosesAppend`'s results. -/

/-- **`latestInteropRootTimestamp` NEVER DECREASES AND STAYS THE MAXIMUM.**  Along every v35 run
from a world whose root storage keeps its running maximum (`RootsWf`), it keeps it, and no
chain's `latest` decreases.  The counterpart of
`Contracts.AtomicFlowManager.RefundClosesAppend.Properties.LatestBoundsStoredInvariant` and
`LatestNeverDecreases`, here on every chain's L1 entry at once. -/
def Properties.LatestRootTimestampMonotoneMaxV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log → RootsWf X →
      RootsWf Y ∧ ∀ c, (X c).roots.latest ≤ (Y c).roots.latest

/-- **A CHAIN THAT AUTHORIZED A REFUND HAS IMPORTED A ROOT PAST THAT FLOW'S DEADLINE.**  Along
every v35 run from a `RootsWf` world, for every logged `authorizeRefund` step `a`, the chain it
ran on (`a.leg.chain`) ends the run with `latestInteropRootTimestamp` strictly above
`a.flow.deadline`.  The counterpart of the first conjunct of
`Contracts.AtomicFlowManager.RefundClosesAppend.Properties.AuthorizedPreimageAppendHitsDeadlineGate`. -/
def Properties.RefundedChainLatestPastDeadlineV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log → RootsWf X →
      ∀ a, CallV35.authorize a ∈ log → a.flow.deadline < (Y a.leg.chain).roots.latest

/-- **AFTER A REFUND ON A CHAIN, EVERY LATER `append` THERE IS OF A FLOW WITH A LATER DEADLINE.**
Along every v35 run from a `RootsWf` world: if the log is `later ++ authorize a :: earlier`, then
every `append` in `later` on the chain `a` ran on is of a flow whose deadline is strictly after
`a.flow.deadline`.  In particular no leg of a flow with `a.flow`'s deadline, `a.flow` itself
included, is appended on that chain after the refund.  Appends on other chains are not
constrained (`Properties.RefundThenAppendWitnessV35`).  The counterpart of
`Contracts.AtomicFlowManager.RefundClosesAppend.Properties.LaterAppendsHaveLaterDeadlines` and
`AuthorizedPreimageNeverAppendedAgain`, which state it for one chain's runs in which one
`authorizeRefund` call marks every `Committed` key of the flow. -/
def Properties.NoAppendAfterRefundOnSameChainV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log → RootsWf X →
      ∀ (later : List CallV35) (a : AuthCall) (earlier : List CallV35),
        log = later ++ CallV35.authorize a :: earlier →
          ∀ (c : Chain) (F : Flow) (b : UInt256) (dest : Chain),
            CallV35.append c F b dest ∈ later → c = a.leg.chain → a.flow.deadline < F.deadline

/-! ## The receive filter and the bundle status

`HubsAreReplayedAdminLogV35`, `GateFilterHeldWhenLoggedV35`, `RefundFilterHeldWhenLoggedV35` and
`DeregisteredPeerBlocksLaterGatesAndRefundsV35` are counterparts over `RunV35` of
`Contracts.LegSourceFilterAtV35`'s results; `StatusLeavesUnreceivedOnlyThroughGateV35` is the
counterpart of `Contracts.InteropHandlerAtV35.Properties.DeliveryNeedsTheGateAtV35`. -/

/-- **THE BRIDGEHUBS ARE THE STARTING ONES WITH THE LOGGED ADMIN CALLS REPLAYED.**  Along every
v35 run, every chain's bridgehub at the end is `hubsAfter` of the starting bridgehubs and the
run's log.  The counterpart of `Contracts.LegSourceFilterAtV35`'s logged allow-lists: there each
logged gate and refund call records the allow-lists it read; here they are replayed from the
logged admin calls. -/
def Properties.HubsAreReplayedAdminLogV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log → Y.hubs = hubsAfter X.hubs log

/-- **EVERY LOGGED GATE PASSED, ON THE BRIDGEHUB OF ITS TIME.**  Along every v35 run, if the log
is `later ++ gate d e :: earlier`, then `e`'s evidence verified (`ExecCall.Verified`) and every
leg of `e.flow` passed the receive filter on chain `d`'s bridgehub after the admin calls of
`earlier`, which is the bridgehub `d` had when the gate ran.  The counterpart of
`Contracts.LegSourceFilterAtV35`'s gate step, which requires the filter on the allow-lists it
logs (`Contracts.LegSourceFilterAtV35.Properties.GateAtV35IffPinGateAndSourcesAllowed`). -/
def Properties.GateFilterHeldWhenLoggedV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log →
      ∀ (later : List CallV35) (d : Chain) (e : ExecCall) (earlier : List CallV35),
        log = later ++ CallV35.gate d e :: earlier →
          e.Verified h z0 hl cv fh S
            ∧ ∀ l ∈ e.flow.legs, SourceAllowedV35 (hubsAfter X.hubs earlier d) d l.chain

/-- **EVERY LOGGED REFUND PASSED, ON THE BRIDGEHUB OF ITS TIME.**  Along every v35 run, if the log
is `later ++ authorize a :: earlier`, then `a`'s checks verified (`AuthCall.Verified`) and the
missing leg's source passed the receive filter on the bridgehub of the chain `a` ran on, after
the admin calls of `earlier`.  The counterpart of `Contracts.LegSourceFilterAtV35`'s refund step,
which requires the filter on the allow-lists it logs. -/
def Properties.RefundFilterHeldWhenLoggedV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log →
      ∀ (later : List CallV35) (a : AuthCall) (earlier : List CallV35),
        log = later ++ CallV35.authorize a :: earlier →
          a.Verified h z0 hl cv fh S
            ∧ SourceAllowedV35 (hubsAfter X.hubs earlier a.leg.chain) a.leg.chain a.missing.chain

/-- **A DEREGISTERED PEER BLOCKS LATER GATES AND REFUNDS ON THAT CHAIN UNTIL IT IS ALLOWED
AGAIN.**  Along every v35 run, if the log is `later ++ admin d (deregister s) :: earlier` with
`s ≠ d`, and `later` has no `admin d (allow s)`, then no gate call on `d` in `later` presents a
flow with a leg from `s`, and no refund step on `d` in `later` has its missing leg on `s`.  The
calls before the deregistration are not constrained
(`Properties.VerifiedBundleExecutesAfterDeregistrationV35`).  The counterpart of
`Contracts.LegSourceFilterAtV35.Properties.BlockedUntilReallowedAtV35`.  The gate half also
parallels the first conjunct of
`Contracts.InteropHandlerAtV35.Properties.ReceiveFilterIsReadAtTheGateAtV35` (after
`deregisterChainForInterop(c)` the gate's verdict is `false`), whose verdict is
`gateVerdictAtV35` of a whitelist; here the filter is read on the chain's bridgehub. -/
def Properties.DeregisteredPeerBlocksLaterGatesAndRefundsV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log →
      ∀ (later : List CallV35) (d s : Chain) (earlier : List CallV35),
        log = later ++ CallV35.admin d (.deregister s) :: earlier → s ≠ d →
          CallV35.admin d (.allow s) ∉ later →
            (∀ e, CallV35.gate d e ∈ later → ∀ l ∈ e.flow.legs, l.chain ≠ s)
              ∧ ∀ a, CallV35.authorize a ∈ later → a.leg.chain = d → a.missing.chain ≠ s

/-- **A BUNDLE LEAVES `Unreceived` ONLY THROUGH A LOGGED GATE CALL.**  Along every v35 run, if
bundle `b` is `Unreceived` on chain `d` at the start and not at the end, the log has a gate call
on `d` whose executing bundle is `b`.

This is a structural invariant of the step relation: only the `gate` step writes a status from
`Unreceived`, and the `resume` edges (`NoGateEdge`) start from `Verified` or `Unbundled`.  It
carries no protocol content beyond that shape of the model.  It is the counterpart over `RunV35`,
in contrapositive form, of `Contracts.InteropHandlerAtV35.Properties.DeliveryNeedsTheGateAtV35`
(a bundle hash none of whose entry-point calls carries a passing verdict stays `Unreceived`).
There the verdict is an input bit of each entry-point call.  What `RunV35` adds is that a logged
gate call passed `GateOkV35` on the composed state, its evidence checked against `S` and its
legs' sources against chain `d`'s bridgehub of that moment, which
`Properties.GateFilterHeldWhenLoggedV35` locates as the replayed admin log; this statement itself
names only the logged call.  `RunV35` has none of that model's call trees, re-entry, reverting
frames or per-call statuses. -/
def Properties.StatusLeavesUnreceivedOnlyThroughGateV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log →
      ∀ (d : Chain) (b : UInt256), (X d).status b = .Unreceived → (Y d).status b ≠ .Unreceived →
        ∃ e, CallV35.gate d e ∈ log ∧ e.leg.bundleHash = b

/-! ## Once per leg, manager half -/

/-- **EACH OBLIGATION IS APPENDED AT MOST ONCE AT v35, AND ITS KEY STAYS SET.**  Along every v35
run from genesis, the appended obligations `⟨flowId, bundleHash, chain⟩` are pairwise distinct,
and the key of every one of them is not `Unset` on its chain at the end: no step returns a key
to `Unset`, and `append` needs it `Unset` (`ManagerLegAlreadyCommitted`,
`AtomicFlowManager.sol:162-164`).  The counterpart, proved directly over `RunV35`, of the first
conjunct of `Contracts.AppendPath.Properties.SystemOncePerLegAtHead` (the first half here, which
is also the first conjunct of the transfer `Properties.SystemOncePerLegV35`), and on one chain of
`Contracts.FlowCanonicalAtV35.Properties.RunV35AppendsEachLegAtMostOnce`. -/
def Properties.AppendedAtMostOnceV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (H0 : Chain → HubV35) (Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S (genesisV35 H0) Y log →
      (appendLog log).Nodup
        ∧ ∀ o ∈ appendLog log, (Y o.chain).base.mgr.legState o.flowId o.bundleHash ≠ .Unset

/-! ## The refund simplification -/

/-- **A KEY THAT IS NOT `Unset` WAS APPENDED ON ITS CHAIN BY A LOGGED CALL.**  Along every v35 run
from genesis, if key `(f, b)` is not `Unset` in chain `x`'s manager, the log has an `append` of
`b` on `x` whose flow has id `f`, passed `_checkFlowId`, declares `b` on `x`, and has strictly
ascending bundle hashes.  The counterpart of
`Contracts.FlowBindingAtHead.Properties.CommittedLegHasLoggedPreimage`, and on one chain of
`Contracts.FlowCanonicalAtV35.Properties.WrittenLegAppendedUnderAcceptedPreimageV35`. -/
def Properties.SetKeyHasLoggedAppendV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (H0 : Chain → HubV35) (Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S (genesisV35 H0) Y log →
      ∀ (x : Chain) (f b : UInt256), (Y x).base.mgr.legState f b ≠ .Unset →
        ∃ (F : Flow) (dest : Chain), CallV35.append x F b dest ∈ log ∧ F.flowId = f
          ∧ FlowIdChecked fh F ∧ (⟨x, b⟩ : FlowLeg) ∈ F.legs
          ∧ (F.legs.map FlowLeg.bundleHash).Pairwise (· < ·)

/-- **A KEY THE CODE'S `authorizeRefund` WOULD MARK IS DECLARED ON THE MARKING CHAIN, OR THE
PRESENTED FLOW CLASHES WITH A LOGGED `append`'S FLOW.**  Along every v35 run from genesis: take
a chain `x`, a flow `F` that passes `_checkFlowId`, and a leg `l` of `F` whose key
`(F.flowId, l.bundleHash)` is `Committed` in `x`'s manager.  The code's `authorizeRefund(F, …)`
run on `x` marks, once its checks pass, exactly such keys (`AtomicFlowManager.sol:238-246`).
Then `F` declares `l` on `x`, or the log has an `append` of `l.bundleHash` on `x` whose flow and
`F` clash on `fh` (`FlowIdClash`).  The counterpart of
`Contracts.FlowBindingAtHead.Properties.AuthorizeMarksDeclaredLegOrLoggedClash`, whose model
marks the calling chain; here it bounds this model's declared-chain marking per key.  On one
chain, `Contracts.FlowCanonicalAtV35.Properties.RefundedLegSameFlowOrLoggedClashV35` bounds the
code's marking loop in a related way: a refunded leg was marked under the preimage it was
appended under, or one that clashes with it. -/
def Properties.CodeAuthorizeMarksDeclaredLegOrLoggedClashV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (H0 : Chain → HubV35) (Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S (genesisV35 H0) Y log →
      ∀ (x : Chain) (F : Flow) (l : FlowLeg), FlowIdChecked fh F → l ∈ F.legs →
        (Y x).base.mgr.legState F.flowId l.bundleHash = .Committed →
          l.chain = x
            ∨ ∃ (F' : Flow) (dest : Chain), CallV35.append x F' l.bundleHash dest ∈ log
                ∧ FlowIdClash fh F F'

/-- **ONE CODE `authorizeRefund` CALL IS A SEQUENCE OF MODEL STEPS, OUTSIDE A LOGGED CLASH.**
New.  Along every v35 run from genesis, take a chain `x` and a code call `authorizeRefund` on `x`
presenting flow `F`, missing leg `m` and absence evidence `(N, p)`, whose checks, as this model
states them, pass on `x`: `F` passes `_checkFlowId` and has strictly ascending bundle hashes
(`_validateAndComputeFlowId`, which the code runs on this path, `AtomicFlowManager.sol:217`,
`:348-379`), `m` is a leg of `F` (`:224-226`) whose absence proof passes against its declared
chain (`LegRefundableBy`; `:227-230`, `:233-234`), `x`'s bridgehub allows `m`'s source (`:231`),
and `x` has imported an L1 root after `F`'s deadline.  Suppose no logged `append` on `x` of a
bundle hash of `F` has a flow that clashes with `F` on `fh`.  Then the run extends by a list of
`authorize` steps, each with flow `F`, missing leg `m`, evidence `(N, p)` and a leg of `F`
declared on `x`, to the world whose only change is chain `x`'s manager, rewritten as the code's
marking loop rewrites it (`:238-246`, as
`Contracts.AtomicFlowManager.RefundClosesAppend.markCommittedRevertable` transcribes it over
`F`'s bundle hashes).

Related merged results read the same loop as one `authorize` step per marked leg of the pin's
leg machine `Contracts.AtomicFlowManager.Reach`
(`Contracts.AtomicFlowManager.RefundClosesAppend.Properties.ChainRunLegsReach`,
`Contracts.FlowCanonicalAtV35.Properties.RunV35IsPinLegRun`); that machine has no chains, logs
or checks.  What this statement adds is that each step is a logged `RunV35` step whose checks
pass and whose declared chain is the calling chain `x`. -/
def Properties.CodeAuthorizeCallIsAuthorizeStepsV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (H0 : Chain → HubV35) (Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S (genesisV35 H0) Y log →
      ∀ (x : Chain) (F : Flow) (m : FlowLeg) (N : ℕ) (p : ImtProof),
        FlowIdChecked fh F → (F.legs.map FlowLeg.bundleHash).Pairwise (· < ·) → m ∈ F.legs →
        LegRefundableBy h z0 hl cv S F m N p → SourceAllowedV35 (Y x).hub x m.chain →
        (∃ blk, F.deadline < (Y x).roots.stored blk) →
        (∀ l ∈ F.legs, ∀ (F' : Flow) (dest : Chain),
            CallV35.append x F' l.bundleHash dest ∈ log → ¬ FlowIdClash fh F F') →
          ∃ steps : List CallV35,
            (∀ c ∈ steps, ∃ l ∈ F.legs, l.chain = x ∧ c = CallV35.authorize ⟨F, l, m, N, p⟩)
            ∧ RunV35 h z0 hl cv fh S (genesisV35 H0)
                (Y.set x { Y x with base :=
                  ⟨RefundClosesAppend.markCommittedRevertable (Y x).base.mgr F.flowId
                      (F.legs.map FlowLeg.bundleHash), (Y x).base.tree⟩ })
                (steps ++ log)

/-! ## Witnesses and countermodels

Every run below starts at `genesisV35 (fun _ => v35ClosedHub)` (no chain allows or registers any
peer), uses the commit value `v35BundleCv` and `lengthFlowHash`, and holds for every node hash,
padding constant and leaf hash.  The fixed history is `mixedSystem 1`, except in
`Properties.DeregisteredPeerWitnessV35`, which uses `Contracts.LegSourceFilterAtV35.swapSystem`.

Each bullet names the statement's category from the header.

* `Properties.RefundThenAppendWitnessV35` (new) meets the premises of the projections, the root
  results, `NoAppendAfterRefundOnSameChainV35`, `RefundFilterHeldWhenLoggedV35`,
  `AppendedAtMostOnceV35` and `SystemOncePerLegV35` (three appends), `SetKeyHasLoggedAppendV35` and
  `CodeAuthorizeMarksDeclaredLegOrLoggedClashV35`, with each disjunct of the last firing alone on
  one instance.
* `Properties.ExecutedObligationStaysCommittedWitnessV35` (a witness only) meets the premises of
  `V35ExecutedObligationNeverRefundedOrBreak` with the executed obligation appended and still
  `Committed`, executed on its destination, next to a refunded obligation.
* `Properties.WithoutDeadlineGateAppendAfterRefundV35` (a counterpart) shows the expired-flow
  gate is load-bearing for `NoAppendAfterRefundOnSameChainV35` on that run.
* `Properties.VerifiedBundleExecutesAfterDeregistrationV35` (a counterpart) meets the premises
  of the bridgehub and status results with a gate call in the log.
* `Properties.DeregisteredPeerWitnessV35` (a witness only) meets the premises of
  `DeregisteredPeerBlocksLaterGatesAndRefundsV35` with a gate and a refund on the chain after
  the deregistration, both reading the filter on a still-allowed peer other than the chain
  itself.
* `Properties.ReallowedPeerGateWitnessV35` (a counterpart) shows that the premise "no `allow s`
  in `later`" is needed.
* `Properties.CodeAuthorizeCallIsAuthorizeStepsWitnessV35` (a witness only) meets the premises of
  `CodeAuthorizeCallIsAuthorizeStepsV35` with a code call that marks two keys. -/

/-- **A REFUND, THEN APPENDS: ON THE SAME CHAIN ONLY WITH A LATER DEADLINE.**  New.  In order:
chain `1` allows peer `0` and chain `0` allows peer `1`; chain `1` appends leg `⟨1, 2⟩` of
`v35RefundFlow` (deadline `0`), sending it to chain `0`; chain `1` imports an L1 root with
timestamp `1` at block `0`; chain `1` authorizes the refund of that leg on an absence proof for
the never-appended leg `⟨1, 3⟩`; chain `0` appends leg `⟨0, 1⟩` of the same `v35RefundFlow`,
sending it to chain `1`; chain `1` appends leg `⟨1, 4⟩` of `v35LaterFlow` (deadline `1`), the
tree's walk hopping once.  Then:

* the start world is `RootsWf`; the log is `later ++ authorize a :: earlier` with both appends
  above in `later`, and its authorize log is `[a]`;
* key `(0, 4)` is `Committed` on chain `1` and the checked `v35LaterFlow` declares bundle `4` on
  chain `1`, with no logged `append` of bundle `4` on chain `1` whose flow clashes with it; key
  `(1, 1)` is `Committed` on chain `0` while the checked `v35ClashFlow` declares bundle `1` on
  chain `1`, and the logged `append` of `v35RefundFlow` on chain `0` clashes with it.  So each
  disjunct of `Properties.CodeAuthorizeMarksDeclaredLegOrLoggedClashV35` holds without the
  other on one instance.

The append of leg `⟨0, 1⟩` on chain `0` after the refund on chain `1` is the per-chain scope of
the expired-flow gate, as the NatSpec at `AtomicFlowManager.sol:114-116` says. -/
def Properties.RefundThenAppendWitnessV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Y : WorldV35) (a : AuthCall),
      a.flow = v35RefundFlow ∧ a.leg = ⟨1, 2⟩ ∧ a.missing = ⟨1, 3⟩
      ∧ RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1)
          (genesisV35 (fun _ => v35ClosedHub)) Y
          ([.append 1 v35LaterFlow 4 0, .append 0 v35RefundFlow 1 1]
            ++ CallV35.authorize a :: [.append 1 v35RefundFlow 2 0, .admin 0 (.allow 1),
              .admin 1 (.allow 0)])
      ∧ authLog ([.append 1 v35LaterFlow 4 0, .append 0 v35RefundFlow 1 1]
            ++ CallV35.authorize a :: [.append 1 v35RefundFlow 2 0, .admin 0 (.allow 1),
              .admin 1 (.allow 0)]) = [a]
      ∧ RootsWf (genesisV35 (fun _ => v35ClosedHub))
      ∧ (Y 1).base.mgr.legState v35LaterFlow.flowId 4 = .Committed
      ∧ FlowIdChecked lengthFlowHash v35LaterFlow ∧ (⟨1, 4⟩ : FlowLeg) ∈ v35LaterFlow.legs
      ∧ (¬ ∃ (F' : Flow) (dest : Chain),
            CallV35.append 1 F' 4 dest ∈
              [.append 1 v35LaterFlow 4 0, .append 0 v35RefundFlow 1 1, .authorize a,
                .append 1 v35RefundFlow 2 0, .admin 0 (.allow 1), .admin 1 (.allow 0)]
            ∧ FlowIdClash lengthFlowHash v35LaterFlow F')
      ∧ (Y 0).base.mgr.legState v35ClashFlow.flowId 1 = .Committed
      ∧ FlowIdChecked lengthFlowHash v35ClashFlow ∧ (⟨1, 1⟩ : FlowLeg) ∈ v35ClashFlow.legs
      ∧ CallV35.append 0 v35RefundFlow 1 1 ∈
          [.append 1 v35LaterFlow 4 0, .append 0 v35RefundFlow 1 1, .authorize a,
            .append 1 v35RefundFlow 2 0, .admin 0 (.allow 1), .admin 1 (.allow 0)]
      ∧ FlowIdClash lengthFlowHash v35ClashFlow v35RefundFlow

/-- **AN EXECUTED OBLIGATION, APPENDED AND STILL `Committed`, NEXT TO A REFUNDED ONE.**  In
order: chain `1` allows peer `0` and chain `0` allows peer `1`; chain `0` appends the leg
`⟨0, 1⟩` of `subsetFlow 0 1`, sending it to chain `1`; chain `1` appends leg `⟨1, 2⟩` of
`v35RefundFlow`; chain `1` imports an L1 root with timestamp `1`; chain `1` authorizes the refund
of that leg on an absence proof for `⟨1, 3⟩`; chain `1` runs the gate for bundle `1`, the leg
`⟨0, 1⟩` of `subsetFlow 0 1`, on honest evidence `e.evidence`.  So the premises of
`Properties.V35ExecutedObligationNeverRefundedOrBreak` hold (`mixedSystem 1` is `Wf`, and
`subsetFlow 0 1` executes on `e.evidence` through the pin's gate), with the executed obligation
`⟨0, 1, 0⟩` on the run's append log and still `Committed` on chain `0`, the refunded obligation
`⟨1, 2, 1⟩` past `Committed`, and the executed one neither refunded nor carrying a `RefundBreak`
against the authorize log. -/
def Properties.ExecutedObligationStaysCommittedWitnessV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Y : WorldV35) (a : AuthCall) (e : ExecCall),
      a.flow = v35RefundFlow ∧ a.leg = ⟨1, 2⟩ ∧ a.missing = ⟨1, 3⟩
      ∧ e.flow = subsetFlow 0 1 ∧ e.leg = ⟨0, 1⟩
      ∧ RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1)
          (genesisV35 (fun _ => v35ClosedHub)) Y
          [.gate 1 e, .authorize a, .append 1 v35RefundFlow 2 0, .append 0 (subsetFlow 0 1) 1 1,
            .admin 0 (.allow 1), .admin 1 (.allow 0)]
      ∧ Wf (mixedSystem 1)
      ∧ ExecutedViaBy h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) (subsetFlow 0 1)
          e.evidence ⟨0, 1⟩
      ∧ obligationOf (subsetFlow 0 1) ⟨0, 1⟩ ∈
          appendLog [.gate 1 e, .authorize a, .append 1 v35RefundFlow 2 0,
            .append 0 (subsetFlow 0 1) 1 1, .admin 0 (.allow 1), .admin 1 (.allow 0)]
      ∧ (Y 0).base.mgr.legState (subsetFlow 0 1).flowId 1 = .Committed
      ∧ Refunded Y.mgrs (obligationOf v35RefundFlow ⟨1, 2⟩)
      ∧ ¬ Refunded Y.mgrs (obligationOf (subsetFlow 0 1) ⟨0, 1⟩)
      ∧ ¬ RefundBreak h z0 hl lengthFlowHash (mixedSystem 1) (subsetFlow 0 1) e.evidence
            (obligationOf (subsetFlow 0 1) ⟨0, 1⟩)
            (authLog [.gate 1 e, .authorize a, .append 1 v35RefundFlow 2 0,
              .append 0 (subsetFlow 0 1) 1 1, .admin 0 (.allow 1), .admin 1 (.allow 0)])

/-- **COUNTERMODEL: WITHOUT THE EXPIRED-FLOW GATE, A LEG OF THE REFUNDED FLOW IS APPENDED AFTER
THE REFUND.**  A run with the calls of `Properties.RefundThenAppendWitnessV35` ends in a world in
which the never-appended leg `⟨1, 3⟩` of the refunded `v35RefundFlow` passes every check of
`append` on chain `1` except `ManagerFlowDeadlinePassed` (`AppendOkV35WithoutDeadlineGate`, from
hint `0`, landing on leaf `1`), while the real `append` rejects it from every hint.  So the
expired-flow gate, which the pin's `append` did not have, is the check that makes
`Properties.NoAppendAfterRefundOnSameChainV35` hold on this run.  The counterpart of
`Contracts.AtomicFlowManager.RefundClosesAppend.Properties.WithoutDeadlineGateLegCommittedAfterRefund`,
which also runs the mutant's `append`. -/
def Properties.WithoutDeadlineGateAppendAfterRefundV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Y : WorldV35) (a : AuthCall),
      a.flow = v35RefundFlow ∧ a.leg = ⟨1, 2⟩ ∧ a.missing = ⟨1, 3⟩
      ∧ RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1)
          (genesisV35 (fun _ => v35ClosedHub)) Y
          [.append 1 v35LaterFlow 4 0, .append 0 v35RefundFlow 1 1, .authorize a,
            .append 1 v35RefundFlow 2 0, .admin 0 (.allow 1), .admin 1 (.allow 0)]
      ∧ AppendOkV35WithoutDeadlineGate v35BundleCv lengthFlowHash (Y 1) 1 v35RefundFlow 3 0 0 1
      ∧ ∀ hint low, ¬ AppendOkV35 v35BundleCv lengthFlowHash (Y 1) 1 v35RefundFlow 3 0 hint low

/-- **A BUNDLE VERIFIED BEFORE A DEREGISTRATION EXECUTES AFTER IT.**  In order: chain `1` allows
peer `0`; chain `1` runs the gate for bundle `1` (the executing leg `⟨0, 1⟩` of `subsetFlow 0 1`,
on honest evidence), its source `0` passing the receive filter; chain `1` deregisters peer `0`.
In that world `Z` bundle `1` is `Verified` on chain `1` and its leg's source `0` no longer passes
chain `1`'s receive filter.  The status edge that runs no gate (`executeAtomicBundle` on a
`Verified` bundle) then takes it to `FullyExecuted`: the world `Y` is a run with the same log, in
which bundle `1` is `FullyExecuted`, the filter still fails, and the same gate call would fail.
The checked log is nonempty.  This is the behaviour `protocol-docs/interop-gating.md:195-197`
documents: the filter is read when the bundle is verified.

The counterpart over `RunV35` of the last conjunct of
`Contracts.InteropHandlerAtV35.Properties.ReceiveFilterIsReadAtTheGateAtV35` and of its witness
`Contracts.InteropHandlerAtV35.Properties.ReceiveFilterWitnessAtV35` (a bundle verified while the
peer was allowed executes after `deregisterChainForInterop`), through the edge of
`Contracts.InteropHandlerAtV35.Properties.VerifiedBundleExecutesWithoutTheGateAtV35` (a
`Verified` bundle executes with a failing verdict).  There the verdict is `gateVerdictAtV35` of a
whitelist, with every other check of `requireFlowFinalized` one input bit.  What `RunV35` adds is
that the verdict is read from the composed state: the gate call's honest evidence is checked
against `mixedSystem 1`, the filter is read on chain `1`'s bridgehub as the run's own logged
admin steps leave it, and `GateOkV35` fails on the end state for the same call. -/
def Properties.VerifiedBundleExecutesAfterDeregistrationV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Z Y : WorldV35) (e : ExecCall),
      e.flow = subsetFlow 0 1 ∧ e.leg = ⟨0, 1⟩
      ∧ RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1)
          (genesisV35 (fun _ => v35ClosedHub)) Z
          [.admin 1 (.deregister 0), .gate 1 e, .admin 1 (.allow 0)]
      ∧ (genesisV35 (fun _ => v35ClosedHub) 1).status 1 = .Unreceived
      ∧ (Z 1).status 1 = .Verified
      ∧ ¬ SourceAllowedV35 (Z 1).hub 1 0
      ∧ NoGateEdge ((Z 1).status 1) .FullyExecuted
      ∧ Y = Z.set 1 { Z 1 with status := setStatusV35 (Z 1).status 1 .FullyExecuted }
      ∧ RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1)
          (genesisV35 (fun _ => v35ClosedHub)) Y
          [.admin 1 (.deregister 0), .gate 1 e, .admin 1 (.allow 0)]
      ∧ (Y 1).status 1 = .FullyExecuted
      ∧ ¬ SourceAllowedV35 (Y 1).hub 1 0
      ∧ ¬ GateOkV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) (Y 1) 1 e
      ∧ checkedLog [.admin 1 (.deregister 0), .gate 1 e, .admin 1 (.allow 0)] ≠ []

/-- **AFTER A DEREGISTRATION, A GATE AND A REFUND ON THE CHAIN, BOTH READING THE FILTER ON A
STILL-ALLOWED PEER.**  Over `Contracts.LegSourceFilterAtV35.swapSystem` (chain `0` committed `1`
and chain `1` committed `2`, both in batch 0).  In order: chain `0` allows peers `1` and `2`, then
deregisters peer `2`; chain `0` appends leg `⟨0, 4⟩` of `v35PeerRefundFlow`, sending it to chain
`1`; chain `0` imports an L1 root with timestamp `1`; chain `0` authorizes the refund of that leg
on an absence proof for the leg `⟨1, 5⟩`, whose source `1` passes chain `0`'s filter because
chain `0` allows peer `1`; chain `0` runs the gate for bundle `2`, the leg `⟨1, 2⟩` of
`mixedFlow 1 1 2` sent from chain `1`, on honest evidence, its legs' sources `0` (chain `0`
itself) and `1` (an allowed peer) passing the filter.  So the premises of
`Properties.DeregisteredPeerBlocksLaterGatesAndRefundsV35` hold with `d = 0` and `s = 2`, with a
gate call and a refund step on `d` in `later` that read the filter on the peer `1`, which is
neither `d` nor `s`; and `s` was allowed before it was deregistered. -/
def Properties.DeregisteredPeerWitnessV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Y : WorldV35) (a : AuthCall) (e : ExecCall),
      a.flow = v35PeerRefundFlow ∧ a.leg = ⟨0, 4⟩ ∧ a.missing = ⟨1, 5⟩
      ∧ e.flow = mixedFlow 1 1 2 ∧ e.leg = ⟨1, 2⟩
      ∧ RunV35 h z0 hl v35BundleCv lengthFlowHash Contracts.LegSourceFilterAtV35.swapSystem
          (genesisV35 (fun _ => v35ClosedHub)) Y
          [.gate 0 e, .authorize a, .append 0 v35PeerRefundFlow 4 1, .admin 0 (.deregister 2),
            .admin 0 (.allow 2), .admin 0 (.allow 1)]
      ∧ (hubsAfter (genesisV35 (fun _ => v35ClosedHub)).hubs
          [.admin 0 (.allow 2), .admin 0 (.allow 1)] 0).peer 2 = true
      ∧ (Y 0).hub.peer 1 = true

/-- **RE-ALLOWING THE PEER LIFTS THE BLOCK.**  In order: chain `1` allows peer `0`, deregisters
it, and allows it again; chain `1` then executes bundle `1` of `subsetFlow 0 1`, whose leg is from
chain `0`.  The log is `later ++ admin 1 (deregister 0) :: earlier` with a gate call on `1` in
`later` presenting a leg from `0`, so the premise "no `admin d (allow s)` in `later`" of
`Properties.DeregisteredPeerBlocksLaterGatesAndRefundsV35` cannot be dropped.  This is the
behaviour `protocol-docs/interop-gating.md:196` documents.  A counterpart: one instance over
`RunV35` of the stronger `Contracts.LegSourceFilterAtV35.Properties.ReallowRestoresGateAtV35`.
It also parallels the second conjunct of
`Contracts.InteropHandlerAtV35.Properties.ReceiveFilterIsReadAtTheGateAtV35` (after the peer is
allowed again the verdict passes when the other checks do), with the verdict read on chain `1`'s
bridgehub instead of taken as an input. -/
def Properties.ReallowedPeerGateWitnessV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Y : WorldV35) (e : ExecCall),
      e.flow = subsetFlow 0 1 ∧ e.leg = ⟨0, 1⟩
      ∧ RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1)
          (genesisV35 (fun _ => v35ClosedHub)) Y
          [.gate 1 e, .admin 1 (.allow 0), .admin 1 (.deregister 0), .admin 1 (.allow 0)]
      ∧ (Y 1).status 1 = .FullyExecuted

/-- **ONE CODE CALL THAT MARKS TWO KEYS MEETS THE PREMISES OF
`CodeAuthorizeCallIsAuthorizeStepsV35`.**  In order: chain `1` allows peers `0` and `2`; chain
`1` appends legs `⟨1, 2⟩` and `⟨1, 3⟩` of `v35SameChainLegsFlow`, sending both to chain `0` (the
second insert's walk hops once); chain `1` imports an L1 root with timestamp `1`.  A code
`authorizeRefund` call on chain `1` presenting `v35SameChainLegsFlow`, with missing leg
`⟨2, 4⟩` (chain `2` never commits in `mixedSystem 1`) and an absence proof `(N, p)`, then meets
every premise of `Properties.CodeAuthorizeCallIsAuthorizeStepsV35` with `x = 1`: the flow is
checked and sorted, the missing leg is in it and its absence proof passes, chain `1` allows its
source `2`, chain `1` has a root after the deadline, and both logged `append`s on chain `1` are
of the presented flow itself, so none clashes with it.  Two keys of the flow are `Committed` on
chain `1`, and the code's loop marks both `Revertable` in that one call. -/
def Properties.CodeAuthorizeCallIsAuthorizeStepsWitnessV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Y : WorldV35) (N : ℕ) (p : ImtProof),
      RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1)
          (genesisV35 (fun _ => v35ClosedHub)) Y
          [.append 1 v35SameChainLegsFlow 3 0, .append 1 v35SameChainLegsFlow 2 0,
            .admin 1 (.allow 2), .admin 1 (.allow 0)]
      ∧ FlowIdChecked lengthFlowHash v35SameChainLegsFlow
      ∧ (v35SameChainLegsFlow.legs.map FlowLeg.bundleHash).Pairwise (· < ·)
      ∧ (⟨2, 4⟩ : FlowLeg) ∈ v35SameChainLegsFlow.legs
      ∧ LegRefundableBy h z0 hl v35BundleCv (mixedSystem 1) v35SameChainLegsFlow ⟨2, 4⟩ N p
      ∧ SourceAllowedV35 (Y 1).hub 1 2
      ∧ (∃ blk, v35SameChainLegsFlow.deadline < (Y 1).roots.stored blk)
      ∧ (∀ l ∈ v35SameChainLegsFlow.legs, ∀ (F' : Flow) (dest : Chain),
          CallV35.append 1 F' l.bundleHash dest ∈
            [.append 1 v35SameChainLegsFlow 3 0, .append 1 v35SameChainLegsFlow 2 0,
              .admin 1 (.allow 2), .admin 1 (.allow 0)] →
          ¬ FlowIdClash lengthFlowHash v35SameChainLegsFlow F')
      ∧ (Y 1).base.mgr.legState v35SameChainLegsFlow.flowId 2 = .Committed
      ∧ (Y 1).base.mgr.legState v35SameChainLegsFlow.flowId 3 = .Committed
      ∧ (RefundClosesAppend.markCommittedRevertable (Y 1).base.mgr v35SameChainLegsFlow.flowId
          (v35SameChainLegsFlow.legs.map FlowLeg.bundleHash)).legState
            v35SameChainLegsFlow.flowId 2 = .Revertable
      ∧ (RefundClosesAppend.markCommittedRevertable (Y 1).base.mgr v35SameChainLegsFlow.flowId
          (v35SameChainLegsFlow.legs.map FlowLeg.bundleHash)).legState
            v35SameChainLegsFlow.flowId 3 = .Revertable

end Contracts.SystemAtV35
