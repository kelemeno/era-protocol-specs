import EraSpec.Protocol.InteropAtomicity.Specs.SystemAtV35

/-!
# Properties: the composed system at `draft/v0.35.0`

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.SystemAtV35` (pin `b17415d20`); proofs
in `EraSpec.Protocol.InteropAtomicity.Proofs.SystemAtV35`.  No statement takes a hash premise.

## What is here

* **The pin's results hold at v35.**  The managers of every `RunV35` run form a pin
  `Contracts.Refund.ReachLog` run with the run's `authorizeRefund` steps as its log, and a pin
  `Contracts.FlowBinding.RunLog` run with its gate and refund calls as its log
  (`Properties.RunV35ProjectsToReachLog`, `Properties.RunV35ProjectsToRunLog`).  So every result
  stated over those two relations holds of the managers of a v35 run;
  `Properties.V35ExecutedObligationNeverRefundedOrBreak` is one, transferred.
* **Refund before append, on one chain.**  `latestInteropRootTimestamp` never decreases and
  stays the maximum of the stored timestamps (`Properties.LatestRootTimestampMonotoneMaxV35`).
  A chain on which a refund was authorized has imported an L1 root past that flow's deadline
  (`Properties.RefundedChainLatestPastDeadlineV35`), so every later `append` on that chain is of
  a flow with a strictly later deadline (`Properties.NoAppendAfterRefundOnSameChainV35`).  This
  is the ordering the NatSpec at `AtomicFlowManager.sol:112-119` describes.  On the witness run,
  a leg of the refunded flow passes every other check of `append` on the refunding chain and
  only the expired-flow gate rejects it (`Properties.WithoutDeadlineGateAppendAfterRefundV35`).
  The gate binds only the chain that imported the root: on the same run another chain appends
  a leg of the refunded flow after the refund (`Properties.RefundThenAppendWitnessV35`).
* **The receive filter is read when a call runs.**  A run's bridgehubs are the starting ones
  with its logged admin calls replayed (`Properties.HubsAreReplayedAdminLogV35`), and every
  logged gate and refund passed the receive filter on the bridgehub of its time
  (`Properties.GateFilterHeldWhenLoggedV35`, `Properties.RefundFilterHeldWhenLoggedV35`).  A
  bundle leaves `Unreceived` only through a logged gate call
  (`Properties.StatusLeavesUnreceivedOnlyThroughGateV35`).  After a peer is deregistered on a
  chain, until it is allowed again no later gate there presents a leg from it and no later
  refund there has its missing leg on it
  (`Properties.DeregisteredPeerBlocksLaterGatesAndRefundsV35`); re-allowing lifts the block
  (`Properties.ReallowedPeerGateWitnessV35`).  A bundle verified before the deregistration
  still executes after it (`Properties.VerifiedBundleExecutesAfterDeregistrationV35`), as
  `protocol-docs/interop-gating.md:195-197` states.
* **Once per leg.**  On a run from genesis no obligation is appended twice, since no step
  returns a manager key to `Unset` (`Properties.AppendedAtMostOnceV35`).
* **The refund simplification.**  The code's `authorizeRefund` marks `Committed` keys in the
  manager of the chain that runs it; the model marks a leg on its declared chain.  On a run from
  genesis every key that is not `Unset` was appended on its chain by a logged `append` whose
  checked, sorted flow declares it there (`Properties.SetKeyHasLoggedAppendV35`), so a
  `Committed` key the code would mark for a checked flow is declared by that flow on the
  marking chain, or that flow and a logged `append`'s flow clash on `fh`
  (`Properties.CodeAuthorizeMarksDeclaredLegOrLoggedClashV35`).

## Scope

The model drops checks of the code that can only reject (the spec's "What differs from the
code"), so the exclusion results here (`…NoAppend…`, `…Blocks…`) are stated over a relation
with more runs than those checks would allow.  Two modelling choices are not of that kind: the
tree side of every proof is the fixed history `S`, as at the pin, and a refund step marks a leg
on its declared chain, which `Properties.CodeAuthorizeMarksDeclaredLegOrLoggedClashV35` bounds.
The witnesses are runs of the model.  Not covered: a projection to the pin's
`Contracts.AppendPath.SysSteps` (it requires the pin's five-hop search and `InsertOkV35` has no
hop bound; none is proved here), liveness, and the settlement layer's own clock (`roots` is a
free sequence of imports).
-/

namespace Contracts.SystemAtV35

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.FlowBinding Contracts.AppendPath

/-! ## The pin's results hold at v35 -/

/-- **THE MANAGERS OF A v35 RUN ARE A LOGGED REFUND RUN.**  For every v35 run, the managers form a
`Contracts.Refund.ReachLog` run whose log is the run's `authorizeRefund` steps, in the same
order.  So every statement of `Properties/Refund.lean` over `ReachLog` applies to them. -/
def Properties.RunV35ProjectsToReachLog : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log → ReachLog h z0 hl cv fh S X.mgrs Y.mgrs (authLog log)

/-- **THE MANAGERS AND GATE CALLS OF A v35 RUN ARE A FLOW-BINDING RUN.**  For every v35 run, the
managers form a `Contracts.FlowBinding.RunLog` run whose log is the run's gate calls (as
`execute`) and `authorizeRefund` steps, in the same order.  So every statement of
`Properties/FlowBinding.lean` over `RunLog` applies to them.  The status edges that run no gate
are not in that log. -/
def Properties.RunV35ProjectsToRunLog : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log → RunLog h z0 hl cv fh S X.mgrs Y.mgrs (checkedLog log)

/-- **AN EXECUTED OBLIGATION IS NEVER REFUNDED AT v35, OR A LOCATED BREAK.**
`Contracts.Refund.Properties.ExecutedObligationNeverRefundedOrBreak`, transferred along
`Properties.RunV35ProjectsToReachLog`: if leg `leg` of `F` passes the pin's gate on evidence `ev`
(`ExecutedViaBy`) against a well-formed history `S`, then in every v35 run from genesis its
obligation is not past `Committed`, or a logged `authorizeRefund` step that marked it carries a
`RefundBreak`. -/
def Properties.V35ExecutedObligationNeverRefundedOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (H0 : Chain → Hub) (Y : WorldV35) (log : List CallV35),
      RunV35 h z0 hl cv fh S (genesisV35 H0) Y log →
        ¬ Refunded Y.mgrs (obligationOf F leg)
          ∨ RefundBreak h z0 hl fh S F ev (obligationOf F leg) (authLog log)

/-! ## Refund before append, on one chain -/

/-- **`latestInteropRootTimestamp` NEVER DECREASES AND STAYS THE MAXIMUM.**  Along every v35 run
from a world whose root storage keeps its running maximum (`RootsWf`), it keeps it, and no
chain's `latest` decreases. -/
def Properties.LatestRootTimestampMonotoneMaxV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log → RootsWf X →
      RootsWf Y ∧ ∀ c, (X c).roots.latest ≤ (Y c).roots.latest

/-- **A CHAIN THAT AUTHORIZED A REFUND HAS IMPORTED A ROOT PAST THAT FLOW'S DEADLINE.**  Along
every v35 run from a `RootsWf` world, for every logged `authorizeRefund` step `a`, the chain it
ran on (`a.leg.chain`) ends the run with `latestInteropRootTimestamp` strictly above
`a.flow.deadline`. -/
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
constrained (`Properties.RefundThenAppendWitnessV35`). -/
def Properties.NoAppendAfterRefundOnSameChainV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log → RootsWf X →
      ∀ (later : List CallV35) (a : AuthCall) (earlier : List CallV35),
        log = later ++ CallV35.authorize a :: earlier →
          ∀ (c : Chain) (F : Flow) (b : UInt256) (dest : Chain),
            CallV35.append c F b dest ∈ later → c = a.leg.chain → a.flow.deadline < F.deadline

/-! ## The receive filter is read when a call runs -/

/-- **THE BRIDGEHUBS ARE THE STARTING ONES WITH THE LOGGED ADMIN CALLS REPLAYED.**  Along every
v35 run, every chain's bridgehub at the end is `hubsAfter` of the starting bridgehubs and the
run's log. -/
def Properties.HubsAreReplayedAdminLogV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log → Y.hubs = hubsAfter X.hubs log

/-- **EVERY LOGGED GATE PASSED, ON THE BRIDGEHUB OF ITS TIME.**  Along every v35 run, if the log
is `later ++ gate d e :: earlier`, then `e`'s evidence verified (`ExecCall.Verified`) and every
leg of `e.flow` passed the receive filter on chain `d`'s bridgehub after the admin calls of
`earlier`, which is the bridgehub `d` had when the gate ran. -/
def Properties.GateFilterHeldWhenLoggedV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log →
      ∀ (later : List CallV35) (d : Chain) (e : ExecCall) (earlier : List CallV35),
        log = later ++ CallV35.gate d e :: earlier →
          e.Verified h z0 hl cv fh S
            ∧ ∀ l ∈ e.flow.legs, SourceAllowed (hubsAfter X.hubs earlier d) d l.chain

/-- **EVERY LOGGED REFUND PASSED, ON THE BRIDGEHUB OF ITS TIME.**  Along every v35 run, if the log
is `later ++ authorize a :: earlier`, then `a`'s checks verified (`AuthCall.Verified`) and the
missing leg's source passed the receive filter on the bridgehub of the chain `a` ran on, after
the admin calls of `earlier`. -/
def Properties.RefundFilterHeldWhenLoggedV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log →
      ∀ (later : List CallV35) (a : AuthCall) (earlier : List CallV35),
        log = later ++ CallV35.authorize a :: earlier →
          a.Verified h z0 hl cv fh S
            ∧ SourceAllowed (hubsAfter X.hubs earlier a.leg.chain) a.leg.chain a.missing.chain

/-- **A DEREGISTERED PEER BLOCKS LATER GATES AND REFUNDS ON THAT CHAIN UNTIL IT IS ALLOWED
AGAIN.**  Along every v35 run, if the log is `later ++ admin d (deregister s) :: earlier` with
`s ≠ d`, and `later` has no `admin d (allow s)`, then no gate call on `d` in `later` presents a
flow with a leg from `s`, and no refund step on `d` in `later` has its missing leg on `s`.  The
calls before the deregistration are not constrained
(`Properties.VerifiedBundleExecutesAfterDeregistrationV35`). -/
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
on `d` whose executing bundle is `b`.  The status edges that skip the gate start from
`Verified` or `Unbundled` only. -/
def Properties.StatusLeavesUnreceivedOnlyThroughGateV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S X Y log →
      ∀ (d : Chain) (b : UInt256), (X d).status b = .Unreceived → (Y d).status b ≠ .Unreceived →
        ∃ e, CallV35.gate d e ∈ log ∧ e.leg.bundleHash = b

/-! ## Once per leg -/

/-- **EACH OBLIGATION IS APPENDED AT MOST ONCE AT v35.**  Along every v35 run from genesis, the
appended obligations `⟨flowId, bundleHash, chain⟩` are pairwise distinct, and the key of every
one of them is not `Unset` on its chain at the end.  This is the manager's
`ManagerLegAlreadyCommitted` check (`AtomicFlowManager.sol:162-164`): no step returns a key to
`Unset`. -/
def Properties.AppendedAtMostOnceV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (H0 : Chain → Hub) (Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S (genesisV35 H0) Y log →
      (appendLog log).Nodup
        ∧ ∀ o ∈ appendLog log, (Y o.chain).base.mgr.legState o.flowId o.bundleHash ≠ .Unset

/-! ## The refund simplification -/

/-- **A KEY THAT IS NOT `Unset` WAS APPENDED ON ITS CHAIN BY A LOGGED CALL.**  Along every v35 run
from genesis, if key `(f, b)` is not `Unset` in chain `x`'s manager, the log has an `append` of
`b` on `x` whose flow has id `f`, passed `_checkFlowId`, declares `b` on `x`, and has strictly
ascending bundle hashes. -/
def Properties.SetKeyHasLoggedAppendV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (H0 : Chain → Hub) (Y : WorldV35) (log : List CallV35),
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
Then `F` declares `l` on `x`, or the log has an `append` of
`l.bundleHash` on `x` whose flow and `F` clash on `fh` (`FlowIdClash`).  So, up to such a
clash, the code marks only legs the presented flow declares on the chain running it, which is
what `RunV35.authorize` (like the pin's `ReachLog`) models. -/
def Properties.CodeAuthorizeMarksDeclaredLegOrLoggedClashV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (H0 : Chain → Hub) (Y : WorldV35) (log : List CallV35),
    RunV35 h z0 hl cv fh S (genesisV35 H0) Y log →
      ∀ (x : Chain) (F : Flow) (l : FlowLeg), FlowIdChecked fh F → l ∈ F.legs →
        (Y x).base.mgr.legState F.flowId l.bundleHash = .Committed →
          l.chain = x
            ∨ ∃ (F' : Flow) (dest : Chain), CallV35.append x F' l.bundleHash dest ∈ log
                ∧ FlowIdClash fh F F'

/-! ## Witnesses and countermodels

Every run below starts at `genesisV35 (fun _ => v35ClosedHub)` (no chain allows or registers any
peer), uses the fixed history `mixedSystem 1`, the commit value `v35BundleCv` and
`lengthFlowHash`, and holds for every node hash, padding constant and leaf hash.

* `Properties.RefundThenAppendWitnessV35` meets the premises of the projections, the root
  results, `NoAppendAfterRefundOnSameChainV35`, `V35ExecutedObligationNeverRefundedOrBreak`,
  `AppendedAtMostOnceV35` (three appends),
  `SetKeyHasLoggedAppendV35` and `CodeAuthorizeMarksDeclaredLegOrLoggedClashV35`, with each
  disjunct of the last firing alone on one instance.
* `Properties.WithoutDeadlineGateAppendAfterRefundV35` shows the expired-flow gate is
  load-bearing for `NoAppendAfterRefundOnSameChainV35`.
* `Properties.VerifiedBundleExecutesAfterDeregistrationV35` meets the premises of the
  bridgehub and status results with a gate call in the log.
* `Properties.DeregisteredPeerWitnessV35` meets the premises of
  `DeregisteredPeerBlocksLaterGatesAndRefundsV35` with a gate and a refund on the chain after
  the deregistration, the refund's filter passing on an allowed peer.
* `Properties.ReallowedPeerGateWitnessV35` shows that the premise "no `allow s` in `later`" is
  needed. -/

/-- **A REFUND, THEN APPENDS: ON THE SAME CHAIN ONLY WITH A LATER DEADLINE.**  In order:
chain `1` allows peer `0` and chain `0` allows peer `1`; chain `1` appends leg `⟨1, 2⟩` of
`v35RefundFlow` (deadline `0`), sending it to chain `0`; chain `1` imports an L1 root with
timestamp `1` at block `0`; chain `1` authorizes the refund of that leg on an absence proof for
the never-appended leg `⟨1, 3⟩`; chain `0` appends leg `⟨0, 1⟩` of the same `v35RefundFlow`,
sending it to chain `1`; chain `1` appends leg `⟨1, 4⟩` of `v35LaterFlow` (deadline `1`), the
tree's walk hopping once.  Then:

* the start world is `RootsWf`; the log is `later ++ authorize a :: earlier` with both appends
  above in `later`, and its authorize log is `[a]`;
* the history is `Wf` and `subsetFlow 0 1` executes on honest evidence (`ExecutedViaBy`); some
  obligation is refunded, while that executed obligation is neither refunded nor carries a
  `RefundBreak` against the authorize log;
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
    ∃ (Y : WorldV35) (a : AuthCall) (ev : GateEvidence),
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
      ∧ Wf (mixedSystem 1)
      ∧ ExecutedViaBy h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) (subsetFlow 0 1) ev ⟨0, 1⟩
      ∧ (∃ o, Refunded Y.mgrs o)
      ∧ ¬ Refunded Y.mgrs (obligationOf (subsetFlow 0 1) ⟨0, 1⟩)
      ∧ ¬ RefundBreak h z0 hl lengthFlowHash (mixedSystem 1) (subsetFlow 0 1) ev
            (obligationOf (subsetFlow 0 1) ⟨0, 1⟩) [a]
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

/-- **COUNTERMODEL: WITHOUT THE EXPIRED-FLOW GATE, A LEG OF THE REFUNDED FLOW IS APPENDED AFTER
THE REFUND.**  A run with the calls of `Properties.RefundThenAppendWitnessV35` ends in a world in
which the never-appended leg `⟨1, 3⟩` of the refunded `v35RefundFlow` passes every check of `append` on
chain `1` except `ManagerFlowDeadlinePassed` (`AppendOkV35WithoutDeadlineGate`, from hint `0`,
landing on leaf `1`), while the real `append` rejects it from every hint.  So the expired-flow
gate, which the pin's `append` did not have, is the check that makes
`Properties.NoAppendAfterRefundOnSameChainV35` hold on this run. -/
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
documents: the filter is read when the bundle is verified. -/
def Properties.VerifiedBundleExecutesAfterDeregistrationV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Z Y : WorldV35) (e : ExecCall),
      e.flow = subsetFlow 0 1 ∧ e.leg = ⟨0, 1⟩
      ∧ RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1)
          (genesisV35 (fun _ => v35ClosedHub)) Z
          [.admin 1 (.deregister 0), .gate 1 e, .admin 1 (.allow 0)]
      ∧ (genesisV35 (fun _ => v35ClosedHub) 1).status 1 = .Unreceived
      ∧ (Z 1).status 1 = .Verified
      ∧ ¬ SourceAllowed (Z 1).hub 1 0
      ∧ NoGateEdge ((Z 1).status 1) .FullyExecuted
      ∧ Y = Z.set 1 { Z 1 with status := setStatus (Z 1).status 1 .FullyExecuted }
      ∧ RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1)
          (genesisV35 (fun _ => v35ClosedHub)) Y
          [.admin 1 (.deregister 0), .gate 1 e, .admin 1 (.allow 0)]
      ∧ (Y 1).status 1 = .FullyExecuted
      ∧ ¬ SourceAllowed (Y 1).hub 1 0
      ∧ ¬ GateOkV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) (Y 1) 1 e
      ∧ checkedLog [.admin 1 (.deregister 0), .gate 1 e, .admin 1 (.allow 0)] ≠ []

/-- **AFTER A DEREGISTRATION, A GATE AND A REFUND ON THE CHAIN THAT AVOID THE PEER.**  In order:
chain `0` allows peers `1` and `2`, then deregisters peer `1`; chain `0` appends leg `⟨0, 2⟩` of
`v35PeerRefundFlow`, sending it to chain `2`; chain `0` imports an L1 root with timestamp `1`;
chain `0` authorizes the refund of that leg on an absence proof for the leg `⟨2, 3⟩`, whose
source `2` passes the receive filter only because chain `0` allows peer `2`; chain `0` runs the
gate for bundle `1` of `subsetFlow 0 1`, whose only leg is from chain `0` itself.  So the premises of
`Properties.DeregisteredPeerBlocksLaterGatesAndRefundsV35` hold with `d = 0`, `s = 1`, and a
gate call and a refund step on `d` in `later`. -/
def Properties.DeregisteredPeerWitnessV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Y : WorldV35) (a : AuthCall) (e : ExecCall),
      a.flow = v35PeerRefundFlow ∧ a.leg = ⟨0, 2⟩ ∧ a.missing = ⟨2, 3⟩
      ∧ e.flow = subsetFlow 0 1 ∧ e.leg = ⟨0, 1⟩
      ∧ RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1)
          (genesisV35 (fun _ => v35ClosedHub)) Y
          [.gate 0 e, .authorize a, .append 0 v35PeerRefundFlow 2 2, .admin 0 (.deregister 1),
            .admin 0 (.allow 2), .admin 0 (.allow 1)]
      ∧ (hubsAfter (genesisV35 (fun _ => v35ClosedHub)).hubs
          [.append 0 v35PeerRefundFlow 2 2, .admin 0 (.deregister 1), .admin 0 (.allow 2),
            .admin 0 (.allow 1)] 0).peer 2 = true

/-- **RE-ALLOWING THE PEER LIFTS THE BLOCK.**  In order: chain `1` allows peer `0`, deregisters
it, and allows it again; chain `1` then executes bundle `1` of `subsetFlow 0 1`, whose leg is from
chain `0`.  The log is `later ++ admin 1 (deregister 0) :: earlier` with a gate call on `1` in
`later` presenting a leg from `0`, so the premise "no `admin d (allow s)` in `later`" of
`Properties.DeregisteredPeerBlocksLaterGatesAndRefundsV35` cannot be dropped.  This is the
behaviour `protocol-docs/interop-gating.md:196` documents. -/
def Properties.ReallowedPeerGateWitnessV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Y : WorldV35) (e : ExecCall),
      e.flow = subsetFlow 0 1 ∧ e.leg = ⟨0, 1⟩
      ∧ RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1)
          (genesisV35 (fun _ => v35ClosedHub)) Y
          [.gate 1 e, .admin 1 (.allow 0), .admin 1 (.deregister 0), .admin 1 (.allow 0)]
      ∧ (Y 1).status 1 = .FullyExecuted

end Contracts.SystemAtV35
