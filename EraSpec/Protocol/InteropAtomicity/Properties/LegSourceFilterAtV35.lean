import EraSpec.Protocol.InteropAtomicity.Specs.LegSourceFilterAtV35

/-!
# Properties: the v35 receive filter keeps the exclusion results and can strand committed legs

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.LegSourceFilterAtV35`
(`draft/v0.35.0` at `d9f678900`).  Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.LegSourceFilterAtV35`.

## Safety: every exclusion result survives

The filter only rejects.  Every v35 run, admin steps included, is a pin run once the allow-lists
are forgotten (`Properties.RunAtV35ProjectsToRunLog`, `Properties.SysStepsAtV35ProjectsToSysSteps`),
and under full mutual allowance the two models have the same runs
(`Properties.RunLogIsRunAtV35UnderFullAllowance`).  So the pin's exclusion results hold at v35
with the same located breaks and no new premise: `ExecutedExcludesAnyRefundOrBreakAtV35`,
`ExecutedObligationNeverRefundedOrBreakAtV35`, `OneExecutionFreezesTheFlowOrBreakAtV35`,
`SystemOncePerLegAtV35`, `SystemExecutedObligationNeverRefundedOrBreakAtV35`, and the evidence
half of none-or-all (`NoneOrAllOrBreakAtV35`, `ExecutedImpliesRealFlowFinalizableOrLoggedClashAtV35`).

The filter also adds safety content of its own.  A double outcome at v35 needs a forged proof
about a chain that the chain accepting the proof allowed when it accepted it
(`Properties.LoggedGateExcludesLoggedRefundOrAllowedBreakAtV35`).  This is the argument of
`protocol-docs/interop-gating.md:194-197` for filtering refunds too.  The pin's forged-sibling
execution passes the v35 gate exactly on destinations that allow the forging chain
(`Properties.ForgedSiblingExecutionNeedsAllowedForgerAtV35`).  The double payment through a
forged absence proof about a foreign chain is authorized at v35 exactly when the refunding chain
allows the forging chain (`Properties.ForeignForgedRefundNeedsAllowedForgerAtV35`).

## Liveness: a committed leg can be stranded, exactly when the filter blocks it

`Properties.SwapStrandedByDeregistrationAtV35` and
`Properties.IncompleteSwapRefundStrandedByDeregistrationAtV35` refute "a committed leg is always
finalizable or refundable" with one deregistration after commit.  Upstream does not claim it:
this is its documented limitation "K1: stuck flows" (`protocol-docs/interop-gating.md:250-260`).
The two cases are K1's two cases:

* **complete flow** (both legs of a swap committed in time): the destination of one leg
  deregisters the other leg's source.  That leg can execute on no evidence, while its sibling has
  already executed, and no leg can be refunded anywhere without a forged proof.  The swap has
  completed in one direction only.  The pin calls the flow finalizable (`FlowFinalizableBy`).
* **incomplete flow** (one leg never committed): the committed leg's own chain deregisters the
  missing leg's source.  No refund of the committed leg passes there, though the pin's
  `authorizeRefund` checks all pass.  No destination can execute either.

`Properties.StrandedIffAtV35` characterises stranding exactly, for every flow that passes
`_checkFlowId`, has nonzero commit values, and whose missing legs' chains settle past the
deadline.  A leg is stranded (up to located breaks) iff

* every leg was committed on time and the leg's destination does not allow some leg's source; or
* some leg was not, and the leg's own chain allows the source of no leg that was not.

## Re-allowing restores progress

Deregistering and re-allowing a peer restores the allow-lists exactly
(`Properties.DeregisterThenAllowIsIdentity`).  Both gates are monotone in the allow-lists
(`GateMonotoneInPeersAtV35`, `RefundMonotoneInPeersAtV35`).  In every reachable state, one
`allowPeer` step makes a blocked call with pin-valid evidence pass
(`ReallowRestoresGateAtV35`, `ReallowRestoresRefundAtV35`).  Evidence is a fixed history, and a
stranded leg's manager entry stays `Committed`.  Conversely, until the pair is re-allowed, no
call on that chain accepts evidence from that source (`BlockedUntilReallowedAtV35`).

Re-allowing is a step of the model, enabled at every moment.  On the contracts it is the chain
admin's `ChainRegistrationSender.allowInteropPeer` and a service transaction, which the model
does not check (`Specs`, "What is not modelled"); so "one step restores progress" is a statement
about the allow-list, not about who can or will take the step.

## Witnesses

`SafetyAtV35Witness`, `SystemAtV35Witness`, `StrandedIffAtV35Witness` and `ReallowAtV35Witness`
show the premises of the results above hold together on runs that contain a deregistration.
No result here takes a hash premise; every break in a conclusion is located on a proof that a
named call or a quantified piece of evidence submitted.
-/

namespace Contracts.LegSourceFilterAtV35

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.FlowBinding Contracts.AppendPath

/-! ## The gates -/

/-- **THE v35 GATE IS THE PIN'S GATE AND THE FILTER ON EVERY LEG'S SOURCE.**  The filter sits
inside `requireFlowFinalized`'s loop (`AtomicFlowManager.sol:194-209`) and comes out of it: the
gate passes on chain `d` iff the pin's gate passes and `d` allows every leg's source. -/
def Properties.GateAtV35IffPinGateAndSourcesAllowed : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (P : Peers) (d : Chain) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg
      ↔ ExecutedViaBy h z0 hl cv fh S F ev leg ∧ ∀ l ∈ F.legs, SourceAllowed P d l.chain

/-- **MORE PEERS, MORE EXECUTIONS.**  If chain `d` allows every peer under `Q` that it allows
under `P`, every gate call that passes on `d` under `P` passes under `Q`. -/
def Properties.GateMonotoneInPeersAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (P Q : Peers) (d : Chain), (∀ s, P d s = true → Q d s = true) →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
      ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg → ExecutedViaByAtV35 h z0 hl cv fh S Q d F ev leg

/-- **MORE PEERS, MORE REFUNDS.**  The same for `authorizeRefund`'s timeout check on chain `c`. -/
def Properties.RefundMonotoneInPeersAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System)
    (P Q : Peers) (c : Chain), (∀ s, P c s = true → Q c s = true) →
    ∀ (F : Flow) (m : FlowLeg) (N : ℕ) (q : ImtProof),
      LegRefundableByAtV35 h z0 hl cv S P c F m N q → LegRefundableByAtV35 h z0 hl cv S Q c F m N q

/-- **DEREGISTERING AND THEN RE-ALLOWING A PEER CHANGES NOTHING.**  If chain `c` allowed `s`,
`deregisterChainForInterop(s)` followed by `allowInteropPeer(s, _)` on `c` gives back exactly the
allow-lists it started from, so every gate and refund check reads as before. -/
def Properties.DeregisterThenAllowIsIdentity : Prop :=
  ∀ (P : Peers) (c s : Chain), P c s = true → (P.deregister c s).allow c s = P

/-! ## Safety: every v35 run is a pin run -/

/-- **EVERY v35 RUN IS A PIN RUN.**  Forget the allow-lists, drop the admin steps, and the run is
a `Contracts.FlowBinding.RunLog` between the same managers, gate calls as `execute` and
`authorizeRefund` calls as `authorize`.  So every result over `RunLog` (and, through
`RunLogAuthCallsReachLog`, over `Contracts.Refund.ReachLog`) holds at v35. -/
def Properties.RunAtV35ProjectsToRunLog : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (dst : Dest) (X Y : WorldAtV35) (log : List CallAtV35),
    RunAtV35 h z0 hl cv fh S dst X Y log → RunLog h z0 hl cv fh S X.mgrs Y.mgrs (pinLog log)

/-- **UNDER FULL MUTUAL ALLOWANCE THE FILTER CHANGES NOTHING.**  Every pin run is a v35 run in
which every chain allows every peer throughout, with the same calls. -/
def Properties.RunLogIsRunAtV35UnderFullAllowance : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (dst : Dest) (Ms Ns : Managers) (log : List CheckedCall),
    RunLog h z0 hl cv fh S Ms Ns log →
      ∃ log' : List CallAtV35,
        RunAtV35 h z0 hl cv fh S dst ⟨Ms, allPeersAllowed⟩ ⟨Ns, allPeersAllowed⟩ log'
          ∧ pinLog log' = log

/-- **EXECUTION EXCLUDES EVERY REFUND IN THE FLOW, OR A LOCATED BREAK, AT v35.**  If a leg passed
the v35 gate on any chain under any allow-lists, then for every leg `other` of the flow, every
chain `c` and allow-lists `Q`, and every submitted timeout evidence `(N, q)`: the v35 timeout
check on `c` fails, or the inclusion proof `ev other` carries a break, or `q` does.  The pin's
`ExecutedExcludesAnyRefundOrBreak`, with nothing added: the filter cannot open a refund. -/
def Properties.ExecutedExcludesAnyRefundOrBreakAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (P : Peers) (d : Chain) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg →
    ∀ other ∈ F.legs, ∀ (Q : Peers) (c : Chain) (N : ℕ) (q : ImtProof),
      ¬ LegRefundableByAtV35 h z0 hl cv S Q c F other N q
        ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2
        ∨ AbsenceBreak h z0 hl S F.deadline other.chain N q

/-- **THE EVIDENCE HALF OF NONE-OR-ALL, AT v35.**  For every flow, evidence, chain and
allow-lists: every leg of the flow has presentable accepted evidence (the pin's
`FlowFinalizableBy`), or the evidence executes no leg at v35, or it carries a break on the first
stranded leg (`PinnedGateBreak`).  Read it with `Properties.SwapStrandedByDeregistrationAtV35`:
"every leg has evidence" no longer means "every leg's destination can execute". -/
def Properties.NoneOrAllOrBreakAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (P : Peers) (d : Chain) (F : Flow) (ev : GateEvidence),
      FlowFinalizableBy h z0 hl cv S A F
        ∨ (∀ leg, ¬ ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg)
        ∨ PinnedGateBreak h z0 hl cv S A F ev

/-- **A LOGGED EXECUTION AND A LOGGED REFUND OF ONE FLOW ID NEED A FORGED PROOF ABOUT AN ALLOWED
CHAIN.**  In a v35 run, take a gate call `e` (checked under `P` on its bundle's destination) and an
`authorizeRefund` call `a` (checked under `Q` on `a.leg.chain`) claiming one flow id.  Then:

* the inclusion proof `e` submitted for `a`'s missing leg carries a break, AND `e`'s destination
  allowed that leg's source when it accepted the proof; or
* `a`'s absence proof carries a break, AND `a`'s chain allowed the missing leg's source when it
  accepted the proof; or
* the two flows clash on the flow-id hash.

The pin's `LoggedExecutionExcludesLoggedRefundOrBreak` locates the same breaks.  What v35 adds
is that the forged proof is about a chain the accepting chain allowed at that moment: a broken
prover on a chain nobody allows cannot cause a double payment
(`protocol-docs/interop-gating.md:194-197`). -/
def Properties.LoggedGateExcludesLoggedRefundOrAllowedBreakAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (dst : Dest) (X Y : WorldAtV35) (log : List CallAtV35),
    RunAtV35 h z0 hl cv fh S dst X Y log →
    ∀ (e : ExecCall) (P : Peers), CallAtV35.gate e P ∈ log →
    ∀ (a : AuthCall) (Q : Peers), CallAtV35.authorize a Q ∈ log → a.flow.flowId = e.flow.flowId →
      (InclusionBreak h z0 hl S a.missing.chain (e.evidence a.missing).1 (e.evidence a.missing).2
          ∧ SourceAllowed P (dst e.leg.bundleHash) a.missing.chain)
        ∨ (AbsenceBreak h z0 hl S a.flow.deadline a.missing.chain a.batch a.proof
          ∧ SourceAllowed Q a.leg.chain a.missing.chain)
        ∨ FlowIdClash fh e.flow a.flow

/-- **AN EXECUTED OBLIGATION IS NEVER REFUNDED, OR A LOCATED BREAK, AT v35.**  If leg `leg` of `F`
passed the v35 gate on evidence `ev`, then in every v35 run from fresh managers, under any initial
allow-lists and with any admin steps, its obligation stays at `Committed` or below, or a logged
`authorizeRefund` call that marked it carries a `RefundBreak`.  The pin's
`ExecutedObligationNeverRefundedOrBreak`. -/
def Properties.ExecutedObligationNeverRefundedOrBreakAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (P : Peers) (d : Chain) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg →
    ∀ (dst : Dest) (P₀ : Peers) (Y : WorldAtV35) (log : List CallAtV35),
      RunAtV35 h z0 hl cv fh S dst ⟨emptyManagers, P₀⟩ Y log →
        ¬ Refunded Y.mgrs (obligationOf F leg)
          ∨ RefundBreak h z0 hl fh S F ev (obligationOf F leg) (authLogAtV35 log)

/-- **ONE EXECUTION FREEZES THE FLOW, OR A LOCATED BREAK, AT v35.**  The same for every leg of the
flow. -/
def Properties.OneExecutionFreezesTheFlowOrBreakAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (P : Peers) (d : Chain) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg →
    ∀ (dst : Dest) (P₀ : Peers) (Y : WorldAtV35) (log : List CallAtV35),
      RunAtV35 h z0 hl cv fh S dst ⟨emptyManagers, P₀⟩ Y log →
      ∀ other ∈ F.legs,
        ¬ Refunded Y.mgrs (obligationOf F other)
          ∨ RefundBreak h z0 hl fh S F ev (obligationOf F other) (authLogAtV35 log)

/-- **THE REAL FLOW HAS EVIDENCE FOR EVERY LEG, OR A LOCATED BREAK, OR A LOGGED CLASH, AT v35.**
The pin's `ExecutedImpliesRealFlowFinalizableOrLoggedClash` over a v35 run: for a logged gate
call `e`, every flow that a logged call presented under `e`'s flow id has presentable accepted
evidence for every leg, or `e`'s evidence carries a break on the first stranded leg, or the two
flows clash.  Evidence only: whether each leg's destination admits it is
`Properties.StrandedIffAtV35`. -/
def Properties.ExecutedImpliesRealFlowFinalizableOrLoggedClashAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (dst : Dest) (X Y : WorldAtV35) (log : List CallAtV35), RunAtV35 h z0 hl cv fh S dst X Y log →
    ∀ (e : ExecCall) (P : Peers), CallAtV35.gate e P ∈ log →
    ∀ c ∈ pinLog log, c.flow.flowId = e.flow.flowId →
      FlowFinalizableBy h z0 hl cv S A c.flow
        ∨ PinnedGateBreak h z0 hl cv S A e.flow e.evidence
        ∨ FlowIdClash fh e.flow c.flow

/-- **EVERY v35 SYSTEM RUN IS A PIN SYSTEM RUN.**  Every chain's manager and tree, with the same
append and authorize logs. -/
def Properties.SysStepsAtV35ProjectsToSysSteps : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : SysWorldAtV35) (log : List Obligation) (alog : List AuthCall),
    SysStepsAtV35 h z0 hl cv fh S X Y log alog → SysSteps h z0 hl cv fh S X.chains Y.chains log alog

/-- **AND EVERY PIN SYSTEM RUN IS A v35 SYSTEM RUN UNDER FULL MUTUAL ALLOWANCE.** -/
def Properties.SysStepsIsSysStepsAtV35UnderFullAllowance : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (X Y : Chains) (log : List Obligation) (alog : List AuthCall),
    SysSteps h z0 hl cv fh S X Y log alog →
      SysStepsAtV35 h z0 hl cv fh S ⟨X, allPeersAllowed⟩ ⟨Y, allPeersAllowed⟩ log alog

/-- **ONCE PER LEG, SYSTEM-WIDE, AT v35.**  `Contracts.AppendPath.Properties.SystemOncePerLeg` over
every v35 system run from genesis, under any initial allow-lists and with any admin steps: no
obligation is appended twice, each appended obligation occupies exactly one index of its chain's
tree, and two appended obligations on one chain with one commit value are equal. -/
def Properties.SystemOncePerLegAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (P₀ : Peers) (Y : SysWorldAtV35) (log : List Obligation) (alog : List AuthCall),
    SysStepsAtV35 h z0 hl cv fh S ⟨genesisAll, P₀⟩ Y log alog →
      log.Nodup
        ∧ (∀ o ∈ log, ∃! i, i < (Y.chains o.chain).tree.leafCount
            ∧ ((Y.chains o.chain).tree.leaf i).value = commitOf cv o)
        ∧ (∀ o ∈ log, ∀ o' ∈ log, o.chain = o'.chain → commitOf cv o = commitOf cv o' → o = o')

/-- **THE REFUND MILESTONE FOR THE SYSTEM WITH TREES, AT v35.**  If a leg passed the v35 gate, its
obligation is never past `Committed` in a v35 system run from genesis, or a logged
`authorizeRefund` call that marked it carries a `RefundBreak`. -/
def Properties.SystemExecutedObligationNeverRefundedOrBreakAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (P : Peers) (d : Chain) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg →
    ∀ (P₀ : Peers) (Y : SysWorldAtV35) (log : List Obligation) (alog : List AuthCall),
      SysStepsAtV35 h z0 hl cv fh S ⟨genesisAll, P₀⟩ Y log alog →
        ¬ Refunded Y.chains.mgrs (obligationOf F leg)
          ∨ RefundBreak h z0 hl fh S F ev (obligationOf F leg) alog

/-! ## Liveness: stranded legs -/

/-- **DEREGISTERING A PEER AFTER COMMIT STRANDS A LEG OF A COMPLETE SWAP; THE SWAP COMPLETES IN ONE
DIRECTION ONLY.**  For every node hash, padding constant and leaf hash, in `swapSystem` (both legs
committed in batch 0, so the flow is complete), with full data availability:

* the pin's liveness reading holds: every leg of `mixedFlow 1 1 2` has presentable accepted
  evidence (`FlowFinalizableBy`);
* there is a v35 run from fresh managers under full mutual allowance in which both legs are
  appended, leg `⟨0, 1⟩` passes the gate on its destination (chain `1`), and then chain `0`
  deregisters chain `1`;
* at the end both legs are still `Committed`.  Leg `⟨1, 2⟩` passes the gate on its destination
  `swapDest 2` (chain `0`) on NO evidence, with no hash premise.  No leg of the flow passes the
  timeout check on any chain under any allow-lists, unless the absence proof carries a located
  break.  So leg `⟨1, 2⟩` stays `Committed` on chain `1` with no way forward or back while
  chain `0` keeps chain `1` out.  (Funds are not part of this model; with a burn-and-mint bridge
  on top, its burn is neither delivered nor refundable.);
* one `allowPeer 0 1` step lets leg `⟨1, 2⟩` through the gate on chain `0`. -/
def Properties.SwapStrandedByDeregistrationAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    Wf swapSystem
      ∧ DataAvailable h z0 hl swapSystem (honestAccess h z0 hl swapSystem)
      ∧ FlowFinalizableBy h z0 hl (fun _ b => b) swapSystem (honestAccess h z0 hl swapSystem)
          (mixedFlow 1 1 2)
      ∧ ∃ (Y : WorldAtV35) (log : List CallAtV35) (e : ExecCall),
          RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem swapDest
              ⟨emptyManagers, allPeersAllowed⟩ Y log
            ∧ log = [.deregisterPeer 0 1, .gate e allPeersAllowed]
            ∧ e.flow = mixedFlow 1 1 2 ∧ e.leg = ⟨0, 1⟩
            ∧ Y.peers = allPeersAllowed.deregister 0 1
            ∧ stateOf Y.mgrs (obligationOf (mixedFlow 1 1 2) ⟨0, 1⟩) = .Committed
            ∧ stateOf Y.mgrs (obligationOf (mixedFlow 1 1 2) ⟨1, 2⟩) = .Committed
            ∧ (∀ ev : GateEvidence, ¬ ExecutedViaByAtV35 h z0 hl (fun _ b => b) lengthFlowHash
                swapSystem Y.peers (swapDest 2) (mixedFlow 1 1 2) ev ⟨1, 2⟩)
            ∧ (∀ (Q : Peers) (c : Chain), ∀ m ∈ (mixedFlow 1 1 2).legs, ∀ (N : ℕ) (q : ImtProof),
                ¬ LegRefundableByAtV35 h z0 hl (fun _ b => b) swapSystem Q c (mixedFlow 1 1 2) m N q
                  ∨ AbsenceBreak h z0 hl swapSystem (mixedFlow 1 1 2).deadline m.chain N q)
            ∧ ∃ e' : ExecCall, e'.flow = mixedFlow 1 1 2 ∧ e'.leg = ⟨1, 2⟩
                ∧ RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem swapDest
                    ⟨emptyManagers, allPeersAllowed⟩ ⟨Y.mgrs, Y.peers.allow 0 1⟩
                    (.gate e' (Y.peers.allow 0 1) :: .allowPeer 0 1 :: log)

/-- **DEREGISTERING THE MISSING LEG'S SOURCE STRANDS THE COMMITTED LEG OF AN INCOMPLETE SWAP.**
For every node hash, padding constant and leaf hash, in `mixedSystem 1` (leg `⟨0, 1⟩` committed in
batch 0, leg `⟨1, 2⟩` never committed), there is a v35 run from fresh managers under full mutual
allowance that appends leg `⟨0, 1⟩` on chain `0` and then has chain `0` deregister chain `1`.  At
its end:

* leg `⟨0, 1⟩` is `Committed`, and leg `⟨1, 2⟩` was not committed on time: the flow timed out;
* the pin would refund it: an `authorizeRefund` call `a` for leg `⟨0, 1⟩` on the honest absence
  proof of the missing leg `⟨1, 2⟩` passes every check the pin runs, its proof carries no break,
  and the leg is `Committed`;
* at v35 no timeout evidence for any leg of the flow passes on chain `0`, except a forged absence
  proof for the committed leg `⟨0, 1⟩` itself, which carries a located break;
* no leg of the flow passes the gate on any chain under any allow-lists, unless the proof submitted
  for the missing leg `⟨1, 2⟩` carries a located break;
* after one `allowPeer 0 1` step the same call `a` passes, and leg `⟨0, 1⟩` becomes `Revertable`. -/
def Properties.IncompleteSwapRefundStrandedByDeregistrationAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    Wf (mixedSystem 1)
      ∧ ∃ (Y : WorldAtV35) (log : List CallAtV35) (a : AuthCall),
          RunAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2)) (mixedSystem 1) swapDest
              ⟨emptyManagers, allPeersAllowed⟩ Y log
            ∧ log = [.deregisterPeer 0 1]
            ∧ Y.peers = allPeersAllowed.deregister 0 1
            ∧ stateOf Y.mgrs (obligationOf (mixedFlow 0 1 2) ⟨0, 1⟩) = .Committed
            ∧ ¬ CommittedOnTime (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨1, 2⟩
            ∧ a.flow = mixedFlow 0 1 2 ∧ a.leg = ⟨0, 1⟩ ∧ a.missing = ⟨1, 2⟩
            ∧ a.Verified h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2)) (mixedSystem 1)
            ∧ ¬ AbsenceBreak h z0 hl (mixedSystem 1) (mixedFlow 0 1 2).deadline 1 a.batch a.proof
            ∧ AuthorizeGuard (Y.mgrs 0) 0 1
            ∧ (∀ m ∈ (mixedFlow 0 1 2).legs, ∀ (N : ℕ) (q : ImtProof),
                ¬ LegRefundableByAtV35 h z0 hl (fun _ b => b) (mixedSystem 1) Y.peers 0
                    (mixedFlow 0 1 2) m N q
                  ∨ (m = ⟨0, 1⟩
                    ∧ AbsenceBreak h z0 hl (mixedSystem 1) (mixedFlow 0 1 2).deadline 0 N q))
            ∧ (∀ (Q : Peers) (d : Chain) (ev : GateEvidence) (l : FlowLeg),
                ¬ ExecutedViaByAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
                    (mixedSystem 1) Q d (mixedFlow 0 1 2) ev l
                  ∨ InclusionBreak h z0 hl (mixedSystem 1) 1 (ev ⟨1, 2⟩).1 (ev ⟨1, 2⟩).2)
            ∧ RunAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2)) (mixedSystem 1)
                swapDest ⟨emptyManagers, allPeersAllowed⟩
                ⟨setAt Y.mgrs 0 ((Y.mgrs 0).set 0 1 .Revertable), Y.peers.allow 0 1⟩
                (.authorize a (Y.peers.allow 0 1) :: .allowPeer 0 1 :: log)

/-- **A MISSING LEG HAS HONEST TIMEOUT EVIDENCE WHEREVER ITS SOURCE IS ALLOWED.**  If a leg of a
flow has a nonzero commit value, was not committed on time, and its chain settled a batch after the
deadline, then on every chain `c` that allows its source there is timeout evidence `(N, q)` that
passes the v35 check and carries no break: the honest low-leaf proof against the BEGIN root of
the first late batch.  No hash premise.  The completeness direction of
`Properties.StrandedIffAtV35`. -/
def Properties.RefundEvidenceCompleteAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (F : Flow) (m : FlowLeg), legValue cv F m ≠ 0 → ¬ CommittedOnTime cv S F m →
    SettledAfterDeadline S F m → ∀ (P : Peers) (c : Chain), SourceAllowed P c m.chain →
      ∃ (N : ℕ) (q : ImtProof), LegRefundableByAtV35 h z0 hl cv S P c F m N q
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline m.chain N q

/-- **A COMPLETE FLOW EXECUTES ON A CHAIN EXACTLY WHEN THAT CHAIN ALLOWS EVERY LEG'S SOURCE.**  For a
checked flow every leg of which was committed on time, with data availability: presentable
evidence passes the v35 gate for a leg on chain `d` iff `d` allows every leg's source.  No hash
premise in either direction. -/
def Properties.CompleteFlowGateOpenIffSourcesAllowedAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (F : Flow), FlowIdChecked fh F → (∀ l ∈ F.legs, CommittedOnTime cv S F l) →
    ∀ (leg : FlowLeg), leg ∈ F.legs → ∀ (P : Peers) (d : Chain),
      GateOpenAtV35 h z0 hl cv fh S A P d F leg ↔ ∀ l ∈ F.legs, SourceAllowed P d l.chain

/-- **EXACTLY WHICH LEGS ARE STRANDED.**  Take a well-formed system and a flow that passes
`_checkFlowId` and has nonzero commit values, every leg of which that missed the deadline comes
from a chain that settled past it.  For a leg of that flow, its destination `d` and allow-lists
`P`, the leg is stranded up to located breaks (`StrandedOrBreakAtV35`) iff one of:

* **complete flow**: every leg was committed on time, and `d` does not allow some leg's source;
* **incomplete flow**: some leg was not committed on time, and the leg's own chain `leg.chain`
  allows the source of no leg that was not.

So a deregistration strands exactly the legs it makes satisfy this.  In a complete flow those are
the legs whose destination dropped a leg source; refunds are impossible whatever the allow-lists.
In an incomplete flow they are the committed legs on a chain that dropped every missing leg's
source; no destination can execute. -/
def Properties.StrandedIffAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow), FlowIdChecked fh F → FlowWf cv F →
    (∀ l ∈ F.legs, ¬ CommittedOnTime cv S F l → SettledAfterDeadline S F l) →
    ∀ (leg : FlowLeg), leg ∈ F.legs → ∀ (P : Peers) (d : Chain),
      StrandedOrBreakAtV35 h z0 hl cv fh S P d F leg ↔
        ((∀ l ∈ F.legs, CommittedOnTime cv S F l) ∧ ∃ l ∈ F.legs, ¬ SourceAllowed P d l.chain)
          ∨ ((∃ l ∈ F.legs, ¬ CommittedOnTime cv S F l)
              ∧ ∀ m ∈ F.legs, ¬ CommittedOnTime cv S F m → ¬ SourceAllowed P leg.chain m.chain)

/-- **THE CHARACTERISATION IS NOT VACUOUS, AND BOTH CASES OCCUR.**  For every node hash, padding
constant and leaf hash, the premises of `Properties.StrandedIffAtV35` hold in both swap worlds.
In the complete swap, leg `⟨1, 2⟩` is stranded on its destination after chain `0` drops chain `1`,
and not stranded under full allowance.  In the incomplete swap, leg `⟨0, 1⟩` is stranded after the
same deregistration, and not stranded under full allowance. -/
def Properties.StrandedIffAtV35Witness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    Wf swapSystem ∧ FlowIdChecked lengthFlowHash (mixedFlow 1 1 2)
      ∧ FlowWf (fun _ b => b) (mixedFlow 1 1 2)
      ∧ (∀ l ∈ (mixedFlow 1 1 2).legs, CommittedOnTime (fun _ b => b) swapSystem (mixedFlow 1 1 2) l)
      ∧ StrandedOrBreakAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem
          (allPeersAllowed.deregister 0 1) (swapDest 2) (mixedFlow 1 1 2) ⟨1, 2⟩
      ∧ ¬ StrandedOrBreakAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem allPeersAllowed
          (swapDest 2) (mixedFlow 1 1 2) ⟨1, 2⟩
      ∧ Wf (mixedSystem 1) ∧ FlowIdChecked (honestFlowHash (mixedFlow 0 1 2)) (mixedFlow 0 1 2)
      ∧ FlowWf (fun _ b => b) (mixedFlow 0 1 2)
      ∧ (∀ l ∈ (mixedFlow 0 1 2).legs, SettledAfterDeadline (mixedSystem 1) (mixedFlow 0 1 2) l)
      ∧ ¬ CommittedOnTime (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨1, 2⟩
      ∧ StrandedOrBreakAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
          (mixedSystem 1) (allPeersAllowed.deregister 0 1) (swapDest 1) (mixedFlow 0 1 2) ⟨0, 1⟩
      ∧ ¬ StrandedOrBreakAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
          (mixedSystem 1) allPeersAllowed (swapDest 1) (mixedFlow 0 1 2) ⟨0, 1⟩

/-! ## Re-allowing restores progress -/

/-- **ONE RE-ALLOW LETS A BLOCKED GATE CALL THROUGH.**  In every reachable state of every v35 run,
take a gate call whose evidence passes the pin's gate, and whose bundle's destination allows every
leg's source except possibly `s`.  Then the run extends by `allowPeer` of `s` on that destination
followed by the gate call. -/
def Properties.ReallowRestoresGateAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (dst : Dest) (X Y : WorldAtV35) (log : List CallAtV35) (e : ExecCall) (s : Chain),
    RunAtV35 h z0 hl cv fh S dst X Y log → e.Verified h z0 hl cv fh S →
    (∀ l ∈ e.flow.legs, l.chain = s ∨ SourceAllowed Y.peers (dst e.leg.bundleHash) l.chain) →
      RunAtV35 h z0 hl cv fh S dst X ⟨Y.mgrs, Y.peers.allow (dst e.leg.bundleHash) s⟩
        (.gate e (Y.peers.allow (dst e.leg.bundleHash) s)
          :: .allowPeer (dst e.leg.bundleHash) s :: log)

/-- **ONE RE-ALLOW LETS A BLOCKED REFUND THROUGH.**  In every reachable state of every v35 run,
take an `authorizeRefund` call that passes every check of the pin's, for a leg that is still
`Committed`.  Then the run extends by `allowPeer` of the missing leg's source on the leg's chain,
followed by the call, which marks the leg `Revertable`. -/
def Properties.ReallowRestoresRefundAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (dst : Dest) (X Y : WorldAtV35) (log : List CallAtV35) (a : AuthCall),
    RunAtV35 h z0 hl cv fh S dst X Y log → a.Verified h z0 hl cv fh S →
    AuthorizeGuard (Y.mgrs a.leg.chain) a.flow.flowId a.leg.bundleHash →
      RunAtV35 h z0 hl cv fh S dst X
        ⟨setAt Y.mgrs a.leg.chain
            ((Y.mgrs a.leg.chain).set a.flow.flowId a.leg.bundleHash .Revertable),
          Y.peers.allow a.leg.chain a.missing.chain⟩
        (.authorize a (Y.peers.allow a.leg.chain a.missing.chain)
          :: .allowPeer a.leg.chain a.missing.chain :: log)

/-- **UNTIL RE-ALLOWED, A DROPPED SOURCE STAYS BLOCKED.**  Take a v35 run segment that starts with
chain `c` not allowing `s ≠ c` and contains no `allowPeer c s`.  Then `c` still does not allow
`s` at its end.  No gate call on `c` in the segment accepted a flow with a leg from `s`, and no
`authorizeRefund` call on `c` used a missing leg from `s`. -/
def Properties.BlockedUntilReallowedAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (dst : Dest) (X Y : WorldAtV35) (log : List CallAtV35) (c s : Chain),
    RunAtV35 h z0 hl cv fh S dst X Y log → s ≠ c → X.peers c s = false →
    CallAtV35.allowPeer c s ∉ log →
      Y.peers c s = false
        ∧ (∀ (e : ExecCall) (P : Peers), CallAtV35.gate e P ∈ log → dst e.leg.bundleHash = c →
            ∀ l ∈ e.flow.legs, l.chain ≠ s)
        ∧ (∀ (a : AuthCall) (P : Peers), CallAtV35.authorize a P ∈ log → a.leg.chain = c →
            a.missing.chain ≠ s)

/-! ## The pin's forgeries at v35 -/

/-- **THE PIN'S FORGED-SIBLING EXECUTION PASSES AT v35 EXACTLY WHERE THE FORGING CHAIN IS ALLOWED.**
For every node hash and padding constant, with the toy leaf hash: the evidence `ev` of
`Contracts.FlowBinding.Properties.ForgedSiblingProofLandsInPinnedBreak` executes leg `⟨0, 1⟩` of
`mixedFlow 0 1 2` through the pin's gate.  Its proof for leg `⟨0, 1⟩` is honest and its proof for
the never-committed leg `⟨1, 2⟩` is forged.  At v35 it passes on chain `d` under allow-lists `P`
iff `d` allows chains `0` and `1`, so a destination that does not allow chain `1`, the chain whose
tree the forgery is about, rejects it.  The forgery exists because `toyLeafHash` collides; it
stands in for a broken prover on chain `1`. -/
def Properties.ForgedSiblingExecutionNeedsAllowedForgerAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256), ∃ ev : GateEvidence,
    ExecutedViaBy h z0 toyLeafHash (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
        (mixedSystem 1) (mixedFlow 0 1 2) ev ⟨0, 1⟩
      ∧ ¬ InclusionBreak h z0 toyLeafHash (mixedSystem 1) 0 (ev ⟨0, 1⟩).1 (ev ⟨0, 1⟩).2
      ∧ InclusionBreak h z0 toyLeafHash (mixedSystem 1) 1 (ev ⟨1, 2⟩).1 (ev ⟨1, 2⟩).2
      ∧ ∀ (P : Peers) (d : Chain),
          ExecutedViaByAtV35 h z0 toyLeafHash (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
              (mixedSystem 1) P d (mixedFlow 0 1 2) ev ⟨0, 1⟩
            ↔ SourceAllowed P d 0 ∧ SourceAllowed P d 1

/-- **A FORGED ABSENCE PROOF ABOUT A FOREIGN CHAIN PAYS A LEG TWICE AT THE PIN, AND AT v35 ONLY IF
THE REFUNDING CHAIN ALLOWS THE FORGING CHAIN.**  For every node hash and leaf hash, with the pin's
padding constant `z0 = hashLeaf({0,0,0})`, and every `0 < a < b` and `0 < y`, in
`foreignPaddedSystem a b y` (chain `0` holds the padded tree with `a`, chain `1` holds `y`), for
the flow `foreignFlow a y` (legs `⟨0, a⟩` and `⟨1, y⟩`):

* leg `⟨1, y⟩` executes on honest evidence carrying no break;
* the forged padding absence proof `q` for the OTHER leg `⟨0, a⟩`, which was committed, passes the
  pin's timeout check; its located break is on chain `0`'s tree;
* so a pin run appends leg `⟨1, y⟩` on chain `1`, executes it, and authorizes its refund on chain
  `1` with missing leg `⟨0, a⟩`: the leg is executed AND refunded;
* the same v35 run under full allowance exists, with the gate and the authorization logged;
* at v35 the timeout check for `⟨0, a⟩` on `q` passes on chain `1` iff chain `1` allows chain
  `0`.

So the refund filter is what keeps chain `1` from paying on chain `0`'s word when it does not
allow chain `0` (`protocol-docs/interop-gating.md:194-197`).

This is the PIN's tree under v35's filter, not a forgery that exists at v35: `78e14b3bc`, which
`draft/v0.35.0` contains, pads with `IMT_EMPTY_LEAF_HASH`
(`common/libraries/IndexedMerkleTree.sol:44-52`), so `z0 = hashLeaf({0,0,0})` is not v35's
constant.  The padding proof stands in for any forged absence proof about chain `0`; for an
arbitrary hash and padding the statement is `LoggedGateExcludesLoggedRefundOrAllowedBreakAtV35`. -/
def Properties.ForeignForgedRefundNeedsAllowedForgerAtV35 : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b y : UInt256), 0 < a → a < b → 0 < y →
    Wf (foreignPaddedSystem a b y)
      ∧ ∃ (ev : GateEvidence) (q : ImtProof) (r : AuthCall),
          ExecutedViaBy h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (honestFlowHash (foreignFlow a y))
              (foreignPaddedSystem a b y) (foreignFlow a y) ev ⟨1, y⟩
            ∧ ¬ GateBreak h (hl ⟨0, 0, 0⟩) hl (foreignPaddedSystem a b y) (foreignFlow a y) ev
            ∧ LegRefundableBy h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (foreignPaddedSystem a b y)
                (foreignFlow a y) ⟨0, a⟩ 0 q
            ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (foreignPaddedSystem a b y)
                (foreignFlow a y).deadline 0 0 q
            ∧ r = ⟨foreignFlow a y, ⟨1, y⟩, ⟨0, a⟩, 0, q⟩
            ∧ (∃ (Ms : Managers) (log : List CheckedCall),
                RunLog h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (honestFlowHash (foreignFlow a y))
                    (foreignPaddedSystem a b y) emptyManagers Ms log
                  ∧ CheckedCall.execute ⟨foreignFlow a y, ev, ⟨1, y⟩⟩ ∈ log
                  ∧ CheckedCall.authorize r ∈ log
                  ∧ Refunded Ms (obligationOf (foreignFlow a y) ⟨1, y⟩))
            ∧ (∃ (Y : WorldAtV35) (log : List CallAtV35),
                RunAtV35 h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (honestFlowHash (foreignFlow a y))
                    (foreignPaddedSystem a b y) (fun _ => 2) ⟨emptyManagers, allPeersAllowed⟩ Y log
                  ∧ CallAtV35.gate ⟨foreignFlow a y, ev, ⟨1, y⟩⟩ allPeersAllowed ∈ log
                  ∧ CallAtV35.authorize r allPeersAllowed ∈ log
                  ∧ Refunded Y.mgrs (obligationOf (foreignFlow a y) ⟨1, y⟩))
            ∧ ∀ P : Peers,
                LegRefundableByAtV35 h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (foreignPaddedSystem a b y)
                    P 1 (foreignFlow a y) ⟨0, a⟩ 0 q
                  ↔ P 1 0 = true

/-! ## Witnesses -/

/-- **THE SAFETY RESTATEMENTS HAVE SATISFIABLE PREMISES, ON RUNS WITH A DEREGISTRATION.**  For every
node hash, padding constant and leaf hash, in `swapSystem` with full data availability: a v35 run
from fresh managers under full allowance appends both swap legs and the leg `⟨2, 3⟩` of the
different one-leg flow `⟨0, [⟨2, 3⟩], 0⟩`, authorizes that leg's refund on its honest timeout
evidence, executes swap leg `⟨0, 1⟩`, and ends with chain `0` deregistering chain `1`.  The
authorize log is nonempty, no `RefundBreak` is located for either swap leg, and neither is
refunded. -/
def Properties.SafetyAtV35Witness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Y : WorldAtV35) (log : List CallAtV35) (ev : GateEvidence),
      Wf swapSystem ∧ DataAvailable h z0 hl swapSystem (honestAccess h z0 hl swapSystem)
        ∧ ExecutedViaByAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem allPeersAllowed
            (swapDest 1) (mixedFlow 1 1 2) ev ⟨0, 1⟩
        ∧ RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem swapDest
            ⟨emptyManagers, allPeersAllowed⟩ Y log
        ∧ CallAtV35.gate ⟨mixedFlow 1 1 2, ev, ⟨0, 1⟩⟩ allPeersAllowed ∈ log
        ∧ CallAtV35.deregisterPeer 0 1 ∈ log
        ∧ authLogAtV35 log ≠ []
        ∧ (∀ other ∈ (mixedFlow 1 1 2).legs,
            ¬ Refunded Y.mgrs (obligationOf (mixedFlow 1 1 2) other)
              ∧ ¬ RefundBreak h z0 hl lengthFlowHash swapSystem (mixedFlow 1 1 2) ev
                  (obligationOf (mixedFlow 1 1 2) other) (authLogAtV35 log))

/-- **THE SYSTEM RESTATEMENTS HAVE SATISFIABLE PREMISES, ON A RUN WITH A DEREGISTRATION.**  The
pin's `Contracts.AppendPath.Properties.SystemWitness` lifted to v35: a v35 system run from genesis
under full allowance, ending with a deregistration, with both logs nonempty, an executed obligation
that was appended, no `RefundBreak` for it and no refund of it. -/
def Properties.SystemAtV35Witness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (F : Flow) (ev : GateEvidence)
      (leg : FlowLeg) (d : Chain) (Y : SysWorldAtV35) (log : List Obligation) (alog : List AuthCall),
      Wf S ∧ ExecutedViaByAtV35 h z0 hl cv fh S allPeersAllowed d F ev leg
        ∧ SysStepsAtV35 h z0 hl cv fh S ⟨genesisAll, allPeersAllowed⟩ Y log alog
        ∧ Y.peers = allPeersAllowed.deregister 0 1
        ∧ obligationOf F leg ∈ log ∧ alog ≠ []
        ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) alog
        ∧ ¬ Refunded Y.chains.mgrs (obligationOf F leg)

/-- **THE RE-ALLOW, MONOTONICITY AND BLOCKING RESULTS HAVE SATISFIABLE PREMISES.**  For every node
hash, padding constant and leaf hash, on the complete swap:

* chain `1`'s gate call for leg `⟨0, 1⟩` passes under `allPeersAllowed.deregister 0 1`, whose
  entries are all also entries of `allPeersAllowed` (the premises of `GateMonotoneInPeersAtV35`);
  and `allPeersAllowed` allows `1` on `0`, as `DeregisterThenAllowIsIdentity` asks;
* there is a run segment of the kind `BlockedUntilReallowedAtV35` takes, for `c = 2` and
  `s = 3`, on which its two call-level conclusions say something: every bundle's destination
  is chain `2`, chain `2` does not allow chain `3` at the start, and the segment is an
  `authorizeRefund` call on chain `2` (the one-leg flow `strandedFlow`, whose leg `⟨2, 3⟩` is
  its own missing leg), then the gate call for swap leg `⟨0, 1⟩` on chain `2`, then an
  unrelated deregistration.  Both calls are logged under the starting allow-lists, and no
  `allowPeer 2 3` is in the log.

The premises of `ReallowRestoresGateAtV35` and `ReallowRestoresRefundAtV35` are met by the runs
of the two countermodels, which apply them. -/
def Properties.ReallowAtV35Witness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    (∃ ev : GateEvidence,
      ExecutedViaByAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem
        (allPeersAllowed.deregister 0 1) (swapDest 1) (mixedFlow 1 1 2) ev ⟨0, 1⟩)
      ∧ (∀ s, (allPeersAllowed.deregister 0 1) (swapDest 1) s = true
          → allPeersAllowed (swapDest 1) s = true)
      ∧ allPeersAllowed 0 1 = true
      ∧ ∃ (X Y : WorldAtV35) (log : List CallAtV35) (e : ExecCall) (a : AuthCall),
          RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem (fun _ => 2) X Y log
            ∧ X.peers 2 3 = false ∧ CallAtV35.allowPeer 2 3 ∉ log
            ∧ log = [.deregisterPeer 0 1, .gate e X.peers, .authorize a X.peers]
            ∧ e.flow = mixedFlow 1 1 2 ∧ e.leg = ⟨0, 1⟩
            ∧ a.leg = ⟨2, 3⟩ ∧ a.missing = ⟨2, 3⟩

end Contracts.LegSourceFilterAtV35
