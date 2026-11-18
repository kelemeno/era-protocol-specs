import EraSpec.Protocol.InteropAtomicity.Specs.LegSourceFilterAtV35

/-!
# Properties: the v35 receive filter keeps the exclusion results and can strand committed legs

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.LegSourceFilterAtV35`
(`draft/v0.35.0` at `b17415d20`; the Solidity it cites is the same at `d9f678900`).  Proofs are
in `EraSpec.Protocol.InteropAtomicity.Proofs.LegSourceFilterAtV35`.  The tree, the proof checks
and the manager are the pin's models: proofs are checked against the true batch roots, with no
settlement-layer import.  What follows is about the filter on top of them.

## Safety: every exclusion result survives

The filter only rejects.  Every v35 run, admin steps included, is a pin run once the allow-lists
are forgotten (`Properties.RunAtV35ProjectsToRunLog`, `Properties.SysStepsAtV35ProjectsToSysSteps`),
and every pin run is a v35 run under full mutual allowance
(`Properties.RunLogIsRunAtV35UnderFullAllowance`,
`Properties.SysStepsIsSysStepsAtV35UnderFullAllowance`).  So the pin's exclusion results hold over
v35 runs with the same located breaks and no new premise: `ExecutedExcludesAnyRefundOrBreakAtV35`,
`ExecutedObligationNeverRefundedOrBreakAtV35`, `OneExecutionFreezesTheFlowOrBreakAtV35`,
`SystemOncePerLegAtV35`, `SystemExecutedObligationNeverRefundedOrBreakAtV35`, and the evidence
half of none-or-all (`NoneOrAllOrBreakAtV35`, `ExecutedImpliesRealFlowFinalizableOrLoggedClashAtV35`).

The filter adds one refinement.  A logged execution and a logged refund of one flow id need a
broken proof about the refund's missing leg, accepted by a chain that allowed that leg's source
when it accepted the proof, or a flow-id clash between the two logged flows
(`Properties.LoggedGateExcludesLoggedRefundOrAllowedBreakAtV35`).  Upstream gives the same reason
for filtering refunds too (`protocol-docs/interop-gating.md:200-203`).  Two of the pin's
forgeries, replayed under the filter: the forged-sibling execution passes the v35 gate exactly on
destinations that allow both of its leg sources, one of them the chain whose tree the forgery is
about (`Properties.ForgedSiblingExecutionNeedsAllowedForgerAtV35`); and a forged absence proof
about chain `0`, which at the pin authorizes the refund of an executed leg, passes the v35
timeout check on the refunding chain exactly when that chain allows chain `0`
(`Properties.ForeignForgedRefundNeedsAllowedForgerAtV35`).

## Liveness: a committed leg can be stranded, exactly when the filter blocks it

`Properties.SwapStrandedByDeregistrationAtV35` and
`Properties.IncompleteSwapRefundStrandedByDeregistrationAtV35` refute "a committed leg is always
finalizable or refundable" with one deregistration after commit.  Upstream does not claim it:
this is its documented limitation "K1: stuck flows" (`protocol-docs/interop-gating.md:256-266`).
The two cases are K1's two cases:

* **complete flow** (both legs of a swap committed in time): the destination of one leg
  deregisters that leg's source chain.  That leg then passes the gate there on no evidence, for
  no presented flow, and a flow that declares its bundle under another source chain passes only
  on evidence that carries a located break, while its sibling has already executed; and every
  `authorizeRefund` call that presents the flow's id and passes carries a located break.  The
  swap has completed in one direction only.  The pin calls the flow finalizable
  (`FlowFinalizableBy`).
* **incomplete flow** (one leg never committed): the committed leg's own chain deregisters the
  missing leg's source.  No refund of the committed leg passes there without a forged proof,
  though the honest call passes every check the pin runs, and no gate passes anywhere without a
  forged proof.

`Properties.StrandedIffAtV35` characterises stranding exactly, in this model, for every flow that
passes `_checkFlowId`, has nonzero commit values, and whose missing legs' chains settle past the
deadline.  A leg is stranded (up to located breaks, `StrandedOrBreakAtV35`) iff

* every leg was committed on time and the leg's destination does not allow some leg's source; or
* some leg was not, and the leg's own chain allows the source of no leg that was not.

## Re-allowing restores progress

Deregistering and re-allowing a peer restores the allow-lists exactly
(`Properties.DeregisterThenAllowIsIdentity`).  Both checks are monotone in the allow-lists
(`GateMonotoneInPeersAtV35`, `RefundMonotoneInPeersAtV35`).  In every reachable state, one
`allowPeer` step lets through a gate call whose evidence passes the pin's gate and whose
destination allows every leg source but the re-allowed one (`ReallowRestoresGateAtV35`), and an
`authorizeRefund` call that passes the pin's checks for a leg that is still `Committed`
(`ReallowRestoresRefundAtV35`).  Conversely, until the pair is re-allowed, no gate call on that
chain accepts a flow with a leg from that source, and no `authorizeRefund` call on it has a
missing leg from that source (`BlockedUntilReallowedAtV35`).

Re-allowing is a step of the model, enabled at every moment.  On the contracts it is the chain
admin's `ChainRegistrationSender.allowInteropPeer` and a service transaction, which the model
does not check (`Specs`, "What is not modelled"); so "one step restores progress" is a statement
about the allow-list, not about who can or will take the step.

## Witnesses

Each result with premises has a witness that meets them: `SafetyAtV35Witness` (the run-level
safety results, on a run that contains a deregistration), `SystemAtV35Witness` (the system
results), `StrandedIffAtV35Witness` (both cases of the characterisation, and neither under full
allowance), `CompleteFlowGateOpenIffSourcesAllowedAtV35Witness` (both sides of the iff),
`RefundEvidenceCompleteAtV35Witness` (its filter premise is needed), `MonotoneInPeersAtV35Witness`
(strictly smaller allow-lists), `ReallowRestoresGateAtV35Witness` (a gate call the filter
blocks), and `ReallowAtV35Witness` (the identity and blocking results).
`IncompleteSwapRefundStrandedByDeregistrationAtV35` meets the premises of
`ReallowRestoresRefundAtV35`, `ForeignForgedRefundNeedsAllowedForgerAtV35` those of
`LoggedGateExcludesLoggedRefundOrAllowedBreakAtV35` and `RunLogIsRunAtV35UnderFullAllowance`, and
the pin's `Contracts.AppendPath.Properties.SystemWitness` that of
`SysStepsIsSysStepsAtV35UnderFullAllowance`.
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
`RunLogAuthCallsReachLog`, over `Contracts.Refund.ReachLog`) applies to v35 runs through this
projection. -/
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

/-- **A LOGGED EXECUTION AND A LOGGED REFUND OF ONE FLOW ID NEED A BROKEN PROOF ABOUT AN ALLOWED
CHAIN, OR A FLOW-ID CLASH.**  In a v35 run, take a gate call `e` (checked under `P` on its bundle's
destination) and an `authorizeRefund` call `a` (checked under `Q` on `a.leg.chain`) claiming one
flow id.  Then:

* the inclusion proof `e` submitted for `a`'s missing leg carries a break, AND `e`'s destination
  allowed that leg's source (or is that chain) when it accepted the proof; or
* `a`'s absence proof carries a break, AND `a`'s chain allowed the missing leg's source (or is
  that chain) when it accepted the proof; or
* the two flows clash on the flow-id hash.

The pin's `LoggedExecutionExcludesLoggedRefundOrBreak` locates the same breaks.  What v35 adds is
the allowance conjunct: if neither accepting chain allows the missing leg's source chain, and
that chain is neither of them, the two calls' flows clash.  Upstream gives this as the reason the
filter covers refunds (`protocol-docs/interop-gating.md:200-203`).  The breaks here are IMT-level
forgeries against true batch roots; a broken prover, which would forge a batch root, is not
modelled. -/
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
evidence for every leg, or `e`'s evidence carries a break on the first stranded leg of `e`'s
flow, or the two flows clash.  Evidence only: whether each leg's destination admits it is
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
committed in batch 0, so the flow is complete), with full data availability, and with a flow hash
that is honest about the swap `mixedFlow 1 1 2`:

* the pin's liveness reading holds: every leg of the swap has presentable accepted evidence
  (`FlowFinalizableBy`);
* there is a v35 run from fresh managers under full mutual allowance in which both legs are
  appended, leg `⟨0, 1⟩` passes the gate on its destination (chain `1`), and then chain `0`
  deregisters chain `1`;
* at the end both legs are still `Committed`.  Leg `⟨1, 2⟩` passes the gate on its destination
  `swapDest 2` (chain `0`) for no presented flow and no evidence, with no hash premise.  A flow
  that declares bundle `2` with another source chain passes there only on evidence that carries
  a located break (the contract's `executingIsLeg` check compares bundle hashes only).  No leg of
  the swap passes the timeout check on any chain under any allow-lists, unless the absence proof
  carries a located break; and every `authorizeRefund` call that presents the swap's flow id and
  passes the v35 checks, on any chain under any allow-lists, carries a located break on its
  absence proof.  (Funds are not part of this model.  Read with a burn-and-mint bridge on top,
  the burn of leg `⟨1, 2⟩` is neither delivered nor refunded without a forged proof for as long
  as chain `0` keeps chain `1` out, which `Properties.BlockedUntilReallowedAtV35` covers for the
  gate.);
* one `allowPeer 0 1` step lets leg `⟨1, 2⟩` through the gate on chain `0`. -/
def Properties.SwapStrandedByDeregistrationAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    Wf swapSystem
      ∧ DataAvailable h z0 hl swapSystem (honestAccess h z0 hl swapSystem)
      ∧ FlowFinalizableBy h z0 hl (fun _ b => b) swapSystem (honestAccess h z0 hl swapSystem)
          (mixedFlow 1 1 2)
      ∧ ∃ (Y : WorldAtV35) (log : List CallAtV35) (e : ExecCall),
          RunAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 1 1 2)) swapSystem swapDest
              ⟨emptyManagers, allPeersAllowed⟩ Y log
            ∧ log = [.deregisterPeer 0 1, .gate e allPeersAllowed]
            ∧ e.flow = mixedFlow 1 1 2 ∧ e.leg = ⟨0, 1⟩
            ∧ Y.peers = allPeersAllowed.deregister 0 1
            ∧ stateOf Y.mgrs (obligationOf (mixedFlow 1 1 2) ⟨0, 1⟩) = .Committed
            ∧ stateOf Y.mgrs (obligationOf (mixedFlow 1 1 2) ⟨1, 2⟩) = .Committed
            ∧ (∀ (F : Flow) (ev : GateEvidence), ¬ ExecutedViaByAtV35 h z0 hl (fun _ b => b)
                (honestFlowHash (mixedFlow 1 1 2)) swapSystem Y.peers (swapDest 2) F ev ⟨1, 2⟩)
            ∧ (∀ (F : Flow) (ev : GateEvidence) (l : FlowLeg), l.bundleHash = 2 →
                ¬ ExecutedViaByAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 1 1 2))
                    swapSystem Y.peers (swapDest 2) F ev l
                  ∨ GateBreak h z0 hl swapSystem F ev)
            ∧ (∀ (Q : Peers) (c : Chain), ∀ m ∈ (mixedFlow 1 1 2).legs, ∀ (N : ℕ) (q : ImtProof),
                ¬ LegRefundableByAtV35 h z0 hl (fun _ b => b) swapSystem Q c (mixedFlow 1 1 2) m N q
                  ∨ AbsenceBreak h z0 hl swapSystem (mixedFlow 1 1 2).deadline m.chain N q)
            ∧ (∀ (Q : Peers) (a : AuthCall), a.flow.flowId = (mixedFlow 1 1 2).flowId →
                AuthorizeCallPassesAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 1 1 2))
                    swapSystem Q a →
                  AbsenceBreak h z0 hl swapSystem a.flow.deadline a.missing.chain a.batch a.proof)
            ∧ ∃ e' : ExecCall, e'.flow = mixedFlow 1 1 2 ∧ e'.leg = ⟨1, 2⟩
                ∧ RunAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 1 1 2)) swapSystem
                    swapDest ⟨emptyManagers, allPeersAllowed⟩ ⟨Y.mgrs, Y.peers.allow 0 1⟩
                    (.gate e' (Y.peers.allow 0 1) :: .allowPeer 0 1 :: log)

/-- **DEREGISTERING THE MISSING LEG'S SOURCE STRANDS THE COMMITTED LEG OF AN INCOMPLETE SWAP.**
For every node hash, padding constant and leaf hash, in `mixedSystem 1` (leg `⟨0, 1⟩` committed in
batch 0, leg `⟨1, 2⟩` never committed), with a flow hash that is honest about the flow
`mixedFlow 0 1 2`, there is a v35 run from fresh managers under full mutual allowance that
appends leg `⟨0, 1⟩` on chain `0` and then has chain `0` deregister chain `1`.  At its end:

* leg `⟨0, 1⟩` is `Committed`, and leg `⟨1, 2⟩` was not committed on time: the flow timed out;
* the pin would refund it: an `authorizeRefund` call `a` for leg `⟨0, 1⟩` on the honest absence
  proof of the missing leg `⟨1, 2⟩` passes every check the pin runs, its proof carries no break,
  and the leg is `Committed`;
* at v35 no timeout evidence for any leg of the flow passes on chain `0`, except a forged absence
  proof for the committed leg `⟨0, 1⟩` itself, which carries a located break;
* no leg of the flow passes the gate on any chain under any allow-lists, unless the proof submitted
  for the missing leg `⟨1, 2⟩` carries a located break;
* every flow that passes `_checkFlowId` with the flow's id is the flow itself, so the two clauses
  above are about every call that presents flow id `0`;
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
            ∧ (∀ F : Flow, FlowIdChecked (honestFlowHash (mixedFlow 0 1 2)) F →
                F.flowId = (mixedFlow 0 1 2).flowId → F = mixedFlow 0 1 2)
            ∧ RunAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2)) (mixedSystem 1)
                swapDest ⟨emptyManagers, allPeersAllowed⟩
                ⟨setAt Y.mgrs 0 ((Y.mgrs 0).set 0 1 .Revertable), Y.peers.allow 0 1⟩
                (.authorize a (Y.peers.allow 0 1) :: .allowPeer 0 1 :: log)

/-- **A MISSING LEG HAS HONEST TIMEOUT EVIDENCE WHEREVER ITS SOURCE IS ALLOWED.**  If a leg of a
flow has a nonzero commit value, was not committed on time, and its chain settled a batch after the
deadline, then on every chain `c` that allows its source there is timeout evidence `(N, q)` that
passes the model's v35 timeout check (`LegRefundableByAtV35`: the filter and the pin's IMT-level
check; the imported settlement-layer root that `verifyTimeoutAbsence` also needs is not modelled)
and carries no break: the honest low-leaf proof against the BEGIN root of the first late batch.
No hash premise.  The completeness direction of `Properties.StrandedIffAtV35`. -/
def Properties.RefundEvidenceCompleteAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (F : Flow) (m : FlowLeg), legValue cv F m ≠ 0 → ¬ CommittedOnTime cv S F m →
    SettledAfterDeadline S F m → ∀ (P : Peers) (c : Chain), SourceAllowed P c m.chain →
      ∃ (N : ℕ) (q : ImtProof), LegRefundableByAtV35 h z0 hl cv S P c F m N q
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline m.chain N q

/-- **A COMPLETE FLOW EXECUTES ON A CHAIN EXACTLY WHEN THAT CHAIN ALLOWS EVERY LEG'S SOURCE.**  For a
checked flow every leg of which was committed on time, with data availability: presentable
evidence passes the v35 gate for a leg on chain `d` (`GateOpenAtV35`, the IMT half of the gate,
without the destination's settlement-layer import) iff `d` allows every leg's source.  No hash
premise in either direction. -/
def Properties.CompleteFlowGateOpenIffSourcesAllowedAtV35 : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (F : Flow), FlowIdChecked fh F → (∀ l ∈ F.legs, CommittedOnTime cv S F l) →
    ∀ (leg : FlowLeg), leg ∈ F.legs → ∀ (P : Peers) (d : Chain),
      GateOpenAtV35 h z0 hl cv fh S A P d F leg ↔ ∀ l ∈ F.legs, SourceAllowed P d l.chain

/-- **EXACTLY WHICH LEGS ARE STRANDED, IN THIS MODEL.**  Take a well-formed system and a flow that
passes `_checkFlowId` and has nonzero commit values, every leg of which that missed the deadline
comes from a chain that settled past it.  For a leg of that flow, a chain `d` (read: the leg's
destination) and allow-lists `P`, the leg is stranded up to located breaks
(`StrandedOrBreakAtV35`, about the flow's own preimage and the model's IMT-level checks) iff one of:

* **complete flow**: every leg was committed on time, and `d` does not allow some leg's source;
* **incomplete flow**: some leg was not committed on time, and the leg's own chain `leg.chain`
  allows the source of no leg that was not.

So in a complete flow the stranded legs are those whose destination does not allow some leg's
source, and in an incomplete flow those whose own chain allows no missing leg's source (a missing
leg's own chain allows it, so a missing leg is never stranded). -/
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

/-- **THE COMPLETE-FLOW CHARACTERISATION HAS SATISFIABLE PREMISES, AND BOTH SIDES OCCUR.**  For
every node hash, padding constant and leaf hash, on the complete swap with honest access, every
premise of `Properties.CompleteFlowGateOpenIffSourcesAllowedAtV35` holds for leg `⟨1, 2⟩`.  Under
full allowance its destination (chain `0`) can be passed on presentable evidence; after chain `0`
drops chain `1` it cannot. -/
def Properties.CompleteFlowGateOpenIffSourcesAllowedAtV35Witness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    Wf swapSystem ∧ DataAvailable h z0 hl swapSystem (honestAccess h z0 hl swapSystem)
      ∧ FlowIdChecked lengthFlowHash (mixedFlow 1 1 2)
      ∧ (∀ l ∈ (mixedFlow 1 1 2).legs, CommittedOnTime (fun _ b => b) swapSystem (mixedFlow 1 1 2) l)
      ∧ (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 1 1 2).legs
      ∧ GateOpenAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem
          (honestAccess h z0 hl swapSystem) allPeersAllowed (swapDest 2) (mixedFlow 1 1 2) ⟨1, 2⟩
      ∧ ¬ GateOpenAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem
          (honestAccess h z0 hl swapSystem) (allPeersAllowed.deregister 0 1) (swapDest 2)
          (mixedFlow 1 1 2) ⟨1, 2⟩

/-- **THE REFUND-EVIDENCE RESULT HAS SATISFIABLE PREMISES, AND ITS FILTER PREMISE IS NEEDED.**  For
every node hash, padding constant and leaf hash, in the incomplete swap: the missing leg `⟨1, 2⟩`
has a nonzero commit value, was not committed on time, and its chain settled a batch after the
deadline; chain `0`, which is not the leg's own chain, allows chain `1` under full allowance.
After chain `0` drops chain `1`, no timeout evidence for that leg passes on chain `0`. -/
def Properties.RefundEvidenceCompleteAtV35Witness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    Wf (mixedSystem 1)
      ∧ legValue (fun _ b => b) (mixedFlow 0 1 2) ⟨1, 2⟩ ≠ 0
      ∧ ¬ CommittedOnTime (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨1, 2⟩
      ∧ SettledAfterDeadline (mixedSystem 1) (mixedFlow 0 1 2) ⟨1, 2⟩
      ∧ SourceAllowed allPeersAllowed 0 1
      ∧ ∀ (N : ℕ) (q : ImtProof),
          ¬ LegRefundableByAtV35 h z0 hl (fun _ b => b) (mixedSystem 1)
            (allPeersAllowed.deregister 0 1) 0 (mixedFlow 0 1 2) ⟨1, 2⟩ N q

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

/-- **THE PIN'S FORGED-SIBLING EXECUTION PASSES AT v35 EXACTLY WHERE BOTH LEG SOURCES ARE
ALLOWED.**  For every node hash and padding constant, with the toy leaf hash: the evidence `ev` of
`Contracts.FlowBinding.Properties.ForgedSiblingProofLandsInPinnedBreak` executes leg `⟨0, 1⟩` of
`mixedFlow 0 1 2` through the pin's gate.  Its proof for leg `⟨0, 1⟩` is honest and its proof for
the never-committed leg `⟨1, 2⟩` is forged.  At v35 it passes on chain `d` under allow-lists `P`
iff `d` allows chains `0` and `1`, so a destination that does not allow chain `1`, the chain whose
tree the forged proof is about, rejects it.  The forgery is a collision of `toyLeafHash`; the
statement fixes that leaf hash. -/
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

/-- **A FORGED ABSENCE PROOF ABOUT A FOREIGN CHAIN REFUNDS AN EXECUTED LEG AT THE PIN, AND AT v35
PASSES ONLY IF THE REFUNDING CHAIN ALLOWS THAT CHAIN.**  For every node hash and leaf hash, with the
pin's padding constant `z0 = hashLeaf({0,0,0})`, and every `0 < a < b` and `0 < y`, in
`foreignPaddedSystem a b y` (chain `0` holds the padded tree with `a`, chain `1` holds `y`), for
the flow `foreignFlow a y` (legs `⟨0, a⟩` and `⟨1, y⟩`):

* leg `⟨0, a⟩` was committed on time;
* leg `⟨1, y⟩` executes on honest evidence carrying no break;
* the forged padding absence proof `q` for the OTHER leg `⟨0, a⟩` passes the pin's timeout check;
  its located break is on chain `0`'s tree;
* so a pin run appends leg `⟨1, y⟩` on chain `1`, executes it, and authorizes its refund on chain
  `1` with missing leg `⟨0, a⟩`: the leg is executed AND marked for refund;
* the same v35 run under full allowance exists, with the gate and the authorization logged;
* at v35 the timeout check for `⟨0, a⟩` on `q` passes on chain `1` iff chain `1` allows chain
  `0`.

So, on this tree, the filter is what keeps chain `1` from authorizing the refund on a forged
absence proof about chain `0` when it does not allow chain `0`
(`protocol-docs/interop-gating.md:200-203`).

This is the PIN's tree under v35's filter, not a forgery that exists at v35: `78e14b3bc`, which
`draft/v0.35.0` contains, pads with `IMT_EMPTY_LEAF_HASH`
(`common/libraries/IndexedMerkleTree.sol:44-52`), so `z0 = hashLeaf({0,0,0})` is not v35's
constant.  For an arbitrary hash and padding the statement is
`Properties.LoggedGateExcludesLoggedRefundOrAllowedBreakAtV35`. -/
def Properties.ForeignForgedRefundNeedsAllowedForgerAtV35 : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b y : UInt256), 0 < a → a < b → 0 < y →
    Wf (foreignPaddedSystem a b y)
      ∧ CommittedOnTime (fun _ k => k) (foreignPaddedSystem a b y) (foreignFlow a y) ⟨0, a⟩
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

/-- **THE MONOTONICITY RESULTS HAVE SATISFIABLE PREMISES, WITH STRICTLY SMALLER ALLOW-LISTS.**  For
every node hash, padding constant and leaf hash:

* gate: chain `1` drops chain `3`.  Every entry chain `1` has is an entry of `allPeersAllowed`,
  which also has `3`; the gate call for leg `⟨0, 1⟩` of the complete swap still passes on chain
  `1` under the smaller allow-lists (the premises of `Properties.GateMonotoneInPeersAtV35`);
* refund: chain `0` drops chain `3`, likewise; the timeout check for the missing leg `⟨1, 2⟩` of
  the incomplete swap still passes on chain `0` under the smaller allow-lists (the premises of
  `Properties.RefundMonotoneInPeersAtV35`). -/
def Properties.MonotoneInPeersAtV35Witness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    (∀ s, (allPeersAllowed.deregister 1 3) 1 s = true → allPeersAllowed 1 s = true)
      ∧ (allPeersAllowed.deregister 1 3) 1 3 = false
      ∧ (∃ ev : GateEvidence,
          ExecutedViaByAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem
            (allPeersAllowed.deregister 1 3) 1 (mixedFlow 1 1 2) ev ⟨0, 1⟩)
      ∧ (∀ s, (allPeersAllowed.deregister 0 3) 0 s = true → allPeersAllowed 0 s = true)
      ∧ (allPeersAllowed.deregister 0 3) 0 3 = false
      ∧ ∃ (N : ℕ) (q : ImtProof),
          LegRefundableByAtV35 h z0 hl (fun _ b => b) (mixedSystem 1)
            (allPeersAllowed.deregister 0 3) 0 (mixedFlow 0 1 2) ⟨1, 2⟩ N q

/-- **THE GATE RE-ALLOW RESULT HAS SATISFIABLE PREMISES, ON A CALL THE FILTER BLOCKS.**  For every
node hash, padding constant and leaf hash, at the end of a complete-swap run in which chain `0`
has dropped chain `1` (the run of `Properties.SwapStrandedByDeregistrationAtV35`): the gate call
`e` for leg `⟨1, 2⟩` on honest evidence passes the pin's gate, every leg source other than chain
`1` is allowed on the bundle's destination, and `e` fails the v35 gate there.  These are the
premises of `Properties.ReallowRestoresGateAtV35` with `s = 1`, met by a call that the
re-allow is needed for. -/
def Properties.ReallowRestoresGateAtV35Witness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Y : WorldAtV35) (log : List CallAtV35) (e : ExecCall),
      RunAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 1 1 2)) swapSystem swapDest
          ⟨emptyManagers, allPeersAllowed⟩ Y log
        ∧ Y.peers = allPeersAllowed.deregister 0 1
        ∧ e.flow = mixedFlow 1 1 2 ∧ e.leg = ⟨1, 2⟩
        ∧ e.Verified h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 1 1 2)) swapSystem
        ∧ (∀ l ∈ e.flow.legs, l.chain = 1 ∨ SourceAllowed Y.peers (swapDest e.leg.bundleHash) l.chain)
        ∧ ¬ GateCallPassesAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 1 1 2)) swapSystem
            swapDest Y.peers e

/-- **THE IDENTITY AND BLOCKING RESULTS HAVE SATISFIABLE PREMISES.**  For every node hash, padding
constant and leaf hash:

* the allow-lists `allPeersAllowed.deregister 2 3`, which are not constant, allow `1` on `0`,
  as `Properties.DeregisterThenAllowIsIdentity` asks;
* there is a run segment of the kind `Properties.BlockedUntilReallowedAtV35` takes, for `c = 2`
  and `s = 3`, on which both of its call-level conclusions have a call to apply to: every
  bundle's destination is chain `2`, chain `2` does not allow chain `3` at the start, and the
  segment is an `authorizeRefund` call on chain `2` (the one-leg flow `strandedFlow`, whose leg
  `⟨2, 3⟩` is its own missing leg), then the gate call for swap leg `⟨0, 1⟩` on chain `2`, then
  an unrelated deregistration.  Both calls are logged under the starting allow-lists, and no
  `allowPeer 2 3` is in the log. -/
def Properties.ReallowAtV35Witness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    (allPeersAllowed.deregister 2 3) 0 1 = true
      ∧ ∃ (X Y : WorldAtV35) (log : List CallAtV35) (e : ExecCall) (a : AuthCall),
          RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem (fun _ => 2) X Y log
            ∧ X.peers 2 3 = false ∧ CallAtV35.allowPeer 2 3 ∉ log
            ∧ log = [.deregisterPeer 0 1, .gate e X.peers, .authorize a X.peers]
            ∧ e.flow = mixedFlow 1 1 2 ∧ e.leg = ⟨0, 1⟩
            ∧ a.leg = ⟨2, 3⟩ ∧ a.missing = ⟨2, 3⟩

end Contracts.LegSourceFilterAtV35
