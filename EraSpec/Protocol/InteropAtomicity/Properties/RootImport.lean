import EraSpec.Protocol.InteropAtomicity.Specs.RootImport
import EraSpec.Protocol.InteropAtomicity.Specs.SourceHeight
import EraSpec.Protocol.InteropAtomicity.Specs.FlowBinding

/-!
# Properties: finalizability on the destination that has to finalize

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.RootImport`.  Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.RootImport`.

## What this corrects

`Contracts.Atomicity.Properties.MemberIsFinalizable`, `ExecutedImpliesAllFinalizable`,
`NoneOrAll`, and their `…OrBreak`, `…Pinned` and `…FromRuns` forms conclude
`LegFinalizableBy` / `FlowFinalizableBy`: an on-time batch, and a presentable IMT proof
that the verifier accepts against that batch's true END root.  That is the source-side
half of what a destination needs.  The destination must also authenticate that root,
through a multi-hop settlement proof that ends at a settlement-layer root the destination
has itself imported (`Specs/RootImport.lean`, "What a destination checks").  Source data
availability does not supply that import.

So those results do not say "every leg's destination can run `requireFlowFinalized` and
pass".  Take every source leg committed on time, with all IMT data available.  A
destination that has not imported a covering root still cannot pass, while another
destination that has imported one executes (`Properties.WithoutImportFlowSitsHalfExecuted`).

The safety results (`GateRequiresEveryLeg`, `FinalitySignalMeansMembership`,
`ExecutedExcludesAnyRefund`, the flow-id results) are unaffected.  Authenticating the root
only removes accepted proofs, and an execution on a destination is an `ExecutedViaBy`
(`Properties.ExecutedAtProjects`).

## The corrected property, in one line

**If any leg of a flow executes, on any destination, then every leg can be finalized on
every destination that is ready for the flow** — the destination's `L1_CHAIN_ID` is the
flow's settlement layer, and it has imported roots covering every batch that settled by the
deadline — provided the source chains' data and the settlement layer's data are available.
Otherwise a break is located on a submitted proof, as in
`Contracts.Atomicity.Properties.NoneOrAllOrBreak`.

## How it is stated

* `Properties.FinalizableAtImpliesBy`: finalizability on a destination implies the old
  predicate, which is its IMT half.  `Properties.ReadyFinalizableAtIffBy`: on a ready
  destination, with settlement data available, the two coincide.  So a result that
  concludes `FlowFinalizableBy` speaks about ready destinations, and about no others.
* The restated results are `MemberIsFinalizableAt`, `ExecutedImpliesAllFinalizableAtOrBreak`,
  `ExecutedAtImpliesAllFinalizableAtOrBreak` (an execution on one destination, finalizability
  on another), `NoneOrAllAtOrBreak`, `NoneOrAllAtOrBreakPinned`,
  `ExecutedImpliesFinalityPersistsAtOrBreak`, `NoneOrAllAtOrBreakPinnedFromRuns` and
  `ExecutedImpliesRealFlowFinalizableAtOrLoggedClash`.  None takes a hash premise.  The forms
  that take `HashAssumptions` are vacuous (`HashAssumptionsUnsatisfiable`) and are not
  restated.
* The import premise can be discharged.  One imported root created at or after the deadline
  is enough, given the settlement layer's `Aggregates`
  (`ImportAvailableOfPostDeadlineImport`).  More imports never hurt
  (`FinalizableAtPersistsAsImportsGrow`).

## Countermodels and witnesses

| Result | What it shows |
|---|---|
| `WithoutImportFlowSitsHalfExecuted` | import availability is necessary: `dA` executes a leg, `dB` can execute none, no leg is refundable, and `FlowFinalizableBy` holds |
| `ImportAloneRestoresFinalizability` | in that world, the one root import is all `dB` lacks |
| `WithoutSettlementDataLegIsStuck` | settlement-proof availability is necessary |
| `ExecutedAtOrBreakSatisfiable` | every premise of the cross-destination result at once, with no break and the conclusion true |
| `NoneOrAllAtOrBreakPinnedStrandedNotTautology` | on a ready destination, the pinned break is evaluated on a stranded leg and is false |
| `PinnedGateBreakAtFires` | on that world, a destination execution on a forged sibling proof lands in the pinned break |
| `NoneOrAllAtOrBreakPinnedFromRunsStranded`, `ExecutedImpliesRealFlowFinalizableAtOrLoggedClashWitness` | the premises of the runs and logged-run forms, together |
-/

namespace Contracts.RootImport

open IMTAbstract MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity

/-! ## The destination gate and the old predicates -/

/-- **AN EXECUTION ON A DESTINATION IS AN EXECUTION OF THE MODEL'S GATE.**  A destination's
gate checks everything `Contracts.Atomicity.ExecutedViaBy` checks, on the IMT half of its
evidence.  So every safety result stated over `ExecutedViaBy` or `ExecutedVia` applies to
executions on a destination. -/
def Properties.ExecutedAtProjects : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (W : World)
    (S : System) (d : Dest) (sl : Chain) (F : Flow) (ev : GateEvidenceAt) (leg : FlowLeg),
    ExecutedAtBy h z0 hl cv fh W S d sl F ev leg →
      ExecutedViaBy h z0 hl cv fh S F (imtEvidence ev) leg

/-- **WHAT A DESTINATION ACCEPTS.**  An accepted proof is multi-hop, resolves on the flow's
settlement layer, and ends at a root the destination has imported that aggregates the batch.
Its IMT half is accepted as in `Contracts.Atomicity.Accepts`. -/
def Properties.AcceptedAtShape : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (W : World) (S : System) (d : Dest)
    (sl c : Chain) (n : ℕ) (v : UInt256) (p : ImtProof) (sp : SettlementProof),
    AcceptsAt h z0 hl W S d sl c n v p sp →
      sp.finalProofNode = false ∧ sp.slChainId = sl ∧ W.imported d sl sp.slBlock
        ∧ RootImported W d sl c n ∧ Accepts h z0 hl S c n v p

/-- **`FlowFinalizableBy` IS THE IMT HALF.**  A flow that is finalizable on some destination
is finalizable in `Contracts.Atomicity`'s sense. -/
def Properties.FinalizableAtImpliesBy : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (W : World) (S : System)
    (A : Access) (SA : SettlementAccess) (d : Dest) (sl : Chain) (F : Flow),
    FlowFinalizableAt h z0 hl cv W S A SA d sl F → FlowFinalizableBy h z0 hl cv S A F

/-- **ON A READY DESTINATION THE TWO COINCIDE.**  Take settlement data available, and a
destination whose `L1_CHAIN_ID` is the flow's settlement layer and that has imported roots
covering every batch settled by the deadline.  The flow is finalizable on that destination
exactly when it is finalizable in `Contracts.Atomicity`'s sense. -/
def Properties.ReadyFinalizableAtIffBy : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (W : World) (S : System)
    (A : Access) (SA : SettlementAccess), SettlementDataAvailable W SA →
    ∀ (d : Dest) (sl : Chain) (F : Flow), W.l1 d = sl → ImportAvailable W S d sl F.deadline →
      (FlowFinalizableAt h z0 hl cv W S A SA d sl F ↔ FlowFinalizableBy h z0 hl cv S A F)

/-! ## Discharging the new premises -/

/-- **HONEST SETTLEMENT ACCESS IS SETTLEMENT DATA AVAILABILITY.** -/
def Properties.HonestSettlementAccessAvailable : Prop :=
  ∀ W : World, SettlementDataAvailable W (honestSettlementAccess W)

/-- **ONE POST-DEADLINE IMPORT IS ENOUGH, GIVEN `Aggregates`.**  Suppose destination `d` has
imported a root of settlement layer `sl` that was created at or after `D`, and the settlement
layer aggregates into that root every batch that had settled by its creation
(`Contracts.Timeout.Aggregates`, `PROTO-AGGREGATES`).  Then `d` has import availability for
deadline `D`. -/
def Properties.ImportAvailableOfPostDeadlineImport : Prop :=
  ∀ (W : World) (S : System) (d : Dest) (sl : Chain) (k D : ℕ),
    W.imported d sl k → D ≤ (W.slRoot sl k).created →
    Contracts.Timeout.Aggregates S (W.slRoot sl k) → ImportAvailable W S d sl D

/-- **MORE IMPORTS NEVER HURT.**  Along a later snapshot in which imports have only
accumulated, import availability, settlement data availability and finalizability on a
destination are all kept.  This is the destination side of "finalizability does not
decay". -/
def Properties.FinalizableAtPersistsAsImportsGrow : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (W W' : World) (S : System)
    (A : Access) (SA : SettlementAccess) (d : Dest) (sl : Chain) (F : Flow),
    ImportsGrow W W' →
      (ImportAvailable W S d sl F.deadline → ImportAvailable W' S d sl F.deadline)
        ∧ (SettlementDataAvailable W SA → SettlementDataAvailable W' SA)
        ∧ (FlowFinalizableAt h z0 hl cv W S A SA d sl F →
            FlowFinalizableAt h z0 hl cv W' S A SA d sl F)

/-! ## The corrected finalizability results -/

/-- **MEMBERSHIP, DATA AVAILABILITY AND A COVERING IMPORT GIVE A PROOF THE DESTINATION
ACCEPTS.**  The corrected `Contracts.Atomicity.Properties.MemberIsFinalizable`.  Take a
committed value at an on-time batch.  Its honest `merklePath` proof is presentable (IMT data
availability).  A destination holding an imported root that aggregates the batch gets the
honest multi-hop settlement proof (settlement data availability).  And it accepts both. -/
def Properties.MemberIsFinalizableAt : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (W : World) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (SA : SettlementAccess), SettlementDataAvailable W SA →
    ∀ (d : Dest) (sl : Chain) (F : Flow) (leg : FlowLeg) (n : ℕ),
      S.time leg.chain n ≤ F.deadline → RootImported W d sl leg.chain n →
      legValue cv F leg ∈ keys (toAbs (S.tree leg.chain n)) →
      LegFinalizableAt h z0 hl cv W S A SA d sl F leg

/-- **PARTIAL ATOMICITY ON A DESTINATION WITH IMPORTS, OR A LOCATED BREAK, PER LEG.**  The
corrected `Contracts.Atomicity.Properties.ExecutedImpliesAllFinalizableOrBreak`.  Suppose a
leg executed on the evidence `ev`, and destination `d` has import availability for the
flow's deadline.  Then every leg `other` of the flow is finalizable on `d`, or the inclusion
proof `ev other` submitted for that very leg carries a `TreeRootBreak`. -/
def Properties.ExecutedImpliesAllFinalizableAtOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (W : World)
    (S : System), Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (SA : SettlementAccess), SettlementDataAvailable W SA →
    ∀ (d : Dest) (sl : Chain) (F : Flow), ImportAvailable W S d sl F.deadline →
    ∀ (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ other ∈ F.legs,
      LegFinalizableAt h z0 hl cv W S A SA d sl F other
        ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2

/-- **EXECUTED ON ONE DESTINATION, FINALIZABLE ON EVERY READY ONE, OR A LOCATED BREAK.**
Suppose a leg executed on destination `dA`, through `dA`'s own gate, on the evidence `ev`.
Let `dB` be any destination whose `L1_CHAIN_ID` is the flow's settlement layer and that has
import availability for the deadline.  Then `dB` can run `requireFlowFinalized` on
presentable proofs and pass, or the evidence `dA` accepted carries a located break on one of
the flow's legs.  `Properties.WithoutImportFlowSitsHalfExecuted` shows the import premise on
`dB` cannot be dropped. -/
def Properties.ExecutedAtImpliesAllFinalizableAtOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (W : World)
    (S : System), Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (SA : SettlementAccess), SettlementDataAvailable W SA →
    ∀ (dA dB : Dest) (sl : Chain) (F : Flow) (ev : GateEvidenceAt) (leg : FlowLeg),
      ExecutedAtBy h z0 hl cv fh W S dA sl F ev leg →
      W.l1 dB = sl → ImportAvailable W S dB sl F.deadline →
        FlowFinalizableAt h z0 hl cv W S A SA dB sl F ∨ GateBreak h z0 hl S F (imtEvidence ev)

/-- **NONE OR ALL ON A READY DESTINATION, OR A LOCATED BREAK.**  The corrected
`Contracts.Atomicity.Properties.NoneOrAllOrBreak`.  For every flow, every evidence `ev` and
every ready destination `d`, one of three things holds: the flow is finalizable on `d`; `ev`
executes no leg, on any destination (`Properties.ExecutedAtProjects`); or the inclusion proof
`ev` submits for one of the flow's own legs carries a break. -/
def Properties.NoneOrAllAtOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (W : World)
    (S : System), Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (SA : SettlementAccess), SettlementDataAvailable W SA →
    ∀ (d : Dest) (sl : Chain) (F : Flow), W.l1 d = sl → ImportAvailable W S d sl F.deadline →
    ∀ (ev : GateEvidence),
      FlowFinalizableAt h z0 hl cv W S A SA d sl F
        ∨ (∀ leg, ¬ ExecutedViaBy h z0 hl cv fh S F ev leg)
        ∨ GateBreak h z0 hl S F ev

/-- **THE FIRST LEG STRANDED ON A DESTINATION IS UNIQUE.** -/
def Properties.FirstStrandedLegAtUnique : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (W : World) (S : System)
    (A : Access) (SA : SettlementAccess) (d : Dest) (sl : Chain) (F : Flow) (l₁ l₂ : FlowLeg),
    FirstStrandedLegAt h z0 hl cv W S A SA d sl F l₁ →
      FirstStrandedLegAt h z0 hl cv W S A SA d sl F l₂ → l₁ = l₂

/-- **ON A DESTINATION WITH IMPORTS, THE FIRST STRANDED LEG IS THE WORLD'S.**  With settlement
data available and import availability on `d`, the first leg stranded on `d` is the first
leg that is not finalizable in `Contracts.Atomicity`'s sense.  So the leg the pinned break
names does not depend on which ready destination is asked. -/
def Properties.ReadyFirstStrandedLegAtIff : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (W : World) (S : System)
    (A : Access) (SA : SettlementAccess), SettlementDataAvailable W SA →
    ∀ (d : Dest) (sl : Chain) (F : Flow), ImportAvailable W S d sl F.deadline →
    ∀ leg : FlowLeg,
      FirstStrandedLegAt h z0 hl cv W S A SA d sl F leg ↔ FirstStrandedLeg h z0 hl cv S A F leg

/-- **NONE OR ALL ON A READY DESTINATION, OR A BREAK ON THE FIRST LEG STRANDED THERE.**  The
corrected `Contracts.Atomicity.Properties.NoneOrAllOrBreakPinned`.  As
`Properties.NoneOrAllAtOrBreak`, with the break located on the first leg of the flow, in list
order, that is not finalizable on `d`. -/
def Properties.NoneOrAllAtOrBreakPinned : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (W : World)
    (S : System), Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (SA : SettlementAccess), SettlementDataAvailable W SA →
    ∀ (d : Dest) (sl : Chain) (F : Flow), W.l1 d = sl → ImportAvailable W S d sl F.deadline →
    ∀ (ev : GateEvidence),
      FlowFinalizableAt h z0 hl cv W S A SA d sl F
        ∨ (∀ leg, ¬ ExecutedViaBy h z0 hl cv fh S F ev leg)
        ∨ PinnedGateBreakAt h z0 hl cv W S A SA d sl F ev

/-- **FINALIZABILITY DOES NOT DECAY, ON A DESTINATION THAT IMPORTS A LATER ROOT, OR A LOCATED
BREAK.**  This is the precise form of what
`Contracts.Atomicity.Properties.ExecutedImpliesFinalityPersists`'s docstring describes.
Suppose a leg executed on the evidence `ev`.  Then every leg `other` of the flow has an
on-time batch `n` with the following property, or `ev other` carries a break.  At every later
on-time batch `m` for which destination `d` holds an imported root covering `m`, a prover can
present an IMT proof and a settlement proof that `d` accepts. -/
def Properties.ExecutedImpliesFinalityPersistsAtOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (W : World)
    (S : System), Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (SA : SettlementAccess), SettlementDataAvailable W SA →
    ∀ (d : Dest) (sl : Chain) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ other ∈ F.legs,
      (∃ n, S.time other.chain n ≤ F.deadline ∧
        ∀ m, n ≤ m → S.time other.chain m ≤ F.deadline → RootImported W d sl other.chain m →
          ∃ (p : ImtProof) (sp : SettlementProof), A other.chain m p ∧ SA other.chain m sp
            ∧ AcceptsAt h z0 hl W S d sl other.chain m (legValue cv F other) p sp)
        ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2

/-- **`NoneOrAllAtOrBreakPinned` FOR SYSTEMS BUILT FROM RUNS.**  The corrected
`Contracts.Atomicity.Properties.NoneOrAllOrBreakPinnedFromRuns`: its `Wf` premise is replaced
by `RunsWf`, which has no capacity field. -/
def Properties.NoneOrAllAtOrBreakPinnedFromRuns : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (St : Chain → ℕ → HState) (time : Chain → ℕ → ℕ), RunsWf St time →
    ∀ (A : Access), DataAvailable h z0 hl (systemOfRuns St time) A →
    ∀ (W : World) (SA : SettlementAccess), SettlementDataAvailable W SA →
    ∀ (d : Dest) (sl : Chain) (F : Flow), W.l1 d = sl →
      ImportAvailable W (systemOfRuns St time) d sl F.deadline →
    ∀ (ev : GateEvidence),
      FlowFinalizableAt h z0 hl cv W (systemOfRuns St time) A SA d sl F
        ∨ (∀ leg, ¬ ExecutedViaBy h z0 hl cv fh (systemOfRuns St time) F ev leg)
        ∨ PinnedGateBreakAt h z0 hl cv W (systemOfRuns St time) A SA d sl F ev

/-- **PARTIAL ATOMICITY OVER THE REAL FLOW, ON A READY DESTINATION, OR A LOCATED BREAK, OR A
LOGGED CLASH.**  The destination form of
`Contracts.FlowBinding.Properties.ExecutedImpliesRealFlowFinalizableOrLoggedClash`.  Take a
logged run, an execution `e` in its log, a call `c` of the same log claiming `e`'s flow id,
and a destination `d` that is ready for `c.flow`.  Then one of three things holds: every leg
of `c.flow` is finalizable on `d`; `e`'s evidence carries a break on the first leg of `e.flow`
that is not finalizable (`PinnedGateBreak`); or the two logged flows clash on the flow
hash. -/
def Properties.ExecutedImpliesRealFlowFinalizableAtOrLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (W : World) (SA : SettlementAccess), SettlementDataAvailable W SA →
    ∀ (Ms Ns : Contracts.Refund.Managers) (log : List Contracts.FlowBinding.CheckedCall),
      Contracts.FlowBinding.RunLog h z0 hl cv fh S Ms Ns log →
    ∀ (e : Contracts.FlowBinding.ExecCall), Contracts.FlowBinding.CheckedCall.execute e ∈ log →
    ∀ c ∈ log, c.flow.flowId = e.flow.flowId →
    ∀ (d : Dest) (sl : Chain), W.l1 d = sl → ImportAvailable W S d sl c.flow.deadline →
      FlowFinalizableAt h z0 hl cv W S A SA d sl c.flow
        ∨ PinnedGateBreak h z0 hl cv S A e.flow e.evidence
        ∨ FlowIdClash fh e.flow c.flow

/-! ## Countermodels: the new premises are load-bearing -/

/-- **WITHOUT A ROOT IMPORT, A FLOW SITS HALF-EXECUTED.**  The setting holds for every node
hash, leaf hash and padding constant, every settlement layer `sl`, and two distinct
destinations `dA ≠ dB`.  The system is `twoChainSystem 1 2`, and the flow is
`mixedFlow 0 1 2` with commit value `cv _ b = b`.  So both of its legs, `⟨0, 1⟩` and
`⟨1, 2⟩`, are committed on time, and IMT and settlement data are both available (honest
access).  The world is `importWorld sl (· = dA)`: only `dA` has imported the one
settlement-layer root, and both destinations are configured for `sl`.  Then:

* `dA` is ready, and leg `⟨0, 1⟩` executes on `dA` through `dA`'s own gate;
* `FlowFinalizableBy` holds, so `Contracts.Atomicity`'s none-or-all says the flow is fine;
* `dB` is not ready.  No leg can execute on `dB`, under any flow hash, and no leg is
  finalizable on `dB`, whatever the prover can present;
* no leg can be refunded either: no timeout evidence passes the gate unless it carries a
  located `AbsenceBreak`.

So a leg whose bundle is addressed to `dB` cannot complete until `dB` imports a root
(`Properties.ImportAloneRestoresFinalizability`), and the flow cannot be unwound meanwhile.
No contract defect is involved.  This is a liveness assumption about destinations, like
data availability. -/
def Properties.WithoutImportFlowSitsHalfExecuted : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (sl : Chain) (dA dB : Dest), dA ≠ dB →
    Wf (twoChainSystem 1 2)
      ∧ DataAvailable h z0 hl (twoChainSystem 1 2) (honestAccess h z0 hl (twoChainSystem 1 2))
      ∧ SettlementDataAvailable (importWorld sl (· = dA))
          (honestSettlementAccess (importWorld sl (· = dA)))
      ∧ (importWorld sl (· = dA)).l1 dA = sl ∧ (importWorld sl (· = dA)).l1 dB = sl
      ∧ ImportAvailable (importWorld sl (· = dA)) (twoChainSystem 1 2) dA sl
          (mixedFlow 0 1 2).deadline
      ∧ ¬ ImportAvailable (importWorld sl (· = dA)) (twoChainSystem 1 2) dB sl
          (mixedFlow 0 1 2).deadline
      ∧ ExecutedAt h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
          (importWorld sl (· = dA)) (twoChainSystem 1 2) dA sl (mixedFlow 0 1 2) ⟨0, 1⟩
      ∧ FlowFinalizableBy h z0 hl (fun _ b => b) (twoChainSystem 1 2)
          (honestAccess h z0 hl (twoChainSystem 1 2)) (mixedFlow 0 1 2)
      ∧ (∀ (fh : FlowHash) (leg : FlowLeg), ¬ ExecutedAt h z0 hl (fun _ b => b) fh
          (importWorld sl (· = dA)) (twoChainSystem 1 2) dB sl (mixedFlow 0 1 2) leg)
      ∧ (∀ (A : Access) (SA : SettlementAccess), ∀ leg ∈ (mixedFlow 0 1 2).legs,
          ¬ LegFinalizableAt h z0 hl (fun _ b => b) (importWorld sl (· = dA))
              (twoChainSystem 1 2) A SA dB sl (mixedFlow 0 1 2) leg)
      ∧ (∀ other ∈ (mixedFlow 0 1 2).legs, ∀ (N : ℕ) (q : ImtProof),
          ¬ LegRefundableBy h z0 hl (fun _ b => b) (twoChainSystem 1 2) (mixedFlow 0 1 2)
              other N q
            ∨ AbsenceBreak h z0 hl (twoChainSystem 1 2) (mixedFlow 0 1 2).deadline other.chain
                N q)

/-- **THE IMPORT IS ALL THAT IS MISSING.**  In the world of
`Properties.WithoutImportFlowSitsHalfExecuted`, add `dB`'s import of the same root, and change
nothing else (`ImportsGrow`).  Then `dB` has import availability, and the whole flow is
finalizable on `dB`. -/
def Properties.ImportAloneRestoresFinalizability : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (sl : Chain) (dA dB : Dest),
    ImportsGrow (importWorld sl (· = dA)) (importWorld sl (fun d => d = dA ∨ d = dB))
      ∧ ImportAvailable (importWorld sl (fun d => d = dA ∨ d = dB)) (twoChainSystem 1 2) dB sl
          (mixedFlow 0 1 2).deadline
      ∧ FlowFinalizableAt h z0 hl (fun _ b => b) (importWorld sl (fun d => d = dA ∨ d = dB))
          (twoChainSystem 1 2) (honestAccess h z0 hl (twoChainSystem 1 2))
          (honestSettlementAccess (importWorld sl (fun d => d = dA ∨ d = dB))) dB sl
          (mixedFlow 0 1 2)

/-- **SETTLEMENT-PROOF AVAILABILITY IS NECESSARY.**  Take destination `d`, which has imported
the covering root, in `twoChainSystem 1 2`, but with no settlement proof presentable.  Leg
`⟨0, 1⟩` is finalized on `d`: an accepted proof exists.  But it is not finalizable on `d`,
whatever IMT access the prover has.  And it cannot be refunded either: no timeout evidence
passes unless it carries a located `AbsenceBreak`. -/
def Properties.WithoutSettlementDataLegIsStuck : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (sl : Chain) (d : Dest),
    ImportAvailable (importWorld sl (· = d)) (twoChainSystem 1 2) d sl (mixedFlow 0 1 2).deadline
      ∧ ¬ SettlementDataAvailable (importWorld sl (· = d)) noSettlementAccess
      ∧ LegFinalizedAt h z0 hl (fun _ b => b) (importWorld sl (· = d)) (twoChainSystem 1 2) d sl
          (mixedFlow 0 1 2) ⟨0, 1⟩
      ∧ (∀ A : Access, ¬ LegFinalizableAt h z0 hl (fun _ b => b) (importWorld sl (· = d))
          (twoChainSystem 1 2) A noSettlementAccess d sl (mixedFlow 0 1 2) ⟨0, 1⟩)
      ∧ ∀ (N : ℕ) (q : ImtProof),
          ¬ LegRefundableBy h z0 hl (fun _ b => b) (twoChainSystem 1 2) (mixedFlow 0 1 2)
              ⟨0, 1⟩ N q
            ∨ AbsenceBreak h z0 hl (twoChainSystem 1 2) (mixedFlow 0 1 2).deadline 0 N q

/-! ## Anti-vacuity -/

/-- **THE CROSS-DESTINATION RESULT'S PREMISES HOLD TOGETHER, ITS BREAK IS FALSE, ITS
CONCLUSION IS TRUE.**  The setting holds for every node hash, leaf hash and padding constant,
every settlement layer `sl` and all destinations `dA`, `dB`.  It is `twoChainSystem 1 2` with
honest IMT and settlement access, in the world where both `dA` and `dB` have imported the
root.  There, leg `⟨0, 1⟩` of `mixedFlow 0 1 2` executes on `dA` on honest evidence, and that
evidence has no `GateBreak`.  `dB` is ready, and the flow is finalizable on `dB`.  So every
premise of `Properties.ExecutedAtImpliesAllFinalizableAtOrBreak` holds, and its first
disjunct holds while its second fails. -/
def Properties.ExecutedAtOrBreakSatisfiable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (sl : Chain) (dA dB : Dest),
    Wf (twoChainSystem 1 2)
      ∧ DataAvailable h z0 hl (twoChainSystem 1 2) (honestAccess h z0 hl (twoChainSystem 1 2))
      ∧ SettlementDataAvailable (importWorld sl (fun d => d = dA ∨ d = dB))
          (honestSettlementAccess (importWorld sl (fun d => d = dA ∨ d = dB)))
      ∧ (importWorld sl (fun d => d = dA ∨ d = dB)).l1 dB = sl
      ∧ ImportAvailable (importWorld sl (fun d => d = dA ∨ d = dB)) (twoChainSystem 1 2) dB sl
          (mixedFlow 0 1 2).deadline
      ∧ ∃ ev : GateEvidenceAt,
          ExecutedAtBy h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
            (importWorld sl (fun d => d = dA ∨ d = dB)) (twoChainSystem 1 2) dA sl
            (mixedFlow 0 1 2) ev ⟨0, 1⟩
          ∧ ¬ GateBreak h z0 hl (twoChainSystem 1 2) (mixedFlow 0 1 2) (imtEvidence ev)
          ∧ FlowFinalizableAt h z0 hl (fun _ b => b) (importWorld sl (fun d => d = dA ∨ d = dB))
              (twoChainSystem 1 2) (honestAccess h z0 hl (twoChainSystem 1 2))
              (honestSettlementAccess (importWorld sl (fun d => d = dA ∨ d = dB))) dB sl
              (mixedFlow 0 1 2)

/-- **ON A READY DESTINATION, THE PINNED BREAK IS EVALUATED ON A STRANDED LEG AND IS FALSE.**
The setting holds for every node hash, leaf hash, padding constant, settlement layer `sl` and
destination `d`.  The system is the well-formed `mixedSystem 1`, in which chain `0` commits
`1` and chain `1` commits nothing.  Prover access is honest for both IMT and settlement data.
The world is `importWorld sl (· = d)`, in which `d` is ready.  For `mixedFlow 0 1 2`: the flow
is not finalizable on `d`, and the first leg stranded on `d` is `⟨1, 2⟩`.  There is evidence
`ev` on which no leg executes, and `PinnedGateBreakAt`, which here inspects the proof `ev`
submits for `⟨1, 2⟩`, is false.  So all premises of `Properties.NoneOrAllAtOrBreakPinned`
hold, its first disjunct fails, and its third is evaluated on a named leg and fails. -/
def Properties.NoneOrAllAtOrBreakPinnedStrandedNotTautology : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (sl : Chain) (d : Dest),
    Wf (mixedSystem 1)
      ∧ DataAvailable h z0 hl (mixedSystem 1) (honestAccess h z0 hl (mixedSystem 1))
      ∧ SettlementDataAvailable (importWorld sl (· = d))
          (honestSettlementAccess (importWorld sl (· = d)))
      ∧ (importWorld sl (· = d)).l1 d = sl
      ∧ ImportAvailable (importWorld sl (· = d)) (mixedSystem 1) d sl (mixedFlow 0 1 2).deadline
      ∧ ¬ FlowFinalizableAt h z0 hl (fun _ b => b) (importWorld sl (· = d)) (mixedSystem 1)
          (honestAccess h z0 hl (mixedSystem 1)) (honestSettlementAccess (importWorld sl (· = d)))
          d sl (mixedFlow 0 1 2)
      ∧ FirstStrandedLegAt h z0 hl (fun _ b => b) (importWorld sl (· = d)) (mixedSystem 1)
          (honestAccess h z0 hl (mixedSystem 1)) (honestSettlementAccess (importWorld sl (· = d)))
          d sl (mixedFlow 0 1 2) ⟨1, 2⟩
      ∧ ∃ ev : GateEvidence,
          (∀ leg, ¬ ExecutedViaBy h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
              (mixedSystem 1) (mixedFlow 0 1 2) ev leg)
          ∧ ¬ PinnedGateBreakAt h z0 hl (fun _ b => b) (importWorld sl (· = d)) (mixedSystem 1)
              (honestAccess h z0 hl (mixedSystem 1))
              (honestSettlementAccess (importWorld sl (· = d))) d sl (mixedFlow 0 1 2) ev

/-- **ON THE SAME WORLD, A DESTINATION EXECUTION LANDS IN THE PINNED BREAK.**  The setting is
the world of `Properties.NoneOrAllAtOrBreakPinnedStrandedNotTautology`, with the toy leaf
hash (`value - nextValue`).  Leg `⟨0, 1⟩` executes on `d`, through `d`'s gate with honest
settlement proofs, on evidence whose IMT proof for the never-committed leg `⟨1, 2⟩` is forged:
a leaf-hash collision with chain `1`'s sentinel.  The flow is not finalizable on `d`, so the
first two disjuncts of `Properties.NoneOrAllAtOrBreakPinned` fail.  The pinned break holds,
on the stranded leg, and the executing leg's own proof carries no break. -/
def Properties.PinnedGateBreakAtFires : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (sl : Chain) (d : Dest),
    ∃ ev : GateEvidenceAt,
      ExecutedAtBy h z0 toyLeafHash (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
          (importWorld sl (· = d)) (mixedSystem 1) d sl (mixedFlow 0 1 2) ev ⟨0, 1⟩
        ∧ ¬ FlowFinalizableAt h z0 toyLeafHash (fun _ b => b) (importWorld sl (· = d))
            (mixedSystem 1) (honestAccess h z0 toyLeafHash (mixedSystem 1))
            (honestSettlementAccess (importWorld sl (· = d))) d sl (mixedFlow 0 1 2)
        ∧ PinnedGateBreakAt h z0 toyLeafHash (fun _ b => b) (importWorld sl (· = d))
            (mixedSystem 1) (honestAccess h z0 toyLeafHash (mixedSystem 1))
            (honestSettlementAccess (importWorld sl (· = d))) d sl (mixedFlow 0 1 2)
            (imtEvidence ev)
        ∧ ¬ InclusionBreak h z0 toyLeafHash (mixedSystem 1) 0 (imtEvidence ev ⟨0, 1⟩).1
            (imtEvidence ev ⟨0, 1⟩).2

/-- **`NoneOrAllAtOrBreakPinnedFromRuns`: PREMISES MET, BREAK EVALUATED ON A STRANDED LEG AND
FALSE.**  The setting holds for every node hash, leaf hash, padding constant, settlement
layer `sl` and destination `d`.  There are runs meeting `RunsWf` whose system has honest IMT
access, which is data available.  In `importWorld sl (· = d)`, settlement data is available
and `d` is ready.  The flow `mixedFlow 0 1 2` is not finalizable on `d`, and there is
evidence `ev` on which no leg executes and `PinnedGateBreakAt` is false. -/
def Properties.NoneOrAllAtOrBreakPinnedFromRunsStranded : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (sl : Chain) (d : Dest),
    ∃ St : Chain → ℕ → HState, RunsWf St (fun _ n => n)
      ∧ DataAvailable h z0 hl (systemOfRuns St (fun _ n => n))
          (honestAccess h z0 hl (systemOfRuns St (fun _ n => n)))
      ∧ SettlementDataAvailable (importWorld sl (· = d))
          (honestSettlementAccess (importWorld sl (· = d)))
      ∧ (importWorld sl (· = d)).l1 d = sl
      ∧ ImportAvailable (importWorld sl (· = d)) (systemOfRuns St (fun _ n => n)) d sl
          (mixedFlow 0 1 2).deadline
      ∧ ¬ FlowFinalizableAt h z0 hl (fun _ b => b) (importWorld sl (· = d))
            (systemOfRuns St (fun _ n => n)) (honestAccess h z0 hl (systemOfRuns St (fun _ n => n)))
            (honestSettlementAccess (importWorld sl (· = d))) d sl (mixedFlow 0 1 2)
      ∧ ∃ ev : GateEvidence,
          (∀ leg, ¬ ExecutedViaBy h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
              (systemOfRuns St (fun _ n => n)) (mixedFlow 0 1 2) ev leg)
          ∧ ¬ PinnedGateBreakAt h z0 hl (fun _ b => b) (importWorld sl (· = d))
              (systemOfRuns St (fun _ n => n))
              (honestAccess h z0 hl (systemOfRuns St (fun _ n => n)))
              (honestSettlementAccess (importWorld sl (· = d))) d sl (mixedFlow 0 1 2) ev

/-- **THE LOGGED-RUN FORM'S PREMISES HOLD TOGETHER.**  The setting holds for every node hash,
leaf hash, padding constant, settlement layer `sl` and destination `d`.  The system is the
well-formed `twoChainSystem 1 2`, with honest IMT access.  A logged run from fresh managers
executes leg `⟨0, 1⟩` of `mixedFlow 0 1 2` on honest evidence.  In `importWorld sl (· = d)`,
settlement data is available and `d` is ready for that flow.  Taking the execution itself as
the call `c`, the first disjunct of
`Properties.ExecutedImpliesRealFlowFinalizableAtOrLoggedClash` holds and the other two
fail. -/
def Properties.ExecutedImpliesRealFlowFinalizableAtOrLoggedClashWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (sl : Chain) (d : Dest),
    ∃ (log : List Contracts.FlowBinding.CheckedCall) (e : Contracts.FlowBinding.ExecCall),
      Wf (twoChainSystem 1 2)
        ∧ DataAvailable h z0 hl (twoChainSystem 1 2) (honestAccess h z0 hl (twoChainSystem 1 2))
        ∧ SettlementDataAvailable (importWorld sl (· = d))
            (honestSettlementAccess (importWorld sl (· = d)))
        ∧ Contracts.FlowBinding.RunLog h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
            (twoChainSystem 1 2) Contracts.Refund.emptyManagers Contracts.Refund.emptyManagers log
        ∧ Contracts.FlowBinding.CheckedCall.execute e ∈ log
        ∧ e.flow = mixedFlow 0 1 2
        ∧ (importWorld sl (· = d)).l1 d = sl
        ∧ ImportAvailable (importWorld sl (· = d)) (twoChainSystem 1 2) d sl e.flow.deadline
        ∧ FlowFinalizableAt h z0 hl (fun _ b => b) (importWorld sl (· = d)) (twoChainSystem 1 2)
            (honestAccess h z0 hl (twoChainSystem 1 2))
            (honestSettlementAccess (importWorld sl (· = d))) d sl e.flow
        ∧ ¬ PinnedGateBreak h z0 hl (fun _ b => b) (twoChainSystem 1 2)
            (honestAccess h z0 hl (twoChainSystem 1 2)) e.flow e.evidence
        ∧ ¬ FlowIdClash (honestFlowHash (mixedFlow 0 1 2)) e.flow e.flow

end Contracts.RootImport
