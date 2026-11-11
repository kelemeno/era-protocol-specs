import EraSpec.Protocol.InteropAtomicity.Specs.RefundStrong

/-!
# Properties: the refund side, strengthened

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.RefundStrong`,
`EraSpec.Protocol.InteropAtomicity.Specs.Refund` and
`EraSpec.Protocol.InteropAtomicity.Specs.Timeout`.  Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.RefundStrong`.  No statement here takes a hash
premise.

Three statements of `Properties/Refund.lean` say less than their documentation claimed.
This file states what was meant.

## 1. The timeout gate can be passed: completeness of the refund side

`Properties.TimeoutProofRefundsCommittedLeg` is the `Step.authorize` constructor with its
premises passed through.  It takes `RefundAuthorized` as a premise and never establishes
it, so it holds verbatim of a gate that never fires, and so does every refund-side safety
result.  The finalize side has its completeness statement
(`Contracts.Atomicity.Properties.MemberIsFinalizable`); the refund side had none.

* `Properties.RefundableIffMissedDeadline`: for a nonzero commit value on a well-formed
  history, the timeout gate accepts a proof carrying no located break exactly when the
  leg missed its deadline and its chain has a batch after the deadline.  The `→` half is
  completeness; the `←` half is the soundness of
  `Contracts.Timeout.Properties.TimeoutMeansMissedDeadlineOrBreak`, read for break-free
  proofs.
* `Properties.MissedDeadlineRefundableByHonestProof`: which proof does it.  At the first
  batch that settled after the deadline, the honest low-leaf proof against that batch's
  BEGIN tree passes, carries no break, and is presentable under data availability.
* `Properties.AcceptedGateIffMissedDeadline`: the same characterization for the gate as
  the contract runs it (`LegRefundableAcceptedBy`, with `_verifyLastBatchInRoot` as a
  proof), once a settlement-layer root created after the deadline is imported and the
  settlement layer aggregates honestly.
* `Properties.EndBranchAcceptsHonestProofs`: the END branch (the halted-chain path) is
  live too.  The honest batch-leaf path of the root's last batch passes
  `_verifyLastBatchInRoot`, with no located break.
* `Properties.StrandedFlowCommittedLegRefundable`: the run-level form.  If one leg of a
  checked flow missed its deadline on a chain that moved past it, then from EVERY
  reachable logged state, each leg of that flow still `Committed` can be authorized by a
  logged, verified `authorizeRefund` call carrying a break-free proof, and then claimed.

## 2. A cross-flow refund is a pinned clash between two flows of the run

`Properties.CrossFlowIdClashIsPinnedCollision` mentions no run, refund, manager or tree:
its conclusion is `FlowIdClash fh F F'` unfolded from its premises.
`Properties.CrossFlowRefundYieldsLoggedPinnedClash` is the statement about refunds: if an
obligation of a checked flow `F` is refunded in a reachable logged run, and no logged call
that marked it presented `F`, then a logged, verified call marked it and its flow clashes
with `F` on exactly the two flows' own preimages.  `Properties.RefundedIffLoggedMark` is
the run fact behind it: an obligation is past `Committed` exactly when some logged call
marked it.

## 3. The executed obligation, live and unrefunded

`Properties.ExecutedObligationNeverRefundedOrBreakWitness` never appends the executed
obligation, and its one logged call has a different flow id, so its two conclusions
already hold on the empty run.  `Properties.RefundBreakImpliesRefunded` explains why no
witness can do better on the break side: a `RefundBreak` names a logged call that marked
the obligation, so the milestone's content is `Refunded → RefundBreak`, and any witness
with the obligation unrefunded has no `RefundBreak` automatically.  What a witness can
show is that the obligation was live.
`Properties.ExecutedObligationNeverRefundedOrBreakAppendedWitness` (every hash) appends the
executed obligation and logs a verified call that claims the executed flow's id, with a
`FlowIdClash` against it.  `Properties.ExecutedObligationRefundBlockedOnlyByTimeoutGate`
(the sealed hash pair) adds that no `authorizeRefund` call of any flow can pass for the
executed obligation, while the flow passes `_checkFlowId` and the per-leg guard is open:
what holds it at `Committed` is the timeout gate.
-/

namespace Contracts.Refund

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf IMTAbstract
open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.AtomicFlowManager

/-! ## 1. Completeness of the timeout gate -/

/-- **THE TIMEOUT GATE ACCEPTS A BREAK-FREE PROOF EXACTLY FOR A LEG THAT MISSED ITS
DEADLINE.**  On a well-formed history, for a leg whose commit value is nonzero (a keccak
hash; `0` is the tree's sentinel and `verifyNonInclusion` rejects it): the leg's chain
has a batch after the deadline and the leg was absent from every on-time batch, if and
only if some timeout evidence `(N, p)` passes `LegRefundable`'s check and `p` carries no
`AbsenceBreak`.

The `→` half is the completeness `Properties.TimeoutProofRefundsCommittedLeg` lacked.  The
`←` half needs both conjuncts: a refund always needs a batch past the deadline, and a
break-free proof always means the leg missed it. -/
def Properties.RefundableIffMissedDeadline : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (F : Flow) (leg : FlowLeg), legValue cv F leg ≠ 0 →
      (((∃ N, F.deadline < S.time leg.chain N) ∧ LegMissedDeadline cv S F leg)
        ↔ ∃ (N : ℕ) (p : ImtProof), LegRefundableBy h z0 hl cv S F leg N p
            ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N p)

/-- **ITS PREMISES ARE SATISFIABLE, AND BOTH SIDES TAKE BOTH VALUES.**  In the well-formed
`mixedSystem 1` with commit value `fun _ b => b`, the leg `⟨1, 2⟩` of `mixedFlow 0 1 2`
(never committed) missed its deadline on a chain that moved past it, and the leg
`⟨0, 1⟩` (committed at batch 0) did not.  Both commit values are nonzero.  The left side
of the equivalence mentions no hash, so by the theorem the right side holds for `⟨1, 2⟩`
and fails for `⟨0, 1⟩` under every hash. -/
def Properties.RefundableIffMissedDeadlineWitness : Prop :=
  Wf (mixedSystem 1)
    ∧ legValue (fun _ b => b) (mixedFlow 0 1 2) ⟨1, 2⟩ ≠ 0
    ∧ (∃ N, (mixedFlow 0 1 2).deadline < (mixedSystem 1).time 1 N)
    ∧ LegMissedDeadline (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨1, 2⟩
    ∧ legValue (fun _ b => b) (mixedFlow 0 1 2) ⟨0, 1⟩ ≠ 0
    ∧ ¬ LegMissedDeadline (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨0, 1⟩

/-- **THE HONEST PROOF AT THE FIRST LATE BATCH DOES IT, AND DATA AVAILABILITY PRESENTS
IT.**  On a well-formed history with data availability, let a leg with nonzero commit
value miss its deadline, and let `N` be the first batch of its chain that settled after
the deadline.  Then for some occupied index `i` of the tree as batch `N` began, the
honest proof `honestBeginProof … N i` passes the timeout gate on the BEGIN branch at `N`,
carries no `AbsenceBreak`, and is presentable: either `N = 0` (the BEGIN tree is the
genesis `setup`, which needs no chain data) or the prover access covers it as the honest
proof of batch `N - 1`'s published tree. -/
def Properties.MissedDeadlineRefundableByHonestProof : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (F : Flow) (leg : FlowLeg), legValue cv F leg ≠ 0 → LegMissedDeadline cv S F leg →
    ∀ (N : ℕ), F.deadline < S.time leg.chain N → (∀ M < N, S.time leg.chain M ≤ F.deadline) →
      ∃ i, i < (beginTree S leg.chain N).leafCount
        ∧ LegRefundableBy h z0 hl cv S F leg N (honestBeginProof h z0 hl S leg.chain N i)
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N (honestBeginProof h z0 hl S leg.chain N i)
        ∧ (N = 0 ∨ A leg.chain (N - 1) (honestBeginProof h z0 hl S leg.chain N i))

/-- **ITS PREMISES ARE SATISFIABLE, WITH THE ACCESS DISJUNCT EXERCISED.**  For every hash:
`mixedSystem 1` is well formed, honest access is data available, and the never-committed
leg `⟨1, 2⟩` of `mixedFlow 0 1 2` (commit value `fun _ b => b`) missed its deadline, with
batch `1` the first late batch of chain `1`.  Since `1 ≠ 0`, the conclusion must supply
the proof through the prover access. -/
def Properties.MissedDeadlineRefundableByHonestProofWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    Wf (mixedSystem 1)
      ∧ DataAvailable h z0 hl (mixedSystem 1) (honestAccess h z0 hl (mixedSystem 1))
      ∧ legValue (fun _ b => b) (mixedFlow 0 1 2) ⟨1, 2⟩ ≠ 0
      ∧ LegMissedDeadline (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨1, 2⟩
      ∧ (mixedFlow 0 1 2).deadline < (mixedSystem 1).time 1 1
      ∧ (∀ M < 1, (mixedSystem 1).time 1 M ≤ (mixedFlow 0 1 2).deadline)

/-- **THE GATE AS THE CONTRACT RUNS IT, CHARACTERIZED.**  On a well-formed history whose
settlement layer aggregates honestly into an imported root `R` created after the
deadline, for a leg with nonzero commit value: the leg missed its deadline if and only if
some submission `(N, p, sibs, x)` passes `verifyTimeoutAbsence` as run, its absence proof
`p` carries no `AbsenceBreak`, and (on the END branch) its batch-leaf path pins no
collision.

`→` is completeness: the BEGIN branch at the first late batch, which exists because the
batch right after the root's last one settled after the root was created.  `←` is
`Contracts.Timeout.Properties.AcceptedTimeoutMeansMissedDeadlineOrBreak` with its breaks
excluded. -/
def Properties.AcceptedGateIffMissedDeadline : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R), Aggregates S R →
    ∀ (F : Flow) (leg : FlowLeg), F.deadline < R.created → legValue cv F leg ≠ 0 →
      (LegMissedDeadline cv S F leg
        ↔ ∃ (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
            LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x
            ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N p
            ∧ ¬ (EndBranchAccepted B S leg.chain F.deadline N sibs x
                ∧ (PinnedBreak h ze (B.leaves leg.chain) N
                  ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x)))

/-- **ITS PREMISES ARE SATISFIABLE, AND BOTH SIDES TAKE BOTH VALUES.**  For every hash and
chain-tree padding constant: `mixedSystem 1` with `timeOneRoot` and a backing for it
(`Aggregates` holds, the root was created at time `1`, after deadline `0`); commit value
`fun _ b => b`; the leg `⟨1, 2⟩` of `mixedFlow 0 1 2` missed its deadline and `⟨0, 1⟩`
did not. -/
def Properties.AcceptedGateIffMissedDeadlineWitness : Prop :=
  ∀ (h : Hash) (ze : UInt256),
    Nonempty (RootBacking h ze timeOneRoot)
      ∧ Wf (mixedSystem 1) ∧ Aggregates (mixedSystem 1) timeOneRoot
        ∧ (mixedFlow 0 1 2).deadline < timeOneRoot.created
        ∧ legValue (fun _ b => b) (mixedFlow 0 1 2) ⟨1, 2⟩ ≠ 0
        ∧ LegMissedDeadline (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨1, 2⟩
        ∧ legValue (fun _ b => b) (mixedFlow 0 1 2) ⟨0, 1⟩ ≠ 0
        ∧ ¬ LegMissedDeadline (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨0, 1⟩

/-- **THE END BRANCH IS LIVE: THE HALTED-CHAIN PATH.**  On a well-formed history, with an
imported root `R` created after the deadline whose last batch of the leg's chain settled
by the deadline, a leg with nonzero commit value absent from that batch's tree passes the
gate as the contract runs it on the END branch: the honest IMT absence proof of that
batch's tree, with the honest batch-leaf path of the root's last batch for
`_verifyLastBatchInRoot`.  Neither proof carries a located break.  No `Aggregates`
premise: completeness does not need it. -/
def Properties.EndBranchAcceptsHonestProofs : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R) (F : Flow) (leg : FlowLeg),
      F.deadline < R.created → S.time leg.chain (R.upTo leg.chain) ≤ F.deadline →
      legValue cv F leg ≠ 0 →
      legValue cv F leg ∉ keys (toAbs (S.tree leg.chain (R.upTo leg.chain))) →
      ∃ i, i < (S.tree leg.chain (R.upTo leg.chain)).leafCount
        ∧ LegRefundableAcceptedBy h z0 hl cv S B F leg (R.upTo leg.chain)
            (honestProof h z0 hl S leg.chain (R.upTo leg.chain) i)
            (honestSibs h ze (B.leaves leg.chain) (R.upTo leg.chain))
            ((B.leaves leg.chain).getD (R.upTo leg.chain) ze)
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain (R.upTo leg.chain)
            (honestProof h z0 hl S leg.chain (R.upTo leg.chain) i)
        ∧ ¬ PinnedBreak h ze (B.leaves leg.chain) (R.upTo leg.chain)
        ∧ ¬ PathCollision h ze (B.leaves leg.chain)
            (honestSibs h ze (B.leaves leg.chain) (R.upTo leg.chain)) 0 (B.height leg.chain)
            (R.upTo leg.chain) ((B.leaves leg.chain).getD (R.upTo leg.chain) ze)

/-- **ITS PREMISES ARE SATISFIABLE.**  For every hash and chain-tree padding constant:
`demoSystem` (batches `0, 1` at time `0`, the tree stays `setup`) is well formed, and with
`demoRoot` (created at time `1`, last batch `1`) and a backing for it, the leg `⟨0, 0⟩`
with commit value `1` and deadline `0` has the root's last batch on time and is absent
from it. -/
def Properties.EndBranchAcceptsHonestProofsWitness : Prop :=
  ∀ (h : Hash) (ze : UInt256),
    Nonempty (RootBacking h ze demoRoot)
      ∧ Wf demoSystem
        ∧ (⟨0, [⟨0, 0⟩], 0⟩ : Flow).deadline < demoRoot.created
        ∧ demoSystem.time 0 (demoRoot.upTo 0) ≤ (⟨0, [⟨0, 0⟩], 0⟩ : Flow).deadline
        ∧ legValue (fun _ _ => 1) ⟨0, [⟨0, 0⟩], 0⟩ ⟨0, 0⟩ ≠ 0
        ∧ legValue (fun _ _ => 1) ⟨0, [⟨0, 0⟩], 0⟩ ⟨0, 0⟩
            ∉ keys (toAbs (demoSystem.tree 0 (demoRoot.upTo 0)))

/-- **A STRANDED FLOW'S COMMITTED LEGS CAN BE REFUNDED FROM EVERY REACHABLE STATE.**  Let
a leg `m` of a checked flow `F` have a nonzero commit value, miss its deadline, and sit on
a chain with a batch after the deadline.  Then from every state a logged run reaches from
fresh managers, every leg `leg` of `F` whose obligation is still `Committed` can be moved
on: there is an `authorizeRefund` call for exactly `(F, leg)` with missing leg `m`, which
passes every check (`AuthCall.Verified`) on an absence proof carrying no located break;
appending it to the run reaches a state where the obligation is `Revertable`, and a
further `claimRefund` reaches one where it is `Reverted` and every other obligation is as
before.

This is what `Properties.TimeoutProofRefundsCommittedLeg` claimed ("the refund branch is
reachable") with its `RefundAuthorized` premise discharged.  The refunded leg need not be
the stranded one: `authorizeRefund` refunds the flow's other legs on the strength of one
missing leg, and the witness refunds a leg that WAS committed on time. -/
def Properties.StrandedFlowCommittedLegRefundable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow), FlowIdChecked fh F → ∀ m ∈ F.legs, legValue cv F m ≠ 0 →
    (∃ N, F.deadline < S.time m.chain N) → LegMissedDeadline cv S F m →
    ∀ (Ms : Managers) (log : List AuthCall), ReachLog h z0 hl cv fh S emptyManagers Ms log →
    ∀ leg ∈ F.legs, stateOf Ms (obligationOf F leg) = .Committed →
      ∃ (a : AuthCall) (Ms₁ Ms₂ : Managers),
        a.flow = F ∧ a.leg = leg ∧ a.missing = m ∧ a.Verified h z0 hl cv fh S
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline m.chain a.batch a.proof
        ∧ ReachLog h z0 hl cv fh S emptyManagers Ms₁ (a :: log)
        ∧ stateOf Ms₁ (obligationOf F leg) = .Revertable
        ∧ ReachLog h z0 hl cv fh S emptyManagers Ms₂ (a :: log)
        ∧ stateOf Ms₂ (obligationOf F leg) = .Reverted
        ∧ ∀ o, o ≠ obligationOf F leg → stateOf Ms₂ o = stateOf Ms o

/-- **ITS PREMISES ARE SATISFIABLE, AND THE REFUNDED LEG WAS DELIVERED ON TIME.**  For
every hash: in `mixedSystem 1` with commit value `fun _ b => b`, the flow
`mixedFlow 0 1 2` passes `_checkFlowId` under its honest flow hash; its leg `⟨1, 2⟩` missed
its deadline on a chain that moved past it; the one-step run appending leg `⟨0, 1⟩` on
chain `0` leaves that leg's obligation `Committed`; and `⟨0, 1⟩` did NOT miss its
deadline.  So the theorem refunds a committed sibling of a stranded leg. -/
def Properties.StrandedFlowCommittedLegRefundableWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Ms : Managers) (log : List AuthCall),
      Wf (mixedSystem 1)
        ∧ FlowIdChecked (honestFlowHash (mixedFlow 0 1 2)) (mixedFlow 0 1 2)
        ∧ (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 0 1 2).legs
        ∧ legValue (fun _ b => b) (mixedFlow 0 1 2) ⟨1, 2⟩ ≠ 0
        ∧ (∃ N, (mixedFlow 0 1 2).deadline < (mixedSystem 1).time 1 N)
        ∧ LegMissedDeadline (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨1, 2⟩
        ∧ ReachLog h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2)) (mixedSystem 1)
            emptyManagers Ms log
        ∧ (⟨0, 1⟩ : FlowLeg) ∈ (mixedFlow 0 1 2).legs
        ∧ stateOf Ms (obligationOf (mixedFlow 0 1 2) ⟨0, 1⟩) = .Committed
        ∧ ¬ LegMissedDeadline (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨0, 1⟩

/-! ## 2. Cross-flow refunds, at run level -/

/-- **AN OBLIGATION IS PAST `Committed` EXACTLY WHEN A LOGGED CALL MARKED IT.**  On every
logged run from fresh managers.  `→` is `Properties.RefundNeedsLoggedAuthorize`; `←` is
the manager's monotone lifecycle: once `authorizeRefund` marks an obligation, `append`
and `authorizeRefund` can no longer fire on it and `claimRefund` only moves it on. -/
def Properties.RefundedIffLoggedMark : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (Ms : Managers) (log : List AuthCall), ReachLog h z0 hl cv fh S emptyManagers Ms log →
    ∀ (o : Obligation), Refunded Ms o ↔ ∃ a ∈ log, obligationOf a.flow a.leg = o

/-- **ITS PREMISES ARE SATISFIABLE, AND BOTH SIDES TAKE BOTH VALUES.**  For every hash: a
three-step run in `mixedSystem 1` under the constant commit value `1` and `lengthFlowHash`
(append `(1, 2)` on chain `1`, authorize it through `mixedFlow 1 1 2` on a verified
timeout, append `(0, 1)` on chain `0`).  The authorized obligation is refunded; the other
appended one is `Committed`. -/
def Properties.RefundedIffLoggedMarkWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Ms : Managers) (log : List AuthCall) (o o' : Obligation),
      ReachLog h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) emptyManagers Ms log
        ∧ Refunded Ms o ∧ stateOf Ms o' = .Committed

/-- **A CROSS-FLOW REFUND IS A PINNED CLASH BETWEEN TWO FLOWS OF THE RUN.**  If an
obligation carrying a checked flow `F`'s id is past `Committed` in a reachable logged
state, and no logged call that marked it presented `F` itself, then a logged call marked
it, that call passed every check of `authorizeRefund`, and its flow and `F` collide under
`fh` on exactly their own `(legs, deadline)` preimages.

The run-level form of the README's "a cross-flow refund yields a collision of the
flow-id hash on the two flows' own preimages", which
`Properties.CrossFlowIdClashIsPinnedCollision` only restates as a definition.  Given that
both flows pass `_checkFlowId` with one id, the clash is equivalent to the marking call's
flow differing from `F` (as for `FlowBinding`'s logged clash): what this adds is that the
colliding flow is the one a logged, verified call presented, not a free variable. -/
def Properties.CrossFlowRefundYieldsLoggedPinnedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (F : Flow) (leg : FlowLeg), FlowIdChecked fh F →
    ∀ (Ms : Managers) (log : List AuthCall), ReachLog h z0 hl cv fh S emptyManagers Ms log →
    Refunded Ms (obligationOf F leg) →
    (∀ a ∈ log, obligationOf a.flow a.leg = obligationOf F leg → a.flow ≠ F) →
      ∃ a ∈ log, a.Verified h z0 hl cv fh S ∧ obligationOf a.flow a.leg = obligationOf F leg
        ∧ FlowIdClash fh F a.flow

/-- **ITS PREMISES ARE SATISFIABLE: A REAL CROSS-FLOW REFUND.**  For every hash: under
`lengthFlowHash`, the one-leg flows `⟨0, [⟨1, 2⟩], 0⟩` and `⟨0, [⟨1, 2⟩], 5⟩` both pass
`_checkFlowId` with id `0` and own the same obligation.  In `mixedSystem 1` the run that
appends that obligation and authorizes the second flow's refund on its own verified
timeout refunds the first flow's obligation through the second flow alone. -/
def Properties.CrossFlowRefundYieldsLoggedPinnedClashWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (F : Flow) (leg : FlowLeg) (Ms : Managers) (log : List AuthCall),
      FlowIdChecked lengthFlowHash F ∧ leg ∈ F.legs
        ∧ ReachLog h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) emptyManagers Ms log
        ∧ log ≠ [] ∧ Refunded Ms (obligationOf F leg)
        ∧ ∀ a ∈ log, obligationOf a.flow a.leg = obligationOf F leg → a.flow ≠ F

/-! ## 3. The executed obligation, live and unrefunded -/

/-- **A LOCATED REFUND BREAK NEEDS A REFUND.**  On every logged run from fresh managers,
a `RefundBreak` for an obligation names a logged call that marked it, so the obligation
is past `Committed`.  Hence `Properties.ExecutedObligationNeverRefundedOrBreak` says
exactly "refunded → `RefundBreak`", and any state in which the obligation is not refunded
has no `RefundBreak` for it. -/
def Properties.RefundBreakImpliesRefunded : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (Ms : Managers) (log : List AuthCall), ReachLog h z0 hl cv fh S emptyManagers Ms log →
    ∀ (F : Flow) (ev : GateEvidence) (o : Obligation),
      RefundBreak h z0 hl fh S F ev o log → Refunded Ms o

/-- **ITS PREMISES ARE SATISFIABLE.**  For every node hash and leaf hash, with the
extraction-pin padding: the padding-forgery run of
`Properties.PaddingRefundOfExecutedObligationLocatesAbsenceBreak` carries a
`RefundBreak`. -/
def Properties.RefundBreakImpliesRefundedWitness : Prop :=
  ∀ (h : Hash) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (Ms : Managers) (log : List AuthCall) (F : Flow)
      (ev : GateEvidence) (o : Obligation),
      ReachLog h (hl ⟨0, 0, 0⟩) hl cv fh (paddedSystem 1 2) emptyManagers Ms log
        ∧ RefundBreak h (hl ⟨0, 0, 0⟩) hl fh (paddedSystem 1 2) F ev o log

/-- **THE EXECUTED OBLIGATION IS APPENDED, A LOGGED CALL CLAIMS ITS FLOW ID, AND NO
BREAK IS LOCATED.**  For every node hash, leaf hash and padding constant: in
`mixedSystem 1` under the constant commit value `1` and `lengthFlowHash`, the one-leg flow
`subsetFlow 0 1` executes on honest evidence (no `GateBreak`).  The run appends its
obligation, which is `Committed` at the end, so `authorizeRefund`'s per-leg guard is open
for it.  The run also appends and authorizes, on a verified timeout, a leg of a different
flow claiming the SAME id `0`, and that flow and the executed one have a `FlowIdClash`.
Still no `RefundBreak` is located for the executed obligation and it is not refunded:
the clash is not a break, since that call marked a different obligation.

Strengthens `Properties.ExecutedObligationNeverRefundedOrBreakWitness`, whose run never
appends the executed obligation and whose logged call has a different id. -/
def Properties.ExecutedObligationNeverRefundedOrBreakAppendedWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (F : Flow) (ev : GateEvidence)
      (leg : FlowLeg) (Ms : Managers) (log : List AuthCall),
      Wf S ∧ ExecutedViaBy h z0 hl cv fh S F ev leg ∧ ¬ GateBreak h z0 hl S F ev
        ∧ ReachLog h z0 hl cv fh S emptyManagers Ms log
        ∧ stateOf Ms (obligationOf F leg) = .Committed
        ∧ (∃ a ∈ log, a.flow.flowId = F.flowId ∧ FlowIdClash fh F a.flow)
        ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) log
        ∧ ¬ Refunded Ms (obligationOf F leg)

/-- **ONLY THE TIMEOUT GATE HOLDS THE EXECUTED OBLIGATION AT `Committed`.**  The run of
`Properties.ExecutedObligationNeverRefundedOrBreakAppendedWitness` under the sealed pair
`sealedNodeHash`, `sealedLeafHash`.  In addition to everything there: the executed flow
passes `_checkFlowId`, its leg is one of its legs and the obligation's guard is open, yet
no timeout evidence `(N, p)` passes the gate for that leg; and no `authorizeRefund` call
of ANY flow that passes every check marks the executed obligation.  So the obligation is
live, and what keeps it unrefunded is the timeout gate. -/
def Properties.ExecutedObligationRefundBlockedOnlyByTimeoutGate : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (F : Flow) (ev : GateEvidence) (leg : FlowLeg) (Ms : Managers) (log : List AuthCall),
    Wf S ∧ ExecutedViaBy h z0 hl cv fh S F ev leg ∧ ¬ GateBreak h z0 hl S F ev
      ∧ ReachLog h z0 hl cv fh S emptyManagers Ms log
      ∧ stateOf Ms (obligationOf F leg) = .Committed
      ∧ (∃ a ∈ log, a.flow.flowId = F.flowId ∧ FlowIdClash fh F a.flow)
      ∧ (∀ (N : ℕ) (p : ImtProof), ¬ LegRefundableBy h z0 hl cv S F leg N p)
      ∧ (∀ a : AuthCall, a.Verified h z0 hl cv fh S →
          obligationOf a.flow a.leg ≠ obligationOf F leg)
      ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) log
      ∧ ¬ Refunded Ms (obligationOf F leg)

end Contracts.Refund
