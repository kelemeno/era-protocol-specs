import EraSpec.Protocol.InteropAtomicity.Specs.RefundStrong

/-!
# Properties: the refund side, strengthened

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.RefundStrong`,
`EraSpec.Protocol.InteropAtomicity.Specs.Refund` and
`EraSpec.Protocol.InteropAtomicity.Specs.Timeout`.  Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.RefundStrong`.  No statement here takes a hash
premise.

Three statements of `Properties/Refund.lean` say less than their documentation claimed.
This file states what can be proved in their place, and says where each statement stops.

Source lines are in `atomic-interop/libraries/AtomicInteropProof.sol`, under
`l1-contracts/contracts/` of the pinned era-contracts tree (`c67894b9`).

## Two gates

Every statement below names the gate it is about.

* The LOOSE gate `Contracts.Atomicity.LegRefundableBy` resolves against no root.  Its BEGIN
  branch may cite any batch of the fixed history that settled after the deadline, and its
  END branch is `IsLastOnTime`: the batch is on time and every later batch of the history
  is late.  `AuthCall.Verified`, `ReachLog` and the fixed-history safety results use it.
  It admits more refunds than the contract.  That is the conservative direction for a
  result that excludes a refund, and the non-conservative one for a result that says a
  refund can happen.
* The gate AS RUN is `Contracts.Timeout.LegRefundableAcceptedBy`, against an imported root
  `R` and its chain batch trees `B`: the three timestamp comparisons, the IMT absence
  check, and `_verifyLastBatchInRoot` as a path proof on the END branch.  The contract
  also authenticates the proven batch as a batch of that same root, on BOTH branches
  (`_authenticateRoot`, called at `:166`, defined at `:256-290`; the root's timestamp is
  read at `:171-179`; "one batch of the source chain inside that root", `:64-65`).
  `LegRefundableAcceptedBy` says that on the END branch only (`LastBatchAccepted.inRange`),
  so the statements about the gate as run add `N ≤ R.upTo leg.chain`.  Authentication
  itself is taken by its documented meaning, as in `Specs/Timeout.lean` and
  `Specs/Operational.lean`.

## 1. The timeout gate can be passed: completeness of the refund side

`Properties.TimeoutProofRefundsCommittedLeg` is the `Step.authorize` constructor with its
premises passed through.  It takes `RefundAuthorized` as a premise and never establishes
it, so it holds verbatim of a gate that never fires, and so does every refund-side safety
result of `Properties/Refund.lean` and `Properties/Timeout.lean`.  The finalize side has
its completeness statement (`Contracts.Atomicity.Properties.MemberIsFinalizable`).  For
the refund side two results exist elsewhere: the operational model proves that
`authorizeRefund` is enabled against a recorded root
(`Contracts.InteropOperational.Properties.OpTimedOutLegIsRefundable`, with
`_verifyLastBatchInRoot` taken by its conclusion), and the reference bridge proves
completeness at index level
(`Applications.BurnMintBridge.EndBranch.Properties.TimeoutComplete`).  This file adds
the gate-level statements: both directions, at hash level, with the located breaks
excluded, the END branch's batch-leaf path as a proof, and presentability of the BEGIN
proof.

* `Properties.RefundableIffMissedDeadline` (loose gate): for a nonzero commit value on a
  well-formed history, the loose gate accepts a proof carrying no located break exactly
  when the leg missed its deadline and the history has a batch of its chain after the
  deadline.  The `→` half is completeness; the `←` half is the soundness of
  `Contracts.Timeout.Properties.TimeoutMeansMissedDeadlineOrBreak`, read for break-free
  proofs.
* `Properties.MissedDeadlineRefundableByHonestProof` (loose gate): which proof does it.
  At the first batch that settled after the deadline, the honest low-leaf proof against
  that batch's BEGIN tree passes, carries no break, and is presentable under data
  availability.
* `Properties.AcceptedGateCompleteFromAnyPostDeadlineRoot` (gate as run): the source's
  COMPLETENESS paragraph (`:89-94`).  From ANY imported root created after the deadline,
  a leg that missed its deadline has an accepted, break-free submission for a batch
  inside that root.  No aggregation premise.
* `Properties.AcceptedGateIffMissedDeadline` (gate as run): with the strict aggregation
  fact `AggregatesBefore`, that is an equivalence.
* `Properties.EndBranchAcceptsHonestProofs` (gate as run): the END case with its proofs
  named.  The honest batch-leaf path of the root's last batch passes
  `_verifyLastBatchInRoot`, with no located break.
* `Properties.StrandedFlowCommittedLegRefundable` (loose gate, fixed history): the
  manager-level form.  If one leg of a checked flow missed its deadline on a chain with a
  later batch, then at every manager state each leg of that flow still `Committed` can be
  authorized by a verified `authorizeRefund` call carrying a break-free proof, and then
  claimed.  This is enabledness in a model that admits more refunds than the contract;
  its docstring lists what the model leaves out.

## 2. Refunds at run level

`Properties.RefundedIffLoggedMark` is the run fact: on a logged run from fresh managers
an obligation is past `Committed` exactly when some logged call marked it.  `→` is
`Properties.RefundNeedsLoggedAuthorize`; `←`, the manager's monotone lifecycle, is new.

`Properties.CrossFlowIdClashIsPinnedCollision` mentions no run, refund, manager or tree:
it is the definition of `FlowIdClash` under its premises.
`Properties.CrossFlowRefundYieldsLoggedPinnedClash` puts it next to a run, and it is a
corollary: `Properties.RefundNeedsLoggedAuthorize` composed with
`Properties.CrossFlowIdClashIsPinnedCollision`.  If an obligation carrying a checked flow
`F`'s id is refunded in a logged run, and no logged call that marked it presented `F`,
then a logged, verified call marked it and its flow clashes with `F`.  Only that call's
flow is a flow of the run.  `F` is any checked flow claiming the id: a `ReachLog` run does
not record which flow an `append` was made for, so `F` need not occur in it.
`Properties.RefundImpliesOwnFlowTimeoutOrLoggedClash` is the same fact in disjunctive
form.  Its witness is a refund that does cross flows: a leg delivered through one flow is
refunded on the timeout of another flow with the same id.

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
`FlowIdClash` against it.
`Properties.ExecutedObligationLiveAndUnmarkableUnderSealedHash` (the sealed hash pair)
adds that no `authorizeRefund` call of any flow can pass for the executed obligation,
while the flow passes `_checkFlowId` and the per-leg guard is open.  Two checks do that
together, the flow-id check and the timeout gate; the witness of section 2 shows that the
timeout gate alone does not.
-/

namespace Contracts.Refund

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf IMTAbstract
open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.AtomicFlowManager

/-! ## 1. Completeness of the timeout gate -/

/-- **THE LOOSE GATE ACCEPTS A BREAK-FREE PROOF EXACTLY FOR A LEG THAT MISSED ITS DEADLINE
ON A CHAIN WITH A LATER BATCH.**  On a well-formed history, for a leg whose commit value
is nonzero (a keccak hash; `0` is the tree's sentinel and `verifyNonInclusion` rejects
it): the leg's chain has a batch after the deadline and the leg was absent from every
on-time batch, if and only if some timeout evidence `(N, p)` passes the loose gate
`LegRefundableBy` and `p` carries no `AbsenceBreak`.

The `→` half is the completeness `Properties.TimeoutProofRefundsCommittedLeg` lacked, for
the gate that statement is about.  The `←` half needs both conjuncts: the loose gate
passes only if the history has a batch after the deadline (its END branch, `IsLastOnTime`,
says the next batch is late), and a break-free proof always means the leg missed the
deadline.

This is not a statement about `verifyTimeoutAbsence`.  The contract can cite only a batch
inside an imported root, so a late batch of the history is of no use to it unless such a
root holds it; and its END branch needs no late batch at all, only a root created after
the deadline.  The gate as run is characterized by
`Properties.AcceptedGateIffMissedDeadline`. -/
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

/-- **THE HONEST PROOF AT THE FIRST LATE BATCH PASSES THE LOOSE GATE, AND DATA AVAILABILITY
PRESENTS IT.**  On a well-formed history with data availability, let a leg with nonzero
commit value miss its deadline, and let `N` be the first batch of its chain that settled
after the deadline.  Then for some occupied index `i` of the tree as batch `N` began, the
honest proof `honestBeginProof … N i` passes the loose gate `LegRefundableBy` on the BEGIN
branch at `N`, carries no `AbsenceBreak`, and is presentable: either `N = 0` (the BEGIN
tree is the genesis `setup`, which needs no chain data) or the prover access covers it as
the honest proof of batch `N - 1`'s published tree.

The contract can use this proof only against an imported root that holds batch `N`.  The
proof of `Properties.AcceptedGateCompleteFromAnyPostDeadlineRoot` takes it in exactly that
case, and the END branch otherwise. -/
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

/-- **THE GATE AS RUN IS COMPLETE FROM ANY ROOT CREATED AFTER THE DEADLINE.**  On a
well-formed history, take any imported settlement-layer root `R` created after the
deadline, with its chain batch trees `B`, and a leg with nonzero commit value that missed
its deadline.  Then some submission `(N, p, sibs, x)` for a batch inside `R`
(`N ≤ R.upTo leg.chain`) passes `verifyTimeoutAbsence` as run, its absence proof `p`
carries no `AbsenceBreak`, and (on the END branch) its batch-leaf path pins no collision.

This is the source's COMPLETENESS paragraph (`:89-94`), and the proof makes its case
split.  If `R` holds a batch of the leg's chain that settled after the deadline, the
submission is on the BEGIN branch at the first such batch.  Otherwise it is on the END
branch at `R`'s last batch of that chain (`Properties.EndBranchAcceptsHonestProofs`), the
case of a chain that halted.  There is no premise on how the settlement layer aggregates:
`R` may be any root.  The index-level counterpart is
`Applications.BurnMintBridge.EndBranch.Properties.TimeoutComplete`.

`N ≤ R.upTo leg.chain` is what makes this the contract's completeness (see "Two gates" in
the header).  Without it the BEGIN branch could cite a late batch of the history that
lies outside `R`, which no call can authenticate against `R`; whenever the history has
such a batch, the END branch would never be needed.

The statement says an accepted submission exists.  The proof builds it from the honest
IMT proofs: `Properties.MissedDeadlineRefundableByHonestProof` shows the BEGIN proof is
presentable under data availability, and the END proof is `honestProof` of a batch tree,
which `DataAvailable` covers by definition.  The batch-leaf path is settlement-layer data,
which `Access` does not model. -/
def Properties.AcceptedGateCompleteFromAnyPostDeadlineRoot : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R) (F : Flow) (leg : FlowLeg),
      F.deadline < R.created → legValue cv F leg ≠ 0 → LegMissedDeadline cv S F leg →
      ∃ (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
        N ≤ R.upTo leg.chain
          ∧ LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x
          ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N p
          ∧ ¬ (EndBranchAccepted B S leg.chain F.deadline N sibs x
              ∧ (PinnedBreak h ze (B.leaves leg.chain) N
                ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x))

/-- **THE GATE AS THE CONTRACT RUNS IT, CHARACTERIZED.**  On a well-formed history, with
an imported root `R` created after the deadline that holds every batch settled strictly
before it (`AggregatesBefore`), for a leg with nonzero commit value: the leg missed its
deadline if and only if some submission `(N, p, sibs, x)` for a batch inside `R`
(`N ≤ R.upTo leg.chain`) passes `verifyTimeoutAbsence` as run, its absence proof `p`
carries no `AbsenceBreak`, and (on the END branch) its batch-leaf path pins no collision.

`→` is `Properties.AcceptedGateCompleteFromAnyPostDeadlineRoot`; it does not use the
aggregation premise.  `←` is the argument of
`Contracts.Timeout.Properties.AcceptedTimeoutMeansMissedDeadlineOrBreak` with its breaks
excluded, run from the strict `AggregatesBefore` instead of `Aggregates`; it does not use
`N ≤ R.upTo leg.chain`.  The strict form is the one every recorded root of an operational
run satisfies (`Contracts.InteropOperational.Properties.OpRunRootsAggregateBefore`); the
non-strict form can fail there
(`Contracts.InteropOperational.Properties.OpRootMayMissSameTimeBatch`). -/
def Properties.AcceptedGateIffMissedDeadline : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R),
      Contracts.InteropOperational.AggregatesBefore S R →
    ∀ (F : Flow) (leg : FlowLeg), F.deadline < R.created → legValue cv F leg ≠ 0 →
      (LegMissedDeadline cv S F leg
        ↔ ∃ (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
            N ≤ R.upTo leg.chain
            ∧ LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x
            ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N p
            ∧ ¬ (EndBranchAccepted B S leg.chain F.deadline N sibs x
                ∧ (PinnedBreak h ze (B.leaves leg.chain) N
                  ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x)))

/-- **THEIR PREMISES ARE SATISFIABLE ON BOTH BRANCHES, AND BOTH SIDES TAKE BOTH VALUES.**
The witness of `Properties.AcceptedGateIffMissedDeadline` and of
`Properties.AcceptedGateCompleteFromAnyPostDeadlineRoot`.  For every hash and chain-tree
padding constant, two worlds:

* A root that holds a late batch.  `mixedSystem 1` with `timeOneRoot` and a backing for
  it (`AggregatesBefore` holds; the root was created at time `1`, after deadline `0`, and
  its last batch of chain `1` settled at time `1`); commit value `fun _ b => b`.  The leg
  `⟨1, 2⟩` of `mixedFlow 0 1 2` missed its deadline and `⟨0, 1⟩` did not, so both sides of
  the equivalence take both values.
* A root that holds no late batch.  `demoSystem` with `demoRoot` and a backing for it
  (`AggregatesBefore` holds; batches `0, 1` settled at time `0`, the root was created at
  time `1` and holds exactly those).  The leg `⟨0, 0⟩` with commit value `1` and deadline
  `0` missed its deadline, and no batch inside the root meets the BEGIN branch's
  conditions.  So here the completeness half can be met only on the END branch. -/
def Properties.AcceptedGateIffMissedDeadlineWitness : Prop :=
  ∀ (h : Hash) (ze : UInt256),
    (Nonempty (RootBacking h ze timeOneRoot)
      ∧ Wf (mixedSystem 1)
      ∧ Contracts.InteropOperational.AggregatesBefore (mixedSystem 1) timeOneRoot
      ∧ (mixedFlow 0 1 2).deadline < timeOneRoot.created
      ∧ legValue (fun _ b => b) (mixedFlow 0 1 2) ⟨1, 2⟩ ≠ 0
      ∧ LegMissedDeadline (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨1, 2⟩
      ∧ legValue (fun _ b => b) (mixedFlow 0 1 2) ⟨0, 1⟩ ≠ 0
      ∧ ¬ LegMissedDeadline (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨0, 1⟩
      ∧ (mixedFlow 0 1 2).deadline < (mixedSystem 1).time 1 (timeOneRoot.upTo 1))
    ∧ (Nonempty (RootBacking h ze demoRoot)
      ∧ Wf demoSystem
      ∧ Contracts.InteropOperational.AggregatesBefore demoSystem demoRoot
      ∧ (⟨0, [⟨0, 0⟩], 0⟩ : Flow).deadline < demoRoot.created
      ∧ legValue (fun _ _ => 1) ⟨0, [⟨0, 0⟩], 0⟩ ⟨0, 0⟩ ≠ 0
      ∧ LegMissedDeadline (fun _ _ => 1) demoSystem ⟨0, [⟨0, 0⟩], 0⟩ ⟨0, 0⟩
      ∧ ∀ N, N ≤ demoRoot.upTo 0 →
          ¬ BeginBranchVerified demoSystem demoRoot 0 (⟨0, [⟨0, 0⟩], 0⟩ : Flow).deadline N)

/-- **THE END BRANCH IS LIVE: THE HALTED-CHAIN PATH.**  On a well-formed history, with an
imported root `R` created after the deadline whose last batch of the leg's chain settled
by the deadline, a leg with nonzero commit value absent from that batch's tree passes the
gate as the contract runs it on the END branch, at a batch inside `R` (its last one): the
honest IMT absence proof of that batch's tree, with the honest batch-leaf path of the
root's last batch for `_verifyLastBatchInRoot`.  Neither proof carries a located break.
No aggregation premise: this is the END case of
`Properties.AcceptedGateCompleteFromAnyPostDeadlineRoot`, which takes none. -/
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

/-- **ITS PREMISES ARE SATISFIABLE, WITH THE ZERO CHECK EXERCISED.**  For every hash and
chain-tree padding constant: `demoSystem` (batches `0, 1` at time `0`, the tree stays
`setup`) is well formed, and `demoRoot` (created at time `1`, last batch `1`) has a
backing in which the path of the root's last batch goes left at some level below the
tree's height, so `_verifyLastBatchInRoot` has a sibling to compare with that level's
empty-subtree hash.  The leg `⟨0, 0⟩` with commit value `1` and deadline `0` has the
root's last batch on time and is absent from it. -/
def Properties.EndBranchAcceptsHonestProofsWitness : Prop :=
  ∀ (h : Hash) (ze : UInt256),
    ∃ B : RootBacking h ze demoRoot,
      (∃ l < B.height 0, (demoRoot.upTo 0 / 2 ^ l) % 2 = 0)
        ∧ Wf demoSystem
        ∧ (⟨0, [⟨0, 0⟩], 0⟩ : Flow).deadline < demoRoot.created
        ∧ demoSystem.time 0 (demoRoot.upTo 0) ≤ (⟨0, [⟨0, 0⟩], 0⟩ : Flow).deadline
        ∧ legValue (fun _ _ => 1) ⟨0, [⟨0, 0⟩], 0⟩ ⟨0, 0⟩ ≠ 0
        ∧ legValue (fun _ _ => 1) ⟨0, [⟨0, 0⟩], 0⟩ ⟨0, 0⟩
            ∉ keys (toAbs (demoSystem.tree 0 (demoRoot.upTo 0)))

/-- **IN THE FIXED-HISTORY MODEL, THE REFUND STEPS OF A STRANDED FLOW'S COMMITTED LEGS ARE
ENABLED.**  Let a leg `m` of a checked flow `F` have a nonzero commit value, miss its
deadline, and sit on a chain with a batch after the deadline.  Then at every manager
state `Ms`, every leg `leg` of `F` whose obligation is `Committed` can be moved on.  There
is an `authorizeRefund` call for exactly `(F, leg)` with missing leg `m` that passes
every check of the model (`AuthCall.Verified`) on an absence proof carrying no located
break.  A run from `Ms` whose log is that one call reaches a state `Ms₁` in which the
obligation is `Revertable` (the `authorizeRefund` step), and a run from `Ms₁` with no
further call reaches a state `Ms₂` in which it is `Reverted` (the `claimRefund` step).
Both states agree with `Ms` on every other obligation.

This is what `Properties.TimeoutProofRefundsCommittedLeg` claimed ("the refund branch is
reachable") with its `RefundAuthorized` premise discharged.  The refunded leg need not be
the stranded one: `authorizeRefund` refunds the flow's other legs on the strength of one
missing leg, and the witness refunds a leg that WAS committed on time.  `Ms` need not be
reachable; when it is, the two steps extend the run that reached it (`reachLog_trans`).

**What this does not say.**  It is enabledness of two steps of `ReachLog`'s model, and
that model admits more refunds than the contract, so this is not a liveness claim about
the deployed contracts.

* The gate is the loose one, over a fixed history given up front.  The call may cite any
  batch of that history and needs no root.  `authorizeRefund` needs an imported root
  created after the deadline and a batch inside it, so it cannot cite a batch that has not
  settled or that no imported root holds.
* `claimRefund` is its leg-state guard.  The recovery calls it makes can revert and leave
  the leg `Revertable`: under a paused source vault
  (`Contracts.InteropPause.Properties.PausedVaultKeepsLegRevertable`), or for good
  (`Contracts.AssetRouter.AtomicRecovery.Properties.LegNeverRefunded`).
* `_checkFlowId` is the hash comparison alone (`FlowIdChecked`); its sortedness and length
  checks, and the settlement-layer check, are not modelled.
* A step marks one leg, so "every other obligation" is unchanged.  The contract's call
  marks every `Committed` leg of the flow in the manager that runs it (`Specs/Operational.lean`,
  model boundaries).
* There is no prover access here: the proof exists.  Presenting it needs the chain's data
  (`Properties.MissedDeadlineRefundableByHonestProof` states that for the gate).
* Nobody is assumed to send either call.

The statement against a recorded root, citing settled batches only and using the END
branch for a chain that halted, is
`Contracts.InteropOperational.Properties.OpTimedOutLegIsRefundable`.  It is enabledness
too, and its model omits the same reject-only checks. -/
def Properties.StrandedFlowCommittedLegRefundable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow), FlowIdChecked fh F → ∀ m ∈ F.legs, legValue cv F m ≠ 0 →
    (∃ N, F.deadline < S.time m.chain N) → LegMissedDeadline cv S F m →
    ∀ (Ms : Managers), ∀ leg ∈ F.legs, stateOf Ms (obligationOf F leg) = .Committed →
      ∃ (a : AuthCall) (Ms₁ Ms₂ : Managers),
        a.flow = F ∧ a.leg = leg ∧ a.missing = m ∧ a.Verified h z0 hl cv fh S
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline m.chain a.batch a.proof
        ∧ ReachLog h z0 hl cv fh S Ms Ms₁ [a]
        ∧ stateOf Ms₁ (obligationOf F leg) = .Revertable
        ∧ (∀ o, o ≠ obligationOf F leg → stateOf Ms₁ o = stateOf Ms o)
        ∧ ReachLog h z0 hl cv fh S Ms₁ Ms₂ []
        ∧ stateOf Ms₂ (obligationOf F leg) = .Reverted
        ∧ ∀ o, o ≠ obligationOf F leg → stateOf Ms₂ o = stateOf Ms o

/-- **ITS PREMISES ARE SATISFIABLE AT A REACHABLE STATE, AND THE REFUNDED LEG WAS DELIVERED
ON TIME.**  For every hash: in `mixedSystem 1` with commit value `fun _ b => b`, the flow
`mixedFlow 0 1 2` passes `_checkFlowId` under its honest flow hash; its leg `⟨1, 2⟩` missed
its deadline on a chain that moved past it; the one-step run appending leg `⟨0, 1⟩` on
chain `0` reaches, from fresh managers, a state in which that leg's obligation is
`Committed`; and `⟨0, 1⟩` did NOT miss its deadline.  So the theorem refunds a committed
sibling of a stranded leg. -/
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

/-! ## 2. Refunds at run level -/

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

/-- **COROLLARY: A REFUND UNDER A CHECKED FLOW'S ID THAT NO LOGGED CALL MADE FOR THAT FLOW
WAS MADE BY A LOGGED CALL WHOSE FLOW CLASHES WITH IT.**  If an obligation carrying a
checked flow `F`'s id is past `Committed` in a reachable logged state, and no logged call
that marked it presented `F` itself, then a logged call marked it, that call passed every
check of `authorizeRefund`, and its flow and `F` collide under `fh` on exactly their own
`(legs, deadline)` preimages.

This is `Properties.RefundNeedsLoggedAuthorize` composed with
`Properties.CrossFlowIdClashIsPinnedCollision`, and it adds nothing to them.  Given that
both flows pass `_checkFlowId` with one id, the clash conjunct is equivalent to the
marking call's flow differing from `F`, which is the fourth premise.
`Properties.RefundImpliesOwnFlowTimeoutOrLoggedClash` is the same fact in disjunctive
form.

Only the marking call's flow is a flow of the run.  `F` is any checked flow claiming the
obligation's id, and `leg` need not be one of its legs: `append` takes the id as an
opaque word, so a `ReachLog` run does not record which flow an obligation was appended
for. -/
def Properties.CrossFlowRefundYieldsLoggedPinnedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (F : Flow) (leg : FlowLeg), FlowIdChecked fh F →
    ∀ (Ms : Managers) (log : List AuthCall), ReachLog h z0 hl cv fh S emptyManagers Ms log →
    Refunded Ms (obligationOf F leg) →
    (∀ a ∈ log, obligationOf a.flow a.leg = obligationOf F leg → a.flow ≠ F) →
      ∃ a ∈ log, a.Verified h z0 hl cv fh S ∧ obligationOf a.flow a.leg = obligationOf F leg
        ∧ FlowIdClash fh F a.flow

/-- **ITS PREMISES ARE SATISFIABLE BY A REFUND THAT CROSSES FLOWS: A DELIVERED LEG IS
REFUNDED ON ANOTHER FLOW'S TIMEOUT.**  For every hash, in `mixedSystem 1` under the
constant commit value `1` and the constant flow hash `fun _ _ => 0`, which lets the
truncated flow `subsetFlow 0 1` and the full flow `mixedFlow 0 1 2` both pass
`_checkFlowId` with id `0`.

* `F = subsetFlow 0 1` and its leg `⟨0, 1⟩` meet the theorem's premises on a run with the
  single logged call `a`.
* That leg was delivered: `F` executes it on honest gate evidence, with no `GateBreak`.
* `a` presents the full flow, marks the delivered leg `⟨0, 1⟩`, and proves the absence of
  the full flow's other leg `⟨1, 2⟩`, which really missed its deadline; `a`'s absence
  proof carries no break.

So the obligation of a leg that executed is refunded by the run's one logged call,
because a second flow claims the same id.  The system, commit value, executed flow,
evidence and leg are the ones
`Properties.ExecutedObligationLiveAndUnmarkableUnderSealedHash` is proved with; only the
flow hash differs. -/
def Properties.CrossFlowRefundYieldsLoggedPinnedClashWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (Ms : Managers) (a : AuthCall),
      FlowIdChecked (fun _ _ => 0) (subsetFlow 0 1)
        ∧ ReachLog h z0 hl (fun _ _ => 1) (fun _ _ => 0) (mixedSystem 1) emptyManagers Ms [a]
        ∧ Refunded Ms (obligationOf (subsetFlow 0 1) ⟨0, 1⟩)
        ∧ (∀ c ∈ [a], obligationOf c.flow c.leg = obligationOf (subsetFlow 0 1) ⟨0, 1⟩ →
            c.flow ≠ subsetFlow 0 1)
        ∧ Wf (mixedSystem 1)
        ∧ ExecutedViaBy h z0 hl (fun _ _ => 1) (fun _ _ => 0) (mixedSystem 1) (subsetFlow 0 1)
            (fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1)) ⟨0, 1⟩
        ∧ ¬ GateBreak h z0 hl (mixedSystem 1) (subsetFlow 0 1)
            (fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1))
        ∧ a.flow = mixedFlow 0 1 2 ∧ a.leg = ⟨0, 1⟩ ∧ a.missing = ⟨1, 2⟩
        ∧ LegMissedDeadline (fun _ _ => 1) (mixedSystem 1) (mixedFlow 0 1 2) ⟨1, 2⟩
        ∧ ¬ AbsenceBreak h z0 hl (mixedSystem 1) (mixedFlow 0 1 2).deadline 1 a.batch a.proof

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

/-- **UNDER THE SEALED HASH PAIR THE EXECUTED OBLIGATION IS LIVE, AND NO VERIFIED CALL CAN
MARK IT.**  The run of `Properties.ExecutedObligationNeverRefundedOrBreakAppendedWitness`
under the sealed pair `sealedNodeHash`, `sealedLeafHash` (a toy pair, not a model of
keccak).  In addition to everything there: the executed flow passes `_checkFlowId`, its
leg is one of its legs and the obligation's guard is open, yet no timeout evidence
`(N, p)` passes the loose gate for that leg; and no `authorizeRefund` call of ANY flow
that passes every check marks the executed obligation.  So the obligation is live and
stays unrefunded.

Two checks do that together.  `_checkFlowId` under `lengthFlowHash` lets only one-leg
flows claim id `0`, so a call that marks the executed obligation must name the executed
leg itself as its missing leg; and the timeout gate, under the sealed pair, rejects every
absence proof for that leg.  The timeout gate alone is not enough:
`Properties.CrossFlowRefundYieldsLoggedPinnedClashWitness` keeps the system, commit value,
executed flow, evidence and leg this statement is proved with, changes the flow hash to
the constant `0`, and there a logged call of a two-leg flow marks the executed obligation.
That witness holds for every hash, so also for the sealed pair, under which the gate
rejects the executed leg all the same (the seventh conjunct below does not mention the
flow hash). -/
def Properties.ExecutedObligationLiveAndUnmarkableUnderSealedHash : Prop :=
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
