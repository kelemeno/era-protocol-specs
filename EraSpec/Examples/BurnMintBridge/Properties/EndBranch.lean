import EraSpec.Examples.BurnMintBridge.Specs.EndBranch

/-!
# Properties: the END timeout branch composed into the reference bridge

Statements about `../Specs/EndBranch.lean`; proofs in `../Proofs/EndBranch.lean`.

## What is claimed

* **§1, over the adapter's history.**  The abstract END form is already an instance of the
  adapter's `Missing` (`MissingEndImpliesMissing`, no premise), so composing it changes no
  run (`EvidenceEitherRunsAreAdapterRuns`).  Both branches still give "never finalized"
  through `TimeoutSoundness.timeout_implies_never_finalized` (`MissingEitherNeverFinalized`),
  and the re-proved exclusivity, evidence soundness, no-double-payment and value
  conservation cover both branches.
* **§2, the gate as the contract runs it.**  SOUNDNESS (`AtomicInteropProof.sol:84-87`): an
  accepted timeout means the leg was never committed in time — the BEGIN branch from
  `TimeoutSoundness.begin_absence_implies_never_finalized` with no settlement-layer premise,
  the END branch from `LastBatchInRoot.end_branch_from_onchain_check` under
  `RootAggregates`.  The as-run gate refines the adapter's `Missing`, so the bridge never
  double-pays, conserves value, and never refunds a transfer whose prerequisites were on
  time (`CheckedExecutionRemainsPossible`).  COMPLETENESS (:89-94): a leg never committed in
  time has an accepted timeout against EVERY root created after the deadline
  (`TimeoutComplete`, no aggregation premise), which needs the END branch
  (`BeginOnlyIncomplete`, `HaltedChainNeedsEndBranch`); in the halted world the adapter's
  own `Missing` cites only batches outside every imported root
  (`HaltedAdapterMissingCitesUnimportedBatch`).  `RootAggregates` and the last-batch check
  are each load-bearing (`StaleRootDoublePays`, `UncheckedEndDoublePays`).
* **§3, hash level.**  With the batch-leaf path checked as `LastBatchAccepted`, an accepted
  END submission for a leg committed on time carries a break located on that submission
  (`AcceptedEndOnTimeLocatesBreak`); the bridge never double-pays and conserves value, unless
  the recorded transfer's END submission carries such a break.  The break is false on an
  honest submission (`PinnedBridgeRefundWitness`) and fires on a forged one
  (`ForgedLastBatchLocatesBreak`).

**Correction (LastBatchInRootOffset).**  §2 and §3 use one number as a chain-tree leaf position
and as a batch number.  `EndVia`'s `B` is the position in `RightEmpty` and the batch in
`settledAt` and `tree`; an `EndSubmission`'s `batch` is the index in `LastBatchAccepted` and the
batch of `EndAcceptedBy`'s clock and gap witness; and a root holds the chain's batches
`0 … upTo` (`Roots`, `Contracts.Timeout.RootBacking`).  The END soundness above takes the same
reading from `LastBatchInRoot.end_branch_from_onchain_check`.  At `c67894b9` every
atomic-interop source chain's first pushed batch on L1 is 0, so the reading is exact there while
every later batch is pushed into the chain tree (`PROTO-CONTIGUOUS-PUSH`, ASSUMPTIONS.md); the
realistic break is a non-contiguous push after a Gateway round trip.
`AttackVectors.LastBatchInRootOffset.EndBranchFromOnchainCheckOffset` keeps position and number
apart; it is not composed into the bridge.

**Correction (LastLeafFaithful).**  §3's `LastBatchAccepted` takes the batch-leaf walk's length
to be the chain tree's height and the batch to be an occupied leaf.  The deployed verifier
checks neither: the path length and mask are the prover's, and `Merkle.sol` accepts a padded
index.  A wrong-length or padded-index submission that passes every check the contract performs
is no `EndAcceptedBy` submission, so the §3 results say nothing about a refund on one.  The
last-leaf result over every accepted submission is
`MerkleSpec.LastLeafFaithful.AcceptedLastLeafAnyLengthOrBreak`, with a wrong-length
(`HeightBreak`) and a padded-entry case added.  `WrongLengthLastLeafAccepted` and
`PaddedIndexLastLeafAccepted` show both cases passing those checks; there the claimed leaf hash
is free, and on chain each witness needs a cross-length keccak preimage.  None of this is
composed into the bridge.  At the index level, §2's `EndVia` likewise takes an occupied batch
(`B < upTo + 1`) and a walk depth the tree fits in.

**Correction (StaleSnapshotFaithful).**  §2 and §3 take the non-inclusion proof to open a leaf of
the snapshot (`GapWitness`).  At `c67894b9` the deployed check also accepts the padding sentinel
`{0,0,0}` at an empty slot, and the timeout gate passes on it for a leg committed on time
(`Contracts.Timeout.PaddingTimeoutLocatesAbsenceBreak`).  The §2 and §3 results say nothing
about a refund on such a proof, and §3's breaks, located on the END submission, do not locate
it; see the module docstring of `../Specs/EndBranch.lean`.

## Premises, and where each is shown satisfiable

* `History.Valid` (guarded IMT evolution from genesis, monotone settlement times):
  `EndBranchRefundWitness`, `OnTimeLegExecutesWitness`, `HaltedChainNeedsEndBranch`.
* `RootAggregates` for every imported root: `HaltedChainNeedsEndBranch`,
  `CheckedExecutionWitness`, `PinnedBridgeRefundWitness`, `ForgedLastBatchLocatesBreak`.
* An accepted timeout on the BEGIN branch as run: `BeginBranchRefundWitness`.  In every world
  where it holds, the BEGIN branch alone also refunds the transfer that timeout belongs to
  (`BeginBranchRefundWitnessRecordPinFree`).  A refund on the BEGIN branch with no END-branch
  timeout available for that transfer, so that the BEGIN branch is needed:
  `BeginBranchRefundWitnessPinned` (`Properties/EndBranchStrong.lean`).
* An accepted timeout on the END branch: `HaltedChainNeedsEndBranch` (index level),
  `PinnedBridgeRefundWitness` (hash level; with the refund on that submission:
  `PinnedBridgeRefundWitnessLinked`); on the forged path with the leg on time:
  `ForgedLastBatchLocatesBreak`.
* A prepared transfer with every prerequisite on time (`CheckedExecutionRemainsPossible`):
  `CheckedExecutionWitness`, which a transfer with no prerequisite meets vacuously
  (`CheckedExecutionWitnessGap`); with at least one prerequisite, each with a nonzero commit
  value: `CheckedExecutionWitnessPinned` (`Properties/EndBranchStrong.lean`).
* A never-committed leg, a root after the deadline and a recorded unrefunded transfer
  (`TimeoutComplete`, `TimedOutTransferRefundEnabled`): `HaltedChainNeedsEndBranch` (its END
  timeout carries the root's post-deadline creation; its burned state records the transfer).

`EndBranchRefundWitness`, `OnTimeLegExecutesWitness` and `BeginBranchRefundWitness` do not
say that the run resolves their own transfer `i`, and neither does the last conjunct of
`HaltedChainNeedsEndBranch`.  But in every world where one of the first three holds, the run
that prepares and resolves `i` itself meets it too, so pinning the record adds nothing world
by world (`Properties/EndBranchStrong.lean`).  What the pinned forms there add per world is at
least one prerequisite with nonzero commit values for the on-time witness, and for the BEGIN
witness the exclusion of an END-branch timeout on `i`'s legs, which is what pins its branch.
The stronger forms of `CheckedExecutionWitness` and `PinnedBridgeRefundWitness` are there too,
with gaps that show what their bodies admit.

No hash-injectivity premise appears anywhere.  `PinnedBridgeRefundWitness` and
`ForgedLastBatchLocatesBreak` use the colliding toy hash `demoHash`.
-/

namespace Applications.BurnMintBridge.EndBranch

open IMTAbstract Properties.PreparedBridge

/-! ## 1. The END branch over the adapter's history -/

/-- **THE ABSTRACT END FORM IS ALREADY A SUCCESSOR-PINNED `Missing`.**  No premise: the
batch after `B` settles no earlier than `T`, which is after the deadline, so batch `B`'s
END tree is the BEGIN tree of a late batch.  Composing `MissingEnd` into the adapter admits
no new refund; the END branch's content appears only once evidence is restricted to batches
inside imported roots (§2). -/
def Properties.MissingEndImpliesMissing : Prop :=
  ∀ (H : History) (l : Leg), MissingEnd H l → Missing H l

/-- **THE GATE'S FORM IS THE ABSENCE FORM.**  On a valid history, `MissingEnd` (a gap
witness at batch `B`, what the non-inclusion proof opens) holds iff the END disjunct of
`TimeoutSoundness.timeout_implies_never_finalized` does with `v ∉ endSet B`. -/
def Properties.MissingEndIffAbsence : Prop :=
  ∀ (H : History), H.Valid → ∀ (l : Leg),
    MissingEnd H l ↔ ∃ (B : ℕ) (T : UInt256),
      H.settledAt l.sourceChain B ≤ l.deadline ∧ l.deadline < T ∧
        (∀ n, B < n → T ≤ H.settledAt l.sourceChain n) ∧
        l.commitValue ∉ keys (H.tree l.sourceChain B)

/-- **EITHER BRANCH MEANS NEVER FINALIZED** — `TimeoutSoundness.timeout_implies_never_finalized`
on the leg's chain: the commit value is absent from every snapshot settled by the deadline. -/
def Properties.MissingEitherNeverFinalized : Prop :=
  ∀ (H : History), H.Valid → ∀ (l : Leg), MissingEither H l →
    ∀ n, H.settledAt l.sourceChain n ≤ l.deadline →
      l.commitValue ∉ keys (H.tree l.sourceChain n)

/-- `onTime_excludes_missing` for both branches. -/
def Properties.OnTimeExcludesMissingEither : Prop :=
  ∀ (H : History), H.Valid → ∀ (l : Leg), OnTime H l → ¬ MissingEither H l

/-- `evidence_sound` for both branches. -/
def Properties.EvidenceEitherSound : Prop :=
  ∀ (H : History), H.Valid → ∀ (flow : Transfer → List Leg), (evidenceEither H flow).Sound

/-- `prepared_bridge_no_double_payment` for both branches. -/
def Properties.PreparedBridgeNoDoublePaymentEither : Prop :=
  ∀ (H : History), H.Valid → ∀ (flow : Transfer → List Leg) (source destination : ℕ)
    (s : State), Run (evidenceEither H flow) (initial source destination) s →
      ¬ (s.delivered = true ∧ s.refunded = true)

/-- `prepared_bridge_value_conserved` for both branches. -/
def Properties.PreparedBridgeValueConservedEither : Prop :=
  ∀ (H : History), H.Valid → ∀ (flow : Transfer → List Leg) (source destination : ℕ)
    (s : State), Run (evidenceEither H flow) (initial source destination) s →
      accounted s = source + destination

/-- Weakening evidence only adds runs. -/
def Properties.RunMonotone : Prop :=
  ∀ (E E' : Evidence), (∀ i, E.finalize i → E'.finalize i) →
    (∀ i, E.recover i → E'.recover i) → ∀ (s t : State), Run E s t → Run E' s t

/-- **COMPOSING THE ABSTRACT END FORM CHANGES NO RUN.**  The runs driven by `evidenceEither`
are exactly the adapter's runs, on every history. -/
def Properties.EvidenceEitherRunsAreAdapterRuns : Prop :=
  ∀ (H : History) (flow : Transfer → List Leg) (s t : State),
    Run (evidenceEither H flow) s t ↔ Run (evidence H flow) s t

/-- **§1 PREMISES SATISFIABLE, REFUND ON THE END FORM.**  A valid history, a transfer `i` with a
leg that has an END-form timeout, and a run of the bridge from `initial i.amount 0` that ends
refunded with source balance `i.amount`.  The statement does not say that the refunded record
is `i`: a run that prepares and refunds another transfer, of amount at most `i.amount`,
satisfies it (`Properties.EndBranchRefundWitnessGap`).  But in every world where it holds, the
run that prepares and refunds `i` itself does too.  So the form pinned to `i`, on a run of the
END-form evidence, `Properties.EndBranchRefundWitnessPinned`
(`Properties/EndBranchStrong.lean`), holds in the same worlds
(`Properties.EndBranchRefundWitnessRecordPinFree`).  In §1 that evidence does not exclude the
BEGIN form (`MissingEndImpliesMissing`). -/
def Properties.EndBranchRefundWitness : Prop :=
  ∃ (H : History) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    H.Valid ∧ (∃ l ∈ flow i, MissingEnd H l) ∧
      Run (evidenceEither H flow) (initial i.amount 0) s ∧ s.refunded = true ∧
      s.sourceBalance = i.amount

/-- **§1 PREMISES SATISFIABLE, EXECUTION ON TIME.**  A valid history, a transfer `i` all of whose
prerequisites are on time, and a run of the bridge from `initial i.amount 0` that ends delivered
with destination balance `i.amount`.  The statement does not say that the executed record is
`i`, and it holds vacuously for a transfer with no prerequisite.  Its body is met by a run that
executes another transfer, on a history where no nonzero value is ever on time
(`Properties.OnTimeLegExecutesWitnessGap`).  A prerequisite with commit value `0`, the tree's
sentinel, which is in every snapshot of a valid history, is on time as soon as some batch of its
chain settled by its deadline, with nothing committed, so the on-time premise alone shows no
commitment either.  The form pinned to `i`, with at least one prerequisite and nonzero commit
values, is `Properties.OnTimeLegExecutesWitnessPinned` (`Properties/EndBranchStrong.lean`); per
world its record pin adds nothing (`Properties.OnTimeLegExecutesWitnessRecordPinFree`). -/
def Properties.OnTimeLegExecutesWitness : Prop :=
  ∃ (H : History) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    H.Valid ∧ (∀ l ∈ flow i, OnTime H l) ∧
      Run (evidenceEither H flow) (initial i.amount 0) s ∧ s.delivered = true ∧
      s.destinationBalance = i.amount

/-! ## 2. The timeout gate as the contract runs it -/

/-- **THE ZERO-CASCADE CHECK IS EXACTLY "LAST IN ROOT".**  `EndVia` (the index-level
`RightEmpty` check) accepts precisely the root's last batch: `LastBatchInRoot.last_of_rightEmpty`
one way, `rightEmpty_of_last` (an honest prover can always pass) the other. -/
def Properties.EndCheckIffLastInRoot : Prop :=
  ∀ (H : History) (R : Contracts.Timeout.SlRoot) (l : Leg), EndVia H R l ↔ EndLastVia H R l

/-- **A BEGIN-BRANCH TIMEOUT MEANS NEVER FINALIZED**, with no settlement-layer premise
(`TimeoutSoundness.begin_absence_implies_never_finalized`).

**Correction (StaleSnapshotFaithful).**  The absence witness is a genuine leaf (`GapWitness`);
the deployed check accepts more (module docstring of `../Specs/EndBranch.lean`). -/
def Properties.BeginViaNeverFinalized : Prop :=
  ∀ (H : History) (R : Contracts.Timeout.SlRoot), H.Valid → ∀ (l : Leg), BeginVia H R l →
    ∀ n, H.settledAt l.sourceChain n ≤ l.deadline →
      l.commitValue ∉ keys (H.tree l.sourceChain n)

/-- **AN END-BRANCH TIMEOUT MEANS NEVER FINALIZED**, from the on-chain check
(`LastBatchInRoot.end_branch_from_onchain_check`), when the root aggregates every batch
settled before it.

**Correction (LastBatchInRootOffset).**  `EndVia`'s `B` is both the chain-tree leaf position and
the batch number, as in `end_branch_from_onchain_check`: exact at `c67894b9` for atomic-interop
source chains while pushes are contiguous (`PROTO-CONTIGUOUS-PUSH`); see the module docstring.

**Correction (StaleSnapshotFaithful).**  The absence witness is a genuine leaf (`GapWitness`);
the deployed check accepts more (module docstring of `../Specs/EndBranch.lean`). -/
def Properties.EndViaNeverFinalized : Prop :=
  ∀ (H : History) (R : Contracts.Timeout.SlRoot), H.Valid → RootAggregates H R →
    ∀ (l : Leg), EndVia H R l → ∀ n, H.settledAt l.sourceChain n ≤ l.deadline →
      l.commitValue ∉ keys (H.tree l.sourceChain n)

/-- **THE GATE AS RUN REFINES THE ADAPTER.**  An accepted timeout against an aggregating
root is an instance of `Missing`, so every `ProtocolComposition` result applies to the path
the contract takes.

**Correction (StaleSnapshotFaithful).**  With a genuine-leaf absence witness (`GapWitness`); the
deployed check accepts more (module docstring of `../Specs/EndBranch.lean`). -/
def Properties.TimeoutViaImpliesMissing : Prop :=
  ∀ (H : History) (R : Contracts.Timeout.SlRoot), H.Valid → RootAggregates H R →
    ∀ (l : Leg), TimeoutVia H R l → Missing H l

/-- The as-run evidence is sound when every imported root aggregates.

**Correction (StaleSnapshotFaithful).**  "As run" with a genuine-leaf absence witness; see the
module docstring of `../Specs/EndBranch.lean`. -/
def Properties.CheckedEvidenceSound : Prop :=
  ∀ (H : History) (roots : Roots), H.Valid → (∀ k, RootAggregates H (roots k)) →
    ∀ (flow : Transfer → List Leg), (checkedEvidence H roots flow).Sound

/-- **NO DOUBLE PAYMENT, BOTH BRANCHES AS RUN.**

**Correction (StaleSnapshotFaithful).**  "As run" with a genuine-leaf absence witness; see the
module docstring of `../Specs/EndBranch.lean`. -/
def Properties.CheckedBridgeNoDoublePayment : Prop :=
  ∀ (H : History) (roots : Roots), H.Valid → (∀ k, RootAggregates H (roots k)) →
    ∀ (flow : Transfer → List Leg) (source destination : ℕ) (s : State),
      Run (checkedEvidence H roots flow) (initial source destination) s →
        ¬ (s.delivered = true ∧ s.refunded = true)

/-- **VALUE CONSERVED, BOTH BRANCHES AS RUN.**

**Correction (StaleSnapshotFaithful).**  "As run" with a genuine-leaf absence witness; see the
module docstring of `../Specs/EndBranch.lean`. -/
def Properties.CheckedBridgeValueConserved : Prop :=
  ∀ (H : History) (roots : Roots), H.Valid → (∀ k, RootAggregates H (roots k)) →
    ∀ (flow : Transfer → List Leg) (source destination : ℕ) (s : State),
      Run (checkedEvidence H roots flow) (initial source destination) s →
        accounted s = source + destination

/-- **COMPLETENESS** (`AtomicInteropProof.sol:89-94`).  A leg whose nonzero commit value is
absent from every snapshot settled by the deadline has an accepted timeout against EVERY
root created after the deadline: the first late batch inside the root on the BEGIN branch,
or else the root's last batch, which is in time, on the END branch.  No aggregation
premise. -/
def Properties.TimeoutComplete : Prop :=
  ∀ (H : History), H.Valid → ∀ (l : Leg), l.commitValue ≠ 0 →
    (∀ n, H.settledAt l.sourceChain n ≤ l.deadline →
      l.commitValue ∉ keys (H.tree l.sourceChain n)) →
    ∀ (R : Contracts.Timeout.SlRoot), l.deadline.val < R.created → TimeoutVia H R l

/-- **§2 PREMISES SATISFIABLE ON THE BEGIN BRANCH.**  A valid history whose imported roots
aggregate, a transfer `i` with a leg that has an accepted BEGIN-branch timeout (a late batch
inside the root), and a run of the bridge from `initial i.amount 0` that ends refunded with
source balance `i.amount`.  The statement pins neither the refunded record nor the branch that
authorized the refund.  Its body is met by a run that refunds another transfer, none of whose
legs has a BEGIN-branch timeout, on the END branch alone
(`Properties.BeginBranchRefundWitnessGap`).  But in every world where it holds, `i` itself can
also be refunded on the BEGIN branch alone (`Properties.BeginBranchRefundWitnessRecordPinFree`).
What the statement does not exclude is an END-branch timeout on a leg of `i`: on another leg,
even against the same root (`Properties.BeginBranchRefundWitnessSingleRootGap`, with one imported
root); on the leg with the BEGIN-branch timeout, against another imported root
(`Properties.BeginBranchRefundWitnessBranchGap`).  So it does not show that the BEGIN branch is
needed.  The form that excludes it, pinned to `i` and to the BEGIN branch, is
`Properties.BeginBranchRefundWitnessPinned` (`Properties/EndBranchStrong.lean`). -/
def Properties.BeginBranchRefundWitness : Prop :=
  ∃ (H : History) (roots : Roots) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧
      (∃ l ∈ flow i, ∃ k, BeginVia H (roots k) l) ∧
      Run (checkedEvidence H roots flow) (initial i.amount 0) s ∧ s.refunded = true ∧
      s.sourceBalance = i.amount

/-- **THE BEGIN BRANCH ALONE IS INCOMPLETE.**  A valid history and an aggregating root
created after the deadline, for a leg never committed in time, with no BEGIN-branch timeout:
the root holds only in-time batches of the chain, as for a chain that halts. -/
def Properties.BeginOnlyIncomplete : Prop :=
  ∃ (H : History) (R : Contracts.Timeout.SlRoot) (l : Leg),
    H.Valid ∧ RootAggregates H R ∧ l.commitValue ≠ 0 ∧
      (∀ n, H.settledAt l.sourceChain n ≤ l.deadline →
        l.commitValue ∉ keys (H.tree l.sourceChain n)) ∧
      l.deadline.val < R.created ∧ ¬ BeginVia H R l

/-- **A HALTED CHAIN NEEDS THE END BRANCH, AT THE BRIDGE.**  A valid history whose imported
roots all aggregate; every transfer's only prerequisite was never committed in time.  With the
BEGIN branch only, nothing is ever resolved and a prepared transfer stays in limbo forever.
With both branches, a run of the bridge ends refunded, with the source balance restored and
nothing in limbo.  The statement does not pin that run's record to `i`.  No transfer here has a
BEGIN-branch timeout, so the refund is on the END branch whichever transfer it resolves. -/
def Properties.HaltedChainNeedsEndBranch : Prop :=
  ∃ (H : History) (roots : Roots) (flow : Transfer → List Leg) (i : Transfer),
    H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧
      (∀ j, ∀ l ∈ flow j, l.commitValue ≠ 0 ∧
        ∀ n, H.settledAt l.sourceChain n ≤ l.deadline →
          l.commitValue ∉ keys (H.tree l.sourceChain n)) ∧
      (∀ j, ∀ l ∈ flow j, ∀ k, ¬ BeginVia H (roots k) l) ∧
      (∀ s, Run (beginOnlyEvidence H roots flow) (initial i.amount 0) s →
        s.delivered = false ∧ s.refunded = false) ∧
      (∀ s, Run (beginOnlyEvidence H roots flow) (burn (initial i.amount 0) i) s →
        limbo s = i.amount) ∧
      (∃ l ∈ flow i, ∃ k, EndVia H (roots k) l) ∧
      (∃ s, Run (checkedEvidence H roots flow) (initial i.amount 0) s ∧
        s.refunded = true ∧ s.sourceBalance = i.amount ∧ limbo s = 0)

/-- **WHY §1 CANNOT SEE THE HALT.**  In the same kind of world, the adapter's `Missing`
holds, but every late batch it can cite lies outside every imported root, so no on-chain
proof of it exists, and no BEGIN-branch timeout exists.  The refund the unrestricted history
admits is a model artifact; on chain only the END branch provides it. -/
def Properties.HaltedAdapterMissingCitesUnimportedBatch : Prop :=
  ∃ (H : History) (roots : Roots) (l : Leg),
    H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧ Missing H l ∧
      (∀ n, l.deadline < H.settledAt l.sourceChain (n + 1) →
        ∀ k, (roots k).upTo l.sourceChain < n + 1) ∧
      (∀ k, ¬ BeginVia H (roots k) l) ∧ (∃ k, EndVia H (roots k) l)

/-- **EXECUTION STAYS POSSIBLE** (`prepared_execution_remains_possible`, REVIEW.md P2) with
both branches as run: once a prepared transfer's prerequisites are all on time, no run
refunds it, and it is executed or still executable.

**Correction (StaleSnapshotFaithful).**  "As run" with a genuine-leaf absence witness; see the
module docstring of `../Specs/EndBranch.lean`. -/
def Properties.CheckedExecutionRemainsPossible : Prop :=
  ∀ (H : History) (roots : Roots), H.Valid → (∀ k, RootAggregates H (roots k)) →
    ∀ (flow : Transfer → List Leg) (s p t : State) (i : Transfer),
      Prepare s i p → (checkedEvidence H roots flow).finalize i →
        Run (checkedEvidence H roots flow) p t →
          t.refunded = false ∧
            (t.delivered = true
              ∨ ∃ u, AuthorizedExecution (checkedEvidence H roots flow) t i i u)

/-- **ITS PREMISES ARE SATISFIABLE.**  A valid history whose imported roots aggregate, a
prepared transfer all of whose prerequisites are on time, and its authorized execution.  The
statement does not ask the transfer to have a prerequisite; for one with none, the `finalize`
conjunct holds vacuously (`Properties.CheckedExecutionWitnessGap`).  A prerequisite with commit
value `0`, the tree's sentinel, is on time on a valid history as soon as some batch of its chain
settled by its deadline, with nothing committed, so a transfer whose prerequisites all have
commit value `0` meets the body on a history where no nonzero value is ever on time
(`Properties.CheckedExecutionWitnessZeroValueGap`).
The form with at least one prerequisite, each with a nonzero commit value, is
`Properties.CheckedExecutionWitnessPinned` (`Properties/EndBranchStrong.lean`). -/
def Properties.CheckedExecutionWitness : Prop :=
  ∃ (H : History) (roots : Roots) (flow : Transfer → List Leg) (s p : State) (i : Transfer),
    H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧ Prepare s i p ∧
      (checkedEvidence H roots flow).finalize i ∧
      ∃ u, AuthorizedExecution (checkedEvidence H roots flow) p i i u

/-- **REFUND LIVENESS.**  A recorded, unrefunded transfer one of whose prerequisites was
never committed in time can be refunded in one step, against any imported root created
after the deadline. -/
def Properties.TimedOutTransferRefundEnabled : Prop :=
  ∀ (H : History) (roots : Roots) (flow : Transfer → List Leg), H.Valid →
    ∀ (i : Transfer) (l : Leg), l ∈ flow i → l.commitValue ≠ 0 →
      (∀ n, H.settledAt l.sourceChain n ≤ l.deadline →
        l.commitValue ∉ keys (H.tree l.sourceChain n)) →
      ∀ k, l.deadline.val < (roots k).created →
      ∀ (s : State), s.record = some i → s.refunded = false →
        ∃ t, Step (checkedEvidence H roots flow) s t ∧ t.refunded = true ∧
          t.sourceBalance = s.sourceBalance + i.amount

/-- **A STALE ROOT DOUBLE-PAYS** (`StaleRootRefundsDeliveredLeg` at the bridge).  A valid
history in which the leg is committed in time and its finalization evidence sits inside an
imported root; one imported root omits an already-settled batch.  The END branch, with the
last-batch check passing, then refunds a transfer that was also executed: two units for one. -/
def Properties.StaleRootDoublePays : Prop :=
  ∃ (H : History) (roots : Roots) (flow : Transfer → List Leg) (s : State),
    H.Valid ∧ ¬ (∀ k, RootAggregates H (roots k)) ∧
      (∀ j, ∀ l ∈ flow j, ∃ k, OnTimeIn H (roots k) l) ∧
      Run (checkedEvidence H roots flow) (initial 1 0) s ∧
      s.delivered = true ∧ s.refunded = true ∧ accounted s = 2

/-- **THE LAST-BATCH CHECK IS LOAD-BEARING.**  Every imported root aggregates, the leg is
committed in time inside an imported root, and an END branch that accepts any in-time batch
inside the root double-pays: batch `0` is in time and lacks the leg, but it is not the last. -/
def Properties.UncheckedEndDoublePays : Prop :=
  ∃ (H : History) (roots : Roots) (flow : Transfer → List Leg) (s : State),
    H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧
      (∀ j, ∀ l ∈ flow j, ∃ k, OnTimeIn H (roots k) l) ∧
      Run (uncheckedEvidence H roots flow) (initial 1 0) s ∧
      s.delivered = true ∧ s.refunded = true ∧ accounted s = 2

/-! ## 3. The END branch with the hash-level last-batch proof -/

/-- **AN ACCEPTED END SUBMISSION FOR A LEG COMMITTED ON TIME IS A LOCATED BREAK.**  No hash
premise.  Under `RootAggregates`, if `_verifyLastBatchInRoot` (as `LastBatchAccepted`) and the
non-inclusion proof both pass for a leg that was committed on time, the chain tree carries a
`PinnedBreak` right after the submitted batch or the submitted path a `PathCollision`.

**Correction (LastLeafFaithful).**  `LastBatchAccepted` takes the walk's length to be the chain
tree's height and the batch to be an occupied leaf, which the deployed verifier does not check;
see the module docstring.

**Correction (LastBatchInRootOffset).**  The submission's `batch` is both the leaf position and
the batch number; see the module docstring.

**Correction (StaleSnapshotFaithful).**  The break list is over the model's genuine-leaf absence
witness (`GapWitness`).  With the deployed check, an END submission on a padding-forged absence
proof and the honest batch-leaf path for the root's last batch can pass for a leg committed on
time and carries neither break; see the module docstring of `../Specs/EndBranch.lean`. -/
def Properties.AcceptedEndOnTimeLocatesBreak : Prop :=
  ∀ (h : MerkleSpec.Hash) (ze : UInt256) (H : History) (roots : Roots)
    (bk : Backing h ze roots), H.Valid → (∀ k, RootAggregates H (roots k)) →
    ∀ (e : EndSubmission), OnTime H e.leg → EndAcceptedBy H roots bk e → EndBreak bk e

/-- **NO DOUBLE PAYMENT, OR A BREAK ON THE RECORDED TRANSFER'S SUBMISSION.**

**Correction (StaleSnapshotFaithful).**  The break is on the END submission only because both
branches take a genuine-leaf absence witness.  With the deployed check, a transfer that executed
can also be refunded on the BEGIN branch on a padding-forged proof, which needs no END
submission, so it is paid twice with no break on one (an executed flow passes that branch:
`Contracts.Refund.PaddingAcceptedRefundLocatesAbsenceBreak`); see the module docstring of
`../Specs/EndBranch.lean`. -/
def Properties.PinnedBridgeNoDoublePaymentOrBreak : Prop :=
  ∀ (h : MerkleSpec.Hash) (ze : UInt256) (H : History) (roots : Roots)
    (bk : Backing h ze roots), H.Valid → (∀ k, RootAggregates H (roots k)) →
    ∀ (flow : Transfer → List Leg) (sub : Transfer → EndSubmission)
      (source destination : ℕ) (s : State),
      Run (pinnedEvidence H roots bk flow sub) (initial source destination) s →
        ¬ (s.delivered = true ∧ s.refunded = true)
          ∨ ∃ i, s.record = some i ∧ EndAcceptedBy H roots bk (sub i) ∧ EndBreak bk (sub i)

/-- **VALUE CONSERVED, OR A BREAK ON THE RECORDED TRANSFER'S SUBMISSION.**

**Correction (StaleSnapshotFaithful).**  As for `Properties.PinnedBridgeNoDoublePaymentOrBreak`:
the break list is over a genuine-leaf absence witness; see the module docstring of
`../Specs/EndBranch.lean`. -/
def Properties.PinnedBridgeValueConservedOrBreak : Prop :=
  ∀ (h : MerkleSpec.Hash) (ze : UInt256) (H : History) (roots : Roots)
    (bk : Backing h ze roots), H.Valid → (∀ k, RootAggregates H (roots k)) →
    ∀ (flow : Transfer → List Leg) (sub : Transfer → EndSubmission)
      (source destination : ℕ) (s : State),
      Run (pinnedEvidence H roots bk flow sub) (initial source destination) s →
        accounted s = source + destination
          ∨ ∃ i, s.record = some i ∧ EndAcceptedBy H roots bk (sub i) ∧ EndBreak bk (sub i)

/-- **§3 PREMISES SATISFIABLE, THE BREAK IS FALSE ON AN HONEST SUBMISSION.**  Under a hash
that collides elsewhere, every imported root aggregates, the recorded transfer is refunded, and
its END submission is accepted and carries no break.  The statement does not say that the
refund used that submission: it asks neither that the submission's leg is a prerequisite of the
transfer nor that no leg of the transfer has a BEGIN-branch timeout, and its body is met by a
refund on the BEGIN branch alone (`Properties.PinnedBridgeRefundWitnessGap`).  The form that
asks both is `Properties.PinnedBridgeRefundWitnessLinked` (`Properties/EndBranchStrong.lean`).
In the instance the submission is the honest batch-leaf path for the root's last batch. -/
def Properties.PinnedBridgeRefundWitness : Prop :=
  ∃ (h : MerkleSpec.Hash) (ze : UInt256) (H : History) (roots : Roots) (bk : Backing h ze roots)
    (flow : Transfer → List Leg) (sub : Transfer → EndSubmission) (i : Transfer) (s : State),
    H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧
      Run (pinnedEvidence H roots bk flow sub) (initial i.amount 0) s ∧
      s.refunded = true ∧ s.record = some i ∧
      EndAcceptedBy H roots bk (sub i) ∧ ¬ EndBreak bk (sub i) ∧
      (∃ a b c d : UInt256, (a, b) ≠ (c, d) ∧ h a b = h c d)

/-- **THE BREAK FIRES WHERE THE BUG IS.**  Every imported root aggregates and the leg is
committed in time, but the chain tree's next batch leaf equals the empty-entry constant, so
a non-last in-time batch passes `_verifyLastBatchInRoot`.  The bridge pays twice, and the
located break is a `PinnedBreak` on exactly the recorded transfer's END submission. -/
def Properties.ForgedLastBatchLocatesBreak : Prop :=
  ∃ (h : MerkleSpec.Hash) (ze : UInt256) (H : History) (roots : Roots) (bk : Backing h ze roots)
    (flow : Transfer → List Leg) (sub : Transfer → EndSubmission) (i : Transfer) (s : State),
    H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧ OnTime H (sub i).leg ∧
      Run (pinnedEvidence H roots bk flow sub) (initial i.amount 0) s ∧
      s.delivered = true ∧ s.refunded = true ∧ accounted s = 2 * i.amount ∧
      s.record = some i ∧ EndAcceptedBy H roots bk (sub i) ∧
      MerkleSpec.LastLeaf.PinnedBreak h ze ((bk (sub i).root).leaves (sub i).leg.sourceChain)
        (sub i).batch

/-! ## What soundness buys, for any evidence -/

/-- **WITHOUT SOUNDNESS, ONLY DOUBLE PAYMENT BREAKS CONSERVATION.**  For every evidence,
every reachable state has paid both outcomes or conserves value.  Evidence soundness is used
only to exclude the first disjunct. -/
def Properties.ValueConservedUnlessDoublePaid : Prop :=
  ∀ (E : Evidence) (source destination : ℕ) (s : State),
    Run E (initial source destination) s →
      (s.delivered = true ∧ s.refunded = true) ∨ accounted s = source + destination

end Applications.BurnMintBridge.EndBranch
