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

## Premises, and where each is shown satisfiable

* `History.Valid` (guarded IMT evolution from genesis, monotone settlement times):
  `EndBranchRefundWitness`, `OnTimeLegExecutesWitness`, `HaltedChainNeedsEndBranch`.
* `RootAggregates` for every imported root: `HaltedChainNeedsEndBranch`,
  `CheckedExecutionWitness`, `PinnedBridgeRefundWitness`, `ForgedLastBatchLocatesBreak`.
* An accepted timeout on the BEGIN branch as run: `BeginBranchRefundWitness`.
* An accepted timeout on the END branch: `HaltedChainNeedsEndBranch` (index level),
  `PinnedBridgeRefundWitness` (hash level); on the forged path with the leg on time:
  `ForgedLastBatchLocatesBreak`.
* A prepared transfer with every prerequisite on time (`CheckedExecutionRemainsPossible`):
  `CheckedExecutionWitness`.
* A never-committed leg, a root after the deadline and a recorded unrefunded transfer
  (`TimeoutComplete`, `TimedOutTransferRefundEnabled`): `HaltedChainNeedsEndBranch` (its END
  timeout carries the root's post-deadline creation; its burned state records the transfer).

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

/-- **§1 PREMISES SATISFIABLE, REFUND ON THE END FORM.**  A valid history, a leg with an
END-form timeout, and a run of the bridge that refunds the prepared transfer. -/
def Properties.EndBranchRefundWitness : Prop :=
  ∃ (H : History) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    H.Valid ∧ (∃ l ∈ flow i, MissingEnd H l) ∧
      Run (evidenceEither H flow) (initial i.amount 0) s ∧ s.refunded = true ∧
      s.sourceBalance = i.amount

/-- **§1 PREMISES SATISFIABLE, EXECUTION ON TIME.**  A valid history in which every
prerequisite of a transfer is on time, and a run that executes it. -/
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
(`TimeoutSoundness.begin_absence_implies_never_finalized`). -/
def Properties.BeginViaNeverFinalized : Prop :=
  ∀ (H : History) (R : Contracts.Timeout.SlRoot), H.Valid → ∀ (l : Leg), BeginVia H R l →
    ∀ n, H.settledAt l.sourceChain n ≤ l.deadline →
      l.commitValue ∉ keys (H.tree l.sourceChain n)

/-- **AN END-BRANCH TIMEOUT MEANS NEVER FINALIZED**, from the on-chain check
(`LastBatchInRoot.end_branch_from_onchain_check`), when the root aggregates every batch
settled before it. -/
def Properties.EndViaNeverFinalized : Prop :=
  ∀ (H : History) (R : Contracts.Timeout.SlRoot), H.Valid → RootAggregates H R →
    ∀ (l : Leg), EndVia H R l → ∀ n, H.settledAt l.sourceChain n ≤ l.deadline →
      l.commitValue ∉ keys (H.tree l.sourceChain n)

/-- **THE GATE AS RUN REFINES THE ADAPTER.**  An accepted timeout against an aggregating
root is an instance of `Missing`, so every `ProtocolComposition` result applies to the path
the contract takes. -/
def Properties.TimeoutViaImpliesMissing : Prop :=
  ∀ (H : History) (R : Contracts.Timeout.SlRoot), H.Valid → RootAggregates H R →
    ∀ (l : Leg), TimeoutVia H R l → Missing H l

/-- The as-run evidence is sound when every imported root aggregates. -/
def Properties.CheckedEvidenceSound : Prop :=
  ∀ (H : History) (roots : Roots), H.Valid → (∀ k, RootAggregates H (roots k)) →
    ∀ (flow : Transfer → List Leg), (checkedEvidence H roots flow).Sound

/-- **NO DOUBLE PAYMENT, BOTH BRANCHES AS RUN.** -/
def Properties.CheckedBridgeNoDoublePayment : Prop :=
  ∀ (H : History) (roots : Roots), H.Valid → (∀ k, RootAggregates H (roots k)) →
    ∀ (flow : Transfer → List Leg) (source destination : ℕ) (s : State),
      Run (checkedEvidence H roots flow) (initial source destination) s →
        ¬ (s.delivered = true ∧ s.refunded = true)

/-- **VALUE CONSERVED, BOTH BRANCHES AS RUN.** -/
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
aggregate, a leg with an accepted BEGIN-branch timeout (a late batch inside the root), and a
run of the bridge that refunds the prepared transfer. -/
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
With both branches, the bridge refunds it (on the END branch). -/
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
refunds it, and it is executed or still executable. -/
def Properties.CheckedExecutionRemainsPossible : Prop :=
  ∀ (H : History) (roots : Roots), H.Valid → (∀ k, RootAggregates H (roots k)) →
    ∀ (flow : Transfer → List Leg) (s p t : State) (i : Transfer),
      Prepare s i p → (checkedEvidence H roots flow).finalize i →
        Run (checkedEvidence H roots flow) p t →
          t.refunded = false ∧
            (t.delivered = true
              ∨ ∃ u, AuthorizedExecution (checkedEvidence H roots flow) t i i u)

/-- **ITS PREMISES ARE SATISFIABLE.**  A valid history whose imported roots aggregate, a
prepared transfer whose prerequisite is on time, and its authorized execution. -/
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
`PinnedBreak` right after the submitted batch or the submitted path a `PathCollision`. -/
def Properties.AcceptedEndOnTimeLocatesBreak : Prop :=
  ∀ (h : MerkleSpec.Hash) (ze : UInt256) (H : History) (roots : Roots)
    (bk : Backing h ze roots), H.Valid → (∀ k, RootAggregates H (roots k)) →
    ∀ (e : EndSubmission), OnTime H e.leg → EndAcceptedBy H roots bk e → EndBreak bk e

/-- **NO DOUBLE PAYMENT, OR A BREAK ON THE RECORDED TRANSFER'S SUBMISSION.** -/
def Properties.PinnedBridgeNoDoublePaymentOrBreak : Prop :=
  ∀ (h : MerkleSpec.Hash) (ze : UInt256) (H : History) (roots : Roots)
    (bk : Backing h ze roots), H.Valid → (∀ k, RootAggregates H (roots k)) →
    ∀ (flow : Transfer → List Leg) (sub : Transfer → EndSubmission)
      (source destination : ℕ) (s : State),
      Run (pinnedEvidence H roots bk flow sub) (initial source destination) s →
        ¬ (s.delivered = true ∧ s.refunded = true)
          ∨ ∃ i, s.record = some i ∧ EndAcceptedBy H roots bk (sub i) ∧ EndBreak bk (sub i)

/-- **VALUE CONSERVED, OR A BREAK ON THE RECORDED TRANSFER'S SUBMISSION.** -/
def Properties.PinnedBridgeValueConservedOrBreak : Prop :=
  ∀ (h : MerkleSpec.Hash) (ze : UInt256) (H : History) (roots : Roots)
    (bk : Backing h ze roots), H.Valid → (∀ k, RootAggregates H (roots k)) →
    ∀ (flow : Transfer → List Leg) (sub : Transfer → EndSubmission)
      (source destination : ℕ) (s : State),
      Run (pinnedEvidence H roots bk flow sub) (initial source destination) s →
        accounted s = source + destination
          ∨ ∃ i, s.record = some i ∧ EndAcceptedBy H roots bk (sub i) ∧ EndBreak bk (sub i)

/-- **§3 PREMISES SATISFIABLE, THE BREAK IS FALSE ON AN HONEST SUBMISSION.**  Under a hash
that collides elsewhere, every imported root aggregates, the bridge refunds the recorded
transfer on its END submission (the honest batch-leaf path for the root's last batch), and
that submission carries no break. -/
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
