import EraSpec.Examples.BurnMintBridge.Specs.EndBranchStrong

/-!
# Properties: the END-branch witnesses, pinned to the transfer and the branch

Statements about `../Specs/EndBranch.lean` and `../Specs/EndBranchStrong.lean`; proofs in
`../Proofs/EndBranchStrong.lean`.

## Why

Three satisfiability witnesses of `Properties/EndBranch.lean` say less than their docstrings.

* `EndBranchRefundWitness` and `BeginBranchRefundWitness` say that a run refunds "the prepared
  transfer".  The statements tie the transfer `i` to the run only through the starting balance
  `i.amount` and the final `s.sourceBalance = i.amount`.  So the run may prepare and refund
  any other transfer of the same amount (`EndBranchRefundWitnessGap`,
  `BeginBranchRefundWitnessGap`).  For the BEGIN witness that refund may even be authorized by
  the END branch alone, with no BEGIN-branch timeout on any leg of the refunded transfer
  (`BeginBranchRefundWitnessGap`).  It then does not show that a BEGIN-branch timeout, as run,
  drives a refund.
* `OnTimeLegExecutesWitness` says that a run executes a transfer "in which every prerequisite
  is on time".  The statement does not pin the executed transfer to `i`, and `∀ l ∈ flow i,
  OnTime H l` holds vacuously when `i` has no prerequisite.  A run that executes another
  transfer with no prerequisite satisfies it, on a history where no nonzero value is ever on
  time (`OnTimeLegExecutesWitnessGap`).

## What is claimed

* **Pinned witnesses.**  Each records the transfer that was resolved (`s.record = some i`):
  * `EndBranchRefundWitnessPinned`: the refund is driven by the END form alone, since the
    run is a run of `endFormEvidence`.  The BEGIN form cannot also be excluded in §1, because
    `MissingEndImpliesMissing` makes every END-form timeout a `Missing`.
  * `OnTimeLegExecutesWitnessPinned`: the executed transfer has a prerequisite
    (`flow i ≠ []`), all on time, and it is not refunded.
  * `BeginBranchRefundWitnessPinned`: the BEGIN branch alone drives the refund, since the run
    is a run of `beginOnlyEvidence`.  No leg of the refunded transfer has an END-branch
    timeout against any imported root, so the BEGIN branch is the only possible
    authorization of the refund in the as-run bridge too.
* **The record carries the authorization** (`ReachableResolutionAuthorizedByRecord`, any
  evidence).  In every reachable state, a delivery is backed by finalization evidence and a
  refund by recovery evidence, each for the recorded transfer.  With it, the pinned witnesses
  say which evidence paid: for `BeginBranchRefundWitnessPinned`, a BEGIN-branch timeout of a
  leg of `i`.
* **The gaps** (`EndBranchRefundWitnessGap`, `OnTimeLegExecutesWitnessGap`,
  `BeginBranchRefundWitnessGap`).  Each one's first conjunct is the unpinned statement's body,
  verbatim, and its remaining conjuncts show what that body allows.

No property here has a premise.  None uses a hash.
-/

namespace Applications.BurnMintBridge.EndBranch

open IMTAbstract Properties.PreparedBridge

/-! ## Pinned witnesses -/

/-- **§1 REFUND ON THE END FORM, PINNED.**  A valid history; a transfer `i` one of whose legs
has an END-form timeout; and a run from `initial i.amount 0` in which only END-form timeouts
authorize recovery (`endFormEvidence`).  The run is also a run of `evidenceEither`, and it
ends with `i` recorded and refunded and the source balance restored. -/
def Properties.EndBranchRefundWitnessPinned : Prop :=
  ∃ (H : History) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    H.Valid ∧ (∃ l ∈ flow i, MissingEnd H l) ∧
      Run (endFormEvidence H flow) (initial i.amount 0) s ∧
      Run (evidenceEither H flow) (initial i.amount 0) s ∧
      s.record = some i ∧ s.refunded = true ∧ s.sourceBalance = i.amount

/-- **§1 EXECUTION ON TIME, PINNED.**  A valid history; a transfer `i` with at least one
prerequisite, every one of them on time; and a run of `evidenceEither` from
`initial i.amount 0` that ends with `i` recorded, delivered and not refunded, and with its
amount at the destination. -/
def Properties.OnTimeLegExecutesWitnessPinned : Prop :=
  ∃ (H : History) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    H.Valid ∧ flow i ≠ [] ∧ (∀ l ∈ flow i, OnTime H l) ∧
      Run (evidenceEither H flow) (initial i.amount 0) s ∧
      s.record = some i ∧ s.delivered = true ∧ s.refunded = false ∧
      s.destinationBalance = i.amount

/-- **§2 REFUND ON THE BEGIN BRANCH AS RUN, PINNED.**  A valid history whose imported roots
aggregate; a transfer `i` one of whose legs has an accepted BEGIN-branch timeout, and none of
whose legs has an END-branch timeout against any imported root; and a run from
`initial i.amount 0` in which only BEGIN-branch timeouts authorize recovery
(`beginOnlyEvidence`).  The run is also a run of the as-run bridge (`checkedEvidence`), and
it ends with `i` recorded and refunded and the source balance restored. -/
def Properties.BeginBranchRefundWitnessPinned : Prop :=
  ∃ (H : History) (roots : Roots) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧
      (∃ l ∈ flow i, ∃ k, BeginVia H (roots k) l) ∧
      (∀ l ∈ flow i, ∀ k, ¬ EndVia H (roots k) l) ∧
      Run (beginOnlyEvidence H roots flow) (initial i.amount 0) s ∧
      Run (checkedEvidence H roots flow) (initial i.amount 0) s ∧
      s.record = some i ∧ s.refunded = true ∧ s.sourceBalance = i.amount

/-- **THE RECORD CARRIES THE AUTHORIZATION**, for any evidence and no soundness premise.  In
every state reachable from `initial`, a delivery is backed by finalization evidence for the
recorded transfer, and a refund by recovery evidence for it (`Authorized`).  With
`checkedEvidence`, a refund is therefore an accepted timeout, against an imported root, of a
prerequisite of the recorded transfer. -/
def Properties.ReachableResolutionAuthorizedByRecord : Prop :=
  ∀ (E : Evidence) (source destination : ℕ) (s : State),
    Run E (initial source destination) s → Authorized E s

/-! ## What the unpinned statements allow -/

/-- **`EndBranchRefundWitness`'s BODY ALLOWS A REFUND OF ANOTHER TRANSFER.**  The first
conjunct is that body, verbatim.  In the instance, the refunded record is not `i`. -/
def Properties.EndBranchRefundWitnessGap : Prop :=
  ∃ (H : History) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    (H.Valid ∧ (∃ l ∈ flow i, MissingEnd H l) ∧
      Run (evidenceEither H flow) (initial i.amount 0) s ∧ s.refunded = true ∧
      s.sourceBalance = i.amount) ∧
    s.record ≠ some i

/-- **`OnTimeLegExecutesWitness`'s BODY ALLOWS AN EXECUTION WITH NOTHING ON TIME.**  The first
conjunct is that body, verbatim.  In the instance, `i` has no prerequisite, the executed record
is not `i`, and no leg with a nonzero commit value is ever on time. -/
def Properties.OnTimeLegExecutesWitnessGap : Prop :=
  ∃ (H : History) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    (H.Valid ∧ (∀ l ∈ flow i, OnTime H l) ∧
      Run (evidenceEither H flow) (initial i.amount 0) s ∧ s.delivered = true ∧
      s.destinationBalance = i.amount) ∧
    flow i = [] ∧ s.record ≠ some i ∧ (∀ l : Leg, l.commitValue ≠ 0 → ¬ OnTime H l)

/-- **`BeginBranchRefundWitness`'s BODY ALLOWS A REFUND ON THE END BRANCH ONLY.**  The first
conjunct is that body, verbatim.  In the instance, the refunded record is not `i`, and no leg
of the refunded transfer has a BEGIN-branch timeout against any imported root.  So the refund
was authorized by the END branch alone. -/
def Properties.BeginBranchRefundWitnessGap : Prop :=
  ∃ (H : History) (roots : Roots) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    (H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧
      (∃ l ∈ flow i, ∃ k, BeginVia H (roots k) l) ∧
      Run (checkedEvidence H roots flow) (initial i.amount 0) s ∧ s.refunded = true ∧
      s.sourceBalance = i.amount) ∧
    s.record ≠ some i ∧
    (∀ j, s.record = some j → ∀ l ∈ flow j, ∀ k, ¬ BeginVia H (roots k) l)

end Applications.BurnMintBridge.EndBranch
