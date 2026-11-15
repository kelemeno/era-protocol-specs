import EraSpec.Examples.BurnMintBridge.Specs.EndBranchStrong

/-!
# Properties: the END-branch witnesses, pinned to the transfer and the branch

Statements about `../Specs/EndBranch.lean` and `../Specs/EndBranchStrong.lean`; proofs in
`../Proofs/EndBranchStrong.lean`.

## Why

Three satisfiability witnesses of `Properties/EndBranch.lean` said less than their docstrings
did.  Those docstrings now state the gap and point here.

* `EndBranchRefundWitness` and `BeginBranchRefundWitness` were documented as a run that refunds
  "the prepared transfer".  The statements tie the transfer `i` to the run only through the
  starting balance
  `i.amount` and the final `s.sourceBalance = i.amount`.  So the run may prepare and refund
  any other transfer of the same amount (`EndBranchRefundWitnessGap`,
  `BeginBranchRefundWitnessGap`).  For the BEGIN witness that refund may even be authorized by
  the END branch alone, with no BEGIN-branch timeout on any leg of the refunded transfer
  (`BeginBranchRefundWitnessGap`).  It then does not show that a BEGIN-branch timeout, as run,
  drives a refund.
* `OnTimeLegExecutesWitness` was documented as a history "in which every prerequisite of a
  transfer is on time, and a run that executes it".  The statement does not pin the executed
  transfer to `i`, and `∀ l ∈ flow i, OnTime H l` holds vacuously when `i` has no prerequisite.
  With `flow i = []`, a run that executes another transfer satisfies it, on a history where no
  nonzero value is ever on time (`OnTimeLegExecutesWitnessGap`).  A prerequisite with commit
  value `0` does not help either: `0` is the tree's sentinel key, a member of the genesis
  snapshot of every valid history, so such a leg is on time with nothing committed.

## What is claimed

* **Pinned witnesses.**  Each records the transfer that was resolved (`s.record = some i`):
  * `EndBranchRefundWitnessPinned`: the run is a run of `endFormEvidence`, whose recovery is
    the END form only.  In §1 this names the form and pins no branch: the conjunct follows
    from the unpinned body together with the record pin, and the BEGIN form cannot be
    excluded, because `MissingEndImpliesMissing` makes every END-form timeout a `Missing`.
  * `OnTimeLegExecutesWitnessPinned`: the executed transfer has a prerequisite
    (`flow i ≠ []`), every prerequisite has a nonzero commit value and is on time, and the
    transfer is not refunded.  The run is a run of `evidenceEither`.
  * `BeginBranchRefundWitnessPinned`: no leg of the refunded transfer has an END-branch
    timeout against any imported root, so the BEGIN branch is the only possible
    authorization of the refund in the as-run bridge.  That conjunct is what pins the branch;
    the `beginOnlyEvidence` run follows from it, the unpinned body and the record pin.
* **The record carries the authorization** (`ReachableResolutionAuthorizedByRecord`, any
  evidence).  In every reachable state, a delivery is backed by finalization evidence and a
  refund by recovery evidence, each for the recorded transfer.  With it, the pinned witnesses
  say which evidence paid: for `BeginBranchRefundWitnessPinned`, a BEGIN-branch timeout of a
  leg of `i`.
* **The gaps** (`EndBranchRefundWitnessGap`, `OnTimeLegExecutesWitnessGap`,
  `BeginBranchRefundWitnessGap`).  Each one's first conjunct is the unpinned statement's body,
  verbatim, and its remaining conjuncts show what that body allows.

The pinned witnesses and the gaps are existential statements with no premise.  The one
universal statement, `ReachableResolutionAuthorizedByRecord`, has only the `Run` premise, which
the empty run meets, and the pinned refund witnesses reach states where its refund clause is
not idle.  None uses a hash.
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
prerequisite, every one of them a nonzero commit value that is on time; and a run of
`evidenceEither` from `initial i.amount 0` that ends with `i` recorded, delivered and not
refunded, and with its amount at the destination.

The commit values must be nonzero for the statement to show a commitment.  `0` is the tree's
sentinel key and belongs to the genesis snapshot of every valid history, so a leg with commit
value `0` is on time everywhere, and without this conjunct the statement would hold on any valid
history with nothing committed. -/
def Properties.OnTimeLegExecutesWitnessPinned : Prop :=
  ∃ (H : History) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    H.Valid ∧ flow i ≠ [] ∧ (∀ l ∈ flow i, l.commitValue ≠ 0 ∧ OnTime H l) ∧
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

/-- **`OnTimeLegExecutesWitness`'s BODY ALLOWS AN EXECUTION WITH NO NONZERO VALUE ON TIME.**
The first conjunct is that body, verbatim.  In the instance, `i` has no prerequisite, the
executed record is not `i`, and no leg with a nonzero commit value is ever on time. -/
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
