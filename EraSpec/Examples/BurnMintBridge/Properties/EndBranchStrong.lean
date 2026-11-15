import EraSpec.Examples.BurnMintBridge.Specs.EndBranchStrong

/-!
# Properties: the END-branch witnesses, pinned to the transfer and the branch

Statements about `../Specs/EndBranch.lean` and `../Specs/EndBranchStrong.lean`; proofs in
`../Proofs/EndBranchStrong.lean`.

## Why

Three satisfiability witnesses of `Properties/EndBranch.lean` said less than their docstrings
did: `OnTimeLegExecutesWitness`, `CheckedExecutionWitness` and `PinnedBridgeRefundWitness`.  The
bodies of two more, `EndBranchRefundWitness` and `BeginBranchRefundWitness`, admit final states
that refund a transfer other than their `i`, but in every world where such a body holds, the
run that refunds `i` itself meets it too.  Those docstrings now say what each statement shows
and point here.

* `EndBranchRefundWitness` and `BeginBranchRefundWitness` were documented as a run that refunds
  "the prepared transfer".  Their bodies tie the transfer `i` to the run only through the
  starting balance `i.amount` and the final `s.sourceBalance = i.amount`, so they admit final
  states that refund another transfer of amount at most `i.amount`
  (`EndBranchRefundWitnessGap`, `BeginBranchRefundWitnessGap`).  But in every world
  `(H, flow, i)`, with `roots` for the BEGIN witness, where such a body holds, the run that
  prepares and refunds `i` itself meets it too, so the record pin adds nothing world by world
  (`EndBranchRefundWitnessRecordPinFree`, `BeginBranchRefundWitnessRecordPinFree`).
  `EndBranchRefundWitnessPinned` restates `EndBranchRefundWitness`, and
  `EndBranchRefundWitnessGap` shows a final state the body allows, not a world that the
  pinned form misses.
* The other refund that `BeginBranchRefundWitness`'s body admits may be authorized by the END
  branch alone (`BeginBranchRefundWitnessGap`).  Still, in every world where the body holds,
  `i` itself can also be refunded on the BEGIN branch alone
  (`BeginBranchRefundWitnessRecordPinFree`).  What the statement does not exclude is an
  END-branch timeout on a leg of `i` against another imported root
  (`BeginBranchRefundWitnessBranchGap`), so it does not show that the BEGIN branch is needed.
  `BeginBranchRefundWitnessPinned` excludes it.
* `OnTimeLegExecutesWitness` was documented as a history "in which every prerequisite of a
  transfer is on time, and a run that executes it", and `CheckedExecutionWitness` as "a
  prepared transfer whose prerequisite is on time, and its authorized execution".  Neither
  asks `i` to have a prerequisite, and with `flow i = []` the on-time premise holds
  vacuously: `OnTimeLegExecutesWitness`'s body is then met on a history where no nonzero value
  is ever on time (`OnTimeLegExecutesWitnessGap`).  A prerequisite with commit value `0` does
  not help either: `0` is the tree's sentinel key, in every snapshot of a valid history, so
  such a leg is on time as soon as some batch of its chain settled by its deadline, with
  nothing committed.  `OnTimeLegExecutesWitnessPinned` and `CheckedExecutionWitnessPinned` ask
  for at least one prerequisite, each with a nonzero commit value.  Per world that is all
  `OnTimeLegExecutesWitnessPinned` adds: its record pin comes free
  (`OnTimeLegExecutesWitnessRecordPinFree`).
* `PinnedBridgeRefundWitness` was documented as a refund of the recorded transfer "on its END
  submission".  Its body asks that the transfer be refunded and that its END submission be
  accepted with no break, but not that the refund used that submission: the submission's leg
  need not be a prerequisite of the transfer, and a BEGIN-branch timeout may authorize the
  refund.  `PinnedBridgeRefundWitnessLinked` excludes both.

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
* **Per world** (`EndBranchRefundWitnessRecordPinFree`, `OnTimeLegExecutesWitnessRecordPinFree`,
  `BeginBranchRefundWitnessRecordPinFree`).  For every world, an unpinned body that holds for
  some final state also holds for the run that prepares and resolves `i` itself, which for the
  two refund forms is also a run of their single-form evidence.  Each pinned body is its
  unpinned body with the record pinned (for the on-time form, also not refunded), the
  single-form run for the refund forms, and further conjuncts on the world: none for the END
  form, `flow i ≠ []` with nonzero commit values for the on-time form, and the no-END conjunct
  for the BEGIN form.  Per world, those further conjuncts are all that a pinned form adds.
* **Stronger forms of two older witnesses.**  The first conjunct of each is the older body,
  verbatim.  `CheckedExecutionWitnessPinned` adds at least one prerequisite, each with a
  nonzero commit value.  `PinnedBridgeRefundWitnessLinked` adds that the END submission's leg
  is a prerequisite of the recorded transfer and that no leg of that transfer has a
  BEGIN-branch timeout, so the only recovery evidence `pinnedEvidence` accepts for it is that
  submission.
* **The record carries the authorization** (`ReachableResolutionAuthorizedByRecord`, any
  evidence).  In every reachable state, a delivery is backed by finalization evidence and a
  refund by recovery evidence, each for the recorded transfer.  With it, the pinned witnesses
  say which evidence paid: for `BeginBranchRefundWitnessPinned`, a BEGIN-branch timeout of a
  leg of `i`; for `PinnedBridgeRefundWitnessLinked`, the END submission of `i`.
* **The gaps** (`EndBranchRefundWitnessGap`, `OnTimeLegExecutesWitnessGap`,
  `BeginBranchRefundWitnessGap`, `BeginBranchRefundWitnessBranchGap`).  Each one's first
  conjunct is the unpinned statement's body, verbatim, and its remaining conjuncts show what
  that body allows.  `EndBranchRefundWitnessGap` and `BeginBranchRefundWitnessGap` show final
  states that resolve another transfer.  `OnTimeLegExecutesWitnessGap` and
  `BeginBranchRefundWitnessBranchGap` show worlds in which no final state meets the pinned
  body.

The pinned witnesses, the stronger forms and the gaps are existential statements with no
premise.  The per-world statements are equivalences with no premise.
`ReachableResolutionAuthorizedByRecord` has only the `Run` premise, which the empty run meets,
and the pinned refund witnesses reach states where its refund clause is not idle.  Only
`PinnedBridgeRefundWitnessLinked` uses a hash: as in `PinnedBridgeRefundWitness`, one that
collides elsewhere.
-/

namespace Applications.BurnMintBridge.EndBranch

open IMTAbstract Properties.PreparedBridge

/-! ## Pinned witnesses -/

/-- **§1 REFUND ON THE END FORM, PINNED.**  A valid history; a transfer `i` one of whose legs
has an END-form timeout; and a run from `initial i.amount 0` in which only END-form timeouts
authorize recovery (`endFormEvidence`).  The run is also a run of `evidenceEither`, and it
ends with `i` recorded and refunded and the source balance restored.

This restates `EndBranchRefundWitness` with the record made explicit: in every world, one body
holds for some final state iff the other does (`EndBranchRefundWitnessRecordPinFree`). -/
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
sentinel key and is in every snapshot of a valid history, so a leg with commit value `0` is on
time as soon as some batch of its chain settled by its deadline, with nothing committed.
Without this conjunct the statement would hold on any valid history with nothing committed. -/
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
it ends with `i` recorded and refunded and the source balance restored.

Per world, the no-END conjunct is all this adds to `BeginBranchRefundWitness`: the record pin
and the `beginOnlyEvidence` run come free (`BeginBranchRefundWitnessRecordPinFree`).  Across
two imported roots that conjunct can fail where the rest holds
(`BeginBranchRefundWitnessBranchGap`). -/
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

/-! ## Per world: what the record pin adds -/

/-- **THE END RECORD PIN ADDS NOTHING, WORLD BY WORLD.**  For every history `H`, flow and
transfer `i`, some final state meets `EndBranchRefundWitness`'s body iff some final state meets
`EndBranchRefundWitnessPinned`'s body (the right-hand side).  A refunded run from
`initial i.amount 0` needs `0 < i.amount`, and then preparing and recovering `i` itself is a
run of `endFormEvidence` that ends with `i` recorded and refunded and the balance restored.
So no world separates the two statements. -/
def Properties.EndBranchRefundWitnessRecordPinFree : Prop :=
  ∀ (H : History) (flow : Transfer → List Leg) (i : Transfer),
    (∃ s : State, H.Valid ∧ (∃ l ∈ flow i, MissingEnd H l) ∧
      Run (evidenceEither H flow) (initial i.amount 0) s ∧ s.refunded = true ∧
      s.sourceBalance = i.amount) ↔
    ∃ s : State, H.Valid ∧ (∃ l ∈ flow i, MissingEnd H l) ∧
      Run (endFormEvidence H flow) (initial i.amount 0) s ∧
      Run (evidenceEither H flow) (initial i.amount 0) s ∧
      s.record = some i ∧ s.refunded = true ∧ s.sourceBalance = i.amount

/-- **THE ON-TIME RECORD PIN ADDS NOTHING, WORLD BY WORLD.**  For every history `H`, flow and
transfer `i`, some final state meets `OnTimeLegExecutesWitness`'s body iff one meets it with
`i` recorded and not refunded: preparing and executing `i` itself.  So, per world,
`OnTimeLegExecutesWitnessPinned` adds only `flow i ≠ []` and nonzero commit values. -/
def Properties.OnTimeLegExecutesWitnessRecordPinFree : Prop :=
  ∀ (H : History) (flow : Transfer → List Leg) (i : Transfer),
    (∃ s : State, H.Valid ∧ (∀ l ∈ flow i, OnTime H l) ∧
      Run (evidenceEither H flow) (initial i.amount 0) s ∧ s.delivered = true ∧
      s.destinationBalance = i.amount) ↔
    ∃ s : State, (H.Valid ∧ (∀ l ∈ flow i, OnTime H l) ∧
      Run (evidenceEither H flow) (initial i.amount 0) s ∧ s.delivered = true ∧
      s.destinationBalance = i.amount) ∧
      s.record = some i ∧ s.refunded = false

/-- **THE BEGIN WITNESS ALREADY REFUNDS ITS TRANSFER ON THE BEGIN BRANCH, WORLD BY WORLD.**  For
every history `H`, roots, flow and transfer `i`, some final state meets
`BeginBranchRefundWitness`'s body iff one meets it with `i` recorded, on a run of
`beginOnlyEvidence`: preparing and recovering `i` itself on the BEGIN branch alone.  So, per
world, `BeginBranchRefundWitnessPinned` adds only the no-END conjunct. -/
def Properties.BeginBranchRefundWitnessRecordPinFree : Prop :=
  ∀ (H : History) (roots : Roots) (flow : Transfer → List Leg) (i : Transfer),
    (∃ s : State, H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧
      (∃ l ∈ flow i, ∃ k, BeginVia H (roots k) l) ∧
      Run (checkedEvidence H roots flow) (initial i.amount 0) s ∧ s.refunded = true ∧
      s.sourceBalance = i.amount) ↔
    ∃ s : State, (H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧
      (∃ l ∈ flow i, ∃ k, BeginVia H (roots k) l) ∧
      Run (checkedEvidence H roots flow) (initial i.amount 0) s ∧ s.refunded = true ∧
      s.sourceBalance = i.amount) ∧
      Run (beginOnlyEvidence H roots flow) (initial i.amount 0) s ∧ s.record = some i

/-! ## Stronger forms of two older witnesses -/

/-- **`CheckedExecutionWitness` WITH A PREREQUISITE THAT SHOWS A COMMITMENT.**  The first
conjunct is `CheckedExecutionWitness`'s body, verbatim: a valid history whose imported roots
aggregate, a prepared transfer `i` all of whose prerequisites are on time, and its authorized
execution.  The other conjuncts ask `i` to have at least one prerequisite, each with a nonzero
commit value, as `OnTimeLegExecutesWitnessPinned` does.  Without them the body is met by a
transfer with no prerequisite, for which `finalize` holds vacuously, or by one whose only
prerequisite has commit value `0` and is on time with nothing committed. -/
def Properties.CheckedExecutionWitnessPinned : Prop :=
  ∃ (H : History) (roots : Roots) (flow : Transfer → List Leg) (s p : State) (i : Transfer),
    (H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧ Prepare s i p ∧
      (checkedEvidence H roots flow).finalize i ∧
      ∃ u, AuthorizedExecution (checkedEvidence H roots flow) p i i u) ∧
    flow i ≠ [] ∧ ∀ l ∈ flow i, l.commitValue ≠ 0

/-- **§3 THE REFUND IS ON THE RECORDED TRANSFER'S END SUBMISSION.**  The first conjunct is
`PinnedBridgeRefundWitness`'s body, verbatim: under a hash that collides elsewhere, every
imported root aggregates, the recorded transfer `i` is refunded, and its END submission is
accepted and carries no break.  The other conjuncts make that submission's leg a prerequisite
of `i` and exclude a BEGIN-branch timeout on every leg of `i`, against any imported root.  So
the only recovery evidence `pinnedEvidence` accepts for `i` is that END submission, and the
refund used it. -/
def Properties.PinnedBridgeRefundWitnessLinked : Prop :=
  ∃ (h : MerkleSpec.Hash) (ze : UInt256) (H : History) (roots : Roots) (bk : Backing h ze roots)
    (flow : Transfer → List Leg) (sub : Transfer → EndSubmission) (i : Transfer) (s : State),
    (H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧
      Run (pinnedEvidence H roots bk flow sub) (initial i.amount 0) s ∧
      s.refunded = true ∧ s.record = some i ∧
      EndAcceptedBy H roots bk (sub i) ∧ ¬ EndBreak bk (sub i) ∧
      (∃ a b c d : UInt256, (a, b) ≠ (c, d) ∧ h a b = h c d)) ∧
    (sub i).leg ∈ flow i ∧ ∀ l ∈ flow i, ∀ k, ¬ BeginVia H (roots k) l

/-! ## What the unpinned statements allow -/

/-- **`EndBranchRefundWitness`'s BODY ALLOWS A REFUND OF ANOTHER TRANSFER.**  The first
conjunct is that body, verbatim.  In the instance, the refunded record is not `i`.

The gap is in the final state only, so this restates what the body's text allows rather than
showing a world that separates the two statements.  Every world that meets the body also meets
`EndBranchRefundWitnessPinned`'s body, this instance's included
(`EndBranchRefundWitnessRecordPinFree`). -/
def Properties.EndBranchRefundWitnessGap : Prop :=
  ∃ (H : History) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    (H.Valid ∧ (∃ l ∈ flow i, MissingEnd H l) ∧
      Run (evidenceEither H flow) (initial i.amount 0) s ∧ s.refunded = true ∧
      s.sourceBalance = i.amount) ∧
    s.record ≠ some i

/-- **`OnTimeLegExecutesWitness`'s BODY ALLOWS AN EXECUTION WITH NO NONZERO VALUE ON TIME.**
The first conjunct is that body, verbatim.  In the instance, `i` has no prerequisite, the
executed record is not `i`, and no leg with a nonzero commit value is ever on time.  With
`flow i = []`, no final state meets `OnTimeLegExecutesWitnessPinned`'s body in this world. -/
def Properties.OnTimeLegExecutesWitnessGap : Prop :=
  ∃ (H : History) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    (H.Valid ∧ (∀ l ∈ flow i, OnTime H l) ∧
      Run (evidenceEither H flow) (initial i.amount 0) s ∧ s.delivered = true ∧
      s.destinationBalance = i.amount) ∧
    flow i = [] ∧ s.record ≠ some i ∧ (∀ l : Leg, l.commitValue ≠ 0 → ¬ OnTime H l)

/-- **`BeginBranchRefundWitness`'s BODY ALLOWS A REFUND ON THE END BRANCH ONLY.**  The first
conjunct is that body, verbatim.  In the instance, the refunded record is not `i`, and no leg
of the refunded transfer has a BEGIN-branch timeout against any imported root.  So the refund
was authorized by the END branch alone.  This is a final state the body allows;
`BeginBranchRefundWitnessBranchGap` shows a world in which `BeginBranchRefundWitnessPinned`
fails. -/
def Properties.BeginBranchRefundWitnessGap : Prop :=
  ∃ (H : History) (roots : Roots) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    (H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧
      (∃ l ∈ flow i, ∃ k, BeginVia H (roots k) l) ∧
      Run (checkedEvidence H roots flow) (initial i.amount 0) s ∧ s.refunded = true ∧
      s.sourceBalance = i.amount) ∧
    s.record ≠ some i ∧
    (∀ j, s.record = some j → ∀ l ∈ flow j, ∀ k, ¬ BeginVia H (roots k) l)

/-- **`BeginBranchRefundWitness`'s BODY DOES NOT SHOW THAT THE BEGIN BRANCH IS NEEDED.**  The
first conjunct is that body, verbatim.  In the instance, `i` is recorded and refunded on a run
of `beginOnlyEvidence`, and one leg of `i` has a BEGIN-branch timeout against one imported root
and an END-branch timeout against another (on a valid history one root never gives a leg both,
`beginVia_not_endVia`).  Every conjunct of `BeginBranchRefundWitnessPinned`'s body holds except
the no-END one, which fails, so in this world no final state meets that body. -/
def Properties.BeginBranchRefundWitnessBranchGap : Prop :=
  ∃ (H : History) (roots : Roots) (flow : Transfer → List Leg) (i : Transfer) (s : State),
    (H.Valid ∧ (∀ k, RootAggregates H (roots k)) ∧
      (∃ l ∈ flow i, ∃ k, BeginVia H (roots k) l) ∧
      Run (checkedEvidence H roots flow) (initial i.amount 0) s ∧ s.refunded = true ∧
      s.sourceBalance = i.amount) ∧
    Run (beginOnlyEvidence H roots flow) (initial i.amount 0) s ∧ s.record = some i ∧
    ∃ l ∈ flow i, (∃ k, BeginVia H (roots k) l) ∧ ∃ k, EndVia H (roots k) l

end Applications.BurnMintBridge.EndBranch
