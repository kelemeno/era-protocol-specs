import EraSpec.Protocol.InteropAtomicity.Specs.Refund

/-!
# Properties: one outcome per obligation, system-wide

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.Refund`.  Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.Refund`.

## The milestone

`Properties.ExecutedObligationNeverRefunded` is the statement this layer exists for: if an
obligation is executed on its destination, then in **no** reachable interleaving of
**any** chains' manager calls does that obligation ever get past `Committed`.  Not
authorized for refund, so never claimed.

Three things had to come together for it:

1. **Refunds need a timeout proof** (`Properties.RefundNeedsOwnFlowTimeout`).  Only
   `authorize` lifts an obligation past `Committed`, and it carries one.  `claim`
   needs `Revertable` already, so it inherits the witness rather than creating it.
2. **The timeout has to be this obligation's own flow's**
   (`Properties.RefundImpliesOwnFlowTimeout`).  `authorize` marks `(F.flowId, …)` for the flow
   it checked, so a refund of an obligation belonging to checked flow `F` can only
   have come from a checked flow with `F`'s id — which `_checkFlowId` makes `F`
   itself.  A different flow's timeout, however genuine, refunds nothing here.
3. **A flow with a verified timeout cannot have delivered**
   (`Contracts.Atomicity.Properties.ExecutedExcludesAnyRefund`), which is where the tree side
   comes in.

## Timeout validity is derived, not assumed

`Properties.VerifiedTimeoutAuthorizes` closes the loop with `EraSpec.Protocol.InteropAtomicity.Properties.Timeout`: a
timeout the contract really verifies — three comparisons against an imported
aggregation root, with the last-batch proof itself discharged in
`Contracts.Timeout.Properties.LastBatchProofIdentifiesLastBatch` — enables the `authorize`
step.  So the capstone covers the real path, and the "last in-time batch" fact that
`Contracts.Atomicity.IsLastOnTime` used to stand for is derived rather than assumed.

What that conclusion *does* carry is `Contracts.Timeout.Aggregates`, the settlement
layer's own invariant: the route from a verified timeout to this capstone runs
through `Properties.VerifiedTimeoutAuthorizes`, which needs it.  The capstone's own statement
does not mention it, and it would be an overstatement to read that as the real path
being assumption-free.

## What the interleaving covers, and what it does not

`Reach` interleaves every chain's manager calls in any order, for any number of
flows at once.  The tree side is a *fixed* history: `System` assigns each chain a
tree per batch up front, and the evidence predicates quantify existentially over all
batches of it.

That is the conservative direction, and worth being explicit about.  A step may cite
evidence from anywhere in the timeline — including batches that had not been
produced when the call was made — so this model admits strictly more refunds and
more executions than an operational one in which evidence must precede the call.
Excluding both outcomes here is therefore the stronger claim.

What it does **not** establish is the operational statement in which root
publication, commitment, authorization and claim are transitions of one system.
That needs either such a model or a projection theorem showing every execution of it
induces a `System` and a `Reach` over that history.  Until one exists, read these
results as: no fixed history admits both outcomes for one obligation.

## The supporting cryptographic claim

`Properties.CrossFlowRefundYieldsCollision` states the binding in the form that does not
assume anything: if one flow's timeout ever refunds another flow's obligation, the
two `flowId` preimages collide.  The protocol guarantee is unconditional; the
cryptography only says the violation is as hard as finding a keccak collision.
-/

namespace Contracts.Refund

open MerkleSpec MerkleSpec.LastLeaf IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.Timeout Contracts.AtomicFlowManager Contracts.Refund

/-! ## No refund without a timeout proof -/

/-- **A REFUNDED OBLIGATION HAS A TIMEOUT PROOF BEHIND IT.**  If an obligation is
past `Committed` in any reachable state, some checked flow carrying that obligation
had a verified timeout proof. -/
def Properties.RefundNeedsOwnFlowTimeout : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Ms : Managers),
    Reach h z0 hl cv fh S emptyManagers Ms → ∀ (o : Obligation), Refunded Ms o →
      ∃ F', FlowIdChecked fh F' ∧ ∃ leg ∈ F'.legs, obligationOf F' leg = o
        ∧ RefundAuthorized h z0 hl cv S F'

/-- **AND IT IS THE OBLIGATION'S OWN FLOW'S.**  Another flow's timeout — genuine or
not — cannot authorize this one.  `_checkFlowId` is what closes the gap: two checked
flows claiming one id are the same flow. -/
def Properties.RefundImpliesOwnFlowTimeout : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash),
    FlowHashInj fh → ∀ (S : System) (F : Flow) (leg : FlowLeg),
    FlowIdChecked fh F → leg ∈ F.legs → ∀ (Ms : Managers),
    Reach h z0 hl cv fh S emptyManagers Ms → Refunded Ms (obligationOf F leg) →
      RefundAuthorized h z0 hl cv S F

/-! ## The milestone -/

/-- **AN EXECUTED OBLIGATION IS NEVER REFUNDED.**  For one economic obligation:
if it was executed on its destination, then across every interleaving of every
chain's manager calls it stays at `Committed` or below — no `authorizeRefund`
succeeds for it, so no `claimRefund` ever opens.

This is delivered-XOR-refunded at the level of the thing that carries value, over
the actual transitions, rather than at the level of one tree or one chain's state
machine. -/
def Properties.ExecutedObligationNeverRefunded : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash), FlowHashInj fh → ∀ (S : System), Wf S →
    ∀ (F : Flow) (leg : FlowLeg), leg ∈ F.legs → FlowIdChecked fh F →
    ExecutedVia h z0 hl cv fh S F leg →
    ∀ (Ms : Managers), Reach h z0 hl cv fh S emptyManagers Ms →
      ¬ Refunded Ms (obligationOf F leg)

/-- The same for every leg of the flow at once: one delivered leg freezes the whole
flow's refund path, which is what makes the outcome a property of the flow rather
than of the leg that happened to execute. -/
def Properties.OneExecutionFreezesTheFlow : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash), FlowHashInj fh → ∀ (S : System), Wf S →
    ∀ (F : Flow) (leg : FlowLeg), leg ∈ F.legs → FlowIdChecked fh F →
    ExecutedVia h z0 hl cv fh S F leg →
    ∀ (Ms : Managers), Reach h z0 hl cv fh S emptyManagers Ms →
    ∀ other ∈ F.legs, ¬ Refunded Ms (obligationOf F other)

/-! ## Timeout validity, derived -/

/-- **A VERIFIED TIMEOUT ENABLES THE REFUND.**  What `verifyTimeoutAbsence` actually
checks, against an imported aggregation root, is enough to authorize the step — so
the results above cover the real path with no "last in-time batch" fact assumed. -/
def Properties.VerifiedTimeoutAuthorizes : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (R : SlRoot),
    Aggregates S R → ∀ (F : Flow) (leg : FlowLeg), leg ∈ F.legs →
      LegRefundableVerified h z0 hl cv S R F leg → RefundAuthorized h z0 hl cv S F

/-- **AND A REFUNDED FLOW REALLY MISSED ITS DEADLINE.**  Composed with
`Protocol/InteropAtomicity/Properties/Timeout.lean`: if an obligation is refunded on the strength of a verified
timeout for its own flow, no leg of that flow was committed in time on its own
chain.  The refund is deserved, not merely permitted. -/
def Properties.RefundedFlowMissedDeadline : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (S : System), Wf S → ∀ (R : SlRoot), Aggregates S R →
    ∀ (F : Flow) (leg : FlowLeg), LegRefundableVerified h z0 hl cv S R F leg →
    ∀ n, S.time leg.chain n ≤ F.deadline →
      legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n))

/-! ## The chain, end to end -/

/-- **AN ACCEPTED TIMEOUT PROOF ENABLES THE REFUND, OR BREAKS A HASH.**  The gate as
the contract runs it — including `_verifyLastBatchInRoot` rather than its conclusion
— authorizes the step. -/
def Properties.AcceptedTimeoutAuthorizes : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (S : System) (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R),
      Aggregates S R → ∀ (F : Flow) (leg : FlowLeg), leg ∈ F.legs →
      LegRefundableAccepted h z0 hl cv S B F leg →
        RefundAuthorized h z0 hl cv S F ∨ HashBreak h ze (B.leaves leg.chain)

/-- **THE PUNCHLINE.**  Producing an accepted timeout proof for a flow that has a
delivered leg *is* producing a hash break.

Reading the hypotheses left to right: keccak behaves on the IMT, the tree histories
are well formed, the settlement layer aggregates honestly, the flow passed
`_checkFlowId`, and one of its legs executed.  Then no accepted timeout proof for
any of its legs exists — unless the prover has a collision in hand.

This is the dependency chain complete: accepted proof → last included batch → no
later in-time batch → justified timeout → obligation exclusivity. -/
def Properties.AcceptedTimeoutForDeliveredFlowIsABreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash) (S : System), Wf S →
    ∀ (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R), Aggregates S R →
    ∀ (F : Flow) (leg : FlowLeg), ExecutedVia h z0 hl cv fh S F leg →
    ∀ other ∈ F.legs, LegRefundableAccepted h z0 hl cv S B F other →
      HashBreak h ze (B.leaves other.chain)

/-! ## The supporting cryptographic claim -/

/-- **A CROSS-FLOW REFUND EXHIBITS A HASH COLLISION.**  No injectivity hypothesis:
if two checked flows ever share a `flowId` without being the same flow — which is
what a cross-flow refund would need — their `flowId` preimages collide.

This is the form worth stating.  The protocol guarantee is unconditional; keccak
enters only to say that breaking it is exactly as hard as finding a collision. -/
def Properties.CrossFlowRefundYieldsCollision : Prop :=
  ∀ (fh : FlowHash) (F F' : Flow), FlowIdChecked fh F → FlowIdChecked fh F' →
    F.flowId = F'.flowId → F ≠ F' →
      ∃ (l₁ : List FlowLeg) (d₁ : ℕ) (l₂ : List FlowLeg) (d₂ : ℕ),
        (l₁, d₁) ≠ (l₂, d₂) ∧ fh l₁ d₁ = fh l₂ d₂

/-- **WHAT A SHARED COMMITMENT MEANS.**  Two obligations with the same tree
commitment are the same leg — possibly on different chains — or they exhibit a
`commitValue` collision.

The scoping is the content here.  `commitValue(flowId, bundleHash)` carries no
chain, so obligations differing *only* in chain share a commitment by construction:
that is not a collision and not a defect.  What binds the chain is where the value
was inserted, plus `authorizeRefund`'s source-chain comparison — which is exactly
what `Contracts.Protocol.unbound_gate_refunds_delivered_leg` shows is load-bearing. -/
def Properties.SharedCommitmentYieldsCollision : Prop :=
  ∀ (cv : CommitValue) (o o' : Obligation),
    cv o.flowId o.bundleHash = cv o'.flowId o'.bundleHash →
      (o.flowId = o'.flowId ∧ o.bundleHash = o'.bundleHash)
        ∨ ∃ f₁ b₁ f₂ b₂, (f₁, b₁) ≠ (f₂, b₂) ∧ cv f₁ b₁ = cv f₂ b₂

/-- The same under the injectivity hypothesis: a shared commitment means the same
leg, with the chain still to be pinned separately. -/
def Properties.CommitmentPinsLeg : Prop :=
  ∀ (cv : CommitValue), CommitValueInj cv → ∀ (o o' : Obligation),
    cv o.flowId o.bundleHash = cv o'.flowId o'.bundleHash →
      o.flowId = o'.flowId ∧ o.bundleHash = o'.bundleHash

/-! ## The other branch stays live -/

/-- Once a timeout proof for the flow exists, any of its legs still `Committed` on
its own chain can be moved to `Revertable`.  The refund branch is not merely
permitted, it is reachable. -/
def Properties.TimeoutProofRefundsCommittedLeg : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Ms : Managers) (F : Flow) (leg : FlowLeg),
    FlowIdChecked fh F → leg ∈ F.legs → RefundAuthorized h z0 hl cv S F →
    AuthorizeGuard (Ms leg.chain) F.flowId leg.bundleHash →
      Step h z0 hl cv fh S Ms
        (setAt Ms leg.chain ((Ms leg.chain).set F.flowId leg.bundleHash .Revertable))


/-! ## `CommitValueInj` is unsatisfiable

Added during the consolidation.  `CommitValueInj` is global pair-injectivity of a
map `UInt256 → UInt256 → UInt256`, which counting rules out, so
`Properties.CommitmentPinsLeg` is vacuously true.  The collision form is
`Properties.SharedCommitmentYieldsCollision`. -/
def Properties.CommitValueInjUnsatisfiable : Prop := ∀ cv : CommitValue, ¬ CommitValueInj cv


/-- **THE UNPINNED COLLISION CONCLUSIONS ARE ALWAYS TRUE.**  Added during the
collision-form repair.  The conclusions of `Properties.CrossFlowRefundYieldsCollision`
and `Properties.SharedCommitmentYieldsCollision` existentially quantify the colliding
inputs, and every `fh` and every `cv` has a collision, so those two properties say
nothing as stated. -/
def Properties.UnpinnedCollisionsAlwaysExist : Prop :=
  (∀ fh : FlowHash, ∃ (l₁ : List FlowLeg) (d₁ : ℕ) (l₂ : List FlowLeg) (d₂ : ℕ),
      (l₁, d₁) ≠ (l₂, d₂) ∧ fh l₁ d₁ = fh l₂ d₂)
  ∧ (∀ cv : CommitValue, ∃ f₁ b₁ f₂ b₂, (f₁, b₁) ≠ (f₂, b₂) ∧ cv f₁ b₁ = cv f₂ b₂)

/-- **A CROSS-FLOW ID CLASH IS A COLLISION ON THE TWO FLOWS' OWN PREIMAGES.**  The pinned
form of `Properties.CrossFlowRefundYieldsCollision`: two distinct checked flows with one
id give `fh` a collision on exactly their `(legs, deadline)` preimages. -/
def Properties.CrossFlowIdClashIsPinnedCollision : Prop :=
  ∀ (fh : FlowHash) (F F' : Flow), FlowIdChecked fh F → FlowIdChecked fh F' →
    F.flowId = F'.flowId → F ≠ F' →
      (F.legs, F.deadline) ≠ (F'.legs, F'.deadline) ∧ fh F.legs F.deadline = fh F'.legs F'.deadline

/-! ## Repaired: pinned and bounded forms

Added with the collision-form repair.  `Properties.RefundImpliesOwnFlowTimeout` takes
`FlowHashInj` and `Properties.CommitmentPinsLeg` takes `CommitValueInj`; neither can
hold.  The replacements below carry no global injectivity premise.

Which of them have protocol content:

* `Properties.RefundImpliesOwnFlowTimeoutOrCollision` and its flow-level form
  `Properties.RefundOfFlowIdImpliesOwnFlowTimeoutOrCollision` **do**.  The collision
  disjunct is not the negation of the conclusion: to get from "this obligation is
  refunded" to "some checked flow `F'` sharing `F`'s id and owning this obligation had
  a timeout proof" takes the induction over every interleaving of every chain's calls
  (`refund_needs_own_flow_timeout`).  `Properties.RefundOrCollisionNeedsReach` shows that
  the conclusion fails without the reachability premise, and
  `Properties.RefundImpliesOwnFlowTimeoutOrCollisionWitness` that on a concrete
  reachable refund the collision disjunct is false.
* `Properties.CommitmentPinsLegOrCollision` **does not**: given the shared commitment,
  its collision disjunct is the negation of its first disjunct, so it is excluded
  middle.  It is recorded as the honest pinned shape of the old statement; the bounded
  form `Properties.CommitmentPinsLegOn` is the usable one. -/

/-- **A REFUNDED OBLIGATION OF A CHECKED FLOW HAS THAT FLOW'S TIMEOUT BEHIND IT, OR
`fh` COLLIDES ON TWO NAMED FLOWS.**  If an obligation of checked flow `F` is past
`Committed` in a reachable state, then `F` itself had a verified timeout proof, or some
checked flow `F'` that owns this same obligation and had a verified timeout proof
collides with `F` on exactly their two `(legs, deadline)` preimages.

The pinned form of `Properties.RefundImpliesOwnFlowTimeout`.  Only half-pinned: `F'`
is existentially quantified and is not tied to a flow that appears in the run, so a
reviewer showed the collision disjunct can be met by any second checked flow sharing
`F`'s id.  A run-level form naming the `authorize` call's flow is open. -/
def Properties.RefundImpliesOwnFlowTimeoutOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (F : Flow) (leg : FlowLeg),
    FlowIdChecked fh F → leg ∈ F.legs → ∀ (Ms : Managers),
    Reach h z0 hl cv fh S emptyManagers Ms → Refunded Ms (obligationOf F leg) →
      RefundAuthorized h z0 hl cv S F
        ∨ ∃ F', FlowIdChecked fh F'
            ∧ (∃ leg' ∈ F'.legs, obligationOf F' leg' = obligationOf F leg)
            ∧ RefundAuthorized h z0 hl cv S F' ∧ FlowIdClash fh F F'

/-- **THE SAME, FOR EVERY OBLIGATION CARRYING THE FLOW'S ID.**  Any obligation with
`F`'s id — the executed leg's or a sibling's, on any chain — that is refunded in a
reachable state has `F`'s own timeout behind it, or a pinned collision between `F`
and a checked, timed-out flow `F'` owning that obligation.  This is the form a
flow-level freeze composes with. -/
def Properties.RefundOfFlowIdImpliesOwnFlowTimeoutOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (F : Flow), FlowIdChecked fh F → ∀ (Ms : Managers),
    Reach h z0 hl cv fh S emptyManagers Ms → ∀ (o : Obligation), o.flowId = F.flowId →
    Refunded Ms o →
      RefundAuthorized h z0 hl cv S F
        ∨ ∃ F', FlowIdChecked fh F' ∧ (∃ leg' ∈ F'.legs, obligationOf F' leg' = o)
            ∧ RefundAuthorized h z0 hl cv S F' ∧ FlowIdClash fh F F'

/-- **THE CONTENT IS IN THE REACHABILITY PREMISE.**  Drop `Reach … emptyManagers Ms`
and the conclusion of `Properties.RefundImpliesOwnFlowTimeoutOrCollision` fails: there
is a checked flow, a leg of it, and a manager state in which that leg's obligation is
`Revertable` while neither the flow nor any other flow has a timeout proof.  So the
statement is not a rearrangement of its other hypotheses. -/
def Properties.RefundOrCollisionNeedsReach : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (F : Flow) (leg : FlowLeg) (Ms : Managers),
    FlowIdChecked fh F ∧ leg ∈ F.legs ∧ Refunded Ms (obligationOf F leg) ∧
      ¬ (RefundAuthorized h z0 hl cv S F
          ∨ ∃ F', FlowIdChecked fh F'
              ∧ (∃ leg' ∈ F'.legs, obligationOf F' leg' = obligationOf F leg)
              ∧ RefundAuthorized h z0 hl cv S F' ∧ FlowIdClash fh F F')

/-- **ANTI-VACUITY WITNESS.**  The premises of
`Properties.RefundImpliesOwnFlowTimeoutOrCollision` hold together — a checked flow, a
reachable run (`append` then `authorize`) and a refunded obligation — while its
collision disjunct is false on that same instance.  So on this run the theorem
delivers its first disjunct, and the disjunct is no tautology. -/
def Properties.RefundImpliesOwnFlowTimeoutOrCollisionWitness : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (F : Flow) (leg : FlowLeg) (Ms : Managers),
    FlowIdChecked fh F ∧ leg ∈ F.legs ∧ Reach h z0 hl cv fh S emptyManagers Ms
      ∧ Refunded Ms (obligationOf F leg)
      ∧ ¬ ∃ F', FlowIdChecked fh F'
          ∧ (∃ leg' ∈ F'.legs, obligationOf F' leg' = obligationOf F leg)
          ∧ RefundAuthorized h z0 hl cv S F' ∧ FlowIdClash fh F F'

/-- **A SHARED COMMITMENT: THE SAME LEG, OR `cv` COLLIDES ON THESE TWO INPUTS.**  The
pinned form of `Properties.CommitmentPinsLeg`.  Tautological given its hypothesis (see
the section header): recorded for its shape, not its content. -/
def Properties.CommitmentPinsLegOrCollision : Prop :=
  ∀ (cv : CommitValue) (o o' : Obligation),
    cv o.flowId o.bundleHash = cv o'.flowId o'.bundleHash →
      (o.flowId = o'.flowId ∧ o.bundleHash = o'.bundleHash) ∨ CommitClash cv o o'

/-- **A SHARED COMMITMENT PINS THE LEG, BOUNDED.**  If `cv` has no collision among the
obligations of a finite list `os`, two of them with one commitment have the same
`(flowId, bundleHash)` — the chain still to be pinned separately. -/
def Properties.CommitmentPinsLegOn : Prop :=
  ∀ (cv : CommitValue) (os : List Obligation), CommitValueInjOn cv os →
    ∀ o ∈ os, ∀ o' ∈ os, cv o.flowId o.bundleHash = cv o'.flowId o'.bundleHash →
      o.flowId = o'.flowId ∧ o.bundleHash = o'.bundleHash

/-- **THE BOUNDED PREMISE IS SATISFIABLE.**  For every list of fewer than `2^256`
obligations there is a commit value with no collision among them. -/
def Properties.CommitValueInjOnSatisfiable : Prop :=
  ∀ os : List Obligation, os.length < UInt256.size → ∃ cv : CommitValue, CommitValueInjOn cv os

/-- **THE PINNED DISJUNCT IS NOT A TAUTOLOGY.**  For every obligation `o`, the commit
value `honestCommitValue o` has no `CommitClash` between `o` and any obligation. -/
def Properties.HonestCommitValueNoClash : Prop :=
  ∀ o o' : Obligation, ¬ CommitClash (honestCommitValue o) o o'

/-! ## The milestone without hash premises: the property, or a located break

`Properties.ExecutedObligationNeverRefunded` and `OneExecutionFreezesTheFlow` take
`HashAssumptions` and `FlowHashInj`, neither of which can hold.  The forms below take
neither.  They are stated over the logged run `ReachLog` (same reachable states as
`Reach`: `Properties.ReachIffReachLog`) and the named gate evidence `ExecutedViaBy`, and
their break is a `RefundBreak`: a call in the run's own log that marked the obligation,
with a `FlowIdClash` between the executed flow and that call's flow, or a
`TreeRootBreak` on the executed flow's inclusion proof for the call's missing leg, or on
the call's own absence proof. -/

/-- **LOGGING THE CALLS LOSES NOTHING.** -/
def Properties.ReachIffReachLog : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Ms Ns : Managers),
    Reach h z0 hl cv fh S Ms Ns ↔ ∃ log, ReachLog h z0 hl cv fh S Ms Ns log

/-- **A REFUNDED OBLIGATION WAS MARKED BY A LOGGED, VERIFIED CALL.**  The run-level
form of `Properties.RefundNeedsOwnFlowTimeout`: the authorizing flow is the flow of a
call in the log. -/
def Properties.RefundNeedsLoggedAuthorize : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Ms : Managers) (log : List AuthCall),
    ReachLog h z0 hl cv fh S emptyManagers Ms log → ∀ (o : Obligation), Refunded Ms o →
      ∃ a ∈ log, a.Verified h z0 hl cv fh S ∧ obligationOf a.flow a.leg = o

/-- **A REFUNDED OBLIGATION OF A CHECKED FLOW HAS THAT FLOW'S TIMEOUT BEHIND IT, OR
`fh` COLLIDES ON THAT FLOW AND A LOGGED CALL'S FLOW.**  The run-level pinning of
`Properties.RefundImpliesOwnFlowTimeoutOrCollision`, whose `F'` was existential: here
the other flow is the flow of a call in the run's log that marked this very
obligation. -/
def Properties.RefundImpliesOwnFlowTimeoutOrLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (F : Flow) (leg : FlowLeg), FlowIdChecked fh F → leg ∈ F.legs →
    ∀ (Ms : Managers) (log : List AuthCall), ReachLog h z0 hl cv fh S emptyManagers Ms log →
      Refunded Ms (obligationOf F leg) →
      RefundAuthorized h z0 hl cv S F
        ∨ ∃ a ∈ log, obligationOf a.flow a.leg = obligationOf F leg ∧ FlowIdClash fh F a.flow

/-- **AN EXECUTED OBLIGATION IS NEVER REFUNDED, OR A LOCATED BREAK.**  If leg `leg` of
`F` executed on gate evidence `ev`, then in every logged run its obligation stays at
`Committed` or below, or a call in the run's log that marked it carries a
`RefundBreak`. -/
def Properties.ExecutedObligationNeverRefundedOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Ms : Managers) (log : List AuthCall), ReachLog h z0 hl cv fh S emptyManagers Ms log →
      ¬ Refunded Ms (obligationOf F leg)
        ∨ RefundBreak h z0 hl fh S F ev (obligationOf F leg) log

/-- **ONE EXECUTION FREEZES THE FLOW, OR A LOCATED BREAK.**  The same for every leg of
the flow. -/
def Properties.OneExecutionFreezesTheFlowOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Ms : Managers) (log : List AuthCall), ReachLog h z0 hl cv fh S emptyManagers Ms log →
    ∀ other ∈ F.legs,
      ¬ Refunded Ms (obligationOf F other)
        ∨ RefundBreak h z0 hl fh S F ev (obligationOf F other) log

/-- **A REFUNDED FLOW REALLY MISSED ITS DEADLINE, OR A LOCATED BREAK.**  The refund
form of `Contracts.Timeout.Properties.TimeoutMeansMissedDeadlineOrBreak`. -/
def Properties.RefundedFlowMissedDeadlineOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (R : SlRoot), Aggregates S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      LegRefundableVerifiedBy h z0 hl cv S R F leg N p →
      (∀ n, S.time leg.chain n ≤ F.deadline →
          legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
        ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p

/-! ### Anti-vacuity -/

/-- **THE PREMISES ARE SATISFIABLE WITH A LIVE REFUND PATH, AND THE BREAK IS FALSE.**
For every node hash, leaf hash and padding constant: in `mixedSystem 1` the one-leg flow
`subsetFlow 0 1` executes on honest evidence, while in the same run a DIFFERENT checked
flow `mixedFlow 1 1 2` is appended and authorized for refund (log nonempty).  No
`RefundBreak` is located for the executed obligation, and it is not refunded. -/
def Properties.ExecutedObligationNeverRefundedOrBreakWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (F : Flow) (ev : GateEvidence)
      (leg : FlowLeg) (Ms : Managers) (log : List AuthCall),
      Wf S ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ ReachLog h z0 hl cv fh S emptyManagers Ms log ∧ log ≠ []
        ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) log
        ∧ ¬ Refunded Ms (obligationOf F leg)

/-- **THE LOGGED-CLASH DISJUNCT IS NOT A TAUTOLOGY.**  On that same run, the refunded
obligation of `mixedFlow 1 1 2` has all the premises of
`Properties.RefundImpliesOwnFlowTimeoutOrLoggedClash`, and no logged call clashes. -/
def Properties.RefundImpliesOwnFlowTimeoutOrLoggedClashWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (F : Flow) (leg : FlowLeg)
      (Ms : Managers) (log : List AuthCall),
      FlowIdChecked fh F ∧ leg ∈ F.legs ∧ ReachLog h z0 hl cv fh S emptyManagers Ms log
        ∧ Refunded Ms (obligationOf F leg)
        ∧ ¬ ∃ a ∈ log, obligationOf a.flow a.leg = obligationOf F leg ∧ FlowIdClash fh F a.flow

/-- **THE BREAK FIRES WHERE THE BUG IS.**  With the extraction-pin padding
`z0 = hl ⟨0,0,0⟩`, in `paddedSystem a b` a one-leg flow executes on the honest inclusion
proof, and the run appends its obligation and then authorizes its refund on the forged
padding absence proof.  The obligation IS refunded, so the theorem must return a
`RefundBreak`; every logged call is the executed flow's own (no `FlowIdClash`), the
executed flow's inclusion proof carries no break, and the call's absence proof does. -/
def Properties.PaddingRefundOfExecutedObligationLocatesAbsenceBreak : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    ∃ (cv : CommitValue) (fh : FlowHash) (F : Flow) (ev : GateEvidence) (leg : FlowLeg)
      (Ms : Managers) (log : List AuthCall),
      Wf (paddedSystem a b) ∧ ExecutedViaBy h (hl ⟨0, 0, 0⟩) hl cv fh (paddedSystem a b) F ev leg
        ∧ ReachLog h (hl ⟨0, 0, 0⟩) hl cv fh (paddedSystem a b) emptyManagers Ms log
        ∧ Refunded Ms (obligationOf F leg)
        ∧ RefundBreak h (hl ⟨0, 0, 0⟩) hl fh (paddedSystem a b) F ev (obligationOf F leg) log
        ∧ ∀ c ∈ log, c.flow = F ∧ ¬ FlowIdClash fh F c.flow
            ∧ ¬ InclusionBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) c.missing.chain
                (ev c.missing).1 (ev c.missing).2
            ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) F.deadline c.missing.chain
                c.batch c.proof

open MerkleSpec.Verifier

/-! ### The accepted-timeout chain without hash premises

`Properties.AcceptedTimeoutAuthorizes` and `AcceptedTimeoutForDeliveredFlowIsABreak`
take `HashAssumptions` and conclude an unpinned `HashBreak`, which is always inhabited.
The forms below take no hash premise and locate the break on the submitted proofs:
the batch-leaf path `(sibs, x)` (`PinnedBreak` / `PathCollision`), the absence proof
`p` (`AbsenceBreak`), and the executed flow's inclusion proof (`InclusionBreak`). -/

/-- **AN ACCEPTED TIMEOUT PROOF AUTHORIZES THE REFUND, OR PINS A COLLISION ON ITS
LAST-BATCH PATH.** -/
def Properties.AcceptedTimeoutAuthorizesPinned : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (R : SlRoot) (B : RootBacking h ze R), Aggregates S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      leg ∈ F.legs → LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x →
        RefundAuthorized h z0 hl cv S F ∨ PinnedBreak h ze (B.leaves leg.chain) N
          ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x

/-- **ITS PREMISES HOLD AND ITS BREAKS ARE FALSE ON THE DEMO INSTANCE.**  `demoSystem`
with `demoRoot`/`demoBacking` under the colliding `demoHash`, an END-branch accepted
timeout for batch 1 on the honest batch-leaf path: no `PinnedBreak`, no
`PathCollision`, and the refund is authorized. -/
def Properties.AcceptedTimeoutAuthorizesPinnedWitness : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (R : SlRoot) (B : RootBacking h ze R) (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof)
    (sibs : ℕ → UInt256) (x : UInt256),
      Aggregates S R ∧ leg ∈ F.legs ∧ LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x
        ∧ EndBranchAccepted B S leg.chain F.deadline N sibs x
        ∧ ¬ PinnedBreak h ze (B.leaves leg.chain) N
        ∧ ¬ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x
        ∧ RefundAuthorized h z0 hl cv S F

/-- **EXECUTION EXCLUDES EVERY ACCEPTED TIMEOUT IN THE FLOW, OR A LOCATED BREAK.**  The
repaired `Properties.AcceptedTimeoutForDeliveredFlowIsABreak`: if a leg executed on gate
evidence `ev`, then no leg `other` of the flow passes the timeout gate as the contract
runs it on `(N, p, sibs, x)`, unless `ev other` carries a break, or `p` does, or the
last-batch path `(sibs, x)` pins a collision. -/
def Properties.ExecutedExcludesAcceptedRefundOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R), Aggregates S R →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ other ∈ F.legs, ∀ (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      ¬ LegRefundableAcceptedBy h z0 hl cv S B F other N p sibs x
        ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2
        ∨ AbsenceBreak h z0 hl S F.deadline other.chain N p
        ∨ PinnedBreak h ze (B.leaves other.chain) N
        ∨ PathCollision h ze (B.leaves other.chain) sibs 0 (B.height other.chain) N x

/-- **ITS PREMISES HOLD AND ALL FOUR BREAKS ARE FALSE.**  `subsetFlow 0 1` executes in
`mixedSystem 1` under `demoHash`, with `demoRoot`/`demoBacking` (`Aggregates` holds);
for the submitted evidence (batch 0, the honest IMT proof, the honest batch-leaf path
for batch 0) no break is located, and the timeout gate does not pass. -/
def Properties.ExecutedExcludesAcceptedRefundOrBreakWitness : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R) (F : Flow) (ev : GateEvidence)
    (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      Wf S ∧ Aggregates S R ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ ¬ InclusionBreak h z0 hl S leg.chain (ev leg).1 (ev leg).2
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N p
        ∧ ¬ PinnedBreak h ze (B.leaves leg.chain) N
        ∧ ¬ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x
        ∧ ¬ LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x

/-- **THE BREAK FIRES WHERE THE BUG IS.**  With the extraction-pin padding, in
`paddedSystem a b` with `timeOneRoot` (`Aggregates` holds), an executed one-leg flow
passes the timeout gate as run, on the BEGIN branch at batch 1 with the forged padding
proof.  The located break is on the absence proof, not on the inclusion proof. -/
def Properties.PaddingAcceptedRefundLocatesAbsenceBreak : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    ∃ (ze : UInt256) (B : RootBacking h ze timeOneRoot) (cv : CommitValue) (fh : FlowHash)
      (F : Flow) (ev : GateEvidence) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      Wf (paddedSystem a b) ∧ Aggregates (paddedSystem a b) timeOneRoot
        ∧ ExecutedViaBy h (hl ⟨0, 0, 0⟩) hl cv fh (paddedSystem a b) F ev leg
        ∧ (∀ (sibs : ℕ → UInt256) (x : UInt256),
            LegRefundableAcceptedBy h (hl ⟨0, 0, 0⟩) hl cv (paddedSystem a b) B F leg N p sibs x)
        ∧ ¬ InclusionBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) leg.chain (ev leg).1 (ev leg).2
        ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) F.deadline leg.chain N p


end Contracts.Refund
