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

end Contracts.Refund
